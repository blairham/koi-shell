// Copyright (c) 2025, koi authors.
// See LICENSE for licensing information.

package expand

import (
	"maps"
	"slices"
)

// bash iterates an associative array in the order of its own hash table,
// which is neither sorted nor insertion order, and every surface that
// lists the array — `${A[@]}`, `${!A[@]}`, `${A[*]}`, `declare -p`,
// `${A[@]@K}`, `${A[@]@A}` — shows it. Scripts read that order, and
// bash's own test suite asserts it, so koi reproduces it (#749).
//
// The rule below was derived by *measurement*, never by reading bash's
// source: bash is GPLv3 and koi is MIT, so the same rule that keeps
// bash's test suite out of the tree (#211) and made `help`'s topic text
// be written from observation (#557) applies here. The order of an
// associative array is a total function of its key set and the sequence
// the keys were inserted in, so it can be probed exhaustively: feed bash
// key sets, read back `${!A[@]}`, and fit. What was fitted, and what each
// number was pinned down by, is recorded in assocorder_test.go against
// the measurements themselves.
//
// The four independent parts, in the order they had to be nailed down —
// a right hash with a wrong bucket count is still the wrong order. The
// scores are against the 197 measured key sets in
// testdata/assocorder.txt, all of which the rule below reproduces;
// TestAssocOrderRivals keeps each rival on the record so that a later
// change cannot quietly land on one:
//
//  1. Hash: 32-bit FNV-1 — multiply by the prime, *then* xor the byte —
//     over the key's bytes, offset basis 2166136261, prime 16777619.
//     FNV-1a, which xors first, reproduces 11/197.
//  2. Bucket: the hash modulo a bucket count that starts at 1024. 512
//     reproduces 41/197 and 2048 36/197, which is what a wrong bucket
//     count looks like: agreement wherever a set happens not to
//     straddle the difference.
//  3. Chain: newest first. A key goes to the head of its bucket,
//     re-assigning an existing key does not move it, and unsetting then
//     re-assigning moves it back to the head. Oldest-first reproduces
//     156/197 — every set without a collision cannot tell the two
//     apart, which is why 36 of the sets were built to collide.
//  4. Growth: when a key would make the entry count exceed twice the
//     bucket count, the table first grows to *four* times its size and
//     re-inserts, which reverses every chain. Fitted on the first
//     growth (2048 entries against 2049) and confirmed on the second
//     and third (8192/8193, 32768/32769) up to 35000 keys.
//
// Neither sorting nor insertion order comes close: they reproduce
// 16/197 and 11/197, which is the measure of how visible this is.
//
// One deliberate non-match, because bash does not match itself here.
// bash xors each byte as a plain `char`, so whether a byte above 0x7f
// is sign-extended follows the platform's ABI: signed on x86-64 (any
// OS) and on arm64 macOS, unsigned on arm64 Linux. koi signs it
// unconditionally — it agrees with bash on the two mainstream targets,
// and a shell whose expansion order changed with the machine's ABI
// would be worse than one that picks. It only shows for keys holding
// bytes above 0x7f, which is why the unsigned reading still reproduces
// 157/197; on the 40 sets that do hold them it reproduces none.
const (
	assocHashOffset = 2166136261
	assocHashPrime  = 16777619

	// assocBuckets is the bucket count a fresh table starts with.
	assocBuckets = 1024
	// assocLoad is the entries-per-bucket ratio a table grows past, and
	// assocGrowth the factor it grows by.
	assocLoad   = 2
	assocGrowth = 4
)

// assocHash hashes a key the way bash's table does. The byte is xored as
// a *signed* char, so 0x80..0xff carry their sign into the high bits.
func assocHash(key string) uint32 {
	h := uint32(assocHashOffset)
	for i := 0; i < len(key); i++ {
		h *= assocHashPrime
		h ^= uint32(int32(int8(key[i])))
	}
	return h
}

// assocOrder returns the keys of m in bash's hash-table order, given the
// sequence they were inserted in.
//
// ins is advisory, not trusted: it is filtered down to the keys m still
// holds, and any key of m it does not mention is treated as inserted
// last, in sorted order. That keeps the order total and stable even for
// a write that did not record itself — `${A[k]=v}` adds one key without
// touching the sequence, and appending it last is exactly right, since
// it *was* the last insertion.
func assocOrder(m map[string]string, ins []string) []string {
	if len(m) == 0 {
		return nil
	}
	seq := make([]string, 0, len(m))
	seen := make(map[string]bool, len(m))
	for _, k := range ins {
		if _, ok := m[k]; ok && !seen[k] {
			seen[k] = true
			seq = append(seq, k)
		}
	}
	if len(seq) < len(m) {
		missing := make([]string, 0, len(m)-len(seq))
		for k := range m {
			if !seen[k] {
				missing = append(missing, k)
			}
		}
		slices.Sort(missing)
		seq = append(seq, missing...)
	}
	return assocTableOrder(seq)
}

// assocTableOrder replays seq into a table shaped like bash's and reads
// the table back out: buckets in index order, each chain newest first.
//
// The buckets are a map rather than a 1024-entry slice so that listing a
// three-element array does not walk 1021 empty chains. Nothing is lost:
// growth multiplies the bucket count, so every key of one old bucket
// lands in a new bucket that no other old bucket reaches, which makes
// the order buckets are re-inserted in unobservable.
func assocTableOrder(seq []string) []string {
	// Below the first growth threshold — every real script — the table
	// never rehashed and the whole order is one pass: bucket ascending,
	// newest first within a bucket. Past it, each growth reverses every
	// chain, so the growths are replayed rather than their parity
	// guessed. A grown table's order is the pass applied to the order
	// the table already had, since a key's new bucket is reached by no
	// other old bucket, which is what makes a growth a re-lay rather
	// than a merge.
	out := seq
	for n := assocBuckets; ; n *= assocGrowth {
		grown := n * assocLoad
		if len(seq) <= grown {
			return assocLay(out, n)
		}
		out = append(assocLay(out[:grown], n), seq[grown:]...)
	}
}

// assocLay places seq into n buckets, newest first within each bucket,
// and flattens the buckets in index order.
func assocLay(seq []string, n int) []string {
	buckets := make(map[uint32][]string, len(seq))
	for i := len(seq) - 1; i >= 0; i-- {
		b := assocHash(seq[i]) % uint32(n)
		buckets[b] = append(buckets[b], seq[i])
	}
	out := make([]string, 0, len(seq))
	for _, b := range slices.Sorted(maps.Keys(buckets)) {
		out = append(out, buckets[b]...)
	}
	return out
}
