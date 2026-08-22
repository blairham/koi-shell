// Copyright (c) 2025, koi authors.
// See LICENSE for licensing information.

package expand

import (
	"bufio"
	"maps"
	"os"
	"slices"
	"strconv"
	"strings"
	"testing"
)

// assocCase is one measurement: a key set in the order its keys were
// assigned, and the order bash listed them back in.
type assocCase struct {
	label string
	keys  []string
	want  []string
}

// readAssocCases parses testdata/assocorder.txt, which holds bash 5.3's
// answers rather than koi's expectations — see the file's own header.
func readAssocCases(t *testing.T) []assocCase {
	t.Helper()
	f, err := os.Open("testdata/assocorder.txt")
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	var cases []assocCase
	var keys []string
	line := 0
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 1<<20)
	for sc.Scan() {
		line++
		text := sc.Text()
		switch {
		case text == "" || strings.HasPrefix(text, "#"):
		case strings.HasPrefix(text, "set "):
			keys = nil
			for _, field := range strings.Split(text[len("set "):], "\t") {
				k, err := strconv.Unquote(field)
				if err != nil {
					t.Fatalf("line %d: %v", line, err)
				}
				keys = append(keys, k)
			}
		case strings.HasPrefix(text, "gen "):
			n, err := strconv.Atoi(text[len("gen "):])
			if err != nil {
				t.Fatalf("line %d: %v", line, err)
			}
			keys = make([]string, n)
			for i := range keys {
				keys[i] = "k" + strconv.Itoa(i)
			}
		case strings.HasPrefix(text, "want "):
			if keys == nil {
				t.Fatalf("line %d: want without a key set", line)
			}
			fields := strings.Fields(text[len("want "):])
			if len(fields) != len(keys) {
				t.Fatalf("line %d: %d indices for %d keys", line, len(fields), len(keys))
			}
			want := make([]string, len(fields))
			for i, field := range fields {
				idx, err := strconv.Atoi(field)
				if err != nil {
					t.Fatalf("line %d: %v", line, err)
				}
				want[i] = keys[idx]
			}
			label := strconv.Itoa(len(keys)) + " keys starting " + keys[0]
			cases = append(cases, assocCase{label, keys, want})
			keys = nil
		default:
			t.Fatalf("line %d: unrecognized %q", line, text)
		}
	}
	if err := sc.Err(); err != nil {
		t.Fatal(err)
	}
	if len(cases) < 195 {
		t.Fatalf("only %d cases parsed, testdata is truncated", len(cases))
	}
	return cases
}

// TestAssocOrder is the whole basis for assocorder.go: bash's order for
// 197 measured key sets, against the rule fitted to them. It covers the
// hash, the initial bucket count, the newest-first chain order for keys
// that share a bucket, the signed reading of bytes above 0x7f, and the
// first two table growths.
func TestAssocOrder(t *testing.T) {
	t.Parallel()
	for _, c := range readAssocCases(t) {
		m := make(map[string]string, len(c.keys))
		for _, k := range c.keys {
			m[k] = ""
		}
		got := assocOrder(m, c.keys)
		if !slices.Equal(got, c.want) {
			t.Errorf("%s:\ngot  %q\nwant %q", c.label, got, c.want)
		}
	}
}

// TestAssocOrderRivals checks that the golden data actually pins the
// rule down rather than agreeing with anything plausible. Each rival is
// one part of assocorder.go changed and nothing else; a rival that
// scored as well as the real thing would mean the measurements do not
// distinguish them, and the fit would be a coincidence.
func TestAssocOrderRivals(t *testing.T) {
	t.Parallel()
	cases := readAssocCases(t)
	// Only the sets that fit 1024 buckets, so the rivals are judged on
	// the hash and the chain rather than on the growth policy.
	var small []assocCase
	for _, c := range cases {
		if len(c.keys) <= assocBuckets*assocLoad {
			small = append(small, c)
		}
	}
	fnv1a := func(key string) uint32 {
		h := uint32(assocHashOffset)
		for i := 0; i < len(key); i++ {
			h ^= uint32(int32(int8(key[i])))
			h *= assocHashPrime
		}
		return h
	}
	unsigned := func(key string) uint32 {
		h := uint32(assocHashOffset)
		for i := 0; i < len(key); i++ {
			h *= assocHashPrime
			h ^= uint32(key[i])
		}
		return h
	}
	lay := func(seq []string, n int, hash func(string) uint32, oldestFirst bool) []string {
		buckets := make(map[uint32][]string, len(seq))
		for i := range seq {
			j := i
			if !oldestFirst {
				j = len(seq) - 1 - i
			}
			b := hash(seq[j]) % uint32(n)
			buckets[b] = append(buckets[b], seq[j])
		}
		var out []string
		for _, b := range slices.Sorted(maps.Keys(buckets)) {
			out = append(out, buckets[b]...)
		}
		return out
	}
	rivals := []struct {
		name string
		fn   func(c assocCase) []string
	}{
		{"sorted by key", func(c assocCase) []string { return slices.Sorted(slices.Values(c.keys)) }},
		{"insertion order", func(c assocCase) []string { return c.keys }},
		{"fnv-1a instead of fnv-1", func(c assocCase) []string {
			return lay(c.keys, assocBuckets, fnv1a, false)
		}},
		{"512 buckets", func(c assocCase) []string { return lay(c.keys, 512, assocHash, false) }},
		{"2048 buckets", func(c assocCase) []string { return lay(c.keys, 2048, assocHash, false) }},
		{"oldest first in a bucket", func(c assocCase) []string {
			return lay(c.keys, assocBuckets, assocHash, true)
		}},
		{"unsigned key bytes", func(c assocCase) []string {
			return lay(c.keys, assocBuckets, unsigned, false)
		}},
	}
	for _, rival := range rivals {
		agree := 0
		for _, c := range small {
			if slices.Equal(rival.fn(c), c.want) {
				agree++
			}
		}
		t.Logf("%s: agrees on %d/%d", rival.name, agree, len(small))
		if agree == len(small) {
			t.Errorf("%q reproduces every measurement, so the data does not pin the rule down",
				rival.name)
		}
	}
}

// TestAssocOrderAdvisory covers the sequence being advisory rather than
// trusted: a write that did not record itself, a key unset without the
// sequence being pruned, and no sequence at all must all still yield a
// total, stable order — a Go map's own iteration would not.
func TestAssocOrderAdvisory(t *testing.T) {
	t.Parallel()
	m := map[string]string{"bz": "", "66": "", "edc": ""}
	full := assocOrder(m, []string{"bz", "66", "edc"})
	if want := []string{"edc", "66", "bz"}; !slices.Equal(full, want) {
		t.Fatalf("got %q, want %q", full, want)
	}
	// A key the sequence never mentioned counts as the newest, which is
	// exactly right for the one writer that does this: `${A[k]=v}` adds
	// a single key and it is the last insertion.
	if got := assocOrder(m, []string{"bz", "66"}); !slices.Equal(got, full) {
		t.Errorf("unrecorded key: got %q, want %q", got, full)
	}
	// A stale name in the sequence is ignored rather than listed.
	if got := assocOrder(m, []string{"bz", "gone", "66", "edc", "bz"}); !slices.Equal(got, full) {
		t.Errorf("stale key: got %q, want %q", got, full)
	}
	// With no sequence at all the order is still total and repeatable.
	first := assocOrder(m, nil)
	if len(first) != len(m) {
		t.Fatalf("got %q for a 3-key map", first)
	}
	for range 20 {
		if got := assocOrder(m, nil); !slices.Equal(got, first) {
			t.Fatalf("unstable without a sequence: %q then %q", first, got)
		}
	}
	if got := assocOrder(nil, nil); got != nil {
		t.Errorf("empty map: got %q", got)
	}
}
