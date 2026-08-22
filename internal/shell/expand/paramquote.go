// Copyright (c) 2017, Daniel Martí <mvdan@mvdan.cc>
// See LICENSE for licensing information

package expand

import (
	"fmt"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

// quoteReusable renders a value in a form that can be read back as shell
// input, which is what `${x@Q}` is for: bash's sh_quote_reusable.
//
// The rule that makes it different from [syntax.Quote] is that the quotes
// are **unconditional** — `${x@Q}` of `hello` is `'hello'`, not `hello`
// (#648). syntax.Quote picks the shortest representation and hands a
// plain word back unchanged, which is right for a printer and wrong for
// an operator whose callers write `[[ ${x@Q} == "'$x'" ]]` or diff the
// answer against a saved listing.
//
// Two shapes are bash's and would not fall out of "always single-quote":
// the empty string is `”` rather than nothing, and a lone single quote
// is `\'` rather than `”\”'`.
func quoteReusable(s string, cLocale bool) string {
	switch {
	case s == "":
		return "''"
	case s == "'":
		return `\'`
	case ansiCShouldQuote(s, cLocale):
		return ansiCQuote(s, cLocale)
	}
	return singleQuote(s)
}

// singleQuote wraps s in single quotes, ending and restarting the quoted
// span around each single quote in the value: bash's sh_single_quote, so
// `it's` becomes `'it'\”s'`.
func singleQuote(s string) string {
	var sb strings.Builder
	sb.Grow(len(s) + 2)
	sb.WriteByte('\'')
	for i := range len(s) {
		c := s[i]
		sb.WriteByte(c)
		if c == '\'' {
			sb.WriteString(`\''`)
		}
	}
	sb.WriteByte('\'')
	return sb.String()
}

// doubleQuote wraps s in double quotes, escaping the four characters that
// would still be special inside them: bash's sh_double_quote, which is
// how a `declare -p`-shaped answer renders a value.
func doubleQuote(s string) string {
	var sb strings.Builder
	sb.Grow(len(s) + 2)
	sb.WriteByte('"')
	for i := range len(s) {
		switch c := s[i]; c {
		case '$', '`', '"', '\\':
			sb.WriteByte('\\')
			sb.WriteByte(c)
		default:
			sb.WriteByte(c)
		}
	}
	sb.WriteByte('"')
	return sb.String()
}

// ansiCShouldQuote reports whether a value needs the `$'…'` form, which
// is bash's ansic_shouldquote: any character the locale says is not
// printable. In the C locale a character is a byte (#470), so every byte
// over 0x7f is unprintable there — measured, `LC_ALL=C` turns `ü` into
// `$'\303\274'` where a UTF-8 locale leaves it single-quoted.
func ansiCShouldQuote(s string, cLocale bool) bool {
	for i := 0; i < len(s); {
		if c := s[i]; c < utf8Self {
			if !printableASCII(c) {
				return true
			}
			i++
			continue
		}
		if cLocale {
			return true
		}
		r, size := utf8.DecodeRuneInString(s[i:])
		if r == utf8.RuneError && size == 1 {
			return true // an invalid byte is not a printable character
		}
		if !unicode.IsPrint(r) {
			return true
		}
		i += size
	}
	return false
}

// ansiCQuote renders a value as `$'…'`: bash's ansic_quote. The named
// escapes are bash's own set, which spells escape as `\E` rather than
// `\e`, and anything else unprintable comes out as a three-digit octal
// byte.
func ansiCQuote(s string, cLocale bool) string {
	var sb strings.Builder
	sb.Grow(len(s) + 4)
	sb.WriteString("$'")
	for i := 0; i < len(s); {
		c := s[i]
		if esc, ok := ansiCEscape(c); ok {
			sb.WriteString(esc)
			i++
			continue
		}
		if c < utf8Self {
			if printableASCII(c) {
				sb.WriteByte(c)
			} else {
				fmt.Fprintf(&sb, `\%03o`, c)
			}
			i++
			continue
		}
		if !cLocale {
			if r, size := utf8.DecodeRuneInString(s[i:]); size > 1 && unicode.IsPrint(r) {
				sb.WriteString(s[i : i+size])
				i += size
				continue
			}
		}
		fmt.Fprintf(&sb, `\%03o`, c)
		i++
	}
	sb.WriteByte('\'')
	return sb.String()
}

func ansiCEscape(c byte) (string, bool) {
	switch c {
	case 0x1b:
		return `\E`, true // bash spells escape with a capital E
	case '\a':
		return `\a`, true
	case '\b':
		return `\b`, true
	case '\f':
		return `\f`, true
	case '\n':
		return `\n`, true
	case '\r':
		return `\r`, true
	case '\t':
		return `\t`, true
	case '\v':
		return `\v`, true
	case '\\', '\'':
		return `\` + string(c), true
	}
	return "", false
}

func printableASCII(c byte) bool { return c >= 0x20 && c < 0x7f }

// declValue renders one element of a `${x@A}` or `${x@K}` answer, which
// bash double-quotes rather than single-quotes — `declare -a a=([0]="1")`
// — falling back to `$'…'` for a value that needs it.
func declValue(s string, cLocale bool) string {
	if ansiCShouldQuote(s, cLocale) {
		return ansiCQuote(s, cLocale)
	}
	return doubleQuote(s)
}

// declKey renders an associative array's key the way bash prints one in a
// `declare -p` or `${m[@]@A}` listing: bare unless it holds a character
// that would be read as something else, measured per character (#626).
func declKey(k string, cLocale bool) string {
	if ansiCShouldQuote(k, cLocale) {
		return ansiCQuote(k, cLocale)
	}
	if declKeyIsPlain(k) {
		return k
	}
	return doubleQuote(k)
}

func declKeyIsPlain(k string) bool {
	if k == "" {
		return false
	}
	for i := range len(k) {
		switch c := k[i]; {
		case c >= 'a' && c <= 'z', c >= 'A' && c <= 'Z', c >= '0' && c <= '9':
		case c == '_', c == '-', c == '.', c == '/',
			c == '+', c == ',', c == ':', c == '=', c == '@', c == '%':
			// bash leaves these unquoted wherever they fall.
		case c == '#', c == '~':
			// Plain in the middle of a key and quoted at its head,
			// where one would start a comment and the other a tilde
			// expansion.
			if i == 0 {
				return false
			}
		default:
			return false
		}
	}
	return true
}

// arrayIndexes yields each element of an indexed array with the index it
// is stored at, which is not its position when the array is sparse.
func arrayIndexes(vr Variable) func(func(int, string) bool) {
	return func(yield func(int, string) bool) {
		for i, v := range vr.List {
			idx := i
			if vr.Indexes != nil {
				idx = vr.Indexes[i]
			}
			if !yield(idx, v) {
				return
			}
		}
	}
}

// scalarAssignment answers `${x@A}` for a variable that is not a list:
// bash's string_var_assignment. A variable with attributes prints as a
// `declare` that restates them, one without as a plain assignment, and a
// declared-but-unset variable prints no value at all rather than an empty
// one — `declare -lr VAR; echo ${VAR@A}` is `declare -rl VAR` (measured).
//
// set is whether there is a value to print rather than whether the
// variable exists, which is not the same question: bash reads element
// zero here, so `declare -ia foo=(); echo ${foo@A}` is `declare -ai foo`
// even though foo was assigned.
func (cfg *Config) scalarAssignment(name string, vr Variable, str string, set bool) string {
	flags := vr.Flags()
	hasValue := set
	switch {
	case flags != "" && !hasValue:
		return "declare -" + flags + " " + name
	case flags != "":
		return "declare -" + flags + " " + name + "=" + cfg.quoteReusable(str)
	case !hasValue:
		// No attributes and no value: bash has nothing to restate.
		return ""
	}
	return name + "=" + cfg.quoteReusable(str)
}

// arrayAssignment answers `${a[@]@A}`: bash's array_var_assignment with
// the whole-variable form, `declare -a a=([0]="x" [1]="y")`, rather than
// the scalar `name=value` a per-element answer would build (#647).
func (cfg *Config) arrayAssignment(name string, vr Variable) string {
	prefix, val := cfg.arrayAssignmentParts(name, vr)
	return prefix + val
}

// arrayAssignmentParts is [Config.arrayAssignment] split where bash's own
// protection ends: the prefix is the text bash sprintf'd, which is
// ordinary text a `[@]` answer gets field-split at, and val is the part
// that came from the variable's value, which is protected (#716). The
// name is in the prefix, measured: with `IFS=z` a `zz` array's answer
// splits inside its own name.
func (cfg *Config) arrayAssignmentParts(name string, vr Variable) (prefix, val string) {
	flags := vr.Flags()
	val = cfg.arrayValue(vr)
	if val == "" {
		if !vr.IsSet() {
			// Declared but never assigned: attributes only.
			if flags == "" {
				return "", ""
			}
			return "declare -" + flags + " " + name, ""
		}
		// Set and empty is `()`, which re-reads as an empty array.
		val = "()"
	}
	return "declare -" + flags + " " + name + "=", val
}

// arrayValue renders the parenthesised half of an `${a[@]@A}`. An
// associative array's entries each carry a trailing space, which is
// bash's own spelling — `([k]="v" )` — while an indexed array's are
// separated by one.
func (cfg *Config) arrayValue(vr Variable) string {
	cLocale := cfg.CLocale()
	var sb strings.Builder
	switch vr.Kind {
	case Indexed:
		if len(vr.List) == 0 {
			return ""
		}
		sb.WriteByte('(')
		first := true
		for idx, v := range arrayIndexes(vr) {
			if !first {
				sb.WriteByte(' ')
			}
			first = false
			fmt.Fprintf(&sb, "[%d]=%s", idx, declValue(v, cLocale))
		}
		sb.WriteByte(')')
	case Associative:
		if len(vr.Map) == 0 {
			return ""
		}
		sb.WriteByte('(')
		for _, k := range vr.AssocKeys() {
			fmt.Fprintf(&sb, "[%s]=%s ", declKey(k, cLocale), declValue(vr.Map[k], cLocale))
		}
		sb.WriteByte(')')
	default:
		return ""
	}
	return sb.String()
}

// kvPairs answers `${a[@]@K}`: bash's array_to_kvpair, a single string of
// `key value` pairs with each value quoted for re-reading. An
// associative array trails each pair with a space where an indexed one
// separates them, which is bash's own asymmetry.
func (cfg *Config) kvPairs(vr Variable) string {
	cLocale := cfg.CLocale()
	var sb strings.Builder
	switch vr.Kind {
	case Indexed:
		first := true
		for idx, v := range arrayIndexes(vr) {
			if !first {
				sb.WriteByte(' ')
			}
			first = false
			fmt.Fprintf(&sb, "%d %s", idx, declValue(v, cLocale))
		}
	case Associative:
		for _, k := range vr.AssocKeys() {
			fmt.Fprintf(&sb, "%s %s ", declKey(k, cLocale), declValue(vr.Map[k], cLocale))
		}
	}
	return sb.String()
}

// kvPairList answers `${a[@]@k}`, which is @K's list form: the keys and
// values alternate as separate fields, unquoted, so `"${a[@]@k}"` on a
// two-element array is four words.
func kvPairList(vr Variable) []string {
	var out []string
	switch vr.Kind {
	case Indexed:
		for idx, v := range arrayIndexes(vr) {
			out = append(out, strconv.Itoa(idx), v)
		}
	case Associative:
		for _, k := range vr.AssocKeys() {
			out = append(out, k, vr.Map[k])
		}
	}
	return out
}

// quoteReusable is [quoteReusable] with the locale the config is in,
// since in the C locale a character is a byte (#470).
func (cfg *Config) quoteReusable(s string) string {
	return quoteReusable(s, cfg.CLocale())
}
