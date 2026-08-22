// Copyright (c) 2018, Daniel Martí <mvdan@mvdan.cc>
// See LICENSE for licensing information

package expand

import (
	"cmp"
	"runtime"
	"slices"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"
)

// Environ is the base interface for a shell's environment, allowing it to fetch
// variables by name and to iterate over all the currently set variables.
type Environ interface {
	// Get retrieves a variable by its name. To check if the variable is
	// set, use Variable.IsSet.
	Get(name string) Variable

	// TODO(v4): make Each below a func that returns an iterator.

	// Each iterates over all the currently set variables, calling the
	// supplied function on each variable. Iteration is stopped if the
	// function returns false.
	//
	// The names used in the calls aren't required to be unique or sorted.
	// If a variable name appears twice, the latest occurrence takes
	// priority.
	//
	// Each is required to forward exported variables when executing
	// programs.
	Each(func(name string, vr Variable) bool)
}

// TODO(v4): [WriteEnviron.Set] below is overloaded to the point that correctly
// implementing both sides of the interface is tricky. In particular, some operations
// such as `export foo` or `readonly foo` alter the attributes but not the value,
// and `foo=bar` or `foo=[3]=baz` alter the value but not the attributes.

// WriteEnviron is an extension on Environ that supports modifying and deleting
// variables.
type WriteEnviron interface {
	Environ
	// Set sets a variable by name. If !vr.IsSet(), the variable is being
	// unset; otherwise, the variable is being replaced.
	//
	// The given variable can have the kind [KeepValue] to replace an existing
	// variable's attributes without changing its value at all.
	// This is helpful to implement `readonly foo=bar; export foo`,
	// as the second declaration needs to clearly signal that the value is not modified.
	//
	// An error may be returned if the operation is invalid, such as if the
	// name is empty or if we're trying to overwrite a read-only variable.
	Set(name string, vr Variable) error
}

//go:generate go tool stringer -type=ValueKind

// ValueKind describes which kind of value the variable holds.
// While most unset variables will have an [Unknown] kind, an unset variable may
// have a kind associated too, such as via `declare -a foo` resulting in [Indexed].
type ValueKind uint8

const (
	// Unknown is used for unset variables which do not have a kind yet.
	Unknown ValueKind = iota
	// String describes plain string variables, such as `foo=bar`.
	String
	// NameRef describes variables which reference another by name, such as `declare -n foo=foo2`.
	NameRef
	// Indexed describes indexed array variables, such as `foo=(bar baz)`.
	Indexed
	// Associative describes associative array variables, such as `foo=([bar]=x [baz]=y)`.
	Associative

	// KeepValue is used by [WriteEnviron.Set] to signal that we are changing attributes
	// about a variable, such as exporting it, without changing its value at all.
	KeepValue

	// Deprecated: use [Unknown], as tracking whether or not a variable is set
	// is now done via [Variable.Set].
	// Otherwise it was impossible to describe an unset variable with a known kind
	// such as `declare -A foo`.
	Unset = Unknown
)

// Variable describes a shell variable, which can have a number of attributes
// and a value.
type Variable struct {
	// Set is true when the variable has been set to a value,
	// which may be empty.
	Set bool

	Local    bool
	Exported bool
	ReadOnly bool

	// Global marks a write that must reach the global scope through
	// every function scope in between — `declare -g` (#379). It is a
	// write-time signal like [KeepValue], never stored.
	Global bool

	// Integer marks a variable declared with "declare -i", whose assigned
	// values are evaluated as arithmetic expressions.
	Integer bool

	// CaseMod marks a variable declared with "declare -u", "-l" or "-c",
	// whose assigned values are upper-cased, lower-cased or capitalized
	// (#385). It holds that option's letter, or zero for none.
	CaseMod byte

	// Trace marks a variable declared with "declare -t". bash gives the
	// attribute no meaning of its own for variables — it is carried so
	// that declare -p reports it.
	Trace bool

	// Kind defines which of the value fields below should be used.
	Kind ValueKind

	Str  string            // Used when Kind is String or NameRef.
	List []string          // Used when Kind is Indexed.
	Map  map[string]string // Used when Kind is Associative.

	// MapOrder records the order [Variable.Map]'s keys were assigned
	// in, oldest first, which is what bash's iteration order of an
	// associative array is computed from (#749). A Go map carries no
	// order at all, so it has to be carried beside it.
	//
	// It is advisory: a stale or partial sequence still yields a total,
	// stable order — see assocOrder. Keys it names that Map no longer
	// holds are ignored, and keys Map holds that it does not name sort
	// in at the end.
	MapOrder []string

	// Indexes records the index of each [Variable.List] element when an
	// indexed array is sparse, such as `a=([2]=x [5]=y)`. The indices
	// must be unique, non-negative, sorted, and as many as the List
	// elements. Nil means the array is dense: element i has index i.
	Indexes []int
}

// IsSet reports whether the variable has been set to a value.
// The zero value of a Variable is unset.
func (v Variable) IsSet() bool {
	return v.Set
}

// Declared reports whether the variable has been declared.
// Declared variables may not be set; `export foo` is exported but not set to a value,
// and `declare -a foo` is an indexed array but not set to a value.
func (v Variable) Declared() bool {
	return v.Set || v.Local || v.Exported || v.ReadOnly || v.Integer ||
		v.CaseMod != 0 || v.Trace || v.Kind != Unknown
}

// Flags returns the variable's attribute flags in the order used by bash's
// declare builtin and ${var@a}: type (a/A/n), integer (i), readonly (r),
// exported (x).
func (v Variable) Flags() string {
	var flags []byte
	switch v.Kind {
	case Indexed:
		flags = append(flags, 'a')
	case Associative:
		flags = append(flags, 'A')
	case NameRef:
		flags = append(flags, 'n')
	}
	if v.Integer {
		flags = append(flags, 'i')
	}
	if v.ReadOnly {
		flags = append(flags, 'r')
	}
	if v.Trace {
		flags = append(flags, 't')
	}
	if v.Exported {
		flags = append(flags, 'x')
	}
	// The case-modification letter comes last, which is bash's order:
	// `declare -tux w` prints as -txu (#385).
	if v.CaseMod != 0 {
		flags = append(flags, v.CaseMod)
	}
	return string(flags)
}

// ApplyCaseMod returns s transformed by the variable's -u, -l or -c
// attribute, which bash applies on every assignment (#385).
func (v Variable) ApplyCaseMod(s string) string {
	switch v.CaseMod {
	case 'u':
		return strings.ToUpper(s)
	case 'l':
		return strings.ToLower(s)
	case 'c':
		if s == "" {
			return s
		}
		r, size := utf8.DecodeRuneInString(s)
		return string(unicode.ToUpper(r)) + s[size:]
	}
	return s
}

// String returns the variable's value as a string. In general, this only makes
// sense if the variable has a string value or no value at all.
func (v Variable) String() string {
	switch v.Kind {
	case String:
		return v.Str
	case Indexed:
		if str, ok := v.indexedVal(0); ok {
			return str
		}
	case Associative:
		// nothing to do
	}
	return ""
}

// indexedVal returns the element of an indexed array at index i,
// taking [Variable.Indexes] into account for sparse arrays.
func (v Variable) indexedVal(i int) (string, bool) {
	if v.Indexes != nil {
		if pos, ok := slices.BinarySearch(v.Indexes, i); ok {
			return v.List[pos], true
		}
		return "", false
	}
	if i < len(v.List) {
		return v.List[i], true
	}
	return "", false
}

// indexedKeys returns the index of each element of an indexed array as a
// string, for the sake of expansions like "${!a[@]}".
func (v Variable) indexedKeys() []string {
	keys := make([]string, len(v.List))
	for i := range v.List {
		if v.Indexes != nil {
			keys[i] = strconv.Itoa(v.Indexes[i])
		} else {
			keys[i] = strconv.Itoa(i)
		}
	}
	return keys
}

// AssocKeys returns an associative array's keys in the one order every
// expansion of it must agree on, and AssocValues its values in that same
// order. That order is bash's hash-table order, derived by measurement
// in assocorder.go (#749); every surface that lists the array has to use
// these, since `${!A[@]}` and `${A[@]}` must line up element for element
// — reading a map by parallel key and value lists is what an
// associative array is for. Sorting one by key and the other by *value*
// answers both questions plausibly and pairs the wrong value with every
// key.
func (v Variable) AssocKeys() []string {
	return assocOrder(v.Map, v.MapOrder)
}

// AssocValues returns the values of v.Map in [Variable.AssocKeys] order.
func (v Variable) AssocValues() []string {
	keys := v.AssocKeys()
	vals := make([]string, len(keys))
	for i, k := range keys {
		vals[i] = v.Map[k]
	}
	return vals
}

// The unexported spellings the rest of this package already calls. Kept
// as aliases so that exporting the pair for interp's declare -p and set
// printers did not touch every expansion site.
func (v Variable) assocKeys() []string   { return v.AssocKeys() }
func (v Variable) assocValues() []string { return v.AssocValues() }

// maxNameRefDepth defines the maximum number of times to follow references when
// resolving a variable. Otherwise, simple name reference loops could crash a
// program quite easily.
const maxNameRefDepth = 100

// OuterEnviron is an [Environ] with nested scopes that can answer a name
// from the scope *outside* the innermost one binding it.
//
// It exists for the one shape that needs it: a nameref whose target is
// its own name. bash creates one for `typeset -n v=v` inside a function
// — it warns and declares it anyway (#663) — and resolves it against the
// enclosing scope, so a read through it answers the outer v and the
// reference itself stays a reference. Following it in the scope that
// holds it would loop instead, which is the difference between koi
// answering "inside" and answering the value the function shadowed.
type OuterEnviron interface {
	Environ

	// OuterGet answers name from outside the innermost scope that binds
	// it, or an unset variable when no outer scope has it.
	OuterGet(name string) Variable
}

// Resolve follows a number of nameref variables, returning the last reference
// name that was followed and the variable that it points to.
func (v Variable) Resolve(env Environ) (string, Variable) {
	name := ""
	for range maxNameRefDepth {
		if v.Kind != NameRef {
			return name, v
		}
		if v.Str == "" {
			// A nameref with no target: `declare -n foo` on a variable
			// that was unset. It points at nothing, and bash expands it
			// to nothing. Following it would ask the environment for the
			// variable named "" — which is not a name any shell has, and
			// which the interpreter panics on rather than answering.
			return name, Variable{}
		}
		name = v.Str // keep name for the next iteration
		v = env.Get(name)
		if v.Kind == NameRef && v.Str == name {
			// The variable called name is a reference to itself, so the
			// value lives in the scope outside the one holding it — see
			// [OuterEnviron]. A self-reference cannot exist at the top
			// level, where bash refuses the declaration outright, so
			// there is nothing to answer when no scope encloses it.
			outer, ok := env.(OuterEnviron)
			if !ok {
				return name, Variable{}
			}
			v = outer.OuterGet(name)
		}
	}
	return name, Variable{}
}

// FuncEnviron wraps a function mapping variable names to their string values,
// and implements [Environ]. Empty strings returned by the function will be
// treated as unset variables. All variables will be exported.
//
// Note that the returned Environ's Each method will be a no-op.
func FuncEnviron(fn func(string) string) Environ {
	return funcEnviron(fn)
}

type funcEnviron func(string) string

func (f funcEnviron) Get(name string) Variable {
	value := f(name)
	if value == "" {
		return Variable{}
	}
	return Variable{Set: true, Exported: true, Kind: String, Str: value}
}

func (f funcEnviron) Each(func(name string, vr Variable) bool) {}

// ListEnviron returns an [Environ] with the supplied variables, in the form
// "key=value". All variables will be exported. The last value in pairs is used
// if multiple values are present.
//
// On Windows, where environment variable names are case-insensitive, the
// resulting variable names will all be uppercase.
func ListEnviron(pairs ...string) Environ {
	return listEnviron_(runtime.GOOS == "windows", pairs...)
}

// listEnviron_ implements [ListEnviron], but letting the tests specify
// whether to uppercase all names or not.
func listEnviron_(caseInsensitive bool, pairs ...string) Environ {
	list := slices.Clone(pairs)
	env := listEnviron{caseInsensitive: caseInsensitive}
	slices.SortStableFunc(list, func(a, b string) int {
		isep := strings.IndexByte(a, '=')
		jsep := strings.IndexByte(b, '=')
		if isep < 0 {
			isep = 0
		} else {
			isep += 1
		}
		if jsep < 0 {
			jsep = 0
		} else {
			jsep += 1
		}
		return env.compare(a[:isep], b[:jsep])
	})

	last := ""
	for i := 0; i < len(list); {
		name, _, ok := strings.Cut(list[i], "=")
		if name == "" || !ok {
			// invalid element; remove it
			list = slices.Delete(list, i, i+1)
			continue
		}
		if env.compare(last, name) == 0 {
			// duplicate; the last one wins
			list = slices.Delete(list, i-1, i)
			continue
		}
		last = name
		i++
	}
	env.pairs = list
	return env
}

// listEnviron is a sorted list of "name=value" strings.
type listEnviron struct {
	caseInsensitive bool
	pairs           []string
}

func (l listEnviron) compare(a, b string) int {
	if l.caseInsensitive {
		// This is not particularly efficient, but it does the job.
		// If we had a cmp-compatible version of [strings.EqualFold], we'd use it.
		a = strings.ToUpper(a)
		b = strings.ToUpper(b)
	}
	return strings.Compare(a, b)
}

func (l listEnviron) Get(name string) Variable {
	eqpos := len(name)
	endpos := len(name) + 1
	i, ok := slices.BinarySearchFunc(l.pairs, name, func(pair, name string) int {
		if len(pair) < endpos {
			// Too short; see if we are before or after the name.
			return l.compare(pair, name)
		}
		// Compare the name prefix, then the equal character.
		c := l.compare(pair[:eqpos], name)
		eq := pair[eqpos]
		if c == 0 {
			return cmp.Compare(eq, '=')
		}
		return c
	})
	if ok {
		return Variable{Set: true, Exported: true, Kind: String, Str: l.pairs[i][endpos:]}
	}
	return Variable{}
}

func (l listEnviron) Each(fn func(name string, vr Variable) bool) {
	for _, pair := range l.pairs {
		name, value, ok := strings.Cut(pair, "=")
		if !ok {
			// should never happen; see listEnvironWithUpper
			panic("expand.listEnviron: did not expect malformed name-value pair: " + pair)
		}
		if !fn(name, Variable{Set: true, Exported: true, Kind: String, Str: value}) {
			return
		}
	}
}
