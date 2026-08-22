// Copyright (c) 2017, Daniel Martí <mvdan@mvdan.cc>
// See LICENSE for licensing information

package interp

import (
	"bufio"
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"io/fs"
	"maps"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
	"time"

	"golang.org/x/term"

	"github.com/blairham/koi-shell/internal/shell/expand"
	"github.com/blairham/koi-shell/internal/shell/syntax"
)

// TODO: given the categories below, perhaps this should be more like:
//
//   func IsBuiltin(lang syntax.LangVariant, name string) bool
//
// or perhaps some API that also lets the user iterate through the builtins?
//
// Also, should we move this to the syntax package too?
// It's not a syntactical property strictly speaking,
// but it's also odd to require importing the interp package for it.

// IsBuiltin returns true if the given word is a POSIX Shell
// or Bash builtin.
func IsBuiltin(name string) bool {
	_, ok := builtinNames[name]
	return ok
}

// builtinNames is every builtin koi recognizes, and whether koi actually
// implements it. It is a map rather than the switch statement it replaced
// because three separate surfaces have to agree about what exists -- `type`,
// `compgen -b`, and running the thing -- and when they were free to disagree
// they did: `jobs` was reported by `type` as a builtin, omitted by
// `compgen -b`, and refused when run, which is the disagreement #302 is named
// after.
//
// A false value means the name is a real builtin that koi does not implement
// yet, so `compgen -b` leaves it out rather than advertising something that
// would refuse. The remaining six are all job control -- bg, fg, suspend and
// disown need a foreground/background notion koi does not have without `set
// -m` (#245), and enable and logout are interactive-shell management.
var builtinNames = map[string]bool{
	// POSIX Shell builtins, from section 1.d obtained in September 2025 from:
	// https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_09_01_01
	"alias":   true,
	"bg":      true,
	"cd":      true,
	"command": true,
	"false":   true,
	"fc":      false,
	"fg":      true,
	"getopts": true,
	"hash":    true,
	"jobs":    true,
	"kill":    false,
	"newgrp":  false,
	"pwd":     true,
	"read":    true,
	"true":    true,
	"umask":   false,
	"unalias": true,
	"wait":    true,

	// POSIX Shell special built-ins, obtained in September 2025 from:
	// https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_14
	"break":    true,
	":":        true,
	"continue": true,
	".":        true,
	"eval":     true,
	"exec":     true,
	"exit":     true,
	"export":   true, // NOTE: our parser treats this as a keyword
	"readonly": true, // NOTE: our parser treats this as a keyword
	"return":   true,
	"set":      true,
	"shift":    true,
	"times":    false,
	"trap":     true,
	"unset":    true,

	// Bash built-ins which are not present in POSIX, obtained in September 2025 from:
	// https://man.archlinux.org/man/bash.1.en#SHELL_BUILTIN_COMMANDS
	"source":    true,
	"bind":      false,
	"builtin":   true,
	"caller":    true,
	"compgen":   true,
	"complete":  false,
	"compopt":   false,
	"declare":   true, // NOTE: our parser treats this as a keyword
	"typeset":   true, // NOTE: our parser treats this as a keyword
	"dirs":      true,
	"disown":    true,
	"echo":      true, // TODO: surely this is POSIX? but why is it not in the main POSIX spec page?
	"enable":    true,
	"history":   false,
	"help":      false,
	"let":       true, // NOTE: our parser treats this as a keyword
	"local":     true,
	"logout":    true,
	"mapfile":   true,
	"readarray": true,
	"popd":      true,
	"printf":    true, // TODO: surely this is POSIX? but why is it not in the main POSIX spec page?
	"pushd":     true,
	"shopt":     true,
	"suspend":   false,
	"test":      true,
	"[":         true, // NOTE: an alias for "test", not explicitly listed
	"type":      true,
	"ulimit":    true,
}

// ImplementedBuiltins is the sorted list of builtins this interpreter can
// actually run, and UnimplementedBuiltins its complement: names it recognizes
// as builtins but refuses.
//
// They are exported because the layers above need the same answer. koi wraps
// this interpreter and adds builtins of its own, so "which builtins are there?"
// was being answered from a hand-maintained copy of this list in
// internal/builtins -- which is how `compgen -b` came to omit builtins that
// work and, before this, to omit `jobs` for a different reason than it was
// actually missing (#302). One list, derived, cannot drift from the dispatch
// it describes.
func ImplementedBuiltins() []string { return builtinsWhere(true) }

// UnimplementedBuiltins returns the recognized-but-refused builtins.
func UnimplementedBuiltins() []string { return builtinsWhere(false) }

// RecognizedBuiltins is every name [IsBuiltin] answers true for, sorted:
// what this shell *calls* a builtin, which is the question `type` answers
// and the set `enable -n` accepts.
//
// It is deliberately wider than [ImplementedBuiltins], which answers "what
// can I call" for `compgen -b` (#302). bash makes the same split -- its
// `enable` lists `suspend` in a non-interactive shell where running it
// fails -- and koi needs it because the layer above replaces builtins the
// interpreter recognizes but does not implement (#565): listing only the
// interpreter's own would drop `times`, `kill` and `umask` from `enable`
// while `enable -n times` still worked, so the listing and the acceptance
// disagreed about what exists (#603).
func RecognizedBuiltins() []string {
	names := make([]string, 0, len(builtinNames))
	for name := range builtinNames {
		names = append(names, name)
	}
	slices.Sort(names)
	return names
}

// enableUsage reports an `enable` option error the way bash does: the
// diagnostic carries a location and the usage line following it does not
// (#611), and the status is bash's EX_USAGE.
func (r *Runner) enableUsage(format string, a ...any) exitStatus {
	r.errf(format, a...)
	r.rawErrf("enable: usage: enable [-a] [-dnps] [-f filename] [name ...]\n")
	return exitStatus{code: 2}
}

func builtinsWhere(implemented bool) []string {
	names := make([]string, 0, len(builtinNames))
	for name, impl := range builtinNames {
		if impl == implemented {
			names = append(names, name)
		}
	}
	slices.Sort(names)
	return names
}

// TODO: atoi is duplicated in the expand package.

// atoi is like [strconv.ParseInt](s, 10, 64), but it ignores errors and trims whitespace.
func atoi(s string) int64 {
	s = strings.TrimSpace(s)
	n, _ := strconv.ParseInt(s, 10, 64)
	return n
}

type errBuiltinExitStatus exitStatus

func (e errBuiltinExitStatus) Error() string {
	return fmt.Sprintf("builtin exit status %d", e.code)
}

// Builtin allows [ExecHandlerFunc] implementations to execute any builtin,
// which can be useful for an exec handler to wrap or combine builtin calls.
//
// Note that a non-nil error may be returned in cases where the builtin
// alters the control flow of the runner, even if the builtin did not fail.
// For example, this is the case with `exit 0` or `return`.
func (hc HandlerContext) Builtin(ctx context.Context, args []string) error {
	if hc.kind != handlerKindExec {
		return fmt.Errorf("HandlerContext.Builtin can only be called via an ExecHandlerFunc")
	}
	exit := hc.runner.builtin(ctx, hc.Pos, args[0], args[1:])
	if exit != (exitStatus{}) {
		return errBuiltinExitStatus(exit)
	}
	return nil
}

// DisabledBuiltins returns the names `enable -n` has switched off in this
// session, sorted.
//
// The shell around the interpreter needs the same answer: `compgen -A
// disabled` lists exactly this set and `compgen -A enabled` is its
// complement, and both are answered by koi's own compgen rather than by
// this package's (#603).
func (hc HandlerContext) DisabledBuiltins() []string {
	names := make([]string, 0, len(hc.runner.disabledBuiltins))
	for name, off := range hc.runner.disabledBuiltins {
		if off {
			names = append(names, name)
		}
	}
	slices.Sort(names)
	return names
}

func (r *Runner) builtin(ctx context.Context, pos syntax.Pos, name string, args []string) (exit exitStatus) {
	failf := func(code uint8, format string, args ...any) exitStatus {
		r.errf(format, args...)
		exit.code = code
		return exit
	}
	switch name {
	case ":", "true":
	case "false":
		exit.code = 1
	case "exit":
		switch len(args) {
		case 0:
			exit = r.lastExit
		case 1:
			n, err := strconv.Atoi(args[0])
			if err != nil {
				// bash's wording, which names the argument: koi's
				// "invalid exit status code" is the same fact said a
				// way nothing greps for.
				return failf(2, "exit: %s: numeric argument required\n", args[0])
			}
			exit.code = uint8(n)
		default:
			return failf(1, "exit: too many arguments\n")
		}
		exit.exiting = true
	case "set":
		wasPosix := r.opts[optPosix]
		defer func() {
			if r.opts[optPosix] != wasPosix {
				// POSIXLY_CORRECT and the option are two views of one
				// state in bash: setting the option sets the variable
				// to "y", and turning it off unsets it (#395).
				if r.opts[optPosix] {
					r.setVarString("POSIXLY_CORRECT", "y")
				} else {
					r.delVar("POSIXLY_CORRECT")
				}
			}
		}()
		if len(args) == 0 {
			// POSIX: bare `set` lists the shell's variables, and bash
			// adds its functions after them. koi listed nothing and
			// exited 1, so posix2.tests never reached the four cases
			// that probe the *quoting* of this listing (#394).
			r.setListing()
			break
		}
		if err := Params(args...)(r); err != nil {
			r.errf("set: %v\n", err)
			var ue setUsageError
			if errors.As(err, &ue) {
				// The usage line follows an invalid option letter and
				// not an invalid `-o` name, and it is not a diagnostic,
				// so it carries no location (#611).
				r.rawErrf("set: usage: set [-abefhkmnptuvxBCEHPT] [-o option-name] [--] [-] [arg ...]\n")
			}
			return exitStatus{code: 2}
		}
		r.updateExpandOpts()
	case "shift":
		// Every answer here is bash's, measured (#595), because the two
		// koi had were a crash and a silent loss: `shift -1` indexed a
		// slice at -1, and `shift 3` on two parameters *cleared* them
		// and answered 0 where bash keeps them and answers 1 — which is
		// how an argument-parsing loop carries on believing it consumed
		// what it did not.
		n := 1
		switch len(args) {
		case 0:
		case 1:
			// A whole number, not an arithmetic expression: bash calls
			// `shift 1+1` a numeric-argument error rather than 2.
			n2, err := strconv.Atoi(args[0])
			if err != nil {
				return failf(2, "shift: %s: numeric argument required\n", args[0])
			}
			n = n2
		default:
			// Fatal to the input unit, unlike the other two errors here:
			// `echo pre; shift 1 2; echo same` never prints `same`, and
			// the next line reads $? as 2 (#469's abandonment).
			r.errf("shift: too many arguments\n")
			exit.code = 2
			exit.aborting = true
			return exit
		}
		switch {
		case n < 0:
			return failf(1, "shift: %d: shift count out of range\n", n)
		case n > len(r.Params):
			// Nothing moves, and the status is the only thing that says
			// so — `shift 2` on exactly two parameters still succeeds, so
			// the boundary is *past* the end rather than at it.
			exit.code = 1
		default:
			r.Params = r.Params[n:]
		}
	case "unset":
		vars := true
		funcs := true
		// -n unsets the *reference* rather than what it points at, which
		// is the only way to remove a nameref at all (#277).
		byRef := false
	unsetOpts:
		for i, arg := range args {
			switch arg {
			case "-v":
				funcs = false
			case "-f":
				vars = false
			case "-n":
				byRef, funcs = true, false
			default:
				args = args[i:]
				break unsetOpts
			}
		}

		for _, arg := range args {
			// Without -n, unsetting a nameref unsets its *target* and
			// leaves the reference in place. That is bash's rule and it
			// is the opposite of what koi did, so `unset foo` removed the
			// nameref and kept the variable it pointed at — after which
			// every later use of the name was an ordinary variable and
			// the rest of a script drifted (#277).
			if base := arg; vars {
				if name, _, ok := cutElemSubscript(base); ok {
					base = name
				}
				if unsettableNever[base] {
					// Four of the shell's own arrays refuse `unset`
					// outright, with no "readonly variable" behind it:
					// bash answers `unset: BASH_SOURCE: cannot unset` at
					// 1 for BASH_SOURCE, BASH_LINENO, BASH_ARGV and
					// BASH_ARGC, for -v and -n alike and for an element
					// as well as the whole array, while FUNCNAME,
					// DIRSTACK and GROUPS *are* unsettable and keep
					// #547's one-way rule (#691). koi accepted all of
					// them, so a library's `${BASH_SOURCE[0]}` location
					// helper could be silently disarmed by an unrelated
					// unset earlier in the same shell.
					r.errf("unset: %s: cannot unset\n", base)
					exit.code = 1
					continue
				}
			}
			viaRef := false
			if _, _, isElem := cutElemSubscript(arg); vars && !byRef && !isElem {
				if vr := r.lookupVar(arg); vr.Kind == expand.NameRef && vr.Str != "" {
					arg, viaRef = vr.Str, true
				}
			}
			if name, sub, ok := cutElemSubscript(arg); vars && ok {
				// The status is the builtin's own: setting r.exit.code
				// here would be overwritten by the exit this returns,
				// so `unset x[2]` on a scalar answered 0 — a refusal
				// reported and then reported as success (#610).
				if !r.unsetElem(name, sub, viaRef) {
					exit.code = 1
				}
			} else if vars && r.lookupVar(arg).IsSet() {
				if r.lookupVar(arg).ReadOnly {
					// The refusal is the command's, and it has to be
					// visible as one: koi reported the variable's state
					// and answered 0, so `unset R || die` was told the
					// unset had worked (#535). bash names the builtin
					// and what it could not do.
					r.errf("unset: %s: cannot unset: readonly variable\n", arg)
					exit.code = 1
					continue
				}
				r.delVar(arg)
				r.unsetDynamicVar(arg)
			} else if _, ok := r.Funcs[arg]; ok && funcs {
				if r.readonlyFuncs[arg] {
					// The function half of #535's rule: report and
					// answer 1 rather than reporting and answering 0,
					// and carry on to the next name — `unset -f a b c`
					// with a readonly `b` removes a and c (#615).
					r.errf("unset: %s: cannot unset: readonly function\n", arg)
					exit.code = 1
					continue
				}
				delete(r.Funcs, arg)
			} else if vars && dynamicVars[arg] {
				// A computed variable can be *listed* without being set —
				// FUNCNAME outside a function is bash's `declare -a
				// FUNCNAME` (#616) — so the unset is recorded whether or
				// not there was a value to remove. Without this the name
				// stayed in `declare -a` after a script had unset it,
				// which is #547's one-way rule failing at the reader that
				// enumerates rather than the one that expands.
				r.unsetDynamicVar(arg)
			}
			if vars && arg == "GLOBIGNORE" {
				// bash turns dotglob off on `unset GLOBIGNORE` even when
				// the variable was never set (#375); delVar covers the
				// set case, this covers the rest.
				r.opts[optDotGlob] = false
				r.updateExpandOpts()
			}
		}
	case "echo":
		// xpg_echo makes escape interpretation echo's default, which is
		// the mode bash's own tests put it in (#604). `-e` and `-E` still
		// override it — except with posix mode on as well, where bash's
		// echo recognizes no options at all and `echo -n x` prints the
		// flag as an operand. Measured against bash 5.3, both ways.
		xpgEcho := r.opts[optXpgEcho]
		newline, doExpand := true, xpgEcho
		readOpts := !(xpgEcho && r.opts[optPosix])
	echoOpts:
		for readOpts && len(args) > 0 {
			// The letters cluster: `echo -ne` is -n and -e, and koi
			// read only the exact spellings, so it printed "-ne" as an
			// operand (#399) — which is the whole of strip.tests.
			arg := args[0]
			if len(arg) < 2 || arg[0] != '-' {
				break echoOpts
			}
			// The whole cluster is read before any of it is applied: a
			// cluster carrying any other letter is not an option at
			// all, so `echo -nx` prints `-nx` *and* its newline. The
			// first cut applied the n before rejecting the x, which the
			// builtins matrix caught.
			nextNewline, nextExpand := newline, doExpand
			for i := 1; i < len(arg); i++ {
				switch arg[i] {
				case 'n':
					nextNewline = false
				case 'e':
					nextExpand = true
				case 'E':
					nextExpand = false
				default:
					break echoOpts
				}
			}
			newline, doExpand = nextNewline, nextExpand
			args = args[1:]
		}
		// One logical line, one write. Background jobs are goroutines
		// sharing this writer rather than separate processes with their
		// own fds, so an echo assembled from a write per argument lets
		// another job's output land mid-line -- "done:2done:3" (#301).
		// bash is atomic here because a short echo is a single write(2),
		// and building the line first is how we get the same guarantee.
		var line strings.Builder
		for i, arg := range args {
			if i > 0 {
				line.WriteString(" ")
			}
			if doExpand {
				arg, _, _ = expand.Format(r.ecfg, arg, nil)
			}
			line.WriteString(arg)
		}
		if newline {
			line.WriteString("\n")
		}
		r.out(line.String())
	case "printf":
		if len(args) == 0 {
			return failf(2, "usage: printf format [arguments]\n")
		}
		format, args := args[0], args[1:]
		// Accumulated for the same reason as echo above: a format that
		// recycles over its arguments would otherwise be one write per
		// cycle, and a concurrent job could interleave between them.
		var out strings.Builder
		for {
			s, n, err := expand.Format(r.ecfg, format, args)
			if err != nil {
				return failf(1, "%v\n", err)
			}
			out.WriteString(s)
			args = args[n:]
			if n == 0 || len(args) == 0 {
				break
			}
		}
		r.out(out.String())
	case "break", "continue":
		if !r.inLoop {
			return failf(0, "%s is only useful in a loop\n", name)
		}
		enclosing := &r.breakEnclosing
		if name == "continue" {
			enclosing = &r.contnEnclosing
		}
		// `--` ends the options, which every builtin taking arguments
		// accepts and these two rejected with a usage error (#411).
		if len(args) > 0 && args[0] == "--" {
			args = args[1:]
		}
		switch len(args) {
		case 0:
			*enclosing = 1
		case 1:
			if n, err := strconv.Atoi(args[0]); err == nil {
				*enclosing = n
				break
			}
			fallthrough
		default:
			return failf(2, "usage: %s [n]\n", name)
		}
	case "pwd":
		// `set -o physical` makes resolving the default, which is what
		// -P asks for one call at a time.
		evalSymlinks := r.opts[optPhysical]
		for len(args) > 0 {
			switch args[0] {
			case "-L":
				evalSymlinks = false
			case "-P":
				evalSymlinks = true
			default:
				return failf(2, "invalid option: %q\n", args[0])
			}
			args = args[1:]
		}
		pwd := r.envGet("PWD")
		if evalSymlinks {
			var err error
			pwd, err = filepath.EvalSymlinks(pwd)
			if err != nil {
				exit.fatal(err) // perhaps overly dramatic?
				return exit
			}
		}
		r.outf("%s\n", pwd)
	case "cd":
		if r.opts[optRestricted] {
			return failf(1, "cd: restricted\n")
		}
		// -L and -P choose whether a symlinked path is kept as written
		// or resolved (#391). koi rejected both with a usage error and
		// exit 2, which cost whole suite files their content: a script
		// opening with `cd -P /` never changed directory at all.
		physical := false
		for len(args) > 0 && (args[0] == "-L" || args[0] == "-P" || args[0] == "--") {
			if args[0] == "--" {
				args = args[1:]
				break
			}
			physical = args[0] == "-P"
			args = args[1:]
		}
		var path string
		switch len(args) {
		case 0:
			path = r.envGet("HOME")
		case 1:
			path = args[0]

			// replicate the commonly implemented behavior of `cd -`
			// ref: https://www.man7.org/linux/man-pages/man1/cd.1p.html#OPERANDS
			if path == "-" {
				path = r.envGet("OLDPWD")
				r.outf("%s\n", path)
			} else if found, ok := r.cdPathLookup(ctx, path); ok {
				// A CDPATH hit prints where it landed, which is how a
				// script can tell the search happened.
				path = found
				r.outf("%s\n", path)
			}
		default:
			return failf(2, "cd: too many arguments\n")
		}
		if physical {
			if resolved, err := filepath.EvalSymlinks(r.absPath(path)); err == nil {
				path = resolved
			}
		}
		exit.code = r.changeDir(ctx, "cd", path)
	case "wait":
		anyJob := false
		pidVar := ""
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-n":
				anyJob = true
			case "-p":
				if pidVar = fp.value(); pidVar == "" {
					return failf(2, "wait: -p: option requires an argument\n")
				}
			case "-f":
				// -f asks to wait for the job to *terminate* rather
				// than to change state, which is the only thing koi's
				// wait does: its jobs are goroutines and cannot stop
				// (#397). Accepted rather than refused, because
				// refusing it made `wait -f %1` a usage error where
				// bash simply waits.
			default:
				return failf(2, "wait: invalid option %q\n", flag)
			}
		}
		args = fp.args()
		// bash leaves the variable *unset* unless a single job's status is
		// what comes back, so a script can tell "job N finished" from
		// "there was nothing to wait for" without reading $? twice.
		if pidVar != "" && r.lookupVar(pidVar).IsSet() {
			r.delVar(pidVar)
		}
		if anyJob {
			return r.waitAny(args, pidVar)
		}
		if len(args) == 0 {
			// Note that "wait" without arguments always returns exit status zero.
			for i := range r.bgProcs {
				if r.bgProcs[i].disowned {
					// Forgotten by `disown`, so not waited for (#397).
					continue
				}
				<-r.bgProcs[i].done
				r.bgProcs[i].reaped = true
			}
			break
		}
		for _, arg := range args {
			i, ok := r.bgIndex(arg)
			if !ok {
				if strings.HasPrefix(arg, "%") {
					// A jobspec that names nothing is a different
					// error from a pid that is not ours, and carries
					// bash's 127 rather than 1 (#397).
					return failf(127, "wait: %s: no such job\n", arg)
				}
				return failf(1, "wait: pid %s is not a child of this shell\n", arg)
			}
			<-r.bgProcs[i].done
			r.bgProcs[i].reaped = true
			exit = *r.bgProcs[i].exit
			if pidVar != "" {
				r.setVarString(pidVar, arg)
			}
		}
	case "builtin":
		if len(args) < 1 {
			break
		}
		if !IsBuiltin(args[0]) || r.disabledBuiltins[args[0]] {
			// bash says which name it refused; koi failed silently, so
			// `builtin ls` looked like a builtin that produced nothing.
			//
			// A name `enable -n` switched off gets the same answer, which
			// is the one place `builtin` and `command` part company for a
			// disabled name: `command printf` runs /usr/bin/printf while
			// `builtin printf` refuses, because `builtin` asks for the
			// shell's version and there no longer is one (#603).
			return failf(1, "builtin: %s: not a shell builtin\n", args[0])
		}
		// The name is checked before the call seam and dispatched after
		// it: what makes something a builtin is the interpreter's list,
		// but what *runs* may be the embedder's replacement (#565).
		exit = r.callSkippingFuncs(ctx, pos, args)
	case "type":
		anyNotFound := false
		mode := ""
		all, noFuncs := false, false
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-a":
				// -a reports *every* match rather than the first, which
				// is how a script sees that a builtin is shadowing the
				// program it meant (#411). koi answered "NOT
				// IMPLEMENTED" at status 3.
				all = true
			case "-f":
				// -f suppresses the function lookup.
				noFuncs = true
			case "-p", "-P", "-t":
				mode = flag
			default:
				return failf(2, "type: invalid option %q\n", flag)
			}
		}
		args := fp.args()
		for _, arg := range args {
			if mode == "-p" || mode == "-P" {
				// -p prints the disk file only when the name is not
				// something the shell would run instead; -P forces the
				// PATH search. koi treated them as the same, so
				// `type -p echo` named /bin/echo where bash — which
				// would run its builtin — prints nothing (#411).
				if mode == "-p" && (syntax.IsKeyword(arg) || IsBuiltin(arg) || r.Funcs[arg] != nil ||
					(r.opts[optExpandAliases] && r.alias[arg].text != "")) {
					continue
				}
				if paths := r.lookPathAll(arg, all); len(paths) > 0 {
					for _, path := range paths {
						r.outf("%s\n", path)
					}
				} else {
					anyNotFound = true
				}
				continue
			}
			found := false
			if syntax.IsKeyword(arg) {
				if mode == "-t" {
					r.out("keyword\n")
				} else {
					r.outf("%s is a shell keyword\n", arg)
				}
				if !all {
					continue
				}
				found = true
			}
			if als, ok := r.alias[arg]; ok && r.opts[optExpandAliases] {
				buf := als.text
				if mode == "-t" {
					r.out("alias\n")
				} else {
					r.outf("%s is aliased to `%s'\n", arg, buf)
				}
				if !all {
					continue
				}
				found = true
			}
			if body, ok := r.Funcs[arg]; ok && !noFuncs {
				if mode == "-t" {
					r.out("function\n")
				} else {
					// bash prints the definition under the verdict,
					// which is what `type` is for when the name is a
					// function: naming it without showing it leaves the
					// caller to run declare -f anyway (#386).
					r.outf("%s is a function\n", arg)
					r.printFuncDef(arg, body)
				}
				if !all {
					continue
				}
				found = true
			}
			if IsBuiltin(arg) && !r.disabledBuiltins[arg] {
				if mode == "-t" {
					r.out("builtin\n")
				} else {
					r.outf("%s is a shell builtin\n", arg)
				}
				if !all {
					continue
				}
				found = true
			}
			if paths := r.lookPathAll(arg, all); len(paths) > 0 {
				for _, path := range paths {
					switch {
					case mode == "-t":
						r.out("file\n")
					case r.hashTable[arg] == path:
						// bash says where a hashed name came from,
						// which is how you see a `hash -p` pin.
						r.outf("%s is hashed (%s)\n", arg, path)
					default:
						r.outf("%s is %s\n", arg, path)
					}
				}
				continue
			}
			if found {
				continue
			}
			if mode != "-t" {
				r.errf("type: %s: not found\n", arg)
			}
			anyNotFound = true
		}
		if anyNotFound {
			exit.code = 1
		}
	case "hash":
		// The table `hash -p` writes is consulted before a PATH search,
		// which is how a script points a name at a specific program
		// (#411). koi accepted the line and did nothing with it, so the
		// name still resolved by PATH — or not at all.
		//
		// -l, -t and -d were accepted and ignored on top of that, so
		// `hash -t cmd` — the way a script asks where a name resolved —
		// printed the whole table and answered 0 for a name that was
		// not in it.
		hashUsage := func(format string, a ...any) exitStatus {
			if format != "" {
				r.errf(format, a...)
			}
			// The usage line stands on its own and is not a diagnostic,
			// so it carries no location (#611).
			r.rawErrf("hash: usage: hash [-lr] [-p pathname] [-dt] [name ...]\n")
			return exitStatus{code: 2}
		}
		reset, remember, pinned := false, "", false
		del, terse, listing := false, false, false
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-r":
				reset = true
			case "-p":
				if !fp.hasValue() {
					return hashUsage("hash: -p: option requires an argument\n")
				}
				remember, pinned = fp.value(), true
			case "-l":
				listing = true
			case "-t":
				terse = true
			case "-d":
				del = true
			default:
				return hashUsage("hash: %s: invalid option\n", flag)
			}
		}
		args := fp.args()
		if reset {
			// -r wins wherever it appears: `hash -l -r` clears and
			// prints nothing, measured.
			r.hashTable = nil
			break
		}
		if pinned && r.opts[optRestricted] {
			return failf(1, "hash: %s: restricted\n", remember)
		}
		if pinned {
			if len(args) == 0 {
				return hashUsage("")
			}
			// A path that does not exist is fine — that is how a script
			// pins a name ahead of building the program — but a
			// directory is refused, measured.
			if info, err := r.stat(ctx, remember); err == nil && info.IsDir() {
				return failf(1, "hash: %s: %s\n", remember, reasonIsDir)
			}
			if r.hashTable == nil {
				r.hashTable = map[string]string{}
			}
			for _, name := range args {
				r.hashTable[name] = remember
			}
			break
		}
		if len(args) == 0 {
			if len(r.hashTable) == 0 {
				if listing {
					// `hash -l` on an empty table prints nothing at all,
					// since its output is meant to be replayed.
					break
				}
				// On stdout, not stderr: measured.
				r.outf("hash: hash table empty\n")
				break
			}
			if !listing {
				r.outf("hits\tcommand\n")
			}
			for _, name := range slices.Sorted(maps.Keys(r.hashTable)) {
				if listing {
					r.outf("builtin hash -p %s %s\n", r.hashTable[name], name)
					continue
				}
				r.outf("   0\t%s\n", r.hashTable[name])
			}
			break
		}
		for _, name := range args {
			switch {
			case terse:
				// -t queries the table and never searches PATH; -l
				// changes what it prints into the re-runnable form.
				// With more than one name each answer is labelled, so a
				// caller can tell them apart. `-dt` prints rather than
				// deletes, measured.
				path, ok := r.hashTable[name]
				if !ok {
					r.errf("hash: %s: not found\n", name)
					exit.code = 1
					continue
				}
				switch {
				case listing:
					r.outf("builtin hash -p %s %s\n", path, name)
				case len(args) > 1:
					r.outf("%s\t%s\n", name, path)
				default:
					r.outf("%s\n", path)
				}
			case del:
				if _, ok := r.hashTable[name]; !ok {
					r.errf("hash: %s: not found\n", name)
					exit.code = 1
					continue
				}
				delete(r.hashTable, name)
			default:
				// A bare `hash name` *records* the lookup rather than
				// querying it, which is what makes `hash cmd` at the top
				// of a script a cheap existence check. It searches PATH
				// whatever the table already says, and a search that
				// fails leaves the name unhashed — so `hash e1` on a
				// pinned `e1` that PATH does not have drops the pin.
				delete(r.hashTable, name)
				path, err := LookPathDir(r.Dir, r.writeEnv, name)
				if err != nil {
					r.errf("hash: %s: not found\n", name)
					exit.code = 1
					continue
				}
				if r.hashTable == nil {
					r.hashTable = map[string]string{}
				}
				r.hashTable[name] = path
			}
		}

	case "logout":
		// A non-login shell refuses, naming the command that does work
		// (#427). koi answered "unsupported builtin", which reads as
		// koi lacking the builtin rather than as the shell not being a
		// login shell — and the two want different fixes from whoever
		// hits it.
		//
		// The login case belongs to the shell around the interpreter,
		// which owns whether it is a login session; here it is the
		// refusal that matters, since that is what a script sees.
		return failf(1, "logout: not login shell: use `exit'\n")

	case "enable":
		// `enable -n name` turns a builtin off, so the name resolves on
		// PATH like any other command. koi refused the whole builtin,
		// which made an ordinary line in a test script fatal (#411) --
		// and then took none of the other options while accepting `-n`
		// and *ignoring* it, so a script that disabled a builtin to
		// reach the program behind it got the builtin anyway, with
		// nothing printed (#603).
		//
		// The branch order below is bash's own (builtins/enable.def) and
		// is not the order the options are documented in: a listing wins
		// over -f and -d, `-f` wins over `-d`, and only names with none
		// of the three switch a builtin on or off. So `enable -dp test`
		// lists where `enable -d test` refuses, which no reading of the
		// manual would predict.
		disable, listAll, listSpecial := false, false, false
		print, dynamic, haveFilename := false, false, false
		var names []string
		fp := flagParser{remaining: args}
		for fp.more() {
			if fp.current == "" && strings.HasPrefix(fp.remaining[0], "+") {
				// bash's getopt takes no `+` word here, so one is an
				// operand and ends the options: `enable +x` answers
				// `+x: not a shell builtin`. #556 measured the same rule
				// for the completion builtins, where `+o` belongs to
				// compopt alone.
				break
			}
			switch flag := fp.flag(); flag {
			case "-n":
				disable = true
			case "-a":
				listAll = true
			case "-p":
				print = true
			case "-s":
				listSpecial = true
			case "-d":
				dynamic = true
			case "-f":
				if fp.current == "" && len(fp.remaining) == 0 {
					return r.enableUsage("enable: -f: option requires an argument\n")
				}
				// The object is read only to be refused below, so its
				// name is consumed and dropped.
				fp.value()
				haveFilename = true
			case "-":
				// A lone dash is a name in bash rather than an option,
				// and gets the ordinary "not a shell builtin".
				names = append(names, flag)
			default:
				return r.enableUsage("enable: %s: invalid option\n", flag)
			}
		}
		names = append(names, fp.args()...)
		if r.opts[optRestricted] && (haveFilename || dynamic) {
			// A restricted shell cannot load or unload a builtin at all,
			// checked before anything else -- so even the listing forms
			// of -d and -f are refused (#398).
			return failf(1, "enable: restricted\n")
		}
		switch {
		case len(names) == 0 || print:
			for _, name := range RecognizedBuiltins() {
				if listSpecial && !isSpecialBuiltin(name) {
					continue
				}
				off := r.disabledBuiltins[name]
				switch {
				case off && (listAll || disable):
					r.outf("enable -n %s\n", name)
				case off || disable:
					// A plain listing shows what is enabled; `-n` alone
					// shows only what is off.
				default:
					r.outf("enable %s\n", name)
				}
			}
		case haveFilename:
			// `-f` loads a builtin from a shared object built against
			// bash's own internals, so there is nothing koi could open
			// even if Go could dlopen it. This is bash's *own* wording
			// for the case, printed by a bash compiled without dlopen
			// support, down to the EX_USAGE status -- which is the
			// honest refusal, where "invalid option" would read as koi
			// not knowing the flag (#603).
			return failf(2, "enable: dynamic loading not available\n")
		case dynamic:
			// `-d` removes a builtin that `-f` loaded, so in koi it can
			// only ever refuse -- and bash refuses a statically built
			// builtin with the same two answers, so these match rather
			// than approximate.
			for _, name := range names {
				if !IsBuiltin(name) {
					r.errf("enable: %s: not a shell builtin\n", name)
				} else {
					r.errf("enable: %s: not dynamically loaded\n", name)
				}
				exit.code = 1
			}
		default:
			for _, name := range names {
				if !IsBuiltin(name) {
					r.errf("enable: %s: not a shell builtin\n", name)
					exit.code = 1
					continue
				}
				if disable {
					if r.disabledBuiltins == nil {
						r.disabledBuiltins = map[string]bool{}
					}
					r.disabledBuiltins[name] = true
					continue
				}
				if r.opts[optRestricted] && r.disabledBuiltins[name] {
					// Turning a builtin back on is unrestricted; putting
					// one back that was switched off is not, because a
					// restricted shell's rule is about what it can reach
					// and `enable -n` is how a name reaches PATH.
					return failf(1, "enable: restricted\n")
				}
				delete(r.disabledBuiltins, name)
			}
		}
	case "eval":
		src := strings.Join(args, " ")
		// Read as bash reads (#276): what parsed before the error runs,
		// and only then is the error reported. `eval "$(tool init)"` is
		// the shape that matters — one construct koi cannot read at the
		// bottom of a generated hook used to discard the whole hook.
		stmts, perr := ParseAsRead(strings.NewReader(src), "")
		// The string is numbered as if it were spliced in where the
		// eval stands, which is how bash numbers it: `eval` on line 2
		// reports its string's second line as line 3, for $LINENO and
		// for a diagnostic's location alike (#571).
		restore := r.shiftLines(pos.Line())
		r.stmts(ctx, stmts)
		restore()
		if perr != nil && !r.exit.exiting {
			return failf(SyntaxErrorStatus, "eval: %v\n", perr)
		}
		exit = r.exit
	case "source", ".":
		// `-p path` searches an explicit colon-separated list instead of
		// $PATH, and searches it whether or not `sourcepath` is on — the
		// spelling `. [-p path] filename` in bash's own usage line, and a
		// whole section of its source8.sub. koi read the `-p` as the
		// filename, so every one of those lines answered `-p: No such
		// file or directory`.
		usage := func(format string, a ...any) exitStatus {
			r.errf(format, a...)
			// The usage line is not a diagnostic and carries no location,
			// which is the split #611 drew for every other builtin.
			r.rawErrf("%s: usage: %s [-p path] filename [arguments]\n", name, name)
			return exitStatus{code: 2}
		}
		srcPath, havePath := "", false
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-p":
				if !fp.hasValue() {
					return usage("%s: -p: option requires an argument\n", name)
				}
				// Last one wins: `. -p a -p b f` searches b, measured.
				srcPath, havePath = fp.value(), true
			default:
				return usage("%s: %s: invalid option\n", name, flag)
			}
		}
		args := fp.args()
		if len(args) == 0 {
			// bash's wording, in place of koi's `source: need filename`.
			return usage("%s: filename argument required\n", name)
		}
		if r.opts[optRestricted] && strings.ContainsRune(args[0], '/') {
			// A restricted shell may source by name but not by path,
			// which is what keeps the search inside PATH (#398).
			return failf(1, "%s: %s: restricted\n", name, args[0])
		}
		path := args[0]
		// A name with a slash in it is used as given rather than
		// searched for, in every one of the three forms below.
		if !strings.ContainsRune(args[0], '/') {
			// Which list is searched and whether the current directory is
			// a fallback when it runs out are two independent answers,
			// which is why they are two variables. Measured against bash
			// 5.3 in all four combinations:
			//
			//   -p path      that list, and no fallback
			//   sourcepath   decides whether $PATH is searched at all
			//   posix        removes the fallback
			//
			// So posix mode with sourcepath off finds a bare name
			// *nowhere*. `shopt -u sourcepath` is the half koi accepted
			// and ignored: a script that turned the search off still got
			// a file out of $PATH, silently.
			searchPath, search, fallBackToCwd := srcPath, havePath, false
			if !havePath {
				searchPath, search = r.envGet("PATH"), r.opts[optSourcePath]
				fallBackToCwd = !r.opts[optPosix]
			}
			if !search && !fallBackToCwd {
				return failf(1, "%s: %s: file not found\n", name, args[0])
			}
			if search {
				// A candidate that is missing, unreadable or a directory
				// is *skipped* rather than reported, so the whole list
				// running out is one error — and when there is no
				// fallback it is worded differently from the plain
				// form's strerror message, which is how bash says "I
				// searched and did not find it".
				found := false
				for elem := range strings.SplitSeq(searchPath, ":") {
					if elem == "" {
						// An empty element means the current directory,
						// so `. -p '' f` is `. ./f`.
						elem = "."
					}
					cand := filepath.Join(elem, args[0])
					if info, err := r.stat(ctx, cand); err != nil || info.IsDir() {
						continue
					}
					if r.access(ctx, cand, AccessRead) != nil {
						continue
					}
					path, found = cand, true
					break
				}
				if !found && !fallBackToCwd {
					return failf(1, "%s: %s: file not found\n", name, args[0])
				}
			}
			// Falling back leaves the name as given, so the open handler
			// still gets a chance at files it manages (eg: a virtual
			// filesystem) and the error names the file as it was written.
		}
		f, err := r.open(ctx, path, os.O_RDONLY, 0, false)
		if err != nil {
			// bash names the file the way it was written and uses
			// strerror's wording, without a builtin prefix. koi printed
			// Go's error, so a missing file came back as `source: open
			// /Users/me/work/x: no such file or directory` (#569).
			return failf(1, "%s: %s\n", args[0], openReason(err))
		}
		defer f.Close()
		// A directory opens fine and fails on the first read, which
		// answered with Go's wording and status 2. bash refuses it here,
		// naming the builtin as it was called (`source` or `.`).
		if statter, ok := f.(interface{ Stat() (fs.FileInfo, error) }); ok {
			if info, serr := statter.Stat(); serr == nil && info.IsDir() {
				return failf(1, "%s: %s: is a directory\n", name, args[0])
			}
		}
		// Read and run a line at a time, the way bash reads a script: a
		// sourced file that turns on `set -o posix` changes how the rest
		// of itself is parsed (#450), and only a reader which runs as it
		// reads can do that.
		sr := NewScriptReader(f, path, r.ParserOptions()...)

		// Keep the current versions of some fields we might modify.
		oldParams := r.Params
		oldSourceSetParams := r.sourceSetParams
		oldInSource := r.inSource

		// If we run "source file args...", set said args as parameters.
		// Otherwise, keep the current parameters.
		sourceArgs := len(args[1:]) > 0
		if sourceArgs {
			r.Params = args[1:]
			r.sourceSetParams = false
		}
		// We want to track if the sourced file explicitly sets the
		// parameters.
		r.sourceSetParams = false
		r.inSource = true // know that we're inside a sourced script.
		// A `source` is its own frame, so a library's own top level names
		// itself in BASH_SOURCE and a function it defines carries that
		// file with it. The line is where the `source` was written, which
		// is what BASH_LINENO reports for the frame below.
		// BASH_SOURCE reports the path as it was written, not as it was
		// resolved: `. ./lib.sh` names `./lib.sh`, which is what bash says
		// and what a library's own `dirname "${BASH_SOURCE[0]}"` expects.
		// Only a bare name — the PATH-searched form — reports where it was
		// actually found, since the name alone would not lead anyone back
		// to the file.
		sourceName := args[0]
		if !strings.ContainsRune(sourceName, filepath.Separator) {
			sourceName = path
		}
		popFrame := r.pushFrame(callFrame{
			name:     sourceFrameName,
			source:   sourceName,
			callLine: pos.Line(),
		})
		// BASH_COMMAND is the `source` again once the file is done, not
		// whatever the file ran last (#614) — measured, and it is what
		// the RETURN trap below reads. A function does not restore it,
		// which is why this is here and not in the frame machinery. Put
		// back only when some trap could read it, on the same reasoning
		// as publishing it at all: the variable exists for a reader
		// that only exists inside a trap.
		oldCommandVar := r.lookupVar(shellCommandVar)
		perr := r.runReading(ctx, sr)
		if r.anyTrapSet() {
			r.setVar(shellCommandVar, oldCommandVar)
		}
		popFrame()
		// A sourced file's return fires RETURN too, and unlike a
		// function it inherits the trap without needing "functrace".
		//
		// Fired *after* the frame is popped, which is the opposite of a
		// function and is bash's, measured both ways: the action sees
		// the caller's FUNCNAME and BASH_SOURCE, and `$LINENO` is the
		// line the `source` was written on rather than anything inside
		// the file. So `. ./lib.sh` inside a function reports that
		// function and that line — a cleanup handler naming where the
		// library came from, which is the only location a caller of
		// `source` could act on.
		r.runReturnTrap(ctx, pos.Line())

		// If we modified the parameters and the sourced file didn't
		// explicitly set them, we restore the old ones.
		if sourceArgs && !r.sourceSetParams {
			r.Params = oldParams
		}
		r.sourceSetParams = oldSourceSetParams
		r.inSource = oldInSource

		exit = r.exit
		exit.returning = false
		// The status of a sourced file that would not parse is the
		// syntax error's, not that of the last statement that did run —
		// and an `exit` inside it means bash never read far enough to
		// find the error at all.
		if perr != nil && !exit.exiting {
			return failf(SyntaxErrorStatus, "source: %v\n", perr)
		}
	case "[":
		if len(args) == 0 || args[len(args)-1] != "]" {
			return failf(2, "%v: [: missing matching ]\n", pos)
		}
		args = args[:len(args)-1]
		fallthrough
	case "test":
		parseErr := false
		p := testParser{
			rem: args,
			err: func(err error) {
				r.errf("%v: %v\n", pos, err)
				parseErr = true
			},
		}
		p.next()
		expr := p.classicOr("[")
		if parseErr {
			exit.code = 2
			return exit
		}
		r.testCallName = name
		falsy := r.bashTest(ctx, expr, true) == ""
		r.testCallName = ""
		// An operand error is status 2 and outranks the true/false
		// answer: `test 4+3 -eq 7` is neither true nor false (#401).
		if r.exit.code == 2 {
			exit.code = 2
			r.exit.code = 0
			return exit
		}
		exit.oneIf(falsy)
	case "exec":
		if r.opts[optRestricted] && len(args) > 0 {
			return failf(1, "exec: restricted\n")
		}
		// TODO: Consider unix.Exec, i.e. actually replacing
		// the process. It's in theory what a shell should do,
		// but in practice it would kill the entire Go process
		// and it's not available on Windows.
		argv0 := ""
		login, clearEnv := false, false
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-a":
				if len(fp.remaining) == 0 {
					return failf(2, "exec: -a: option requires an argument\n")
				}
				argv0 = fp.value()
			case "-l":
				login = true
			case "-c":
				clearEnv = true
			default:
				return failf(2, "exec: invalid option %q\n", flag)
			}
		}
		args := fp.args()
		if len(args) == 0 {
			// "exec" on its own keeps this statement's redirections open. Any
			// flags then have nothing to apply to, as in bash.
			r.keepRedirs = true
			break
		}
		if argv0 == "" {
			argv0 = args[0]
		}
		if login {
			// A login shell is told an argv[0] prefixed with "-".
			argv0 = "-" + argv0
		}
		r.exit.exiting = true
		if argv0 == args[0] {
			argv0 = "" // nothing to override
		}
		r.execWith(ctx, pos, argv0, clearEnv, args)
		exit = r.exit
	case "command":
		show, verbose, defPath := false, false, false
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-v":
				show = true
			case "-V":
				// The prose form of -v, which is what a script prints
				// when it wants to tell a human what it found (#411).
				show, verbose = true, true
			case "-p":
				// Search the *default* PATH rather than the session's,
				// which is how a script reaches the system tools when
				// PATH may have been rewritten — and exactly what a
				// restricted shell exists to prevent (#398).
				if r.opts[optRestricted] {
					return failf(1, "command: -p: restricted\n")
				}
				defPath = true
			default:
				return failf(2, "command: invalid option %q\n", flag)
			}
		}
		args := fp.args()
		if len(args) == 0 {
			break
		}
		if defPath {
			// The default PATH stands in for confstr(_CS_PATH), which
			// Go does not expose; it is the same set every system ships.
			prev, had := r.writeEnv.Get("PATH"), true
			r.setVarString("PATH", "/usr/bin:/bin:/usr/sbin:/sbin")
			defer func() {
				if had {
					r.setVar("PATH", prev)
				}
			}()
		}
		if !show {
			// Through the call seam, so a builtin the embedder replaced
			// is the one `command` finds too (#565). Functions are what
			// `command` skips, and neither branch below looks at them.
			return r.callSkippingFuncs(ctx, pos, args)
		}
		last := uint8(0)
		for _, arg := range args {
			last = 0
			switch {
			case syntax.IsKeyword(arg):
				if verbose {
					r.outf("%s is a shell keyword\n", arg)
				} else {
					r.outf("%s\n", arg)
				}
			case r.Funcs[arg] != nil:
				if verbose {
					r.outf("%s is a function\n", arg)
					r.printFuncDef(arg, r.Funcs[arg])
				} else {
					r.outf("%s\n", arg)
				}
			case IsBuiltin(arg) && !r.disabledBuiltins[arg]:
				// A disabled builtin falls through to the PATH search,
				// which is the whole point of disabling it: `command -v
				// printf` answers /usr/bin/printf, exactly as `type`
				// already did (#603).
				if verbose {
					r.outf("%s is a shell builtin\n", arg)
				} else {
					r.outf("%s\n", arg)
				}
			default:
				// Through lookPathAll rather than a bare PATH search, so
				// a `hash -p` pin is what `command -v` reports — as
				// `type` already did. koi answered with whatever PATH
				// held, which is the one answer the pin exists to
				// override.
				if paths := r.lookPathAll(arg, false); len(paths) > 0 {
					path := paths[0]
					switch {
					case !verbose:
						r.outf("%s\n", path)
					case r.hashTable[arg] == path:
						r.outf("%s is hashed (%s)\n", arg, path)
					default:
						r.outf("%s is %s\n", arg, path)
					}
				} else {
					if verbose {
						r.errf("command: %s: not found\n", arg)
					}
					last = 1
				}
			}
		}
		exit.code = last
	case "dirs":
		return r.dirs(args)
	case "pushd":
		return r.pushd(ctx, args)
	case "popd":
		return r.popd(ctx, args)
	case "return":
		if !r.inFunc && !r.inSource {
			return failf(1, "return: can only be done from a func or sourced script\n")
		}
		switch len(args) {
		case 0:
		case 1:
			n, err := strconv.Atoi(args[0])
			if err != nil {
				return failf(2, "return: %s: numeric argument required\n", args[0])
			}
			exit.code = uint8(n)
		default:
			return failf(2, "return: too many arguments\n")
		}
		exit.returning = true
	case "read":
		var prompt string
		raw := false
		silent := false
		arrayName := ""
		delim := byte('\n')
		// maxChars is the count given to -n or -N; a negative value means that
		// the read is only stopped by the delimiter or by the end of the input.
		maxChars := -1
		// exactly is set by -N, which reads a fixed number of characters,
		// ignoring the delimiter and doing no field splitting.
		exactly := false
		// fd is the descriptor -u names; 0 is the shell's own stdin. haveFd
		// separates "the caller named a descriptor" from the default,
		// because only the first is worth a Bad file descriptor: a shell
		// with no stdin at all is the embedder's business, and readLine
		// already says so in those words.
		fd, haveFd := 0, false
		// timeout is -t. haveTimeout is separate because -t 0 is its own
		// thing — a test for whether input is waiting, reading nothing.
		var timeout time.Duration
		haveTimeout := false
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-s":
				silent = true
			case "-r":
				raw = true
			case "-a":
				// Note that bash takes the array name as this option's
				// argument, so further options may follow it.
				if len(fp.remaining) == 0 {
					return failf(2, "read: -a: option requires an argument\n")
				}
				arrayName = fp.value()
				if !syntax.ValidName(arrayName) {
					return failf(2, "read: invalid identifier %q\n", arrayName)
				}
			case "-p":
				prompt = fp.value()
				if prompt == "" {
					return failf(2, "read: -p: option requires an argument\n")
				}
			case "-d":
				// Note that an empty string is a valid delimiter, so we can't
				// use the empty return from value to detect a missing argument.
				if len(fp.remaining) == 0 {
					return failf(2, "read: -d: option requires an argument\n")
				}
				if val := fp.value(); val == "" {
					// Bash uses an ASCII NUL when given an empty string,
					// which is how "find -print0" input is consumed.
					delim = 0
				} else {
					delim = val[0]
				}
			case "-n", "-N":
				if len(fp.remaining) == 0 {
					return failf(2, "read: %s: option requires an argument\n", flag)
				}
				val := fp.value()
				n, err := strconv.Atoi(val)
				if err != nil || n < 0 {
					return failf(1, "read: %s: invalid number\n", val)
				}
				maxChars = n
				exactly = flag == "-N"
			case "-t":
				if len(fp.remaining) == 0 {
					return failf(2, "read: -t: option requires an argument\n")
				}
				val := fp.value()
				// Seconds, and fractional: `read -t 0.1` is how a script
				// polls without spinning. Note the status is 1 rather than
				// the usual 2 for a bad value, which is bash's.
				secs, err := strconv.ParseFloat(val, 64)
				if err != nil || secs < 0 {
					return failf(1, "read: %s: invalid timeout specification\n", val)
				}
				haveTimeout = true
				timeout = time.Duration(secs * float64(time.Second))
			case "-u":
				if len(fp.remaining) == 0 {
					return failf(2, "read: -u: option requires an argument\n")
				}
				val := fp.value()
				n, err := strconv.Atoi(val)
				if err != nil || n < 0 {
					return failf(1, "read: %s: invalid file descriptor specification\n", val)
				}
				fd, haveFd = n, true
			default:
				return failf(2, "read: invalid option %q\n", flag)
			}
		}

		args := fp.args()
		for _, name := range args {
			if !syntax.ValidName(name) {
				return failf(2, "read: invalid identifier %q\n", name)
			}
		}

		// After the names are validated, so `read 0ab` still complains
		// about the identifier rather than about a descriptor.
		src := r.fdReader(fd)
		if src == nil && haveFd {
			return failf(1, "read: %d: invalid file descriptor: Bad file descriptor\n", fd)
		}

		if prompt != "" {
			r.out(prompt)
		}

		// `-t 0` reads nothing at all: it answers whether input is waiting,
		// through the status alone. Anything else would consume the byte it
		// was asked about, which is worse than not implementing it — a
		// script that polls would eat its own input one character at a time.
		if haveTimeout && timeout == 0 {
			ready, err := readyToRead(src)
			if err != nil {
				return failf(1, "read: %v\n", err)
			}
			if !ready {
				exit.code = 1
			}
			return exit
		}

		var line []byte
		var err error
		var timedOut bool
		// -s only has an effect when reading from a terminal, as there is no
		// echo to suppress when the input is a pipe or a file. Note that we
		// must use the shell's stdin rather than the process's, as they differ
		// under a redirect and when the caller supplied its own via [StdIO].
		if f, ok := src.(*os.File); ok && silent && delim == '\n' && maxChars < 0 &&
			term.IsTerminal(int(f.Fd())) {
			line, err = term.ReadPassword(int(f.Fd()))
		} else {
			line, timedOut, err = r.readLine(ctx, src, raw, delim, maxChars, exactly, timeout)
		}
		switch {
		case arrayName != "":
			// Use -1 as max to get all fields without joining the last ones.
			values := expand.ReadFields(r.ecfg, string(line), -1, raw)
			r.setVar(arrayName, expand.Variable{
				Set:  true,
				Kind: expand.Indexed,
				List: values,
			})
		case exactly, len(args) == 0:
			// A bare "read" assigns the whole line to REPLY, and -N assigns
			// the characters it read to the first name given. Neither does any
			// trimming nor field splitting; both discard escapes unless raw.
			val := string(line)
			if !raw {
				val = unescapeRead(val)
			}
			name := shellReplyVar
			if len(args) > 0 {
				name = args[0]
			}
			r.setVarString(name, val)
			// Bash leaves any remaining names empty rather than unset.
			for _, name := range args[min(1, len(args)):] {
				r.setVarString(name, "")
			}
		default:
			values := expand.ReadFields(r.ecfg, string(line), len(args), raw)
			for i, name := range args {
				val := ""
				if i < len(values) {
					val = values[i]
				}
				r.setVarString(name, val)
				// A readonly target *aborts* the assignment list at
				// status 2, per POSIX: koi reported the error, skipped
				// that name, assigned the rest, and answered 0 — so a
				// script guarding on read's status was told it worked
				// (#404).
				if r.exit.code != 0 {
					r.exit.code = 0
					return exitStatus{code: 2}
				}
			}
		}

		// We can get data back from readLine and an error at the same time, so
		// check err after we process the data. The same goes for a timeout:
		// whatever arrived before it is assigned, and only the status says
		// the read was cut short.
		switch {
		case timedOut:
			// bash reports a timeout as a status above 128, the way it
			// reports a signal — 128 + SIGALRM.
			exit.code = readTimeoutStatus
			return exit
		case err != nil:
			exit.code = 1
			return exit
		}

	case "getopts":
		if len(args) < 2 {
			return failf(2, "getopts: usage: getopts optstring name [arg ...]\n")
		}
		optind, _ := strconv.Atoi(r.envGet("OPTIND"))
		if optind-1 != r.optState.argidx {
			if optind < 1 {
				optind = 1
			}
			r.optState = getopts{argidx: optind - 1}
		}
		optstr := args[0]
		name := args[1]
		if !syntax.ValidName(name) {
			return failf(2, "getopts: invalid identifier: %q\n", name)
		}
		args = args[2:]
		if len(args) == 0 {
			args = r.Params
		}
		// A leading colon in the optstring asks for silent mode, and so
		// does OPTERR=0 — which koi ignored, so a script that set it
		// still got koi's diagnostics in its output (#403).
		diagnostics := !strings.HasPrefix(optstr, ":") && r.envGet("OPTERR") != "0"

		opt, optarg, done := r.optState.next(optstr, args)

		r.setVarString(name, string(opt))
		r.delVar("OPTARG")
		switch {
		case opt == '?' && diagnostics && !done:
			r.errf("getopts: illegal option -- %q\n", optarg)
		case opt == ':' && diagnostics:
			r.errf("getopts: option requires an argument -- %q\n", optarg)
		default:
			if optarg != "" {
				r.setVarString("OPTARG", optarg)
			}
		}
		if optind-1 != r.optState.argidx {
			r.setVarInt("OPTIND", strconv.FormatInt(int64(r.optState.argidx+1), 10))
		}

		exit.oneIf(done)

	case "shopt":
		mode := ""
		posixOpts, quiet, print := false, false, false
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-s", "-u":
				if mode != "" && mode != flag {
					// bash refuses the pair rather than letting the
					// last one win, which is the only safe answer: a
					// script that wrote both meant one of them.
					return failf(1, "shopt: cannot set and unset shell options simultaneously\n")
				}
				mode = flag
			case "-o":
				posixOpts = true
			case "-q":
				// The scripting probe form: no output, the answer is
				// the status (#393). koi refused it with exit 2, so
				// `shopt -q extglob && …` took the error branch.
				quiet = true
			case "-p":
				print = true
			default:
				return failf(2, "shopt: invalid option %q\n", flag)
			}
		}
		args := fp.args()
		if len(args) == 0 {
			if quiet {
				break
			}
			// With no names, `-s` and `-u` are not a request but a
			// *filter*: bash lists the options in that state, which is
			// how a script asks "what is on here?" without reading 59
			// lines. koi printed nothing at all, status 0 — the empty
			// answer reads as a shell with no options set (#574).
			//
			// Names change that back into a set operation, which is why
			// this only applies here: `shopt -s -p cdspell` sets
			// cdspell and prints nothing, measured.
			listing := func(on bool) bool {
				switch mode {
				case "-s":
					return on
				case "-u":
					return !on
				}
				return true
			}
			if posixOpts {
				for _, i := range posixOptNames() {
					if !listing(r.opts[i]) {
						continue
					}
					if print {
						r.outf("set %co %s\n", setSign(r.opts[i]), posixOptsTable[i].name)
						continue
					}
					r.printOptLine(posixOptsTable[i].name, setOptColumn, r.opts[i])
				}
			} else {
				// Alphabetical, as bash prints it: koi's supported
				// options sit in a leading block of the table, which
				// listed them all first (#393).
				for _, i := range bashOptNames() {
					opt := bashOptsTable[i]
					on := r.opts[len(posixOptsTable)+i]
					if !listing(on) {
						continue
					}
					if print {
						// -p prints each option as the command that
						// would set it, which is what a script saves
						// and replays.
						r.outf("shopt %s %s\n", shoptState(on), opt.name)
						continue
					}
					r.printOptLine(opt.name, shoptOptColumn, on)
				}
			}
			break
		}
		// -q and a bare listing both answer through the status: 0 when
		// every named option is on, 1 otherwise. -p's status does the
		// same, which koi always reported as 0.
		allOn := true
		for _, arg := range args {
			opt, supported := (*bool)(nil), true
			var po posixOpt
			if posixOpts {
				opt, po = r.posixOptByName(arg)
				supported = po.supported
			} else {
				opt, supported = r.bashOptByName(arg)
			}
			if opt == nil {
				// The two tables word it differently, and the -o form
				// answers 0 when *setting* an unknown name — measured,
				// odd, and bash's.
				if posixOpts {
					r.errf("shopt: %s: invalid option name\n", arg)
					if mode == "" {
						exit.code = 1
					}
					return exit
				}
				return failf(1, "shopt: %s: invalid shell option name\n", arg)
			}

			switch mode {
			case "-s", "-u":
				want := mode == "-s"
				if !supported {
					// An option koi does not implement can never leave
					// its default, so asking for the state it is already
					// in is a request koi *is* satisfying — refusing
					// there reports a failure for something that did
					// happen (#542). `shopt -u xpg_echo` is the line
					// scripts write defensively, and bash's own
					// posixexp2.tests opens with it. Asking for the
					// behavior koi does not have is the other question,
					// and still gets the honest refusal.
					//
					// This is the rule `set -o` already followed: `set
					// +o notify` is fine and `set -o notify` is not.
					if *opt == want {
						continue
					}
					return failf(1, "shopt: unsupported option %q\n", arg)
				}
				*opt = want
				// `shopt -o -s vi` is `set -o vi` spelled the other way,
				// so it owes the same exclusion (#576).
				r.excludeEditMode(po.name, want)
			default: // "" and -p
				if !*opt {
					allOn = false
				}
				if quiet {
					continue
				}
				if posixOpts {
					if print {
						r.outf("set %co %s\n", setSign(*opt), arg)
						continue
					}
					r.printOptLine(arg, setOptColumn, *opt)
					continue
				}
				if print {
					r.outf("shopt %s %s\n", shoptState(*opt), arg)
					continue
				}
				r.printOptLine(arg, shoptOptColumn, *opt)
			}
		}
		if mode == "" && !allOn {
			exit.code = 1
		}
		r.updateExpandOpts()

	case "alias":
		show := func(name string, als alias) {
			// The listing is single-quoted the way bash spells it, and
			// the text is what was defined rather than a re-print of a
			// parse — an alias may not be a command at all.
			r.outf("alias %s='%s'\n", name, strings.ReplaceAll(als.text, "'", `'\''`))
		}

		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-p":
				// The listing form; koi read it as an alias named -p.
			default:
				r.errf("alias: %s: invalid option\n", flag)
				r.rawErrf("alias: usage: alias [-p] [name[=value] ... ]\n")
				return exitStatus{code: 2}
			}
		}
		args := fp.args()

		if len(args) == 0 {
			for _, name := range slices.Sorted(maps.Keys(r.alias)) {
				show(name, r.alias[name])
			}
		}
		for _, arg := range args {
			name, src, ok := strings.Cut(arg, "=")
			if !ok {
				als, ok := r.alias[name]
				if !ok {
					r.errf("alias: %s: not found\n", name)
					exit.code = 1
					continue
				}
				show(name, als)
				continue
			}

			if r.alias == nil {
				r.alias = make(map[string]alias)
			}
			r.alias[name] = alias{
				text: src,
				// A trailing blank asks for the *next* word to be
				// alias-expanded too.
				blank: strings.TrimRight(src, " \t") != src,
			}
		}
	case "unalias":
		// bash diagnoses all three of these; koi answered 0 for every
		// one (#407).
		if len(args) == 0 {
			// A usage line is not a diagnostic, so it carries no
			// location — measured: bare `unalias` in a script prints the
			// line and nothing else, where koi prefixed it with
			// `file: line N:` (#611). This is the only one of the three
			// where the usage line stands alone rather than following a
			// message of its own.
			r.rawErrf("unalias: usage: unalias [-a] name [name ...]\n")
			exit.code = 2
			return exit
		}
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-a":
				r.alias = nil
				return exit
			default:
				r.errf("unalias: %s: invalid option\n", flag)
				r.rawErrf("unalias: usage: unalias [-a] name [name ...]\n")
				return exitStatus{code: 2}
			}
		}
		for _, name := range fp.args() {
			if _, ok := r.alias[name]; !ok {
				r.errf("unalias: %s: not found\n", name)
				exit.code = 1
				continue
			}
			delete(r.alias, name)
		}

	case "trap":
		fp := flagParser{remaining: args}
		callback := "-"
		list, print := false, false
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-l":
				list = true
			case "-p":
				print = true
			case "-":
				// default signal
			default:
				r.errf("trap: %q: invalid option\n", flag)
				r.rawErrf("trap: usage: trap [-lp] [[arg] signal_spec ...]\n")
				exit.code = 2
				return exit
			}
		}
		args := fp.args()
		if list {
			r.printSignalNames()
			break
		}
		// `trap -p` and bare `trap` print the same thing; `-p` additionally
		// takes names to print, which is the form a script uses to save one
		// handler and restore it later.
		if print || len(args) == 0 {
			r.printTraps(args)
			break
		}
		// `trap SIG` and `trap - SIG` restore the default; `trap '' SIG`
		// ignores the signal. The fake traps have no default to restore,
		// so resetting and ignoring are the same operation for them —
		// for a real signal they are not (#350).
		reset := false
		switch len(args) {
		case 1:
			reset = true
		default:
			callback = args[0]
			args = args[1:]
			if callback == "-" {
				callback, reset = "", true
			}
		}
		if callback == "-" {
			callback = ""
		}
		for _, arg := range args {
			// Specs are case-insensitive, and 0 is EXIT (#351):
			// `trap 'rm -f $tmp' 0` is the cleanup idiom in decades of
			// scripts.
			spec := strings.ToUpper(arg)
			if spec == "0" {
				spec = "EXIT"
			}
			switch spec {
			case "ERR":
				r.callbackErr, r.listed.err = callback, callback
				// Installing the trap rebases the inheritance rule to
				// here: a trap set inside a subshell or a function fires
				// for failures in that scope (#354) — "not inherited"
				// restricts a *parent's* trap, not the one this scope
				// just set. Leaving depth alone made `(trap 'echo e'
				// ERR; false)` silent. Function returns restore their
				// caller's depth, so the rebase does not leak upward.
				r.errTrapDepth = 0
			case "EXIT":
				r.callbackExit, r.listed.exit = callback, callback
				r.callbackExitLine = pos.Line()
			case "DEBUG":
				// Reachable here for the same reason RETURN is, below:
				// `trap` installs the handler for the context it is run
				// in, so a function that sets its own DEBUG trap traces
				// its own remaining commands even though entering the
				// function turned inheritance off. Measured — koi ran
				// the function's body untraced and only started tracing
				// after it returned, which is the shape a `set -x`
				// replacement written in a function reads as dead
				// (#697, found while giving the trace attribute its
				// entry point).
				r.callbackDebug, r.listed.debug = callback, callback
				r.debugTrapOff = false
			case "RETURN":
				// Setting it here also makes it reachable here: `trap`
				// installs the handler for the context it is run in, so a
				// function that sets its own RETURN trap fires it even
				// though entering that function had turned inheritance
				// off. That is what makes the cleanup idiom work.
				r.callbackReturn, r.listed.ret = callback, callback
				r.returnTrapOff = false
			default:
				name, sig, ok := lookupSignal(arg)
				if !ok {
					return failf(1, "trap: %s: invalid signal specification\n", arg)
				}
				r.setSignalTrap(name, sig, callback, reset, pos.Line())
			}
		}

	case "readarray", "mapfile":
		dropDelim := false
		delim := "\n"
		// The count/origin/skip trio and the callback pair were all
		// refused with "invalid option", which left the array *never
		// created* — so every later loop over it printed nothing with
		// no sign of why (#392).
		maxCount, origin, skip := 0, 0, 0
		callback, quantum := "", 5000
		fd, haveFd := 0, false
		fp := flagParser{remaining: args}
		// Each numeric option names what it was expecting when the
		// value does not parse — bash's wording, and its status: 1
		// rather than the 2 a usage error usually carries.
		intArg := func(flag, what string) (int, bool) {
			if len(fp.remaining) == 0 {
				r.errf("%s: %s: option requires an argument\n", name, flag)
				return 0, false
			}
			val := fp.value()
			n, err := strconv.Atoi(val)
			if err != nil || n < 0 {
				r.errf("%s: %s: invalid %s\n", name, val, what)
				return 0, false
			}
			return n, true
		}
		for fp.more() {
			var ok bool
			switch flag := fp.flag(); flag {
			case "-t":
				// Remove the delim from each line read
				dropDelim = true
			case "-d":
				if len(fp.remaining) == 0 {
					return failf(2, "%s: -d: option requires an argument\n", name)
				}
				delim = fp.value()
				if delim == "" {
					// Bash sets the delim to an ASCII NUL if provided with an empty
					// string.
					delim = "\x00"
				}
			case "-n":
				if maxCount, ok = intArg(flag, "line count"); !ok {
					return exitStatus{code: 1}
				}
			case "-O":
				if origin, ok = intArg(flag, "array origin"); !ok {
					return exitStatus{code: 1}
				}
			case "-s":
				if skip, ok = intArg(flag, "line count"); !ok {
					return exitStatus{code: 1}
				}
			case "-c":
				if quantum, ok = intArg(flag, "callback quantum"); !ok {
					return exitStatus{code: 1}
				}
				if quantum == 0 {
					quantum = 5000
				}
			case "-C":
				if len(fp.remaining) == 0 {
					return failf(2, "%s: -C: option requires an argument\n", name)
				}
				callback = fp.value()
			case "-u":
				if fd, ok = intArg(flag, "file descriptor specification"); !ok {
					return exitStatus{code: 1}
				}
				haveFd = true
			default:
				return failf(2, "%s: invalid option %q\n", name, flag)
			}
		}

		args := fp.args()
		var arrayName string
		switch len(args) {
		case 0:
			arrayName = "MAPFILE"
		case 1:
			if !syntax.ValidName(args[0]) {
				return failf(2, "%s: invalid identifier %q\n", name, args[0])
			}
			arrayName = args[0]
		default:
			return failf(2, "%s: Only one array name may be specified, %v\n", name, args)
		}

		src := r.fdReader(fd)
		if src == nil {
			if haveFd {
				return failf(1, "%s: %d: invalid file descriptor: Bad file descriptor\n", name, fd)
			}
			return failf(1, "%s: no stdin to read from\n", name)
		}

		var vr expand.Variable
		vr.Kind, vr.Set = expand.Indexed, true
		scanner := bufio.NewScanner(src)
		scanner.Split(mapfileSplit(delim[0], dropDelim))
		read := 0
		for scanner.Scan() {
			if skip > 0 {
				// -s discards leading lines rather than storing them,
				// so they do not count toward -n either.
				skip--
				continue
			}
			vr.List = append(vr.List, scanner.Text())
			read++
			if callback != "" && read%quantum == 0 {
				// The callback is evaluated with the index the line
				// landed at and the line itself, which is how a script
				// reports progress over a long read.
				idx := origin + len(vr.List) - 1
				r.mapfileCallback(ctx, callback, idx, vr.List[len(vr.List)-1])
			}
			if maxCount > 0 && read >= maxCount {
				break
			}
		}
		if err := scanner.Err(); err != nil {
			return failf(2, "%s: unable to read, %v\n", name, err)
		}
		if origin > 0 {
			// -O stores the first line at that index, so the array is
			// sparse from zero rather than shifted.
			vr.Indexes = make([]int, len(vr.List))
			for i := range vr.List {
				vr.Indexes[i] = origin + i
			}
		}
		r.setVar(arrayName, vr)

	case "compgen":
		// Only the actions which enumerate what the shell itself knows are
		// implemented; the rest are refused rather than silently answering
		// nothing, which is the failure mode worth avoiding for a builtin
		// whose whole job is to answer "what exists?".
		action := ""
		fp := flagParser{remaining: args}
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-A":
				if len(fp.remaining) == 0 {
					return failf(2, "compgen: -A: option requires an argument\n")
				}
				action = fp.value()
			case "-a":
				action = "alias"
			case "-v":
				action = "variable"
			case "-b":
				action = "builtin"
			default:
				return failf(2, "compgen: %q: NOT IMPLEMENTED flag\n", flag)
			}
		}
		var names []string
		switch action {
		case "function":
			for name := range r.Funcs {
				names = append(names, name)
			}
		case "alias":
			for name := range r.alias {
				names = append(names, name)
			}
		case "builtin":
			// Only the builtins koi implements. Listing one it would
			// refuse is the disagreement this is here to end (#302):
			// "what exists?" and "what can I call?" have to be the
			// same answer for a builtin whose whole job is the first
			// question.
			names = append(names, ImplementedBuiltins()...)
		case "enabled":
			// The same list minus what `enable -n` turned off, with
			// `disabled` its complement (#603). `builtin` above stays
			// the whole list, which is bash's answer too: a disabled
			// builtin is still a builtin *name*.
			for _, name := range ImplementedBuiltins() {
				if !r.disabledBuiltins[name] {
					names = append(names, name)
				}
			}
		case "disabled":
			for name, off := range r.disabledBuiltins {
				if off {
					names = append(names, name)
				}
			}
			slices.Sort(names)
		case "variable":
			r.writeEnv.Each(func(name string, vr expand.Variable) bool {
				if vr.IsSet() {
					names = append(names, name)
				}
				return true
			})
		case "":
			return failf(2, "compgen: an action is required, such as -A function\n")
		default:
			return failf(2, "compgen: -A %q: NOT IMPLEMENTED action\n", action)
		}
		// A word operand is a prefix to match, not a pattern.
		if rest := fp.args(); len(rest) > 0 {
			prefix := rest[0]
			names = slices.DeleteFunc(names, func(name string) bool {
				return !strings.HasPrefix(name, prefix)
			})
		}
		slices.Sort(names)
		names = slices.Compact(names)
		for _, name := range names {
			r.outf("%s\n", name)
		}
		if len(names) == 0 {
			// Bash reports no matches with a non-zero status.
			exit.code = 1
		}

	case "caller":
		// `caller` is the frame stack as a builtin (#250, #266): the same
		// three fields FUNCNAME, BASH_SOURCE and BASH_LINENO expose, read
		// one frame down from the argument.
		//
		// It answers by *status* when there is no such frame, which is what
		// callers act on: `caller 0` at the top level of a script is how an
		// error helper asks "was I called from a function?" and expects a
		// non-zero answer rather than a diagnostic.
		frames := r.baseFrames()
		depth := 0
		if len(args) > 0 {
			n, err := strconv.Atoi(args[0])
			if err != nil || n < 0 {
				// bash separates these: a negative number is read as an
				// option, anything else as a bad number. Both exit 2 with
				// the usage line, which is what a caller sees.
				what := "invalid number"
				if strings.HasPrefix(args[0], "-") {
					what = "invalid option"
				}
				r.errf("caller: %s: %s\ncaller: usage: caller [expr]\n", args[0], what)
				exit.code = 2
				break
			}
			depth = n
		}
		// Bare `caller` answers at the top level too, with `0 NULL`
		// (#410): that shape is how a dbg script asks "am I in a
		// function?" and koi printed nothing, so the probe read as an
		// error. `caller N` still needs a function frame, because it
		// names one.
		if depth >= len(frames) || (len(args) > 0 && !r.inFunction()) {
			exit.code = 1
			break
		}
		if len(args) == 0 {
			// Bare `caller` prints the line and the file only, and it does
			// not need a frame above to exist — bash prints its literal
			// "NULL" for the file instead, which is what `-c` produces.
			src := ""
			if depth+1 < len(frames) {
				src = frames[depth+1].source
			}
			r.outf("%d %s\n", frames[depth].callLine, orNull(src))
			break
		}
		// `caller N` names a function, so the frame above has to be there.
		if depth+1 >= len(frames) {
			exit.code = 1
			break
		}
		up := frames[depth+1]
		r.outf("%d %s %s\n", frames[depth].callLine, up.name, orNull(up.source))

	case "ulimit":
		return r.ulimitBuiltin(args)

	case "jobs":
		return r.jobsBuiltin(args)

	case "fg", "bg":
		return r.jobControlBuiltin(ctx, name, args)

	case "disown":
		// Forget a job, so it is no longer listed and no longer waited
		// for (#397). koi refused the builtin, which made the ordinary
		// `cmd & disown` line fatal.
		//
		// koi's jobs are goroutines rather than processes, so there is
		// no SIGHUP to withhold — what disown can honestly do here is
		// drop the bookkeeping, which is what a script observes.
		fp := flagParser{remaining: args}
		all, running := false, false
		for fp.more() {
			switch flag := fp.flag(); flag {
			case "-a":
				all = true
			case "-r":
				running = true
			case "-h":
				// Mark to skip SIGHUP: koi has nothing to send one to.
			default:
				return failf(2, "disown: invalid option %q\n", flag)
			}
		}
		args := fp.args()
		drop := func(i int) {
			if i >= 0 && i < len(r.bgProcs) {
				r.bgProcs[i].disowned = true
			}
		}
		switch {
		case len(args) > 0:
			for _, arg := range args {
				i, ok := r.bgIndex(arg)
				if !ok {
					r.errf("disown: %s: no such job\n", arg)
					exit.code = 1
					continue
				}
				drop(i)
			}
		case all, running:
			for i := range r.bgProcs {
				if running && r.bgProcs[i].reaped {
					continue
				}
				drop(i)
			}
		default:
			// Bare disown forgets the current job, and says so when
			// there is none — bash names it "current".
			i, ok := r.bgCurrent(0)
			if !ok {
				return failf(1, "disown: current: no such job\n")
			}
			drop(i)
		}

	case "declare", "typeset", "local", "export", "readonly", "nameref":
		// The parser produces a DeclClause when one of these words sits
		// at command position, so this path runs only when something kept
		// it from being a keyword — a prefix assignment is the case
		// bash's own suite exercises (`ref=xxx typeset -p ref var`,
		// nameref14.sub), and it answered "unsupported builtin" (#277).
		// The args arrive already expanded; wrapping each in a literal
		// Assign is exactly what flattenAssigns builds for a naked word,
		// so no value is expanded twice.
		assigns := make([]*syntax.Assign, 0, len(args))
		for _, field := range args {
			as := &syntax.Assign{}
			nm, val, ok := strings.Cut(field, "=")
			as.Name = &syntax.Lit{Value: nm}
			if !ok {
				as.Naked = true
			} else {
				as.Value = &syntax.Word{Parts: []syntax.WordPart{&syntax.Lit{Value: val}}}
			}
			assigns = append(assigns, as)
		}
		// declClause reports through r.exit, the way the DeclClause node
		// does; run it against a clean status and hand the result back
		// through the builtin contract.
		oldExit := r.exit
		r.exit = exitStatus{}
		r.declClause(name, assigns)
		exit, r.exit = r.exit, oldExit
		return exit

	default:
		return failf(2, "%s: unsupported builtin\n", name)
	}
	return exit
}

// orNull is bash's spelling for a frame whose file is not known.
func orNull(s string) string {
	if s == "" {
		return "NULL"
	}
	return s
}

// setListing prints what a bare `set` lists: every set variable as
// name=value, then every function in the canonical form declare -f
// prints. Both halves are sorted, which is bash's order.
func (r *Runner) setListing() {
	var names []string
	r.writeEnv.Each(func(name string, vr expand.Variable) bool {
		if vr.IsSet() && vr.Kind != expand.NameRef {
			names = append(names, name)
		}
		return true
	})
	slices.Sort(names)
	for _, name := range names {
		vr := r.lookupVar(name)
		switch vr.Kind {
		case expand.Indexed:
			// An array prints its elements the way declare -p does,
			// without the declare prefix.
			r.outf("%s=(", name)
			for i, v := range vr.List {
				if i > 0 {
					r.out(" ")
				}
				idx := i
				if vr.Indexes != nil {
					idx = vr.Indexes[i]
				}
				r.outf("[%d]=%s", idx, declQuote(v))
			}
			r.out(")\n")
		case expand.Associative:
			r.outf("%s=(", name)
			for _, k := range vr.AssocKeys() {
				r.outf("[%s]=%s ", declQuoteKey(k), declQuote(vr.Map[k]))
			}
			r.out(")\n")
		default:
			r.outf("%s=%s\n", name, setQuote(vr.Str))
		}
	}
	for _, name := range slices.Sorted(maps.Keys(r.Funcs)) {
		r.out(printFuncCanonical(name, r.Funcs[name], false))
	}
}

// setQuote renders a value the shortest way that reads back, which is
// what `set` prints: bare when nothing needs quoting, ANSI-C when a
// control character does, and single quotes otherwise. declare -p's
// always-double-quoted form is a different question and has its own
// renderer.
func setQuote(s string) string {
	if s == "" {
		return ""
	}
	safe := true
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c >= 'a' && c <= 'z', c >= 'A' && c <= 'Z', c >= '0' && c <= '9':
		case c == '_', c == '.', c == '-', c == '/', c == ':', c == '+', c == '@', c == '%', c == ',', c == '=':
		default:
			safe = false
		}
		if !safe {
			break
		}
	}
	if safe {
		return s
	}
	if strings.ContainsFunc(s, func(r rune) bool { return r < 0x20 || r == 0x7f }) {
		return declQuote(s)
	}
	return "'" + strings.ReplaceAll(s, "'", `'\''`) + "'"
}

// mapfileCallback runs mapfile's -C action, which bash evaluates with
// the array index and the line appended as arguments (#392).
func (r *Runner) mapfileCallback(ctx context.Context, callback string, index int, line string) {
	src := callback + " " + strconv.Itoa(index) + " " + shellQuoteArg(line)
	file, err := syntax.NewParser().Parse(strings.NewReader(src), "")
	if err != nil {
		return
	}
	r.stmts(ctx, file.Stmts)
}

// shellQuoteArg single-quotes a value so the callback receives it as
// one word whatever it contains.
func shellQuoteArg(s string) string {
	return "'" + strings.ReplaceAll(s, "'", `'\''`) + "'"
}

// mapfileSplit returns a suitable Split function for a [bufio.Scanner];
// the code is mostly stolen from [bufio.ScanLines].
func mapfileSplit(delim byte, dropDelim bool) bufio.SplitFunc {
	return func(data []byte, atEOF bool) (advance int, token []byte, err error) {
		if atEOF && len(data) == 0 {
			return 0, nil, nil
		}
		if i := bytes.IndexByte(data, delim); i >= 0 {
			// We have a full newline-terminated line.
			if dropDelim {
				return i + 1, data[0:i], nil
			} else {
				return i + 1, data[0 : i+1], nil
			}
		}
		// If we're at EOF, we have a final, non-terminated line. Return it.
		if atEOF {
			return len(data), data, nil
		}
		// Request more data.
		return 0, nil, nil
	}
}

// setOptColumn and shoptOptColumn are the widths bash pads a name to
// before the tab in each listing. Measured from bash 5.3 rather than
// chosen — a listing is something scripts cut fields out of.
//
// shopt's width is *not* stable across bash versions: 5.x pads to twenty
// and the 3.2 that ships on macOS pads to fifteen, so there is no width
// that matches both. koi previously padded to zero, which resolved that
// by matching neither (#574). It follows the version koi claims (#120),
// and the builtins matrix asks the oracle which bash it is rather than
// splitting the difference.
const (
	setOptColumn   = 15
	shoptOptColumn = 20
)

// setSign and shoptState spell an option's state the way each listing
// re-states it: `set -o x` / `set +o x`, and `shopt -s x` / `shopt -u x`.
func setSign(on bool) byte {
	if on {
		return '-'
	}
	return '+'
}

func shoptState(on bool) string {
	if on {
		return "-s"
	}
	return "-u"
}

// lookPathAll finds a name on PATH: the first match, or every match
// when `type -a` asked for all of them (#411).
func (r *Runner) lookPathAll(name string, all bool) []string {
	// `hash -p` pins a name to a path, and that pin is consulted before
	// PATH — which is the point of it (#411).
	if path, ok := r.hashTable[name]; ok {
		return []string{path}
	}
	if !all {
		if path, err := LookPathDir(r.Dir, r.writeEnv, name); err == nil {
			return []string{path}
		}
		return nil
	}
	var out []string
	seen := map[string]bool{}
	for _, dir := range filepath.SplitList(r.envGet("PATH")) {
		if dir == "" {
			dir = "."
		}
		cand := filepath.Join(r.absPath(dir), name)
		if seen[cand] {
			continue
		}
		info, err := os.Stat(cand)
		if err != nil || info.IsDir() || info.Mode()&0o111 == 0 {
			continue
		}
		seen[cand] = true
		out = append(out, cand)
	}
	return out
}

// printOptLine prints one row of a `set -o` or `shopt` listing: the name
// padded to the listing's column, a tab, and the state.
//
// It used to add `("on" not supported)` to the row of an option koi does
// not implement. Well meant, and the wrong place for it (#574): a
// listing is *data* — scripts cut fields out of it and diff it against a
// saved copy — and the annotation made every such row differ from bash
// on the most-read form of the command. The honesty belongs where the
// answer is a refusal, and `shopt -s <unsupported>` still says so.
func (r *Runner) printOptLine(name string, column int, enabled bool) {
	r.outf("%-*s\t%s\n", column, name, r.optStatusText(enabled))
}

// unescapeRead drops the backslashes which escape another character, as "read"
// does when its -r option is not given.
func unescapeRead(val string) string {
	var sb strings.Builder
	esc := false
	for i := range len(val) {
		if val[i] == '\\' && !esc {
			esc = true
			continue
		}
		sb.WriteByte(val[i])
		esc = false
	}
	return sb.String()
}

// readLine reads from the shell's stdin until it reaches delim, or maxChars
// characters when it is not negative, or the end of the input. When exactly is
// set, delim is not looked for at all, as used by "read -N".
//
// Note that the returned line still holds the backslashes which escape another
// character, as whether they are dropped depends on the caller.
// deadlineReader is what a source has to be for `read -t` to bound it,
// and for the context to be able to interrupt it. A pipe and a terminal
// both qualify; a regular file does not, and does not need to, since it
// never blocks.
type deadlineReader interface {
	io.Reader
	SetReadDeadline(time.Time) error
}

// isRegularFile reports whether f is a plain file, which never blocks a
// read and so needs neither a deadline nor a poll.
func isRegularFile(f *os.File) bool {
	info, err := f.Stat()
	return err == nil && info.Mode().IsRegular()
}

// readLine reads one line, or one -n/-N-bounded run, from src.
//
// It reports whether the read timed out separately from the error,
// because a timeout is not a failure to the caller: bash assigns whatever
// it managed to read — `{ printf par; sleep 2; } | read -t 1 x` leaves x
// as "par" — and reports the timeout only through a status above 128
// (#267).
func (r *Runner) readLine(ctx context.Context, src io.Reader, raw bool, delim byte, maxChars int, exactly bool, timeout time.Duration) (line []byte, timedOut bool, _ error) {
	if src == nil {
		return nil, false, errors.New("interp: can't read, there's no stdin")
	}
	if maxChars == 0 {
		return nil, false, nil
	}

	esc := false
	// chars counts the characters that the line will hold once the escaping
	// backslashes are dropped, which is what -n and -N count. Characters,
	// not bytes (#377): а is one toward -n 5. pending tracks a multibyte
	// sequence in flight — its lead byte counts when the last
	// continuation byte arrives, and a stray continuation byte counts
	// alone, which is how bash's mbrtowc failure path treats it.
	chars := 0
	pending := 0
	// In the C locale a character *is* a byte, so -n and -N count bytes
	// and a read can stop in the middle of a multibyte sequence (#470).
	// A script that sets LC_ALL=C is asking for exactly that.
	cLocale := r.ecfg != nil && r.ecfg.CLocale()
	countByte := func(b byte) {
		if cLocale {
			chars++
			pending = 0
			return
		}
		switch {
		case b < 0x80:
			chars++
			pending = 0
		case b >= 0xf8: // not a legal UTF-8 lead or continuation
			chars++
			pending = 0
		case b >= 0xf0:
			pending = 3
		case b >= 0xe0:
			pending = 2
		case b >= 0xc0:
			pending = 1
		default: // continuation byte
			if pending > 0 {
				pending--
				if pending == 0 {
					chars++
				}
			} else {
				chars++
			}
		}
	}

	// The deadline serves two callers at once: the context, which sets it to
	// now to interrupt a blocked read, and -t, which sets it ahead. Whichever
	// fires, the read returns os.ErrDeadlineExceeded and which one it was is
	// decided by asking the context afterwards.
	//
	// Not every blocking file takes a deadline: the runtime refuses one on
	// anything it cannot add to its poller, and a FIFO opened read-write —
	// `exec 9<> pipe`, the shape scripts use precisely to keep a FIFO from
	// blocking on open — is in that set. Treating the refusal as "a regular
	// file, returns immediately" left `read -u 9 -t 1` blocked until killed
	// (#348), so a refused deadline on something other than a regular file
	// falls back to poll(2) before each byte instead.
	var poll *os.File
	var pollDeadline time.Time
	if dr, ok := src.(deadlineReader); ok && dr.SetReadDeadline(time.Time{}) == nil {
		if timeout > 0 {
			dr.SetReadDeadline(time.Now().Add(timeout))
		}
		stopc := make(chan struct{})
		stop := context.AfterFunc(ctx, func() {
			dr.SetReadDeadline(time.Now())
			close(stopc)
		})
		defer func() {
			if !stop() {
				// The AfterFunc was started.
				// Wait for it to complete before clearing the deadline.
				<-stopc
			}
			dr.SetReadDeadline(time.Time{})
		}()
	} else if f, ok := src.(*os.File); ok && !isRegularFile(f) {
		poll = f
		if timeout > 0 {
			pollDeadline = time.Now().Add(timeout)
		}
	}
	for {
		if poll != nil {
			pollTimedOut, err := waitReadable(ctx, poll, pollDeadline)
			if err != nil {
				return line, false, err
			}
			if pollTimedOut {
				return line, true, nil
			}
		}
		var buf [1]byte
		n, err := src.Read(buf[:])
		if n > 0 {
			b := buf[0]
			switch {
			case !raw && b == '\\':
				line = append(line, b)
				esc = !esc
				if !esc {
					// A second backslash, so the pair is one character.
					chars++
					pending = 0
				}
			case !raw && !exactly && b == delim && esc && delim == '\n':
				// line continuation; drop the trailing backslash
				line = line[:len(line)-1]
				esc = false
			case !exactly && b == delim && !esc:
				return line, false, nil
			default:
				// Note that an escaped delimiter lands here, so it becomes a
				// literal character rather than ending the line.
				line = append(line, b)
				esc = false
				countByte(b)
			}
			if maxChars >= 0 && chars >= maxChars {
				return line, false, nil
			}
		}
		if err != nil {
			// A deadline fired. It was -t unless the context is what
			// cancelled, in which case this is an interrupted command and
			// not a timeout the script asked for.
			if timeout > 0 && errors.Is(err, os.ErrDeadlineExceeded) && ctx.Err() == nil {
				return line, true, nil
			}
			return line, false, err
		}
	}
}

// cdPathLookup searches CDPATH for a relative operand, which is how a
// script cds to a directory by name from anywhere (#391). An absolute
// or explicitly-relative path never searches, and a miss falls back to
// the operand as written.
func (r *Runner) cdPathLookup(ctx context.Context, path string) (string, bool) {
	if path == "" || filepath.IsAbs(path) ||
		strings.HasPrefix(path, "./") || strings.HasPrefix(path, "../") ||
		path == "." || path == ".." {
		return "", false
	}
	cdpath := r.envGet("CDPATH")
	if cdpath == "" {
		return "", false
	}
	for _, dir := range strings.Split(cdpath, ":") {
		if dir == "" {
			dir = "."
		}
		cand := filepath.Join(dir, path)
		if info, err := r.stat(ctx, r.absPath(cand)); err == nil && info.IsDir() {
			return cand, true
		}
	}
	return "", false
}

// cdErr reports why a directory could not be entered, naming it as it
// was written and using strerror's wording rather than Go's (#571).
func (r *Runner) cdErr(cmd, path string, err error) uint8 {
	r.errf("%s: %s: %s\n", cmd, path, openReason(err))
	return 1
}

func (r *Runner) changeDir(ctx context.Context, cmd, path string) uint8 {
	// The wording and the order are bash's: the directory named as it
	// was written, then strerror's phrasing, and a file that is not a
	// directory says so rather than claiming it does not exist (#571).
	if path == "" {
		r.errf("%s: null directory\n", cmd)
		return 1
	}
	apath := r.absPath(path)
	info, err := r.stat(ctx, apath)
	switch {
	case err != nil:
		return r.cdErr(cmd, path, err)
	case !info.IsDir():
		r.errf("%s: %s: Not a directory\n", cmd, path)
		return 1
	}
	if err := r.access(ctx, apath, AccessExec); err != nil {
		return r.cdErr(cmd, path, err)
	}
	r.Dir = apath
	r.setVarString("OLDPWD", r.envGet("PWD"))
	r.setVarString("PWD", apath)
	// Entry 0 of the directory stack *is* the current directory in
	// bash, so every chdir moves it (#390): leaving it frozen at the
	// shell's startup directory made popd return to the wrong place.
	r.dirStackSync()
	return 0
}

func absPath(dir, path string) string {
	if path == "" {
		return ""
	}
	if !filepath.IsAbs(path) {
		path = filepath.Join(dir, path)
	}
	return filepath.Clean(path) // TODO: this clean is likely unnecessary
}

func (r *Runner) absPath(path string) string {
	return absPath(r.Dir, path)
}

// flagParser is used to parse builtin flags.
//
// It's similar to the getopts implementation, but with some key differences.
// First, the API is designed for Go loops, making it easier to use directly.
// Second, it doesn't require the awkward ":ab" syntax that getopts uses.
// Third, it supports "-a" flags as well as "+a".
type flagParser struct {
	current   string
	remaining []string
}

func (p *flagParser) more() bool {
	if p.current != "" {
		// We're still parsing part of "-ab".
		return true
	}
	if len(p.remaining) == 0 {
		// Nothing left.
		p.remaining = nil
		return false
	}
	arg := p.remaining[0]
	if arg == "--" {
		// We explicitly stop parsing flags.
		p.remaining = p.remaining[1:]
		return false
	}
	if len(arg) == 0 || (arg[0] != '-' && arg[0] != '+') {
		// The next argument is not a flag.
		return false
	}
	// More flags to come.
	return true
}

func (p *flagParser) flag() string {
	arg := p.current
	if arg == "" {
		arg = p.remaining[0]
		p.remaining = p.remaining[1:]
	} else {
		p.current = ""
	}
	if len(arg) > 2 {
		// We have "-ab", so return "-a" and keep "-b".
		p.current = arg[:1] + arg[2:]
		arg = arg[:2]
	}
	return arg
}

// hasValue reports whether [flagParser.value] has anything to return,
// which is not the same question as whether it returns a non-empty
// string: `. -p ”` is a legal empty search path and `. -p` is bash's
// "option requires an argument".
func (p *flagParser) hasValue() bool {
	return p.current != "" || len(p.remaining) > 0
}

func (p *flagParser) value() string {
	if p.current != "" {
		// The value may be attached to its flag inside a cluster:
		// `read -ru3` is -r, -u, and the fd 3 (#405). Only the spaced
		// form worked, so the *variable name* was read as the
		// descriptor — and read.tests and procsub.tests run that inside
		// a loop, turning one parse bug into hundreds of error lines.
		val := p.current[1:]
		p.current = ""
		return val
	}
	if len(p.remaining) == 0 {
		return ""
	}
	arg := p.remaining[0]
	p.remaining = p.remaining[1:]
	return arg
}

func (p *flagParser) args() []string { return p.remaining }

type getopts struct {
	argidx  int
	runeidx int
}

func (g *getopts) next(optstr string, args []string) (opt rune, optarg string, done bool) {
	if len(args) == 0 || g.argidx >= len(args) {
		return '?', "", true
	}
	if args[g.argidx] == "--" {
		// `--` ends the options and is itself consumed, so OPTIND
		// points *past* it: koi left it in place and a script's
		// `shift $((OPTIND-1))` then kept the -- as an operand (#403).
		g.argidx++
		g.runeidx = 0
		return '?', "", true
	}
	arg := []rune(args[g.argidx])
	if len(arg) < 2 || arg[0] != '-' || arg[1] == '-' {
		return '?', "", true
	}

	opts := arg[1:]
	opt = opts[g.runeidx]

	i := strings.IndexRune(optstr, opt)
	if i >= 0 && i+1 < len(optstr) && optstr[i+1] == ':' {
		// the option requires an argument
		if g.runeidx+1 < len(opts) {
			// attached to the option in the same word, like -bval
			optarg = string(opts[g.runeidx+1:])
		} else if g.argidx+1 < len(args) {
			// the word that follows
			optarg = args[g.argidx+1]
			g.argidx++
		} else {
			// missing argument
			g.argidx++
			g.runeidx = 0
			return ':', string(opt), false
		}
		g.argidx++
		g.runeidx = 0
		return opt, optarg, false
	}

	if g.runeidx+1 < len(opts) {
		g.runeidx++
	} else {
		g.argidx++
		g.runeidx = 0
	}
	if i < 0 {
		// invalid option
		return '?', string(opt), false
	}
	return opt, "", false
}

// optStatusText returns a shell option's status text display
func (r *Runner) optStatusText(status bool) string {
	if status {
		return "on"
	}
	return "off"
}
