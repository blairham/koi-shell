// Copyright (c) 2017, Daniel Martí <mvdan@mvdan.cc>
// See LICENSE for licensing information

package interp_test

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"math/bits"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"slices"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/blairham/koi-shell/internal/shell/expand"
	"github.com/blairham/koi-shell/internal/shell/interp"
	"github.com/blairham/koi-shell/internal/shell/shinternal"
	"github.com/blairham/koi-shell/internal/shell/syntax"
	"github.com/go-quicktest/qt"
)

// runnerRunTimeout is the context timeout used by any tests calling [Runner.Run].
// The timeout saves us from hangs or burning too much CPU if there are bugs.
// All the test cases are designed to be inexpensive and stop in a very short
// amount of time, so 5s should be plenty even for busy machines.
const runnerRunTimeout = 5 * time.Second

// Some program which should be in $PATH. Needs to run before runTests is
// initialized (so an init function wouldn't work), because runTest uses it.
var pathProg = func() string {
	if runtime.GOOS == "windows" {
		return "cmd"
	}
	return "sh"
}()

func parse(tb testing.TB, parser *syntax.Parser, src string) *syntax.File {
	if parser == nil {
		parser = syntax.NewParser()
	}
	file, err := parser.Parse(strings.NewReader(src), "")
	if err != nil {
		tb.Fatal(err)
	}
	return file
}

func BenchmarkRun(b *testing.B) {
	b.ReportAllocs()

	src := `
echo a b c d
echo ./$foo/etc $(echo foo bar)
foo="bar"
x=y :
fn() {
	local a=b
	for i in 1 2 3; do
		echo $i | cat
	done
}
[[ $foo == bar ]] && fn
echo a{b,c}d *.go
let i=(2 + 3)
`
	file := parse(b, nil, src)
	r, _ := interp.New()
	ctx := b.Context()

	for b.Loop() {
		r.Reset()
		if err := r.Run(ctx, file); err != nil {
			b.Fatal(err)
		}
	}
}

var hasBash53 bool

// koi-local: see skipIfOracleGap.
var oracleTildeIgnoresHome bool

func TestMain(m *testing.M) {
	if os.Getenv("GOSH_PROG") != "" {
		switch os.Getenv("GOSH_CMD") {
		case "exit_0":
			os.Exit(0)
		case "exit_5":
			os.Exit(5)
		case "print_ok":
			fmt.Printf("exec ok\n")
			os.Exit(0)
		case "print_fail":
			fmt.Printf("exec fail\n")
			os.Exit(1)
		case "pid_and_hang":
			fmt.Println(os.Getpid())
			time.Sleep(time.Hour)
			os.Exit(0)
		case "foo_null_bar":
			fmt.Println("foo\x00bar")
			os.Exit(0)
		case "lookpath":
			_, err := exec.LookPath(pathProg)
			if err != nil {
				fmt.Println(err)
				os.Exit(1)
			}
			fmt.Printf("%s found\n", pathProg)
			os.Exit(0)
		}
		r := strings.NewReader(os.Args[1])
		file, err := syntax.NewParser().Parse(r, "")
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		runner, _ := interp.New(
			interp.StdIO(os.Stdin, os.Stdout, os.Stderr),
			interp.ExecHandlers(testExecHandler),
		)
		ctx := context.Background()
		if err := runner.Run(ctx, file); err != nil {
			var es interp.ExitStatus
			if errors.As(err, &es) {
				os.Exit(int(es))
			}

			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		os.Exit(0)
	}

	prog, err := os.Executable()
	if err != nil {
		panic(err)
	}
	os.Setenv("GOSH_PROG", prog)

	shinternal.TestMainSetup()

	hasBash53 = checkBash()
	oracleTildeIgnoresHome = checkOracleTilde()

	wd, err := os.Getwd()
	if err != nil {
		panic(err)
	}
	os.Setenv("GO_TEST_DIR", wd)

	os.Setenv("INTERP_GLOBAL", "value")
	os.Setenv("MULTILINE_INTERP_GLOBAL", "\nwith\nnewlines\n\n")

	// Double check that env vars on Windows are case insensitive.
	if runtime.GOOS == "windows" {
		os.Setenv("mixedCase_INTERP_GLOBAL", "value")
	} else {
		os.Setenv("MIXEDCASE_INTERP_GLOBAL", "value")
	}

	os.Setenv("PATH_PROG", pathProg)

	// To print env vars. Only a builtin on Windows.
	if runtime.GOOS == "windows" {
		os.Setenv("ENV_PROG", "cmd /c set")
	} else {
		os.Setenv("ENV_PROG", "env")
	}

	m.Run()
}

func checkBash() bool {
	out, err := exec.Command("bash", "-c", "echo -n $BASH_VERSION").Output()
	if err != nil {
		return false
	}
	return strings.HasPrefix(string(out), "5.3")
}

// concBuffer wraps a [bytes.Buffer] in a mutex so that concurrent writes
// to it don't upset the race detector.
type concBuffer struct {
	buf bytes.Buffer
	sync.Mutex
}

func (c *concBuffer) Write(p []byte) (int, error) {
	c.Lock()
	n, err := c.buf.Write(p)
	c.Unlock()
	return n, err
}

func (c *concBuffer) WriteString(s string) (int, error) {
	c.Lock()
	n, err := c.buf.WriteString(s)
	c.Unlock()
	return n, err
}

func (c *concBuffer) String() string {
	c.Lock()
	s := c.buf.String()
	c.Unlock()
	return s
}

func (c *concBuffer) Reset() {
	c.Lock()
	c.buf.Reset()
	c.Unlock()
}

type runTest struct {
	in, want string
}

var runTests = []runTest{
	// no-op programs
	{"", ""},
	{"true", ""},
	{":", ""},
	{"exit", ""},
	{"exit 0", ""},
	{"{ :; }", ""},
	{"(:)", ""},

	// exit status codes
	{"exit 1", "exit status 1"},
	{"exit -1", "exit status 255"},
	{"exit 300", "exit status 44"},
	{"false", "exit status 1"},
	{"false foo", "exit status 1"},
	{"! false", ""},
	{"true foo", ""},
	{": foo", ""},
	{"! true", "exit status 1"},
	{"false; true", ""},
	{"false; exit", "exit status 1"},
	{"exit; echo foo", ""},
	{"exit 0; echo foo", ""},
	{"printf", "usage: printf format [arguments]\nexit status 2 #JUSTERR"},
	{"break", "break is only useful in a loop\n #JUSTERR"},
	{"continue", "continue is only useful in a loop\n #JUSTERR"},
	{"cd a b", "cd: too many arguments\nexit status 2 #JUSTERR"},
	// Every one of these is bash's answer, measured (#595). The two that
	// matter most are the third and fourth: koi used to *panic* on a
	// negative count, and to clear the parameters and answer 0 when the
	// count ran past the end, where bash keeps them and answers 1.
	{"shift a", "shift: a: numeric argument required\nexit status 2 #JUSTERR"},
	{"shift 1+1", "shift: 1+1: numeric argument required\nexit status 2 #JUSTERR"},
	{"set -- a b; shift -1", "shift: -1: shift count out of range\nexit status 1 #JUSTERR"},
	{`set -- a b; shift 3; echo "st=$? [$*]"`, "st=1 [a b]\n"},
	{`set -- a b; shift 2; echo "st=$? [$*]"`, "st=0 []\n"},
	{`set -- a b; shift 0; echo "st=$? [$*]"`, "st=0 [a b]\n"},
	{`set -- a b; shift; echo "st=$? [$*]"`, "st=0 [b]\n"},
	// "too many arguments" abandons the input unit where the other two
	// errors do not, so nothing after it on the line runs.
	{
		`set -- a b; shift 1 2; echo unreachable`,
		"shift: too many arguments\nexit status 2 #JUSTERR",
	},
	{
		"shouldnotexist",
		"shouldnotexist: command not found\nexit status 127 #JUSTERR",
	},
	{
		"for i in 1; do continue a; done",
		"usage: continue [n]\nexit status 2 #JUSTERR",
	},
	{
		"for i in 1; do break a; done",
		"usage: break [n]\nexit status 2 #JUSTERR",
	},
	{"false; a=b", ""},
	{"false; false &", ""},
	{
		"GOSH_CMD=exit_0 $GOSH_PROG; echo next",
		"next\n",
	},
	{
		"GOSH_CMD=exit_5 $GOSH_PROG; echo next",
		"next\n",
	},
	{
		"! GOSH_CMD=exit_0 $GOSH_PROG",
		"exit status 1",
	},
	{
		"! GOSH_CMD=exit_5 $GOSH_PROG",
		"",
	},

	// we don't need to follow bash error strings
	{"exit a", "exit: a: numeric argument required\nexit status 2 #JUSTERR"},
	{"exit 1 2", "exit: too many arguments\nexit status 1 #JUSTERR"},
	{"f() { return a; }; f", "return: a: numeric argument required\nexit status 2 #JUSTERR"},

	// echo
	{"echo", "\n"},
	{"echo a b c", "a b c\n"},
	{"echo -n foo", "foo"},
	{`echo -e '\t'`, "\t\n"},
	{`echo -E '\t'`, "\\t\n"},
	{`echo -e 'before\x00after'`, "before\x00after\n"},
	{"echo -x foo", "-x foo\n"},
	{"echo -e -x -e foo", "-x -e foo\n"},

	// printf
	{"printf foo", "foo"},
	{"printf %%", "%"},
	{"printf %", "missing format char\nexit status 1 #JUSTERR"},
	{"printf %; echo foo", "missing format char\nfoo\n #IGNORE"},
	{"printf %1", "missing format char\nexit status 1 #JUSTERR"},
	{"printf %+", "missing format char\nexit status 1 #JUSTERR"},
	{"printf %B foo", "invalid format char: B\nexit status 1 #JUSTERR"},
	{"printf %12-s foo", "invalid format char: -\nexit status 1 #JUSTERR"},
	{"printf ' %s \n' bar", " bar \n"},
	{"printf '\\A'", "\\A"},
	{"printf %s foo", "foo"},
	{"printf %s", ""},
	{"printf %d,%i 3 4", "3,4"},
	{"printf %d", "0"},
	{"printf %d,%d 010 0x10", "8,16"},
	{"printf %c,%c,%c foo àa", "f,\xc3,\x00"}, // TODO: use a rune?
	{"printf %3s a", "  a"},
	{"printf %3i 1", "  1"},
	{"printf %+i%+d 1 -3", "+1-3"},
	{"printf %-5x 10", "a    "},
	{"printf %02x 1", "01"},
	{"printf 'a% 5s' a", "a    a"},
	{"printf 'nofmt' 1 2 3", "nofmt"},
	{"printf '%d_' 1 2 3", "1_2_3_"},
	{"printf '%02d %02d\n' 1 2 3", "01 02\n03 00\n"},
	{`printf '0%s1' 'a\bc'`, `0a\bc1`},
	{`printf '0%b1' 'a\bc'`, "0a\bc1"},
	{"printf 'a%bc'", "ac"},
	{"printf 'before\\x00after'", "before\x00after"},

	// printf escape sequences at end of format string (must not panic)
	{"printf '\\0'", "\x00"},
	{"printf '\\01'", "\x01"},
	{"printf '\\x'", "\\x #IGNORE bash prints a warning to stderr"},
	{"printf 'a\\0'", "a\x00"},
	{"printf '\\\\'", "\\"},

	// words and quotes
	{"echo  foo ", "foo\n"},
	{"echo ' foo '", " foo \n"},
	{`echo " foo "`, " foo \n"},
	{`echo a'b'c"d"e`, "abcde\n"},
	{`a=" b c "; echo $a`, "b c\n"},
	{`a=" b c "; echo "$a"`, " b c \n"},
	{`a=" b c "; echo foo${a}bar`, "foo b c bar\n"},
	{`a="b    c"; echo foo${a}bar`, "foob cbar\n"},
	{`echo "$(echo ' b c ')"`, " b c \n"},
	{"echo \"`echo \\\"foobar\\\"`\"", "foobar\n"},
	{"echo ''", "\n"},
	{`$(echo)`, ""},
	{`echo -n '\\'`, `\\`},
	{`echo -n "\\"`, `\`},
	{`set -- a b c; x="$@"; echo "$x"`, "a b c\n"},
	{`set -- b c; echo a"$@"d`, "ab cd\n"},
	{`count() { echo $#; }; set --; count "$@"`, "0\n"},
	{`count() { echo $#; }; set -- ""; count "$@"`, "1\n"},
	{`count() { echo $#; }; set -- ""; shift; count "$@"`, "0\n"},
	{`count() { echo $#; }; a=(); count "${a[@]}"`, "0\n"},
	{`count() { echo $#; }; count "${unset_var[@]}"`, "0\n"},
	{`count() { echo $#; }; a=(""); count "${a[@]}"`, "1\n"},
	{`echo $1 $3; set -- a b c; echo $1 $3`, "\na c\n"},
	// ${10} and beyond are positional parameters (#362); bare $10 stays
	// $1 followed by 0.
	{`set -- 1 2 3 4 5 6 7 8 9 ten eleven; echo "[${10}][${11}][${12:-none}][$10]"`, "[ten][eleven][none][10]\n"},
	{`[[ $0 == "bash" || $0 == "gosh" ]]`, ""},

	// dollar quotes
	{`echo $'foo\nbar'`, "foo\nbar\n"},
	{`echo $'\r\t\\'`, "\r\t\\\n"},
	{`echo $"foo\nbar"`, "foo\\nbar\n"},
	{`echo $'%s'`, "%s\n"},
	{`a=$'\r\t\\'; echo "$a"`, "\r\t\\\n"},
	{`a=$"foo\nbar"; echo "$a"`, "foo\\nbar\n"},
	{`echo $'\a\b\e\E\f\v'`, "\a\b\x1b\x1b\f\v\n"},
	{`echo $'\\\'\"\?'`, "\\'\"?\n"},
	{`echo $'\1\45\12345\777\9'`, "\x01%S45\xff\\9\n"},
	{`echo $'\x\xf\x09\xAB'`, "\\x\x0f\x09\xab\n"},
	{`echo $'\u\uf\u09\uABCD\u00051234'`, "\\u\u000f\u0009\uabcd\u00051234\n"},
	{`echo $'\U\Uf\U09\UABCD\U00051234'`, "\\U\u000f\u0009\uabcd\U00051234\n"},
	{
		"echo 'before\x00after'",
		"beforeafter\n",
	},
	{
		"echo \"before\x00after\"",
		"beforeafter\n",
	},
	{
		"echo $'before\x00after'",
		"beforeafter\n",
	},
	{
		"echo $'before\\x00after'",
		"before\n",
	},
	{
		"echo $'before\\xafter'",
		"before\xafter\n",
	},
	{
		"a='before\x00after'; eval \"echo -n ${a} ${a@Q}\";",
		"beforeafter beforeafter",
	},
	{
		"a=$'before\\x00after'; eval \"echo -n ${a} ${a@Q}\";",
		"before before",
	},
	{
		"i\x00f true; then echo before\x00; \x00fi",
		"before\n",
	},
	{
		"echo $(GOSH_CMD=foo_null_bar $GOSH_PROG)",
		"foobar\n #IGNORE",
	},
	// See the TODO where foo_NULL_BAR is set.
	// {
	// 	"echo $foo_NULL_BAR \"${foo_NULL_BAR}\"",
	// 	"foo\n",
	// },

	// escaped chars
	{"echo a\\b", "ab\n"},
	{"echo a\\ b", "a b\n"},
	{"echo \\$a", "$a\n"},
	{"echo \"a\\b\"", "a\\b\n"},
	{"echo 'a\\b'", "a\\b\n"},
	{"echo \"a\\\nb\"", "ab\n"},
	{"echo 'a\\\nb'", "a\\\nb\n"},
	{`echo "\""`, "\"\n"},
	{`echo \\`, "\\\n"},
	{`echo \\\\`, "\\\\\n"},
	{`echo \`, "\\\n"},

	// escape characters in double quote literal
	{`echo "\\"`, "\\\n"},     // special character is preserved
	{`echo "\b"`, "\\b\n"},    // non-special character has both characters preserved
	{`echo "\\\\"`, "\\\\\n"}, // sequential backslashes (escape characters repeated sequentially)

	// vars
	{"foo=bar; echo $foo", "bar\n"},
	{"foo=bar foo=etc; echo $foo", "etc\n"},
	{"foo=bar; foo=etc; echo $foo", "etc\n"},
	{"foo=bar; foo=; echo $foo", "\n"},
	{"unset foo; echo $foo", "\n"},
	{"foo=bar; unset foo; echo $foo", "\n"},
	{"echo $INTERP_GLOBAL", "value\n"},
	{"INTERP_GLOBAL=; echo $INTERP_GLOBAL", "\n"},
	{"unset INTERP_GLOBAL; echo $INTERP_GLOBAL", "\n"},
	{"echo $MIXEDCASE_INTERP_GLOBAL", "value\n"},
	{"foo=bar; foo=x true; echo $foo", "bar\n"},
	{"foo=bar; foo=x true; echo $foo", "bar\n"},
	{"foo=bar; $ENV_PROG | grep '^foo='", "exit status 1"},
	{"foo=bar $ENV_PROG | grep '^foo='", "foo=bar\n"},
	{"foo=a foo=b $ENV_PROG | grep '^foo='", "foo=b\n"},
	{"$ENV_PROG | grep -i '^interp_global='", "INTERP_GLOBAL=value\n"},
	{"INTERP_GLOBAL=new; $ENV_PROG | grep -i '^interp_global='", "INTERP_GLOBAL=new\n"},
	{"INTERP_GLOBAL=; $ENV_PROG | grep -i '^interp_global='", "INTERP_GLOBAL=\n"},
	{"unset INTERP_GLOBAL; $ENV_PROG | grep -i '^interp_global='", "exit status 1"},
	{"a=b; a+=c x+=y; echo $a $x", "bc y\n"},
	{`a=" x  y"; b=$a c="$a"; echo $b; echo $c`, "x y\nx y\n"},
	{`a=" x  y"; b=$a c="$a"; echo "$b"; echo "$c"`, " x  y\n x  y\n"},
	{`arr=("foo" "bar" "lala" "foobar"); echo ${arr[@]:2}; echo ${arr[*]:2}`, "lala foobar\nlala foobar\n"},
	{`arr=("foo" "bar" "lala" "foobar"); echo ${arr[@]:2:4}; echo ${arr[*]:1:4}`, "lala foobar\nbar lala foobar\n"},
	{`arr=("foo" "bar"); echo ${arr[@]}; echo ${arr[*]}`, "foo bar\nfoo bar\n"},
	{`arr=("foo"); echo ${arr[@]:99}`, "\n"},
	{`echo ${arr[@]:1:99}; echo ${arr[*]:1:99}`, "\n\n"},
	{`arr=(0 1 2 3 4 5 6 7 8 9 0 a b c d e f g h); echo ${arr[@]:3:4}`, "3 4 5 6\n"},

	// quoted array slicing
	{`a=(1 2 3 4 5); echo "${a[@]:2:2}"`, "3 4\n"},
	{`a=(1 2 3 4 5); echo "${a[*]:2:2}"`, "3 4\n"},
	{`a=(1 2 3 4 5); b=("${a[@]:2:2}"); echo ${#b[@]}`, "2\n"},
	{`a=(1 2 3 4 5); echo "${a[@]:3}"`, "4 5\n"},
	{`a=(1 2 3 4 5); echo "${a[@]: -2}"`, "4 5\n"},
	{`a=(1 2 3 4 5); echo "${a[@]: -99}"`, "\n"},

	// positional parameter slicing (1-based offset, $0 at offset 0)
	{`f() { echo "${@:2:2}"; }; f a b c d e`, "b c\n"},
	{`f() { echo ${@:2:2}; }; f a b c d e`, "b c\n"},
	{`f() { echo "${@:1}"; }; f a b c`, "a b c\n"},
	{`f() { echo "${*:2:2}"; }; f a b c d e`, "b c\n"},
	{`f() { echo "${@: -2}"; }; f a b c d e`, "d e\n"},
	{`f() { echo "${@: -3:2}"; }; f a b c d e`, "c d\n"},
	{`f() { echo "${@:1:0}"; }; f a b c`, "\n"},
	{`f() { echo "${@:99}"; }; f a b c`, "\n"},
	{`set -- a b c; v=("${@:0:2}"); echo "${#v[@]}"`, "2\n"},
	{`f() { for x in "${@:2:2}"; do echo "$x"; done; }; f a b c d e`, "b\nc\n"},
	{`set --; v=("${@:0}"); echo "${#v[@]}"`, "1\n"},
	{`f() { echo "${@: -10}"; }; f a b c`, "\n"},

	{`echo ${foo[@]}; echo ${foo[*]}`, "\n\n"},
	// TODO: reenable once we figure out the broken pipe error
	//{`$ENV_PROG | while read line; do if test -z "$line"; then echo empty; fi; break; done`, ""}, // never begin with an empty element

	// inline variables have special scoping
	{
		"f() { echo $inline; inline=bar true; echo $inline; }; inline=foo f",
		"foo\nfoo\n",
	},
	{"v=x; read v <<< 'y'; echo $v", "y\n"},
	{"v=x; v=inline read v <<< 'y'; echo $v", "x\n"},
	{"v=x; v=inline unset v; echo $v", "x\n"},
	{"v=x; echo 'v=y' >f; v=inline source ./f; echo $v", "x\n"},
	{"declare -n v=v2; v=inline true; echo $v $v2", "\n"},
	{"f() { echo $v; }; v=x; v=y f; f", "y\nx\n"},
	{"f() { echo $v; }; v=x; v+=y f; f", "xy\nx\n"},
	{"f() { echo $v; }; declare -n v=v2; v2=x; v=y f; f", "y\nx\n"},
	{"f() { echo ${v[@]}; }; v=(e1 e2); v=y f; f", "y\ne1 e2\n"},

	// special vars
	{"echo $?; false; echo $?", "0\n1\n"},
	{"for i in 1 2; do\necho $LINENO\necho $LINENO\ndone", "2\n3\n2\n3\n"},
	{"[[ -n $$ && $$ -gt 0 ]]", ""},
	{"[[ $$ -eq $PPID ]]", "exit status 1"},
	{"[[ $RANDOM -eq $RANDOM ]]", "exit status 1"}, // 1 in 32k chance of a collision, 0.003%
	// Assigning RANDOM seeds it, which is the whole reason the idiom
	// exists (#547). The claim is that a seed repeats *in koi* — never
	// that it reproduces bash's digits, which are bash's generator and
	// not part of its interface (#120) — so every case here compares
	// two runs of the same seed rather than a literal.
	{`RANDOM=42; a="$RANDOM $RANDOM $RANDOM"; RANDOM=42; [[ $a == "$RANDOM $RANDOM $RANDOM" ]]`, ""},
	{`RANDOM=1+1; a=$RANDOM; RANDOM=2; [[ $a == "$RANDOM" ]]`, ""}, // the value is arithmetic
	{`x=3; RANDOM=x; a=$RANDOM; RANDOM=3; [[ $a == "$RANDOM" ]]`, ""},
	{`RANDOM=42; a=$RANDOM; RANDOM=43; [[ $a == "$RANDOM" ]]`, "exit status 1"},
	// A subshell draws its own numbers and leaves this sequence where
	// it was, which is what makes a seeded run repeatable at all.
	{`RANDOM=7; x=$(echo $RANDOM); a="$RANDOM $RANDOM"; RANDOM=7; [[ $a == "$RANDOM $RANDOM" ]]`, ""},
	{`RANDOM=5; [[ $RANDOM -ge 0 && $RANDOM -le 32767 ]]`, ""},
	// Unsetting a computed variable ends its specialness for the rest
	// of the shell: it reads empty, and an assignment makes it an
	// ordinary variable rather than a seed.
	{`unset RANDOM; echo "[$RANDOM]"`, "[]\n"},
	{`unset RANDOM; RANDOM=5; echo "[$RANDOM]"`, "[5]\n"},
	{`unset SECONDS; echo "[$SECONDS]"`, "[]\n"},
	{`unset EPOCHSECONDS; echo "[$EPOCHSECONDS]"`, "[]\n"},
	// SECONDS counts from where it is set. Its value is a whole
	// integer or zero — not arithmetic, unlike RANDOM's, which is
	// measured rather than reasoned from the one next to it.
	{"SECONDS=100; echo $SECONDS", "100\n"},
	{"SECONDS=-5; echo $SECONDS", "-5\n"},
	{"SECONDS=1+1; echo $SECONDS", "0\n"},
	{"SECONDS=abc; echo $SECONDS", "0\n"},
	{"SECONDS=; echo $SECONDS", "0\n"},
	{"[[ $SRANDOM -eq $SRANDOM ]]", "exit status 1"}, // 1 in 2**32 chance of a collision,

	// Ensure that we consistently use 64 bits even on 32-bit platforms.
	// Bash doesn't do this, but we do, for portability and consistency.
	{"[[ 1000000000123 -lt 100 ]]", "exit status 1"},
	{"[[ 1000000000123 -eq 1000000000456 ]]", "exit status 1"},
	{"[[ 1000000000123 < 100 ]]", "exit status 1"},
	{"((1000000000123 == 1000000000456))", "exit status 1"},

	// var manipulation
	{"echo ${#a} ${#a[@]}", "0 0\n"},
	{"a=bar; echo ${#a} ${#a[@]}", "3 1\n"},
	{"a=世界; echo ${#a}", "2\n"},
	{"a=(a bcd); echo ${#a} ${#a[@]} ${#a[*]} ${#a[1]}", "1 2 2 3\n"},
	{
		"a=($(echo a bcd)); echo ${#a} ${#a[@]} ${#a[*]} ${#a[1]}",
		"1 2 2 3\n",
	},
	{
		"a=([0]=$(echo a b) $(echo c d)); echo ${#a} ${#a[@]} ${#a[*]} ${#a[0]}",
		"3 3 3 3\n",
	},
	{"set -- a bc; echo ${#@} ${#*} $#", "2 2 2\n"},
	{
		"echo ${!a}; echo more",
		"a: invalid indirect expansion\nexit status 1 #JUSTERR",
	},
	{
		"a=b; echo ${!a}; b=c; echo ${!a}",
		"\nc\n",
	},
	// An operator after the indirection applies to the target (#277):
	// substitution and trims rewrite the target's value, a slice cuts
	// it, and a default fires on the target being unset. All were
	// silently dropped, so ${!x//c/X} answered the unsubstituted value.
	{`x=var; var=abcde; echo "${!x//c/X}"`, "abXde\n"},
	{`x=var; var=abcde; echo "${!x:1:2}"`, "bc\n"},
	{`x=var; var=abcde; echo "${!x%de}"`, "abc\n"},
	{`x=var; var=abcde; echo "${!x:-def}"`, "abcde\n"},
	{`x=var; unset var; echo "${!x-def}"`, "def\n"},
	// An empty or invalid target name is an error in bash, never a
	// silent empty string — silence made ${!x} with a garbage x read
	// as an unset variable.
	{
		`foo=; echo "${!foo-def}"`,
		": invalid variable name\nexit status 1 #JUSTERR",
	},
	{
		`x='a b'; echo "${!x}"`,
		"a b: invalid variable name\nexit status 1 #JUSTERR",
	},
	{
		"a=foo_very_long; echo ${a:1}; echo ${a: -1}; echo ${a: -10}; echo ${a:5}",
		"oo_very_long\ng\n_very_long\nery_long\n",
	},
	{
		"a=foo_very_long; echo ${a::2}; echo ${a::-1}; echo ${a: -10}; echo ${a::5}",
		"fo\nfoo_very_lon\n_very_long\nfoo_v\n",
	},
	{
		"a=abc; echo ${a:1:1}",
		"b\n",
	},
	{
		`a=héllo; echo "${a:2}" "${a:1:2}" "${a::-3}" "${a: -2}"`,
		"llo él hé lo\n",
	},
	{
		"a=foo; echo ${a/no/x} ${a/o/i} ${a//o/i} ${a/fo/}",
		"foo fio fii o\n",
	},
	{
		"a=foo; echo ${a/*/xx} ${a//?/na} ${a/o*}",
		"xx nanana f\n",
	},
	{
		"a=12345; echo ${a//[42]} ${a//[^42]} ${a//[!42]}",
		"135 24 24\n",
	},
	{"a=0123456789; echo ${a//[1-35-8]}", "049\n"},
	{"a=]abc]; echo ${a//[]b]}", "ac\n"},
	{"a=-abc-; echo ${a//[-b]}", "ac\n"},
	{`a='x\y'; echo ${a//\\}`, "xy\n"},
	{"a=']'; echo ${a//[}", "]\n"},
	{"a=']'; echo ${a//[]}", "]\n"},
	{"a=']'; echo ${a//[]]}", "\n"},
	{"a='['; echo ${a//[[]}", "\n"},
	{"a=']'; echo ${a//[xy}", "]\n"},
	{"a='abc123'; echo ${a//[[:digit:]]}", "abc\n"},
	{"a='[[:wrong:]]'; echo ${a//[[:wrong:]]}", "[[:wrong:]]\n"},
	{"a='[[:wrong:]]'; echo ${a//[[:}", "[[:wrong:]]\n"},
	{"a='abcx1y'; echo ${a//x[[:digit:]]y}", "abc\n"},
	{`a=xyz; echo "${a/y/a  b}"`, "xa  bz\n"},
	{"a='foo/bar'; echo ${a//o*a/}", "fr\n"},
	{"a=foobar; echo ${a//a/} ${a///b} ${a///}", "foobr foobar foobar\n"},
	{
		"echo ${a:-b}; echo $a; a=; echo ${a:-b}; a=c; echo ${a:-b}",
		"b\n\nb\nc\n",
	},
	{
		"echo ${#:-never} ${?:-never} ${LINENO:-never}",
		"0 0 1\n",
	},
	{
		"echo ${1-one} ${2-two} ${3-three}",
		"one two three\n",
	},
	{
		"set -u; echo ${1}",
		"1: unbound variable\nexit status 1 #JUSTERR",
	},
	{
		"echo ${a-b}; echo $a; a=; echo ${a-b}; a=c; echo ${a-b}",
		"b\n\n\nc\n",
	},
	{
		"echo ${a:=b}; echo $a; a=; echo ${a:=b}; a=c; echo ${a:=b}",
		"b\nb\nb\nc\n",
	},
	{
		"echo ${a=b}; echo $a; a=; echo ${a=b}; a=c; echo ${a=b}",
		"b\nb\n\nc\n",
	},
	{
		"echo ${a:+b}; echo $a; a=; echo ${a:+b}; a=c; echo ${a:+b}",
		"\n\n\nb\n",
	},
	{
		"echo ${a+b}; echo $a; a=; echo ${a+b}; a=c; echo ${a+b}",
		"\n\nb\nb\n",
	},
	{
		"a=b; echo ${a:?err1}; a=; echo ${a:?err2}; unset a; echo ${a:?err3}",
		"b\na: err2\nexit status 1 #JUSTERR",
	},
	{
		"a=b; echo ${a?err1}; a=; echo ${a?err2}; unset a; echo ${a?err3}",
		"b\n\na: err3\nexit status 1 #JUSTERR",
	},
	{
		"echo ${a:?%s}",
		"a: %s\nexit status 1 #JUSTERR",
	},
	{
		"x=aaabccc; echo ${x#*a}; echo ${x##*a}",
		"aabccc\nbccc\n",
	},
	{
		"x=(__a _b c_); echo ${x[@]#_}",
		"_a b c_\n",
	},
	{
		"x=(a__ b_ _c); echo ${x[@]%%_}",
		"a_ b _c\n",
	},
	{
		"x=aaabccc; echo ${x%c*}; echo ${x%%c*}",
		"aaabcc\naaab\n",
	},
	{
		"x=aaabccc; echo ${x%%[bc}",
		"aaabccc\n",
	},
	{
		"a='àÉñ bAr'; echo ${a^}; echo ${a^^}",
		"ÀÉñ bAr\nÀÉÑ BAR\n",
	},
	{
		"a='àÉñ bAr'; echo ${a,}; echo ${a,,}",
		"àÉñ bAr\nàéñ bar\n",
	},
	{
		"a='àÉñ bAr'; echo ${a^?}; echo ${a^^[br]}",
		"ÀÉñ bAr\nàÉñ BAR\n",
	},
	{
		"a='àÉñ bAr'; echo ${a,?}; echo ${a,,[br]}",
		"àÉñ bAr\nàÉñ bAr\n",
	},
	{
		"a=foo; echo ${a^o} ${a^f}; a=OOF; echo ${a,O} ${a,,O} ${a,o}",
		"foo Foo\noOF ooF OOF\n",
	},
	{
		"a=(àÉñ bAr); echo ${a[@]^}; echo ${a[*],,}",
		"ÀÉñ BAr\nàéñ bar\n",
	},
	{
		`a=(foo boo); printf '[%s]' "${a[@]%o}"; echo; printf '[%s]' "${a[@]/o/O}"; echo; printf '[%s]' "${a[@]^}"; echo`,
		"[fo][bo]\n[fOo][bOo]\n[Foo][Boo]\n",
	},
	{
		`set -- foo boo; printf '[%s]' "${@#?}"; echo; IFS=,; echo "${*%o}"`,
		"[oo][oo]\nfo,bo\n",
	},
	{
		`a=(foo boo); IFS=,; echo "${a[*]%o}"`,
		"fo,bo\n",
	},
	{
		`a=(aax abx); echo ${a[@]/x/}; b=("${a[@]/a/z}"); echo "${b[0]}" "${b[1]}"`,
		"aa ab\nzax zbx\n",
	},
	{
		"a=(foo boo); echo ${a[@]%o}; echo ${a[@]}",
		"fo bo\nfoo boo\n",
	},
	{
		"INTERP_X_1=a INTERP_X_2=b; echo ${!INTERP_X_*}",
		"INTERP_X_1 INTERP_X_2\n",
	},
	{
		"INTERP_X_2=b INTERP_X_1=a; echo ${!INTERP_*}",
		"INTERP_GLOBAL INTERP_X_1 INTERP_X_2\n",
	},
	{
		`INTERP_X_2=b INTERP_X_1=a; set -- ${!INTERP_*}; echo $#`,
		"3\n",
	},
	{
		`INTERP_X_2=b INTERP_X_1=a; set -- "${!INTERP_*}"; echo $#`,
		"1\n",
	},
	{
		`INTERP_X_2=b INTERP_X_1=a; set -- ${!INTERP_@}; echo $#`,
		"3\n",
	},
	{
		`INTERP_X_2=b INTERP_X_1=a; set -- "${!INTERP_@}"; echo $#`,
		"3\n",
	},
	{
		`a='b  c'; eval "echo -n ${a} ${a@Q}"`,
		`b c b  c`,
	},
	{
		`a='"\n'; printf "%s %s" "${a}" "${a@E}"`,
		"\"\\n \"\n",
	},

	// ${var@a} and ${var@A}
	{
		`a=foo; echo "<${a@a}>"`,
		"<>\n",
	},
	{
		`declare -a arr=(1 2 3); echo "${arr@a}"`,
		"a\n",
	},
	{
		`declare -A map=([k]=v); echo "${map@a}"`,
		"A\n",
	},
	{
		`export e=1; echo "${e@a}"`,
		"x\n",
	},
	{
		`readonly ro=1; echo "${ro@a}"`,
		"r\n",
	},
	{
		`declare -a arr=(1); export arr; echo "${arr@a}"`,
		"ax\n",
	},
	{
		// `@A` quotes its value with `@Q`, which single-quotes
		// unconditionally (#648).
		`a=hello; echo "${a@A}"`,
		"a='hello'\n",
	},
	{
		`export e=1; echo "${e@A}"`,
		"declare -x e='1'\n",
	},
	{
		`a=Hello; echo "${a@U}"`,
		"HELLO\n",
	},
	{
		`a=hello; echo "${a@u}"`,
		"Hello\n",
	},
	{
		`a=HELLO; echo "${a@L}"`,
		"hello\n",
	},
	{
		// `@K` and `@k` are `@Q` for anything that is not a whole array
		// (#647).
		`a=foo; echo "<${a@K}><${a@k}>"`,
		"<'foo'><'foo'>\n",
	},
	{
		"declare a; a+=(b); echo ${a[@]} ${#a[@]}",
		"b 1\n",
	},
	{
		`a=""; a+=(b); echo ${a[@]} ${#a[@]}`,
		"b 2\n",
	},
	{
		"f() { local a; a=bad; a=good; echo $a; }; f",
		"good\n",
	},
	{
		`declare x; [[ -v x ]] && echo set || echo unset`,
		"unset\n",
	},
	{
		`declare x=; [[ -v x ]] && echo set || echo unset`,
		"set\n",
	},
	{
		`declare -a x; [[ -v x ]] && echo set || echo unset`,
		"unset\n",
	},
	{
		`declare -A x; [[ -v x ]] && echo set || echo unset`,
		"unset\n",
	},
	{
		`declare -r -x x; [[ -v x ]] && echo set || echo unset`,
		"unset\n",
	},
	{
		`declare -n x; [[ -v x ]] && echo set || echo unset`,
		"unset\n",
	},

	// compgen
	{
		`g() { :; }; a() { :; }; compgen -A function`,
		"a\ng\n",
	},
	{
		// a word operand is a prefix to match
		`foo() { :; }; fob() { :; }; bar() { :; }; compgen -A function fo`,
		"fob\nfoo\n",
	},
	{
		// no matches is a non-zero status, as bash reports it
		`compgen -A function; echo "st=$?"`,
		"st=1\n",
	},
	{
		`foo() { :; }; compgen -A function zz; echo "st=$?"`,
		"st=1\n",
	},
	{
		`alias foo=bar; compgen -A alias`,
		"foo\n",
	},
	{
		`alias zz=ls; compgen -a`,
		"zz\n",
	},
	{
		`xyzzy=1; compgen -A variable xyzzy`,
		"xyzzy\n",
	},
	{
		`xyzzy=1; compgen -v xyzzy`,
		"xyzzy\n",
	},
	{
		// the actions which are not implemented are refused rather than
		// answering nothing, which for compgen would be indistinguishable
		// from a correct empty answer
		`compgen -A directory`,
		"compgen: -A \"directory\": NOT IMPLEMENTED action\nexit status 2 #IGNORE bash implements this action",
	},

	// FUNCNEST bounds function nesting (#349). The violation unwinds the
	// whole function stack and the top level resumes: the rest of the
	// violating line is lost, the next line runs with status 1.
	{
		"FUNCNEST=2; f(){ echo f; g; }; g(){ echo g; h; }; h(){ echo h; }; f; echo never",
		"f\ng\nh: maximum function nesting level exceeded (2)\nexit status 1 #JUSTERR",
	},
	{
		"FUNCNEST=1\nf(){ g; echo never; }\ng(){ :; }\nf\necho st=$?",
		"g: maximum function nesting level exceeded (1)\nst=1\n #JUSTERR",
	},
	{
		// A runaway f(){ f; } dies cleanly instead of hanging the shell.
		"FUNCNEST=20\nx=0\nf(){ x=$((x+1)); f; }\nf\necho x=$x st=$?",
		"f: maximum function nesting level exceeded (20)\nx=20 st=1\n #JUSTERR",
	},
	{
		// Zero and non-numeric values do not bind.
		"FUNCNEST=0; n=0; f(){ n=$((n+1)); [ $n -lt 3 ] && f; }; f; echo n=$n",
		"n=3\n",
	},
	{
		"FUNCNEST=abc; n=0; f(){ n=$((n+1)); [ $n -lt 3 ] && f; }; f; echo n=$n",
		"n=3\n",
	},

	// FUNCNAME
	{
		`f() { echo "[${FUNCNAME[0]:-MISSING}]"; }; f`,
		"[f]\n",
	},
	{
		// innermost first, like bash
		`g() { echo "[${FUNCNAME[@]}]"; }; f() { g; }; f`,
		"[g f]\n",
	},
	{
		`g() { echo "[${FUNCNAME[1]}]"; }; f() { g; }; f`,
		"[f]\n",
	},
	{
		// unset at the top level, and again once the call returns
		`echo "[${FUNCNAME[@]:-EMPTY}] n=${#FUNCNAME[@]}"`,
		"[EMPTY] n=0\n",
	},
	{
		`f() { :; }; f; echo "[${FUNCNAME[@]:-EMPTY}]"`,
		"[EMPTY]\n",
	},
	{
		`g() { :; }; f() { g; echo "[${FUNCNAME[@]}]"; }; f`,
		"[f]\n",
	},
	{
		// a subshell inside a function is still inside it
		`f() { ( echo "[${FUNCNAME[0]}]" ); }; f`,
		"[f]\n",
	},

	// declare -i
	{
		`declare -i n; n=1+1; echo "[$n]"`,
		"[2]\n",
	},
	{
		`declare -i n=2+3; echo "[$n]"`,
		"[5]\n",
	},
	{
		// a name which is not set is zero in arithmetic, so this is not an error
		`declare -i n; n=abc; echo "[$n]"`,
		"[0]\n",
	},
	{
		`declare -i n; n=; echo "[$n]"`,
		"[0]\n",
	},
	{
		// += adds rather than concatenating
		`declare -i n=1; n+=2; echo "[$n]"`,
		"[3]\n",
	},
	{
		`declare -i n; m=3; n=m*2; echo "[$n]"`,
		"[6]\n",
	},
	{
		`declare -i n; n=7/2; echo "[$n]"`,
		"[3]\n",
	},
	{
		// the attribute does not re-evaluate what is already there
		`x=abc; declare -i x; echo "[$x]"`,
		"[abc]\n",
	},
	{
		`declare -i n=1; declare +i n; n=1+1; echo "[$n]"`,
		"[1+1]\n",
	},
	{
		`f() { local -i n; n=2+2; echo "[$n]"; }; f`,
		"[4]\n",
	},
	{
		`declare -ia a; a[0]=1+1; echo "[${a[0]}]"`,
		"[2]\n",
	},
	{
		`declare -i n=2; declare -p n`,
		`declare -i n="2"` + "\n",
	},
	{
		// every flag clustered into one argument applies, not just the first
		`declare -ri n=1+1; declare -p n`,
		`declare -ir n="2"` + "\n",
	},
	{
		`declare -ix n=1+1; declare -p n`,
		`declare -ix n="2"` + "\n",
	},
	{
		`declare -rx v=1; declare -p v`,
		`declare -rx v="1"` + "\n",
	},
	{
		`declare -ia a=(1); declare -p a`,
		`declare -ai a=([0]="1")` + "\n",
	},

	// The array attribute is sticky (#378): a naked declare -a/-A
	// declares an unset array that prints bare, a later scalar
	// assignment fills element 0 instead of flattening to a scalar,
	// converting a scalar keeps its value at element 0, and converting
	// one array kind to the other is an error with the data kept.
	{
		`declare -a c; declare -p c`,
		"declare -a c\n",
	},
	{
		`declare -A m; declare -p m`,
		"declare -A m\n",
	},
	{
		`declare -a c; c=4; declare -p c`,
		`declare -a c=([0]="4")` + "\n",
	},
	{
		`declare -a r; r="(5)"; declare -p r`,
		`declare -a r=([0]="(5)")` + "\n",
	},
	{
		`x=5; declare -a x; declare -p x`,
		`declare -a x=([0]="5")` + "\n",
	},
	{
		`x=5; declare -A x; declare -p x`,
		`declare -A x=([0]="5" )` + "\n",
	},
	{
		`declare -a q=5; declare -p q`,
		`declare -a q=([0]="5")` + "\n",
	},
	{
		`declare -a x=(1); declare -A x; echo rc=$?; declare -p x`,
		"declare: x: cannot convert indexed to associative array\nrc=1\n" +
			`declare -a x=([0]="1")` + "\n #JUSTERR",
	},
	{
		`declare -A m=([k]=v); declare -a m; echo rc=$?; declare -p m`,
		"declare: m: cannot convert associative to indexed array\nrc=1\n" +
			`declare -A m=([k]="v" )` + "\n #JUSTERR",
	},
	{
		`declare -ia n; n=2+3; declare -p n`,
		`declare -ai n=([0]="5")` + "\n",
	},
	{
		`declare -a d; d[3]=x; declare -p d`,
		`declare -a d=([3]="x")` + "\n",
	},
	{
		`declare -a e; e+=(z); declare -p e`,
		`declare -a e=([0]="z")` + "\n",
	},
	{
		`a=(1 2); export a=5; declare -p a`,
		`declare -ax a=([0]="5" [1]="2")` + "\n",
	},
	{
		`declare -A f=([a]=b); declare f[qux]=assigned; echo "${f[qux]}-${f[a]}"`,
		"assigned-b\n",
	},
	{
		`declare -A m=([a]=b); m=x; echo "${m[0]}-${m[a]}"`,
		"x-b\n",
	},

	// The shell's own arrays are listed, and a subscript declares one
	// (#616). The computed variables (#547) are answered from the
	// runner rather than stored, so a listing built from the variable
	// table alone saw none of them — `declare -a` named not one of the
	// arrays the shell itself maintains. That is #547's shape at a
	// third reader, after lookupVar and after setVar/unset.
	//
	// Each listing case asserts *both* halves, because a containment
	// check passes against a listing that contains everything: the
	// computed array present and an ordinary variable absent.
	{
		`declare -p FUNCNAME`,
		"declare -a FUNCNAME\n",
	},
	{
		`f(){ declare -p FUNCNAME; }; f`,
		`declare -a FUNCNAME=([0]="f")` + "\n",
	},
	{
		`f(){ declare -p BASH_LINENO; }; f`,
		`declare -a BASH_LINENO=([0]="1")` + "\n",
	},
	{
		`declare -p BASH_SOURCE`,
		`declare -a BASH_SOURCE=()` + "\n",
	},
	{
		`s=plain; l=$(declare -a); case $l in *"declare -a FUNCNAME"*) echo has-funcname;; *) echo no-funcname;; esac; ` +
			`case $l in *"s=plain"*) echo has-s;; *) echo no-s;; esac`,
		"has-funcname\nno-s\n",
	},
	{
		`l=$(declare -a); for n in BASH_LINENO BASH_SOURCE DIRSTACK GROUPS; do ` +
			`case $l in *"declare -a $n="*) echo "$n yes";; *) echo "$n no";; esac; done`,
		"BASH_LINENO yes\nBASH_SOURCE yes\nDIRSTACK yes\nGROUPS yes\n",
	},
	{
		// An indexed array is not an associative one: the same names
		// must stay out of `declare -A`.
		`l=$(declare -A); case $l in *FUNCNAME*) echo bad;; *) echo good;; esac`,
		"good\n",
	},
	{
		// Unsetting a computed variable ends its specialness for the
		// rest of the shell (#547), and the listing has to agree —
		// FUNCNAME is listed while never being *set*, so the unset is
		// recorded whether or not there was a value.
		`unset FUNCNAME; declare -p FUNCNAME 2>/dev/null; echo rc=$?; ` +
			`l=$(declare -a); case $l in *FUNCNAME*) echo bad;; *) echo good;; esac`,
		"rc=1\ngood\n",
	},

	// The attribute filters compose, which is three commands
	// array.tests runs in a row (#616): `readonly -a` and `declare -ar`
	// are the arrays that are also readonly, and `export -a` lists
	// nothing at all, where taking the first filter alone listed every
	// array in the shell.
	{
		`a=(1 2); readonly a; b=(3); l=$(readonly -a); ` +
			`case $l in *" a="*) echo has-a;; *) echo no-a;; esac; ` +
			`case $l in *" b="*) echo has-b;; *) echo no-b;; esac`,
		"has-a\nno-b\n",
	},
	{
		`a=(1 2); readonly a; b=(3); l=$(declare -ar); ` +
			`case $l in *" a="*) echo has-a;; *) echo no-a;; esac; ` +
			`case $l in *" b="*) echo has-b;; *) echo no-b;; esac`,
		"has-a\nno-b\n",
	},
	{
		`a=(1 2); l=$(export -a); case $l in *" a="*) echo has-a;; *) echo no-a;; esac`,
		"no-a\n",
	},
	{
		// POSIX mode names the builtin instead of `declare`, and shows
		// the array kind as the only attribute — both halves, since the
		// ordinary form must not change.
		`a=(1); readonly a; set -o posix; l=$(readonly -a); ` +
			`case $l in *"readonly -a a=([0]=\"1\")"*) echo posix-form;; *) echo other;; esac; ` +
			`set +o posix; l=$(readonly -a); ` +
			`case $l in *"declare -ar a=([0]=\"1\")"*) echo declare-form;; *) echo other;; esac`,
		"posix-form\ndeclare-form\n",
	},

	// A naked declaration whose name carries a subscript declares an
	// *indexed array* (#616), which is what array.tests' `declare -r
	// c[100]` needs: koi left the name a scalar, so the readonly
	// declared-but-unset array was in no `declare -a` listing and a
	// script could not tell it from a name never declared.
	{
		`declare -r c[100]; declare -p c`,
		"declare -ar c\n",
	},
	{
		`declare d[2]; declare -p d`,
		"declare -a d\n",
	},
	{
		`f(){ local h[1]; declare -p h; }; f`,
		"declare -a h\n",
	},
	{
		`x=scalar; declare x[3]; declare -p x`,
		`declare -a x=([0]="scalar")` + "\n",
	},
	{
		// An explicit -A still wins.
		`declare -A m[k]; declare -p m`,
		"declare -A m\n",
	},
	{
		// Per name, not per command.
		`declare d[2] e=1; declare -p d; declare -p e`,
		"declare -a d\n" + `declare -- e="1"` + "\n",
	},

	// `readonly` and `export` take names, and a subscript is not one
	// (#616): both refuse it, answer 1, and carry on to the next name.
	// declare/typeset/local accept one and write the element.
	{
		`a=(1); readonly a[5] 2>/dev/null; echo rc=$?; declare -p a`,
		"rc=1\n" + `declare -a a=([0]="1")` + "\n",
	},
	{
		`readonly a[5] z=1 2>/dev/null; echo rc=$?; declare -p z`,
		"rc=1\n" + `declare -r z="1"` + "\n",
	},
	{
		`export q[1]=1 2>/dev/null; echo rc=$?; echo "q=${q-unset}"`,
		"rc=1\nq=unset\n",
	},
	{
		`readonly a[]=x 2>/dev/null; echo rc=$?`,
		"rc=1\n",
	},
	{
		`readonly "a[*]"=x 2>/dev/null; echo rc=$?`,
		"rc=1\n",
	},
	// A temp-env assignment before a declaration utility (#380): the
	// binding is what the utility sees, and when the utility declares
	// the name — not merely queries it — the binding is promoted in
	// its scope instead of unwound; a function-local declaration
	// shadows the promoted scope, so the unwind lands underneath it.
	{
		`func(){ var=value declare -x var; echo -n "inside: "; declare -p var; }; var=one; func; echo -n "outside: "; declare -p var`,
		`inside: declare -x var="value"` + "\noutside: " + `declare -- var="one"` + "\n",
	},
	{
		`foo="" export foo; declare -p foo`,
		`declare -x foo=""` + "\n",
	},
	{
		`foo=bar declare -p foo; echo after: ${foo-unset}`,
		`declare -x foo="bar"` + "\nafter: unset\n",
	},
	{
		`tempvar1=foo declare -r tempvar1; declare -p tempvar1`,
		`declare -rx tempvar1="foo"` + "\n",
	},
	{
		`v=base; f(){ local v=fl; g; echo f:$v; }; g(){ v=temp declare -x v; echo g:$v; }; f; echo out:$v`,
		"g:temp\nf:fl\nout:base\n",
	},
	{
		`v=base; f(){ local v=fl; g; echo f:$v; }; g(){ v=temp export v; echo g:$v; }; f; echo out:$v`,
		"g:temp\nf:temp\nout:base\n",
	},
	{
		`v=base; f(){ local v=fl; g; echo f:$v; }; g(){ v=temp true; echo g:$v; }; f; echo out:$v`,
		"g:fl\nf:fl\nout:base\n",
	},
	{
		`ref=xxx typeset -p ref; echo ${ref-unset}`,
		`declare -x ref="xxx"` + "\nunset\n",
	},
	{
		`foo=bar :; echo colon:${foo-unset}`,
		"colon:unset\n",
	},

	// A new local starts unset rather than inheriting the outer
	// variable (#381): only the export attribute carries over, a
	// readonly outer refuses the declaration, and a second `local` in
	// the same scope keeps what the first one holds. `typeset` is
	// declare's synonym and localizes with it (#382).
	{
		`V=abc; f(){ local V; echo "${V-unset}"; }; f`,
		"unset\n",
	},
	{
		`V=abc; f(){ declare V; echo "${V-unset}"; declare -p V; }; f`,
		"unset\ndeclare -- V\n",
	},
	{
		`f() { typeset v=inner; :; }; v=outer; f; echo "v=$v"`,
		"v=outer\n",
	},
	{
		`V=abc; f(){ typeset V; echo "${V-unset}"; }; f; echo $V`,
		"unset\nabc\n",
	},
	{
		// A leaked `typeset IFS=:` poisons every later expansion in
		// the file, which is how ifs.tests found this.
		`f(){ typeset IFS=:; }; f; x="a b"; set -- $x; echo $#`,
		"2\n",
	},
	{
		`f(){ local V=1; local V; echo "${V-unset}"; }; f`,
		"1\n",
	},
	{
		`V=out; f(){ local V=fl; g; }; g(){ local V; echo "${V-unset}"; }; f`,
		"unset\n",
	},
	{
		`declare -x V=abc; f(){ local V; declare -p V; }; f`,
		"declare -x V\n",
	},
	{
		`declare -i V=5; f(){ local V; declare -p V; V=2+2; declare -p V; }; f`,
		"declare -- V\n" + `declare -- V="2+2"` + "\n",
	},
	{
		`declare -a V=(1); f(){ local V; declare -p V; }; f`,
		"declare -- V\n",
	},
	{
		`declare -r V=5; f(){ local V W=ok; declare -p W; }; f`,
		"local: V: readonly variable\n" + `declare -- W="ok"` + "\n #JUSTERR",
	},
	{
		`shopt -s localvar_inherit; V=abc; f(){ local V; echo "${V-unset}"; }; f`,
		"abc\n",
	},
	{
		`shopt -s localvar_inherit; declare -x V=abc; f(){ local -x V; declare -p V; }; f`,
		`declare -x V="abc"` + "\n",
	},

	// declare -g writes the global scope through any local shadowing
	// the name (#379); reads stay dynamically scoped, so both
	// functions still see the local.
	{
		`f(){ local v; g; echo f:$v; }; g(){ declare -g v=two; echo g:$v; }; f; echo FIN:$v`,
		"g:\nf:\nFIN:two\n",
	},
	{
		`f(){ local v=one; declare -g v=two; echo in:$v; }; f; echo out:$v`,
		"in:one\nout:two\n",
	},
	{
		`v=g0; f(){ local v=one; g; }; g(){ declare -g v; v=three; }; f; echo $v`,
		"g0\n",
	},
	{
		`f(){ declare -ga arr=(1 2); }; f; declare -p arr`,
		`declare -a arr=([0]="1" [1]="2")` + "\n",
	},
	// The string form of a compound assignment (#379): parsed as an
	// array literal — its elements expanded — only under an explicit
	// -a/-A or an existing array; the bare form stays a literal
	// string (bash 5.1), and so does an unbalanced "(".
	{
		`aux=v; declare -ga "$aux=( a b )"; declare -p v`,
		`declare -a v=([0]="a" [1]="b")` + "\n",
	},
	{
		`aux="v=( a b )"; declare "$aux"; declare -p v`,
		`declare -- v="( a b )"` + "\n",
	},
	{
		`v=(1); declare "v=( new )"; declare -p v`,
		`declare -a v=([0]="new")` + "\n",
	},
	{
		`x="\$y"; y=z; declare -a v="( $x )"; declare -p v`,
		`declare -a v=([0]="z")` + "\n",
	},
	{
		`aux="( a b )"; declare -a v=$aux; declare -p v`,
		`declare -a v=([0]="a" [1]="b")` + "\n",
	},
	{
		`aux="( a b )"; declare -a v=("$aux"); declare -p v`,
		`declare -a v=([0]="( a b )")` + "\n",
	},
	{
		`declare -a "w=( a b"; echo rc=$?; declare -p w`,
		"rc=0\n" + `declare -a w=([0]="( a b")` + "\n",
	},
	{
		`declare -a "w=()"; declare -p w`,
		"declare -a w=()\n",
	},

	// test -v on arrays (#378): a bare array name tests element 0, a
	// subscript tests that element (@/* meaning any, except that they
	// are ordinary keys for an associative array), and a scalar is
	// element 0 of itself.
	{
		`typeset -A A; A[a]=1; [ -v A ] && echo set || echo unset`,
		"unset\n",
	},
	{
		`a[1]=1; [ -v a ] || echo unset; [ -v "a[1]" ] && echo e1; [ -v "a[@]" ] && echo any`,
		"unset\ne1\nany\n",
	},
	{
		`s=x; [ -v "s[0]" ] && echo s0; [ -v "s[@]" ] && echo sat; [ -v "s[1]" ] || echo no1`,
		"s0\nsat\nno1\n",
	},
	{
		`declare -A B; B[k]=v; [ -v "B[@]" ] || echo nokey; B[@]=x; [ -v "B[@]" ] && echo litkey`,
		"nokey\nlitkey\n",
	},
	{
		`a=(x y); [ -v "a[-1]" ] && echo neg`,
		"neg\n",
	},
	{
		`a=(x y); [ -v "a[-5]" ]`,
		"a: bad array subscript\nexit status 1 #JUSTERR",
	},
	// A subscript is read when the assignment *runs*, not while parsing
	// (#582), so these are runtime verdicts naming the subscript as it
	// was written — and each one abandons the rest of the input unit,
	// which is why nothing after them appears.
	{"b=(x); b[]=1", "b[]: bad array subscript\nexit status 1 #JUSTERR"},
	{"b=(x); b[  ]=9; echo \"${b[0]}\"", "9\n"},
	{"b=(x y); b[*]=1", "b[*]: bad array subscript\nexit status 1 #JUSTERR"},
	{"b=(x y); b[@]=1", "b[@]: bad array subscript\nexit status 1 #JUSTERR"},
	{"b=(x y); b[-9]=1", "b[-9]: bad array subscript\nexit status 1 #JUSTERR"},
	{"d[7]=(a b)", "d[7]: cannot assign list to array member\nexit status 1 #JUSTERR"},
	{"declare -A m; m[k]=(a b)", "m[k]: cannot assign list to array member\nexit status 1 #JUSTERR"},
	// An element's subscript is the same rule, and the diagnostic names
	// the element rather than the variable, which is what tells a reader
	// which element of many was wrong.
	{"d=([]=y)", "[]=y: bad array subscript\nexit status 1 #JUSTERR"},
	{"d=([*]=q)", "[*]=q: cannot assign to non-numeric index\nexit status 1 #JUSTERR"},
	{"d=([-1]=z)", "[-1]=z: bad array subscript\nexit status 1 #JUSTERR"},
	{"d=([1]=ok [2]=fine); declare -p d", "declare -a d=([1]=\"ok\" [2]=\"fine\")\n"},
	// Making that shape legal means the *tree* keeps the element it read
	// and every reader survives it (#673). An empty subscript has no
	// index node, so a printer asking only `Index != nil` dropped it and
	// `a[]=v` came back as `a=v` -- a working assignment where the
	// original is an error -- while an element with no value either
	// panicked `ArrayElem.Pos`. `eval "$(declare -f f)"` is how a
	// function moves between shells, so a definition printed back
	// differently is a different function.
	{
		"f() { A=([]=); }; declare -f f",
		"f () \n{ \n    A=([]=)\n}\n",
	},
	{
		"f() { A=([]=y [1]=z); }; declare -f f",
		"f () \n{ \n    A=([]=y [1]=z)\n}\n",
	},
	{
		"f() { A=([]+=y); }; declare -f f",
		"f () \n{ \n    A=([]+=y)\n}\n",
	},
	{
		"f() { A+=([]=); }; declare -f f",
		"f () \n{ \n    A+=([]=)\n}\n",
	},
	{
		"f() { a[]=v; }; declare -f f",
		"f () \n{ \n    a[]=v\n}\n",
	},
	{
		"f() { a[]=; }; declare -f f",
		"f () \n{ \n    a[]=\n}\n",
	},
	{
		"f() { a[]+=v; }; declare -f f",
		"f () \n{ \n    a[]+=v\n}\n",
	},
	// `[  ]` is a different subscript -- whitespace is an empty
	// arithmetic expression, so it is index 0 (#582) -- and it must not
	// be printed back as the empty one.
	{
		"f() { A=([ ]=); }; declare -f f",
		"f () \n{ \n    A=([ ]=)\n}\n",
	},
	// A `[` inside a compound assignment opens a subscript only when the
	// shape completes (#588): `[1]=14` does, a lone bracket does not, and
	// bash reads the rest as ordinary words. koi used to refuse the line
	// and — parsing ahead — the rest of the file.
	{
		"array=(42 [1]=14 [2]=44); declare -p array",
		"declare -a array=([0]=\"42\" [1]=\"14\" [2]=\"44\")\n",
	},
	{`array2=(grep [ 123 ] \*); echo "${array2[@]}"`, "grep [ 123 ] *\n"},
	{"a=(foo[0-9] bar); declare -p a", "declare -a a=([0]=\"foo[0-9]\" [1]=\"bar\")\n"},
	{`a=("[1]=q"); declare -p a`, "declare -a a=([0]=\"[1]=q\")\n"},
	{"a=([i]); declare -p a", "declare -a a=([0]=\"[i]\")\n"},
	// A leading `=` inside a compound assignment is an operator only
	// where an `[idx]` shape just closed; anywhere else it is an
	// ordinary word character (#707). koi lexed every word-initial `=`
	// as the assignment operator, so a word beginning with one was a
	// syntax error — `x=( [] =c )` is two words to bash, and the
	// divergence needed a bracketed span, whitespace after the `]`, and
	// a next word starting with `=`.
	{`x=( [] =c ); declare -p x`, "declare -a x=([0]=\"[]\" [1]=\"=c\")\n"},
	{`x=( []	=c ); declare -p x`, "declare -a x=([0]=\"[]\" [1]=\"=c\")\n"},
	{`x=( [] = ); declare -p x`, "declare -a x=([0]=\"[]\" [1]=\"=\")\n"},
	{
		// The same word after an *explicit* index, which also shows the
		// implicit index carrying on from it.
		`x=( [0]=a [1] =b ); declare -p x`,
		"declare -a x=([0]=\"a\" [1]=\"[1]\" [2]=\"=b\")\n",
	},
	{
		// bash's own array.tests shape, with the `+=` spelling (#605)
		// in front of it.
		`x=(a); x=( [0]+=b [] =c ); declare -p x`,
		"declare -a x=([0]=\"b\" [1]=\"[]\" [2]=\"=c\")\n",
	},
	{`x=( [] +=c ); declare -p x`, "declare -a x=([0]=\"[]\" [1]=\"+=c\")\n"},
	// The bug was wider than the bracket: a word beginning with `=` was
	// refused with no bracket in sight.
	{`x=(=c); declare -p x`, "declare -a x=([0]=\"=c\")\n"},
	{`x=( =c ); declare -p x`, "declare -a x=([0]=\"=c\")\n"},
	// And the operator still is one where the shape did complete, so
	// this is not "every `=` is a word now".
	{`x=( [0]=a ); declare -p x`, "declare -a x=([0]=\"a\")\n"},
	{`x=( [0]+=b ); declare -p x`, "declare -a x=([0]=\"b\")\n"},
	{`x=( [2]=a b c ); declare -p x`, "declare -a x=([2]=\"a\" [3]=\"b\" [4]=\"c\")\n"},
	// A subscript is text bash cannot classify while reading it: whether
	// `hello world` is an arithmetic expression or an associative key
	// depends on the array, which only running knows (#564). Every one of
	// these was a parse error, so it cost the rest of the file.
	{`declare -A m; m[hello world]=1; declare -p m`, "declare -A m=([\"hello world\"]=\"1\" )\n"},
	{`declare -A m=([a b]=1); declare -p m`, "declare -A m=([\"a b\"]=\"1\" )\n"},
	{`declare -A m; m[%]=x; echo "${m[%]}"`, "x\n"},
	{`declare -A m; m[a b]=1; echo "[${m[a b]}] [${m[a  b]-none}]"`, "[1] [none]\n"},
	// Quotes come off and every metacharacter stays: the text is read to
	// its bracket, so nothing inside it is a separator, an operator, or
	// the end of the construct the subscript sits in.
	{
		`declare -A m; m['a b']=1; m[c\ d]=2; m[e "f"]=3; echo "${m[a b]}${m[c d]}${m[e f]}"`,
		"123\n",
	},
	{
		`declare -A m; m[a;b]=1; m[a{b]=2; m[a}b]=3; m[a(b]=4; echo "${m[a;b]}${m[a{b]}${m[a}b]}${m[a(b]}"`,
		"1234\n",
	},
	{`declare -A m; m[a)b]=Q; echo "[${m[a)b]}]"`, "[Q]\n"},
	// Expansions inside a subscript still run — including one whose own
	// output holds the bracket the scan is looking for.
	{`declare -A m; k='a b'; m[$k]=1; echo "${m[a b]}"`, "1\n"},
	{`declare -A m; m[$(echo "a]b")]=1; echo "${m['a]b']}"`, "1\n"},
	{`declare -A m; m[a b]=7; echo $((m[a b]))`, "7\n"},
	{`declare -A m; m[a b]=v; echo "${m[a b]-alt} ${#m[a b]} ${m[a b]:0:1}"`, "v 1 v\n"},
	{
		`declare -A m; m[a b]=1; echo "${!m[@]}"; unset "m[a b]"; declare -p m`,
		"a b\ndeclare -A m=()\n",
	},
	{`a=(1 2 3); echo "${a[1 ]} ${a[ 1]} ${a[1+1]}"`, "2 2 3\n"},
	// The array decides what the text means, and the sharpest case is a
	// key that *also* reads as arithmetic: `a-b` is a subtraction, `-1` a
	// count from the end, `(1)` a parenthesized one and `x[1]` another
	// array's element — and every one of them is an ordinary key here
	// (#626). Reading them as arithmetic while parsing dropped the write
	// without a word and crashed the read on an interface conversion.
	{"declare -A m; m[a-b]=1; declare -p m", "declare -A m=([a-b]=\"1\" )\n"},
	{"declare -A m; m[-1]=v; declare -p m", "declare -A m=([-1]=\"v\" )\n"},
	{"declare -A m; m[+1]=v; declare -p m", "declare -A m=([+1]=\"v\" )\n"},
	{"declare -A m; m[1+2]=v; declare -p m", "declare -A m=([1+2]=\"v\" )\n"},
	{"declare -A m; m[(1)]=w; declare -p m", "declare -A m=([\"(1)\"]=\"w\" )\n"},
	{"declare -A m; m[!z]=q; declare -p m", "declare -A m=([\"!z\"]=\"q\" )\n"},
	{"declare -A m; m[a|b]=x; declare -p m", "declare -A m=([\"a|b\"]=\"x\" )\n"},
	// The nested bracket is the one that stored under the *empty* key, so
	// the stored key is read back independently of the read path.
	{
		`declare -A m; m[x[1]]=q; declare -p m; echo "${!m[@]}"`,
		"declare -A m=([\"x[1]\"]=\"q\" )\nx[1]\n",
	},
	{`declare -A m; echo "[${m[a-b]}]"`, "[]\n"},
	{`declare -A m; echo "[${m[-1]}]"`, "[]\n"},
	{`declare -A m; echo "[${m[a-b]=v}]"; declare -p m`, "[v]\ndeclare -A m=([a-b]=\"v\" )\n"},
	{`declare -A m; echo "[${m[a-b]:-default}]"`, "[default]\n"},
	{`declare -A m; echo "${#m[a-b]}"`, "0\n"},
	{`declare -A m; m[a-b]=hello; echo "${#m[a-b]}"`, "5\n"},
	{`declare -A m; m[a-b]=1; m[a-b]=2; echo "${m[a-b]}"`, "2\n"},
	{`declare -A m; m[a-b]=1; unset "m[a-b]"; declare -p m`, "declare -A m=()\n"},
	{`declare -A m; m[x[1]]=1; unset "m[x[1]]"; declare -p m`, "declare -A m=()\n"},
	{`declare -A m; m[a-b]=1; [[ -v m[a-b] ]]; echo "v=$?"`, "v=0\n"},
	// A compound assignment's keys are the same text, read back one at a
	// time rather than through `declare -p`, whose order is bash's hash.
	{
		`declare -A m=([a-b]=1 [-1]=2 [x[1]]=3); echo "[${m[a-b]}][${m[-1]}][${m[x[1]]}]"`,
		"[1][2][3]\n",
	},
	// The key is the expansion's *result*, so it cannot be the raw source.
	{`a=X; b=Y; declare -A m; m[$a-$b]=1; declare -p m`, "declare -A m=([X-Y]=\"1\" )\n"},
	// An indirection and a nameref reach a subscript from a *string*, and
	// each one has to read it the way the parser reads one in place.
	{`declare -A m; m[a-b]=1; n=m[a-b]; echo "[${!n}]"`, "[1]\n"},
	{`declare -n r=m[a-b]; declare -A m; r=1; declare -p m`, "declare -A m=([a-b]=\"1\" )\n"},
	// The same characters in an *indexed* array's subscript are the
	// arithmetic they look like, which is the whole point of not deciding
	// while reading: a-b is index 0, -1 is the last element, x[1] reads
	// another array, 0x10 is sixteen.
	{"declare -a a=(z0 z1 z2 z3); a[-1]=V; declare -p a", "declare -a a=([0]=\"z0\" [1]=\"z1\" [2]=\"z2\" [3]=\"V\")\n"},
	{"declare -a a=(z0 z1 z2 z3); a[a-b]=V; declare -p a", "declare -a a=([0]=\"V\" [1]=\"z1\" [2]=\"z2\" [3]=\"z3\")\n"},
	{"declare -a a=(z0 z1 z2 z3); a[x[1]]=V; declare -p a", "declare -a a=([0]=\"V\" [1]=\"z1\" [2]=\"z2\" [3]=\"z3\")\n"},
	{"declare -a a=(z0 z1 z2 z3); a[0x10]=V; declare -p a", "declare -a a=([0]=\"z0\" [1]=\"z1\" [2]=\"z2\" [3]=\"z3\" [16]=\"V\")\n"},
	{`declare -a a=(z0 z1 z2 z3); a[1+2]=V; echo "${a[1+2]}"`, "V\n"},
	// Spacing is part of a key and is trimmed by the arithmetic reader,
	// so ` k ` and `k` are two keys while ` 1 ` and `1` are one index.
	{"declare -A m; m[ a - b ]=V; declare -p m", "declare -A m=([\" a - b \"]=\"V\" )\n"},
	{`declare -A m; m[ k ]=1; echo "[${m[ k ]}][${m[k]}]"`, "[1][]\n"},
	{`a=(x y z); echo "[${a[ 1 ]}]"`, "[y]\n"},
	// And ` @ ` is not the every-element subscript: bash reads the spaced
	// form arithmetically and refuses it, where trimming made it `@`.
	{`a=(x y z); echo "[${a[ @ ]}]"; echo after`, "@: arithmetic syntax error\nexit status 1 #JUSTERR"},
	// `declare -p` leaves a key bare or quotes it per character, measured:
	// `+ , : = @ %` are plain wherever they fall, `#` and `~` are plain
	// only away from the head, where one starts a comment and the other a
	// tilde expansion — which only matters now that a key spelled like
	// arithmetic can exist at all (#626).
	{"declare -A m; m[a#b]=v; declare -p m", "declare -A m=([a#b]=\"v\" )\n"},
	{`declare -A m; m['#x']=v; declare -p m`, "declare -A m=([\"#x\"]=\"v\" )\n"},
	{`declare -A m; m['~x']=v; declare -p m`, "declare -A m=([\"~x\"]=\"v\" )\n"},
	{"declare -A m; m[a:b=c]=v; declare -p m", "declare -A m=([a:b=c]=\"v\" )\n"},
	{"declare -A m; m[a^b]=v; declare -p m", "declare -A m=([\"a^b\"]=\"v\" )\n"},
	// An *indexed* array reads the same text arithmetically and reports it
	// while running, which abandons the rest of the line — where the parse
	// error used to cost the rest of the file. bash names the token it
	// stopped at too, which koi does not yet (#598).
	{
		`declare -a a; a[hello world]=1; echo after`,
		"hello world: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{`declare -a a; a[%]=10; echo after`, "%: arithmetic syntax error\nexit status 1 #JUSTERR"},
	{`echo "[${foo[1 2]}]"; echo after`, "1 2: arithmetic syntax error\nexit status 1 #JUSTERR"},
	{
		`declare -a foo=(x y); echo "[${#foo[1 2]}]"; echo after`,
		"1 2: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	// The one exception, measured: `${#name[…]}` on a name that does not
	// exist answers 0 without ever reading the subscript, while
	// `${name[…]}` on the same missing name reports the error.
	{`unset foo; echo "[${#foo[1 2]}]"; echo after`, "[0]\nafter\n"},
	// `name[i]+=v` appends to that element. It stored *nothing* — no
	// diagnostic, status 0, the element left empty rather than left
	// alone — because the append was computed against element 0 while
	// the element path wrote the value the append had not produced
	// (#625). Indexed and associative alike, and creating the element
	// from the empty string when it was not there.
	{`a=(x); a[0]+=y; declare -p a`, "declare -a a=([0]=\"xy\")\n"},
	{`unset a; a[3]+=v; declare -p a`, "declare -a a=([3]=\"v\")\n"},
	{`a=(1 2 3); a[5]+=Z; declare -p a`, "declare -a a=([0]=\"1\" [1]=\"2\" [2]=\"3\" [5]=\"Z\")\n"},
	{`declare -A m; m[k]=1; m[k]+=2; echo "${m[k]}"`, "12\n"},
	{`declare -A m; m[k]+=2; echo "${m[k]}"`, "2\n"},
	// A negative index counts from one past the maximum, so the append
	// lands on the last element rather than creating one.
	{`a=(1 2 3); a[-1]+=Z; declare -p a`, "declare -a a=([0]=\"1\" [1]=\"2\" [2]=\"3Z\")\n"},
	// The subscript is evaluated once, measured: `a[i++]+=Z` leaves i at
	// 1 and appends to element 0. Reading the old value where the value
	// is built would have evaluated it twice and advanced i to 2.
	{
		`i=0; a=(p q r); a[i++]+=Z; declare -p a; echo "i=$i"`,
		"declare -a a=([0]=\"pZ\" [1]=\"q\" [2]=\"r\")\ni=1\n",
	},
	// Under the integer attribute the join is arithmetic rather than
	// concatenation, exactly as it is for a scalar `n+=x` — and an unset
	// element, or one whose value will not read as a number, is zero.
	{`declare -i a; a[0]+=5; a[0]+=5; declare -p a`, "declare -ai a=([0]=\"10\")\n"},
	{`declare -Ai m; m[k]=3; m[k]+=4; echo "${m[k]}"`, "7\n"},
	// `declare` reaches the same element path, so it appends too.
	{`a=(x); declare a[0]+=y; declare -p a`, "declare -a a=([0]=\"xy\")\n"},
	{`declare -A m=([k]=1); declare m[k]+=2; echo "${m[k]}"`, "12\n"},
	// `[i]+=v` inside a compound assignment was a *parse* error, so it
	// cost the rest of the file for a line bash reads (#605). What it
	// appends to depends on the enclosing assignment: a plain `x=(…)`
	// clears first, so `[2]+=7` starts from nothing, while `x+=(…)`
	// keeps the base and appends to what is there.
	{
		`x=( 1 2 [2]+=7 4 5 ); declare -p x`,
		"declare -a x=([0]=\"1\" [1]=\"2\" [2]=\"7\" [3]=\"4\" [4]=\"5\")\n",
	},
	{`x=(1 2 3); x=( [2]+=7 ); declare -p x`, "declare -a x=([2]=\"7\")\n"},
	{
		`x=(1 2 3); x+=( [2]+=7 ); declare -p x`,
		"declare -a x=([0]=\"1\" [1]=\"2\" [2]=\"37\")\n",
	},
	// An explicit subscript still resets the index counter, so the
	// elements after the append carry on from one past it.
	{
		`x=( 1 2 [2]+=7 4 5 [1]+=Q ); declare -p x`,
		"declare -a x=([0]=\"1\" [1]=\"2Q\" [2]=\"7\" [3]=\"4\" [4]=\"5\")\n",
	},
	// An *indexed* compound assignment appends to the list it is
	// building, so appends accumulate within one assignment.
	{`x=([0]=1 [0]+=2 [0]+=3); declare -p x`, "declare -a x=([0]=\"123\")\n"},
	{
		`x=( a b ); x+=( [0]+=Z [0]+=Y ); declare -p x`,
		"declare -a x=([0]=\"aZY\" [1]=\"b\")\n",
	},
	{`declare -i n=(); n=( [0]+=5 [0]+=5 ); declare -p n`, "declare -ai n=([0]=\"10\")\n"},
	{`declare -i n=(); n=([0]+=5 [0]+=x); declare -p n`, "declare -ai n=([0]=\"5\")\n"},
	// An *associative* one does not, and the difference is bash's
	// implementation showing through: `m=(…)` builds a fresh table while
	// its appends still read the old one, so each element sees the value
	// from before the assignment began — `m=([a]=1); m=([a]+=2 [a]+=3)`
	// answers `13`, not `123`. `m+=(…)` works in the table itself and
	// does accumulate. Both measured against bash 5.3.
	{`declare -A m=([k]=1 [k]+=2); echo "${m[k]}"`, "2\n"},
	{`declare -A m; m=([a]=1); m=([a]+=2 [a]+=3); echo "${m[a]}"`, "13\n"},
	{`declare -A m=([a]=x); m+=([a]+=Z [a]+=Y); echo "${m[a]}"`, "xZY\n"},
	{`declare -Ai m=([k]=2); m+=([k]+=5 [k]+=5); echo "${m[k]}"`, "12\n"},
	// In the key/value-pairing mode a bracketed element is read back as
	// the literal word it was written as, `+=` and all.
	{`declare -A m=(a b [k]+=v); echo "[${m[a]}][${m['[k]+=v']}]"`, "[b][]\n"},
	// `+=` with nothing after it appends nothing, which still creates the
	// element — and the shapes the lexer's forward scan does *not* count
	// as a subscript stay the ordinary words bash reads them as (#588).
	{`x=( [2]+= ); declare -p x`, "declare -a x=([2]=\"\")\n"},
	{`x=( [2]+ ); declare -p x`, "declare -a x=([0]=\"[2]+\")\n"},
	{`x=( [2] +=7 ); declare -p x`, "declare -a x=([0]=\"[2]\" [1]=\"+=7\")\n"},
	// `declare -f` has to print the `+` back, for the reason #631 gives:
	// `eval "$(declare -f f)"` is how a function moves between shells, so
	// dropping it would hand over a function that assigns where the
	// original appended, with nothing saying so.
	{
		`f() { x=( 1 [2]+=7 ); x[0]+=Q; }; declare -f f`,
		"f () \n{ \n    x=(1 [2]+=7);\n    x[0]+=Q\n}\n",
	},
	{
		`f() { x=( 1 [2]+=7 ); }; eval "$(declare -f f)"; f; declare -p x`,
		"declare -a x=([0]=\"1\" [2]=\"7\")\n",
	},
	// Re-parsing a *string* as arithmetic took a partial read for a whole
	// one everywhere it happens, so text bash refuses evaluated to zero:
	// a name read arithmetically, and a `[[ ]]` operand.
	{
		`y="hello world"; echo $((y)); echo after`,
		"hello world: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{`x="1 2"; [[ $x -eq 1 ]]; echo "r=$?"`, "[[: 1 2: arithmetic syntax error\nr=1\n #JUSTERR"},
	// A loop variable can be a word, and bash refuses it when the loop
	// *runs* — naming the text as written, since it never expands it
	// (#593). The rest of the line still runs, so these are ordinary
	// errors rather than #469's abandonment.
	{
		`for $1 in a; do :; done; echo "after=$?"`,
		"`$1': not a valid identifier\nafter=1\n #JUSTERR",
	},
	{
		`for x$1 in a; do :; done; echo "after=$?"`,
		"`x$1': not a valid identifier\nafter=1\n #JUSTERR",
	},
	{
		`for "x" in a; do echo "q=$x"; done; echo "after=$?"`,
		"`\"x\"': not a valid identifier\nafter=1\n #JUSTERR",
	},
	{
		`select $1 in a; do :; done; echo "after=$?"`,
		"`$1': not a valid identifier\nafter=1\n #JUSTERR",
	},
	// Reported when the function is *called*, not when it is defined:
	// the definition succeeds, so a caller only finds out by running it.
	{
		`f() { for $1 in a; do :; done; }; f; echo "called=$?"`,
		"`$1': not a valid identifier\ncalled=1\n #JUSTERR",
	},
	{"for x in a b; do echo \"ok=$x\"; done", "ok=a\nok=b\n"},
	// A bare `let` is its builtin's own complaint rather than a syntax
	// error, so it parses and answers 1 with the line carrying on.
	{`let; echo "after=$?"`, "let: expression expected\nafter=1\n #JUSTERR"},
	{`x=$(let); echo "[$x] st=$?"`, "let: expression expected\n[] st=1\n #JUSTERR"},
	{`let 1+1; echo "st=$?"`, "st=0\n"},
	// `declare` answers 1 and carries on to the next name rather than
	// abandoning the line, which is the split #308 measured for a
	// readonly variable.
	{`declare a[]=x c=2; echo "c=[$c]"`, "a[]: bad array subscript\nc=[2]\n #JUSTERR"},

	// declare -p output has to re-read as the value it printed (#383):
	// a control character forces ANSI-C quoting, and the characters
	// that would still expand inside double quotes are escaped.
	{
		`v=$'a\nb'; declare -p v`,
		`declare -- v=$'a\nb'` + "\n",
	},
	{
		`export FOO='$$'; declare -p FOO`,
		`declare -x FOO="\$\$"` + "\n",
	},
	{
		`v='` + "`c`" + `'; declare -p v`,
		`declare -- v="\` + "`c\\`" + `"` + "\n",
	},
	{
		`v=$'\t\\'; declare -p v`,
		`declare -- v=$'\t\\'` + "\n",
	},
	{
		`v="it's"; declare -p v`,
		`declare -- v="it's"` + "\n",
	},
	{
		`a=(x $'p\nq'); declare -p a`,
		`declare -a a=([0]="x" [1]=$'p\nq')` + "\n",
	},
	{
		`declare -A m=([k$]=$'v\n'); declare -p m`,
		`declare -A m=(["k\$"]=$'v\n' )` + "\n",
	},
	// An attribute flag with no operands lists the variables carrying
	// it (#384); bare declare prints POSIX name=value pairs instead.
	{
		`declare -A f; f[a]=1; declare -A | grep '^declare -A f'`,
		`declare -A f=([a]="1" )` + "\n",
	},
	{
		`declare -i n=1; declare -i | grep ' n='`,
		`declare -i n="1"` + "\n",
	},
	{
		`zz=1; declare | grep '^zz'`,
		"zz=1\n",
	},
	{
		`zz=1; declare -- | grep '^zz'`,
		"zz=1\n",
	},
	{
		`zz=1; declare -p | grep ' zz='`,
		`declare -- zz="1"` + "\n",
	},
	{
		`declare -- v=1; declare -p v`,
		`declare -- v="1"` + "\n",
	},

	// declare's remaining option surface (#385): -u/-l/-c transform on
	// every assignment, two of them cancel rather than stack, +x/+r/+t
	// remove attributes (readonly refusing to be removed), -I inherits
	// the enclosing scope, and `local -` restores the shell options
	// when the function returns.
	{
		`declare -u u; u=abc; echo $u; declare -p u`,
		"ABC\n" + `declare -u u="ABC"` + "\n",
	},
	{
		`declare -l l=ABC; echo $l; declare -p l`,
		"abc\n" + `declare -l l="abc"` + "\n",
	},
	{
		`declare -c c=hello_world; echo $c; declare -c d="hello world"; echo $d`,
		"Hello_world\nHello world\n",
	},
	{
		`declare -u a=(x y); declare -p a`,
		`declare -au a=([0]="X" [1]="Y")` + "\n",
	},
	{
		`declare -A m; declare -u m; m[k]=vv; declare -p m`,
		`declare -Au m=([k]="VV" )` + "\n",
	},
	{
		`declare -u u=abc; u+=def; echo $u`,
		"ABCDEF\n",
	},
	{
		`declare -u u; u=abc; declare +u u; echo $u; u=xyz; echo $u`,
		"ABC\nxyz\n",
	},
	{
		`declare -ul x=ABC; declare -p x`,
		`declare -- x="ABC"` + "\n",
	},
	{
		`declare -u u=a; declare -l u; declare -p u; u=QQ; echo $u`,
		`declare -l u="A"` + "\nqq\n",
	},
	{
		`export V=1; declare +x V; declare -p V`,
		`declare -- V="1"` + "\n",
	},
	{
		`readonly V=1; declare +r V; declare -p V`,
		"declare: V: readonly variable\n" + `declare -r V="1"` + "\n #JUSTERR",
	},
	{
		`declare -tux w=v; declare -p w`,
		`declare -txu w="V"` + "\n",
	},
	{
		`declare -irtx z=5; declare -p z`,
		`declare -irtx z="5"` + "\n",
	},
	{
		`V=out; f(){ local V=in; g; }; g(){ local -I V; echo "${V-unset}"; }; f`,
		"in\n",
	},
	{
		`unset Z; f(){ local -I Z; echo "${Z-unset}"; }; f`,
		"unset\n",
	},
	{
		`set -e; f(){ local -; set +e; case $- in *e*) echo in-e;; *) echo in-noe;; esac; }; f; case $- in *e*) echo out-e;; esac`,
		"in-noe\nout-e\n",
	},
	{
		`f(){ local -; set -u; case $- in *u*) echo in-u;; esac; }; f; case $- in *u*) echo out-u;; *) echo no-u;; esac`,
		"in-u\nno-u\n",
	},

	// export -f marks a function for export rather than printing it
	// (#387), and an -x listing is filtered to the exported ones
	// (#388) where koi listed every function it had.
	{
		`a(){ :; }; b(){ :; }; export -f a; declare -xF; echo end`,
		"declare -fx a\nend\n",
	},
	{
		`a(){ :; }; b(){ :; }; declare -xF; echo end`,
		"end\n",
	},
	{
		`f(){ :; }; export -f f; export -nf f; declare -xF; echo end`,
		"end\n",
	},
	{
		`f(){ echo body; }; declare -xf f; echo ---; declare -xF`,
		"---\ndeclare -fx f\n",
	},
	{
		`export -f nope`,
		"export: nope: not a function\nexit status 1 #JUSTERR",
	},
	{
		// A function name is not a variable name, so a dashed name
		// exports rather than being refused.
		`foo-bar(){ :; }; export -f foo-bar; echo rc=$?`,
		"rc=0\n",
	},
	{
		// `export -n` removes the export attribute; it is a nameref
		// only for declare/local/typeset.
		`V=1; export V; export -n V; declare -p V`,
		`declare -- V="1"` + "\n",
	},

	// The canonical function printer (#386): bash re-renders the parse
	// tree in one fixed shape rather than echoing source text, `type`
	// prints the definition under its verdict, and -p alongside -f is a
	// modifier rather than a replacement.
	{
		`f(){ echo hi; }; type f`,
		"f is a function\nf () \n{ \n    echo hi\n}\n",
	},
	{
		`f(){ echo hi; }; declare -f -p f; echo rc=$?`,
		"f () \n{ \n    echo hi\n}\nrc=0\n",
	},
	{
		`f(){ if [ 1 ]; then echo a; else echo b; fi; }; declare -f f`,
		"f () \n{ \n    if [ 1 ]; then\n        echo a;\n    else\n        echo b;\n    fi\n}\n",
	},
	{
		`f(){ for i in 1 2; do echo $i; done; }; declare -f f`,
		"f () \n{ \n    for i in 1 2;\n    do\n        echo $i;\n    done\n}\n",
	},
	{
		`f(){ while :; do break; done; }; declare -f f`,
		"f () \n{ \n    while :; do\n        break;\n    done\n}\n",
	},
	{
		`f(){ case $x in a) :;; *) :;; esac; }; declare -f f`,
		"f () \n{ \n    case $x in \n        a)\n            :\n        ;;\n        *)\n            :\n        ;;\n    esac\n}\n",
	},
	{
		// elif renders as a nested else-if, and a duplicating
		// redirection grows its default descriptor.
		`f(){ if a; then b; elif c; then d; else e; fi; echo x >&2; }; declare -f f`,
		"f () \n{ \n    if a; then\n        b;\n    else\n        if c; then\n            d;\n        else\n            e;\n        fi;\n    fi;\n    echo x 1>&2\n}\n",
	},
	{
		// A nested declaration gains bash's `function` keyword.
		`f(){ g(){ echo inner; }; g; }; declare -f f`,
		"f () \n{ \n    function g () \n    { \n        echo inner\n    };\n    g\n}\n",
	},
	{
		`f(){ a=(1 2); x=$((1+2)); echo "${a[@]}$x"; }; declare -f f`,
		"f () \n{ \n    a=(1 2);\n    x=$((1+2));\n    echo \"${a[@]}$x\"\n}\n",
	},

	// An omitted C-style loop part prints as the expression it means
	// (#671). bash does not print the absence back: 1 makes a missing
	// condition true and a missing init or post a harmless no-op, so the
	// listing runs as the loop it came from. koi printed nothing, and
	// `for ((;;))` came back as `for ((; ; ))` — not even the text that
	// went in.
	{
		`f(){ for ((;;)); do break; done; }; declare -f f`,
		"f () \n{ \n    for ((1; 1; 1))\n    do\n        break;\n    done\n}\n",
	},
	{
		`f(){ for ((i=0; i<3;)); do break; done; }; declare -f f`,
		"f () \n{ \n    for ((i=0; i<3; 1))\n    do\n        break;\n    done\n}\n",
	},
	{
		// The rule is the loop header's alone, measured rather than
		// generalized: an empty `(( ))` at command position stays empty.
		`f(){ (()); }; declare -f f`,
		"f () \n{ \n    (())\n}\n",
	},
	{
		// And the round trip, which is why this is worse than cosmetic:
		// the listing has to run as the loop it was printed from.
		`f(){ i=0; for ((;;)); do echo $i; ((i++)); ((i>1)) && break; done; }; eval "$(declare -f f)"; f`,
		"0\n1\n",
	},

	// `time` prefixes a command and that command still gets the
	// canonical layout (#671, #631's shape again): a construct this
	// printer had no case for fell through to the delegate printer,
	// which flattened the whole thing onto one line with the source's
	// own spacing.
	{
		`f(){ time { echo a; echo b; }; }; declare -f f`,
		"f () \n{ \n    time { \n        echo a;\n        echo b\n    }\n}\n",
	},
	{
		`f(){ time while false; do :; done; }; declare -f f`,
		"f () \n{ \n    time while false; do\n        :;\n    done\n}\n",
	},
	{
		`f(){ time for ((;;)); do break; done; }; declare -f f`,
		"f () \n{ \n    time for ((1; 1; 1))\n    do\n        break;\n    done\n}\n",
	},
	{
		// A subshell under `time` gains the padding a bare subshell
		// already had (#631), because it now goes through the same case.
		`f(){ time (echo a); }; declare -f f`,
		"f () \n{ \n    time ( echo a )\n}\n",
	},
	{
		// -p is kept, and bare `time` keeps bash's trailing space.
		`f(){ time -p :; }; g(){ time; }; declare -f f; declare -f g`,
		"f () \n{ \n    time -p :\n}\ng () \n{ \n    time \n}\n",
	},

	// A definition's own redirections are part of the function (#631).
	// They hang off the statement wrapping the body, one level up from
	// where the body is rendered, and were dropped — so the printed
	// definition was not the function that was defined, and eval'ing it
	// elsewhere landed a function with different stdio.
	{
		`f(){ echo hi; } 1>&2; declare -f f`,
		"f () \n{ \n    echo hi\n} 1>&2\n",
	},
	{
		// bash re-spaces the operator it prints — `> /dev/null` from a
		// source that wrote `>/dev/null` — while keeping a duplicating
		// form tight, so what is matched is what bash prints.
		`f(){ echo hi; } >/dev/null 2>&1; declare -f f`,
		"f () \n{ \n    echo hi\n} > /dev/null 2>&1\n",
	},
	{
		`f(){ cat; } < /dev/null; declare -f f`,
		"f () \n{ \n    cat\n} < /dev/null\n",
	},
	{
		// `type` prints through the same path, so the two agree, and a
		// duplicating redirection grows its descriptor here too.
		`f(){ echo hi; } >&2; type f`,
		"f is a function\nf () \n{ \n    echo hi\n} 1>&2\n",
	},
	{
		// A nested definition's redirection is indented with its own
		// closing brace and still takes the statement's semicolon.
		`outer(){ inner(){ echo hi; } 1>&2; inner; }; declare -f outer`,
		"outer () \n{ \n    function inner () \n    { \n        echo hi\n    } 1>&2;\n    inner\n}\n",
	},
	{
		// A body that is not a block is wrapped in braces by bash, so
		// its redirection prints *inside* them, on the statement it was
		// written on rather than after the brace bash supplied.
		`f() ( echo hi ) 1>&2; declare -f f`,
		"f () \n{ \n    ( echo hi ) 1>&2\n}\n",
	},
	{
		`f() ( echo hi ); declare -f f`,
		"f () \n{ \n    ( echo hi )\n}\n",
	},
	{
		`f() if true; then echo a; fi 1>&2; declare -f f`,
		"f () \n{ \n    if true; then\n        echo a;\n    fi 1>&2\n}\n",
	},
	{
		`f(){ echo hi; } 2>&-; declare -f f`,
		"f () \n{ \n    echo hi\n} 2>&-\n",
	},
	{
		// A here-string is an ordinary word and prints inline; a
		// here-document is the one shape that cannot (#638).
		`f(){ cat; } <<< "hi"; declare -f f`,
		"f () \n{ \n    cat\n} <<< \"hi\"\n",
	},
	{
		`f(){ echo hi; } {fd}>/dev/null; declare -f f`,
		"f () \n{ \n    echo hi\n} {fd}> /dev/null\n",
	},
	{
		// The reason this is worse than cosmetic: `eval "$(declare -f
		// f)"` is the documented way to move a function between shells,
		// so a dropped redirection is a function that behaves
		// differently where it lands — silently.
		`f(){ echo hi; } 1>&2; eval "$(declare -f f)"; f 2>/dev/null; echo rc=$?`,
		"rc=0\n",
	},

	// Nameref residuals (#389): a reference may name an array element,
	// its target is validated, a self reference is refused, a nameref
	// loop variable is re-targeted rather than written through, and
	// ${!ref[@]} asks for the target's keys rather than its name.
	{
		`a=("" x); declare -n b="a[1]"; echo "[$b]"; b="foo bar"; declare -p a`,
		"[x]\n" + `declare -a a=([0]="" [1]="foo bar")` + "\n",
	},
	{
		`declare -A m=([k]=v); declare -n r="m[k]"; echo "[$r]"; r=new; declare -p m`,
		"[v]\n" + `declare -A m=([k]="new" )` + "\n",
	},
	{
		// The subscript is evaluated at each use, not when the
		// reference was declared.
		`a=(p q); i=0; declare -n r="a[i]"; echo $r; i=1; echo $r`,
		"p\nq\n",
	},
	{
		`declare -n foo=12345; echo rc=$?`,
		"declare: `12345': invalid variable name for name reference\nrc=1\n #JUSTERR",
	},
	{
		`declare -n v=v; echo rc=$?`,
		"declare: v: nameref variable self references not allowed\nrc=1\n #JUSTERR",
	},
	{
		`one=1 two=2; declare -n ref; for ref in one two; do echo "${!ref}=$ref"; done`,
		"one=1\ntwo=2\n",
	},
	{
		`x=1; declare -n r=x; for r in 5 6; do :; done; echo "$x"`,
		"`5': not a valid identifier\n1\n #JUSTERR",
	},
	{
		`a=([1]=x [3]=y); declare -n r=a; echo "${!r[@]}"`,
		"1 3\n",
	},

	// A reference is resolved on read *and* on write (#610). Without
	// -n, a declaration's attributes land on the target rather than on
	// the reference, which is one bug seen from both ends: assigning
	// through a reference to a readonly variable was allowed, and
	// re-pointing a reference whose target is readonly was refused.
	{
		`bar=one; declare -n ref=bar; readonly ref; declare -p ref bar`,
		"declare -n ref=\"bar\"\ndeclare -r bar=\"one\"\n",
	},
	{
		// The value matters as much as the message: a silent assignment
		// passes any test that only reads the diagnostic. The subshell
		// keeps the abandonment (#308) from costing the rest of the line.
		`bar=one; declare -n ref=bar; readonly ref; ( ref=two ); declare -p bar`,
		"bar: readonly variable\n" + `declare -r bar="one"` + "\n #JUSTERR",
	},
	{
		// Re-pointing is not an assignment to the target, so a for loop
		// walks all three where koi answered `ref: readonly variable`
		// and kept the first.
		`readonly one=1 two=2; declare -n ref=one; readonly ref; for ref in one two; do echo "${!ref}=$ref"; done; declare -p ref`,
		"one=1\ntwo=2\n" + `declare -n ref="two"` + "\n",
	},
	{
		`b=1; declare -n r=b; declare -x r; declare -p r b`,
		"declare -n r=\"b\"\ndeclare -x b=\"1\"\n",
	},
	// A reference cannot be an array or an array element, and what it
	// refused is left exactly as it was.
	{
		`declare -a a=(x y); z=1; declare -n a=z; echo rc=$?; declare -p a`,
		"declare: a: reference variable cannot be an array\nrc=1\n" +
			`declare -a a=([0]="x" [1]="y")` + "\n #JUSTERR",
	},
	{
		`z=1; declare -n r[3]=z; echo rc=$?; declare -p r`,
		"declare: r[3]: reference variable cannot be an array\nrc=1\n" +
			"declare: r: not found\nexit status 1 #JUSTERR",
	},
	{
		// A reference's value is a name, so the integer attribute has
		// nothing to evaluate and bash drops it.
		`declare -i x=1; y=42; declare -n x=y; echo "$x"; declare -p x`,
		"42\n" + `declare -n x="y"` + "\n",
	},
	// unset through a reference to an element of something that is not
	// an array is silent, where the same subscript written out is not.
	{
		`y=42; declare -n r='y[2]'; unset r; echo "rc=$? y=$y"`,
		"rc=0 y=42\n",
	},
	{
		`y=42; unset 'y[2]'; echo "rc=$? y=$y"`,
		"unset: y: not an array variable\nrc=1 y=42\n #JUSTERR",
	},
	// Arithmetic follows a reference in both directions.
	{
		`v=7; declare -n r=v; echo $((r+1)); (( r = 20 )); echo "$v"; (( r += 5 )); echo "$v"`,
		"8\n20\n25\n",
	},
	// An indirect expansion may point at an array element, and a
	// reference to a reference to one resolves through both.
	{
		`arr=(a b); i='arr[1]'; echo ${!i}`,
		"b\n",
	},
	{
		`bar=4; declare -n foo='bar[0]'; f(){ declare -n one=$1; echo "[$one]"; }; f foo`,
		"[4]\n",
	},

	// The directory stack is bash's: entry 0 is the current directory,
	// so cd moves it, dirs prints it first, and pushd/popd take +N/-N
	// stack arguments (#390).
	{
		`cd /; pushd /usr >/dev/null; pushd /tmp >/dev/null; dirs; echo "DS:${DIRSTACK[@]}"`,
		"/tmp /usr /\nDS:/tmp /usr /\n",
	},
	{
		`cd /; pushd /usr>/dev/null; cd /tmp; dirs`,
		"/tmp /\n",
	},
	{
		`cd /; pushd /usr>/dev/null; pushd /tmp>/dev/null; pushd +2>/dev/null; dirs; pwd`,
		"/ /tmp /usr\n/\n",
	},
	{
		`cd /; pushd /usr>/dev/null; popd>/dev/null; pwd`,
		"/\n",
	},
	{
		`cd /; pushd /usr>/dev/null; dirs -v`,
		" 0  /usr\n 1  /\n",
	},
	{
		`cd /; pushd /usr>/dev/null; dirs +1; dirs -1; dirs -c; dirs`,
		"/\n/usr\n/usr\n",
	},
	{
		`cd /; pushd /usr>/dev/null; pushd /tmp>/dev/null; echo ~1 ~-1 ~0 ~+2`,
		"/usr /usr /tmp /\n",
	},
	{
		`cd /; pushd /usr>/dev/null; pushd /tmp>/dev/null; popd +1>/dev/null; dirs`,
		"/tmp /\n",
	},
	{
		// -n pushes below the current directory and pops the entry
		// below it, so the shell never moves.
		`cd /; pushd /usr>/dev/null; pushd -n /tmp>/dev/null; dirs; pwd`,
		"/usr /tmp /\n/usr\n",
	},
	{
		`cd /; pushd /usr>/dev/null; pushd /tmp>/dev/null; popd -n; pwd`,
		"/tmp /\n/tmp\n",
	},
	// cd takes -L and -P, and searches CDPATH for a relative operand
	// (#391) — koi answered a usage error and never changed directory.
	{
		// -L keeps the path as written, -P resolves it. The symlink is
		// built here rather than relying on /tmp, which is a symlink on
		// darwin and a real directory on linux — a case that bakes that
		// in passes on one platform and fails on the other.
		`mkdir real; ln -s real link; cd -L link; [ "$(basename "$PWD")" = link ] && echo kept`,
		"kept\n",
	},
	{
		`mkdir real; ln -s real link; cd -P link; [ "$(basename "$PWD")" = real ] && echo resolved`,
		"resolved\n",
	},
	{
		`cd -P .; echo "st=$?"`,
		"st=0\n",
	},
	{
		`cd -- /tmp && pwd`,
		"/tmp\n",
	},

	// mapfile's remaining flags (#392): each was refused, which left
	// the array never created — so a later loop over it printed
	// nothing rather than failing.
	{
		`printf "a\nb\nc\n" | { mapfile -n 2 arr; declare -p arr; }`,
		`declare -a arr=([0]=$'a\n' [1]=$'b\n')` + "\n",
	},
	{
		`printf "a\nb\n" | { mapfile -O 5 -t arr; declare -p arr; }`,
		`declare -a arr=([5]="a" [6]="b")` + "\n",
	},
	{
		`printf "a\nb\nc\nd\n" | { mapfile -s 2 -t arr; declare -p arr; }`,
		`declare -a arr=([0]="c" [1]="d")` + "\n",
	},
	{
		`printf "a\nb\n" | { mapfile -t -C "echo cb:" -c 1 arr; declare -p arr; }`,
		"cb: 0 a\ncb: 1 b\n" + `declare -a arr=([0]="a" [1]="b")` + "\n",
	},
	{
		`printf "a\nb\n" | { mapfile -t -n 0 arr; declare -p arr; }`,
		`declare -a arr=([0]="a" [1]="b")` + "\n",
	},
	{
		`mapfile -n x arr; echo st=$?`,
		"mapfile: x: invalid line count\nst=1\n #JUSTERR",
	},
	{
		`mapfile -u x arr; echo st=$?`,
		"mapfile: x: invalid file descriptor specification\nst=1\n #JUSTERR",
	},
	// A bare `set` lists the shell's variables and functions (#394),
	// quoted the shortest way that reads back.
	{
		`FOO=bar; set | grep "^FOO="`,
		"FOO=bar\n",
	},
	{
		`V="a b"; set | grep "^V="`,
		"V='a b'\n",
	},
	{
		`V=$'a\nb'; set | grep "^V="`,
		`V=$'a\nb'` + "\n",
	},
	{
		`a=(1 2); set | grep "^a="`,
		`a=([0]="1" [1]="2")` + "\n",
	},
	{
		// The functions come after the variables, in the canonical
		// form declare -f prints.
		`f(){ echo hi; }; set | grep "^f ()"`,
		"f () \n",
	},

	// echo's flag letters cluster (#399): -ne was printed as an
	// operand, which is the whole of strip.tests.
	{"echo -ne \"ab\\ncd\"; echo END", "ab\ncdEND\n"},
	{"echo -en x; echo E", "xE\n"},
	{"echo -nx word", "-nx word\n"},
	{"echo -eE \"a\\tb\"", "a\\tb\n"},
	// printf's missing conversions (#400) are not covered here: koi's
	// printf is the native builtin in internal/builtins, reached
	// through the CallHandler, and this package has its own older
	// implementation in expand.Format. The cases live in cmd/koi's
	// builtins matrix, which runs the printf a user actually gets.

	// test and [ support < and > for string comparison, which koi
	// called invalid operators — status 2 on an ordinary sort check
	// (#401).
	{`test hello \> goodbye; echo gt=$?`, "gt=0\n"},
	{`test a \< b; echo lt=$?`, "lt=0\n"},
	// An operand that is not an integer is a *diagnostic* at status 2,
	// not a silent false: `if test 4+3 -eq 7` took the else branch with
	// nothing printed (#401). The message names the shell the way it
	// was invoked.
	{"test 4+3 -eq 7; echo $?", "test: 4+3: integer expected\n2\n #JUSTERR"},
	{"test -t X; echo $?", "test: X: integer expected\n2\n #JUSTERR"},
	{"[ -t 1x ]; echo $?", "[: 1x: integer expected\n2\n #JUSTERR"},
	{"[[ -t X ]]; echo $?", "[[: X: integer expected\n2\n #JUSTERR"},
	{`test " 7 " -eq 7; echo $?`, "0\n"},
	// [[ ]] evaluates its numeric operands arithmetically, where test
	// wants a plain integer (#402).
	{"[[ 4+3 -eq 7 ]]; echo $?", "0\n"},
	{"[[ x -eq 1 ]]; echo $?", "1\n"},
	// `!` binds to the first term, not to the whole disjunction — the
	// one that changes the truth value of real conditions (#402).
	{"[[ ! x || x ]]; echo $?", "0\n"},
	{`[[ ! x && "" ]]; echo $?`, "1\n"},
	{`[[ ! "" && x ]]; echo $?`, "0\n"},
	{"[[ ! x || x || x ]]; echo $?", "0\n"},
	{"[[ ! ( x || x ) ]]; echo $?", "1\n"},
	{"[[ ! x = y ]]; echo $?", "0\n"},
	{`[[ ! -z "" && x ]]; echo $?`, "1\n"},
	// `&&` binds tighter than `||` in bash's conditionals, so
	// `[[ A && B || C ]]` is `(A && B) || C` (#669). Giving the two
	// equal precedence and grouping right read it as `A && (B || C)`,
	// which answers the *other* branch of one of the commonest idioms
	// in shell with nothing printed to say so. Every case here puts a
	// false-left `&&` to the left of a `||`, since that is the only
	// arrangement the two groupings disagree about -- `[[ x || y && z ]]`
	// answers the same either way and proves nothing.
	{"[[ 1 == 2 && 1 == 2 || 1 == 1 ]]; echo $?", "0\n"},
	{"[[ 1 == 2 && 1 == 1 || 1 == 1 ]]; echo $?", "0\n"},
	{"[[ 1 == 2 && 1 == 2 && 1 == 2 || 1 == 1 ]]; echo $?", "0\n"},
	{"[[ 1 == 2 && 1 == 2 || 1 == 2 || 1 == 1 ]]; echo $?", "0\n"},
	{"[[ 1 == 2 && 1 == 2 || 1 == 1 && 1 == 1 ]]; echo $?", "0\n"},
	// The other direction, which fails if `&&` is made *looser* rather
	// than tighter: `(1 == 1 || 1 == 2) && 1 == 2` would be false.
	{"[[ 1 == 1 || 1 == 2 && 1 == 2 ]]; echo $?", "0\n"},
	// Which is why `!` had to move into the parser with it: the old
	// negation swallowed everything to its right and interp put it back
	// where it belonged, and no amount of that can rescue a `!` sitting
	// inside the right operand of an `&&` -- it still eats the `|| C`.
	{"[[ 1 == 2 && ! 1 == 1 || 1 == 1 ]]; echo $?", "0\n"},
	{"[[ ! 1 == 1 && 1 == 1 || 1 == 1 ]]; echo $?", "0\n"},
	{"[[ ! 1 == 2 && 1 == 2 ]]; echo $?", "1\n"},
	{"[[ ! ! 1 == 2 && 1 == 2 ]]; echo $?", "1\n"},
	{"[[ ! ( 1 == 2 && 1 == 2 ) ]]; echo $?", "0\n"},
	// The classic form has the same shape and the same bug: POSIX makes
	// `-o` looser than `-a`, and bash's test.c is or() over and() over
	// term(), so a `!` binds to one term there too.
	{"[ 1 = 2 -a 1 = 2 -o 1 = 1 ]; echo $?", "0\n"},
	{"[ 1 = 2 -a 1 = 1 -o 1 = 1 ]; echo $?", "0\n"},
	{"[ 1 = 2 -a 1 = 2 -o 1 = 1 -a 1 = 1 ]; echo $?", "0\n"},
	{"[ ! 1 = 1 -a 1 = 1 -o 1 = 1 ]; echo $?", "0\n"},
	{"[ 1 = 2 -a ! 1 = 2 -o 1 = 1 ]; echo $?", "0\n"},
	{"[ ! 1 = 2 -a 1 = 2 ]; echo $?", "1\n"},
	{"[ 1 = 1 -o 1 = 2 -a 1 = 2 ]; echo $?", "0\n"},
	{"test 1 = 2 -a 1 = 2 -o 1 = 1; echo $?", "0\n"},
	{`[ \( 1 = 2 -a 1 = 2 \) -o 1 = 1 ]; echo $?`, "0\n"},
	// The two grammars that were already right, so a fix that reached
	// them is caught rather than reasoned about. The ordinary shell
	// grammar gives `&&` and `||` *equal* precedence, left to right, so
	// `true || false && false` is `(true || false) && false`; the
	// arithmetic evaluator is C's, where `&&` is tighter.
	{"false && false || true; echo $?", "0\n"},
	{"true || false && false; echo $?", "1\n"},
	{"(( 0 && 0 || 1 )); echo $?", "0\n"},
	// `(( 0 && 0 || 1 ))` alone cannot tell C's precedence from equal
	// precedence read left to right -- both answer 1 -- so the case
	// that can is the one with `&&` on the *right*: `1 || (0 && 0)` is
	// 1 where `(1 || 0) && 0` is 0.
	{"(( 1 || 0 && 0 )); echo $?", "0\n"},
	{"echo $(( 1 || 0 && 0 ))", "1\n"},
	// Short-circuiting follows the corrected tree: with `&&` grouped
	// first, a false left operand skips the `&&`'s right side and the
	// `||`'s right side decides -- the arithmetic assignment never runs.
	{`v=1; [[ -z x && -n $(( v=42 )) || -n z ]]; echo "r=$? v=$v"`, "r=0 v=1\n"},
	// The tree is what `declare -f` prints back, and `eval "$(declare -f
	// f)"` is how a function moves between shells -- a definition that
	// came back grouped differently would be a different function.
	{
		"f() { [[ 1 == 2 && 1 == 2 || 1 == 1 ]]; }; declare -f f",
		"f () \n{ \n    [[ 1 == 2 && 1 == 2 || 1 == 1 ]]\n}\n",
	},
	{
		"f() { [[ ! 1 == 1 && 1 == 1 ]]; }; declare -f f",
		"f () \n{ \n    [[ ! 1 == 1 && 1 == 1 ]]\n}\n",
	},
	{
		"f() { [ 1 = 2 -a 1 = 2 -o 1 = 1 ]; }; declare -f f",
		"f () \n{ \n    [ 1 = 2 -a 1 = 2 -o 1 = 1 ]\n}\n",
	},
	// `[[ ]]` short-circuits, so the untaken side of && or || is never
	// expanded and its side effects never happen (#652). The status
	// cases below cannot tell on their own -- a shell that evaluates
	// both sides still answers 0 and 1 here -- so each direction also
	// carries a case whose right-hand side would be *visible* had it
	// run: a command substitution writing to stderr, an arithmetic
	// assignment to a variable the next command prints, and a
	// redirection creating a file.
	{"[[ -n x || -n $(echo SIDE >&2; echo y) ]]; echo r=$?", "r=0\n"},
	{"[[ -z x && -n $(echo SIDE >&2; echo y) ]]; echo r=$?", "r=1\n"},
	{`v=1; [[ -n x || -n $(( v=42 )) ]]; echo "r=$? v=$v"`, "r=0 v=1\n"},
	{`v=1; [[ -z x && -n $(( v=42 )) ]]; echo "r=$? v=$v"`, "r=1 v=1\n"},
	{
		`[[ -n x || -n $(>side; echo y) ]]; s=$?; [[ -f side ]]; echo "r=$s made=$?"`,
		"r=0 made=1\n",
	},
	{
		`[[ -z x && -n $(>side; echo y) ]]; s=$?; [[ -f side ]]; echo "r=$s made=$?"`,
		"r=1 made=1\n",
	},
	// An operand the skipped side could not even read is not read: a
	// bad substitution, an unset with `:?`, and an unreadable numeric
	// operand all cost nothing when the operator has already decided.
	{"H=1; [[ -n x || $HOME -ef ${H*} ]]; echo $?", "0\n"},
	{"H=1; [[ -z x && $HOME -ef ${H*} ]]; echo $?", "1\n"},
	{"[[ -n x || -n ${nope:?boom} ]]; echo $?", "0\n"},
	{"[[ 1 -eq 1 || x+ -eq 1 ]]; echo $?", "0\n"},
	{"[[ 1 -eq 2 && x+ -eq 1 ]]; echo $?", "1\n"},
	// A unary operand is a skipped side too.
	{"[[ -z x && -f $(echo G >&2; echo /etc/hosts) ]]; echo $?", "1\n"},
	// `=~` also writes BASH_REMATCH, so a skipped match must leave the
	// previous one alone.
	{
		`[[ ab =~ (a)(b) ]]; [[ -z x && zz =~ (z)(z) ]]; echo "${BASH_REMATCH[@]}"`,
		"ab a b\n",
	},
	// Grouping: the short circuit follows whichever operand the tree
	// says is first, so parentheses and `!` compose with it. The
	// unparenthesized `a && b || c` shape is deliberately absent --
	// koi groups it to the right where bash groups it left, which is
	// the separate parser bug filed as #669, and a case for it here
	// would be asserting the wrong tree rather than the short circuit.
	{"[[ ( -z x && -n $(echo A >&2; echo y) ) || -n z ]]; echo $?", "0\n"},
	{"[[ -n a || -n b && -n $(echo B >&2; echo y) ]]; echo $?", "0\n"},
	{"[[ ( -n x || -n $(echo C >&2; echo y) ) && -n q ]]; echo $?", "0\n"},
	{"[[ ! -z x || -n $(echo D >&2; echo y) ]]; echo $?", "0\n"},
	{"[[ ! ( -n x || -n $(echo E >&2; echo y) ) ]]; echo $?", "1\n"},
	{"[[ -n x || ! -n $(echo F >&2; echo y) ]]; echo $?", "0\n"},
	// `[` and `test` are not the same construct: they are builtins
	// whose whole argv was expanded before they ran, so `-a` and `-o`
	// have no side to skip and both diagnose. Recorded rather than
	// "fixed" -- matching bash here means evaluating both.
	{`[ -n x -o -n "$(echo SIDE >&2; echo y)" ]; echo r=$?`, "SIDE\nr=0\n"},
	{`test -z x -a -n "$(echo SIDE >&2; echo y)"; echo r=$?`, "SIDE\nr=1\n"},
	{`v=1; [ -n x -o -n "$(( v=42 ))" ]; echo "r=$? v=$v"`, "r=0 v=42\n"},
	{"[ 1 -eq 1 -o x -eq 1 ]; echo $?", "[: x: integer expected\n2\n #JUSTERR"},
	// Arithmetic already short-circuits, and agrees with bash in both
	// directions and for `?:` (#597).
	{`B=1; echo $(( 0 && (B=42) )); echo B=$B`, "0\nB=1\n"},
	{`B=1; echo $(( 1 || (B=42) )); echo B=$B`, "1\nB=1\n"},
	{`B=1; (( 0 && (B=42) )); echo "st=$? B=$B"`, "st=1 B=1\n"},
	{`B=1; (( 1 || (B=42) )); echo "st=$? B=$B"`, "st=0 B=1\n"},
	{`B=1; echo $(( 0 ? (B=42) : 7 )); echo B=$B`, "7\nB=1\n"},
	// getopts: OPTERR=0 silences the diagnostic, and `--` is consumed
	// so OPTIND points past it (#403).
	{
		`OPTERR=0; while getopts ab opt -a -c b; do echo "opt=$opt"; done`,
		"opt=a\nopt=?\n",
	},
	{
		`set -- -a -- -b bval one; OPTIND=1; while getopts ab: opt; do :; done; shift $((OPTIND-1)); echo "rest: $@"`,
		"rest: -b bval one\n",
	},
	{
		// Assigning OPTIND restarts the scan *within* a clustered word
		// too, and the position travels with a local OPTIND. koi
		// compared only the argument index, so this recursion — the
		// suite's getopts8.sub — never terminated (#403).
		`f() { typeset OPTIND=1 o; while getopts ":abcxyz" o; do echo "opt: $o"; if [[ $o = y ]]; then f -abc; fi; done; }; f -xyz`,
		"opt: x\nopt: y\nopt: a\nopt: b\nopt: c\nopt: z\n",
	},

	// A readonly target aborts read's assignment list at status 2, per
	// POSIX (#404): koi reported the error, skipped that name,
	// assigned the rest, and answered 0.
	{
		`readonly b; read a b c <<< "1 2 3"; echo "a=$a b=$b c=$c stat=$?"`,
		"b: readonly variable\na=1 b= c= stat=2\n #JUSTERR",
	},
	// An option's value may be attached inside a cluster (#405): only
	// the spaced form worked, so `read -ru3` read the *variable name*
	// as the descriptor.
	{
		`echo hello > f; exec 3<f; read -ru3 x; echo "clustered:$?:$x"`,
		"clustered:0:hello\n",
	},
	{
		`echo hello > f; exec 3<f; read -u3 x; echo "u3:$?:$x"`,
		"u3:0:hello\n",
	},
	{
		`printf "a\nb\n" | { read -n1 x; echo "n1=[$x]"; }`,
		"n1=[a]\n",
	},

	// The dynamic variables a script times and identifies itself with
	// (#408). SECONDS starts at zero, EPOCHSECONDS is ten digits, and
	// BASHPID differs inside a subshell — koi has no separate process
	// there, so the number is per execution context.
	{`echo "[$SECONDS]"`, "[0]\n"},
	{`x=$EPOCHSECONDS; [ ${#x} -eq 10 ] && echo epoch-ok`, "epoch-ok\n"},
	{`b=$BASHPID; s=$( (echo $BASHPID) ); [ "$b" != "$s" ] && echo differs`, "differs\n"},
	{`BASH_ARGV0=hello; echo $0`, "hello\n"},
	{
		// A write to GROUPS is discarded rather than refused, which is
		// bash's — refusing it would make an ignored assignment fatal.
		`before=${GROUPS[0]}; GROUPS[0]=-1; [ "${GROUPS[0]}" = "$before" ] && echo write-discarded`,
		"write-discarded\n",
	},
	// `$_` is the previous command's last argument, and was the
	// shell's own path forever — which flips every ${_+word} probe.
	{`echo hi >/dev/null; echo "[$_]"`, "[hi]\n"},
	{`true a b; echo "[$_]"`, "[b]\n"},
	{`f(){ :; }; f q; echo "[$_]"`, "[q]\n"},
	{`echo; echo "[$_]"`, "\n[echo]\n"},
	{`x=1; echo "[$_]"`, "[]\n"},
	// A loop variable must be an identifier; koi ran the loop and
	// quietly shadowed the positional parameter (#409).
	{
		`for 1 in a b c; do echo "[$1]"; done; echo rc=$?`,
		"`1': not a valid identifier\nrc=1\n #JUSTERR",
	},

	// The builtin option surface (#411): each of these was a usage
	// error or a wrong answer, and together they are most of
	// builtins.tests' remaining diff.
	{"command -p echo hi; echo rc=$?", "hi\nrc=0\n"},
	{"command -V echo", "echo is a shell builtin\n"},
	{"f(){ :; }; command -V f | head -1", "f is a function\n"},
	{"for i in 1 2; do break --; done; echo rc=$?", "rc=0\n"},
	{"for i in 1 2; do continue --; done; echo rc=$?", "rc=0\n"},
	// kill -l's translation and umask's symbolic modes are koi
	// builtins rather than interpreter ones, so their cases live in
	// cmd/koi's builtins matrix where the real implementations run.
	// -a reports every match rather than the first, so a script can
	// see that a builtin is shadowing the program it meant.
	{"type -a echo | head -1", "echo is a shell builtin\n"},
	{"type -p echo; echo rc=$?", "rc=0\n"},
	{
		// -P forces the PATH search where -p answers about what the
		// shell would run. The path itself differs by platform
		// (/bin/echo on darwin, /usr/bin/echo on linux), so the case
		// asserts that something executable was named.
		`[ -x "$(type -P echo)" ] && echo executable`,
		"executable\n",
	},
	// `enable -n` really turns the builtin off, so the name resolves
	// on PATH like any other command.
	{"enable -n test; type -t test", "file\n"},
	{"enable -n test; enable test; type -t test", "builtin\n"},
	{"enable nosuchxyz; echo rc=$?", "enable: nosuchxyz: not a shell builtin\nrc=1\n #JUSTERR"},
	// -s lists the sixteen POSIX special builtins and nothing else, in
	// the same `enable NAME` shape as the plain listing. The pair below
	// asserts both states of one name: `exit` appears as enabled here
	// and as disabled in the next case, because a listing checked only
	// for what it lacks passes vacuously against an empty listing.
	{
		"enable -ps",
		"enable .\nenable :\nenable break\nenable continue\nenable eval\n" +
			"enable exec\nenable exit\nenable export\nenable readonly\nenable return\n" +
			"enable set\nenable shift\nenable source\nenable times\nenable trap\nenable unset\n",
	},
	{
		"enable -n exit; enable -as",
		"enable .\nenable :\nenable break\nenable continue\nenable eval\n" +
			"enable exec\nenable -n exit\nenable export\nenable readonly\nenable return\n" +
			"enable set\nenable shift\nenable source\nenable times\nenable trap\nenable unset\n",
	},
	// -n alone lists what is off rather than turning anything off, and
	// -p forces that listing even when names follow it -- bash's own
	// branch order, which no reading of the manual would predict.
	{"enable -nps", ""},
	{"enable -n test; enable -pn test", "enable -n test\n"},
	// `builtin` asks for the shell's version of a name, and for a
	// disabled builtin there no longer is one. This is the one place it
	// parts company with `command`, which runs the program instead.
	{
		"enable -n printf; builtin printf x",
		"builtin: printf: not a shell builtin\nexit status 1 #JUSTERR",
	},
	// -d removes a builtin that -f loaded, so here it can only refuse --
	// with bash's two answers rather than with "invalid option", which
	// would read as koi not knowing the flag (#603).
	{"enable -d test", "enable: test: not dynamically loaded\nexit status 1 #JUSTERR"},
	{"enable -d nosuchxyz", "enable: nosuchxyz: not a shell builtin\nexit status 1 #JUSTERR"},
	// A lone dash is a name in bash, not an option, and so is a `+`
	// word -- which also ends the options, so the builtin after it is
	// left alone rather than switched off.
	{"enable -", "enable: -: not a shell builtin\nexit status 1 #JUSTERR"},
	{"enable +n test", "enable: +n: not a shell builtin\nexit status 1 #JUSTERR"},
	{
		"enable -x",
		"enable: -x: invalid option\n" +
			"enable: usage: enable [-a] [-dnps] [-f filename] [name ...]\nexit status 2 #JUSTERR",
	},
	{
		"enable -f",
		"enable: -f: option requires an argument\n" +
			"enable: usage: enable [-a] [-dnps] [-f filename] [name ...]\nexit status 2 #JUSTERR",
	},
	{
		// The one deliberate divergence: bash reaches dlopen here and
		// reports a platform-specific loader error, while koi cannot
		// load a builtin object at all. The message is bash's own for
		// exactly this case -- what a bash compiled without dlopen
		// prints, EX_USAGE included. #JUSTERR asserts only that bash
		// also refuses, which is the honest comparison to make.
		"enable -f /nosuch.so printf",
		"enable: dynamic loading not available\nexit status 2 #JUSTERR",
	},
	// `hash -p` pins a name to a path, and the pin is consulted before
	// PATH — koi accepted the line and did nothing with it.
	{"hash -p /bin/ls myls; type myls", "myls is hashed (/bin/ls)\n"},
	{"hash -p /bin/echo myecho; myecho hi", "hi\n"},
	{"hash; echo rc=$?", "hash: hash table empty\nrc=0\n"},
	// -l, -t and -d were accepted and ignored, so `hash -t name` — the
	// way a script asks where a name resolved — printed the whole table
	// and answered 0 for a name that was not in it (#604).
	{"hash -p /bin/ls myls; hash -t myls", "/bin/ls\n"},
	{"hash -p /bin/ls myls; hash -p /bin/cat mycat; hash -t myls mycat", "myls\t/bin/ls\nmycat\t/bin/cat\n"},
	{"hash -p /bin/ls myls; hash -lt myls", "builtin hash -p /bin/ls myls\n"},
	{"hash -p /bin/ls myls; hash -l", "builtin hash -p /bin/ls myls\n"},
	{"hash -l", ""},
	{"hash -t nope", "hash: nope: not found\nexit status 1 #JUSTERR"},
	{"hash -p /bin/ls myls; hash -d myls; hash", "hash: hash table empty\n"},
	{"hash -d nope", "hash: nope: not found\nexit status 1 #JUSTERR"},
	// -d and -t together prints rather than deletes, and -r wins
	// wherever it appears. Both measured.
	{"hash -p /bin/ls myls; hash -dt myls; hash -t myls", "/bin/ls\n/bin/ls\n"},
	{"hash -p /bin/ls myls; hash -l -r; hash", "hash: hash table empty\n"},
	// A path that does not exist is a legal pin; a directory is not.
	{"hash -p /nosuchdir/x myx; hash -t myx", "/nosuchdir/x\n"},
	{"hash -p / myroot", "hash: /: Is a directory\nexit status 1 #JUSTERR"},
	{"hash -x", "hash: -x: invalid option\nhash: usage: hash [-lr] [-p pathname] [-dt] [name ...]\nexit status 2 #JUSTERR"},
	{"hash -p", "hash: -p: option requires an argument\nhash: usage: hash [-lr] [-p pathname] [-dt] [name ...]\nexit status 2 #JUSTERR"},
	{"hash -p /bin/ls", "hash: usage: hash [-lr] [-p pathname] [-dt] [name ...]\nexit status 2 #JUSTERR"},
	// `checkhash` verifies the pin before running it, so a stale entry
	// is dropped and the name searched again. It governs running only:
	// `type` still answers with the pin.
	{
		// The path `ls` really has is the platform's — /bin/ls on darwin
		// and /usr/bin/ls on linux — so the assertion is that the stale
		// pin was *replaced* by something runnable rather than that it
		// was replaced by one particular path. Without checkhash the
		// line above shows what happens instead: exit 127 and the pin
		// still in the table.
		`hash -p /nosuchdir/nosuchls ls; shopt -s checkhash; ls >/dev/null
p=$(hash -t ls); [[ $p != /nosuchdir/nosuchls && -x $p ]] && echo re-searched`,
		"re-searched\n",
	},
	{"hash -p /nosuchdir/nosuchls ls; shopt -s checkhash; type ls", "ls is hashed (/nosuchdir/nosuchls)\n"},
	{"hash -p /nosuchdir/nosuchls ls; ls >/dev/null", "/nosuchdir/nosuchls: No such file or directory\nexit status 127 #JUSTERR"},
	// `command -v` reads the pin too, which is the one answer a pin
	// exists to override and the one koi answered from PATH.
	{"hash -p /nosuchdir/x mycat; command -v mycat", "/nosuchdir/x\n"},
	{"hash -p /nosuchdir/x mycat; command -V mycat", "mycat is hashed (/nosuchdir/x)\n"},

	// A command substitution runs without errexit unless
	// inherit_errexit asks for it (#412): koi passed it down, so the
	// body stopped at the false and the caller carried on with an
	// empty value.
	{`set -e; echo $(false; echo ok); echo after`, "ok\nafter\n"},
	{`set -e; shopt -s inherit_errexit; echo $(false; echo ok); echo after`, "\nafter\n"},
	{
		// The suppression has to be in force *while* the negated
		// statement runs: koi applied the negation afterwards, so this
		// took the shell down inside eval and truncated the script.
		`set -e; ! eval false; echo ok1`,
		"ok1\n",
	},
	// xtrace fidelity (#413): PS4 is expanded, an append is traced as
	// an append rather than its result, `set` after the first is
	// traced rather than dropped as a blank line, and an arithmetic
	// for header is traced evaluation by evaluation.
	{`PS4="+[x] "; set -x; :; set +x`, "+[x] :\n+[x] set +x\n"},
	{
		// PS4's $LINENO is the *traced* line, not the line of the PS4
		// string — which is parsed on its own and would always be 1.
		`PS4="[\$LINENO] "; set -x; :; set +x`,
		"[1] :\n[1] set +x\n",
	},
	{`set -x; foo=one; foo+=two; set +x`, "+ foo=one\n+ foo+=two\n+ set +x\n"},
	{
		`set -x; for ((i=0;i<2;i++)); do :; done; set +x`,
		"+ (( i=0 ))\n+ (( i<2 ))\n+ :\n+ (( i++ ))\n+ (( i<2 ))\n+ :\n+ (( i++ ))\n+ (( i<2 ))\n+ set +x\n",
	},
	// A trace quotes each *field* on its own (#604). koi joined them
	// into one string and quoted that, and only for a builtin — so
	// `echo a b` traced as one field where the command received two,
	// and `/bin/echo "a b"` as two where it received one. A trace is
	// what someone re-runs, and both re-ran as a different command.
	{`set -x; echo a b; set +x`, "+ echo a b\na b\n+ set +x\n"},
	{`set -x; echo "a b" c; set +x`, "+ echo 'a b' c\na b c\n+ set +x\n"},
	{`set -x; /bin/echo "a b"; set +x`, "+ /bin/echo 'a b'\na b\n+ set +x\n"},
	{`set -x; echo ""; set +x`, "+ echo ''\n\n+ set +x\n"},
	{`set -x; f() { :; }; f "x y"; set +x`, "+ f 'x y'\n+ :\n+ set +x\n"},
	// bash's own quoting rules, which are not a general-purpose
	// quoter's: single quotes rather than double, `#` and `,` and `]`
	// left alone, and a control byte spelled in octal.
	{`set -x; : "it's"; set +x`, "+ : 'it'\\''s'\n+ set +x\n"},
	{`set -x; : a#b a,b "]" "~"; set +x`, "+ : a#b a,b ']' '~'\n+ set +x\n"},
	{`set -x; : $'a\tb'; set +x`, "+ : $'a\\tb'\n+ set +x\n"},
	{`set -x; : $'\001'; set +x`, "+ : $'\\001'\n+ set +x\n"},

	// An alias is replacement *text*, spliced into the command line and
	// re-parsed (#407). koi built a word list at definition time, so
	// most real aliases were refused outright.
	{
		`shopt -s expand_aliases; alias run="echo one; echo two"
run`,
		"one\ntwo\n",
	},
	{
		`shopt -s expand_aliases; alias ok="echo OK >&2"
ok`,
		"OK\n",
	},
	{
		// The replacement is scanned for aliases again, which is what
		// makes an alias built out of another one work.
		`shopt -s expand_aliases; alias e=echo; alias v="e 123"
echo $(v)`,
		"123\n",
	},
	{
		// A trailing blank asks for the next word to be expanded too.
		`shopt -s expand_aliases; alias a="echo x "; alias b=hello
a b`,
		"x hello\n",
	},
	{
		// A self-referential alias expands once and then means the
		// command, rather than looping.
		`shopt -s expand_aliases; alias echo="echo pre"
echo hi`,
		"pre hi\n",
	},
	{
		`shopt -s expand_aliases; alias q="cat <<EOF
inline
EOF"
q`,
		"inline\n",
	},
	// unalias diagnoses; koi answered 0 for all three (#407).
	{"unalias; echo rc=$?", "unalias: usage: unalias [-a] name [name ...]\nrc=2\n #IGNORE bash's usage line names the shell"},
	{"unalias -x; echo rc=$?", "unalias: -x: invalid option\nunalias: usage: unalias [-a] name [name ...]\nrc=2\n #JUSTERR"},
	{"unalias nosuch; echo rc=$?", "unalias: nosuch: not found\nrc=1\n #JUSTERR"},

	{
		// Reading a process substitution a second time gives EOF rather
		// than an error, because bash's are /dev/fd entries and koi's
		// FIFO is gone by then (#420): the failed open answered nothing
		// at all, so a line went missing rather than reading zero.
		// Written with `read` rather than `wc -l`, whose column
		// padding differs between platforms — which is what CI
		// reported when it was.
		`f() { read -r x < $1; echo "1:[$x]"; read -r y < $1; echo "2:[$y] rc=$?"; echo reached; }; f <(echo one); echo done=$?`,
		"1:[one]\n2:[] rc=1\nreached\ndone=0\n",
	},

	// bash 5.3's funsubs run in the *current* shell, which is what they
	// exist for (#421): koi ran them in a subshell like an ordinary
	// substitution, so nothing they changed survived.
	{`v=1; x=${ v=2; echo aa; }; echo "x=$x v=$v"`, "x=aa v=2\n"},
	{`set -- p q; x=${ set -- z; }; echo "$@"`, "z\n"},
	{`x=${ echo a; echo b; }; echo "[$x]"`, "[a\nb]\n"},
	{
		// `${| …; }` takes its value from REPLY and does *not* capture
		// output, and the caller's REPLY is saved around it.
		`y=${| echo out; REPLY=hey; }; echo "y=[$y]"`,
		"out\ny=[hey]\n",
	},
	{`REPLY=old; y=${| :; }; echo "y=[$y] REPLY=[$REPLY]"`, "y=[] REPLY=[old]\n"},

	// Word expansion happens before a command's own redirections, so an
	// expansion error is reported to the stderr that was in force
	// before them (#469): koi applied the redirections first, so the
	// diagnostic went into /dev/null and the script stopped mid-unit
	// with nothing said.
	{
		`set -u; echo $nope 2>/dev/null; echo after`,
		"nope: unbound variable\nexit status 1 #JUSTERR",
	},
	{
		// An enclosing block's redirection is still in force, which is
		// why this is per statement rather than the shell's original
		// stderr.
		`set -u; { echo $nope; } 2>/dev/null; echo after`,
		"exit status 1 #JUSTERR",
	},
	{
		`shopt -s failglob; echo nomatch* 2>/dev/null; echo after`,
		"no match: nomatch*\nexit status 1 #JUSTERR",
	},
	{
		// A trap action that is itself a pipeline fired the trap again
		// from its own stages, which produced no output at all and took
		// the command that triggered it along (#496).
		// One DEBUG here where bash fires two: the granularity
		// divergence recorded in #268, not this fix.
		`trap "echo T | cat" DEBUG; echo x`,
		"T\nx\n #IGNORE koi's DEBUG granularity differs (#268)",
	},

	{
		// A non-login shell refuses, naming the command that does work
		// (#427). koi answered "unsupported builtin", which reads as a
		// missing builtin rather than as the shell not being a login
		// shell — and the two want different fixes.
		"logout; echo rc=$?",
		"logout: not login shell: use `exit'\nrc=1\n #JUSTERR",
	},

	{
		// A `[` that never closes is a literal one, and the scan
		// carries on — so this is a literal bracket followed by a real
		// bracket expression, which is how bash reads it (#468). koi
		// gave up on the whole word and fell back to the literal.
		`touch "[a" b; echo [[:alpha:]`,
		"[a\n",
	},
	{
		`case "[a" in [[:alpha:]) echo m;; *) echo no;; esac`,
		"m\n",
	},
	{
		// The residual of #372: a backslash inside a bracket escapes
		// the character after it, so this is the range a-z. Already
		// answered correctly at the expand layer; the case pins it so
		// it cannot regress unnoticed (#464).
		`case p in [a-\z]) echo m;; *) echo no;; esac`,
		"m\n",
	},

	// A restricted shell (#398). It is a compatibility feature rather
	// than a security boundary — bash's own manual says as much, and
	// koi's answer to confinement is the sandbox profiles on the exec
	// path — but a script asking for it was refused outright, so every
	// probe in rsh.tests simply succeeded.
	{"set -r; cd /tmp; echo rc=$?", "cd: restricted\nrc=1\n #JUSTERR"},
	{"set -r; /bin/echo hi; echo rc=$?", "/bin/echo: restricted: cannot specify `/' in command names\nrc=1\n #JUSTERR"},
	{"set -r; echo hi > f; echo rc=$?", "f: restricted: cannot redirect output\nrc=1\n #JUSTERR"},
	{"set -r; exec /bin/echo x; echo rc=$?", "exec: restricted\nrc=1\n #JUSTERR"},
	{"set -r; source /etc/hosts; echo rc=$?", "source: /etc/hosts: restricted\nrc=1\n #JUSTERR"},
	{
		// The refusal is fatal, unlike an ordinary readonly
		// assignment: measured, and it is what makes the restriction a
		// restriction rather than a message.
		"set -r; PATH=/x; echo rc=$?",
		"PATH: readonly variable\nexit status 1 #JUSTERR",
	},
	{"set -r; echo ok; echo rc=$?", "ok\nrc=0\n"},
	{
		// Not an `-o` option name at all: it is reachable as -r, and
		// neither listed nor settable by name. The differential
		// listing test in cmd/koi caught it being listed, which is
		// where the whole `set -o` table is compared to bash's.
		"set -o restricted; echo rc=$?",
		"set: restricted: invalid option name\nrc=2\n #JUSTERR",
	},

	// POSIX mode (#395). koi refused it — honestly, and at the cost of
	// whole suite files: a script opening with `set -o posix` got exit
	// 2 and every later assertion diverged.
	{"set -o posix; echo rc=$?", "rc=0\n"},
	{
		// The option and POSIXLY_CORRECT are two views of one state:
		// setting the option sets the variable, turning it off unsets
		// it, and assigning the variable turns the option on.
		"set -o posix; echo $POSIXLY_CORRECT",
		"y\n",
	},
	{"set -o posix; set +o posix; echo \"[$POSIXLY_CORRECT]\"", "[]\n"},
	{"POSIXLY_CORRECT=1; set -o | grep posix | awk '{print $2}'", "on\n"},
	{
		// POSIX says a temp assignment on a *special* builtin outlives
		// the command, which is why this leaves v set in posix mode
		// and not otherwise.
		`set -o posix; v=1 export v2=2; echo "v=[$v] v2=[$v2]"`,
		"v=[1] v2=[2]\n",
	},
	{`v=1 export v2=2; echo "v=[$v] v2=[$v2]"`, "v=[] v2=[2]\n"},
	{`set -o posix; v=9 echo hi; echo "v=[$v]"`, "hi\nv=[]\n"},

	// A script could not name a job (#397): wait understood only koi's
	// own pid form, so `wait %1` — what a script actually writes —
	// answered "not a child of this shell".
	{"sleep 0.01 & wait %1; echo w=$?", "w=0\n"},
	{"sleep 0.01 & wait %%; echo w=$?", "w=0\n"},
	{"sleep 0.01 & wait -f %1; echo w=$?", "w=0\n"},
	{
		// A jobspec naming nothing is a different error from a pid
		// that is not ours, and carries bash's 127.
		"sleep 0.01 & wait %9; echo w=$?",
		"wait: %9: no such job\nw=127\n #JUSTERR",
	},
	// disown was refused outright, which made the ordinary
	// `cmd & disown` line fatal.
	{"sleep 0.01 & disown; echo d=$?", "d=0\n"},
	{"sleep 0.01 & disown; jobs", ""},
	{"disown; echo d=$?", "disown: current: no such job\nd=1\n #JUSTERR"},

	// Job control is something a script can ask for (#397): `set -m` was
	// refused outright, which made the line fatal in the scripts most
	// likely to write it.
	{"set -m; echo m=$?", "m=0\n"},
	{"fg; echo f=$?", "fg: no job control\nf=1\n #JUSTERR"},
	{"bg; echo b=$?", "bg: no job control\nb=1\n #JUSTERR"},
	{"set -m; fg; echo f=$?", "fg: current: no such job\nf=1\n #JUSTERR"},
	{"set -m; fg %9; echo f=$?", "fg: %9: no such job\nf=1\n #JUSTERR"},
	// Foregrounding a job in a script is waiting for it, and bash's own
	// output for it is the job's command line. The sleeps are what make
	// these deterministic: a job that finishes before `fg` reaches it is
	// a *different* answer below, and CI found that race before the
	// timing here was pinned.
	{"set -m; sleep 0.2 & fg; echo f=$?", "sleep 0.2\nf=0\n"},
	{"set -m; { sleep 0.2; exit 3; } & fg; echo f=$?", "{ sleep 0.2; exit 3; }\nf=3\n"},
	{"set -m; sleep 0.2 & fg %1; echo f=$?", "sleep 0.2\nf=0\n"},
	// A job which has already finished has two further answers, and
	// which one depends on whether its completion has been *reported*:
	// listing a job is what drops it from the table.
	{
		"set -m; { exit 3; } & sleep 0.2; fg; echo f=$?",
		"fg: job has terminated\nf=1\n #JUSTERR",
	},
	{
		// #IGNORE rather than #JUSTERR because the harness's
		// error check reads the *first* line, and here that is the
		// listing. Measured by hand against bash 5.3 on darwin, which
		// answers exactly this; the job mark differs on linux, which is
		// the other reason this one is not confirmed automatically.
		"set -m; { exit 3; } & sleep 0.2; jobs; fg; echo f=$?",
		"[1]+  Exit 3                     { exit 3; }\nfg: current: no such job\nf=1\n #IGNORE",
	},
	// A job already waited for is gone, whatever its number was.
	{"set -m; sleep 0.01 & wait; fg; echo f=$?", "fg: current: no such job\nf=1\n #JUSTERR"},
	// And a finished job is named by what it answered, not by "Done".
	// The job *mark* is stripped because bash spells it per platform —
	// a finished job is still the current job on darwin (`[1]+`) and no
	// longer one on linux (`[1] `) — which CI found and which is not
	// what these two cases are about.
	{
		`{ exit 3; } & sleep 0.2; jobs | sed "s/^\[1\][-+ ]//"`,
		"  Exit 3                     { exit 3; }\n",
	},
	{
		`{ exit 0; } & sleep 0.2; jobs | sed "s/^\[1\][-+ ]//"`,
		"  Done                       { exit 0; }\n",
	},
	// Nothing koi runs in the background is ever stopped, so every job
	// bg can name is already running — the case bash answers 0 for.
	{"set -m; sleep 0.2 & bg; echo b=$?", "bg: job 1 already in background\nb=0\n #JUSTERR"},
	// Job control turns lastpipe off, which is bash's rule and the one
	// observable consequence of `set -m` in koi.
	{`shopt -s lastpipe; echo x | read v; echo "[$v]"`, "[x]\n"},
	{`set -m; shopt -s lastpipe; echo x | read v; echo "[$v]"`, "[]\n"},

	// `${!-word}` is `$!` with a default, not an indirection through
	// `$-` (#277): a `-` after the `!` is the operator. koi read it as
	// the parameter, which left the word after it with nowhere to go
	// and stopped more-exp.tests.
	{`echo "[${!-posparams}]"`, "[posparams]\n"},
	{`echo "[${!-}]"`, "[]\n"},
	{`echo "[${!:-def}]"`, "[def]\n"},
	// Indirection still reads a name, and its own default still works.
	{`v=x; x=hi; echo "${!v}" "${!v-d}"`, "hi hi\n"},
	{`v=nope; echo "[${!v-d}]"`, "[d]\n"},

	// bash's case *toggle*, which koi did not have at all (#277):
	// `${x~}` swaps the case of the first character and `${x~~}` of
	// every one, both filtered by an optional pattern exactly as `^`
	// and `,` are. casemod.tests stopped on the first one.
	{"Z1=oenophile; echo ${Z1~}", "Oenophile\n"},
	{"Z1=oenophile; echo ${Z1~~}", "OENOPHILE\n"},
	{"Z2=OenOphIlE; echo ${Z2~}", "oenOphIlE\n"},
	{"Z2=OenOphIlE; echo ${Z2~~}", "oENoPHiLe\n"},
	{"x=abc; echo ${x~[b]}", "abc\n"},
	{"x=abc; echo ${x~~[bc]}", "aBC\n"},
	{`a=(abc DEF); echo "${a[@]~}"`, "Abc dEF\n"},
	{`declare -A m=([k]=aB); echo "${m[k]~~}"`, "Ab\n"},
	// And the C locale has no case beyond ASCII here either (#470).
	{"export LC_ALL=C; x=ÿab; echo ${x~~}", "ÿAB\n"},

	// koi's parser refused three shapes bash reads and complains about
	// only while evaluating — and because koi parses ahead, refusing
	// them lost the rest of the file rather than the line (#277).

	// A name an arithmetic assignment writes can be *computed*, which
	// is only knowable when the word is expanded.
	{`v=n; echo $(( ${v}ame=5 )); echo "$name"`, "5\n5\n"},
	{`echo $(( $(echo a)=2 )); echo "a=$a"`, "2\na=2\n"},
	// And it can name an element, which used to answer "variable name
	// must not be empty" — a koi bug wearing a diagnosis.
	{`a=(1 2 3); i=1; echo $(( a[i]=9 )); echo "${a[1]}"`, "9\n9\n"},
	{`a=(1 2 3); echo $(( a[1]+=5 )); echo "${a[*]}"`, "7\n1 7 3\n"},
	{`a=(5 6); i=0; echo $(( a[i]++ )); echo "${a[0]}"`, "5\n6\n"},
	{`declare -A m; m[k]=1; echo $(( m[k]+=2 )); echo "${m[k]}"`, "3\n3\n"},
	{`echo $(( a[9]=7 )); echo "${a[9]}"`, "7\n7\n"},

	// An empty slice length is zero rather than a syntax error, and an
	// empty offset is zero when a length follows it.
	{`x=abcdef; echo "[${x:1:}]"`, "[]\n"},
	{`x=abcdef; echo "[${x::}]"`, "[]\n"},
	{`x=abcdef; echo "[${x::3}]"`, "[abc]\n"},
	{
		// A slice with neither half is bash's "bad substitution", which
		// abandons the input unit: in a command string that is the rest
		// of the string, and in a *file* it is only the command — the
		// half cmd/koi's fatality test covers, since a table case is a
		// command string.
		`x=abcdef; echo "[${x:}]"; echo after`,
		"${x:}: bad substitution\nexit status 1 #JUSTERR",
	},

	// A nested expansion is a zsh feature bash does not have, but bash
	// only says so while *expanding* it (#277), so it lands in the same
	// place as the empty slice above: the command is lost, not the file.
	// koi used to refuse it at parse time, which cost the whole file.
	{
		`foo=bar; echo "${${foo}}"; echo after`,
		"${${foo}}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`foo=bar; echo ${${foo}}; echo after`,
		"${${foo}}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		// The diagnostic names the whole expansion, operators and all.
		`foo=bar; echo "${${foo}#b}"; echo after`,
		"${${foo}#b}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`foo=bar; echo "${#${foo}}"; echo after`,
		"${#${foo}}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		// A nested command substitution is not run first; the shape is
		// rejected before anything inside it expands.
		`echo "${$(echo x)}"; echo after`,
		"${$(echo x)}: bad substitution\nexit status 1 #JUSTERR",
	},

	// The same category, reached by a suffix no operator spells rather
	// than by a nested expansion (#602). bash reads the `${…}` to its
	// closing brace and only then refuses it, which loses the command
	// and not the file; koi refused every one of these while *parsing*,
	// and parsing ahead, lost the file.
	{
		`H=1; echo ${H*}; echo after`,
		"${H*}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`set -- a; echo ${#1xyz}; echo after`,
		"${#1xyz}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`set -- a b c; echo "${@*}"; echo after`,
		"${@*}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		// A name this parser cannot read is the same verdict as an
		// operator it cannot read.
		`echo ${1xyz}; echo after`,
		"${1xyz}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`echo ${a b}; echo after`,
		"${a b}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		// A special parameter with a subscript, and a prefix that cannot
		// combine with an operator.
		`set -- a b; echo ${@[@]}; echo after`,
		"${@[@]}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`foo=bar; echo ${#foo:-x}; echo after`,
		"${#foo:-x}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		// The suffix is raw source, so the quotes and the nested brace
		// only serve to find the brace that closes the expansion.
		`echo ${H*"}"}; echo after`,
		`${H*"}"}: bad substitution` + "\nexit status 1 #JUSTERR",
	},
	{
		`echo ${H*{a}}; echo after`,
		"${H*{a}}: bad substitution\nexit status 1 #JUSTERR",
	},

	// A `${x@…}` transform bash has no letter for is the one bad
	// substitution that is *fatal* rather than input-unit abandonment,
	// and it is only a verdict at all when the parameter has a value
	// (#602). Every letter and none were measured, set and unset.
	{
		`V=1; echo ${V@}; echo after`,
		"${V@}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`x=hello; echo ${x@b}; echo after`,
		"${x@b}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`x=hello; echo ${x@nope}; echo after`,
		"${x@nope}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		// An empty value is still a value.
		`x=; echo ${x@b}; echo after`,
		"${x@b}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`set -- a b c; echo "${*@}"; echo after`,
		"${*@}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		// The operator is the source as written, never an expansion of
		// it: a quoted or substituted letter is not the letter.
		`q=Q; x=hello; echo ${x@$q}; echo after`,
		"${x@$q}: bad substitution\nexit status 1 #JUSTERR",
	},
	{
		`x=hello; echo ${x@"Q"}; echo after`,
		`${x@"Q"}: bad substitution` + "\nexit status 1 #JUSTERR",
	},
	{
		// With no value bash never looks at the letter, so this is not
		// an error at all -- which is why refusing it while parsing was
		// strictly wrong rather than merely early.
		`unset x; echo "[${x@nope}]"; echo after`,
		"[]\nafter\n",
	},
	{`unset x; echo "[${x@}]"`, "[]\n"},
	{`set --; echo "[${*@}]"`, "[]\n"},
	{`unset a; echo "[${a[@]@nope}]"`, "[]\n"},
	{`a=(); echo "[${a[@]@nope}]"`, "[]\n"},
	{
		// An unset parameter answers the empty string rather than the
		// two quotes an empty *value* would give.
		`unset x; echo "[${x@Q}]"`,
		"[]\n",
	},
	{`x=; echo "[${x@Q}]"`, "['']\n"},
	{
		// The four transforms that describe the variable rather than its
		// value are asked before the value is, so a declared-but-unset
		// name still answers its flags.
		`declare -i n; echo "[${n@a}]"`,
		"[i]\n",
	},
	{`declare -i n; echo "[${n@b}]"`, "[]\n"},
	{
		// A list transform applies to each element, not to the elements
		// joined.
		`a=(AB cd); echo "[${a[@]@L}]"`,
		"[ab cd]\n",
	},
	{`a=(ab cd); echo "[${a[@]@u}]"`, "[Ab Cd]\n"},
	{`a=(1 2); echo "[${a[@]@nope}]"`, "${a[@]@nope}: bad substitution\nexit status 1 #JUSTERR"},

	// `${x@Q}` quotes unconditionally: bash's sh_quote_reusable, whose
	// callers rely on the answer always being a quoted word, where
	// [syntax.Quote] picks the shortest form and hands a plain word back
	// unchanged (#648).
	{`x=hello; echo "${x@Q}"`, "'hello'\n"},
	{`x=1; echo "${x@Q}"`, "'1'\n"},
	{`x="a b"; echo "${x@Q}"`, "'a b'\n"},
	{`x="it's"; echo "${x@Q}"`, "'it'\\''s'\n"},
	{
		// A lone single quote is bash's other special case, since the
		// general rule would wrap it in two empty quoted spans.
		`x="'"; echo "${x@Q}"`,
		"\\'\n",
	},
	{`x=$'a\tb'; echo "${x@Q}"`, "$'a\\tb'\n"},
	{`x=$'\001'; echo "${x@Q}"`, "$'\\001'\n"},
	{
		// bash's ansic_quote spells escape with a capital E.
		`x=$'\033'; echo "${x@Q}"`,
		"$'\\E'\n",
	},
	{`a=(1 2); echo "${a[@]@Q}"`, "'1' '2'\n"},

	// The four transforms that describe the variable rather than its
	// value answer for the whole variable, not per element (#647).
	{`a=(1 2); echo "${a[@]@A}"`, "declare -a a=([0]=\"1\" [1]=\"2\")\n"},
	{
		// `@a` is the exception: the flags describe the variable and bash
		// repeats them once per element.
		`a=(1 2); echo "${a[@]@a}"`,
		"a a\n",
	},
	{`declare -A m=([k]=v); echo "${m[@]@A}"`, "declare -A m=([k]=\"v\" )\n"},
	{`declare -A m=([k]=v); echo "${m[@]@K}"`, "k \"v\" \n"},
	{`a=(zero one); echo "${a[@]@K}"`, "0 \"zero\" 1 \"one\"\n"},
	{
		// `@k` is `@K`'s list form: keys and values as separate fields.
		`a=(zero one); printf "<%s>" "${a[@]@k}"; echo`,
		"<0><zero><1><one>\n",
	},
	{`set -- a b; echo "${@@A}"`, "set -- 'a' 'b'\n"},
	{
		// With no variable behind it, `@a` answers nothing per element.
		`set -- a b; echo "[${@@a}]"`,
		"[ ]\n",
	},
	{`set -- a b; echo "${@@K}"`, "'a' 'b'\n"},
	{`x=foo; echo "<${x@K}><${x@k}>"`, "<'foo'><'foo'>\n"},
	{
		// Declared but never assigned prints its attributes and no value.
		`declare -lr V; echo "${V@A}"`,
		"declare -rl V\n",
	},
	{`declare -lr V; echo "${V[@]@a}"`, "rl\n"},
	{`declare -alr W; echo "${W[@]@A}"`, "declare -arl W\n"},
	{`B=(); echo "[${B[@]@A}]"`, "[declare -a B=()]\n"},
	{
		// An empty array has no element zero, so the scalar form has no
		// value to print even though the variable was assigned.
		`declare -ia f=(); echo "${f@A}"`,
		"declare -ai f\n",
	},
	{
		// A nameref answers about its target, and names it.
		`declare -ri n=5; declare -n r=n; echo "${r@a}"`,
		"ir\n",
	},
	{`declare -ri n=5; declare -n r=n; echo "${r@A}"`, "declare -ir n='5'\n"},

	// An unquoted `&` in a replacement is the text that matched, which is
	// bash's patsub_replacement and on by default since 5.2 (#643).
	{`v=aabb; echo "${v/aa/[&]}"`, "[aa]bb\n"},
	{`v=aabb; echo "${v//b/<&>}"`, "aa<b><b>\n"},
	{`v=aabb; echo "${v/#aa/[&]}"`, "[aa]bb\n"},
	{`v=aabb; echo "${v/%bb/[&]}"`, "aa[bb]\n"},
	{
		// An `&` that arrives from an expansion is unquoted too, so it is
		// the match; the same expansion in double quotes is not.
		`v=aabb; r="[&]"; echo "${v/aa/$r}"`,
		"[aa]bb\n",
	},
	{`v=aabb; r="[&]"; echo "${v/aa/"$r"}"`, "[&]bb\n"},
	{`v=aabb; echo "${v/aa/\&}"`, "&bb\n"},
	{`v=aabb; echo "${v/aa/"&"}"`, "&bb\n"},
	{
		// An escaped ampersand in a *value* loses its backslash too, by
		// the other route: the replacement is rewritten per match, and
		// that pass is what removes it.
		`v=aabb; s="\&"; echo "${v/aa/$s}"`,
		"&bb\n",
	},
	{
		// With no `&` and no escape to act on, the replacement is used
		// exactly as it expanded — backslash included.
		`v=aabb; s="a\b"; echo "${v/aa/$s}"`,
		"a\\bbb\n",
	},
	{`v=aabb; echo "${v/aa/a\\b}"`, "a\\bbb\n"},
	{`v=aabb; echo ${v/aa/a\b}`, "abbb\n"},
	{
		// An anchored empty pattern is sed's `^` and `$`, where the match
		// is the empty string.
		`v=aabb; echo "${v/#/P&}"`,
		"Paabb\n",
	},
	{`v=aabb; echo "${v/%/&S}"`, "aabbS\n"},
	{`e=; echo "[${e/#/[&]}]"`, "[[]]\n"},
	{`v=aabb; echo "${v//?/[&]}"`, "[a][a][b][b]\n"},
	{`v=aabb; echo "${v/aa/&}"`, "aabb\n"},
	{`a=(ab cd); echo "${a[@]/?/[&]}"`, "[a]b [c]d\n"},
	{
		// The option is koi's to hold both ways now that there is a
		// behaviour behind it (#575's rule).
		`shopt -u patsub_replacement; v=aabb; echo "${v/aa/[&]}"`,
		"[&]bb\n",
	},
	{`shopt -p patsub_replacement`, "shopt -s patsub_replacement\n"},
	{
		// `shopt -p` answers 1 for an option that is off, so the status
		// is the script's.
		`shopt -u patsub_replacement; shopt -p patsub_replacement`,
		"shopt -u patsub_replacement\nexit status 1",
	},

	// `${#` followed by an operator and nothing else is a shape bash
	// reads and refuses while expanding, where the same operator with a
	// word is an ordinary expansion of the parameter count (#672).
	{`set -- a b; echo "${#/2/X}"`, "X\n"},
	{`set -- a b; echo "${#%%}"`, "2\n"},
	{`set -- a b; echo "${#//}"`, "2\n"},
	{`set -- a b; echo "${#:+x}"`, "x\n"},
	{`set -- a b; echo "${#=x}"`, "2\n"},
	{`set -- a b; echo "${#//a/b}"`, "2\n"},
	{
		// `-` and `?` are parameter names, so these are the length of
		// `$-` and `$?` rather than an operator after the count.
		`set -- a b; echo "${#?}"`,
		"1\n",
	},
	{`set -- a b; echo "${#/}"`, "${#/}: bad substitution\nexit status 1 #JUSTERR"},
	{`set -- a b; echo "${#%}"`, "${#%}: bad substitution\nexit status 1 #JUSTERR"},
	{`set -- a b; echo "${#=}"`, "${#=}: bad substitution\nexit status 1 #JUSTERR"},
	{`set -- a b; echo "${#+}"`, "${#+}: bad substitution\nexit status 1 #JUSTERR"},
	{
		// A case-conversion operator is refused whatever follows it,
		// since bash reads its character into the name.
		`set -- a b; echo "${#^}"`,
		"${#^}: bad substitution\nexit status 1 #JUSTERR",
	},
	{`set -- a b; echo "${#,a}"`, "${#,a}: bad substitution\nexit status 1 #JUSTERR"},
	{
		// It costs the line rather than the script, which is #469's
		// category: the statements sharing the line never run and the
		// next line does. The diagnostic itself is out of the way
		// because bash names `bash: line N:` for a script on standard
		// input where koi names nothing (#120), so what is compared here
		// is which commands ran.
		"set -- a b\nexec 2>/dev/null\necho \"${#+}\"; echo same\necho next",
		"next\n",
	},

	// A replacement can be anchored to the start or the end of the value
	// (#636): `${v/#pat/rep}` and `${v/%pat/rep}`, which koi read as
	// part of the pattern, so `${path/#$HOME/\~}` and
	// `${name/%.txt/.md}` returned their input untouched and said
	// nothing.
	{
		`v=aabbaa; echo "${v/#aa/X}"`,
		"Xbbaa\n",
	},
	{
		`v=aabbaa; echo "${v/%aa/Y}"`,
		"aabbY\n",
	},
	{
		// The anchor is read even when nothing matches there, which is
		// what tells a dropped anchor from an honoured one.
		`v=aabbaa; echo "${v/#bb/X}"`,
		"aabbaa\n",
	},
	{
		// An anchor with no pattern is a pure prepend or append.
		`v=aabbaa; echo "${v/#/P}"`,
		"Paabbaa\n",
	},
	{
		`v=aabbaa; echo "${v/%/S}"`,
		"aabbaaS\n",
	},
	{
		// No replacement is a deletion at the anchor.
		`v=aabbaa; echo "${v/#aa}"`,
		"bbaa\n",
	},
	{
		`v=aabbaa; echo "${v/%aa}"`,
		"aabb\n",
	},
	{
		// The match is the longest one at the anchor, not the shortest.
		`v=aabbaa; echo "${v/#a*b/X}"`,
		"Xaa\n",
	},
	{
		// Anchored at the end it is the earliest start that reaches it.
		`v=aabbaa; echo "${v/%b*a/X}"`,
		"aaX\n",
	},
	{
		`v=aabbaa; echo "${v/#?/X}"`,
		"Xabbaa\n",
	},
	{
		// The double-slash form has no anchor: `#` is an ordinary
		// character there, so this replaces nothing at all…
		`v=aabbaa; echo "${v//#aa/X}"`,
		"aabbaa\n",
	},
	{
		// …and matches a literal `#` where the value has one.
		`v="#a#a"; echo "${v//#a/X}"`,
		"XX\n",
	},
	{
		`v="#aabb"; echo "${v/#aa/X}"`,
		"#aabb\n",
	},
	{
		// Escaped or quoted, it is the literal `#` rather than an
		// anchor — the three spellings a script uses to say so.
		`v="#aabb"; echo "${v/\#aa/X}"`,
		"Xbb\n",
	},
	{
		`v="#aabb"; echo "${v/"#"aa/X}"`,
		"Xbb\n",
	},
	{
		`v='#aabb'; echo "${v/'#'aa/X}"`,
		"Xbb\n",
	},
	{
		// bash reads the anchor *after* expanding the pattern word, so
		// one arriving from a variable anchors too…
		`v=aabbaa; p="#aa"; echo "${v/$p/X}"`,
		"Xbbaa\n",
	},
	{
		// …which is only visible in a case where the anchored pattern
		// then fails to match.
		`v="#ppbb"; p="#pp"; echo "${v/$p/X}"`,
		"#ppbb\n",
	},
	{
		`v="#ppbb"; p="#pp"; echo "${v/#"$p"/X}"`,
		"Xbb\n",
	},
	{
		// Every element, which is what makes a list of names the shape
		// most often affected.
		`a=(aa1 aa2); echo "${a[@]/#aa/X}"`,
		"X1 X2\n",
	},
	{
		`a=(x y); echo "${a[@]/#/P}"`,
		"Px Py\n",
	},
	{
		`a=(x y); echo "${a[@]/%/S}"`,
		"xS yS\n",
	},
	{
		`set -- -a -b; echo "${@/#-/+}"`,
		"+a +b\n",
	},
	{
		`declare -A m=([k]=aav); echo "${m[k]/#aa/X}"`,
		"Xv\n",
	},
	{
		// The two idioms the issue was reported for.
		`v=note.txt; echo "${v/%.txt/.md}"`,
		"note.md\n",
	},
	{
		`h=/home/me; p=/home/me/src; echo "${p/#$h/\~}"`,
		"~/src\n",
	},

	// The same rule reaches every operator that counts characters, not
	// only `?` and ${#x} (#470): a slice, a pattern removal, a
	// replacement and a case conversion are all byte-wise there, and
	// the C locale has no case beyond ASCII.
	{`export LC_ALL=C; a=абв; echo "${a:0:2}"`, "\xd0\xb0\n"},
	{`export LC_ALL=en_US.UTF-8; a=абв; echo "${a:0:2}"`, "аб\n"},
	{`export LC_ALL=C; a=абв; echo "${a#?}"`, "\xb0бв\n"},
	{`export LC_ALL=en_US.UTF-8; a=абв; echo "${a#?}"`, "бв\n"},
	{`export LC_ALL=C; a=абв; echo "${a%?}"`, "аб\xd0\n"},
	{`export LC_ALL=C; a=абв; echo "${a//?/x}"`, "xxxxxx\n"},
	{`export LC_ALL=en_US.UTF-8; a=абв; echo "${a//?/x}"`, "xxx\n"},
	{`export LC_ALL=C; a=абв; echo "${a/б/Y}"`, "аYв\n"},
	// An anchored replacement (#636) is byte-wise there too, since it
	// runs through the same conversion as the plain one.
	{`export LC_ALL=C; a=áb; echo "${a/#?/X}"`, "X\xa1b\n"},
	{`export LC_ALL=en_US.UTF-8; a=áb; echo "${a/#?/X}"`, "Xb\n"},
	{`export LC_ALL=C; a=aÿb; echo "${a^^}"`, "AÿB\n"},
	{`export LC_ALL=en_US.UTF-8; a=aÿb; echo "${a^^}"`, "AŸB\n"},

	// In the C locale a character is a byte (#470): koi was UTF-8
	// everywhere, so a script that sets LC_ALL=C to make its own output
	// stable got UTF-8 answers anyway.
	{
		`export LC_ALL=C; a=$'\316\261'; case $a in ?) echo one;; ??) echo two;; esac`,
		"two\n",
	},
	{
		`export LC_ALL=en_US.UTF-8; a=$'\316\261'; case $a in ?) echo one;; ??) echo two;; esac`,
		"one\n",
	},
	{`export LC_ALL=C; a=$'\316\261'; echo "${#a}"`, "2\n"},
	{`export LC_ALL=en_US.UTF-8; a=$'\316\261'; echo "${#a}"`, "1\n"},
	{
		// C.UTF-8 is a C locale by name and a UTF-8 one by encoding,
		// and it is the encoding this is about.
		`export LC_ALL=C.UTF-8; a=$'\316\261'; echo "${#a}"`,
		"1\n",
	},

	// Backslash-newline is removed by the backquote-level scan before
	// the inner text is parsed — even inside single quotes, which are
	// otherwise literal (#423). The same string outside backquotes
	// keeps both characters, which is what makes this the backquote's
	// rule rather than the quote's.
	{"echo `echo 'foo\\\nbar'`", "foobar\n"},
	{"echo 'foo\\\nbar'", "foo\\\nbar\n"},
	{"echo `echo \\`echo 'a\\\nb'\\``", "ab\n"},
	// The same decision at command position (#277): `((` opens an
	// arithmetic command only when its parens close together, and is
	// two nested subshells otherwise — which is the ordinary shape of
	// `((cd dir); cmd)` and `((a) && (b))`, not just of bash's suite.
	{"((echo sh_a); (echo sh_b))", "sh_a\nsh_b\n"},
	{"((echo sh_a) && (echo sh_b))", "sh_a\nsh_b\n"},
	{"((true ) ); echo rc=$?", "rc=0\n"},
	{"(( 1+1 )); echo rc=$?", "rc=0\n"},
	{"(( 1 > 2 )); echo rc=$?", "rc=1\n"},
	{"(( (1+2) )); echo rc=$?", "rc=0\n"},
	{"x=5; (( x++ )); echo $x", "6\n"},
	{"for ((i=0;i<2;i++)); do echo $i; done", "0\n1\n"},

	// `$((` is arithmetic only when the two parens close together;
	// otherwise it is a command substitution whose first command is a
	// subshell (#424). bash decides the same way — by where the inner
	// paren closes — rather than by parsing and backtracking.
	{"echo $((echo sh_a);(echo sh_b))", "sh_a sh_b\n"},
	{"echo $((1+2))", "3\n"},
	{"echo $(( (1+2) ))", "3\n"},
	{"x=3; echo $((x++))", "3\n"},
	{"echo $((echo hi) )", "hi\n"},
	{"echo [$((echo hi); echo there)]", "[hi there]\n"},
	// An empty arithmetic expansion is zero rather than an error, in
	// every spelling; `(( ))` is zero too, so its status is 1.
	{"echo $(())", "0\n"},
	{"echo $(( ))", "0\n"},
	{"x=$(()); echo \"[$x]\"", "[0]\n"},
	{"echo $[]", "0\n"},
	{"(( )); echo rc=$?", "rc=1\n"},
	{"if (( )); then echo t; else echo f; fi", "f\n"},

	// Backslashes inside a ${x+word} (#541). The closing brace is
	// escapable there and nowhere else, because an unescaped one would
	// end the expansion; every other escape follows the quoting around
	// the expansion rather than the word's own position.
	{`x=y; echo "${x+\}z}"`, "}z\n"},
	{`echo "\}"`, "\\}\n"},
	{`x=y; echo "${x+\{z}"`, "\\{z\n"},
	{`x=y; echo "${x+a\bz}"`, "a\\bz\n"},
	{`x=y; echo "${x+a\"z}"`, "a\"z\n"},
	// The word's escapes still quote, so an escaped space is not a
	// field boundary while a bare one is.
	{`x=y; printf '<%s> ' ${x+a\ b}; echo`, "<a b> \n"},
	{`x=y; printf '<%s> ' ${x+a b}; echo`, "<a> <b> \n"},
	{`unset w; printf '<%s> ' ${w-a\ b} x ${w-c\ d}; echo`, "<a b> <x> <c d> \n"},
	// The two assignment operators are the exception in both halves:
	// what comes back is the variable they just wrote, so quote removal
	// has already happened and the value splits...
	{`unset a; printf '<%s> ' ${a:=x\ y}; echo "[$a]"`, "<x> <y> [x y]\n"},
	// ...while inside double quotes the word is read as the quotes say,
	// so the backslash is part of the value that gets assigned.
	{`unset v; printf '<%s> ' "${v=a\ b}" "${v=c\ d}"; echo`, "<a\\ b> <a\\ b> \n"},

	// declare -F
	{
		`f() { :; }; declare -F f; echo "st=$?"`,
		"f\nst=0\n",
	},
	{
		`declare -F nope; echo "st=$?"`,
		"st=1\n",
	},
	{
		// a missing name does not stop the ones which follow
		`f() { :; }; declare -F f nope; echo "st=$?"`,
		"f\nst=1\n",
	},
	{
		// with no names it lists every function, sorted
		`zeta() { :; }; alpha() { :; }; mid() { :; }; declare -F`,
		"declare -f alpha\ndeclare -f mid\ndeclare -f zeta\n",
	},
	{
		`declare -F; echo "st=$?"`,
		"st=0\n",
	},
	{
		`f() { :; }; typeset -F f`,
		"f\n",
	},
	{
		// the flag is the interpreter's, so it survives a re-parse
		`f() { :; }; eval "declare -F f"; echo "st=$?"`,
		"f\nst=0\n",
	},

	// declare -f and declare -p
	{
		`f() { echo hello; }; declare -f f`,
		"f () \n{ \n    echo hello\n}\n",
	},
	{
		`declare -f nonexistent 2>/dev/null; echo "exit: $?"`,
		"exit: 1\n",
	},
	{
		`f() { echo hello; }; declare -f f >/dev/null && echo "f exists"`,
		"f exists\n",
	},
	{
		`a=hello; declare -p a`,
		"declare -- a=\"hello\"\n",
	},
	{
		`declare -a arr=(1 2 3); declare -p arr`,
		"declare -a arr=([0]=\"1\" [1]=\"2\" [2]=\"3\")\n",
	},
	{
		`export e=1; declare -p e`,
		"declare -x e=\"1\"\n",
	},
	{
		`readonly c=immutable; declare -p c`,
		"declare -r c=\"immutable\"\n",
	},
	{
		`declare -p nonexistent 2>/dev/null; echo "exit: $?"`,
		"exit: 1\n",
	},

	// if
	{
		"if true; then echo foo; fi",
		"foo\n",
	},
	{
		"if false; then echo foo; fi",
		"",
	},
	{
		"if GOSH_CMD=print_fail $GOSH_PROG; then echo foo; fi",
		"exec fail\n",
	},
	{
		"if true; then echo foo; else echo bar; fi",
		"foo\n",
	},
	{
		"if false; then echo foo; else echo bar; fi",
		"bar\n",
	},
	{
		"if true; then false; fi",
		"exit status 1",
	},
	{
		"if false; then :; else false; fi",
		"exit status 1",
	},
	{
		"if false; then :; elif true; then echo foo; fi",
		"foo\n",
	},
	{
		"if false; then :; elif false; then :; elif true; then echo foo; fi",
		"foo\n",
	},
	{
		"if false; then :; elif false; then :; else echo foo; fi",
		"foo\n",
	},

	// while
	{
		"while false; do echo foo; done",
		"",
	},
	{
		"while GOSH_CMD=print_fail $GOSH_PROG; do echo foo; done",
		"exec fail\n",
	},
	{
		"while true; do exit 1; done",
		"exit status 1",
	},
	{
		"while true; do break; done",
		"",
	},
	{
		"while true; do while true; do break 2; done; done",
		"",
	},

	// until
	{
		"until true; do echo foo; done",
		"",
	},
	{
		"until false; do exit 1; done",
		"exit status 1",
	},
	{
		"until false; do break; done",
		"",
	},

	// for
	{
		"for i in 1 2 3; do echo $i; done",
		"1\n2\n3\n",
	},
	{
		"for i in 1 2 3; do echo $i; exit; done",
		"1\n",
	},
	{
		"for i in 1 2 3; do echo $i; false; done",
		"1\n2\n3\nexit status 1",
	},
	{
		"for i in 1 2 3; do echo $i; break; done",
		"1\n",
	},
	{
		"for i in 1 2 3; do echo $i; continue; echo foo; done",
		"1\n2\n3\n",
	},
	{
		"for i in 1 2; do for j in a b; do echo $i $j; continue 2; done; done",
		"1 a\n2 a\n",
	},
	{
		"for ((i=0; i<3; i++)); do echo $i; done",
		"0\n1\n2\n",
	},
	// for, with missing Init, Cond, Post
	{
		"i=0; for ((; i<3; i++)); do echo $i; done",
		"0\n1\n2\n",
	},
	{
		"for ((i=0;; i++)); do if [ $i -ge 3 ]; then break; fi; echo $i; done",
		"0\n1\n2\n",
	},
	{
		"for ((i=0; i<3;)); do echo $i; i=$((i+1)); done",
		"0\n1\n2\n",
	},
	{
		"i=0; for ((;;)); do if [ $i -ge 3 ]; then break; fi; echo $i; i=$((i+1)); done",
		"0\n1\n2\n",
	},
	// TODO: uncomment once expandEnv.Set starts returning errors
	// {
	// 	"readonly i; for ((i=0; i<3; i++)); do echo $i; done",
	// 	"0\n1\n2\n",
	// },
	{
		"for ((i=5; i>0; i--)); do echo $i; break; done",
		"5\n",
	},
	{
		"for i in 1 2; do for j in a b; do echo $i $j; done; break; done",
		"1 a\n1 b\n",
	},
	{
		"for i in 1 2 3; do :; done; echo $i",
		"3\n",
	},
	{
		"for ((i=0; i<3; i++)); do :; done; echo $i",
		"3\n",
	},
	{
		"set -- a 'b c'; for i in; do echo $i; done",
		"",
	},
	{
		"set -- a 'b c'; for i; do echo $i; done",
		"a\nb c\n",
	},

	// block
	{
		"{ echo foo; }",
		"foo\n",
	},
	{
		"{ false; }",
		"exit status 1",
	},

	// subshell
	{
		"(echo foo)",
		"foo\n",
	},
	{
		"(false)",
		"exit status 1",
	},
	{
		"(exit 1)",
		"exit status 1",
	},
	{
		"(false); echo foo",
		"foo\n",
	},
	{
		"(exit 0); echo foo",
		"foo\n",
	},
	{
		"(exit 1); echo foo",
		"foo\n",
	},
	{
		"(foo=bar; echo $foo); echo $foo",
		"bar\n\n",
	},
	{
		"(echo() { printf 'bar\n'; }; echo); echo",
		"bar\n\n",
	},
	{
		"unset INTERP_GLOBAL & echo $INTERP_GLOBAL",
		"value\n",
	},
	{
		"(fn() { :; }) & pwd >/dev/null",
		"",
	},
	{
		"x[0]=x; (echo ${x[0]}; x[0]=y; echo ${x[0]}); echo ${x[0]}",
		"x\ny\nx\n",
	},
	{
		`x[3]=x; (x[3]=y); echo ${x[3]}`,
		"x\n",
	},
	{
		"shopt -s expand_aliases; alias f='echo x'\nf\n(f\nalias f='echo y'\neval f\n)\nf\n",
		"x\nx\ny\nx\n",
	},
	{
		"set -- a; echo $1; (echo $1; set -- b; echo $1); echo $1",
		"a\na\nb\na\n",
	},
	{"false; ( echo $? )", "1\n"},

	// cd/pwd
	{"[[ fo~ == 'fo~' ]]", ""},
	{`[[ 'ab\c' == *\\* ]]`, ""},
	{`[[ foo/bar == foo* ]]`, ""},
	{"[[ a == [ab ]]", "exit status 1"},
	{`HOME='/*'; echo ~; echo "$HOME"`, "/*\n/*\n"},
	{`test -d ~`, ""},
	{
		`for flag in b c d e f g h k L p r s S u w x; do test -$flag ""; echo -n "$flag$? "; done`,
		`b1 c1 d1 e1 f1 g1 h1 k1 L1 p1 r1 s1 S1 u1 w1 x1 `,
	},
	{`foo=~; test -d $foo`, ""},
	{`foo=~; test -d "$foo"`, ""},
	{`foo='~'; test -d $foo`, "exit status 1"},
	{`foo='~'; [ $foo == '~' ]`, ""},
	{
		`[[ ~ == "$HOME" ]] && [[ ~/foo == "$HOME/foo" ]]`,
		"",
	},
	{
		`HOME=$PWD/home; mkdir home; touch home/f; [[ -e ~/f ]]`,
		"",
	},
	{
		`HOME=$PWD/home; mkdir home; touch home/f; [[ ~/f -ef $HOME/f ]]`,
		"",
	},
	{
		"[[ ~noexist == '~noexist' ]]",
		"",
	},
	{
		`w="$HOME"; cd; [[ $PWD == "$w" ]]`,
		"",
	},
	{
		`cd ''`,
		"cd: null directory\nexit status 1 #JUSTERR",
	},
	{
		`HOME=/foo; echo $HOME`,
		"/foo\n",
	},
	{
		"cd noexist",
		"cd: noexist: No such file or directory\nexit status 1 #JUSTERR",
	},
	{
		"mkdir -p a/b && cd a && cd b && cd ../..",
		"",
	},
	{
		// A file is not a missing directory, and bash says which it is.
		">a && cd a",
		"cd: a: Not a directory\nexit status 1 #JUSTERR",
	},
	{
		`[[ $PWD == "$(pwd)" ]]`,
		"",
	},
	{
		"PWD=changed; [[ $PWD == changed ]]",
		"",
	},
	{
		"PWD=changed; mkdir a; cd a; [[ $PWD == changed ]]",
		"exit status 1",
	},
	{
		`mkdir %s; old="$PWD"; cd %s; [[ $old == "$PWD" ]]`,
		"exit status 1",
	},
	{
		`old="$PWD"; mkdir a; cd a; cd ..; [[ $old == "$PWD" ]]`,
		"",
	},
	{
		`[[ $PWD == "$OLDPWD" ]]`,
		"exit status 1",
	},
	{
		`old="$PWD"; mkdir a; cd a; [[ $old == "$OLDPWD" ]]`,
		"",
	},
	{
		`mkdir a; ln -s a b; [[ $(cd a && pwd) == "$(cd b && pwd)" ]]; echo $?`,
		"1\n",
	},
	{
		`pwd -a`,
		"invalid option: \"-a\"\nexit status 2 #JUSTERR",
	},
	{
		`pwd -L -P -a`,
		"invalid option: \"-a\"\nexit status 2 #JUSTERR",
	},
	{
		`mkdir a; ln -s a b; [[ "$(cd a && pwd -P)" == "$(cd b && pwd -P)" ]]`,
		"",
	},
	{
		`mkdir a; ln -s a b; [[ "$(cd a && pwd -P)" == "$(cd b && pwd -L)" ]]; echo $?`,
		"1\n",
	},
	{
		`orig="$PWD"; mkdir a; cd a; cd - >/dev/null; [[ "$PWD" == "$orig" ]]`,
		"",
	},
	{
		`orig="$PWD"; mkdir a; cd a; [[ $(cd -) == "$orig" ]]`,
		"",
	},

	// dirs/pushd/popd
	{"set -- $(dirs); echo $# ${#DIRSTACK[@]}", "1 1\n"},
	{"pushd", "pushd: no other directory\nexit status 1 #JUSTERR"},
	{"pushd -n", ""},
	{"pushd foo bar", "pushd: too many arguments\nexit status 1 #JUSTERR"},
	// `--` ends the options in all three, which koi read as an operand:
	// as a stack index for dirs, and as a directory name for the other
	// two (#604). dirs and popd ignore whatever follows it; pushd reads
	// it as a *directory*, so `pushd -- +1` is not a rotation.
	{"mkdir a; pushd a >/dev/null; set -- $(dirs --); echo $#", "2\n"},
	{"mkdir a; pushd a >/dev/null; set -- $(dirs -- +1); echo $#", "2\n"},
	{"mkdir a; pushd a >/dev/null; pushd -- +1", "pushd: +1: No such file or directory\nexit status 1 #JUSTERR"},
	{"mkdir a; pushd a >/dev/null; popd -- +8 >/dev/null; set -- $(dirs); echo $#", "1\n"},
	{"mkdir a; pushd a >/dev/null; pushd -- >/dev/null; set -- $(dirs); echo $#", "2\n"},
	// A signed word that is not a number is an "invalid number" with a
	// usage line, which koi answered three different wrong ways.
	{"dirs -x", "dirs: -x: invalid number\ndirs: usage: dirs [-clpv] [+N] [-N]\nexit status 2 #JUSTERR"},
	{"dirs -lp", "dirs: -lp: invalid number\ndirs: usage: dirs [-clpv] [+N] [-N]\nexit status 2 #JUSTERR"},
	{"pushd -x", "pushd: -x: invalid number\npushd: usage: pushd [-n] [+N | -N | dir]\nexit status 2 #JUSTERR"},
	{"popd -x", "popd: -x: invalid number\npopd: usage: popd [-n] [+N | -N]\nexit status 2 #JUSTERR"},
	{"popd dir", "popd: dir: invalid argument\npopd: usage: popd [-n] [+N | -N]\nexit status 2 #JUSTERR"},
	// The out-of-range complaint prints the number bash parsed, sign
	// dropped.
	{"dirs +8", "dirs: 8: directory stack index out of range\nexit status 1 #JUSTERR"},
	// popd reads the first operand and ignores the rest rather than
	// calling it too many arguments.
	{"mkdir a b; pushd a >/dev/null; pushd ../b >/dev/null; popd +1 +1 >/dev/null; set -- $(dirs); echo $#", "2\n"},
	// An empty operand is not "no operand" in any of the three, and it
	// is a different thing in each: dirs calls it an invalid option,
	// pushd refuses it as a null directory when it would move, and popd
	// reads it as `-0` — the entry at the *bottom*. koi indexed byte
	// zero of it and took the shell down with a panic.
	{`dirs ""`, "dirs: : invalid option\ndirs: usage: dirs [-clpv] [+N] [-N]\nexit status 2 #JUSTERR"},
	{`pushd ""`, "pushd: null directory\nexit status 1 #JUSTERR"},
	{`mkdir a; pushd a >/dev/null; pushd -n "" >/dev/null; echo ${#DIRSTACK[@]}`, "3\n"},
	{
		// The stack has to be three deep for this to say anything: with
		// two entries, dropping the bottom and dropping the top both
		// leave one. `basename` names which one went.
		`mkdir a b; pushd a >/dev/null; pushd ../b >/dev/null; popd "" >/dev/null
set -- $(dirs); echo "$#:$(basename $1):$(basename $2)"`,
		"2:b:a\n",
	},
	{
		// The control: a bare popd drops the *top*, so the answer is
		// different in both fields. Without this the case above passes
		// under a popd that ignores the operand entirely.
		`mkdir a b; pushd a >/dev/null; pushd ../b >/dev/null; popd >/dev/null
set -- $(dirs); echo "$#:$(basename $1)"`,
		"2:a\n",
	},

	{"pushd does-not-exist; set -- $(dirs); echo $#", "pushd: does-not-exist: No such file or directory\n1\n #IGNORE"},
	{"mkdir a; pushd a >/dev/null; set -- $(dirs); echo $#", "2\n"},
	{"mkdir a; set -- $(pushd a); echo $#", "2\n"},
	{
		`mkdir a; pushd a >/dev/null; set -- $(dirs); [[ $1 == "$HOME" ]]`,
		"exit status 1",
	},
	{
		`mkdir a; pushd a >/dev/null; [[ ${DIRSTACK[0]} == "$HOME" ]]`,
		"exit status 1",
	},
	{
		`old=$(dirs); mkdir a; pushd a >/dev/null; pushd >/dev/null; set -- $(dirs); [[ $1 == "$old" ]]`,
		"",
	},
	{
		`old=$(dirs); mkdir a; pushd a >/dev/null; pushd -n >/dev/null; set -- $(dirs); [[ $1 == "$old" ]]`,
		"exit status 1",
	},
	{
		"mkdir a; pushd a >/dev/null; pushd >/dev/null; rm -r a; pushd",
		"pushd: ABS_PATH_A: No such file or directory\nexit status 1 #JUSTERR",
	},
	{
		`old=$(dirs); mkdir a; pushd -n a >/dev/null; set -- $(dirs); [[ $1 == "$old" ]]`,
		"",
	},
	{
		`old=$(dirs); mkdir a; pushd -n a >/dev/null; pushd >/dev/null; set -- $(dirs); [[ $1 == "$old" ]]`,
		"exit status 1",
	},
	{"popd", "popd: directory stack empty\nexit status 1 #JUSTERR"},
	{"popd -n", "popd: directory stack empty\nexit status 1 #JUSTERR"},
	{"popd foo", "popd: foo: invalid argument\npopd: usage: popd [-n] [+N | -N]\nexit status 2 #JUSTERR"},
	{"old=$(dirs); mkdir a; pushd a >/dev/null; set -- $(popd); echo $#", "1\n"},
	{
		`old=$(dirs); mkdir a; pushd a >/dev/null; popd >/dev/null; [[ $(dirs) == "$old" ]]`,
		"",
	},
	{"old=$(dirs); mkdir a; pushd a >/dev/null; set -- $(popd -n); echo $#", "1\n"},
	{
		`old=$(dirs); mkdir a; pushd a >/dev/null; popd -n >/dev/null; [[ $(dirs) == "$old" ]]`,
		"exit status 1",
	},
	{
		"mkdir a; pushd a >/dev/null; pushd >/dev/null; rm -r a; popd",
		"popd: ABS_PATH_A: No such file or directory\nexit status 1 #JUSTERR",
	},

	// binary cmd
	{
		"true && echo foo || echo bar",
		"foo\n",
	},
	{
		"false && echo foo || echo bar",
		"bar\n",
	},

	// func
	{
		"foo() { echo bar; }; foo",
		"bar\n",
	},
	{
		"foo() { echo $1; }; foo",
		"\n",
	},
	{
		"foo() { echo $1; }; foo a b",
		"a\n",
	},
	{
		"foo() { echo $1; bar c d; echo $2; }; bar() { echo $2; }; foo a b",
		"a\nd\nb\n",
	},
	{
		`foo() { echo $#; }; foo; foo 1 2 3; foo "a b"; echo $#`,
		"0\n3\n1\n0\n",
	},
	{
		`foo() { for a in $*; do echo "$a"; done }; foo 'a  1' 'b  2'`,
		"a\n1\nb\n2\n",
	},
	{
		`foo() { for a in "$*"; do echo "$a"; done }; foo 'a  1' 'b  2'`,
		"a  1 b  2\n",
	},
	{
		`foo() { for a in "foo$*"; do echo "$a"; done }; foo 'a  1' 'b  2'`,
		"fooa  1 b  2\n",
	},
	{
		`foo() { for a in $@; do echo "$a"; done }; foo 'a  1' 'b  2'`,
		"a\n1\nb\n2\n",
	},
	{
		`foo() { for a in "$@"; do echo "$a"; done }; foo 'a  1' 'b  2'`,
		"a  1\nb  2\n",
	},

	// alias (note the input newlines)
	{
		"alias foo; alias foo=echo; alias foo; alias foo=; alias foo",
		// bash's wording, and its status — koi answered 0 (#407).
		"alias: foo: not found\nalias foo='echo'\nalias foo=''\n #JUSTERR",
	},
	{
		"shopt -s expand_aliases; alias foo=echo\nfoo foo; foo bar",
		"foo\nbar\n",
	},
	{
		"shopt -s expand_aliases; alias true=echo\ntrue foo; unalias true\ntrue bar",
		"foo\n",
	},
	{
		"shopt -s expand_aliases; alias echo='echo a'\necho b c",
		"a b c\n",
	},
	{
		"shopt -s expand_aliases; alias foo='echo '\nfoo foo; foo bar",
		"echo\nbar\n",
	},

	// case
	{
		"case b in x) echo foo ;; a|b) echo bar ;; esac",
		"bar\n",
	},
	{
		// ';&' runs the next item's statements without testing its patterns
		"case a in a) echo A ;& b) echo B ;; esac",
		"A\nB\n",
	},
	{
		"case a in a) echo A ;& z) echo Z ;; esac",
		"A\nZ\n",
	},
	{
		"case a in a) ;& b) echo B ;; esac",
		"B\n",
	},
	{
		// ';;&' carries on testing the patterns which follow
		"case a in a) echo A ;;& a*) echo A2 ;; esac",
		"A\nA2\n",
	},
	{
		"case a in a) echo A ;;& z) echo Z ;; esac",
		"A\n",
	},
	{
		"case ab in a*) echo 1 ;;& *b) echo 2 ;;& ab) echo 3 ;; esac",
		"1\n2\n3\n",
	},
	{
		"case a in z) echo Z ;;& a) echo A ;; esac",
		"A\n",
	},
	{
		// the two mix, and a plain ';;' still stops
		"case a in a) echo 1 ;& z) echo 2 ;;& *) echo 3 ;; esac",
		"1\n2\n3\n",
	},
	{
		"case a in a) echo A ;; a*) echo A2 ;; esac",
		"A\n",
	},
	{
		// the status is that of the last body which ran
		`case a in a) false ;& b) true ;; esac; echo "st=$?"`,
		"st=0\n",
	},
	{
		`case a in a) true ;& b) false ;; esac; echo "st=$?"`,
		"st=1\n",
	},
	{
		"case b in x) echo foo ;; y|z) echo bar ;; esac",
		"",
	},
	{
		"case foo in bar) echo foo ;; *) echo bar ;; esac",
		"bar\n",
	},
	{
		"case foo in *o*) echo bar ;; esac",
		"bar\n",
	},
	{
		"case foo in '*') echo x ;; f*) echo y ;; esac",
		"y\n",
	},
	{
		`case 0 in [\0]) echo bar ;; esac`,
		"bar\n",
	},
	{
		`case d in [\d]) echo bar ;; esac`,
		"bar\n",
	},
	{
		`case '[' in [) echo match ;; *) echo miss ;; esac`,
		"match\n",
	},
	{
		`case '[abc' in [a*) echo match ;; *) echo miss ;; esac`,
		"match\n",
	},
	{
		`touch a b; x=']'; echo [ab$x`,
		"a b\n",
	},

	// exec
	{
		"$GOSH_PROG 'echo foo'",
		"foo\n",
	},
	{
		"$GOSH_PROG 'echo foo >&2' >/dev/null",
		"foo\n",
	},
	{
		"echo foo | $GOSH_PROG 'cat >&2' >/dev/null",
		"foo\n",
	},
	{
		"$GOSH_PROG 'exit 1'",
		"exit status 1",
	},
	{
		"exec >/dev/null; echo foo",
		"",
	},
	{
		"exec >a; echo foo; cat a >&2",
		"foo\n",
	},
	{
		"exec >a; echo one >b; echo two; cat a b >&2",
		"two\none\n",
	},
	{
		"{ exec >a; echo in; } >b; echo out; cat a b >&2",
		"out\nin\n",
	},

	// return
	{"return", "return: can only be done from a func or sourced script\nexit status 1 #JUSTERR"},
	{"f() { return; }; f", ""},
	{"f() { return 2; }; f", "exit status 2"},
	{"f() { echo foo; return; echo bar; }; f", "foo\n"},
	{"f1() { :; }; f2() { f1; return; }; f2", ""},
	{"echo 'return' >a; source ./a", ""},
	{"echo 'return' >a; source ./a; return", "return: can only be done from a func or sourced script\nexit status 1 #JUSTERR"},
	{"echo 'return 2' >a; source ./a", "exit status 2"},
	{"echo 'echo foo; return; echo bar' >a; source ./a", "foo\n"},

	// command
	{"command", ""},
	{"command -o echo", "command: invalid option \"-o\"\nexit status 2 #JUSTERR"},
	{"command -vo echo", "command: invalid option \"-o\"\nexit status 2 #JUSTERR"},
	{"echo() { :; }; echo foo", ""},
	{"echo() { :; }; command echo foo", "foo\n"},
	{"command -v does-not-exist", "exit status 1"},
	{"foo() { :; }; command -v foo", "foo\n"},
	{"foo() { :; }; command -v does-not-exist foo", "foo\n"},
	{"command -v echo", "echo\n"},
	{"[[ $(command -v $PATH_PROG) == $PATH_PROG ]]", "exit status 1"},

	// cmd substitution
	{
		"echo foo $(printf bar)",
		"foo bar\n",
	},
	{
		"echo foo $(echo bar)",
		"foo bar\n",
	},
	{
		"$(echo echo foo bar)",
		"foo bar\n",
	},
	{
		"for i in 1 $(echo 2 3) 4; do echo $i; done",
		"1\n2\n3\n4\n",
	},
	{
		"echo 1$(echo 2 3)4",
		"12 34\n",
	},
	{
		`mkdir d; [[ $(cd d && pwd) == "$(pwd)" ]]`,
		"exit status 1",
	},
	{
		"a=sub true & { a=main $ENV_PROG | grep '^a='; }",
		"a=main\n",
	},
	{
		"echo foo >f; echo $(cat f); echo $(<f)",
		"foo\nfoo\n",
	},
	{
		"echo foo >f; echo $(<f; echo bar)",
		"bar\n",
	},
	{
		"$(false); echo $?; $(exit 3); echo $?; $(true); echo $?",
		"1\n3\n0\n",
	},
	{
		"foo=$(false); echo $?; echo foo $(false); echo $?",
		"1\nfoo\n0\n",
	},
	{
		"$(false) $(true); echo $?; $(true) $(false); echo $?",
		"0\n1\n",
	},
	{
		"foo=$(false) $(true); echo $?; foo=$(true) $(false); echo $?",
		"1\n0\n",
	},

	// pipes
	{
		"echo foo | sed 's/o/a/g'",
		"faa\n",
	},
	{
		"echo foo | false | true",
		"",
	},
	{
		"true $(true) | true", // used to panic
		"",
	},
	{
		// The first command in the block used to consume stdin, even
		// though it shouldn't be. We just want to run any arbitrary
		// non-builtin program that doesn't consume stdin.
		"echo foo | { $ENV_PROG >/dev/null; cat; }",
		"foo\n",
	},

	// redirects
	{
		"echo foo >&1 | sed 's/o/a/g'",
		"faa\n",
	},
	{
		"echo foo >&2 | sed 's/o/a/g'",
		"foo\n",
	},
	{
		// TODO: why does bash need a block here?
		"{ echo foo >&2; } |& sed 's/o/a/g'",
		"faa\n",
	},
	{
		"echo foo >/dev/null; echo bar",
		"bar\n",
	},
	{
		">a; echo foo >>b; wc -c <a >>b; cat b | tr -d ' '",
		"foo\n0\n",
	},
	{
		"echo foo >a; <a",
		"",
	},
	{
		"echo foo >a; mkdir b; cd b; cat <../a",
		"foo\n",
	},
	{
		"echo foo >a; wc -c <a | tr -d ' '",
		"4\n",
	},
	{
		"echo foo >>a; echo bar &>>a; wc -c <a | tr -d ' '",
		"8\n",
	},
	{
		"{ echo a; echo b >&2; } &>/dev/null",
		"",
	},
	{
		"sed 's/o/a/g' <<EOF\nfoo$foo\nEOF",
		"faa\n",
	},
	{
		"sed 's/o/a/g' <<'EOF'\nfoo$foo\nEOF",
		"faa$faa\n",
	},
	{
		"sed 's/o/a/g' <<EOF\n\tfoo\nEOF",
		"\tfaa\n",
	},
	{
		"sed 's/o/a/g' <<EOF\nfoo\nEOF",
		"faa\n",
	},
	{
		"cat <<EOF\n~/foo\nEOF",
		"~/foo\n",
	},
	{
		"sed 's/o/a/g' <<<foo$foo",
		"faa\n",
	},
	{
		"cat <<-EOF\n\tfoo\nEOF",
		"foo\n",
	},
	{
		"cat <<-EOF\n\tfoo\n\nEOF",
		"foo\n\n",
	},
	{
		"cat <<EOF\nfoo\\\nbar\nEOF",
		"foobar\n",
	},
	{
		"cat <<'EOF'\nfoo\\\nbar\nEOF",
		"foo\\\nbar\n",
	},
	// `read -t` and `read -u` (#267). Both used to be refused with exit 2,
	// which nothing calling `read` checks — so in practice the variable
	// stayed empty and the loop body never ran.
	{
		"read -r -t 1 x <<< hi; echo \"st=$? x=[$x]\"",
		"st=0 x=[hi]\n",
	},
	{
		"read -r -t 0.2 x <<< hi; echo \"st=$? x=[$x]\"",
		"st=0 x=[hi]\n",
	},
	{
		// A timeout is reported as a status above 128, the way a signal is.
		"{ sleep 0.5; } | { read -r -t 0.1 x; echo \"st=$? x=[$x]\"; }",
		"st=142 x=[]\n",
	},
	{
		// Whatever arrived before the timeout is still assigned: only the
		// status says the read was cut short.
		"{ printf par; sleep 0.5; } | { read -r -t 0.1 x; echo \"st=$? x=[$x]\"; }",
		"st=142 x=[par]\n",
	},
	{
		// A regular file cannot take a deadline and does not need one.
		"printf 'hi\\n' > f; read -r -t 1 x < f; echo \"st=$? x=[$x]\"",
		"st=0 x=[hi]\n",
	},
	{
		"read -r -t zz x 2>/dev/null; echo \"st=$?\"",
		"st=1\n",
	},
	{
		"printf 'hi\\n' > f; exec 3< f; read -r -u 3 x; echo \"st=$? x=[$x]\"",
		"st=0 x=[hi]\n",
	},
	{
		// The descriptor keeps its position between reads, which is what a
		// `while read -u "$fd"` loop depends on.
		"printf 'a\\nb\\n' > f; exec 3< f; read -r -u 3 x; read -r -u 3 y; echo \"[$x][$y]\"",
		"[a][b]\n",
	},
	{
		"printf 'hi\\n' > f; exec 3< f; read -r -N 1 -u 3 x; echo \"[$x]\"",
		"[h]\n",
	},
	{
		"read -r -u 7 x 2>/dev/null; echo \"st=$?\"",
		"st=1\n",
	},
	{
		"read -r -u zz x 2>/dev/null; echo \"st=$?\"",
		"st=1\n",
	},
	{
		"printf 'hi\\n' > f; exec 3< f; read -r -t 1 -u 3 x; echo \"st=$? x=[$x]\"",
		"st=0 x=[hi]\n",
	},
	{
		// `-t 0` asks whether input is waiting and reads nothing at all.
		"printf 'hi\\n' > f; read -r -t 0 x < f; echo \"st=$? x=[$x]\"",
		"st=0 x=[]\n",
	},
	// The call-frame stack: FUNCNAME, BASH_SOURCE, BASH_LINENO and the
	// `caller` builtin, which are four views of one thing (#266, #250).
	//
	// None of these print a *file*, deliberately: this harness runs bash
	// with the script on stdin and koi in process with no parse name, so
	// the two disagree about what to call the input — a divergence about
	// $0 (#120) rather than about frames. The file is checked end to end
	// in cmd/koi, where both shells are given a real script.
	{
		"g(){ echo \"(${FUNCNAME[@]})\"; }; f(){ g; }; f",
		"(g f)\n",
	},
	{
		"echo \"[${FUNCNAME[0]-unset}]\"",
		"[unset]\n",
	},
	{
		// The line the *caller* is on, which is the half of a `die` helper
		// that says where to look.
		"g(){ echo \"${BASH_LINENO[0]}\"; }; f(){ g; }; f",
		"1\n",
	},
	{
		"g(){ echo \"${BASH_LINENO[0]}\"; }\nf(){\n  g\n}\nf",
		"3\n",
	},
	{
		"g(){ echo \"${#BASH_SOURCE[@]}\"; }; f(){ g; }; f",
		"2\n",
	},
	{
		// Unset at the top level of a command string, exactly as bash
		// leaves it — a script file is the case where it is set.
		"echo \"[${BASH_SOURCE[0]-unset}]\"",
		"[unset]\n",
	},
	{
		// `caller` answers by status when there is no frame to name, which
		// is what an error helper branches on.
		"caller; echo \"rc=$?\"",
		"rc=1\n",
	},
	{
		"f(){ caller 0; echo \"rc=$?\"; }; f",
		"rc=1\n",
	},
	{
		// Bare `caller` needs no frame above and prints bash's literal
		// NULL for a context with no file.
		"f(){ caller; }; f",
		"1 NULL\n",
	},
	{
		"g(){ caller 0 | cut -d' ' -f1-2; }; f(){ g; }; f",
		"1 f\n",
	},
	{
		// The diagnostic itself is koi-shaped (#120), so only the status is
		// compared — which is what a caller branches on anyway.
		"f(){ caller zz 2>/dev/null; echo \"rc=$?\"; }; f",
		"rc=2\n",
	},
	// The DEBUG trap, and BASH_COMMAND with it (#268). A DEBUG trap used
	// to be refused here and intercepted a layer up, which left a script's
	// `trap … DEBUG` recorded and never fired — accepted, silent, exit 0.
	{
		"trap 'echo D:$BASH_COMMAND' DEBUG; echo a; echo b",
		"D:echo a\na\nD:echo b\nb\n",
	},
	{
		// BASH_COMMAND is the source text, not the expansion: the trap
		// runs before the words are expanded, which is the whole reason a
		// tracer can print what was written.
		"trap 'echo D:$BASH_COMMAND' DEBUG; x=1; echo $x",
		"D:x=1\nD:echo $x\n1\n",
	},
	{
		// The far more common reader of BASH_COMMAND: an ERR trap saying
		// which command failed. It was reporting an empty string.
		"trap 'echo failed: $BASH_COMMAND' ERR; false; echo done",
		"failed: false\ndone\n",
	},
	{
		// Redirections are part of the command text (#445). koi rendered
		// st.Cmd alone, so a trap matching on BASH_COMMAND saw a
		// different string than bash's.
		"trap 'echo D:[$BASH_COMMAND]' DEBUG; echo a >/dev/null",
		"D:[echo a > /dev/null]\n",
	},
	{
		// bash normalizes the spacing rather than quoting the source:
		// both of these answer "> /dev/null".
		"trap 'echo D:[$BASH_COMMAND]' DEBUG; echo b   >   /dev/null",
		"D:[echo b > /dev/null]\n",
	},
	{
		// A dup stays tight where a target takes a space, and several
		// redirections keep their order.
		"trap 'echo D:[$BASH_COMMAND]' DEBUG; echo c 2>&1 >/dev/null",
		"D:[echo c 2>&1 > /dev/null]\n",
	},
	{
		// The clobber and all-streams forms take a space too.
		"trap 'echo D:[$BASH_COMMAND]' DEBUG; echo d >| /dev/null",
		"D:[echo d >| /dev/null]\n",
	},
	{
		// An fd number prefixes the operator, and a close is tight.
		"trap 'echo D:[$BASH_COMMAND]' DEBUG; exec 4>&-",
		"D:[exec 4>&-]\n",
	},
	{
		// A here-string is a word, so it takes the space.
		"trap 'echo D:[$BASH_COMMAND]' DEBUG; cat <<<hs >/dev/null",
		"D:[cat <<< hs > /dev/null]\n",
	},
	{
		// A here-document keeps its body and its terminator, with real
		// newlines — measured, where the obvious guess is that bash
		// prints the operator alone.
		//
		// The expansion is quoted here and unquoted above on purpose: an
		// unquoted $BASH_COMMAND word-splits, so the newlines collapse to
		// spaces and the case would pass against a rendering that never
		// produced them.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; cat <<EOF >/dev/null\nbody line\nEOF\n",
		"D:[cat <<EOF > /dev/null\nbody line\nEOF\n]\n",
	},
	{
		// A {varname} descriptor outlives the command that opened it —
		// that is the whole point of the form (#418). koi undid it with
		// every other redirection, so $fd named one that was already
		// gone.
		": {fd}>&1; echo redir2 >&$fd; echo \"stat=$?\"",
		"redir2\nstat=0\n",
	},
	{
		// The same for a real file rather than a dup, which is the case
		// that also needed the closer suppressed.
		": {fd}>vf; echo written >&$fd; exec {fd}>&-; cat vf",
		"written\n",
	},
	{
		// Through a nameref the descriptor lands on the target. koi
		// wrote the reference variable itself, destroying the reference.
		//
		// The *number* is not asserted: {var} takes the lowest free
		// descriptor at or above 10, so it depends on what the process
		// already has open — bash itself answered 11 rather than 10 on
		// a CI runner. What this pins is that the target holds a
		// descriptor and the reference was not clobbered.
		"declare -n ref=target; exec {ref}</dev/null; [ \"${target-unset}\" -ge 10 ] && echo assigned",
		"assigned\n",
	},
	{
		// varredir_close asks for the other behavior, and was refused
		// outright before — so neither was reachable.
		"shopt -s varredir_close; : {fd}>&1; ( echo x >&$fd ) 2>/dev/null; echo \"st=$?\"",
		"st=1\n",
	},
	{
		// An ordinary redirection is still undone with its command.
		"exec 3>keep; { echo x; } 3>other; echo y >&3; exec 3>&-; cat keep",
		"x\ny\n",
	},
	{
		// A here-document takes a descriptor like any other input
		// redirection (#414). koi assigned every body to fd 0 before
		// the descriptor was even worked out, so fd 3 was never opened
		// and E2's body landed on the shell's stdin.
		"while read line1; do read line2 <&3; echo \"$line1 - $line2\"; done <<E1 3<<E2\none\nE1\nalpha\nE2\n",
		"one - alpha\n",
	},
	{
		// The exec form, which is how a script keeps one open.
		"exec 4<<EOF\nbody\nEOF\nread -u 4 v; echo \"v=$v\"",
		"v=body\n",
	},
	{
		// A here-string takes one too.
		"read -u 3 x 3<<< hello; echo \"x=$x\"",
		"x=hello\n",
	},
	{
		// And a {varname} here-document assigns the descriptor it
		// allocated, which is one of #418's cases falling out here.
		"exec {v}<<XEOF\nline 1\nXEOF\nread -u $v l; echo \"l=$l\"",
		"l=line 1\n",
	},
	{
		// The ordinary forms are unchanged.
		"cat <<EOF\nplain\nEOF\ncat <<< hs",
		"plain\nhs\n",
	},
	{
		// `<&N-` moves rather than copies: dup onto the target, then
		// close the source (#417). koi did neither, so the descriptor
		// stayed put and nothing was closed.
		// The message text is left out of the comparison on purpose:
		// bash prefixes its diagnostics with the shell name and line,
		// and the status is what a caller acts on.
		// Two lines, deliberately: with only one, the source descriptor
		// is at EOF after the first read and answers status 1 whether
		// it was closed or not — the case would pass against a move
		// that never closed anything.
		//
		// The target is fd 9 rather than fd 0 for a reason worth
		// keeping: this table's confirm pass feeds bash the script on
		// stdin, so moving a two-line file onto fd 0 makes bash read
		// the second line as a command.
		"printf 'B\\nC\\n' > d2; exec 6<d2; exec 9<&6-; read -u 9 y; echo \"move:$y\"; read -u 6 z 2>/dev/null; echo \"fd6:$?\"",
		"move:B\nfd6:1\n",
	},
	{
		// The output side. The write through the moved descriptor is
		// not enough on its own — that works whether or not the source
		// was closed — so this also asserts fd 7 is gone, which is the
		// half that makes it a move rather than a copy.
		// The subshell is what silences the diagnostic: applying a
		// redirection to a closed descriptor is reported by the *shell*,
		// so 2>/dev/null on the command itself does not catch it.
		"exec 7>o7; exec 8>&7-; echo hi >&8; exec 8>&-; cat o7; ( echo x >&7 ) 2>/dev/null; echo \"src:$?\"",
		"hi\nsrc:1\n",
	},
	{
		// Moving a descriptor onto itself is a no-op, not a self-close.
		"exec 6>o6; exec 6>&6-; echo hi >&6; exec 6>&-; cat o6",
		"hi\n",
	},
	{
		// A plain dup still copies, leaving the source open.
		"printf 'C\\n' > d3; exec 6<d3; exec 0<&6; read y; echo \"dup:$y\"",
		"dup:C\n",
	},
	{
		// The shape that leaked: a swizzle loop handing a descriptor
		// back and forth used to run the shell out of them ("too many
		// open files"). This runs in-process over the descriptor map
		// rather than real OS descriptors, so it is a behavioral
		// regression guard rather than proof of the exhaustion — the
		// exhaustion itself was reproduced against the built binary.
		"exec 3</dev/null; i=0; while [ $i -lt 300 ]; do exec 4<&3-; exec 3<&4-; i=$((i+1)); done; echo \"survived i=$i\"",
		"survived i=300\n",
	},
	{
		// A redirection's word is expanded like any other and must come
		// out as exactly one field (#415). Two fields is ambiguous, and
		// koi used to open a file literally named "a b" — creating it,
		// on the output side.
		"z=\"a b\"; cat < $z; echo st=$?",
		"$z: ambiguous redirect\nst=1\n #JUSTERR",
	},
	{
		"z=\"a b\"; echo hi > $z; echo st=$?",
		"$z: ambiguous redirect\nst=1\n #JUSTERR",
	},
	{
		// Quoting makes it one field again, which is the escape hatch.
		"z=\"a b\"; echo hi > \"$z\"; cat \"a b\"",
		"hi\n",
	},
	{
		// Zero fields is ambiguous too, not an empty filename.
		"unset u; echo hi > $u; echo st=$?",
		"$u: ambiguous redirect\nst=1\n #JUSTERR",
	},
	{
		// Globbing happens: one match is used...
		"echo one > g1; cat < g*",
		"one\n",
	},
	{
		// ...and two is ambiguous.
		"touch f1 f2; cat < f*; echo st=$?",
		"f*: ambiguous redirect\nst=1\n #JUSTERR",
	},
	{
		// A word matching nothing stays literal, so creating a new file
		// still works.
		"echo hi > newfile; cat newfile",
		"hi\n",
	},
	{
		// A here-string is content, not a filename: no splitting and no
		// globbing.
		"z=\"a b\"; cat <<< $z; touch h1 h2; cat <<< h*",
		"a b\nh*\n",
	},
	{
		// `>&file` is csh's "both streams to this file" (#416). It used
		// to be dropped silently: no message, no file, the output on the
		// terminal and the script reading a file that was never made.
		"{ echo out; echo err >&2; } >&f; cat f",
		"out\nerr\n",
	},
	{
		// The `exec` form, which is what service scripts write.
		"exec 3>&1 4>&2; exec >&eo; echo out; echo err >&2; exec 1>&3 2>&4; cat eo",
		"out\nerr\n",
	},
	{
		// The word is expanded first, so a variable names the file.
		"v=of; { echo x; } >&$v; cat of",
		"x\n",
	},
	{
		// With an explicit descriptor there is no csh form: bash calls
		// it ambiguous, and so does koi now.
		"{ echo x 2>&o; }; echo st=$?",
		"o: ambiguous redirect\nst=1\n #JUSTERR",
	},
	{
		// There is no csh form on the input side at all.
		"cat <&o; echo st=$?",
		"o: ambiguous redirect\nst=1\n #JUSTERR",
	},
	{
		// A numeric dup is untouched by any of this.
		"echo x 2>&1 | cat",
		"x\n",
	},
	{
		// A subshell is still inside its function, so `return` ends the
		// subshell with that status instead of refusing (#422).
		"f(){ (return 5); echo st=$?; }; f",
		"st=5\n",
	},
	{
		// The one that was worse than a wrong status: the rest of the
		// command substitution used to run anyway.
		"f(){ z=$(echo comsub; return; echo after); echo \"z=$z\"; }; f",
		"z=comsub\n",
	},
	{
		// A status set by return inside a substitution is the
		// substitution's status.
		"f(){ z=$(echo a; return 7); echo \"st=$? z=$z\"; }; f",
		"st=7 z=a\n",
	},
	{
		// And it must not leak: returning inside a subshell does not
		// return from the function containing it.
		"g(){ (return 9); return 3; }; g; echo st=$?",
		"st=3\n",
	},
	{
		// The ordinary case still works — a return in the function body
		// itself stops the body.
		"f(){ return 4; echo NOPE; }; f; echo st=$?",
		"st=4\n",
	},
	{
		// A function body is not traced without "functrace"; the call is.
		"trap 'echo D' DEBUG; f() { echo in; }; f",
		"D\nin\n",
	},
	{
		"trap 'echo D' DEBUG; ( echo sub )",
		"sub\n",
	},

	// Which commands the DEBUG trap fires for (#614). The rule is leaf,
	// not compound, and the leaves are not all a CallExpr — a function
	// that declares its locals traced none of those lines, which for a
	// debugger stepping through a body is the whole preamble.
	{
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; declare -i n=1; echo $n",
		"D:[declare -i n=1]\nD:[echo $n]\n1\n",
	},
	{
		"set -T; trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; f(){ local a=1; declare -i b=2; echo $a$b; }; f",
		"D:[f]\nD:[f]\nD:[local a=1]\nD:[declare -i b=2]\nD:[echo $a$b]\n12\n",
	},
	{
		"set -T; trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; f(){ export E=1; readonly R=2; echo $E$R; }; f",
		"D:[f]\nD:[f]\nD:[export E=1]\nD:[readonly R=2]\nD:[echo $E$R]\n12\n",
	},
	{
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; [[ x == y ]]; let q=2+3; echo $q",
		"D:[[[ x == y ]]]\nD:[let q=2+3]\nD:[echo $q]\n5\n",
	},
	{
		// `(( ))` traces too, and is counted rather than spelled: bash
		// answers BASH_COMMAND with the arithmetic *as written* while
		// koi prints it back from the parse tree with normalized
		// spacing, so `(( a+1 ))` reads `((a + 1))` here — the same
		// root cause as #598, and the timing is what this asserts.
		"set -T; trap 'echo D' DEBUG; [[ x == x ]]; let a=1; (( a+1 )); echo done",
		"D\nD\nD\nD\ndone\n",
	},
	{
		// A compound command gets no trace of its own: the subshell,
		// the block, the negation and `time` all reach the trap once,
		// as their inner command.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; { echo blk; }; ! false",
		"D:[echo blk]\nblk\nD:[false]\n",
	},
	{
		// The trap fires for the command that removes it, which is the
		// order bash runs them in rather than an accident.
		"trap 'echo D' DEBUG; trap - DEBUG; echo after",
		"D\nafter\n",
	},
	{
		// The trap's own status must not become the command's.
		"trap 'true' DEBUG; false; echo $?",
		"1\n",
	},
	{
		"trap 'echo x' EXIT; trap -p",
		"trap -- 'echo x' EXIT\nx\n",
	},

	// A compound command's *head* is its own DEBUG event (#629). Which
	// heads have one had to be enumerated by running bash, exactly as
	// #614's leaves did: `for`, `select` and `case` do, `while`,
	// `until` and `if` do not, and a C-style `for` has no head at all —
	// bash fires for its three arithmetic sections instead.
	{
		// Once per iteration, with the head as written and no `; do`.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; for i in 1 2; do echo b$i; done",
		"D:[for i in 1 2]\nD:[echo b$i]\nb1\nD:[for i in 1 2]\nD:[echo b$i]\nb2\n",
	},
	{
		// Which means an empty list traces nothing at all — the head is
		// not an event of the loop's, it is an event of the iteration's.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; for i in ; do echo nope; done; echo after",
		"D:[echo after]\nafter\n",
	},
	{
		// `for i; do` reports the list it *means*, not the absence.
		"set -- p q; trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; for i; do echo b$i; done",
		"D:[for i in \"$@\"]\nD:[echo b$i]\nbp\nD:[for i in \"$@\"]\nD:[echo b$i]\nbq\n",
	},
	{
		// The `case` head fires once whether or not anything matches,
		// and the trailing space is bash's — the head is rendered with
		// an empty pattern list after the `in`.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; case a in b) echo m;; esac; echo after",
		"D:[case a in ]\nD:[echo after]\nafter\n",
	},
	{
		// Unexpanded, like every other BASH_COMMAND.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; case $(echo a) in a) echo m;; esac",
		"D:[case $(echo a) in ]\nD:[echo m]\nm\n",
	},
	{
		// `select` traces its head exactly *once*, before the menu —
		// the difference from `for` that no amount of reasoning from
		// the two loops looking alike would produce.
		"printf '1\\n' > sel.in; trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; select s in x y; do echo got$s; break; done < sel.in 2>/dev/null; echo end",
		"D:[select s in x y]\nD:[echo got$s]\ngotx\nD:[break]\nD:[echo end]\nend\n",
	},
	{
		// A C-style loop: init, then cond/body/post per iteration, then
		// the cond that ends it. No `for` head anywhere.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; for ((i=0;i<2;i++)); do echo b$i; done",
		"D:[((i=0))]\nD:[((i<2))]\nD:[echo b$i]\nb0\nD:[((i++))]\nD:[((i<2))]\nD:[echo b$i]\nb1\nD:[((i++))]\nD:[((i<2))]\n",
	},
	{
		// An omitted section still fires, as the `((1))` it means.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; for ((;;)); do break; done",
		"D:[((1))]\nD:[((1))]\nD:[break]\n",
	},
	{
		// The negative half, which is what stops the rule generalizing
		// to every compound: `while`, `until` and `if` have no head
		// event, and their conditions trace as the leaves they are.
		"trap 'echo \"D:[$BASH_COMMAND]\"' DEBUG; while [ -z \"$w\" ]; do w=1; done; until [ -n \"$u\" ]; do u=1; done; if true; then echo y; fi",
		"D:[[ -z \"$w\" ]]\nD:[w=1]\nD:[[ -z \"$w\" ]]\nD:[[ -n \"$u\" ]]\nD:[u=1]\nD:[[ -n \"$u\" ]]\nD:[true]\nD:[echo y]\ny\n",
	},
	{
		// extdebug's cancel rule reaches the head, and what it cancels
		// is measured rather than assumed: declining a `for` head skips
		// that iteration's body and leaves the loop running.
		"shopt -s extdebug; trap '[[ $BASH_COMMAND != for* ]]' DEBUG; for i in 1 2; do echo b$i; done; echo end",
		"end\n",
	},
	{
		// Declining a `case` head skips the whole case.
		"shopt -s extdebug; trap '[[ $BASH_COMMAND != case* ]]' DEBUG; case a in a) echo m;; esac; echo end",
		"end\n",
	},

	// DEBUG is suppressed inside the DEBUG trap and nowhere else
	// (#630). Every other trap's action is ordinary code: it traces,
	// and so does a function it calls, which for a debugger is the
	// handler it is stepping through.
	{
		// The RETURN action's own statement is traced, with $LINENO
		// already set to what the trap will report — 4, the returning
		// function's body line, not the last line the body ran.
		"set -T\ntrap 'echo \"D:$LINENO\"' DEBUG\ntrap 'echo RET' RETURN\nf() { echo body; }\nf",
		"D:3\nD:5\nD:4\nD:4\nbody\nD:4\nRET\n",
	},
	{
		// And a function the RETURN action calls traces its own entry
		// and its own body, at its own lines.
		"set -T\ntrap 'echo \"D:$LINENO\"' DEBUG\ntrap 'r' RETURN\nr() { echo in-r; }\nf() { echo body; }\nf",
		"D:3\nD:6\nD:5\nD:5\nbody\nD:5\nD:4\nD:4\nin-r\n",
	},
	{
		// The same for ERR. BASH_COMMAND is *not* maintained inside a
		// trap's action — every one of these reports the `false` that
		// triggered it, including the two from inside e().
		"set -T\ntrap 'echo \"D:[$BASH_COMMAND]\"' DEBUG\ntrap 'e' ERR\ne() { echo in-e; }\nfalse\necho end",
		"D:[trap 'e' ERR]\nD:[false]\nD:[false]\nD:[false]\nD:[false]\nin-e\nD:[echo end]\nend\n",
	},
	{
		// And for EXIT, whose action runs after the last command.
		"set -T\ntrap 'echo D' DEBUG\ntrap 'e' EXIT\ne() { echo in-e; }\necho last",
		"D\nD\nlast\nD\nD\nD\nin-e\n",
	},
	{
		// The suppression that stays: a function called from the DEBUG
		// action traces nothing, and its return fires no RETURN trap
		// either — while the RETURN trap for h() still fires, and is
		// itself traced.
		"set -T\ng() { echo in-g; }\ntrap 'echo DBG; g' DEBUG\ntrap 'echo RET' RETURN\nh() { echo h-body; }\nh",
		"DBG\nin-g\nDBG\nin-g\nDBG\nin-g\nDBG\nin-g\nh-body\nDBG\nin-g\nRET\n",
	},

	// BASH_ARGV and BASH_ARGC (#637): the arguments of every active
	// call, innermost first, maintained under extdebug.
	{
		// bash's own dbg-support3.sub, which is what this is for. The
		// order is reversed *within* a frame as well as across them —
		// `f3 3 z` contributes `z` then `3` — so this is not the
		// concatenation of the `$@`s.
		"shopt -s extdebug; callstack(){ echo \"deep ${#BASH_ARGV[*]}\"; for f in ${BASH_ARGV[@]}; do echo \"- $f\"; done; }; f3(){ callstack; }; f2(){ f3 3 z; }; f1(){ f2 2 y; }; f1 1 x",
		"deep 6\n- z\n- 3\n- y\n- 2\n- x\n- 1\n",
	},
	{
		// BASH_ARGC is one count per frame, innermost first, which is
		// what lets a reader slice BASH_ARGV back into frames.
		"shopt -s extdebug; show(){ echo \"argc=[${BASH_ARGC[*]}]\"; }; f(){ show one; }; f a b",
		"argc=[1 2 0]\n",
	},
	{
		// Without extdebug only the bottom entry is there: a call made
		// with the option off contributes nothing at all, not a zero.
		"echo \"argc=[${BASH_ARGC[*]}] argv=[${BASH_ARGV[*]}]\"; f(){ echo \"in f argc=[${BASH_ARGC[*]}]\"; }; f q",
		"argc=[0] argv=[]\nin f argc=[0]\n",
	},
	{
		// Gated at the moment of the *call*: turning the option off
		// inside f stops g's frame from being recorded even though the
		// stack below it stays.
		"shopt -s extdebug; f(){ shopt -u extdebug; g x y; }; g(){ echo \"argc=[${BASH_ARGC[*]}] argv=[${BASH_ARGV[*]}]\"; }; f a b",
		"argc=[2 0] argv=[b a]\n",
	},
	{
		// The bottom entry is a snapshot rather than a view: it is
		// taken the first time the shell has reason to, and neither
		// `shift` nor a later `set --` moves it afterwards.
		"set -- a b c; echo \"argc=[${BASH_ARGC[*]}] argv=[${BASH_ARGV[*]}]\"; shift; echo \"argc=[${BASH_ARGC[*]}]\"",
		"argc=[3] argv=[c b a]\n" + "argc=[3]\n",
	},
	{
		// Taken *before* the `set --` here, so it holds nothing.
		"echo \"start=[${BASH_ARGC[*]}]\"; set -- x y z; echo \"after=[${BASH_ARGC[*]}]\"",
		"start=[0]\nafter=[0]\n",
	},
	{
		// `shopt -s extdebug` is the other moment it is taken, which is
		// why the second one here changes nothing.
		"shopt -s extdebug; shopt -u extdebug; set -- q r; shopt -s extdebug; echo \"[${BASH_ARGC[*]}] [${BASH_ARGV[*]}]\"",
		"[0] []\n",
	},
	{
		// And a read from inside a function does not take it, which is
		// bash's odd half: the parameters visible there are the
		// function's, so the answer is the empty array until something
		// at the top level asks.
		"set -- a b; f(){ echo \"in=[${BASH_ARGC[*]}] [${BASH_ARGV[*]}]\"; }; f; shopt -s extdebug; f q",
		"in=[] []\nin=[1 2] [q b a]\n",
	},
	{
		// A subshell keeps the stack, since a stack-trace helper is
		// usually reached through `$(…)`.
		"shopt -s extdebug; f(){ ( echo \"sub=[${BASH_ARGV[*]}]\" ); }; f a b",
		"sub=[b a]\n",
	},
	{
		// Both names are in the variable table, so a listing prints
		// them even though nothing ever assigned them.
		"declare -p BASH_ARGC BASH_ARGV",
		"declare -a BASH_ARGC=([0]=\"0\")\ndeclare -a BASH_ARGV=()\n",
	},
	{
		// And both refuse `unset`, as BASH_SOURCE and BASH_LINENO do.
		"unset BASH_ARGV; echo st=$?",
		"unset: BASH_ARGV: cannot unset\nst=1\n #JUSTERR",
	},

	// RETURN (#295). The frame rules are covered end to end against real
	// bash in cmd/koi/trapreturn_test.go, including `source`, which needs
	// a file this table has no way to write. These are the in-package
	// core: that it fires, that it does not eat the return status, and
	// the two inheritance rules that decide everything else.
	{
		"f(){ trap 'echo left' RETURN; echo in; }; f",
		"in\nleft\n",
	},
	{
		"f(){ trap 'echo left' RETURN; return 5; }; f; echo rc=$?",
		"left\nrc=5\n",
	},
	{
		// FUNCNAME inside the trap is still the returning function — a
		// cleanup handler reads it to name what it is cleaning up after.
		"f(){ trap 'echo left:$FUNCNAME' RETURN; :; }; f",
		"left:f\n",
	},
	{
		// A function does not inherit RETURN...
		"trap 'echo R' RETURN; f(){ echo in; }; f; echo done",
		"in\ndone\n",
	},
	{
		// ...until functrace says so.
		"set -T; trap 'echo R' RETURN; f(){ echo in; }; f",
		"in\nR\n",
	},
	{
		// A nested call turning inheritance off must not silence the
		// caller's own return.
		"f(){ trap 'echo R' RETURN; g; }; g(){ echo g; }; f",
		"g\nR\n",
	},
	{
		"f(){ trap 'echo T' RETURN; :; }; f; trap -p RETURN",
		"T\ntrap -- 'echo T' RETURN\n",
	},

	// Where a RETURN trap says it is, and where the DEBUG trap says the
	// function starts (#614). `print_return_trap $LINENO` is bash's own
	// debugger idiom; koi answered the line the *trap* was written on,
	// so every frame in a run reported the same number.
	{
		"set -T\ntrap 'echo \"R:$LINENO\"' RETURN\nf() {\n  echo body\n}\nf",
		"body\nR:3\n",
	},
	{
		// Installed after the function, so the trap's own line is past
		// the body rather than before it: a number taken from the trap
		// would read 5 here and 2 in the case above.
		"set -T\nf() {\n  echo body\n}\ntrap 'echo \"R:$LINENO\"' RETURN\nf",
		"body\nR:2\n",
	},
	{
		// Each frame reports its own, innermost first.
		"set -T\ntrap 'echo \"R:$LINENO\"' RETURN\nouter() { inner; }\ninner() { echo work; }\nouter",
		"work\nR:4\nR:3\n",
	},
	{
		// The action reads BASH_COMMAND as the last command the frame
		// ran, which is why RETURN counts as a trap that wants it
		// maintained.
		"set -T; trap 'echo \"R:[$BASH_COMMAND]\"' RETURN; f(){ echo one; echo two; }; f",
		"one\ntwo\nR:[echo two]\n",
	},
	{
		// Entering a function is its own DEBUG event, reporting the
		// line the body starts on — so a call on line 6 traces 6 in the
		// caller's frame and then 3 in the function's, which is how a
		// stepping debugger follows execution into a call.
		"set -T\ntrap 'echo \"D:$LINENO\"' DEBUG\nf() {\n  echo body\n}\nf",
		"D:6\nD:3\nD:4\nbody\n",
	},
	{
		// extdebug: declining the function-entry trace skips the whole
		// body *and* the RETURN trap, which is what makes it a
		// debugger's "skip this call". `keep` shows both still happen
		// when the trace does not decline.
		"shopt -s extdebug\nset -T\nd() { [ \"$1\" = enter ] && return 1; return 0; }\ntrap 'd $BASH_COMMAND' DEBUG\ntrap 'echo LEFT:$LINENO' RETURN\nenter() { echo NOPE; }\nkeep() { echo yes; }\nenter\nkeep\necho st=$?",
		"yes\nLEFT:7\nst=0\n",
	},
	{
		// bare `trap` prints the same listing as `trap -p`.
		"trap 'echo x' EXIT; trap",
		"trap -- 'echo x' EXIT\nx\n",
	},
	{
		"trap 'echo e' ERR; trap 'echo x' EXIT; trap -p",
		"trap -- 'echo x' EXIT\ntrap -- 'echo e' ERR\nx\n",
	},
	{
		"trap 'echo e' ERR; trap 'echo x' EXIT; trap -p ERR",
		"trap -- 'echo e' ERR\nx\n",
	},
	{
		"trap -p; echo none",
		"none\n",
	},
	{
		// The reason `-p` exists: save a handler, do something that needs
		// it gone, put it back. It runs in a command substitution, and a
		// subshell that reported its own empty set would hand back an
		// empty string — losing the handler silently, which is worse than
		// `-p` never having worked.
		"trap 'echo cleanup' EXIT\nsaved=$(trap -p EXIT)\ntrap - EXIT\neval \"$saved\"\necho body",
		"body\ncleanup\n",
	},
	{
		"trap 'echo bye' EXIT; ( trap -p EXIT )",
		"trap -- 'echo bye' EXIT\nbye\n",
	},
	{
		// The listing is what restores the handler, so it has to be
		// shell-quoted rather than Go-quoted — including the awkward case.
		"trap \"echo \\\"it's fine\\\"\" EXIT; trap -p",
		"trap -- 'echo \"it'\\''s fine\"' EXIT\nit's fine\n",
	},
	// `$-` tracks the options that are set (#265). The letters themselves
	// are not compared, because bash reports `h` for hashing and an
	// embedder contributes letters this package cannot know about; what is
	// compared is the answer the idiom asks for, which is all a caller
	// ever acts on.
	{
		"set -e; case $- in *e*) echo on;; *) echo off;; esac",
		"on\n",
	},
	{
		"set -e; set +e; case $- in *e*) echo on;; *) echo off;; esac",
		"off\n",
	},
	{
		"set -uf; case $- in *u*) echo u;; esac; case $- in *f*) echo f;; esac",
		"u\nf\n",
	},
	{
		"f() { set -e; case $- in *e*) echo on;; esac; }; f",
		"on\n",
	},
	{
		"( set -u; case $- in *u*) echo sub;; esac ); case $- in *u*) echo outer;; *) echo clean;; esac",
		"sub\nclean\n",
	},
	{
		"eval 'set -f; case $- in *f*) echo yes;; esac'",
		"yes\n",
	},
	{
		// `set -o pipefail` has no letter, in bash exactly as here.
		"set -o pipefail; case $- in *o*) echo letter;; *) echo none;; esac",
		"none\n",
	},
	{
		// `$-` is always set, so `set -u` must not make reading it fatal.
		"set -u; echo \"${-+present}\"",
		"present\n",
	},
	// A quoted delimiter makes the body literal, and that includes escape
	// processing — not only expansion (#244). The cases below were the
	// whole bug: `\\`, `\$` and an escaped backquote were the one set
	// still being unescaped, which is the *unquoted* form's rule.
	{
		"cat <<'EOF'\nre=\\\\d+\nEOF",
		"re=\\\\d+\n",
	},
	{
		"cat <<'EOF'\ncost=\\$5\nEOF",
		"cost=\\$5\n",
	},
	{
		"cat <<'EOF'\ncmd=\\`id`\nEOF",
		"cmd=\\`id`\n",
	},
	{
		"cat <<\"EOF\"\nre=\\\\d+\nEOF",
		"re=\\\\d+\n",
	},
	{
		"cat <<\\EOF\nre=\\\\d+\nEOF",
		"re=\\\\d+\n",
	},
	{
		"cat <<-'EOF'\n\tre=\\\\d+\n\t\tindented\n\tEOF",
		"re=\\\\d+\nindented\n",
	},
	{
		"cat <<-'EOF'\n\t  re=\\\\d+\n\tEOF",
		"  re=\\\\d+\n",
	},
	// `eval` and `source` re-parse inside the interpreter, so a fix that
	// rewrites the tree koi parses cannot reach them (#259). The tests
	// above pass either way and would not have noticed.
	{
		"eval 'cat <<'\\''EOF'\\''\nre=\\\\d+\nEOF'",
		"re=\\\\d+\n",
	},
	{
		"cat <<EOF\nfoo\\\"bar\\baz\nEOF",
		"foo\\\"bar\\baz\n",
	},
	{
		"cat <<EOF\n \\\\ \\$ \\` \nEOF",
		" \\ $ ` \n",
	},
	{
		"mkdir a; echo foo >a |& grep -q 'is a directory'",
		" #IGNORE bash prints a warning",
	},
	{
		"echo foo 1>&1 | sed 's/o/a/g'",
		"faa\n",
	},
	{
		"echo foo 2>&2 |& sed 's/o/a/g'",
		"faa\n",
	},
	{
		"printf 2>&1 | sed 's/.*usage.*/foo/'",
		"foo\n",
	},
	{
		"mkdir a && cd a && echo foo >b && cd .. && cat a/b",
		"foo\n",
	},
	{
		"echo foo 2>&-; :",
		"foo\n",
	},
	{
		// `>&-` closes stdout or stderr. Note that any writes result in errors.
		"echo foo >&- 2>&-; :",
		"",
	},
	{
		// `>|` overwrites the file whether or not noclobber is set
		"echo old >f; echo new >|f; cat f",
		"new\n",
	},
	{
		// `<>` opens for reading and writing without truncating
		"echo hi >f; read -r l <>f; echo \"[$l]\"; cat f",
		"[hi]\nhi\n",
	},

	// file descriptors above 2
	{
		`exec 3>f; echo hi >&3; exec 3>&-; cat f`,
		"hi\n",
	},
	{
		`echo hi 3>f >&3; cat f`,
		"hi\n",
	},
	{
		`printf 'line\n' >f; exec 3<f; read -r l <&3; echo "[$l]"`,
		"[line]\n",
	},
	{
		`exec 3>a 4>b; echo A >&3; echo B >&4; exec 3>&- 4>&-; cat a b`,
		"A\nB\n",
	},
	{
		`echo one >f; exec 3>>f; echo two >&3; exec 3>&-; cat f`,
		"one\ntwo\n",
	},
	{
		// a descriptor can be duplicated from another
		`exec 3>&1; echo hi >&3`,
		"hi\n",
	},
	{
		`exec 3>f; echo hi >&2 2>&3; exec 3>&-; cat f`,
		"hi\n",
	},
	{
		// a redirection on one statement does not outlive it, unlike exec's
		`exec 3>a; { echo inner >&3; } 3>b; echo outer >&3; exec 3>&-; echo "a=[$(cat a)] b=[$(cat b)]"`,
		"a=[outer] b=[inner]\n",
	},
	{
		// "{name}>" allocates one and says which
		`exec {v}>f; echo hi >&$v; exec {v}>&-; cat f; [ "$v" -ge 10 ] && echo high`,
		"hi\nhigh\n",
	},
	{
		`printf 'a\nb\n' >f; exec 3<f; read -r x <&3; read -r y <&3; echo "[$x][$y]"`,
		"[a][b]\n",
	},
	{
		`echo hi >f; exec 3<>f; read -r l <&3; echo "[$l]"`,
		"[hi]\n",
	},
	{
		// a subshell inherits them
		`exec 3>f; ( echo sub >&3 ); exec 3>&-; cat f`,
		"sub\n",
	},
	{
		`echo hi >&9`,
		"9: Bad file descriptor\nexit status 1 #JUSTERR",
	},
	{
		`read -r l <&9`,
		"9: Bad file descriptor\nexit status 1 #JUSTERR",
	},

	// noclobber
	{
		`set -C; echo old >f; echo new >f; echo "st=$?"; cat f`,
		"f: cannot overwrite existing file\nst=1\nold\n #IGNORE bash prefixes its diagnostics",
	},
	{
		// the same without the diagnostic, so that bash confirms the behavior
		`set -C; echo old >f; echo new 2>/dev/null >f; echo "st=$?"; cat f`,
		"st=1\nold\n",
	},
	{
		// writing to a file which does not exist yet is allowed
		`set -C; echo new >f; cat f`,
		"new\n",
	},
	{
		`set -C; echo old >f; echo new >|f; cat f`,
		"new\n",
	},
	{
		`set -C; echo old >f; echo new >>f; cat f`,
		"old\nnew\n",
	},
	{
		`set -C; echo old >f; echo new 2>/dev/null &>f; echo "st=$?"; cat f`,
		"st=1\nold\n",
	},
	{
		// only regular files are protected
		`set -C; echo x >/dev/null; echo "st=$?"`,
		"st=0\n",
	},
	{
		`set -C; set +C; echo old >f; echo new >f; cat f`,
		"new\n",
	},
	{
		`set -o noclobber; echo old >f; echo new 2>/dev/null >f; echo "st=$?"`,
		"st=1\n",
	},
	{
		"echo foo | sed $(read line 2>/dev/null; echo 's/o/a/g')",
		"",
	},
	{
		// `<&-` closes stdin, to e.g. ensure that a subshell does not consume
		// the standard input shared with the parent shell.
		// Note that any reads result in errors.
		"echo foo | sed $(exec <&-; read line 2>/dev/null; echo 's/o/a/g')",
		"faa\n",
	},
	{
		// Concurrent pipe commands used to cause races when modifying the environment.
		"a=1 b=2 c=3 d=4 e=5 : | a=1 b=2 c=3 d=4 e=5 : | a=1 b=2 c=3 d=4 e=5 : | a=1 b=2 c=3 d=4 e=5 :",
		"",
	},

	// background/wait
	{"wait", ""},
	{"wait foo", "wait: pid foo is not a child of this shell\nexit status 1 #JUSTERR"},

	// `wait -n` (#287). Every expectation here was taken from real bash
	// rather than reasoned about: the status is the finished job's, an
	// already-finished job satisfies it without blocking, each job is
	// handed back once, and 127 means there is nothing left — which is
	// how a drain loop knows to stop.
	{"wait -n; echo $?", "127\n"},
	{"(exit 3) & wait -n; echo $?", "3\n"},
	// Ordered with a sleep rather than left to the scheduler: two jobs
	// that both exit immediately have no defined finishing order, so an
	// expectation about which -n returns first would be a coin flip
	// dressed up as a test.
	{"(exit 3) & (sleep 0.1; exit 4) & wait -n; echo $?", "3\n"},
	{"(sleep 0.1; exit 3) & (exit 4) & wait -n; echo $?", "4\n"},
	{"(exit 3) & (sleep 0.1; exit 4) & wait -n; wait -n; echo $?", "4\n"},
	{"(exit 3) & wait -n; wait -n; echo $?", "127\n"},
	// Reaping is not a -n-only notion: bash's plain `wait` collects the
	// jobs too, so nothing is left for a following -n.
	{"(exit 3) & wait; wait -n; echo $?", "127\n"},
	{"(exit 3) & p=$!; wait $p; wait -n; echo $?", "127\n"},
	{"wait -n foo", "wait: pid foo is not a child of this shell\nexit status 1 #JUSTERR"},
	// -p records *which* job answered, so a script can tell "job N
	// finished" from "there was nothing left" without reading $? twice.
	// bash leaves it unset in the second case, and so does koi.
	// The pid's *value* is deliberately not compared: koi's jobs are
	// goroutines and $! spells them "gN", where bash has a real process
	// id. What has to agree is whether the variable was set, and that it
	// carries the same spelling the shell itself hands out.
	{"(exit 3) & wait -n -p v; echo \"$?/${v:+set}\"", "3/set\n"},
	{"wait -n -p v; echo \"$?/${v-unset}\"", "127/unset\n"},
	{"(exit 3) & p=$!; wait -p v $p; [ \"$v\" = \"$p\" ] && echo matches", "matches\n"},

	// coproc (#287): the clause parsed and the executor dropped it.
	{
		"coproc C { read -r l; echo \"got:$l\"; }; echo hi >&\"${C[1]}\"; read -r r <&\"${C[0]}\"; echo \"$r\"",
		"got:hi\n",
	},
	// No name means COPROC, which is also bash's rule for a simple command.
	{"coproc { echo named-by-default; }; read -r r <&\"${COPROC[0]}\"; echo \"$r\"", "named-by-default\n"},
	// NAME_PID spells the job the way $! does, so `wait` can find it.
	{"coproc C { exit 4; }; wait \"$C_PID\"; echo $?", "4\n"},
	{"coproc 1bad { :; }", "coproc: \"1bad\": not a valid name\nexit status 1 #JUSTERR"},
	{"{ true; } & wait", ""},
	{"{ false; } & wait", ""},
	{"{ sleep 0.01; true; } & wait", ""},
	{"{ sleep 0.01; false; } & wait", ""},
	{
		"{ echo foo; } & wait; echo bar",
		"foo\nbar\n",
	},
	{
		"{ echo foo & wait; } & wait; echo bar",
		"foo\nbar\n",
	},
	{`mkdir d; old=$PWD; cd d & wait; [[ $old == "$PWD" ]]`, ""},
	{
		"f() { echo 1; }; { sleep 0.01; f; } & f() { echo 2; }; wait",
		"1\n",
	},
	{"[[ -n $! ]]", "exit status 1"},
	{"true & [[ -n $! ]]", ""},
	{"true & true;  [[ -n $! ]]", ""},
	{"true & pid=$!; wait $pid", ""},
	{"false & pid=$!; wait $pid", "exit status 1"},
	{"{ sleep 0.01; true; } & pid=$!; wait $pid", ""},
	{"{ sleep 0.01; false; } & pid=$!; wait $pid", "exit status 1"},
	{"(true) & ok=$!; (false) & fail=$!; wait $ok $fail", "exit status 1"},
	{"(true) & ok=$!; (false) & ignore=$!; wait $ok", ""},
	{"echo foo | true | false & wait $!", "exit status 1"},
	{"echo foo | false | true & wait $!", ""},
	{"f() { false & true; }; f; wait $!", "exit status 1"},
	// The parent and child shells should not cause data races when setting env vars.
	// Note that we can't use `echo $var`, as it seems to write newlines separately,
	// which can cause them to get mixed up between concurrent subshells.
	{
		"{ for n in {0..9}; do { echo -n $n$'\n'; } & done; wait; } | sort",
		"0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n",
	},
	{
		"outer=val; for n in {0..9}; do { echo -n $outer$'\n'; } & outer=val; done; wait",
		"val\nval\nval\nval\nval\nval\nval\nval\nval\nval\n",
	},
	{
		"for n in {0..9}; do { inner=val; } & echo $inner; done",
		"\n\n\n\n\n\n\n\n\n\n",
	},
	{
		"exit 2 & bg1=$!; exit 0 & bg2=$!; wait $bg1 $bg2; echo $?",
		"0\n",
	},
	{
		"exit 2 & bg1=$!; exit 4 & bg2=$!; wait $bg1 $bg2; echo $?",
		"4\n",
	},

	// bash test
	{
		"[[ a ]]",
		"",
	},
	{
		"[[ '' ]]",
		"exit status 1",
	},
	{
		"[[ '' ]]; [[ a ]]",
		"",
	},
	{
		"[[ ! (a == b) ]]",
		"",
	},
	{
		"[[ a != b ]]",
		"",
	},
	{
		"[[ a && '' ]]",
		"exit status 1",
	},
	{
		"[[ a || '' ]]",
		"",
	},
	{
		"[[ a > 3 ]]",
		"",
	},
	{
		"[[ a < 3 ]]",
		"exit status 1",
	},
	{
		"[[ 3 == 03 ]]",
		"exit status 1",
	},
	{
		"[[ a -eq b ]]",
		"",
	},
	{
		"[[ 3 -eq 03 ]]",
		"",
	},
	{
		"[[ 3 -ne 4 ]]",
		"",
	},
	{
		"[[ 3 -le 4 ]]",
		"",
	},
	{
		"[[ 3 -ge 4 ]]",
		"exit status 1",
	},
	{
		"[[ 3 -ge 3 ]]",
		"",
	},
	{
		"[[ 3 -lt 4 ]]",
		"",
	},
	{
		"[[ ' 3' -lt '4 ' ]]",
		"",
	},
	{
		"[[ 3 -gt 4 ]]",
		"exit status 1",
	},
	{
		"[[ 3 -gt 3 ]]",
		"exit status 1",
	},
	{
		"[[ a -nt a || a -ot a ]]",
		"exit status 1",
	},
	{
		"touch -t 202111050000.30 a b; [[ a -nt b || a -ot b ]]",
		"exit status 1",
	},
	{
		"touch -t 202111050200.00 a; touch -t 202111060100.00 b; [[ a -nt b ]]",
		"exit status 1",
	},
	{
		"touch -t 202111050000.00 a; touch -t 202111060000.00 b; [[ a -ot b ]]",
		"",
	},
	{
		">a; [[ a -nt b ]]",
		"",
	},
	{
		">a; [[ a -ot b ]]",
		"exit status 1",
	},
	{
		">b; [[ a -nt b ]]",
		"exit status 1",
	},
	{
		">b; [[ a -ot b ]]",
		"",
	},
	{
		"[[ a -ef b ]]",
		"exit status 1",
	},
	{
		">a >b; [[ a -ef b ]]",
		"exit status 1",
	},
	{
		">a; [[ a -ef a ]]",
		"",
	},
	{
		">a; ln a b; [[ a -ef b ]]",
		"",
	},
	{
		">a; ln -s a b; [[ a -ef b ]]",
		"",
	},
	{
		"[[ -z 'foo' || -n '' ]]",
		"exit status 1",
	},
	{
		"[[ -z '' && -n 'foo' ]]",
		"",
	},
	{
		"a=x b=''; [[ -v a && -v b && ! -v c ]]",
		"",
	},
	{
		"[[ abc == *b* ]]",
		"",
	},
	{
		"[[ abc != *b* ]]",
		"exit status 1",
	},
	{
		"[[ *b = '*b' ]]",
		"",
	},
	{
		"[[ ab == a. ]]",
		"exit status 1",
	},
	{
		`x='*b*'; [[ abc == $x ]]`,
		"",
	},
	{
		`x='*b*'; [[ abc == "$x" ]]`,
		"exit status 1",
	},
	{
		`[[ abc == \a\bc ]]`,
		"",
	},
	{
		"[[ abc != *b'*' ]]",
		"",
	},
	{
		"[[ a =~ b ]]",
		"exit status 1",
	},
	{
		"[[ foo =~ foo && foo =~ .* && foo =~ f.o ]]",
		"",
	},
	{
		"[[ foo =~ oo ]] && echo foo; [[ foo =~ ^oo$ ]] && echo bar || true",
		"foo\n",
	},
	{
		"[[ a =~ [ ]]",
		"exit status 2 #JUSTERR",
	},
	{
		"[[ a__b__c =~ _*(b_*) ]]; echo ${BASH_REMATCH[0]}; echo ${BASH_REMATCH[1]}",
		"__b__\nb__\n",
	},
	{
		"[[ -e a ]] && echo x; >a; [[ -e a ]] && echo y",
		"y\n",
	},
	{
		"ln -s b a; [[ -e a ]] && echo x; >b; [[ -e a ]] && echo y",
		"y\n",
	},
	{
		"[[ -f a ]] && echo x; >a; [[ -f a ]] && echo y",
		"y\n",
	},
	{
		"[[ -e a ]] && echo x; mkdir a; [[ -e a ]] && echo y",
		"y\n",
	},
	{
		"[[ -d a ]] && echo x; mkdir a; [[ -d a ]] && echo y",
		"y\n",
	},
	{
		"[[ -r a ]] && echo x; >a; [[ -r a ]] && echo y",
		"y\n",
	},
	{
		"[[ -w a ]] && echo x; >a; [[ -w a ]] && echo y",
		"y\n",
	},
	{
		"[[ -s a ]] && echo x; echo body >a; [[ -s a ]] && echo y",
		"y\n",
	},
	{
		"[[ -L a ]] && echo x; ln -s b a; [[ -L a ]] && echo y;",
		"y\n",
	},
	{
		"[[ \"multiline\ntext\" == *text* ]] && echo x; [[ \"multiline\ntext\" == *multiline* ]] && echo y",
		"x\ny\n",
	},
	// * should match a newline
	{
		"[[ \"multiline\ntext\" == multiline*text ]] && echo x",
		"x\n",
	},
	{
		"[[ \"multiline\ntext\" == text ]]",
		"exit status 1",
	},
	{
		`case $'a\nb' in a*b) echo match ;; esac`,
		"match\n",
	},
	{
		`a=$'a\nb'; echo "${a/a*b/sub}"`,
		"sub\n",
	},
	{
		"mkdir a; cd a; test -f b && echo x; >b; test -f b && echo y",
		"y\n",
	},
	{
		">a; [[ -b a ]] && echo block; [[ -c a ]] && echo char; true",
		"",
	},
	{
		"[[ -e /dev/sda ]] || { echo block; exit; }; [[ -b /dev/sda ]] && echo block; [[ -c /dev/sda ]] && echo char; true",
		"block\n",
	},
	{
		"[[ -e /dev/nvme0n1 ]] || { echo block; exit; }; [[ -b /dev/nvme0n1 ]] && echo block; [[ -c /dev/nvme0n1 ]] && echo char; true",
		"block\n",
	},
	{
		"[[ -e /dev/tty ]] || { echo char; exit; }; [[ -b /dev/tty ]] && echo block; [[ -c /dev/tty ]] && echo char; true",
		"char\n",
	},
	{"[[ -t 1 ]]", "exit status 1"},
	{"[[ -t 1234 ]]", "exit status 1"},
	{"[[ -o wrong ]]", "exit status 1"},
	{"[[ -o errexit ]]", "exit status 1"},
	{"set -e; [[ -o errexit ]]", ""},
	{"[[ -o noglob ]]", "exit status 1"},
	{"set -f; [[ -o noglob ]]", ""},
	{"[[ -o allexport ]]", "exit status 1"},
	{"set -a; [[ -o allexport ]]", ""},
	{"[[ -o nounset ]]", "exit status 1"},
	{"set -u; [[ -o nounset ]]", ""},
	{"[[ -o noexec ]]", "exit status 1"},
	{"set -n; [[ -o noexec ]]", ""}, // actually does nothing, but oh well
	{"[[ -o pipefail ]]", "exit status 1"},
	{"set -o pipefail; [[ -o pipefail ]]", ""},
	// TODO: we don't implement precedence of && over ||.
	// {"[[ a == x && b == x || c == c ]]", ""},
	{"[[ (a == x && b == x) || c == c ]]", ""},
	{"[[ a == x && (b == x || c == c) ]]", "exit status 1"},

	// classic test
	{
		"[",
		"1:1: [: missing matching ]\nexit status 2 #JUSTERR",
	},
	{
		"[ a",
		"1:1: [: missing matching ]\nexit status 2 #JUSTERR",
	},
	{
		"[ a b c ]",
		"1:1: not a valid test operator: `b`\nexit status 2 #JUSTERR",
	},
	{
		"[ a -a ]",
		"1:1: -a must be followed by an expression\nexit status 2 #JUSTERR",
	},
	{"[ a ]", ""},
	{"[ -n ]", ""},
	{"[ '-n' ]", ""},
	{"[ -z ]", ""},
	{"[ ! ]", ""},
	{"[ a != b ]", ""},
	{"[ ! a '==' a ]", "exit status 1"},
	{"[ a -a 0 -gt 1 ]", "exit status 1"},
	{"[ 0 -gt 1 -o 1 -gt 0 ]", ""},
	{"[ 3 -gt 4 ]", "exit status 1"},
	{"[ 3 -lt 4 ]", ""},
	{"[ ' 3' -lt '4 ' ]", ""},
	{
		"[ -e a ] && echo x; >a; [ -e a ] && echo y",
		"y\n",
	},
	{
		"test 3 -gt 4",
		"exit status 1",
	},
	{
		"test 3 -lt 4",
		"",
	},
	{
		"test 3 -lt",
		"1:1: -lt must be followed by a word\nexit status 2 #JUSTERR",
	},
	{
		"touch -t 202111050000.00 a; touch -t 202111060000.00 b; [ a -nt b ]",
		"exit status 1",
	},
	{
		"touch -t 202111050000.00 a; touch -t 202111060000.00 b; [ a -ot b ]",
		"",
	},
	{
		">a; [ a -nt b ]",
		"",
	},
	{
		">b; [ a -ot b ]",
		"",
	},
	{
		"[ a -nt b ]",
		"exit status 1",
	},
	{
		">a; [ a -ef a ]",
		"",
	},
	{"[ 3 -eq 04 ]", "exit status 1"},
	{"[ 3 -eq 03 ]", ""},
	{"[ 3 -ne 03 ]", "exit status 1"},
	{"[ 3 -le 4 ]", ""},
	{"[ 3 -ge 4 ]", "exit status 1"},
	{
		"[ -d a ] && echo x; mkdir a; [ -d a ] && echo y",
		"y\n",
	},
	{
		"[ -r a ] && echo x; >a; [ -r a ] && echo y",
		"y\n",
	},
	{
		"[ -w a ] && echo x; >a; [ -w a ] && echo y",
		"y\n",
	},
	{
		// A directory is readable, writable, and executable.
		"mkdir d; [ -r d ] && echo r; [ -w d ] && echo w; [ -x d ] && echo x",
		"r\nw\nx\n",
	},
	{
		"test -? a",
		// TODO: this error message should refer to `-?`
		"1:1: not a valid test operator: `a`\n1:1: a must be followed by a word\nexit status 2 #JUSTERR",
	},
	{
		"[ -s a ] && echo x; echo body >a; [ -s a ] && echo y",
		"y\n",
	},
	{
		"[ -L a ] && echo x; ln -s b a; [ -L a ] && echo y;",
		"y\n",
	},
	{
		">a; [ -b a ] && echo block; [ -c a ] && echo char; true",
		"",
	},
	{"[ -t 1 ]", "exit status 1"},
	{"[ -t 1234 ]", "exit status 1"},
	{"[ -o wrong ]", "exit status 1"},
	{"[ -o errexit ]", "exit status 1"},
	{"set -e; [ -o errexit ]", ""},
	{"a=x b=''; [ -v a -a -v b -a ! -v c ]", ""},
	{"[ a = a ]", ""},
	{"[ a != a ]", "exit status 1"},
	{"[ abc = ab* ]", "exit status 1"},
	{"[ abc != ab* ]", ""},
	// TODO: we don't implement precedence of -a over -o.
	// {"[ a = x -a b = x -o c = c ]", ""},
	{`[ \( a = x -a b = x \) -o c = c ]`, ""},
	{`[ a = x -a \( b = x -o c = c \) ]`, "exit status 1"},

	// arithm
	{
		"echo $((1 == +1))",
		"1\n",
	},
	{
		"echo $((!0))",
		"1\n",
	},
	{
		"echo $((!3))",
		"0\n",
	},
	{
		"echo $((~0))",
		"-1\n",
	},
	{
		"echo $((~3))",
		"-4\n",
	},
	{
		"echo $((1 + 2 - 3))",
		"0\n",
	},
	{
		"echo $((-1 * 6 / 2))",
		"-3\n",
	},
	{
		"a=2; echo $(( a + $a + c ))",
		"4\n",
	},
	{
		"a=b; b=c; c=5; echo $((a % 3))",
		"2\n",
	},
	{
		"echo $((2 > 2 || 2 < 2))",
		"0\n",
	},
	{
		"echo $((2 >= 2 && 2 <= 2))",
		"1\n",
	},
	{
		"x=0; echo $((0 && (x = 1))) $x",
		"0 0\n",
	},
	{
		"x=0; echo $((1 || (x = 1))) $x",
		"1 0\n",
	},
	{
		"x=0; echo $((0 && x++)) $x $((1 || x++)) $x",
		"0 0 1 0\n",
	},
	{
		"x=0; echo $((1 && (x = 1))) $x",
		"1 1\n",
	},
	{
		"x=0; echo $((0 || (x = 2))) $x",
		"1 2\n",
	},
	{
		"echo $((0 && 1/0)) $((1 || 1/0))",
		"0 1\n",
	},
	{
		"x=0; y=0; echo $((0 && (x = 1) || (y = 2))) $x $y",
		"1 0 2\n",
	},
	{
		// An arithmetic error abandons the input unit, so the `echo $x`
		// after it never runs and the -c string answers 1 (#597).
		"x=0; echo $((1/0 && x++)); echo $x",
		"division by zero\nexit status 1 #JUSTERR",
	},
	{
		"echo $(((1 & 2) != (1 | 2)))",
		"1\n",
	},
	// Whether an arithmetic assignment's target is a variable is bash's
	// verdict at *evaluation* time, not the parser's (#597). In a word it
	// abandons the input unit, so the `echo post` after it never runs.
	{
		"echo $((5 += 2)); echo post",
		"5 += 2: attempted assignment to non-variable (error token is \"+= 2\")\nexit status 1 #JUSTERR",
	},
	{
		"echo $((7 = 43)); echo post",
		"7 = 43: attempted assignment to non-variable (error token is \"= 43\")\nexit status 1 #JUSTERR",
	},
	{
		"echo $((1 ? 20 : x+=2)); echo post",
		"1 ? 20 : x += 2: attempted assignment to non-variable (error token is \"+= 2\")\nexit status 1 #JUSTERR",
	},
	{
		// Assignment binds looser than `&&`, so the target here is the
		// whole `0 && B` rather than the name — which is why bash refuses
		// a line that looks like an ordinary short-circuit assignment.
		"echo $((0 && B=42)); echo post",
		"0 && B = 42: attempted assignment to non-variable (error token is \"= 42\")\nexit status 1 #JUSTERR",
	},
	{
		// A literal that is not a name reaches the same verdict here;
		// bash gets there by reading `1x` as a number and calling it
		// "value too great for base", so the reason diverges while the
		// refusal, the status and the abandonment agree.
		"echo $((1x=5)); echo post",
		"1x = 5: attempted assignment to non-variable (error token is \"= 5\")\nexit status 1 #JUSTERR",
	},
	{
		// The same error in a command is only that command failing: it
		// reports under the command's own name and the line carries on.
		"(( 5 += 2 )); echo same=$?",
		"((: 5 += 2: attempted assignment to non-variable (error token is \"+= 2\")\nsame=1\n #JUSTERR",
	},
	{
		"let 5+=2; echo same=$?",
		"let: 5 += 2: attempted assignment to non-variable (error token is \"+= 2\")\nsame=1\n #JUSTERR",
	},
	{
		"for ((i=0; 5+=2; i++)); do echo body; done; echo same=$?",
		"((: 5 += 2: attempted assignment to non-variable (error token is \"+= 2\")\nsame=1\n #JUSTERR",
	},
	{
		// Division by zero is the same category and was missing from the
		// abandonment list, so a word carried on where bash stopped.
		"echo pre; echo $((1/0)); echo post",
		"pre\ndivision by zero\nexit status 1 #JUSTERR",
	},
	// The targets that *are* variables keep working, which is the half a
	// parse-time refusal was protecting.
	{
		"x=3; echo $((x += 2)); echo x=$x",
		"5\nx=5\n",
	},
	{
		"a=(1 2); echo $((a[1] += 5)); echo ${a[1]}",
		"7\n7\n",
	},
	{
		"echo $((x=y=3)); echo $x $y",
		"3\n3 3\n",
	},
	{
		"echo $a; echo $((a = 3 ^ 2)); echo $a",
		"\n1\n1\n",
	},
	{
		"echo $((a += 1, a *= 2, a <<= 2, a >> 1))",
		"4\n",
	},
	{
		"echo $((a -= 10, a /= 2, a >>= 1, a << 1))",
		"-6\n",
	},
	{
		"echo $((a |= 3, a &= 1, a ^= 8, a %= 5, a))",
		"4\n",
	},
	{
		"echo $((a = 3, ++a, a--))",
		"4\n",
	},
	// Arithmetic bash cannot read is a runtime error there and only ever
	// a runtime error, since bash parses an expression when it evaluates
	// it, from a string (#600). The consequences are #597's: in a word
	// it abandons the input unit, so the `echo post` after it never runs
	// and the -c string answers 1. bash's wording quotes the expression
	// and names the token it stopped at, which is #598.
	{
		"echo $(( 4 ? : 3 )); echo post",
		"4 ? : 3: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		"echo $(( 1 ? 20 )); echo post",
		"1 ? 20: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		"echo $(( 4 ? 20 : )); echo post",
		"4 ? 20 :: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		// bash has no `**=`, so this is an operand it never reaches.
		"echo $((n**=2)); echo post",
		"n**=2: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		// Text left over where the expression should have ended is the
		// same verdict, and only the construct's delimiter check sees it.
		"echo $(( a b c )); echo post",
		"a b c: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		"echo $(( a ; c )); echo post",
		"a ; c: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		// A slice's halves are the one arithmetic inside an expansion,
		// and they are judged the same way.
		`set -- a b; echo "${#:%}"; echo post`,
		"%: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		`v=abcdef; echo "${v:1:%}"; echo post`,
		"%: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		`v=abcdef; echo "${v:%:3}"; echo post`,
		"%:3: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	// In a command it is only that command failing: reported under the
	// command's own name, status 1, and the line carries on.
	{
		"(( 4 + )); echo same=$?",
		"((: 4 +: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		"(( -- )); echo same=$?",
		"((: --: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		// A C-style loop's header is three expressions, so only the one
		// that cannot be read is a marker: `i=1` and `i < 4` still run,
		// which is why the body runs once before the post expression
		// ends the loop. The count is read afterwards rather than
		// echoed in the body, since the oracle looks for bash's own
		// diagnostic at the *start* of the output.
		`for (( i=1; i < 4; 7++ )); do n=$((n+1)); done; echo "same=$? n=$n"`,
		"((: 7++: arithmetic syntax error\nsame=1 n=1\n #JUSTERR",
	},
	{
		"for (( 4+; i < 4; i++ )); do echo body; done; echo same=$?",
		"((: 4+: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		"for (( i=1; 7++; i++ )); do echo body; done; echo same=$?",
		"((: 7++: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	// An *unquoted* `let` argument is the last member of that family
	// (#670). bash evaluates each expanded argument as an arithmetic
	// string, so a malformed one is the builtin's complaint under
	// `let: ` with status 1, and — the whole point — the rest of the
	// line still runs where a parse error forfeited the file.
	{
		"let 4+; echo same=$?",
		"let: 4+: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		// The arguments before the bad one have already run and the ones
		// after it have not, which is what proves the builtin stopped
		// where bash's does rather than the line being lost.
		`let x=1 4+ y=2; echo "same=$? x=$x y=[$y]"`,
		"let: 4+: arithmetic syntax error\nsame=1 x=1 y=[]\n #JUSTERR",
	},
	{
		// A word boundary ends an argument, so the `5` is an argument of
		// its own and the complaint still names `4+` alone.
		"let 4+ 5; echo same=$?",
		"let: 4+: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		// The argument is named as bash names it — *expanded* — which is
		// why a bailed-out argument is kept as a word rather than as its
		// raw source.
		"v=3; let $v+; echo same=$?",
		"let: 3+: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		`let "x"4+; echo same=$?`,
		"let: x4+: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		"let ++; echo same=$?",
		"let: ++: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		"let 1+*2; echo same=$?",
		"let: 1+*2: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		// `#` starts a comment only at the beginning of a word, so this
		// is one argument and bash names all of it.
		"let 4+#c; echo same=$?",
		"let: 4+#c: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		// In a command substitution the word ends at the `)`, and the
		// substitution's own status is not the line's.
		"echo [$(let 4+)]; echo same=$?",
		"let: 4+: arithmetic syntax error\n[]\nsame=0\n #JUSTERR",
	},
	{
		// A stop token ends the argument too, so what follows is the
		// next command rather than more of the expression.
		"let 4+&& echo t; echo same=$?",
		"let: 4+: arithmetic syntax error\nsame=1\n #JUSTERR",
	},
	{
		// The arguments that read still read, which is the half a
		// parse-time refusal was protecting.
		`let "a = 3" b=a+1; echo "$a $b"`,
		"3 4\n",
	},
	{
		"let 2+2 && echo yes; echo same=$?",
		"yes\nsame=0\n",
	},
	// The expressions that read keep reading, which is the half a
	// parse-time refusal was protecting.
	{
		"echo $(( (1 + 2) * 3 )) $(( 1 ? 2 : 3 ))",
		"9 2\n",
	},
	{
		"v=abcdef; echo ${v:1:2} ${v: -2} ${v::3}",
		"bc ef abc\n",
	},
	{
		"echo $((2 ** 3)) $((1234 ** 4567))",
		"8 0\n",
	},
	{
		"echo $((2 ** -1)); let x=2**-1",
		"exponent less than 0\nexit status 1 #JUSTERR",
	},
	{
		"echo $((1 ? 2 : 3)) $((0 ? 2 : 3))",
		"2 3\n",
	},
	{
		"echo $((2 ? 3 : 4)) $((-1 ? 3 : 4))",
		"3 3\n",
	},
	{
		"echo $((255+1))",
		"256\n",
	},
	{
		"echo $((0xff+1))",
		"256\n",
	},
	{
		"echo $((0377+1))",
		"256\n",
	},
	{
		"echo $((10#255+1))",
		"256\n",
	},
	{
		"echo $((16#ff+1))",
		"256\n",
	},
	{
		"echo $((2#11111111+1))",
		"256\n",
	},
	// TODO: Enable this test once integer bit widths are
	// handled in a consistent manner throughout the library.
	//{
	//	"echo $((16#badc0ffee+1))",
	//	"50159747055\n",
	//},
	{
		"echo $((16#cafe+1))",
		"51967\n",
	},
	{
		"x=-010 y=+010 z=-0x10; echo $((x)) $((y)) $((z))",
		"-8 8 -16\n",
	},
	{
		"echo $((64#z)) $((64#Z)) $((40#A)) $((64#10)) $((36#z))",
		"35 61 36 64 35\n",
	},
	{
		"a=64#@ b=64#_ c=64#1_; echo $((a)) $((b)) $((c))",
		"62 63 127\n",
	},
	{
		"echo $((nope+1))",
		"1\n", // Yes, this is what bash does.
	},
	{
		"((1))",
		"",
	},
	{
		"((3 == 4))",
		"exit status 1",
	},
	{
		"let i=(3+4); let i++; echo $i; let i--; echo $i",
		"8\n7\n",
	},
	{
		"let 3==4",
		"exit status 1",
	},
	{
		"a=1; let a++; echo $a",
		"2\n",
	},
	{
		"a=$((1 + 2)); echo $a",
		"3\n",
	},
	{
		"x=3; echo $(($x)) $((x))",
		"3 3\n",
	},
	{
		"set -- 1; echo $(($@))",
		"1\n",
	},
	{
		// A name chase that cycles is an error, as 5.3's is; a chase
		// that dead-ends stays 0.
		"a=b b=a; echo $(($a)); echo next",
		"b: expression recursion level exceeded\nexit status 1 #JUSTERR",
	},
	{
		"a=b; echo $(($a))",
		"0\n",
	},
	// Bracket-expression forms (#374): single-character collating
	// symbols and equivalence classes resolve to the character — early
	// enough to anchor a range — a closed invalid class contributes
	// nothing, and an unclosed [: degrades to literal members.
	{`case a in [[.a.]]) echo y;; *) echo n;; esac`, "y\n"},
	{`case b in [[=b=]]) echo y;; *) echo n;; esac`, "y\n"},
	{`case a in [[:alpha]) echo y;; *) echo n;; esac`, "y\n"},
	{`case "[" in [[:alpha]) echo y;; *) echo n;; esac`, "y\n"},
	{`case a in [abc[:foo:]]) echo y;; *) echo n;; esac`, "y\n"},
	{`case : in [[:foo:]]) echo y;; *) echo n;; esac`, "n\n"},
	{`case a in [[.ab.]]) echo y;; *) echo n;; esac`, "n\n"},
	{`case c in [[.a.]-z]) echo y;; *) echo n;; esac`, "y\n"},

	// Backslash quoting reaches the pattern matcher (#372): an escaped
	// metacharacter never globs, an escaped name component resolves to
	// the real file, and a trailing lone backslash is a literal one.
	{"touch a abc; echo \\* a\\*", "* a*\n"},
	{`var="ab\\"; [[ $var = $var ]] && echo true || echo false`, "true\n"},
	{`var="ab\\"; case $var in $var) echo m;; *) echo n;; esac`, "m\n"},
	{"mkdir 's*d'; touch 's*d/f'; echo s\\*d/* | sed 's@\\\\@/@g'", "s*d/f\n"},

	// A readonly violation inside an arithmetic expansion is fatal to
	// the input unit (#370): the command aborts with status 1 and a
	// script continues at its next line.
	{
		"readonly xx=1\ncase 1 in $((xx++)) ) echo hi1 ;; *) echo hi2; esac\necho ${xx}.$?",
		"xx: readonly variable\n1.1\n #JUSTERR",
	},
	{
		"readonly xx=1; echo $((xx++)); echo same-line",
		"xx: readonly variable\nexit status 1 #JUSTERR",
	},

	// A failing body command does not end a C-style loop (#369), and an
	// empty update section is fine — the body's own ((i++)) answers
	// status 1 on its first step, which used to stop the loop.
	{`for (( i=0; i<3; )); do echo $i; ((i++)); done; echo st=$?`, "0\n1\n2\nst=0\n"},
	{`for (( f=0; f<3; f++ )); do printf "%d " $f; false; done; echo end $?`, "0 1 2 end 1\n"},

	// declare -i survives arithmetic assignment, and compound element
	// values under it evaluate (#368).
	{`declare -i j=8; let j=j+1; declare -p j`, "declare -i j=\"9\"\n"},
	{`declare -i j=8; ((j=j+2)); declare -p j; j="j+5"; declare -p j`, "declare -i j=\"10\"\ndeclare -i j=\"15\"\n"},
	{`declare -ix e=3; let e=e+1; declare -p e`, "declare -ix e=\"4\"\n"},
	{`typeset -i x; x=([0]=7+11); echo ${x[@]}`, "18\n"},
	{`typeset -i y; y=(1+1 2+2); echo "${y[@]}"`, "2 4\n"},

	// A word in arithmetic context evaluates its string (#367): quoting
	// no longer disables let and ((...)), and a value that is itself an
	// expression evaluates through.
	{`x=5; let "x *= 2"; echo "$? $x"`, "0 10\n"},
	{`let "x=5+2"; echo "$? $x"`, "0 7\n"},
	{`i=0; (( "i < 3" )); echo $?`, "0\n"},
	{`i=0; n=0; for (( ; "i < 3" ; i++ )); do n=$((n+1)); done; echo $n`, "3\n"},
	{`y=1+1; echo $((y))`, "2\n"},
	// An invalid ${var:offset} is an arithmetic error that abandons the
	// input unit, not a silent slice from 0 (#366).
	{
		"HOME2=/x; echo \"${HOME2:`echo \\}`}\"; echo never",
		"}: arithmetic syntax error\nexit status 1 #JUSTERR",
	},
	{
		// bash reports an arithmetic error under the name of the command
		// that failed and carries on — `let:` and `((:` — while the same
		// error inside a word abandons the unit, which is why the last
		// `let` never runs (#597).
		"let x=3; let 3/0; ((3/0)); echo $((x/y)); let x/=0",
		"let: division by zero\n((: division by zero\ndivision by zero\nexit status 1 #JUSTERR",
	},
	{
		"let x=3; let 3%0; ((3%0)); echo $((x%y)); let x%=0",
		"let: division by zero\n((: division by zero\ndivision by zero\nexit status 1 #JUSTERR",
	},
	{
		"let x=' 3'; echo $x",
		"3\n",
	},
	{
		"x=' 3'; let x++; echo \"$x\"",
		"4\n",
	},

	// set/shift
	{
		"echo $#; set foo bar; echo $#",
		"0\n2\n",
	},
	{
		"shift; set a b c; shift; echo $@",
		"b c\n",
	},
	{
		"shift 2; set a b c; shift 2; echo $@",
		"c\n",
	},
	{
		`echo $#; set '' ""; echo $#`,
		"0\n2\n",
	},
	{
		"set -- a b; echo $#",
		"2\n",
	},
	{
		"set +; echo $#",
		"0\n",
	},
	{
		"set + a b; echo $# $1 $2",
		"2 a b\n",
	},
	{
		"set -U",
		"set: -U: invalid option\nset: usage: set [-abefhkmnptuvxBCEHPT] [-o option-name] [--] [-] [arg ...]\nexit status 2 #JUSTERR",
	},
	{
		"set -e; false; echo foo",
		"exit status 1",
	},
	{
		"set -e; shouldnotexist; echo foo",
		"shouldnotexist: command not found\nexit status 127 #JUSTERR",
	},
	{
		"set -e; set +e; false; echo foo",
		"foo\n",
	},
	{
		"set -e; ! false; echo foo",
		"foo\n",
	},
	{
		"set -e; ! true; echo foo",
		"foo\n",
	},
	{
		"set -e; if false; then echo never; fi; echo foo",
		"foo\n",
	},
	{
		"set -e; while false; do echo never; done; echo foo",
		"foo\n",
	},
	{
		"set -e; false || true; echo foo",
		"foo\n",
	},
	{
		"set -e; false && true; echo foo",
		"foo\n",
	},
	{
		"set -e; true && false; echo foo",
		"exit status 1",
	},
	{
		"false | :",
		"",
	},
	{
		// Important that we don't print in these, as otherwise we get "broken pipe" errors.
		"GOSH_CMD=exit_5 $GOSH_PROG | GOSH_CMD=exit_0 $GOSH_PROG",
		"",
	},
	{
		"set -o pipefail; false | :",
		"exit status 1",
	},
	{
		"set -o pipefail; GOSH_CMD=exit_5 $GOSH_PROG | GOSH_CMD=exit_0 $GOSH_PROG",
		"exit status 5",
	},
	{
		"set -o pipefail; true | false | true | :",
		"exit status 1",
	},
	{
		"set -o pipefail; set -M 2>/dev/null | false",
		"exit status 1",
	},
	{
		"set -o pipefail; false | :; echo next",
		"next\n",
	},
	{
		"set -o pipefail; exit 0 | :; echo next",
		"next\n",
	},
	{
		"set -o pipefail; exit 1 | :; echo next",
		"next\n",
	},
	{
		"set -e -o pipefail; false | :; echo next",
		"exit status 1",
	},
	{
		"exit 0 && true; echo foo",
		"",
	},
	{
		"exit 1 && true; echo foo",
		"exit status 1",
	},
	{
		"set -f; >a.x; echo *.x;",
		"*.x\n",
	},
	{
		"set -f; set +f; >a.x; echo *.x;",
		"a.x\n",
	},
	{
		"set -a; foo=bar; $ENV_PROG | grep ^foo=",
		"foo=bar\n",
	},
	{
		"set -a; foo=(b a r); $ENV_PROG | grep ^foo=",
		"exit status 1",
	},
	{
		"foo=bar; set -a; $ENV_PROG | grep ^foo=",
		"exit status 1",
	},
	{
		"a=b; echo $a; set -u; echo $a",
		"b\nb\n",
	},
	{
		"echo $a; set -u; echo $a; echo extra",
		"\na: unbound variable\nexit status 1 #JUSTERR",
	},
	{
		"foo=bar; set -u; echo ${foo/bar/}",
		"\n",
	},
	{
		"foo=bar; set -u; echo ${foo#bar}",
		"\n",
	},
	{
		"set -u; echo ${foo/bar/}",
		"foo: unbound variable\nexit status 1 #JUSTERR",
	},
	{
		"set -u; echo ${foo#bar}",
		"foo: unbound variable\nexit status 1 #JUSTERR",
	},
	// TODO: detect this case as unset
	// {
	// 	"set -u; foo=(bar); echo $foo; echo ${foo[3]}",
	// 	"bar\nfoo: unbound variable\nexit status 1 #JUSTERR",
	// },
	{
		"set -u; foo=(''); echo ${foo[0]}",
		"\n",
	},
	{
		"set -u; echo ${#foo}",
		"foo: unbound variable\nexit status 1 #JUSTERR",
	},
	{
		"set -u; echo ${foo+bar}",
		"\n",
	},
	{
		"set -u; echo ${foo:+bar}",
		"\n",
	},
	{
		"set -u; echo ${foo-bar}",
		"bar\n",
	},
	{
		"set -u; echo ${foo:-bar}",
		"bar\n",
	},
	{
		"set -u; echo ${foo=bar}",
		"bar\n",
	},
	{
		"set -u; echo ${foo:=bar}",
		"bar\n",
	},
	{
		"set -u; echo ${foo?bar}",
		"foo: bar\nexit status 1 #JUSTERR",
	},
	{
		"set -u; echo ${foo:?bar}",
		"foo: bar\nexit status 1 #JUSTERR",
	},
	{
		"set -ue; set -ueo pipefail",
		"",
	},
	{"set -n; echo foo", ""},
	{"set -n; [ wrong", ""},
	{"set -n; set +n; echo foo", ""},
	{
		"set -o foobar",
		"set: foobar: invalid option name\nexit status 2 #JUSTERR",
	},
	{
		// `-o` takes an option name only as a separate word that does
		// not itself begin with a sign, so this is the listing followed
		// by braceexpand rather than an option named `-B`. bash's own
		// builtins.tests counts the listing's lines to check exactly
		// this, and koi answered one line instead of twenty-seven.
		"set -o -B | wc -l | tr -d ' '",
		"27\n",
	},
	{
		// A cluster never supplies the name either: `-oe` is the listing
		// and then errexit.
		"set -oe >/dev/null; case $- in *e*) echo errexit ;; esac",
		"errexit\n",
	},
	{"set -o noexec; echo foo", ""},
	{"set +o noexec; echo foo", "foo\n"},
	{"set -e; set -o | grep -E 'errexit|noexec' | wc -l | tr -d ' '", "2\n"},
	{"set -e; set -o | grep -E 'errexit|noexec' | grep 'on$' | wc -l | tr -d ' '", "1\n"},
	{
		"set -a; set +o",
		`set -o allexport
set -o braceexpand
set +o emacs
set +o errexit
set +o errtrace
set +o functrace
set -o hashall
set +o histexpand
set +o history
set +o ignoreeof
set -o interactive-comments
set +o keyword
set +o monitor
set +o noclobber
set +o noexec
set +o noglob
set +o nolog
set +o notify
set +o nounset
set +o onecmd
set +o physical
set +o pipefail
set +o posix
set +o privileged
set +o verbose
set +o vi
set +o xtrace
 #IGNORE`,
	},
	{`set - foobar; echo $@; set -; echo $@`, "foobar\nfoobar\n"},
	// Options koi does not implement but bash starts in a known state:
	// asking for the state they are already in is a no-op in bash and has
	// to be one here, since refusing it is exit 2 and the end of a script
	// running under `set -e` (#245).
	{"set -h; echo ok", "ok\n"},
	{"set +H; echo ok", "ok\n"},
	{"set +m; echo ok", "ok\n"},
	{"set -o hashall; echo ok", "ok\n"},
	{"set +o posix; echo ok", "ok\n"},
	// braceexpand and physical are implemented rather than tolerated, so
	// both directions have to be real.
	{"set +B; echo a{1,2}", "a{1,2}\n"},
	{"set +B; set -B; echo a{1,2}", "a1 a2\n"},
	{"set +o braceexpand; echo x{y,z}", "x{y,z}\n"},
	// The line editor's dialect (#576). koi switched its editor and left
	// the bit where it was, so `set -o`, `shopt -o vi` and $SHELLOPTS all
	// reported emacs in a shell editing in vi — and a script saving and
	// restoring the mode restored the wrong one.
	//
	// The rule that is not an ordinary option's is that the two are
	// mutually exclusive, one-directionally: turning either on turns the
	// other off, and turning one off leaves the other alone.
	{
		`set -o vi; set -o | grep -E '^(emacs|vi) ' | awk '{print $1, $2}'`,
		"emacs off\nvi on\n",
	},
	{
		`set -o vi; set -o emacs; set -o | grep -E '^(emacs|vi) ' | awk '{print $1, $2}'`,
		"emacs on\nvi off\n",
	},
	{
		`set -o vi; set +o vi; set -o | grep -E '^(emacs|vi) ' | awk '{print $1, $2}'`,
		"emacs off\nvi off\n",
	},
	{
		`set -o emacs; set +o vi; set -o | grep -E '^(emacs|vi) ' | awk '{print $1, $2}'`,
		"emacs on\nvi off\n",
	},
	{
		`set -o vi; set -o emacs; set +o emacs; set -o | grep -E '^(emacs|vi) ' | awk '{print $1, $2}'`,
		"emacs off\nvi off\n",
	},
	// `shopt -o` is the same switch spelled the other way, so it owes the
	// same exclusion and the same answer.
	{
		`shopt -o -s vi; set -o | grep -E '^(emacs|vi) ' | awk '{print $1, $2}'`,
		"emacs off\nvi on\n",
	},
	{
		`set -o vi; shopt -o -u vi; set -o | grep -E '^(emacs|vi) ' | awk '{print $1, $2}'`,
		"emacs off\nvi off\n",
	},
	{`shopt -o vi >/dev/null; echo st=$?`, "st=1\n"},
	{`set -o vi; shopt -o vi >/dev/null; echo st=$?`, "st=0\n"},
	// The save-and-restore idiom the issue was opened about: `set +o` is
	// the form a script stores and replays.
	{`set -o vi; set +o | grep -E ' (emacs|vi)$'`, "set +o emacs\nset -o vi\n"},
	{`set -o vi; case :$SHELLOPTS: in *:vi:*) echo yes;; *) echo no;; esac`, "yes\n"},
	// A function's `set -o vi` is the shell's, and a subshell's is its own
	// — both ordinary option behavior, and both worth pinning since this
	// option used to be answered somewhere else entirely.
	{`f() { set -o vi; }; f; set -o | grep -E '^vi ' | awk '{print $2}'`, "on\n"},
	{`(set -o vi); set -o | grep -E '^vi ' | awk '{print $2}'`, "off\n"},

	// History expansion's *bit* (#559). The expansion itself is a
	// transformation of an input line, so it belongs to the shell around
	// this interpreter and is covered over a real script file in
	// cmd/koi; what is here is what a script can say and read back,
	// which was `set: cannot turn histexpand on: not implemented`.
	//
	// Both spellings, both directions, and through a function and a
	// subshell, because this option was answered from somewhere else
	// entirely until now — the same shape #576 left for `vi`.
	{`set -H; set -o | grep -E '^histexpand ' | awk '{print $2}'`, "on\n"},
	{`set -H; set +H; set -o | grep -E '^histexpand ' | awk '{print $2}'`, "off\n"},
	{`set -o histexpand; case $- in *H*) echo yes;; *) echo no;; esac`, "yes\n"},
	{`set -H; set +o histexpand; case $- in *H*) echo yes;; *) echo no;; esac`, "no\n"},
	{`case $- in *H*) echo yes;; *) echo no;; esac`, "no\n"},
	{`set -H; set +o | grep -E ' histexpand$'`, "set -o histexpand\n"},
	{`set -H; case :$SHELLOPTS: in *:histexpand:*) echo yes;; *) echo no;; esac`, "yes\n"},
	{`set -H; shopt -o histexpand >/dev/null; echo st=$?`, "st=0\n"},
	{`f() { set -H; }; f; set -o | grep -E '^histexpand ' | awk '{print $2}'`, "on\n"},
	{`(set -H); set -o | grep -E '^histexpand ' | awk '{print $2}'`, "off\n"},
	// Asserted as the answer to a probe rather than as the whole string,
	// which is #265's rule: the string carries claims koi deliberately
	// does not make, and pinning it would pin those too.
	{`set -aeH; case $- in *e*H*) echo ordered;; esac`, "ordered\n"},

	// unset
	{
		"a=1; echo $a; unset a; echo $a",
		"1\n\n",
	},
	{
		"notinpath() { echo func; }; notinpath; unset -f notinpath; notinpath",
		"func\nnotinpath: command not found\nexit status 127 #JUSTERR",
	},
	{
		"a=1; a() { echo func; }; unset -f a; echo $a",
		"1\n",
	},
	{
		"a=1; a() { echo func; }; unset -v a; a; echo $a",
		"func\n\n",
	},
	{
		"notinpath=1; notinpath() { echo func; }; notinpath; echo $notinpath; unset notinpath; notinpath; echo $notinpath; unset notinpath; notinpath",
		"func\n1\nfunc\n\nnotinpath: command not found\nexit status 127 #JUSTERR",
	},
	{
		"unset PATH; [[ $PATH == '' ]]",
		"",
	},
	{
		"readonly a=1; echo $a; unset a; echo $a",
		// The refusal is the command's, and its status says so (#535).
		// Not bash-confirmable: bash prefixes the diagnostic with
		// `bash: line 1:` and koi does not (#120), while the script's
		// own status is 0 — so neither JUSTERR nor a plain compare
		// fits.
		"1\nunset: a: cannot unset: readonly variable\n1\n #IGNORE bash prefixes the diagnostic with its own name and line",
	},
	{
		"f() { local a=1; echo $a; unset a; echo $a; }; f",
		"1\n\n",
	},
	{
		`a=b eval 'echo $a; unset a; echo $a'`,
		"b\n\n",
	},
	{
		`$(unset INTERP_GLOBAL); echo $INTERP_GLOBAL; unset INTERP_GLOBAL; echo $INTERP_GLOBAL`,
		"value\n\n",
	},
	{
		`x=orig; f() { local x=local; unset x; x=still_local; }; f; echo $x`,
		"orig\n",
	},
	{
		`x=orig; f() { local x=local; unset x; [[ -v x ]] && echo set || echo unset; }; f`,
		"unset\n",
	},
	{
		`PS3="pick one: "; select opt in foo bar baz; do echo "Selected $opt"; break; done <<< 3`,
		"1) foo\n2) bar\n3) baz\npick one: Selected baz\n",
	},
	{
		`opts=(foo bar baz); select opt in ${opts[@]}; do echo "Selected $opt"; break; done <<< 99`,
		"1) foo\n2) bar\n3) baz\n#? Selected \n",
	},
	{
		`select opt in foo; do
	case $opt in
	foo) echo "option 1"; break;;
	*) echo "invalid option $REPLY"; break;;
	esac
done <<< 2`,
		"1) foo\n#? invalid option 2\n",
	},
	{
		"select opt in a b c; do echo \"got $opt\"; if [[ $REPLY == 2 ]]; then break; fi; done <<< $'1\n2'",
		"1) a\n2) b\n3) c\n#? got a\n#? got b\n",
	},
	{
		"select opt in a b; do break; done </dev/null; echo status $?",
		"1) a\n2) b\n#? \nstatus 1\n",
	},
	{
		"select opt in a b; do echo \"got $opt\"; done <<< 2",
		"1) a\n2) b\n#? got b\n#? \nexit status 1",
	},
	{
		"select opt in a b; do break; done <<< $'\n1'",
		"1) a\n2) b\n#? 1) a\n2) b\n#? ",
	},

	// shopt
	{"set -e; shopt -o | grep -E '^(errexit|noexec)' | wc -l | tr -d ' '", "2\n"},
	{"set -e; shopt -o | grep -E '^(errexit|noexec)' | grep 'on$' | wc -l | tr -d ' '", "1\n"},
	{"set -e; shopt | grep -E '^(errexit|noexec)' | wc -l | tr -d ' '", "0\n"},
	{"shopt -s -o noexec; echo foo", ""},
	{"shopt -so noexec; echo foo", ""},
	{"shopt -u -o noexec; echo foo", "foo\n"},
	{"shopt -u globstar; shopt globstar | grep 'off$' | wc -l | tr -d ' '", "1\n"},
	{"shopt -s globstar; shopt globstar | grep 'off$' | wc -l | tr -d ' '", "0\n"},
	// lastpipe (#277): off by default as in bash, so the last pipeline
	// stage is a subshell like every other stage — before this, koi
	// answered the most famous bash gotcha un-bash-ly and `exit` in a
	// last stage took the whole shell down.
	{"echo foo | read x; echo \"x=[$x]\"", "x=[]\n"},
	{"printf 'a\\nb\\n' | while read l; do n=$((n+1)); done; echo \"n=[$n]\"", "n=[]\n"},
	{"echo | exit 3; echo after=$?", "after=3\n"},
	{"echo | cd /; [ \"$PWD\" = / ] && echo moved || echo stayed", "stayed\n"},
	{"shopt -s lastpipe; echo foo | read x; echo \"x=[$x]\"", "x=[foo]\n"},
	{"shopt -s lastpipe; printf 'a\\nb\\n' | while read l; do n=$((n+1)); done; echo \"n=[$n]\"", "n=[2]\n"},
	{"shopt -s lastpipe; shopt -u lastpipe; echo foo | read x; echo \"x=[$x]\"", "x=[]\n"},
	{"shopt lastpipe | grep 'off$' | wc -l | tr -d ' '", "1\n"},
	{"set -o pipefail; shopt -s lastpipe; false | true; echo st=$?", "st=1\n"},
	// declare/typeset behind a prefix assignment (#277): the prefix keeps
	// the word from being a keyword, so these arrive at the builtin
	// dispatch, which refused them — `ref=xxx typeset -p ref` answered
	// "unsupported builtin" while `typeset -p ref` worked.
	{"x=1 declare -p x", "declare -x x=\"1\"\n"},
	{"x=1 typeset -p x", "declare -x x=\"1\"\n"},
	{"v=1; x=2 declare -p v", "declare -- v=\"1\"\n"},
	{"x=1 declare -x y=2; declare -p y", "declare -x y=\"2\"\n"},
	{"ref=xxx typeset -p nosuch 2>/dev/null; echo st=$?", "st=1\n"},
	{"shopt extglob | grep 'off' | wc -l | tr -d ' '", "1\n"},
	{
		// off by default, as in bash 5.3 — koi had it on (#393), and a
		// default is as visible to a script as a setting. Settable
		// since #412, which is the fix it governs.
		// Padded to bash 5's twenty columns since #574, so this is
		// bash-confirmed rather than #IGNOREd.
		"shopt inherit_errexit",
		"inherit_errexit     \toff\nexit status 1",
	},
	// With no names, `-s` and `-u` filter the listing rather than
	// requesting anything, and koi printed nothing at all (#574). The
	// assertions are on what the filter must not contain, since the
	// count of options in each state is a thing koi and bash can
	// legitimately differ on while the filtering itself cannot.
	// Each state has a pair: the filter contains what it should and not
	// what it should not. Only the negative half would pass vacuously
	// against the very bug this fixes, since an empty listing contains
	// nothing either.
	{"shopt -s | grep -q 'on$'", ""},
	{"shopt -s | grep -q 'off$'", "exit status 1"},
	{"shopt -u | grep -q 'off$'", ""},
	{"shopt -u | grep -q 'on$'", "exit status 1"},
	{"shopt -s -p | grep -q '^shopt -s '", ""},
	{"shopt -s -p | grep -q '^shopt -u '", "exit status 1"},
	{"shopt -u -p | grep -q '^shopt -u '", ""},
	{"shopt -u -p | grep -q '^shopt -s '", "exit status 1"},
	{"shopt -o -s | grep -q 'on$'", ""},
	{"shopt -o -s | grep -q 'off$'", "exit status 1"},
	{"shopt -o -u | grep -q 'off$'", ""},
	{"shopt -o -u | grep -q 'on$'", "exit status 1"},
	{"shopt -s nullglob; shopt -s -p | grep -q '^shopt -s nullglob$'", ""},
	{"shopt -s nullglob; shopt -u -p | grep -q nullglob", "exit status 1"},
	{
		// Names turn it back into a request, and -p is ignored there:
		// this sets nullglob and prints nothing.
		"shopt -s -p nullglob; shopt -p nullglob",
		"shopt -s nullglob\n",
	},
	{
		// bash refuses the pair rather than letting the last one win.
		"shopt -s -u nullglob",
		"shopt: cannot set and unset shell options simultaneously\nexit status 1 #JUSTERR",
	},
	{
		"shopt -o -s pipefail; shopt -o pipefail | grep -q 'on$'",
		"",
	},
	{
		"shopt -o -u pipefail; shopt -o pipefail | grep -q 'on$'",
		"exit status 1",
	},
	{
		"shopt pipefail",
		"shopt: pipefail: invalid shell option name\nexit status 1 #JUSTERR",
	},
	{
		"shopt -s pipefail",
		"shopt: pipefail: invalid shell option name\nexit status 1 #JUSTERR",
	},
	{
		// The -o table words it differently, and *setting* an unknown
		// name through it answers 0 — odd, measured, and bash's.
		"shopt -o -s extglob",
		"shopt: extglob: invalid option name\n #JUSTERR",
	},
	{
		// bash accepts this and does not act on it either: login_shell
		// is derived, not settable, so `shopt login_shell` still says
		// off afterwards. koi refuses instead of pretending, which is
		// the same posture as every other option it does not implement.
		"shopt -s login_shell",
		"shopt: unsupported option \"login_shell\"\nexit status 1 #IGNORE",
	},
	{
		// Asking an unimplemented option for the state it is already in
		// is a request koi does satisfy, so it is not an error (#542).
		// bash is silent and answers 0.
		"shopt -s interactive_comments",
		"",
	},
	// An option whose behavior belongs to the line editor holds its bit
	// (#575): the state is real, only the acting-on-it is somewhere else.
	// Both directions, since the `-u` half is what an init script writes
	// against a default that is on.
	{"shopt -s cdspell; shopt -p cdspell", "shopt -s cdspell\n"},
	{"shopt -s cdspell; shopt -u cdspell; shopt -p cdspell", "shopt -u cdspell\nexit status 1"},
	{"shopt -u checkwinsize; shopt -p checkwinsize", "shopt -u checkwinsize\nexit status 1"},
	{"shopt -s histverify; shopt -q histverify", ""},
	{"shopt -s autocd checkjobs; shopt -p autocd; shopt -p checkjobs", "shopt -s autocd\nshopt -s checkjobs\n"},
	{
		// It reaches BASHOPTS too, since that is the same bits read a
		// second way.
		"shopt -s cdspell; case :$BASHOPTS: in *:cdspell:*) echo listed ;; esac",
		"listed\n",
	},
	{
		// xpg_echo is implemented now, so the refusal is gone and the
		// behavior is the answer: escapes are interpreted without -e
		// (#604).
		"shopt -s xpg_echo; echo 'a\\tb'",
		"a\tb\n",
	},
	{
		"shopt -u xpg_echo; echo 'a\\tb'",
		"a\\tb\n",
	},
	{
		// -E still overrides it and -e still asks for it.
		"shopt -s xpg_echo; echo -E 'a\\tb'; echo -e 'a\\tb'",
		"a\\tb\na\tb\n",
	},
	{
		// -n too, until posix mode joins it: with both on, echo
		// recognizes no options at all and prints the flag as an
		// operand. Measured against bash 5.3 both ways.
		"shopt -s xpg_echo; echo -n 'a\\tb'; echo",
		"a\tb\n",
	},
	{
		"shopt -s xpg_echo; set -o posix; echo -n 'a\\tb'",
		"-n a\tb\n",
	},
	{
		// The two spellings that reach the replacement seam move with
		// it, which is the bug #565 was opened for.
		"shopt -s xpg_echo; command echo 'a\\tb'; builtin echo 'a\\tb'",
		"a\tb\na\tb\n",
	},
	{
		// printf is untouched: its format has always expanded.
		"shopt -s xpg_echo; printf 'a\\tb\\n'",
		"a\tb\n",
	},
	{
		// A request that is satisfied is answered 0 and read back (#575).
		"shopt -s xpg_echo; echo $?; shopt -p xpg_echo; shopt -q xpg_echo; echo $?",
		"0\nshopt -s xpg_echo\n0\n",
	},
	{
		"shopt -s xpg_echo; case :$BASHOPTS: in *:xpg_echo:*) echo listed ;; esac",
		"listed\n",
	},
	{
		"shopt -u xpg_echo",
		"",
	},
	{
		"shopt -s nosuchname",
		"shopt: nosuchname: invalid shell option name\nexit status 1 #JUSTERR",
	},
	{
		"shopt -o -s nosuchname",
		"shopt: nosuchname: invalid option name\n #JUSTERR",
	},
	{
		"touch a .b ..c; shopt -u dotglob; echo *",
		"a\n",
	},
	{
		"touch a .b ..c; shopt -s dotglob; echo *",
		"..c .b a\n",
	},
	{
		"mkdir sub .sub2; touch {sub,.sub2}/{a,.b}; shopt -s globstar; shopt -u dotglob; echo **/* | sed 's@\\\\@/@g'",
		"sub sub/a\n",
	},
	// Adjacent ** collapse instead of cross-multiplying, and the
	// zero-match trailing slash appears only after a literal prefix
	// (#371): a/** answers "a/" where **/a/**, a/**/** and */** answer
	// bare names — with **/a/**'s natural duplicate kept, as bash keeps
	// it.
	{
		"mkdir -p ga/a gb/a; shopt -s globstar; printf '<%s>' **/** | sed 's@\\\\@/@g'; echo",
		"<ga><ga/a><gb><gb/a>\n",
	},
	{
		"mkdir -p ga/a; shopt -s globstar; printf '<%s>' ga/** | sed 's@\\\\@/@g'; echo",
		"<ga/><ga/a>\n",
	},
	{
		"mkdir -p ga/a; shopt -s globstar; printf '<%s>' ga/**/** | sed 's@\\\\@/@g'; echo",
		"<ga><ga/a>\n",
	},
	{
		"mkdir -p a/a b/a; shopt -s globstar; printf '<%s>' **/a/** | sed 's@\\\\@/@g'; echo",
		"<a><a/a><a/a><b/a>\n",
	},
	{
		"mkdir -p ga/a gb/a; shopt -s globstar; printf '<%s>' */** | sed 's@\\\\@/@g'; echo",
		"<ga><ga/a><gb><gb/a>\n",
	},
	{
		"mkdir sub .sub2; touch {sub,.sub2}/{a,.b}; shopt -s globstar; shopt -s dotglob; echo **/* | sed 's@\\\\@/@g'",
		".sub2 .sub2/.b .sub2/a sub sub/.b sub/a\n",
	},
	{
		// Beware that macOS file systems are by default case-preserving but
		// case-insensitive, so e.g. "touch x X" creates only one file.
		"touch a ab Ac Ad; shopt -u nocaseglob; echo a*",
		"a ab\n",
	},
	{
		"touch a ab Ac Ad; shopt -s nocaseglob; echo a*",
		"Ac Ad a ab\n",
	},
	{
		"touch a ab abB Ac Ad; shopt -u nocaseglob; echo *b",
		"ab\n",
	},
	{
		"touch a ab abB Ac Ad; shopt -s nocaseglob; echo *b",
		"ab abB\n",
	},
	// -p and -q are implemented now (#393): -p prints each option as
	// the command that would restore it, -q answers through the status
	// alone, and a named query's status is the option's state.
	{
		"shopt -p dotglob; echo p=$?",
		"shopt -u dotglob\np=1\n",
	},
	{
		"shopt -s dotglob; shopt -p dotglob; echo p=$?",
		"shopt -s dotglob\np=0\n",
	},
	{
		"shopt -q dotglob; echo q=$?; shopt -s dotglob; shopt -q dotglob; echo q=$?",
		"q=1\nq=0\n",
	},
	{
		"shopt -s dotglob; shopt -q dotglob extglob; echo q=$?",
		"q=1\n",
	},
	{
		"shopt -o -p allexport",
		"set +o allexport\nexit status 1",
	},
	{
		"shopt -o -q allexport; echo oq=$?",
		"oq=1\n",
	},
	// SHELLOPTS and BASHOPTS answer the option probe every portable
	// script writes, and were absent entirely (#396).
	{
		`echo "[$SHELLOPTS]"`,
		"[braceexpand:hashall:interactive-comments]\n",
	},
	{
		`set -e; echo "[$SHELLOPTS]"`,
		"[braceexpand:errexit:hashall:interactive-comments]\n",
	},
	{
		"shopt -s dotglob; case $BASHOPTS in *dotglob*) echo yes;; esac",
		"yes\n",
	},
	// set -k binds every assignment-shaped word, not just the leading
	// ones — and decides from what was *written*, so a quoted one and a
	// value that merely expands to an = stay arguments (#396).
	{
		`set -k; f(){ echo "c=[$c] args=[$*]"; }; f hi c=7`,
		"c=[7] args=[hi]\n",
	},
	{
		`set -k; c=1; echo hi c=7; echo "after=[$c]"`,
		"hi\nafter=[1]\n",
	},
	{
		`set -k; echo "x=1"`,
		"x=1\n",
	},
	{
		"set -o ignoreeof; echo rc=$?",
		"rc=0\n",
	},

	// $'\x{...}' and $'\cX' (#365): the brace hex form (closing brace
	// optional, value masked to a byte, empty braces a truncating NUL)
	// and control-char notation. printf's own format keeps its rules.
	{`x=$'ab\x{41}cd'; echo "$x"`, "abAcd\n"},
	{`x=$'\ca'; [ "$x" = "$(printf '\001')" ] && echo ok`, "ok\n"},
	{`x=$'\c?'; [ "$x" = "$(printf '\177')" ] && echo ok`, "ok\n"},
	{`x=$'a\x{}b'; echo "[$x]"`, "[a]\n"},
	{`x=$'a\x{4141}b'; echo "$x"`, "aAb\n"},
	{`x=$'a\x{41 b'; echo "$x"`, "aA b\n"},
	{`x=$'\c'; echo "$x"`, "\\c\n"},
	{`x=$'\u{41}'; echo "$x"`, "\\u{41}\n"},

	// Tilde positions beyond the word start (#364): after each colon in
	// an assignment value, after the = of an assignment-shaped argument,
	// at a colon-terminated prefix — and ~+/~- read PWD/OLDPWD. Results
	// are compared through $HOME so any machine confirms them.
	{`p=/bin:~/bin; [ "$p" = "/bin:$HOME/bin" ] && echo ok`, "ok\n"},
	{`[ "$(echo make FOO=~/mumble)" = "make FOO=$HOME/mumble" ] && echo ok`, "ok\n"},
	{`[ "$(echo a:~)" = "a:~" ] && echo ok`, "ok\n"},
	{`[ "$(echo ~:x)" = "$HOME:x" ] && echo ok`, "ok\n"},
	{`[ "$(echo FOO=~:~)" = "FOO=$HOME:$HOME" ] && echo ok`, "ok\n"},
	{`[ "$(echo 3foo=~)" = "3foo=~" ] && echo ok`, "ok\n"},
	{`cd /usr; cd /tmp; [ "$(echo ~- ~+)" = "/usr $(pwd)" ] && echo ok`, "ok\n"},
	{`p="pre ~"; q=x:$p:~; [ "$q" = "x:pre ~:$HOME" ] && echo ok`, "ok\n"},

	// "$@" splits at element boundaries even with text attached (#361),
	// and a quoted ${x+word} keeps that identity for a "$@" inside the
	// word (#360).
	{`n(){ printf "<%s>" "$@"; echo; }; set -- 1 2; n "x $@ y"`, "<x 1><2 y>\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; set -- 1 2; n "$@$@"`, "<1><21><2>\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; set --; n "x $@ y"`, "<x  y>\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; a=(p q); n "x ${a[@]} y"`, "<x p><q y>\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; set -- "a b" c; n "${1+$@}"`, "<a b><c>\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; set -- "a b" c; n "${1+"$@"}"`, "<a b><c>\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; set -- 1 2; IFS=:; n "x $* y"`, "<x 1:2 y>\n"},
	// A quoted ${x+word} does not tilde-expand; $* and $@ are unset with
	// no positional parameters; empty IFS keeps per-element fields for
	// unquoted list expansions and their per-element operators (#360,
	// #361).
	{`n(){ printf "<%s>" "$@"; echo; }; unset u123; n "${u123:-~}"`, "<~>\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; set --; n ${*-x}`, "<x>\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; set -- " A " " B "; IFS=; n $*`, "< A >< B >\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; set -- " A " " B "; IFS=; n ${*##}`, "< A >< B >\n"},
	{`n(){ printf "<%s>" "$@"; echo; }; unset u; n "${u:-'x'}"`, "<'x'>\n"},

	// Single quotes inside a double-quoted ${x+word} are literal text
	// (#359), and what sits between them still expands; $'..' expands
	// there, a heredoc's ${x+word} keeps the span as written, and a
	// pattern operator's quotes really do quote.
	{`echo "foo ${IFS+'bar'} baz"`, "foo 'bar' baz\n"},
	{`a=foo; echo "${IFS+'$a'}"`, "'foo'\n"},
	{`a=foo; echo "${IFS+'\$a'}"`, "'$a'\n"},
	{`unset u; echo "${u-'x'}"`, "'x'\n"},
	{`a=foo; echo "${a#'f'}"`, "oo\n"},
	{`x=1; echo ${x:+'q'}`, "q\n"},
	{"unset n; cat <<EOF\n${n-a$'\\01'b}\nEOF", "a$'\\01'b\n"},

	// The word in an unquoted ${param op word} expands in the caller's
	// context (#358): quoted nulls make fields, quoted spaces are
	// protected, and an inner "$@" splits into the parameters — the flat
	// string loses all three.
	{`n(){ echo $#; }; x=x; n ${x:+""}`, "1\n"},
	{`n(){ echo $#; }; x=x; n ${x:+'' ''}`, "2\n"},
	{`n(){ echo $#; }; x=x; set -- "" ""; n ${x+"$@"}`, "2\n"},
	{`n(){ echo "$#:$1:$2"; }; unset u; n ${u:-"a b" c}`, "2:a b:c\n"},
	{`n(){ echo $#; }; unset u; n ${u:-}`, "0\n"},
	{`x=x; echo pre${x:+a b}post`, "prea bpost\n"},
	{`n(){ echo "$#:$1"; }; x=x; n "${x:+a b}"`, "1:a b\n"},
	{`IFS=:; x=x; n(){ echo "$#:$1:$2"; }; n ${x:+:a}`, "2::a\n"},

	// Backslash quote removal outside command words (#357): an unquoted
	// \X in an assignment value, a ${...} word, a case subject, or a
	// redirect target reads back as X — while a *pattern*'s backslash
	// survives to mean a literal match.
	{`T=a\;b; echo "$T"`, "a;b\n"},
	{`unset a; printf "[%s]\n" ${a:=a\ b}; echo "a=[$a]"`, "[a]\n[b]\na=[a b]\n"},
	{`v=1; echo ${v/1/\'}`, "'\n"},
	{`case \x in \x) echo m;; *) echo n;; esac`, "m\n"},
	{`case \* in \*) echo star;; *) echo other;; esac`, "star\n"},
	{`case x in \*) echo wrong;; *) echo right;; esac`, "right\n"},
	{`echo hi > a\ b; cat "a b"`, "hi\n"},

	// IFS
	{`echo -n "$IFS"`, " \t\n"},
	{`a="x:y:z"; IFS=:; echo $a`, "x y z\n"},
	// A non-whitespace IFS delimiter delimits *empty* fields (#356):
	// adjacent delimiters do not collapse, a leading one yields an empty
	// first field, and only a trailing one yields nothing.
	{`IFS=:; x=":a::b:"; set -- $x; echo "[$#]($1)($2)($3)($4)"`, "[4]()(a)()(b)\n"},
	{`IFS=:; x=":"; set -- $x; echo "[$#]($1)"`, "[1]()\n"},
	{`IFS=": "; x="a : : b"; set -- $x; echo "[$#]($1)($2)($3)"`, "[3](a)()(b)\n"},
	{`IFS=": " read x y <<< ":a"; echo "($x)($y)"`, "()(a)\n"},
	{`IFS=: read -a A <<< ":a::b:"; echo "n=${#A[@]} [${A[0]}][${A[1]}][${A[2]}][${A[3]}]"`, "n=4 [][a][][b]\n"},
	{`IFS=: read x y z <<< "a::b"; echo "[$x][$y][$z]"`, "[a][][b]\n"},
	// With more fields than names the last name takes the rest of the
	// line as written; with the fields fitting, plain assignment strips
	// the trailing delimiter with the field it closed.
	{`IFS=: read x <<< "a:b:"; echo "[$x]"`, "[a:b:]\n"},
	{`IFS=: read x <<< "a:"; echo "[$x]"`, "[a]\n"},
	{`a=(x y z); IFS=-; echo ${a[*]}`, "x y z\n"},
	{`a=(x y z); IFS=-; echo ${a[@]}`, "x y z\n"},
	{`a=(x y z); IFS=-; echo "${a[*]}"`, "x-y-z\n"},
	{`a=(x y z); IFS=-; echo "${a[@]}"`, "x y z\n"},
	{`a="  x y z"; IFS=; echo $a`, "  x y z\n"},
	{`a=(x y z); IFS=; echo "${a[*]}"`, "xyz\n"},
	{`a=(x y z); IFS=-; echo "${!a[@]}"`, "0 1 2\n"},
	{`set -- x y z; IFS=-; echo $*`, "x y z\n"},
	{`set -- x y z; IFS=-; echo "$*"`, "x-y-z\n"},
	{`set -- x y z; IFS=; echo $*`, "x y z\n"},
	{`set -- x y z; IFS=; echo "$*"`, "xyz\n"},
	{`set -- x y z; IFS=-; a=$*; echo "$a"`, "x-y-z\n"},
	{`set -- x y z; IFS=; a=$*; echo "$a"`, "xyz\n"},
	{`a=(x y z); IFS=; echo ${a[*]}; c=${a[*]}; echo "$c"`, "x y z\nxyz\n"},
	{`a=(x y z); IFS=-; b=${a[*]}; echo "$b"`, "x-y-z\n"},
	{`set -- x y; IFS=éz; a=$*; echo "$a"`, "xéy\n"},
	{`set -- xo yo; IFS=-; a=${*%o}; echo "$a"`, "x-y\n"},
	{`a=(zo wo); IFS=-; b=${a[*]^}; echo "$b"`, "Zo-Wo\n"},
	{`a=(x y z); IFS=-; echo "${!a[*]}"`, "0-1-2\n"},
	{`INTERP_Y_1=a INTERP_Y_2=b; IFS=-; echo "${!INTERP_Y_*}"`, "INTERP_Y_1-INTERP_Y_2\n"},

	// builtin
	{"builtin", ""},
	// bash names what it refused; failing silently made `builtin ls`
	// look like a builtin that ran and printed nothing (#565).
	{"builtin noexist", "builtin: noexist: not a shell builtin\nexit status 1 #JUSTERR"},
	{"builtin echo foo", "foo\n"},
	{
		"echo() { printf 'bar\n'; }; echo foo; builtin echo foo",
		"bar\nfoo\n",
	},

	// type
	{"type", ""},
	{"type for", "for is a shell keyword\n"},
	{"type echo", "echo is a shell builtin\n"},
	{"echo() { :; }; type echo | grep 'is a function'", "echo is a function\n"},
	{"type $PATH_PROG | grep -q -E ' is (/|[A-Z]:)'", ""},
	{"type noexist", "type: noexist: not found\nexit status 1 #JUSTERR"},
	{"type -o echo", "type: invalid option \"-o\"\nexit status 2 #JUSTERR"},
	{"PATH=/; type $PATH_PROG", "type: " + pathProg + ": not found\nexit status 1 #JUSTERR"},
	{"shopt -s expand_aliases; alias interp_foo='bar baz'\ntype interp_foo", "interp_foo is aliased to `bar baz'\n"},
	{"alias interp_foo='bar baz'\ntype interp_foo", "type: interp_foo: not found\nexit status 1 #JUSTERR"},
	{"type -p $PATH_PROG | grep -q -E '^(/|[A-Z]:)'", ""},
	{"PATH=/; type -p $PATH_PROG", "exit status 1"},
	// TODO: type -P should force PATH lookup even for builtins, unlike type -p.
	{"type -P $PATH_PROG | grep -q -E '^(/|[A-Z]:)'", ""},
	{"PATH=/; type -P $PATH_PROG", "exit status 1"},
	{"shopt -s expand_aliases; alias interp_foo='bar'; type -t interp_foo", "alias\n"},
	{"type -t case", "keyword\n"},
	{"interp_foo(){ :; }; type -t interp_foo", "function\n"},
	{"type -t type", "builtin\n"},
	{"type -t $PATH_PROG", "file\n"},
	{"type -t inexisting_dfgsdgfds", "exit status 1"},

	// hash
	{"hash $PATH_PROG", ""},

	// trap
	{"trap 'echo at_exit' EXIT; true", "at_exit\n"},
	{"trap 'echo on_err' ERR; false; echo FAIL", "on_err\nFAIL\n"},
	{"trap 'echo on_err' ERR; false || true; echo OK", "OK\n"},
	{"trap 'echo at_exit' EXIT; trap - EXIT; echo OK", "OK\n"},
	{"set -e; trap 'echo A' ERR EXIT; false; echo FAIL", "A\nA\nexit status 1"},
	{"trap 'foobar' UNKNOWN", "trap: UNKNOWN: invalid signal specification\nexit status 1 #JUSTERR"},
	// $LINENO inside a trap action (#352): DEBUG and ERR count from the
	// line of the command that triggered them, EXIT from the line the
	// trap was set on, and a multi-line action counts on from its base.
	{
		"trap 'echo L=$LINENO' DEBUG\necho one\necho two",
		"L=2\none\nL=3\ntwo\n",
	},
	{
		"trap 'echo E=$LINENO' ERR\ntrue\nfalse\necho after",
		"E=3\nafter\n",
	},
	{
		"trap 'echo X=$LINENO' EXIT\ntrue\nexit 0",
		"X=1\n",
	},
	{
		// EXIT counts from the trap's own line. bash resets LINENO per
		// input unit on stdin (this harness's mode) and answers 1 here;
		// koi parses its input as one file, where bash answers 3 too.
		"true\ntrue\ntrap 'echo X=$LINENO' EXIT\ntrue\nexit 0",
		"X=3\n #IGNORE bash counts stdin lines per input unit",
	},
	{
		"trap 'echo A=$LINENO\necho B=$LINENO' DEBUG\necho one",
		"A=3\nB=4\none\n",
	},
	// An EXIT trap fired by `exit` inside a function sees that
	// function's FUNCNAME, not an emptied stack (#352).
	{
		"f(){ trap 'echo T:${FUNCNAME[0]:-none}' EXIT; exit 5; }\nf\necho never",
		"T:f\nexit status 5",
	},
	{"trap 'foobar' 99; echo st=$?", "trap: 99: invalid signal specification\nst=1\n #JUSTERR"},
	// TODO: our builtin appears to not receive the piped bytes?
	// {"trap 'echo on_err' ERR; trap | grep -q '.*echo on_err.*'", "trap -- \"echo on_err\" ERR\n"},
	{"trap 'false' ERR EXIT; false", "exit status 1"},
	// extdebug: a DEBUG trap answering nonzero cancels the command, the
	// mechanism a debugger's step/skip is built on (#355). The skipped
	// command leaves $? as 0, and its redirections never open.
	{
		"shopt -s extdebug\nskip(){ return 2; }\ntrap 'skip' DEBUG\nx=2\necho \"x is ${x:-unset}\"",
		"",
	},
	{
		"shopt -s extdebug\nskip(){ case \"$BASH_COMMAND\" in echo\\ skipme*) return 2;; esac; return 0; }\ntrap 'skip' DEBUG\nfalse\necho skipme > x1of\necho \"st=$? file=$([ -e x1of ] && echo yes || echo no)\"",
		"st=0 file=no\n",
	},
	{
		// Without extdebug, a nonzero DEBUG trap changes nothing.
		"skip(){ return 2; }\ntrap 'skip' DEBUG\necho runs",
		"runs\n",
	},
	// A `return` inside a function the trap action calls ends that
	// function — it must not be suppressed until the action runs out of
	// statements, or a trailing `return 0` overwrites the answer.
	{
		"f(){ echo a; return 2; echo b; return 0; }\ntrap 'f' DEBUG\ntrue\ntrap - DEBUG",
		"a\na\n #IGNORE bash also fires DEBUG for the trap builtin itself",
	},
	// An ERR trap set inside a subshell or a function fires for failures
	// in that scope (#354): "not inherited" restricts a parent's trap,
	// never the one the scope itself set.
	{"( trap 'echo e' ERR; false; echo after ); echo main", "e\nafter\nmain\n"},
	{"f(){ trap 'echo e' ERR; false; echo in-f; }; f; false; echo top", "e\nin-f\ne\ntop\n"},
	{"trap 'echo outer' ERR; f(){ false; echo in-f; }; f", "in-f\n"},
	{
		// A compound command whose redirection fails also fires it.
		// 2>/dev/null first: redirections apply left to right, and the
		// failing open's complaint is the shell's, so it must already be
		// redirected when the open fails.
		"( trap 'echo e' ERR; while [ -z x ]; do :; done 2>/dev/null </dev/null >/nonexistent-dir-354/f; echo after: $? )",
		"e\nafter: 1\n #IGNORE the unwritable path differs by platform",
	},
	// An EXIT trap set in a subshell runs when that subshell ends (#353),
	// whether it fell off the end, called exit, ran as a command
	// substitution, a background job, or a pipeline stage — and the
	// parent's EXIT trap never fires inside one.
	{"( trap 'echo sub' EXIT; exit 0 ); echo main", "sub\nmain\n"},
	{"( trap 'echo sub' EXIT; true ); echo main", "sub\nmain\n"},
	{"trap 'echo outer' EXIT; ( true ); echo main; trap - EXIT", "main\n"},
	{"x=$( trap 'echo ce' EXIT; echo body ); echo \"[$x]\"", "[body\nce]\n"},
	{"{ trap 'echo bgx' EXIT; true; } & wait; echo done", "bgx\ndone\n"},
	{"true | { trap 'echo p' EXIT; true; }; echo main", "p\nmain\n"},
	// `exit` inside an EXIT trap replaces the status; an ordinary
	// failing command in the action does not.
	{"( trap 'exit 9' EXIT; exit 3 ); echo st=$?", "st=9\n"},
	{"( trap 'echo t; false' EXIT; exit 3 ); echo st=$?", "t\nst=3\n"},
	{"trap 'exit 9' EXIT; exit 3", "exit status 9"},
	// A parse error in one trap callback must not disable later ones.
	{"trap '(' ERR; false; trap 'echo ok' ERR; false; :", "errortrap: error trap:1:1: `(` must be followed by a statement list\nok\n #IGNORE"},
	// On entry to a trap, "$?" is the status of the command which triggered it.
	{"trap 'echo err $?' ERR; false; echo after $?", "err 1\nafter 1\n"},
	{"trap 'echo exit $?' EXIT; false", "exit 1\nexit status 1"},
	{"trap 'echo exit $?' EXIT; true", "exit 0\n"},
	{"trap 'false; echo next $?' EXIT; true", "next 1\n"},
	{"trap 'echo err $?' ERR; trap 'echo exit $?' EXIT; false; true", "err 1\nexit 0\n"},

	// The ERR trap runs once for the command which failed, not again for each
	// compound command which propagates its status outwards.
	{"trap 'echo T' ERR; { false; }; echo end", "T\nend\n"},
	{"trap 'echo T' ERR; { { false; } }; echo end", "T\nend\n"},
	{"trap 'echo T' ERR; if true; then false; fi; echo end", "T\nend\n"},
	{"trap 'echo T' ERR; for i in 1; do false; done; echo end", "T\nend\n"},
	{"trap 'echo T' ERR; case x in x) false;; esac; echo end", "T\nend\n"},
	{"trap 'echo T' ERR; true | false; echo end", "T\nend\n"},
	{"trap 'echo T' ERR; false; false; echo end", "T\nT\nend\n"},

	// Without -E the trap is not inherited by functions or subshells, so only
	// the call itself runs it, however deeply the failure was nested.
	{"trap 'echo T' ERR; f() { false; }; f; echo end", "T\nend\n"},
	{"trap 'echo T' ERR; f() { false; true; }; f; echo end", "end\n"},
	{"trap 'echo T' ERR; g() { false; }; f() { g; }; f; echo end", "T\nend\n"},
	{"trap 'echo T' ERR; ( false ); echo end", "T\nend\n"},

	// With -E it is inherited, so each level runs it: once inside and once for
	// the call.
	{"set -E; trap 'echo T' ERR; f() { false; }; f; echo end", "T\nT\nend\n"},
	{"set -E; trap 'echo T' ERR; g() { false; }; f() { g; }; f; echo end", "T\nT\nT\nend\n"},
	{"set -E; trap 'echo T' ERR; ( false ); echo end", "T\nT\nend\n"},
	{"set -E; trap 'echo T' ERR; { false; }; echo end", "T\nend\n"},
	{"set -E; set +E; trap 'echo T' ERR; f() { false; }; f; echo end", "T\nend\n"},
	{
		// a condition suppresses the trap inside the function too
		"set -E; trap 'echo T' ERR; f() { false; }; if f; then :; fi; echo end",
		"end\n",
	},

	// -E and -T are what let the usual strict-mode header apply at all; with
	// either one refused, none of -e, -u or -o pipefail took effect.
	{"set -Eeuo pipefail; false; echo REACHED", "exit status 1"},
	{"set -eETuo pipefail; echo ok", "ok\n"},
	{"set -T; echo ok", "ok\n"},
	{"set -o errtrace; echo ok", "ok\n"},

	// PIPESTATUS
	{`false | true; echo "${PIPESTATUS[@]}"`, "1 0\n"},
	{`true | false; echo "${PIPESTATUS[@]}"`, "0 1\n"},
	{`(exit 1) | (exit 2) | (exit 3) | (exit 4); echo "${PIPESTATUS[@]}"`, "1 2 3 4\n"},
	{`false | true; echo "${PIPESTATUS[0]}/${PIPESTATUS[1]}/${#PIPESTATUS[@]}"`, "1/0/2\n"},
	{`true |& false; echo "${PIPESTATUS[@]}"`, "0 1\n"},
	{
		// a command which is not a pipeline still gets the one status
		`false; echo "${PIPESTATUS[@]}"`,
		"1\n",
	},
	{`x=1; echo "${PIPESTATUS[@]}"`, "0\n"},
	{
		// the statuses are those the commands exited with, so negating the
		// pipeline changes $? but not PIPESTATUS
		`! true | false; echo "$? ${PIPESTATUS[@]}"`,
		"0 0 1\n",
	},
	{
		// compound commands propagate the pipeline's statuses rather than
		// replacing them with their own single status
		`{ true | false; }; echo "${PIPESTATUS[@]}"`,
		"0 1\n",
	},
	// `time` and `!` are both in bash's pipeline prefix and compose in
	// either order, so `time ! cmd` is an ordinary pipeline where koi
	// answered a parse error and, parsing ahead, lost the rest of the
	// file (#702). The timing lines are dropped rather than compared:
	// they carry a clock, and what is under test is the status and the
	// fact that the line after them runs at all.
	{
		`{ time ! echo a; } >/dev/null 2>&1; echo "same=$?"`,
		"same=1\n",
	},
	{
		`{ time ! false; } >/dev/null 2>&1; echo "same=$?"`,
		"same=0\n",
	},
	{
		// The negated command really runs, side effects and all — a
		// status-only case cannot tell that from a swallowed line.
		`v=; { time ! read -r v <<< hi; } >/dev/null 2>&1; echo "same=$? v=$v"`,
		"same=1 v=hi\n",
	},
	{
		`x=; { time ! x=set; } >/dev/null 2>&1; echo "same=$? x=$x"`,
		"same=1 x=set\n",
	},
	{
		// `-p` is its own prefix and sits before the negation.
		`{ time -p ! true; } >/dev/null 2>&1; echo "same=$?"`,
		"same=1\n",
	},
	{
		// A bare `!` is a negated null command (#632), so `time !` is a
		// timed one and `time ! !` negates it twice.
		`{ time !; } >/dev/null 2>&1; echo "same=$?"`,
		"same=1\n",
	},
	{
		`{ time ! !; } >/dev/null 2>&1; echo "same=$?"`,
		"same=0\n",
	},
	{
		`{ time ! ! true; } >/dev/null 2>&1; echo "same=$?"`,
		"same=0\n",
	},
	{
		// The negation covers the whole pipeline, not its first stage.
		`{ time ! echo a | cat; } >/dev/null 2>&1; echo "same=$?"`,
		"same=1\n",
	},
	{
		`{ time ! false | true; } >/dev/null 2>&1; echo "same=$?"`,
		"same=1\n",
	},
	{
		// The other order already worked, and both nest.
		`{ ! time ! true; } >/dev/null 2>&1; echo "same=$?"`,
		"same=0\n",
	},
	{
		`{ time ! time ! true; } >/dev/null 2>&1; echo "same=$?"`,
		"same=0\n",
	},
	{
		// A `return` is not negated, measured rather than assumed.
		`f(){ time ! return 3; }; { f; } >/dev/null 2>&1; echo "same=$?"`,
		"same=3\n",
	},
	{`if true | false; then :; fi; echo "${PIPESTATUS[@]}"`, "0 1\n"},
	{`for i in 1; do true | false; done; echo "${PIPESTATUS[@]}"`, "0 1\n"},
	{
		// a function call and a subshell are each one command, so they get one
		// status however the body reached it
		`f() { true | false; }; f; echo "${PIPESTATUS[@]}"`,
		"1\n",
	},
	{`( true | false ); echo "${PIPESTATUS[@]}"`, "1\n"},
	{
		// the ERR trap's own commands must not overwrite it
		`trap 'echo T; true' ERR; true | false; echo "${PIPESTATUS[@]}"`,
		"T\n0 1\n",
	},
	{`set -o pipefail; false | true; echo "$? ${PIPESTATUS[@]}"`, "1 1 0\n"},
	{"false; trap 'echo exit $?' EXIT; true", "exit 0\n"},

	// eval
	{"eval", ""},
	{"eval ''", ""},
	{"eval echo foo", "foo\n"},
	{"eval 'echo foo'", "foo\n"},
	{"eval 'exit 1'", "exit status 1"},
	// koi-local: 2, not upstream's 1. bash answers 2 for a syntax error
	// in every non-interactive form — a script, -c, a sourced file and
	// eval alike — and koi's own `-n` check already said so (#276).
	{"eval '(x'", "eval: 1:1: reached EOF without matching `(` with `)`\nexit status 2 #JUSTERR"},
	{"set a b; eval 'echo $@'", "a b\n"},
	{"eval 'a=foo'; echo $a", "foo\n"},
	{`a=b eval "echo $a"`, "\n"},
	{`a=b eval 'echo $a'`, "b\n"},
	{`eval 'echo "\$a"'`, "$a\n"},
	{`a=b eval 'x=y eval "echo \$a \$x"'`, "b y\n"},
	{`a=b eval 'a=y eval "echo $a \$a"'`, "b y\n"},
	{"a=b eval '(echo $a)'", "b\n"},

	// source
	{
		// bash's wording and its usage line, in place of koi's
		// "source: need filename" (#604).
		"source",
		"source: filename argument required\nsource: usage: source [-p path] filename [arguments]\nexit status 2 #JUSTERR",
	},
	{
		".",
		".: filename argument required\n.: usage: . [-p path] filename [arguments]\nexit status 2 #JUSTERR",
	},
	{
		"source -x a",
		"source: -x: invalid option\nsource: usage: source [-p path] filename [arguments]\nexit status 2 #JUSTERR",
	},
	{
		"source -p",
		"source: -p: option requires an argument\nsource: usage: source [-p path] filename [arguments]\nexit status 2 #JUSTERR",
	},
	{
		// `-p path` searches an explicit list rather than $PATH, and
		// searches it whether or not sourcepath is on.
		"mkdir srcd; echo 'echo SRC' >srcd/sfile; . -p $PWD/srcd sfile",
		"SRC\n",
	},
	{
		"mkdir srcd; echo 'echo SRC' >srcd/sfile; shopt -u sourcepath; source -p $PWD/srcd sfile",
		"SRC\n",
	},
	{
		// An empty element — including the whole of `-p ''` — means the
		// current directory, and nothing else reaches it.
		"echo 'echo CWD' >sfile; . -p '' sfile",
		"CWD\n",
	},
	{
		"mkdir srcd; echo 'echo CWD' >sfile; . -p $PWD/srcd:. sfile",
		"CWD\n",
	},
	{
		// The search running out is worded differently from the plain
		// form's strerror message, and it names the builtin as called.
		"mkdir srcd; echo 'echo CWD' >sfile; . -p $PWD/srcd sfile",
		".: sfile: file not found\nexit status 1 #JUSTERR",
	},
	{
		"mkdir srcd; echo 'echo CWD' >sfile; source -p $PWD/srcd sfile",
		"source: sfile: file not found\nexit status 1 #JUSTERR",
	},
	{
		// `--` ends the options; a name with a slash is never searched.
		"echo 'echo CWD' >sfile; . -- sfile",
		"CWD\n",
	},
	{
		// sourcepath off means no $PATH search at all, which koi
		// accepted and ignored.
		"mkdir srcd; echo 'echo SRC' >srcd/sfile; PATH=$PWD/srcd:$PATH; shopt -u sourcepath; . sfile",
		"sfile: No such file or directory\nexit status 1 #JUSTERR",
	},
	{
		"mkdir srcd; echo 'echo SRC' >srcd/sfile; PATH=$PWD/srcd:$PATH; . sfile",
		"SRC\n",
	},
	{
		// posix mode drops the current-directory fallback entirely, so a
		// bare name is found on $PATH or nowhere.
		"echo 'echo CWD' >sfile; set -o posix; . sfile",
		".: sfile: file not found\nexit status 1 #JUSTERR",
	},
	{
		"echo 'echo CWD' >sfile; set -o posix; . ./sfile",
		"CWD\n",
	},
	{
		"mkdir srcd; echo 'echo SRC' >srcd/sfile; PATH=$PWD/srcd:$PATH; set -o posix; shopt -u sourcepath; . sfile",
		".: sfile: file not found\nexit status 1 #JUSTERR",
	},
	{
		"echo 'echo foo' >a; source ./a; . ./a",
		"foo\nfoo\n",
	},
	{
		"echo 'echo $@' >a; source ./a; source ./a b c; echo $@",
		"\nb c\n\n",
	},
	{
		"echo 'foo=bar' >a; source ./a; echo $foo",
		"bar\n",
	},

	// source from PATH
	{
		"mkdir test; echo 'echo foo' >test/a; PATH=$PWD/test source a; . test/a",
		"foo\nfoo\n",
	},

	// source with set and shift
	{
		"echo 'set -- d e f' >a; source ./a; echo $@",
		"d e f\n",
	},
	{
		"echo 'echo $@' >a; set -- b c; source ./a; echo $@",
		"b c\nb c\n",
	},
	{
		"echo 'echo $@' >a; set -- b c; source ./a d e; echo $@",
		"d e\nb c\n",
	},
	{
		"echo 'shift; echo $@' >a; set -- b c; source ./a d e; echo $@",
		"e\nb c\n",
	},
	{
		"echo 'shift' >a; set -- b c; source ./a; echo $@",
		"c\n",
	},
	{
		"echo 'shift; set -- $@' >a; set -- b c; source ./a d e; echo $@",
		"e\n",
	},
	{
		"echo 'set -- g f'>b; echo 'set -- d e f; echo $@; source ./b;' >a; source ./a; echo $@",
		"d e f\ng f\n",
	},
	{
		"echo 'set -- g f'>b; echo 'echo $@; set -- d e f; source ./b;' >a; source ./a b c; echo $@",
		"b c\ng f\n",
	},
	{
		"echo 'shift; echo $@' >b; echo 'shift; echo $@; source ./b' >a; source ./a b c d; echo $@",
		"c d\nd\n\n",
	},
	{
		"echo 'set -- b c d' >b; echo 'source ./b' >a; set -- a; source ./a; echo $@",
		"b c d\n",
	},
	{
		"echo 'echo $@' >b; echo 'set -- b c d; source ./b' >a; set -- a; source ./a; echo $@",
		"b c d\nb c d\n",
	},
	{
		"echo 'shift; echo $@' >b; echo 'shift; echo $@; source ./b c d' >a; set -- a b; source ./a; echo $@",
		"b\nd\nb\n",
	},
	{
		"echo 'set -- a b c' >b; echo 'echo $@; source ./b; echo $@' >a; source ./a; echo $@",
		"\na b c\na b c\n",
	},

	// indexed arrays
	{
		"a=foo; echo ${a[0]} ${a[@]} ${a[x]}; echo ${a[1]}",
		"foo foo foo\n\n",
	},
	{
		"a=(); echo ${a[0]} ${a[@]} ${a[x]} ${a[1]}",
		"\n",
	},
	{
		"a=(b c); echo $a; echo ${a[0]}; echo ${a[1]}; echo ${a[x]}",
		"b\nb\nc\nb\n",
	},
	{
		"a=(b c); echo ${a[@]}; echo ${a[*]}",
		"b c\nb c\n",
	},
	{
		"a=(1 2 3); echo ${a[2-1]}; echo $((a[1+1]))",
		"2\n3\n",
	},
	{
		"a=(1 2) x=(); a+=b x+=c; echo ${a[@]}; echo ${x[@]}",
		"1b 2\nc\n",
	},
	{
		"a=(1 2) x=(); a+=(b c) x+=(d e); echo ${a[@]}; echo ${x[@]}",
		"1 2 b c\nd e\n",
	},
	{
		"a=bbb; a+=(c d); echo ${a[@]}",
		"bbb c d\n",
	},
	{
		`a=('a  1' 'b  2'); for e in ${a[@]}; do echo "$e"; done`,
		"a\n1\nb\n2\n",
	},
	{
		`a=('a  1' 'b  2'); for e in "${a[*]}"; do echo "$e"; done`,
		"a  1 b  2\n",
	},
	{
		`a=('a  1' 'b  2'); for e in "${a[@]}"; do echo "$e"; done`,
		"a  1\nb  2\n",
	},
	{
		`declare -a a; a[0]='a  1'; a[1]='b  2'; for e in "${a[@]}"; do echo "$e"; done`,
		"a  1\nb  2\n",
	},
	{
		`a=([1]=y [0]=x); echo ${a[0]}`,
		"x\n",
	},
	{
		`a=(y); a[2]=x; echo ${a[2]}`,
		"x\n",
	},
	{
		`a="y"; a[2]=x; echo ${a[2]}`,
		"x\n",
	},
	{
		`declare -a a=(x y); echo ${a[1]}`,
		"y\n",
	},
	{
		`a=b; echo "${a[@]}"`,
		"b\n",
	},
	{
		`a=(b); echo ${a[3]}`,
		"\n",
	},
	{
		`a=(b); echo ${a[-2]}`,
		"negative array index\n #JUSTERR",
	},
	// TODO: also test with gaps in arrays.
	{
		`a=([0]=' x ' [1]=' y '); for v in "${a[@]}"; do echo "$v"; done`,
		" x \n y \n",
	},
	{
		`a=([0]=' x ' [1]=' y '); for v in "${a[*]}"; do echo "$v"; done`,
		" x   y \n",
	},
	{
		`a=([0]=' x ' [1]=' y '); for v in "${!a[@]}"; do echo "$v"; done`,
		"0\n1\n",
	},
	{
		`a=([0]=' x ' [1]=' y '); for v in "${!a[*]}"; do echo "$v"; done`,
		"0 1\n",
	},

	// associative arrays
	{
		`a=foo; echo ${a[""]} ${a["x"]}`,
		"foo foo\n",
	},
	{
		`declare -A a=(); echo ${a[0]} ${a[@]} ${a[1]} ${a["x"]}`,
		"\n",
	},
	{
		`declare -A a=([x]=b [y]=c); echo $a; echo ${a[0]}; echo ${a["x"]}; echo ${a["_"]}`,
		"\n\nb\n\n",
	},
	{
		`declare -Ag a=([x]=y); echo ${a["x"]}`,
		"y\n",
	},
	{
		`declare -A a=([x]=b [y]=c); for e in ${a[@]}; do echo $e; done | sort`,
		"b\nc\n",
	},
	{
		`declare -A a=([y]=b [x]=c); for e in ${a[*]}; do echo $e; done | sort`,
		"b\nc\n",
	},
	{
		`declare -A a=([x]=a); a["y"]=d; a["x"]=c; for e in ${a[@]}; do echo $e; done | sort`,
		"c\nd\n",
	},
	{
		`declare -A a=([x]=a); a[y]=d; a[x]=c; for e in ${a[@]}; do echo $e; done | sort`,
		"c\nd\n",
	},
	{
		// cheating a little; bash just did a=c
		`a=(["x"]=b ["y"]=c); echo ${a["y"]}`,
		"c\n",
	},
	{
		`declare -A a=(['x']=b); echo ${a['x']} ${a[$'x']} ${a[$"x"]}`,
		"b b b\n",
	},
	{
		// bash 5.1+: bare words pair up as key/value.
		`declare -A a=(one 1 two 2); for e in "${!a[@]}"; do echo "$e=${a[$e]}"; done | sort`,
		"one=1\ntwo=2\n",
	},
	{
		// An odd word out keys the empty string.
		`declare -A a=(one 1 two); echo "${a[one]}-${a[two]}."`,
		"1-.\n",
	},
	{
		`declare -A a=([k]=v); a+=(b c d e); for e in "${!a[@]}"; do echo "$e=${a[$e]}"; done | sort`,
		"b=c\nd=e\nk=v\n",
	},
	{
		`declare -A a=(one 1); a+=([one]=x [two]=y); echo ${a[one]} ${a[two]}`,
		"x y\n",
	},
	{
		`declare -A a=(one 1); a=(two 2); echo "${a[one]}${a[two]}"`,
		"2\n",
	},
	{
		// A bare word after a subscripted element is a fatal assignment error.
		`declare -A a=([k]=v one 1); echo after`,
		"a: one: must use subscript when assigning associative array\nexit status 1 #JUSTERR",
	},
	{
		// An empty key is skipped with a complaint; the rest still lands.
		`declare -A a=("" e one 1); echo st=$?; echo ${a[one]}`,
		"'': bad array subscript\nst=0\n1\n #IGNORE bash prints the error but continues identically",
	},
	{
		`a=(['x']=b); echo ${a['y']}`,
		"\n #IGNORE bash requires -A",
	},
	{
		`declare -A a=(['a  1']=' x ' ['b  2']=' y '); for v in "${a[@]}"; do echo "$v"; done | sort`,
		" x \n y \n",
	},
	{
		`declare -A a=(['a  1']=' x ' ['b  2']=' y '); for v in "${a[*]}"; do echo "$v"; done`,
		" x   y \n",
	},
	{
		`declare -A a=(['a  1']=' x ' ['b  2']=' y '); for v in "${!a[@]}"; do echo "$v"; done | sort`,
		"a  1\nb  2\n",
	},
	{
		`declare -A a=(['a  1']=' x ' ['b  2']=' y '); for v in "${!a[*]}"; do echo "$v"; done`,
		"a  1 b  2\n",
	},
	{
		`declare -A a; a[a]=x; a[b]=y; for v in "${!a[@]}"; do echo "$v"; done | sort`,
		"a\nb\n",
	},
	{
		`declare -A a; a[a]=x; a[b]=y; declare -A a; for v in "${!a[@]}"; do echo "$v"; done | sort`,
		"a\nb\n",
	},
	// weird assignments
	{"a=b; a=(c d); echo ${a[@]}", "c d\n"},
	{"a=(b c); a=d; echo ${a[@]}", "d c\n"},
	{"declare -A a=([x]=b [y]=c); a=d; for e in ${a[@]}; do echo $e; done | sort", "b\nc\nd\n"},
	{"i=3; a=b; a[i]=x; echo ${a[@]}", "b x\n"},
	{"i=3; declare a=(b); a[i]=x; echo ${!a[@]}", "0 3\n"},
	{`a=(x "" y); echo ${!a[@]}; echo "${!a[@]}"`, "0 1 2\n0 1 2\n"},
	{"a=(0 1 2 3 4 5 6 7 8 9 10); echo ${!a[@]}", "0 1 2 3 4 5 6 7 8 9 10\n"},
	{"i=3; declare -A a=(['x']=b); a[i]=x; for e in ${!a[@]}; do echo $e; done | sort", "i\nx\n"},

	// sparse indexed arrays
	{"a[5]=x; echo ${#a[@]} ${a[@]} ${!a[@]}", "1 x 5\n"},
	{"a=([5]=x [2]=y); echo ${!a[@]}; echo ${a[@]}", "2 5\ny x\n"},
	{"a=([5]=x y z); echo ${!a[@]}", "5 6 7\n"},
	{"a[5]=x; a[2]=y; declare -p a", "declare -a a=([2]=\"y\" [5]=\"x\")\n"},
	{"a[5]=x; echo ${a[0]-unset} ${a[5]}; echo \"${a[@]}\"", "unset x\nx\n"},
	{"a=(x y z); unset 'a[1]'; echo ${#a[@]} ${!a[@]} ${a[@]}", "2 0 2 x z\n"},
	{"a=(x y z); unset 'a[2]'; echo ${#a[@]} ${!a[@]} ${a[@]}", "2 0 1 x y\n"},
	{"a=(x y z); unset 'a[1]'; a+=(w); echo ${!a[@]}", "0 2 3\n"},
	{"a=(x y z); unset 'a[@]'; echo ${#a[@]}", "0\n"},
	{"a=(w x y z); i=2; unset \"a[i+1]\"; echo ${!a[@]}", "0 1 2\n"},
	{"declare -A a=([x]=1 [y]=2); unset 'a[x]'; echo ${!a[@]}", "y\n"},
	{"a=(1 2 3); a[-1]=x; echo ${a[@]}", "1 2 x\n"},
	{"a=(x); a+=([5]=z w); echo ${!a[@]}; echo ${a[@]}", "0 5 6\nx z w\n"},
	{"a=s; a+=([0]=x); echo ${a[@]}", "x\n"},
	{"a=([5]=x); a+=s; echo ${!a[@]}; echo ${a[@]}", "0 5\ns x\n"},
	{"a=([1]=one [5]=five [10]=ten); echo ${a[@]:2:2}; echo ${a[@]:5}; echo ${a[@]: -1}", "five ten\nfive ten\nten\n"},
	{"a=([2]=x [5]=y); echo \"${a[@]::1}\" \"${a[@]:0}\"", "x x y\n"},
	{"a=([2]=x [5]=y); echo $a ${a[0]-unset}", "unset\n"},
	{"a=([0]=x [5]=y); echo $a", "x\n"},
	{"a=([5]=x); echo ${a+set} ${a-unset}", "unset\n"},
	{"a=(x y); : \"${a[5]=z}\"; declare -p a", "declare -a a=([0]=\"x\" [1]=\"y\" [5]=\"z\")\n"},
	{"s=x; : \"${s[1]=z}\"; declare -p s", "declare -a s=([0]=\"x\" [1]=\"z\")\n"},
	{"declare -A m=([k]=v); : \"${m[j]=z}\"; echo ${m[j]} ${m[k]}", "z v\n"},
	{"a=([5]=b [-1]=c d); declare -p a", "declare -a a=([5]=\"c\" [6]=\"d\")\n"},
	{"a=(1 2 3); echo ${a[-1]} ${a[-3]}", "3 1\n"},
	{"a=(x); unset 'a[]'; echo $?; declare -p a", "0\ndeclare -a a=([0]=\"x\")\n"},
	{"s=x; unset 's[0]'; echo ${s-unset}", "unset\n"},
	{"s=x; unset 's[5]'; echo $s", "unset: s: not an array variable\nx\n #JUSTERR"},
	{"a=([5]=x); (a[2]=y; echo ${!a[@]}); echo ${!a[@]}", "2 5\n5\n"},
	{"a=([1]=y [0]=x); declare -p a", "declare -a a=([0]=\"x\" [1]=\"y\")\n"},
	{"declare -n r=a; a=(1 2 3); unset 'r[1]'; echo ${!a[@]}", "0 2\n"},

	// declare
	{"declare -B foo", "declare: -B: invalid option\ndeclare: usage: declare [-aAfFgiIlnrtux] [name[=value] ...] or declare -p [-aAfFilnrtux] [name ...]\nexit status 2 #JUSTERR"},
	{"a=b; declare a; echo $a; declare a=; echo $a", "b\n\n"},
	{"a=b; declare a; echo $a", "b\n"},
	{
		"declare a=b c=(1 2); echo $a; echo ${c[@]}",
		"b\n1 2\n",
	},
	{"a=x; declare $a; echo $a $x", "x\n"},
	{"a=x=y; declare $a; echo $a $x", "x=y y\n"},
	{"a='x=(y)'; declare $a; echo $a $x", "x=(y) (y)\n"},
	{"a='x=b y=c'; declare $a; echo $x $y", "b c\n"},
	// The whole operand is quoted, not the base name before the `=`
	// (#724). These three used to be `#JUSTERR`, pinning koi's answer
	// without claiming it was bash's; they are bash's now and their
	// differential cases live in TestRunnerRunConfirm.
	{"declare =bar", "declare: `=bar': not a valid identifier\nexit status 1 #JUSTERR"},
	{"declare $unset=$unset", "declare: `=': not a valid identifier\nexit status 1 #JUSTERR"},

	// export
	{"declare foo=bar; $ENV_PROG | grep '^foo='", "exit status 1"},
	{"declare -x foo=bar; $ENV_PROG | grep '^foo='", "foo=bar\n"},
	{"export foo=bar; $ENV_PROG | grep '^foo='", "foo=bar\n"},
	{"foo=bar; export foo; $ENV_PROG | grep '^foo='", "foo=bar\n"},
	{"export foo=bar; foo=baz; $ENV_PROG | grep '^foo='", "foo=baz\n"},
	{"export foo=bar; readonly foo=baz; $ENV_PROG | grep '^foo='", "foo=baz\n"},
	{"export foo=(1 2); $ENV_PROG | grep '^foo='", "exit status 1"},
	{"declare -A foo=([a]=b); export foo; $ENV_PROG | grep '^foo='", "exit status 1"},
	{"export foo=(b c); foo=x; $ENV_PROG | grep '^foo='", "exit status 1"},
	{"foo() { bar=foo; export bar; }; foo; $ENV_PROG | grep ^bar=", "bar=foo\n"},
	{"foo() { export bar; }; bar=foo; foo; $ENV_PROG | grep ^bar=", "bar=foo\n"},
	{"foo() { export bar; }; foo; bar=foo; $ENV_PROG | grep ^bar=", "bar=foo\n"},
	{"foo() { export bar=foo; }; foo; readonly bar; $ENV_PROG | grep ^bar=", "bar=foo\n"},

	// local
	{
		"local a=b",
		"local: can only be used in a function\nexit status 1 #JUSTERR",
	},
	{
		"local a=b 2>/dev/null; echo $a",
		"\n",
	},
	{
		"{ local a=b; }",
		"local: can only be used in a function\nexit status 1 #JUSTERR",
	},
	{
		// The sourced file is named, and the line with it, as bash does
		// (#571) — a diagnostic from a file the caller did not write is
		// exactly where a location earns its keep. The other two cases
		// above have no file to name, since a command string is not one.
		"echo 'local a=b' >a; source ./a",
		"./a: line 1: local: can only be used in a function\nexit status 1 #JUSTERR",
	},
	{
		"echo 'local a=b' >a; f() { source ./a; }; f; echo $a",
		"\n",
	},
	{
		"f() { local a=b; }; f; echo $a",
		"\n",
	},
	{
		"a=x; f() { local a=b; }; f; echo $a",
		"x\n",
	},
	{
		"a=x; f() { echo $a; local a=b; echo $a; }; f",
		"x\nb\n",
	},
	{
		"f1() { local a=b; }; f2() { f1; echo $a; }; f2",
		"\n",
	},
	{
		"f() { a=1; declare b=2; export c=3; readonly d=4; declare -g e=5; }; f; echo $a $b $c $d $e",
		"1 3 4 5\n",
	},
	{
		`f() { local x; [[ -v x ]] && echo set || echo unset; }; f`,
		"unset\n",
	},
	{
		`f() { local x=; [[ -v x ]] && echo set || echo unset; }; f`,
		"set\n",
	},
	{
		`export x=before; f() { local x; export x=after; $ENV_PROG | grep '^x='; }; f; echo $x`,
		"x=after\nbefore\n",
	},
	{
		"getx() { echo $X; }; f() { local X=Y; getx; echo $X; }; f",
		"Y\nY\n",
	},
	{
		"setx() { X=Y; }; f() { local X; setx; echo $X; }; f",
		"Y\n",
	},
	{
		"setx() { local X=Y; }; f() { local X; setx; echo $X; }; f",
		"\n",
	},
	{
		"setx() { declare X=Y; }; f() { local X; setx; echo $X; }; f",
		"\n",
	},
	{
		"setx() { X=Y :; }; f() { local X; setx; echo $X; }; f",
		"\n",
	},

	// unset global from inside function
	{"f() { unset foo; echo $foo; }; foo=bar; f", "\n"},
	{"f() { unset foo; }; foo=bar; f; echo $foo", "\n"},

	// name references
	// Writes through a nameref update the *target* (#277): before the
	// assignment path resolved prev, an indexed write started from the
	// nameref's own empty value and replaced the whole target array with
	// one element, and += appended to nothing.
	{`a=(1 3 5 7 9); declare -n r=a; r[2]=42; echo "${a[@]}"`, "1 3 42 7 9\n"},
	{`a=hello; declare -n r=a; r+=X; echo "$a"`, "helloX\n"},
	{`a=(1 2); declare -n r=a; r+=(3); echo "${a[@]}"`, "1 2 3\n"},
	{`declare -A m=([k]=v); declare -n r=m; r[j]=w; echo "${m[j]}"`, "w\n"},
	{`a=(1 2 3); declare -n r=a; unset "r[1]"; echo "${a[@]}"`, "1 3\n"},
	{`declare -n r=newvar; r=5; echo "$newvar"`, "5\n"},
	{"declare -n foo=bar; bar=etc; [[ -R foo ]]", ""},
	{"declare -n foo=bar; bar=etc; [ -R foo ]", ""},
	{"nameref foo=bar; bar=etc; [[ -R foo ]]", " #IGNORE"},
	{"declare foo=bar; bar=etc; [[ -R foo ]]", "exit status 1"},
	{
		"declare -n foo=bar; bar=etc; echo $foo; bar=zzz; echo $foo",
		"etc\nzzz\n",
	},
	{
		"declare -n foo=bar; bar=(x y); echo ${foo[1]}; bar=(a b); echo ${foo[1]}",
		"y\nb\n",
	},
	{
		"declare -n foo=bar; bar=etc; echo $foo; unset bar; echo $foo",
		"etc\n\n",
	},
	{
		"declare -n a1=a2 a2=a3 a3=a4; a4=x; echo $a1 $a3",
		"x x\n",
	},
	{
		"declare -n foo=bar bar=foo; echo $foo",
		"\n #IGNORE",
	},
	{
		"declare -n foo=bar; echo $foo",
		"\n",
	},
	{
		"declare -n foo=bar; echo ${!foo}",
		"bar\n",
	},
	{
		"declare -n foo=bar; bar=etc; echo $foo; echo ${!foo}",
		"etc\nbar\n",
	},
	{
		"declare -n foo=bar; bar=etc; foo=value; echo $foo; echo $bar",
		"value\nvalue\n",
	},
	{
		"declare -n foo=bar; foo=value; echo $foo; echo $bar",
		"value\nvalue\n",
	},
	{
		"declare -n foo=bar; declare foo=value; echo $foo; echo $bar",
		"value\nvalue\n",
	},
	{
		"declare -n foo=bar bar=baz; foo=value; echo $foo; echo $bar; echo $baz",
		"value\nvalue\nvalue\n",
	},
	{
		"declare -n foo=bar; set -u; echo ${foo}",
		"foo: unbound variable\nexit status 1 #JUSTERR",
	},
	{
		"declare -n foo=bar; set -u; echo ${foo:=value}; echo $foo; echo $bar",
		"value\nvalue\nvalue\n",
	},
	{
		"declare -n foo=bar; foo=value $ENV_PROG | grep '^bar='",
		"bar=value\n",
	},
	{
		"echo ${!@}-${!*}; set -- foo; echo ${!@}-${!*}-${!1}; foo=value; echo ${!@}-${!*}-${!1}",
		"-\n--\nvalue-value-value\n",
	},
	{
		"declare -n ref=arr; ref+=(x y); echo ${ref[@]} ${arr[@]}",
		"x y x y\n",
	},

	// read-only vars
	{"declare -r foo=bar; echo $foo", "bar\n"},
	{"readonly foo=bar; echo $foo", "bar\n"},
	{
		// a plain assignment to a readonly variable is fatal in bash, so
		// nothing after it runs
		`readonly v=1; v=2; echo REACHED`,
		"v: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		`readonly v=1; v+=2; echo REACHED`,
		"v: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		// including from inside a function, which ends the whole script
		`f() { v=2; echo IN; }; readonly v=1; f; echo OUT`,
		"v: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		// in a subshell it ends the subshell only
		`readonly v=1; ( v=2; echo INSUB ) 2>/dev/null; echo OUT`,
		"OUT\n",
	},
	{
		// the same error from a command prefix is not fatal, and is reported
		// once rather than again while restoring
		`readonly v=1; { v=2 true; } 2>/dev/null; echo REACHED`,
		"REACHED\n",
	},
	{
		`readonly v=1; export v=2 2>/dev/null; echo REACHED`,
		"REACHED\n",
	},
	{
		`readonly v=1; echo "[$v]"`,
		"[1]\n",
	},
	{"readonly foo=bar; export foo; echo $foo", "bar\n"},
	{"readonly foo=bar; readonly bar=foo; export foo bar; echo $bar", "foo\n"},
	{
		"a=b; a=c; echo $a; readonly a; a=d",
		"c\na: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		"declare -r foo=bar; foo=etc",
		"foo: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		"declare -r foo=bar; export foo=",
		"foo: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		"readonly foo=bar; foo=etc",
		"foo: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		"foo() { bar=foo; readonly bar; }; foo; bar=bar",
		"bar: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		"foo() { readonly bar; }; foo; bar=foo",
		"bar: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		"foo() { readonly bar=foo; }; foo; export bar; $ENV_PROG | grep '^bar='",
		"bar=foo\n",
	},

	// readonly functions (#615). Every refusal here answers 1 and lets
	// the rest of the line run, which is *not* the plain assignment's
	// abandonment above -- measured, and the reason each case keeps a
	// command after the refusal.
	{
		// The redefinition is refused and the body is unchanged. Both
		// halves matter: a test that only reads the message passes for a
		// shell that prints the refusal and writes anyway.
		"f() { echo orig; }; readonly -f f; f() { echo new; }; echo B; f",
		"f: readonly function\nB\norig\n #JUSTERR",
	},
	{
		"f() { echo orig; }; declare -fr f; f() { echo new; }; echo B; f",
		"f: readonly function\nB\norig\n #JUSTERR",
	},
	{
		"f() { echo orig; }; typeset -fr f; f() { echo new; }; echo B; f",
		"f: readonly function\nB\norig\n #JUSTERR",
	},
	{
		`f() { :; }; readonly -f f; f() { :; }; echo "stat=$?"`,
		"f: readonly function\nstat=1\n #JUSTERR",
	},
	{
		"f() { echo orig; }; readonly -f f; unset -f f; f",
		"unset: f: cannot unset: readonly function\norig\n #JUSTERR",
	},
	{
		// A bare `unset` resolves to the function when no variable holds
		// the name, so it gets the function's refusal.
		`f() { echo orig; }; readonly -f f; unset f; echo "stat=$?"; f`,
		"unset: f: cannot unset: readonly function\nstat=1\norig\n #JUSTERR",
	},
	{
		// and it carries on to the names which follow: a and c are gone
		"a() { :; }; b() { :; }; c() { :; }; readonly -f b; unset -f a b c; declare -F",
		"unset: b: cannot unset: readonly function\ndeclare -fr b\n #JUSTERR",
	},
	{
		// `+r` is the one attribute a readonly function refuses to lose
		`f() { echo orig; }; readonly -f f; declare -f +r f; echo "stat=$?"; declare -F`,
		"declare: f: readonly function\nstat=1\ndeclare -fr f\n #JUSTERR",
	},
	{
		// and only when it is readonly; on an ordinary function it is a
		// silent no-op at 0
		`f() { :; }; declare -f +r f; echo "stat=$?"; declare -F`,
		"stat=0\ndeclare -f f\n",
	},
	{
		// Re-marking is silent and 0, and the other attributes are still
		// settable on a readonly function -- measured, rather than
		// assumed from `+r`.
		`f() { :; }; readonly -f f; declare -fr f; echo "a=$?"; readonly -f f; echo "b=$?"; declare -f +x f; echo "c=$?"`,
		"a=0\nb=0\nc=0\n",
	},
	{
		`readonly -f nope; echo "stat=$?"`,
		"readonly: nope: not a function\nstat=1\n #JUSTERR",
	},
	{
		// `declare -f*` keeps its existing silent 1 for a name that is
		// not a function, where `readonly -f` names it
		`declare -fr nope; echo "s1=$?"; typeset -fr nope; echo "s2=$?"`,
		"s1=1\ns2=1\n",
	},
	{
		"a() { :; }; readonly -f a nope; declare -F",
		"readonly: nope: not a function\ndeclare -fr a\n #JUSTERR",
	},
	{
		// A value alongside -f is refused, and the wording differs by
		// variant: declare abandons the command, so g is never marked
		`f() { :; }; g() { :; }; declare -fr f=1 g; echo "stat=$?"; declare -F`,
		"declare: cannot use `-f' to make functions\nstat=1\ndeclare -f f\ndeclare -f g\n #JUSTERR",
	},
	{
		// while readonly reads the whole word as the name it cannot
		// find and carries on, so g *is* marked
		"f() { :; }; g() { :; }; readonly -f f=1 g; declare -F",
		"readonly: f=1: not a function\ndeclare -f f\ndeclare -fr g\n #JUSTERR",
	},
	{
		// -r filters the listing to the readonly functions, where koi
		// listed every one -- so this answered as if nothing were
		// readonly at all
		"f1() { :; }; f2() { :; }; readonly -f f1; declare -Fr; declare -F",
		"declare -fr f1\ndeclare -fr f1\ndeclare -f f2\n",
	},
	{
		// the attribute letters are ordered r then x, and -p is what
		// asks a *named* function for them
		"f() { :; }; readonly -f f; export -f f; declare -F f; declare -pF f; declare -F",
		"f\ndeclare -frx f\ndeclare -frx f\n",
	},
	{
		"f() { :; }; readonly -f f; declare -f f; declare -pf f",
		"f () \n{ \n    :\n}\nf () \n{ \n    :\n}\ndeclare -fr f\n",
	},
	{
		// -p also turns declare's silent 1 into a diagnostic
		`declare -pF nope; echo "stat=$?"`,
		"declare: nope: not found\nstat=1\n #JUSTERR",
	},
	{
		// The bit crosses into a subshell
		"f() { echo orig; }; readonly -f f; ( f() { echo new; }; f ); f",
		"f: readonly function\norig\norig\n #JUSTERR",
	},
	{
		// and a subshell marking one does not mark it in the parent
		"f() { echo orig; }; ( readonly -f f ); f() { echo new; }; f",
		"new\n",
	},
	{
		// A readonly function does not make the *variable* of that name
		// readonly; they are separate namespaces in bash
		`f() { echo fn; }; readonly -f f; f=hello; echo "$f"; f`,
		"hello\nfn\n",
	},

	// multiple var modes at once
	{
		"declare -r -x foo=bar; $ENV_PROG | grep '^foo='",
		"foo=bar\n",
	},
	{
		"declare -r -x foo=bar; foo=x",
		"foo: readonly variable\nexit status 1 #JUSTERR",
	},

	// globbing
	{"echo .", ".\n"},
	{"echo ..", "..\n"},
	{"echo ./.", "./.\n"},
	{
		">a.x >b.x >c.x; echo *.x; rm a.x b.x c.x",
		"a.x b.x c.x\n",
	},
	{
		`>a.x; echo '*.x' "*.x"; rm a.x`,
		"*.x *.x\n",
	},
	{
		`>a.x >b.y; echo *'.'x; rm a.x`,
		"a.x\n",
	},
	{
		`>a.x; echo *'.x' "a."* '*'.x; rm a.x`,
		"a.x a.x *.x\n",
	},
	{
		"echo *.x; echo foo *.y bar",
		"*.x\nfoo *.y bar\n",
	},
	{
		`>a.x >b.x >c.x; a=*.x; echo $a; echo "$a"`,
		"a.x b.x c.x\n*.x\n",
	},
	{
		`>a.x >b.x >c.x; a=(*.x); echo "${a[@]}"; echo ${a[1]}`,
		"a.x b.x c.x\nb.x\n",
	},
	{
		"mkdir a; >a/b.x; echo */*.x | sed 's@\\\\@/@g'; cd a; echo *.x",
		"a/b.x\nb.x\n",
	},
	{
		"mkdir -p a/b/c; echo a/* | sed 's@\\\\@/@g'",
		"a/b\n",
	},
	{
		">.hidden >a; echo *; echo .h*; rm .hidden a",
		"a\n.hidden\n",
	},
	{
		`mkdir d; >d/.hidden >d/a; set -- "$(echo d/*)" "$(echo d/.h*)"; echo ${#1} ${#2}; rm -r d`,
		"3 9\n",
	},
	{
		"mkdir -p a/b/c; echo a/** | sed 's@\\\\@/@g'",
		"a/b\n",
	},
	{
		"shopt -s globstar; mkdir -p a/b/c; echo a/** | sed 's@\\\\@/@g'",
		"a/ a/b a/b/c\n",
	},
	{
		"shopt -s globstar; mkdir -p a/b/c; echo **/c | sed 's@\\\\@/@g'",
		"a/b/c\n",
	},
	{
		"shopt -s globstar; mkdir -p a/b; touch c; echo ** | sed 's@\\\\@/@g'",
		"a a/b c\n",
	},
	{
		"shopt -s globstar; mkdir -p a/b; touch c; echo **/ | sed 's@\\\\@/@g'",
		"a/ a/b/\n",
	},
	{
		"shopt -s globstar; mkdir -p a/b/c a/d; echo ** | sed 's@\\\\@/@g'",
		"a a/b a/b/c a/d\n",
	},
	{
		"shopt -s globstar; mkdir -p a.x a/b.x a/b/c.x; echo **.x ./**.x | sed 's@\\\\@/@g'",
		"a.x ./a.x\n",
	},
	{
		"shopt -s globstar; mkdir -p a/b; touch a/b/c; echo **/* | sed 's@\\\\@/@g'",
		"a a/b a/b/c\n",
	},
	{
		"shopt -s globstar; mkdir -p b; touch x2 a b/c d x1; echo **/* | sed 's@\\\\@/@g'",
		"a b b/c d x1 x2\n",
	},
	{
		"mkdir foo; touch foo/bar; echo */bar */bar/ | sed 's@\\\\@/@g'",
		"foo/bar */bar/\n",
	},
	{
		"shopt -s nullglob; touch existing-1; echo missing-* existing-*",
		"existing-1\n",
	},
	{
		"touch ŀfoo; echo ŀ*",
		"ŀfoo\n",
	},

	// failglob aborts the input unit on a matchless pattern (#375): the
	// -c string loses its remainder and exits 1, and it outranks
	// nullglob; an invalid pattern stays a literal word instead.
	{
		"shopt -s failglob; echo missing-*; echo never",
		"no match: missing-*\nexit status 1 #JUSTERR",
	},
	{
		"shopt -s nullglob failglob; echo missing-* end; echo never",
		"no match: missing-*\nexit status 1 #JUSTERR",
	},
	{
		"shopt -s failglob; echo [x; echo after",
		"[x\nafter\n",
	},
	// GLOBIGNORE filters glob results and implies dotglob while set
	// (#375); patterns match the produced path string verbatim, so a
	// basename ignore does not reach into subdirectories.
	{
		"touch a.h a.c; GLOBIGNORE='*.h'; echo *",
		"a.c\n",
	},
	// Assigning a non-null GLOBIGNORE turns the real dotglob option on
	// — shopt reports it and shopt -u undoes it — while unsetting
	// GLOBIGNORE turns dotglob off even when it was set by hand.
	{
		"touch .h a.c; GLOBIGNORE=zz; echo *; unset GLOBIGNORE; echo *",
		".h a.c\na.c\n",
	},
	{
		"touch .h a.c; GLOBIGNORE=zz; shopt -u dotglob; echo *",
		"a.c\n",
	},
	{
		"touch .h a.c; GLOBIGNORE=zz; shopt dotglob | sed 's/[\t ][\t ]*/ /g'",
		"dotglob on\n",
	},
	{
		"touch .h a.c; shopt -s dotglob; unset GLOBIGNORE; echo *",
		"a.c\n",
	},
	{
		"mkdir d; touch d/b.h; GLOBIGNORE='*.h'; echo d/* | sed 's@\\\\@/@g'",
		"d/b.h\n",
	},
	{
		"mkdir d; touch d/b.h; GLOBIGNORE='*/*.h'; echo d/* | sed 's@\\\\@/@g'",
		"d/*\n",
	},
	// GLOBSORT reorders glob results (#375): - reverses, ties fall back
	// to name order inside the reversal, whole-string numbers sort
	// numerically ahead of everything else, and an unrecognized key —
	// its sign included — is a plain forward name sort.
	{
		"touch ga gb gc; GLOBSORT=-name; echo g*",
		"gc gb ga\n",
	},
	{
		"printf x >s1; printf xxx >s2; printf xx >s3; GLOBSORT=size; echo s*; GLOBSORT=-size; echo s*",
		"s1 s3 s2\ns2 s3 s1\n",
	},
	{
		"touch ga gb; GLOBSORT=-nonsense; echo g*",
		"ga gb\n",
	},
	{
		"touch 10 9 2x; GLOBSORT=numeric; echo *; GLOBSORT=-numeric; echo *",
		"9 10 2x\n2x 10 9\n",
	},
	{
		"touch za zb zc; GLOBSORT=size; echo z?; GLOBSORT=-size; echo z?",
		"za zb zc\nzc zb za\n",
	},
	// A leading dot is only matched by a literal dot (#376): a bracket
	// class never matches it, dotglob and GLOBIGNORE lift that.
	{
		"touch .h b; echo [!a]*",
		"b\n",
	},
	{
		"touch .h b; shopt -s dotglob; echo [!a]*",
		".h b\n",
	},
	{
		"touch .ha; echo .[gh]*",
		".ha\n",
	},
	// A bracket expression broken by an unescaped slash makes the word
	// not a pattern at all (#376, POSIX 2.13.3): it prints literally
	// even under nullglob, where an escaped slash keeps the bracket
	// valid — and unmatchable.
	{
		"shopt -s nullglob; echo [q/w] end",
		"[q/w] end\n",
	},
	{
		"shopt -s nullglob; echo [q\\/w] end",
		"end\n",
	},
	// An extglob group is a pattern even with no *?[ in sight (#375).
	{
		"shopt -s extglob\ntouch ea eb; echo @(ea|zz); echo +(e)b",
		"ea\neb\n",
	},

	// `[[ ]]` matches extended patterns whatever `shopt extglob` says,
	// because a conditional command's right-hand side is a pattern by
	// grammar rather than by option (#619). Neither of these turns the
	// option on, and bash answers both — which is why the parser's
	// extglob rule has to make an exception for a test expression rather
	// than gate every position on the option.
	{
		"[[ abc == +(a|b)c ]] && echo yes",
		"yes\n",
	},
	{
		"[[ abc == @(a)?(b)c ]] && echo yes",
		"yes\n",
	},
	{
		// An empty pattern list is a group here too, matching nothing.
		`[[ "" == @() ]] && echo yes`,
		"yes\n",
	},

	// Extended globbing via the extglob option.
	// Note how extglob affects Bash's own line-by-line parsing, so we set the option before a newline.
	{
		"shopt -s extglob\necho invalid-?([)",
		"invalid-?([)\n",
	},
	{
		"touch az a1z a12z a123z; echo a?([0-9])z",
		"extended globbing operator used without the \"extglob\" option set\n #JUSTERR",
	},

	// An extended glob group whose end bash cannot find is not a group,
	// and the operator does not merely become a literal: everything from
	// it to the end of the word is text (#676). The unterminated bracket
	// expression is *why* the end cannot be found -- it swallows the
	// closing paren -- while a terminated one inside the group is an
	// ordinary bracket, and an unterminated one at the top level leaves
	// the wildcards after it alone.
	{
		"shopt -s extglob\ntouch abc abcx bbc; echo !([*)*",
		"!([*)*\n",
	},
	{
		"shopt -s extglob\ntouch abc abcx bbc; echo +(a|b[)*",
		"+(a|b[)*\n",
	},
	{
		"shopt -s extglob\ntouch abc; echo +(a|b[c])",
		"abc\n",
	},
	{
		"shopt -s extglob\ntouch 'a[b' 'a[bz'; echo a[b*",
		"a[b a[bz\n",
	},
	{
		// The trailing `*` is text, so it matches only itself.
		"shopt -s extglob\ncase '+(a|b[)x' in +(a|b[)*) echo m;; *) echo no;; esac",
		"no\n",
	},
	{
		"shopt -s extglob\ncase '+(a|b[)*' in +(a|b[)*) echo m;; *) echo no;; esac",
		"m\n",
	},
	{
		// A wildcard *before* the operator is still a wildcard.
		"shopt -s extglob\ncase 'x+(a|b[)*' in ?+(a|b[)*) echo m;; *) echo no;; esac",
		"m\n",
	},

	// A `*` immediately followed by an extended glob group is a plain
	// star and the group's operator, never a globstar's second half
	// (#677): ab**(e|f) is ab, then *, then *(e|f).
	{
		"shopt -s extglob\ntouch abc abef; echo ab**(e|f)",
		"abc abef\n",
	},
	{
		"shopt -s extglob\ntouch abc abef; echo ab*+(e|f)",
		"abef\n",
	},
	{
		"shopt -s extglob\ntouch abc abef; echo ab?*(e|f)",
		"abc abef\n",
	},
	{
		"shopt -s extglob\ntouch a ab bar; echo **(e|f)",
		"a ab bar\n",
	},
	{
		// dotglob takes the leading-dot rule out of the way, so this
		// one is answered by the pattern package's own translation
		// rather than by the extglob matcher.
		"shopt -s extglob dotglob\ntouch abc abef; echo ab**(e|f)",
		"abc abef\n",
	},
	{
		"[[ abef == ab**(e|f) ]] && echo yes",
		"yes\n",
	},
	{
		"[[ abc == ab**(e|f) ]] && echo yes",
		"yes\n",
	},

	// Whether a pattern may match a filename beginning with a dot is
	// bash's skipname rule, and an extended glob group names the dot
	// when any one of its alternatives does (#674). Which dotfile then
	// matches is decided per position, because each alternative carries
	// the rule on its own: @(.a|*) matches .a and not .ab.
	{
		"shopt -s extglob\ntouch .foo bar; echo @(.foo)",
		".foo\n",
	},
	{
		// A negation never names the dot, whatever it holds.
		"shopt -s extglob\ntouch .foo bar; echo !(.foo)",
		"bar\n",
	},
	{
		"shopt -s extglob\ntouch .a .ab bar; echo @(.a|*)",
		".a bar\n",
	},
	{
		"shopt -s extglob\ntouch .a .ab bar; echo @(.a|!(x))",
		".a bar\n",
	},
	{
		"shopt -s extglob\ntouch .ab ab; echo @(a|.a)b",
		".ab ab\n",
	},
	{
		// dotglob retires the rule, so the second alternative matches
		// every name.
		"shopt -s extglob dotglob\ntouch .a .ab bar; echo @(.a|*)",
		".a .ab bar\n",
	},
	{
		// Only *( and ?( -- the operators that can match nothing --
		// hand the question on to the pattern after the group.
		"shopt -s extglob\ntouch .foo bar; echo *(bar).foo",
		".foo\n",
	},
	{
		"shopt -s extglob\ntouch .a bar; echo ?(x).a",
		".a\n",
	},
	{
		"shopt -s extglob\ntouch .foo bar; echo !(bar).foo",
		"!(bar).foo\n",
	},
	{
		"shopt -s extglob\ntouch .a bar; echo @(x|).a",
		"@(x|).a\n",
	},
	{
		// The pattern handed on has to name the dot literally; a
		// bracket holding one does not.
		"shopt -s extglob\ntouch .a bar; echo *(x)[.]a",
		"*(x)[.]a\n",
	},
	{
		// A plain star at the start of a name is not the same as a
		// group that matched nothing: it refuses the dot outright.
		"shopt -s extglob\ntouch .a bar; echo *.a",
		"*.a\n",
	},
	{
		// The position survives a group that matched nothing, so the
		// star after it still cannot take the dot -- .b is absent.
		"shopt -s extglob\ntouch .a .ab .b bar; echo @(|.a)*",
		".a .ab bar\n",
	},
	{
		"shopt -s extglob\ntouch .a bar; echo @(?|.?)",
		".a\n",
	},
	{
		// A dot that is not at the start of a name is an ordinary
		// character.
		"shopt -s extglob\ntouch x.a xy; echo x@(*)",
		"x.a xy\n",
	},
	{
		"shopt -s extglob\ntouch az a1z a12z a123z; echo a?([0-9])z",
		"a1z az\n",
	},
	{
		"shopt -s extglob\ntouch az a1z a12z a123z; echo a*([0-9])z",
		"a123z a12z a1z az\n",
	},
	{
		"shopt -s extglob\ntouch az a1z a12z a123z; echo a+([0-9])z",
		"a123z a12z a1z\n",
	},
	{
		"shopt -s extglob\ntouch az a1z a12z a123z; echo a@([0-9])z",
		"a1z\n",
	},
	{
		"shopt -s extglob\ntouch a{1..9}0z; echo a+(0|[1-2]|8)z",
		"a10z a20z a80z\n",
	},
	{
		"shopt -s extglob\ntouch az a1z a12z a123z; echo a!([0-9])z",
		"a123z a12z az\n",
	},
	// !(pattern) extglob negation in case and [[ ]] matching
	{
		"shopt -s extglob\ncase \"bar\" in !(foo)) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \"foo\" in !(foo)) echo match;; esac",
		"",
	},
	{
		"shopt -s extglob\ncase \"\" in !(foo)) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \"baz\" in !(foo|bar)) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \"file.tar.gz\" in !(*.sig)) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \"file.sig\" in !(*.sig)) echo match;; esac",
		"",
	},
	{
		"shopt -s extglob\ncase \"foo_xxx_baz\" in foo_!(bar)_baz) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \"foo_bar_baz\" in foo_!(bar)_baz) echo match;; esac",
		"",
	},
	{
		"shopt -s extglob\n[[ \"bar\" == !(foo) ]] && echo match",
		"match\n",
	},
	// !(...) composed with prefixes, suffixes, and other groups (#373):
	// the backtracking matcher handles what a lookahead-free regexp
	// cannot.
	{
		"shopt -s extglob\ncase \"xabab\" in *a!(b)) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \"baz\" in !(foo)!(bar)) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \".bar\" in .*!(foo)) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \".foo\" in .*!(foo)) echo match;; esac",
		"match\n",
	},
	{
		"shopt -s extglob\ncase \"bar\" in .*!(foo)) echo match;; esac",
		"",
	},
	{"shopt -s extglob\n[[ foo = !(x)* ]]; echo $?", "0\n"},
	{"shopt -s extglob\n[[ fff = *(!(f)) ]]; echo $?", "0\n"},
	{"shopt -s extglob\n[[ a.b = !(*.*).!(*.*) ]]; echo $?", "0\n"},
	{"shopt -s extglob\n[[ a.b.c = !(*.*).!(*.*) ]]; echo $?", "1\n"},
	{"shopt -s extglob\n[[ foo = +(!(f)o) ]]; echo $?", "0\n"},
	// An invalid pattern compares as its literal self.
	{`shopt -s extglob
[[ "+(a|b[" == "+(a|b[" ]] && echo eq
case "+(a|b[" in "+(a|b[") echo m;; esac`, "eq\nm\n"},
	{
		// Extended pattern matching is always available outside of pathname expansions (globbing).
		"[[ a123z == a@([0-9])z ]]; echo $?; [[ a123z == a+([0-9])z ]]; echo $?",
		"1\n0\n",
	},
	// Ensure that setting nullglob does not return invalid globs as null
	// strings.
	{
		"shopt -s nullglob; [ -n butter ] && echo bubbles",
		"bubbles\n",
	},
	{
		"cat <<EOF\n{foo,bar}\nEOF",
		"{foo,bar}\n",
	},
	{
		"cat <<EOF\n*.go\nEOF",
		"*.go\n",
	},
	{
		"mkdir -p a/b a/c; echo ./a/* | sed 's@\\\\@/@g'",
		"./a/b ./a/c\n",
	},
	{
		"mkdir -p a/b a/c d; cd d; echo ../a/* | sed 's@\\\\@/@g'",
		"../a/b ../a/c\n",
	},
	{
		"mkdir x-d1 x-d2; >x-f; echo x-*/ | sed 's@\\\\@/@g'",
		"x-d1/ x-d2/\n",
	},
	{
		"mkdir x-d1 x-d2; >x-f; echo ././x-*/// | sed 's@\\\\@/@g'",
		"././x-d1/ ././x-d2/\n",
	},
	{
		"mkdir -p x-d1/a x-d2/b; >x-f; echo x-*/* | sed 's@\\\\@/@g'",
		"x-d1/a x-d2/b\n",
	},
	{
		"mkdir -p foo/bar; ln -s foo sym; echo sy*/; echo sym/b*",
		"sym/\nsym/bar\n",
	},
	{
		">foo; ln -s foo sym; echo sy*; echo sy*/",
		"sym\nsy*/\n",
	},
	{
		"mkdir x-d; >x-f; test -d $PWD/x-*/",
		"",
	},
	{
		"mkdir dir; >dir/x-f; ln -s dir sym; cd sym; test -f $PWD/x-*",
		"",
	},

	// brace expansion; there are also some tests in the expand package
	// Braces expand before parameters, textually (#363): a brace suffix
	// on a short-form $var extends the variable's name, while ${var}
	// keeps its boundary and $1 was never a name to extend.
	{"var=baz varx=vx vary=vy; echo $var{x,y}", "vx vy\n"},
	{"var=baz; echo ${var}{x,y}", "bazx bazy\n"},
	{"a1=one a2=two; echo $a{1,2}", "one two\n"},
	{"set -- p; echo $1{x,y}", "px py\n"},
	{"vx_q=deep; v=top; echo $v{x_q,}", "deep top\n"},
	{"echo a}b", "a}b\n"},
	{"echo {a,b{c,d}", "{a,bc {a,bd\n"},
	{"echo a{b}", "a{b}\n"},
	{"echo a{à,世界}", "aà a世界\n"},
	{"echo a{b,c}d{e,f}g", "abdeg abdfg acdeg acdfg\n"},
	{"echo a{b{x,y},c}d", "abxd abyd acd\n"},
	{"echo a{1..", "a{1..\n"},
	{
		"echo {00..2}; echo {01..10}; echo {1..10..-2}; echo {10..1..2}; echo {-03..3}",
		"00 01 02\n01 02 03 04 05 06 07 08 09 10\n1 3 5 7 9\n10 8 6 4 2\n-03 -02 -01 000 001 002 003\n",
	},
	{"echo a{1..2}b{4..5}c", "a1b4c a1b5c a2b4c a2b5c\n"},
	{"echo a{c..f}", "ac ad ae af\n"},
	{"echo a{4..1..1}", "a4 a3 a2 a1\n"},
	{"b=c; echo ${b}a{4..1..1}", "ca4 ca3 ca2 ca1\n"},
	{"b=c; echo a{1,2}$b", "a1c a2c\n"},
	{"echo a{1,2}'bc'", "a1bc a2bc\n"},
	{`echo a\{1,2}b`, "a{1,2}b\n"},
	{`echo a{1,2\`, "a{1,2\\\n"},
	{`echo a{1,2\}b`, "a{1,2}b\n"},
	{`echo a{1\,2,3}b`, "a1,2b a3b\n"},
	{`echo a{1\}2,3}b`, "a1}2b a3b\n"},
	{`echo a{1\..2}b`, "a{1..2}b\n"},
	{`echo \{\{iriname\}\}`, "{{iriname}}\n"},
	{
		"echo {1..100000}",
		"brace expansion would exceed 16384 elements\n #IGNORE bash has no defensive limit below MaxInt",
	},
	{
		"echo a{0..9999999999}b",
		"brace expansion would exceed 16384 elements\n #JUSTERR bash errors with a different message",
	},

	// brace expansion in declarations
	{"declare {A,B}_VAR=1; echo $A_VAR $B_VAR", "1 1\n"},
	{"declare {x,y}=val; echo $x $y", "val val\n"},
	{"declare -x RUN_{VERY_,}EXPENSIVE_TESTS=yes; echo $RUN_EXPENSIVE_TESTS", "yes\n"},
	{"declare {A,B}_VAR; A_VAR=1; B_VAR=2; echo $A_VAR $B_VAR", "1 2\n"},
	{"declare {foo=x,bar=y}; echo $foo $bar", "x y\n"},
	{`declare foo{bar=baz`, "declare: `foo{bar=baz': not a valid identifier\nexit status 1 #JUSTERR"},
	{"{a,b}=value", "a=value: command not found\nexit status 127 #JUSTERR"},

	// tilde expansion
	{
		"[[ '~/foo' == ~/foo ]] || [[ ~/foo == '~/foo' ]]",
		"exit status 1",
	},
	{
		"case '~/foo' in ~/foo) echo match ;; esac",
		"",
	},
	{
		"a=~/foo; [[ $a == '~/foo' ]]",
		"exit status 1",
	},
	{
		`a=$(echo "~/foo"); [[ $a == '~/foo' ]]`,
		"",
	},
	{
		`HOME=/foo; rel=/bar; echo ~/bar ~/'bar' ~/"bar" ~/$rel ~/"$rel"`,
		"/foo/bar /foo/bar /foo/bar /foo//bar /foo//bar\n",
	},
	{
		`HOME=/foo; rel=/bar; echo ~'/bar' ~"/bar" ~$rel ~"/$rel"`,
		"~/bar ~/bar ~/bar ~//bar\n",
	},
	{
		`HOME=/foo; echo ~ ~/ ~/'' ~'' ~""`,
		"/foo /foo/ /foo/ ~ ~\n",
	},

	// /dev/null
	{"echo foo >/dev/null", ""},
	{"cat </dev/null", ""},

	// time - real would be slow and flaky; see TestElapsedString
	{"{ time; } |& wc | tr -s ' '", " 4 6 42\n"},
	{"{ time echo -n; } |& wc | tr -s ' '", " 4 6 42\n"},
	{"{ time -p; } |& wc | tr -s ' '", " 3 6 29\n"},
	{"{ time -p echo -n; } |& wc | tr -s ' '", " 3 6 29\n"},

	// exec
	{"exec", ""},
	{
		"exec builtin echo foo",
		"builtin: command not found\nexit status 127 #JUSTERR",
	},
	{
		"exec $GOSH_PROG 'echo foo'; echo bar",
		"foo\n",
	},
	{
		"exec -a",
		"exec: -a: option requires an argument\nexit status 2 #JUSTERR",
	},
	{
		"exec -q foo",
		"exec: invalid option \"-q\"\nexit status 2 #JUSTERR",
	},
	{
		// Flags with no command to apply to still keep this statement's
		// redirections open, as bare "exec" does.
		"exec -a name >/dev/null; echo foo",
		"",
	},

	// read
	{
		"read </dev/null",
		"exit status 1",
	},
	{
		"read 1</dev/null",
		"exit status 1",
	},
	{
		"read -X",
		"read: invalid option \"-X\"\nexit status 2 #JUSTERR",
	},
	{
		"read -rX",
		"read: invalid option \"-X\"\nexit status 2 #JUSTERR",
	},
	{
		"read 0ab",
		"read: invalid identifier \"0ab\"\nexit status 2 #JUSTERR",
	},
	{
		"read <<< foo; echo $REPLY",
		"foo\n",
	},
	{
		"read <<<'  a  b  c  '; echo \"$REPLY\"",
		"  a  b  c  \n",
	},
	{
		"read <<< 'y\nn\n'; echo $REPLY",
		"y\n",
	},
	{
		"read a_0 <<< foo; echo $a_0",
		"foo\n",
	},
	{
		"read a b <<< 'foo  bar  baz  '; echo \"$a\"; echo \"$b\"",
		"foo\nbar  baz\n",
	},
	{
		"while read a; do echo $a; done <<< 'a\nb\nc'",
		"a\nb\nc\n",
	},
	{
		"while read a b; do echo -e \"$a\n$b\"; done <<< '1 2\n3'",
		"1\n2\n3\n\n",
	},
	{
		`read a <<< '\\'; echo "$a"`,
		"\\\n",
	},
	{
		`read a <<< '\a\b\c'; echo "$a"`,
		"abc\n",
	},
	{
		"read -r a b <<< '1\\\t2'; echo $a; echo $b;",
		"1\\\n2\n",
	},
	{
		"echo line\\\ncontinuation | while read a; do echo $a; done",
		"linecontinuation\n",
	},
	{
		"read x <<< $'foo\\\\\nbar'; echo \"$x\"",
		"foobar\n",
	},
	{
		"read x <<< $'a\\\\\nb\\\\\nc'; echo \"$x\"",
		"abc\n",
	},
	{
		"read -r x <<< $'foo\\\\\nbar'; echo \"$x\"",
		"foo\\\n",
	},
	{
		"while read a; do echo $a; GOSH_CMD=print_ok $GOSH_PROG; done <<< 'a\nb\nc'",
		"a\nexec ok\nb\nexec ok\nc\nexec ok\n",
	},
	{
		"while read a; do echo $a; GOSH_CMD=print_ok $GOSH_PROG; done <<EOF\na\nb\nc\nEOF",
		"a\nexec ok\nb\nexec ok\nc\nexec ok\n",
	},
	{
		"echo file1 >f; echo file2 >>f; while read a; do echo $a; done <f",
		"file1\nfile2\n",
	},
	// TODO: our final exit status here isn't right.
	// {
	// 	"while read a; do echo $a; GOSH_CMD=print_fail $GOSH_PROG; done <<< 'a\nb\nc'",
	// 	"a\nexec fail\nb\nexec fail\nc\nexec fail\nexit status 1",
	// },
	{
		`read -r a <<< '\\'; echo "$a"`,
		"\\\\\n",
	},
	{
		"read -r a <<< '\\a\\b\\c'; echo $a",
		"\\a\\b\\c\n",
	},
	{
		"IFS=: read a b c <<< '1:2:3'; echo $a; echo $b; echo $c",
		"1\n2\n3\n",
	},
	{
		"IFS=: read a b c <<< '1\\:2:3'; echo \"$a\"; echo $b; echo $c",
		"1:2\n3\n\n",
	},
	{
		`read x <<< '  a  b  '; echo "[$x]"`,
		"[a  b]\n",
	},
	{
		`IFS=' :' read x <<< ' :a b: '; echo "[$x]"`,
		"[:a b:]\n",
	},
	{
		`IFS=: read x <<< ':a:b:'; echo "[$x]"`,
		"[:a:b:]\n",
	},
	{
		`read <<< '  a \b  '; echo "[$REPLY]"; read -r <<< ' a\b '; echo "[$REPLY]"`,
		"[  a b  ]\n[ a\\b ]\n",
	},
	{
		"read -p",
		"read: -p: option requires an argument\nexit status 2 #JUSTERR",
	},
	{
		"read -X -p",
		"read: invalid option \"-X\"\nexit status 2 #JUSTERR",
	},
	{
		"read -p 'Display me as a prompt. Continue? (y/n) ' choice <<< 'y'; echo $choice",
		"Display me as a prompt. Continue? (y/n) y\n #IGNORE bash requires a terminal",
	},
	{
		"read -r -p 'Prompt and raw flag together: ' a <<< '\\a\\b\\c'; echo $a",
		"Prompt and raw flag together: \\a\\b\\c\n #IGNORE bash requires a terminal",
	},

	// read -a
	{
		`echo "1 2 3" | { read -a arr; echo "${arr[0]} ${arr[1]} ${arr[2]}"; }`,
		"1 2 3\n",
	},
	{
		`echo "a b c" | { read -a arr; echo "${#arr[@]}"; }`,
		"3\n",
	},
	{
		`echo "" | { read -a arr; echo "${#arr[@]}"; }`,
		"0\n",
	},
	{
		`echo 'a\tb' | { read -ra arr; echo "${#arr[@]} ${arr[0]}"; }`,
		"1 a\\tb\n",
	},
	{
		"read -a",
		"read: -a: option requires an argument\nexit status 2 #JUSTERR",
	},

	// read -d
	{
		`printf 'a:b:' | { read -r -d : x; echo "[$x]"; read -r -d : y; echo "[$y]"; }`,
		"[a]\n[b]\n",
	},
	{
		// reaching the end of the input without the delimiter still assigns
		`printf 'ab' | { read -r -d : x; echo "$? [$x]"; }`,
		"1 [ab]\n",
	},
	{
		// an empty delimiter means an ASCII NUL, as used with "find -print0"
		`printf 'a\0b\0' | while read -r -d '' f; do echo "[$f]"; done`,
		"[a]\n[b]\n",
	},
	{
		// an escaped delimiter is a literal character, so it doesn't end the line
		`printf 'a\\:b:' | { read -d : x; echo "[$x]"; }`,
		"[a:b]\n",
	},
	{
		`printf 'a b:' | { read -r -a arr -d :; echo "${#arr[@]} [${arr[0]}] [${arr[1]}]"; }`,
		"2 [a] [b]\n",
	},
	{
		"read -d",
		"read: -d: option requires an argument\nexit status 2 #JUSTERR",
	},

	// read -n and read -N
	{
		`printf 'abcd\n' | { read -r -n 2 x; echo "$? [$x]"; read -r rest; echo "[$rest]"; }`,
		"0 [ab]\n[cd]\n",
	},
	{
		`printf 'ab' | { read -r -N 3 x; echo "$? [$x]"; }`,
		"1 [ab]\n",
	},
	{
		// -N reads a fixed number of characters, ignoring the delimiter
		`printf 'ab:cd' | { read -r -N 4 -d : x; echo "[$x]"; }`,
		"[ab:c]\n",
	},
	{
		// -N does no field splitting nor trimming, unlike -n
		`printf '  a b\n' | { read -N 5 x y; echo "[$x] [$y]"; }`,
		"[  a b] []\n",
	},
	{
		`printf '  a b\n' | { read -n 5 x y; echo "[$x] [$y]"; }`,
		"[a] [b]\n",
	},
	{
		// -N still counts the characters after the escapes are dropped
		`printf 'a\\bc' | { read -N 3 x; echo "[$x]"; }`,
		"[abc]\n",
	},
	// Byte-cleanliness (#377): -n and -N count characters, not bytes; a
	// byte that is not valid UTF-8 survives read and field splitting
	// untouched; a high byte works as -d's delimiter; and printf's
	// octal escapes are bytes on the wire, with overflow wrapping mod
	// 256 the way bash's do.
	{
		`read -n 5 foo <<< "абвгдежз"; echo "$foo"`,
		"абвгд\n",
	},
	{
		`read -N 3 foo <<< "абвгд"; echo "$foo"`,
		"абв\n",
	},
	{
		`printf 'B\315\n' | { IFS= read -r f; printf '%s' "$f" | wc -c | tr -d ' '; }`,
		"2\n",
	},
	{
		`printf 'x B\315 y\n' | { read -r a f b; printf '%s' "$f" | wc -c | tr -d ' '; }`,
		"2\n",
	},
	{
		`printf 'ab\200cd' | { read -rd "$(printf '\200')" s; echo "$s"; }`,
		"ab\n",
	},
	{
		`printf '\303\251' | wc -c | tr -d ' '`,
		"2\n",
	},
	{
		`[ "$(printf '\401')" = "$(printf '\001')" ] && echo wraps`,
		"wraps\n",
	},
	{
		`printf 'abc\n' | { read -r -n 0 x; echo "$? [$x]"; }`,
		"0 []\n",
	},
	{
		"read -n",
		"read: -n: option requires an argument\nexit status 2 #JUSTERR",
	},
	{
		"read -n abc",
		"read: abc: invalid number\nexit status 1 #JUSTERR",
	},
	{
		"read -N -1",
		"read: -1: invalid number\nexit status 1 #JUSTERR",
	},

	// read -s reads from the shell's stdin, which is not the process's stdin
	// under a redirect; there is no echo to suppress when it isn't a terminal.
	{
		`printf 'hi\n' | { read -r -s x; echo "[$x]"; }`,
		"[hi]\n",
	},
	{
		`a=a; echo | (read a; echo -n "$a")`,
		"",
	},
	{
		`a=b; read a < /dev/null; echo -n "$a"`,
		"",
	},
	{
		"a=c; echo x | (read a; echo -n $a)",
		"x",
	},
	{
		"a=d; echo -n y | (read a; echo -n $a)",
		"y",
	},

	// getopts
	{
		"getopts",
		"getopts: usage: getopts optstring name [arg ...]\nexit status 2",
	},
	{
		"getopts a a:b",
		"getopts: invalid identifier: \"a:b\"\nexit status 2 #JUSTERR",
	},
	{
		"getopts abc opt -a; echo $opt; $optarg",
		"a\n",
	},
	{
		"getopts abc opt -z",
		"getopts: illegal option -- \"z\"\n #IGNORE",
	},
	{
		"getopts a: opt -a",
		"getopts: option requires an argument -- \"a\"\n #IGNORE",
	},
	{
		"getopts :abc opt -z; echo $opt; echo $OPTARG",
		"?\nz\n",
	},
	{
		"getopts :a: opt -a; echo $opt; echo $OPTARG",
		":\na\n",
	},
	{
		"getopts abc opt foo -a; echo $opt; echo $OPTIND",
		"?\n1\n",
	},
	{
		"getopts abc opt -a foo; echo $opt; echo $OPTIND",
		"a\n2\n",
	},
	{
		"OPTIND=3; getopts abc opt -a -b -c; echo $opt;",
		"c\n",
	},
	{
		"OPTIND=100; getopts abc opt -a -b -c; echo $opt;",
		"?\n",
	},
	{
		"OPTIND=foo; getopts abc opt -a -b -c; echo $opt;",
		"a\n",
	},
	{
		"while getopts ab:c opt -c -b arg -a foo; do echo $opt $OPTARG $OPTIND; done",
		"c 2\nb arg 4\na 5\n",
	},
	{
		"while getopts abc opt -ba -c foo; do echo $opt $OPTARG $OPTIND; done",
		"b 1\na 2\nc 3\n",
	},
	{
		"while getopts ab: opt -a -bval -a; do echo $opt $OPTARG $OPTIND; done",
		"a 2\nb val 3\na 4\n",
	},
	{
		"while getopts b: opt -bval foo; do echo $opt $OPTARG $OPTIND; done",
		"b val 2\n",
	},
	{
		"while getopts ab: opt -ab val; do echo $opt $OPTARG $OPTIND; done",
		"a 1\nb val 3\n",
	},
	{
		"a() { while getopts abc: opt; do echo $opt $OPTARG; done }; a -a -b -c arg",
		"a\nb\nc arg\n",
	},
	// mapfile
	{
		"mapfile <<EOF\na\nb\nc\nEOF\n" + `for x in "${MAPFILE[@]}"; do echo "$x"; done`,
		"a\n\nb\n\nc\n\n",
	},
	{
		"mapfile -t <<EOF\na\nb\nc\nEOF\n" + `for x in "${MAPFILE[@]}"; do echo "$x"; done`,
		"a\nb\nc\n",
	},
	{
		"mapfile -t -d b <<EOF\nabc\nEOF\n" + `for x in "${MAPFILE[@]}"; do echo "$x"; done`,
		"a\nc\n\n",
	},
	{
		"mapfile -t butter <<EOF\na\nb\nc\nEOF\n" + `for x in "${butter[@]}"; do echo "$x"; done`,
		"a\nb\nc\n",
	},

	// The declare/readonly/nameref attribute cluster: #660, #661, #663,
	// #690, #691. Where the subject is a *state* rather than a wording,
	// the diagnostic goes to /dev/null and the case asserts the status
	// and what `declare -p` shows afterwards -- which makes it a full
	// differential case against bash, since TestRunnerRunConfirm feeds
	// bash on standard input, where bash prefixes `bash: line N:` on a
	// diagnostic and koi prefixes nothing (#120, #571). The wordings get
	// their own #JUSTERR cases below.

	// #660: an attribute that changes how the value is stored is refused
	// on a readonly variable even with nothing to assign.
	{
		"readonly V=1; declare -i V 2>/dev/null; echo rc=$?; declare -p V",
		"rc=1\ndeclare -r V=\"1\"\n",
	},
	{
		// Both polarities, and a case modification as well as the
		// integer bit.
		"readonly V=1; declare -u V 2>/dev/null; echo rc=$?; declare +i V 2>/dev/null; echo rc=$?; declare -p V",
		"rc=1\nrc=1\ndeclare -r V=\"1\"\n",
	},
	{
		// The other half of the same rule: -x, -t and a bare declaration
		// are accepted on the same readonly name, which is why the
		// refusal is per attribute rather than per naked declaration.
		"readonly V=1; declare -x V; echo rc=$?; declare -t V; echo rc=$?; declare V; echo rc=$?; declare -p V",
		"rc=0\nrc=0\nrc=0\ndeclare -rtx V=\"1\"\n",
	},
	{
		// It holds even when the attribute is already on.
		"declare -ir W=1; declare -i W 2>/dev/null; echo rc=$?; declare -p W",
		"rc=1\ndeclare -ir W=\"1\"\n",
	},
	{
		"readonly V=1; declare -a V 2>/dev/null; echo rc=$?; declare -p V",
		"rc=1\ndeclare -r V=\"1\"\n",
	},
	{
		"readonly V=1; declare -i V",
		"declare: V: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		// `+n` on a readonly variable that is not a reference has
		// nothing to detach, and is a silent no-op rather than a
		// readonly complaint.
		"readonly W=1; declare +n W; echo rc=$?; declare -p W",
		"rc=0\ndeclare -r W=\"1\"\n",
	},
	{
		// A readonly reference *with* a target keeps the attribute that
		// decides which variable a write reaches.
		"f(){ typeset q=1; typeset -n -r fr=q; typeset +n fr 2>/dev/null; echo rc=$?; typeset -p fr; }; f",
		"rc=1\ndeclare -nr fr=\"q\"\n",
	},
	{
		// A *dangling* readonly reference does lose it.
		"f(){ declare -r -n d; declare +n d; echo rc=$?; declare -p d; }; f",
		"rc=0\ndeclare -r d\n",
	},
	{
		// The write behind `+n` lands, where re-storing the old variable
		// afterwards put the previous value back over it.
		"p=1; declare +n p=2; declare -p p",
		"declare -- p=\"2\"\n",
	},

	// #661: readonly's -n is export -n's spelling, not declare's nameref.
	{
		"b5=one; declare -n f5=b5; readonly -n f5; echo rc=$?; declare -p f5 b5",
		"rc=0\ndeclare -n f5=\"b5\"\ndeclare -- b5=\"one\"\n",
	},
	{
		"v=1; readonly -n v; echo rc=$?; declare -p v",
		"rc=0\ndeclare -- v=\"1\"\n",
	},
	{
		// The value is assigned and the attribute is not.
		"readonly -n z=9; echo rc=$?; declare -p z",
		"rc=0\ndeclare -- z=\"9\"\n",
	},
	{
		// bash never takes readonly off a variable that has it, and says
		// nothing about the request.
		"readonly w=2; readonly -n w; echo rc=$?; declare -p w",
		"rc=0\ndeclare -r w=\"2\"\n",
	},
	{
		// A name it would only be taking an attribute off is not created.
		"readonly -n nope; echo rc=$?; declare -p nope 2>/dev/null; echo rc2=$?",
		"rc=0\nrc2=1\n",
	},
	{
		"readonly -a -n ar1; echo rc=$?; declare -p ar1 2>/dev/null; echo rc2=$?",
		"rc=0\nrc2=1\n",
	},
	{
		// The attribute letters are not export's or readonly's options.
		"export -i v",
		"export: -i: invalid option\nexport: usage: export [-fn] [name[=value] ...] or export -p [-f]\nexit status 2 #JUSTERR",
	},
	{
		"readonly -i v",
		"readonly: -i: invalid option\nreadonly: usage: readonly [-aAf] [name[=value] ...] or readonly -p\nexit status 2 #JUSTERR",
	},
	{
		// A `+` word is a name for export and readonly, not an option --
		// which is what kept the command's only operand.
		"export +i v 2>/dev/null; echo rc=$?; declare -p v",
		"rc=1\ndeclare -x v\n",
	},
	{
		"readonly +i k=3 2>/dev/null; echo rc=$?; declare -p k",
		"rc=1\ndeclare -r k=\"3\"\n",
	},
	{
		"readonly +i k",
		"readonly: `+i': not a valid identifier\nexit status 1 #JUSTERR",
	},
	{
		// A lone `-` is an option only for `local`.
		"declare - 2>/dev/null; echo rc=$?",
		"rc=1\n",
	},
	{
		// An invalid name is reported and the next name still declared.
		"declare 1x z=1 2>/dev/null; echo rc=$?; declare -p z",
		"rc=1\ndeclare -- z=\"1\"\n",
	},

	// #663: a reference that names itself is a warning inside a function
	// and a refusal at the top level, and the warning is followed by the
	// declaration going through.
	{
		"v=global; f(){ typeset -n v=v; v=inside; }; f 2>/dev/null; echo \"[$v]\"; declare -p v",
		"[inside]\ndeclare -- v=\"inside\"\n",
	},
	{
		// The reference survives the write, and what it stands for is
		// the variable in the enclosing scope.
		"xxx=7; f(){ typeset -n xxx=xxx; xxx=foo; declare -p xxx; }; f 2>/dev/null; echo \"[$xxx]\"",
		"declare -n xxx=\"xxx\"\n[foo]\n",
	},
	{
		// Reading *through* the reference, inside the scope that holds
		// it, answers the enclosing scope's variable rather than
		// looping: the read half of the same rule, which the write
		// cases cannot see because they read at the top level where the
		// reference is out of scope.
		"v=outer; f(){ typeset -n v=v; echo \"read=[$v]\"; }; f 2>/dev/null",
		"read=[outer]\n",
	},
	{
		// Every reader goes through the same resolution: a length, a
		// slice, a default and arithmetic.
		"v=one; f(){ typeset -n v=v; echo \"len=${#v} slice=${v:0:2} def=${v-none} sum=$((v))\"; }; f 2>/dev/null",
		"len=3 slice=on def=one sum=0\n",
	},
	{
		"f(){ typeset -n v=v; }; f",
		"typeset: warning: v: circular name reference\nwarning: v: circular name reference\n #JUSTERR",
	},
	{
		// The top level still refuses, and declares nothing.
		"declare -n v=v 2>/dev/null; echo rc=$?; declare -p v 2>/dev/null; echo rc2=$?",
		"rc=1\nrc2=1\n",
	},
	{
		// The target's base name is what is compared, and a fresh local
		// does not consult the outer variable's kind.
		"a=(0); f(){ local -n a=$1; }; f 'a[0]' 2>/dev/null; echo rc=$?",
		"rc=0\n",
	},
	{
		// The self-reference rule is checked before the already-an-array
		// one, which is bash's order.
		"y=(1); declare -n y='y[0]' 2>/dev/null; echo rc=$?; declare -p y",
		"rc=1\ndeclare -a y=([0]=\"1\")\n",
	},
	{
		// The attribute is refused and the array is still written.
		"declare -n array=(one two three) 2>/dev/null; echo rc=$?; declare -p array",
		"rc=1\ndeclare -a array=([0]=\"one\" [1]=\"two\" [2]=\"three\")\n",
	},

	// #690: a naked declaration records the name, and -p with names is a
	// request rather than a query for export and readonly.
	{
		"declare e; declare -p e; echo rc=$?",
		"declare -- e\nrc=0\n",
	},
	{
		// Declared is not set.
		`declare e; echo "${e-unset}"; echo "${e+set}"`,
		"unset\n\n",
	},
	{
		// A declared-but-unset scalar has no element 0 to carry.
		"declare a; a+=(b); declare -p a",
		"declare -a a=([0]=\"b\")\n",
	},
	{
		"a=(1); readonly a; readonly -p a; echo rc=$?",
		"rc=0\n",
	},
	{
		// It is a request: the attribute is applied, only the printing
		// is suppressed.
		"b=2; readonly -p b; echo rc=$?; declare -p b",
		"rc=0\ndeclare -r b=\"2\"\n",
	},
	{
		"c=3; export -p c; echo rc=$?; declare -p c",
		"rc=0\ndeclare -x c=\"3\"\n",
	},
	{
		// A name neither can find is not an error either.
		"readonly -p zzz; echo rc=$?; export -p yyy; echo rc2=$?",
		"rc=0\nrc2=0\n",
	},

	// #691: two attribute gaps on the shell's own variables.
	// BASH_VERSINFO's own readonly bit is not testable here: the array is
	// declared by the shell around the interpreter (internal/repl), not by
	// a runner, so its case lives in cmd/koi/shellvarattrs_test.go.
	{
		"unset BASH_SOURCE 2>/dev/null; echo rc=$?",
		"rc=1\n",
	},
	{
		// Not "the computed variables refuse unset": FUNCNAME and
		// GROUPS are unsettable, which is what makes the refusal a
		// per-name fact rather than a class.
		"unset BASH_LINENO 2>/dev/null; echo rc=$?; unset FUNCNAME; echo rc2=$?; unset GROUPS; echo rc3=$?",
		"rc=1\nrc2=0\nrc3=0\n",
	},
	{
		// -n refuses too, and the function namespace is untouched.
		"unset -n BASH_SOURCE 2>/dev/null; echo rc=$?; unset -f BASH_SOURCE; echo rc2=$?",
		"rc=1\nrc2=0\n",
	},
	{
		"unset BASH_SOURCE",
		"unset: BASH_SOURCE: cannot unset\nexit status 1 #JUSTERR",
	},

	// The listing residue that cluster left: #689, #697, #720, #722,
	// #723, #724. Same rule as above -- a case whose subject is a state
	// sends the diagnostic to /dev/null and asserts what `declare -p`
	// shows, so it is differential rather than #JUSTERR.

	// #697: -t alongside -f is the trace attribute, not a listing
	// request. It printed the function's body instead, so a script that
	// set an attribute and expected silence had its stdout corrupted at
	// status 0.
	{
		"f() { echo body; }; declare -ft f; echo rc=$?; declare -pF f",
		"rc=0\ndeclare -ft f\n",
	},
	{
		// +t takes it off, and the bare -F listing carries the letter.
		"f() { echo body; }; declare -ft f; declare -F; declare -f +t f; declare -F",
		"declare -ft f\ndeclare -f f\n",
	},
	{
		// The letters compose. `declare -frx f` applied only -x before,
		// because the chain returned at the first attribute it matched.
		"f() { :; }; declare -frtx f; declare -pF f",
		"declare -frtx f\n",
	},
	{
		// With no names, -t filters the listing, and two filters union
		// as -r and -x already did.
		"f() { :; }; g() { :; }; h() { :; }; declare -ft f; declare -fr g; declare -Ft; echo --; declare -Frt",
		"declare -ft f\n--\ndeclare -ft f\ndeclare -fr g\n",
	},
	{
		// Every -f attribute needs the function to exist, and only
		// export and readonly name what they could not find. koi was
		// silently 0 for +x and +r and named it for -x.
		"declare -ft nofunc; echo rc=$?; declare -fx nofunc 2>/dev/null; echo rc2=$?; declare -f +x nofunc; echo rc3=$?; declare -f +r nofunc; echo rc4=$?",
		"rc=1\nrc2=1\nrc3=1\nrc4=1\n",
	},
	{
		"export -nf nofunc 2>/dev/null; echo rc=$?",
		"rc=1\n",
	},
	{
		// Dropping readonly is the one refusal, and it leaves the other
		// letters of the same word unapplied.
		"f() { :; }; export -f f; readonly -f f; declare -f +r +x f 2>/dev/null; echo rc=$?; declare -pF f",
		"rc=1\ndeclare -frx f\n",
	},
	{
		// The attribute is what the DEBUG trap consults, so it changes
		// reachability rather than only what a listing reports.
		"f() { echo in-f; }; declare -ft f; trap 'echo D:$BASH_COMMAND' DEBUG; f",
		"D:f\nD:f\nD:echo in-f\nin-f\n",
	},
	{
		// Inheritance is sticky: a traced function called from an
		// untraced one inherits nothing, which is why the state is
		// recorded on entry rather than asked of the innermost frame.
		"f() { echo in-f; }; g() { echo in-g; f; }; declare -ft f; trap 'echo D:$BASH_COMMAND' DEBUG; g",
		"D:g\nin-g\nin-f\n",
	},
	{
		"f() { echo in-f; }; declare -ft f; trap 'echo RET' RETURN; f",
		"in-f\nRET\n",
	},
	{
		// And a DEBUG trap set inside a function is reachable there,
		// which is the rule RETURN already had: koi ran the rest of the
		// body untraced and started tracing only after it returned.
		"f() { trap 'echo D:$BASH_COMMAND' DEBUG; echo one; echo two; }; f",
		"D:echo one\none\nD:echo two\ntwo\n",
	},

	// #720: the shell's own numeric variables carry the integer
	// attribute, so `declare -i` lists them -- where koi listed none of
	// its own and left PPID out of every listing.
	{
		"declare -p UID EUID | sed 's/=.*//'",
		"declare -ir UID\ndeclare -ir EUID\n",
	},
	{
		"declare -p PPID OPTIND BASHPID RANDOM SRANDOM SECONDS | sed 's/=.*//'",
		"declare -ir PPID\ndeclare -i OPTIND\ndeclare -i BASHPID\ndeclare -i RANDOM\ndeclare -i SRANDOM\ndeclare -i SECONDS\n",
	},
	{
		// PPID is readonly as well, which is the half with behavior
		// under it: a write to it was accepted silently, so a script
		// clobbering the name it finds its parent by was told it
		// worked. The plain assignment runs in a subshell because it
		// abandons the input unit (#308) and would take the `echo` with
		// it.
		"( PPID=1 ) 2>/dev/null; echo rc=$?; declare PPID=1 2>/dev/null; echo rc2=$?",
		"rc=1\nrc2=1\n",
	},
	{
		// The integer bit is not cosmetic -- OPTIND's assignments are
		// arithmetic, and it survives a getopts advancing the scan.
		"OPTIND=1+1; echo $OPTIND",
		"2\n",
	},
	{
		// SECONDS is the measured exception: `declare -p SECONDS`
		// reports -i and yet `SECONDS=1+1` is not an arithmetic
		// assignment, because the bit belongs to bash's *read* function
		// rather than to the variable. A write alone never confers it.
		"SECONDS=1+1; echo $SECONDS; SECONDS=2+2; echo $SECONDS; declare -p SECONDS",
		"0\n4\ndeclare -i SECONDS=\"4\"\n",
	},
	{
		// Two assignments with no read between them stay literal, which
		// is what makes the read the thing that turns the bit on.
		"SECONDS=1+1; SECONDS=2+2; echo $SECONDS",
		"0\n",
	},
	{
		"SECONDS=10; declare -p | grep -E ' SECONDS'",
		"declare -- SECONDS=\"10\"\n",
	},
	{
		"declare -i | sed 's/=.*//'",
		"declare -i BASHPID\ndeclare -ir EUID\ndeclare -i OPTIND\ndeclare -ir PPID\ndeclare -i RANDOM\ndeclare -i SRANDOM\ndeclare -ir UID\n #IGNORE koi has no HISTCMD, which bash also lists here (#720)",
	},

	// #689: a computed variable lists with no value until something
	// reads it, because bash's listings print a cache its dynamic value
	// function fills on first use.
	{
		"declare -a | grep DIRSTACK",
		"declare -a DIRSTACK=()\n",
	},
	{
		// A read fills it, and the same listing then carries the value.
		"cd /; echo ${DIRSTACK[0]}; declare -a | grep DIRSTACK",
		"/\ndeclare -a DIRSTACK=([0]=\"/\")\n",
	},
	{
		// A *named* query counts as a read, which is why the marking
		// cannot live in the expansion path alone.
		"cd /; declare -p DIRSTACK >/dev/null; declare -a | grep DIRSTACK",
		"declare -a DIRSTACK=([0]=\"/\")\n",
	},
	{
		// So does `${x+set}`, and so does a write.
		"x=${SECONDS+set}; declare -p | grep -E ' SECONDS'",
		"declare -i SECONDS=\"0\"\n",
	},
	{
		"declare -p | grep -E ' (SECONDS|RANDOM|BASHPID|EPOCHSECONDS)'",
		"declare -i BASHPID\ndeclare -- EPOCHSECONDS\ndeclare -i RANDOM\ndeclare -- SECONDS\n",
	},
	{
		// A write to a name the shell discards does not materialize it:
		// bash still prints `declare -i BASHPID` with no value.
		"BASHPID=1; declare -p | grep -E ' BASHPID'",
		"declare -i BASHPID\n",
	},
	{
		// RANDOM and SRANDOM never get a value in a *listing* here, and
		// the reason is a side effect rather than a cache: computing one
		// draws a number, so a `declare -p` that did it would advance
		// the sequence a script seeded. bash prints its own cache for
		// RANDOM after a read, which is the stated divergence; SRANDOM
		// it never caches, so the empty form is bash's answer there.
		"declare -p | grep -E ' (RANDOM|SRANDOM)'",
		"declare -i RANDOM\ndeclare -i SRANDOM\n",
	},
	{
		// The property that matters under it: listing the shell's
		// variables must not consume a random number.
		"RANDOM=42; a=$RANDOM; declare -p >/dev/null; b=$RANDOM; RANDOM=42; c=$RANDOM; d=$RANDOM; [ \"$a\" = \"$c\" ] && [ \"$b\" = \"$d\" ] && echo seq-ok",
		"seq-ok\n",
	},
	{
		// GROUPS is the same shape and is what array.tests filters,
		// where DIRSTACK is what it does not.
		"declare -p | grep -E ' GROUPS'",
		"declare -a GROUPS=()\n",
	},

	// #722: `readonly -a NAME` and `export -a NAME` with nothing to
	// assign do not apply the array kind. The rule is per builtin, so
	// declare's own sticky attribute is asserted beside it.
	{
		"readonly -a arr; declare -p arr; readonly -A ass; declare -p ass",
		"declare -r arr\ndeclare -r ass\n",
	},
	{
		"export -a earr; declare -p earr; export -A eass; declare -p eass",
		"declare -x earr\ndeclare -x eass\n",
	},
	{
		// With a value it *is* an array in both, which is what makes the
		// gap easy to miss.
		"readonly -a arr2=(1 2); declare -p arr2; export -a earr2=(9); declare -p earr2",
		"declare -ar arr2=([0]=\"1\" [1]=\"2\")\ndeclare -ax earr2=([0]=\"9\")\n",
	},
	{
		"declare -a c; declare -p c; declare -A m; declare -p m",
		"declare -a c\ndeclare -A m\n",
	},

	// #723: a naked subscript on a readonly scalar converts it, at 0 --
	// the one shape in #660's sweep where bash is *more* permissive than
	// koi, so it is an exemption rather than a stricter rule.
	{
		"readonly V=1; declare V[2]; echo rc=$?; declare -p V",
		"rc=0\ndeclare -ar V=([0]=\"1\")\n",
	},
	{
		// The subscript's own text does not decide the kind, and a
		// readonly with no value converts to a declared-but-unset array.
		"readonly Y=4; declare Y[k]; echo rc=$?; declare -p Y; readonly Z; declare Z[1]; echo rc2=$?; declare -p Z",
		"rc=0\ndeclare -ar Y=([0]=\"4\")\nrc2=0\ndeclare -ar Z\n",
	},
	{
		// The explicit -a on the same name is still a refusal, which is
		// what makes this an exemption for the subscript alone.
		"readonly X=3; declare -a X 2>/dev/null; echo rc=$?; declare -p X",
		"rc=1\ndeclare -r X=\"3\"\n",
	},
	{
		// A subscript carrying a *value* is refused as before.
		"readonly V2=1; declare V2[3]=9 2>/dev/null; echo rc=$?; declare -p V2",
		"rc=1\ndeclare -r V2=\"1\"\n",
	},
	{
		// A name that is already an array is left alone, of either kind:
		// koi read the subscript as a request for an *indexed* array and
		// answered `cannot convert associative to indexed array` at 1.
		"declare -A m=([k]=v); declare m[z]; echo rc=$?; declare -p m",
		"rc=0\ndeclare -A m=([k]=\"v\" )\n",
	},
	{
		"declare -A M=([k]=v); readonly M; declare M[z]; echo rc=$?; readonly -a Q=(a b); declare Q[3]; echo rc2=$?; declare -p Q",
		"rc=0\nrc2=0\ndeclare -ar Q=([0]=\"a\" [1]=\"b\")\n",
	},
	{
		// Inside a function `declare` is `local`, and a fresh local of a
		// readonly name is refused -- so the conversion is a top-level
		// rule rather than a general one.
		"readonly R=5; f() { declare R[9] 2>/dev/null; echo rc=$?; }; f; declare -p R",
		"rc=1\ndeclare -r R=\"5\"\n",
	},

	// #724: the identifier refusal quotes the whole operand rather than
	// the base name, which for the empty-name shapes left koi quoting
	// nothing at all. The parse-error half of that issue is in
	// syntax/parser.go and is untouched.
	{
		"declare =bar 2>/dev/null; echo rc=$?; declare z=1; declare -p z",
		"rc=1\ndeclare -- z=\"1\"\n",
	},
	{
		"declare =bar",
		"declare: `=bar': not a valid identifier\nexit status 1 #JUSTERR",
	},
	{
		"unset x; declare $x=$x",
		"declare: `=': not a valid identifier\nexit status 1 #JUSTERR",
	},
	{
		`unset x; declare "$x"=v`,
		"declare: `=v': not a valid identifier\nexit status 1 #JUSTERR",
	},
	{
		"declare =",
		"declare: `=': not a valid identifier\nexit status 1 #JUSTERR",
	},
	{
		"export =bar",
		"export: `=bar': not a valid identifier\nexit status 1 #JUSTERR",
	},
	{
		"readonly =bar",
		"readonly: `=bar': not a valid identifier\nexit status 1 #JUSTERR",
	},

	// A taken default/alternate whose word is empty answers the empty
	// *string*, which inside double quotes is one field and not none.
	// `echo` cannot see the difference, which is why every case here
	// counts fields.
	{
		"set --; set -- \"${@}\"; echo \"a=$#\"; set --; set -- \"${@-}\"; echo \"b=$#\"; set --; set -- \"${@:-}\"; echo \"c=$#\"; set --; set -- \"${*-}\"; echo \"d=$#\"",
		"a=0\nb=1\nc=1\nd=1\n",
	},
	{
		// With one null parameter the same forms are all one field, and
		// so is a taken alternate.
		"set -- ''; set -- \"${@:-}\"; echo \"a=$#\"; set -- ''; set -- \"${@+}\"; echo \"b=$#\"; set -- ''; set -- \"${@:+}\"; echo \"c=$#\"",
		"a=1\nb=1\nc=1\n",
	},
	{
		// An alternate that is *not* taken is zero fields only when the
		// list has no elements: with a null parameter present it is the
		// empty string, one field, the way `\"\"` is.
		"set --; set -- \"${@+X}\"; echo \"a=$#\"; set -- ''; set -- \"${@:+X}\"; echo \"b=$#[$1]\"; A=(); set -- \"${A[@]+X}\"; echo \"c=$#\"; B=(''); set -- \"${B[@]:+X}\"; echo \"d=$#[$1]\"",
		"a=0\nb=1[]\nc=0\nd=1[]\n",
	},
	{
		// A list is null when the *joined* value is empty, which is not
		// the same as every element being empty: two null parameters are
		// separated by text, so the alternate is taken and the default
		// is not.
		"set -- '' ''; set -- \"${@:+X}\"; echo \"a=$#[$1]\"; set -- '' ''; set -- \"${@:-X}\"; echo \"b=$#\"; A=('' ''); set -- \"${A[@]:+X}\"; echo \"c=$#[$1]\"",
		"a=1[X]\nb=2\nc=1[X]\n",
	},
	{
		// The separator is a space for `@` and IFS for `*`, so a null
		// IFS makes `${*:+X}` null while `${@:+X}` stays non-null.
		"set -- '' ''; IFS=; set -- \"${@:+X}\"; echo \"a=$#[$1]\"; set -- '' ''; IFS=; set -- \"${*:+X}\"; echo \"b=$#[$1]\"; set -- '' ''; IFS=:; set -- \"${*:+X}\"; echo \"c=$#[$1]\"",
		"a=1[X]\nb=1[]\nc=1[X]\n",
	},

	// An assignment operator's answer is the *variable's value*, so
	// nothing inside its word is a list any more: bash joined the
	// parameters before it assigned them.
	{
		"set -- abc 'def ghi' jkl; IFS=; unset v; set -- ${v=$*}; echo \"a=$#[$1]\"; set -- abc 'def ghi' jkl; IFS=; unset v; set -- ${v=$@}; echo \"b=$#[$1]\"",
		"a=1[abcdef ghijkl]\nb=1[abc def ghi jkl]\n",
	},
	{
		// The same inside quotes, where it shows without a null IFS at
		// all: `\"${v=$@}\"` is one field however IFS reads.
		"set -- abc 'def ghi' jkl; IFS=:; unset v; set -- \"${v=$@}\"; echo \"a=$#[$1]\"; set -- abc 'def ghi' jkl; unset v; set -- x${v=$@}y; echo \"b=$#[$1]\"",
		"a=1[abc def ghi jkl]\nb=1[xabc def ghi jkly]\n",
	},
	{
		// An array's list identity goes the same way, and a quoted
		// `\"$@\"` inside the word does not save it.
		"set -- abc 'def ghi' jkl; A=(\"$@\"); IFS=; unset v; set -- ${v=${A[@]}}; echo \"a=$#[$1]\"; set -- abc 'def ghi' jkl; IFS=; unset v; set -- ${v=\"$@\"}; echo \"b=$#[$1]\"",
		"a=1[abc def ghi jkl]\nb=1[abc def ghi jkl]\n",
	},
	{
		// The operators that do *not* assign keep the list: `${v-$*}` is
		// still three fields under a null IFS, and an escape in an
		// assigned word still splits where the value does.
		"set -- abc 'def ghi' jkl; IFS=; unset v; set -- ${v-$*}; echo \"a=$#\"; IFS=' '; unset v; set -- ${v:=p\\ q}; echo \"b=$#[$1][$v]\"",
		"a=3\nb=2[p][p q]\n",
	},

	// A quoted indirect expansion whose target names a list is a list:
	// the flat answer joins the elements into one field.
	{
		"set -- a 'b c' d; foo=@; set -- \"${!foo}\"; echo \"a=$#[$2]\"; set -- a 'b c' d; foo=@; set -- ${!foo}; echo \"b=$#\"",
		"a=3[b c]\nb=4\n",
	},
	{
		"A=(x 'y z' w); foo='A[@]'; set -- \"${!foo}\"; echo \"a=$#[$2]\"; foo='A[*]'; IFS=:; set -- \"${!foo}\"; echo \"b=$#[$1]\"",
		"a=3[y z]\nb=1[x:y z:w]\n",
	},
	{
		// A target that names one value still answers as one field,
		// which is what keeps the flat path in charge of everything else.
		"set -- a 'b c' d; foo=1; set -- \"${!foo}\"; echo \"a=$#[$1]\"; A=(x 'y z'); foo='A[1]'; set -- \"${!foo}\"; echo \"b=$#[$1]\"",
		"a=1[a]\nb=1[y z]\n",
	},

	// An associative array's keys and its values come out in the same
	// order, because reading one against the other is what the two lists
	// are for. These three assert the pairing and the stability on their
	// own, which is what they were written for when koi's order was
	// sorted by key (#751) — they stay because a listing surface can
	// come apart in either way without the order itself being wrong.
	{
		// The pairing is asserted, never the absolute order: values
		// sorted independently of their keys line up plausibly and
		// wrongly, which is what this catches.
		"declare -A A=([k1]=zz [k2]=aa [k3]=mm); ks=(\"${!A[@]}\"); vs=(\"${A[@]}\"); ok=yes; for i in 0 1 2; do [[ ${A[${ks[i]}]} == ${vs[i]} ]] || ok=no; done; echo \"quoted=$ok\"; ks=(${!A[@]}); vs=(${A[@]}); ok=yes; for i in 0 1 2; do [[ ${A[${ks[i]}]} == ${vs[i]} ]] || ok=no; done; echo \"plain=$ok\"",
		"quoted=yes\nplain=yes\n",
	},
	{
		// The `[*]` forms join the same two lists, so they pair too.
		"declare -A A=([k1]=zz [k2]=aa [k3]=mm); IFS=+; ks=(${!A[*]}); vs=(${A[*]}); ok=yes; for i in 0 1 2; do [[ ${A[${ks[i]}]} == ${vs[i]} ]] || ok=no; done; echo \"star=$ok\"",
		"star=yes\n",
	},
	{
		// And the order is stable within a shell, which a Go map's
		// iteration is not: two evaluations of the same expansion must
		// agree.
		"declare -A A=([a]=1 [b]=2 [c]=3 [d]=4 [e]=5 [f]=6); x=(\"${!A[@]}\"); y=(\"${!A[@]}\"); [[ ${x[*]} == \"${y[*]}\" ]] && echo stable || echo \"unstable ${x[*]} / ${y[*]}\"",
		"stable\n",
	},

	// The order itself is bash's hash-table order now, derived by
	// measurement in expand/assocorder.go (#749). Every case below is
	// checked against real bash by TestRunnerRunConfirm, so each is a
	// measurement and not a prediction.
	{
		// The headline: two keys whose sorted order and whose hash
		// order disagree.
		"declare -A A; A[0]=aa; A[1]=bb; printf \"[%s]\" \"${A[@]}\"; echo",
		"[bb][aa]\n",
	},
	{
		// Neither sorted nor insertion order: inserted q a m, sorted
		// a m q, bash q m a.
		"declare -A A=([q]=1 [a]=2 [m]=3); echo \"${!A[@]}\"",
		"q m a\n",
	},
	{
		// Single-character keys land in descending buckets, which is the
		// shape that gave the hash away: the whole alphabet comes back
		// reversed however it went in.
		"declare -A A; for x in {a..z}; do A[$x]=1; done; echo \"${!A[@]}\"\n" +
			"declare -A B; for x in {z..a}; do B[$x]=1; done; echo \"${!B[@]}\"",
		"z y x w v u t s r q p o n m l k j i h g f e d c b a\n" +
			"z y x w v u t s r q p o n m l k j i h g f e d c b a\n",
	},
	{
		// bz, 66 and edc share a bucket, so these two are the same set
		// in the same buckets and differ only in when each key arrived:
		// a bucket lists newest first.
		"declare -A A=([bz]=1 [66]=2 [edc]=3); declare -A B=([edc]=1 [66]=2 [bz]=3); echo \"${!A[@]}\"; echo \"${!B[@]}\"",
		"edc 66 bz\nbz 66 edc\n",
	},
	{
		// Within that bucket: assigning over a key does not move it,
		// and unsetting it and assigning again does.
		"declare -A A; A[bz]=1; A[66]=2; A[edc]=3; A[bz]=9; echo \"${!A[@]}\"; unset \"A[66]\"; A[66]=7; echo \"${!A[@]}\"",
		"edc 66 bz\n66 edc bz\n",
	},
	{
		// A compound assignment inserts left to right, a repeated key
		// keeping the place its first mention gave it, and `+=` carries
		// on from the keys already there.
		"declare -A A=([bz]=1 [66]=2 [bz]=3); declare -p A; declare -A B=([bz]=1); B+=([edc]=3 [66]=2); echo \"${!B[@]}\"",
		"declare -A A=([66]=\"2\" [bz]=\"3\" )\n66 edc bz\n",
	},
	{
		// Every surface that lists the array reads the same order:
		// keys, values, @k, @K, @A and declare -p.
		"declare -A A=([a]=1 [b]=2 [c]=3 [zz]=4); echo \"${!A[@]}\"; echo \"${A[@]}\"; echo \"${A[*]}\"; echo \"${A[@]@k}\"; echo \"${A[@]@K}\"; echo \"${A[@]@A}\"; declare -p A",
		"c b a zz\n3 2 1 4\n3 2 1 4\nc 3 b 2 a 1 zz 4\nc \"3\" b \"2\" a \"1\" zz \"4\" \n" +
			"declare -A A=([c]=\"3\" [b]=\"2\" [a]=\"1\" [zz]=\"4\" )\n" +
			"declare -A A=([c]=\"3\" [b]=\"2\" [a]=\"1\" [zz]=\"4\" )\n",
	},
	{
		// A bare `set` lists arrays through its own printer, which has
		// to agree with declare -p's.
		"declare -A A=([q]=1 [a]=2 [m]=3); set | grep '^A='",
		"A=([q]=\"1\" [m]=\"3\" [a]=\"2\" )\n",
	},
	{
		// A scalar promoted to an associative array by `declare -A`
		// carries its value into key 0, and key 0 was there first: .GC
		// shares 0's bucket and sorts before it, so a promotion that
		// forgot to record the insertion would list them the other way.
		"x=hi; declare -A x; x[.GC]=1; declare -p x",
		"declare -A x=([.GC]=\"1\" [0]=\"hi\" )\n",
	},
	{
		// The table grows, and the growth is visible: 2048 keys is the
		// last count that fits the initial buckets and 2049 relays the
		// whole table, so the two orders have nothing in common.
		"declare -A A; for ((i=0;i<2048;i++)); do A[k$i]=$i; done; x=(${!A[@]}); echo \"${x[0]} ${x[1]} ${x[2046]} ${x[2047]} ${#x[@]}\"\n" +
			"declare -A B; for ((i=0;i<2049;i++)); do B[k$i]=$i; done; y=(${!B[@]}); echo \"${y[0]} ${y[1]} ${y[2047]} ${y[2048]} ${#y[@]}\"",
		"k1775 k1191 k832 k465 2048\nk1698 k1699 k1049 k1048 2049\n",
	},
}

var runTestsUnix = []runTest{
	{"[[ -n $PPID && $PPID -ge 0 ]]", ""}, // can be 0 if running as the init process

	// exec's flags, which need a program that reports its own argv[0] and
	// environment. gosh sets $0 itself, so /bin/sh is the observer here.
	{
		// -a runs one file while telling it a different argv[0], which is how
		// a multi-call binary is dispatched without a wrapper.
		"(exec -a argv0name /bin/sh -c 'echo $0')",
		"argv0name\n",
	},
	{
		// -l marks a login shell by prefixing argv[0] with a dash.
		"(exec -l /bin/sh -c 'case $0 in -*) echo dashed ;; *) echo plain ;; esac')",
		"dashed\n",
	},
	{
		// -a and -l compose: the dash goes on the overridden name.
		"(exec -l -a argv0name /bin/sh -c 'echo $0')",
		"-argv0name\n",
	},
	{
		// -c runs the command with an empty environment.
		"export FOO=bar; (exec -c /bin/sh -c 'echo ${FOO-unset}')",
		"unset\n",
	},
	{
		"export FOO=bar; (exec /bin/sh -c 'echo ${FOO-unset}')",
		"bar\n",
	},
	{
		// no root user on windows
		"[[ ~root == '~root' ]]",
		"exit status 1",
	},

	// windows does not support paths with '*'
	{
		"mkdir -p '*/a.z' 'b/a.z'; cd '*'; set -- *.z; echo $#",
		"1\n",
	},
	{
		"mkdir -p 'a-*/d'; test -d $PWD/a-*/*",
		"",
	},

	// windows does not reliably track last-access time, so -N is unix-only
	{
		">a; cat a; sleep 0.01; echo 'Hello' >> a; test -N a && echo yes",
		"yes\n",
	},
	{
		"test -N nonexistent",
		"exit status 1",
	},
	{
		">a; sleep 0.01; cat a; test -N a; echo $?",
		"1\n",
	},

	// no fifos on windows
	{
		"[ -p a ] && echo x; mkfifo a; [ -p a ] && echo y",
		"y\n",
	},
	// `read -t` on a FIFO opened read-write (#348). The runtime refuses a
	// deadline on that shape, and treating the refusal as "regular file"
	// left the read blocked until killed; it is answered with poll(2) now.
	{
		"mkfifo p; exec 9<> p; read -r -u 9 -t 0.1 x; echo \"st=$? x=[$x]\"",
		"st=142 x=[]\n",
	},
	{
		"mkfifo p; exec 9<> p; echo hi >&9; read -r -u 9 -t 1 x; echo \"st=$? x=[$x]\"",
		"st=0 x=[hi]\n",
	},
	{
		// Whatever arrived before the timeout is still assigned here too.
		"mkfifo p; exec 9<> p; printf par >&9; read -r -u 9 -t 0.1 x; echo \"st=$? x=[$x]\"",
		"st=142 x=[par]\n",
	},

	// Traps on real OS signals (#350). Each case uses a signal no other
	// case fires: these tests share one process, and a Notify fans a
	// delivery out to every runner armed for that signal. /bin/kill
	// rather than kill, which the interpreter leaves to the shell above.
	// The sleep gives Go's asynchronous signal forwarding a boundary to
	// land before; bash runs the trap before the sleep, so the visible
	// order is the same either way.
	{
		"trap 'echo t' USR1; /bin/kill -USR1 $$; sleep 0.1; echo after",
		"t\nafter\n",
	},
	{
		// The shell survives a trapped TERM instead of dying 143.
		"trap 'echo caught' TERM; /bin/kill -TERM $$; sleep 0.1; echo alive",
		"caught\nalive\n",
	},
	{
		// Control flow raised inside a signal trap propagates: this is
		// what lets `trap 'return' SIG` break a busy loop.
		"trap 'echo t; exit 3' ALRM; /bin/kill -ALRM $$; sleep 0.1; echo unreachable",
		"t\nexit status 3",
	},
	// `trap '' SIG` ignoring a signal and listing as `trap -- '' SIG...`
	// is covered in cmd/koi's builtin matrix, NOT here: signal.Ignore is
	// process-global and inherited by children, so a case ignoring a
	// signal in this shared test process makes every bash oracle spawned
	// after it list the inherited ignore — a cross-test flake that hit CI
	// on the first day (#352's PR). Subprocess tests cannot contaminate
	// each other that way.
	{
		// Signal traps are listed between EXIT and the pseudo-signals,
		// under their SIG names, and `trap -p` accepts any spec spelling.
		"trap 'echo x' hup; trap 'echo bye' 0; trap -p SIGHUP; trap",
		"trap -- 'echo x' SIGHUP\ntrap -- 'echo bye' EXIT\ntrap -- 'echo x' SIGHUP\nbye\n",
	},
	{
		// Numeric specs resolve to the signal, and `trap - N` restores
		// the default.
		"trap 'echo z' 2; trap -p INT; trap - 2; trap -p INT; echo done",
		"trap -- 'echo z' SIGINT\ndone\n",
	},
	{
		"[[ -p a ]] && echo x; mkfifo a; [[ -p a ]] && echo y",
		"y\n",
	},

	{"sh() { :; }; sh -c 'echo foo'", ""},
	{"sh() { :; }; command sh -c 'echo foo'", "foo\n"},

	// files without a shebang line are run as shell scripts; see issue #1065
	{
		"echo 'echo foo' >a; chmod +x a; ./a",
		"foo\n",
	},
	{
		"echo 'echo $#: $1' >a; chmod +x a; ./a one two",
		"2: one\n",
	},
	{
		"echo 'echo \"[$foo][$bar]\"' >a; chmod +x a; foo=1; export bar=2; ./a",
		"[][2]\n",
	},
	{
		"echo 'exit 5' >a; chmod +x a; ./a",
		"exit status 5",
	},
	{
		"printf '\\0\\n' >a; chmod +x a; ./a",
		"./a: cannot execute binary file\nexit status 126 #JUSTERR",
	},
	{
		"echo 'if' >a; chmod +x a; ./a",
		"./a:1:1: `if` must be followed by a statement list\nexit status 2 #JUSTERR",
	},

	// chmod is practically useless on Windows
	{
		"[ -x a ] && echo x; >a; chmod 0755 a; [ -x a ] && echo y",
		"y\n",
	},
	{
		"[[ -x a ]] && echo x; >a; chmod 0755 a; [[ -x a ]] && echo y",
		"y\n",
	},
	{
		">a; [ -k a ] && echo x; chmod +t a; [ -k a ] && echo y",
		"y\n",
	},
	{
		">a; [ -u a ] && echo x; chmod u+s a; [ -u a ] && echo y",
		"y\n",
	},
	{
		">a; [ -g a ] && echo x; chmod g+s a; [ -g a ] && echo y",
		"y\n",
	},
	{
		">a; [[ -k a ]] && echo x; chmod +t a; [[ -k a ]] && echo y",
		"y\n",
	},
	{
		">a; [[ -u a ]] && echo x; chmod u+s a; [[ -u a ]] && echo y",
		"y\n",
	},
	{
		">a; [[ -g a ]] && echo x; chmod g+s a; [[ -g a ]] && echo y",
		"y\n",
	},
	{
		`mkdir a; chmod 0100 a; cd a`,
		"",
	},
	// Note that these will succeed if we're root.
	{
		`mkdir a; chmod 0000 a; cd a`,
		"cd: a: Permission denied\nexit status 1 #JUSTERR",
	},
	{
		`mkdir a; chmod 0222 a; cd a`,
		"cd: a: Permission denied\nexit status 1 #JUSTERR",
	},
	{
		`mkdir a; chmod 0444 a; cd a`,
		"cd: a: Permission denied\nexit status 1 #JUSTERR",
	},
	{
		`mkdir a; chmod 0010 a; cd a`,
		"cd: a: Permission denied\nexit status 1 #JUSTERR",
	},
	{
		`mkdir a; chmod 0001 a; cd a`,
		"cd: a: Permission denied\nexit status 1 #JUSTERR",
	},
	{
		`unset UID`,
		"unset: UID: cannot unset: readonly variable\nexit status 1 #JUSTERR",
	},
	{
		`test -n "$EUID" && echo OK`,
		"OK\n",
	},
	{
		`set EUID=newvalue; test EUID != newvalue && echo OK || echo EUID=$EUID`,
		"OK\n",
	},
	{
		`unset EUID`,
		"unset: EUID: cannot unset: readonly variable\nexit status 1 #JUSTERR",
	},
	// GID is not set in bash
	{
		// GID is koi's own — bash has GROUPS and no GID at all, so its
		// `unset GID` is a silent no-op on a variable that was never
		// there. The message and status are the readonly ones (#535).
		`unset GID`,
		"unset: GID: cannot unset: readonly variable\nexit status 1 #IGNORE GID is not a bash variable",
	},
	{
		`[[ -z $GID ]] && echo "GID not set"`,
		"exit status 1 #JUSTERR #IGNORE",
	},

	// Unix-y PATH
	{
		"PATH=; bash -c 'echo foo'",
		"bash: command not found\nexit status 127 #JUSTERR",
	},
	{
		"cd /; sure/is/missing",
		"sure/is/missing: No such file or directory\nexit status 127 #JUSTERR",
	},
	{
		"echo '#!/bin/sh\necho b' >a; chmod 0755 a; PATH=; a",
		"b\n",
	},
	{
		"mkdir c; cd c; echo '#!/bin/sh\necho b' >a; chmod 0755 a; PATH=; a",
		"b\n",
	},
	{
		"mkdir c; echo '#!/bin/sh\necho b' >c/a; chmod 0755 c/a; c/a",
		"b\n",
	},
	{
		"GOSH_CMD=lookpath $GOSH_PROG",
		"sh found\n",
	},

	// error strings which are too different on Windows
	{
		"echo foo >/shouldnotexist/file",
		"open /shouldnotexist/file: no such file or directory\nexit status 1 #JUSTERR",
	},
	{
		"set -e; echo foo >/shouldnotexist/file; echo foo",
		"open /shouldnotexist/file: no such file or directory\nexit status 1 #JUSTERR",
	},

	// process substitution; named pipes (fifos) are a TODO for windows
	{
		"sed 's/o/e/g' <(echo foo bar)",
		"fee bar\n",
	},
	{
		"cat <(echo foo) <(echo bar) <(echo baz)",
		"foo\nbar\nbaz\n",
	},
	{
		"cat <(cat <(echo nested))",
		"nested\n",
	},
	{
		// The tests here use "wait" because otherwise the parent may finish before
		// the subprocess has had time to process the input and print the result.
		"echo foo bar > >(sed 's/o/e/g'); wait",
		"fee bar\n",
	},
	{
		"echo foo bar | tee >(sed 's/o/e/g') >/dev/null; wait",
		"fee bar\n",
	},
	{
		"echo nested > >(cat > >(cat); wait); wait",
		"nested\n",
	},
	{
		"cat <(exit 0); wait $!; echo $?",
		"0\n",
	},
	{
		"cat <(exit 5); wait $!; echo $?",
		"5\n",
	},
	{
		// The reader here does not consume the named pipe.
		"test -e <(echo foo)",
		"",
	},
	// echo trace
	{
		`set -x; animals=("dog", "cat", "otter"); echo "hello ${animals[*]}"`,
		`+ animals=("dog", "cat", "otter")
+ echo 'hello dog, cat, otter'
hello dog, cat, otter
`,
	},
	{
		`set -x; s="always print a decimal point for %e, %E, %f, %F, %g and %G; do not remove trailing zeros for %g and %G"; echo "$s"`,
		`+ s='always print a decimal point for %e, %E, %f, %F, %g and %G; do not remove trailing zeros for %g and %G'
+ echo 'always print a decimal point for %e, %E, %f, %F, %g and %G; do not remove trailing zeros for %g and %G'
always print a decimal point for %e, %E, %f, %F, %g and %G; do not remove trailing zeros for %g and %G
`,
	},
	{
		`set -x
x=without; echo "$x"
x="double quote"; echo "$x"
x='single quote'; echo "$x"`,
		`+ x=without
+ echo without
without
+ x='double quote'
+ echo 'double quote'
double quote
+ x='single quote'
+ echo 'single quote'
single quote
`,
	},
	// for trace
	{
		`set -x
exec >/dev/null
echo "trace should go to stderr"`,
		`+ exec
+ echo 'trace should go to stderr'
`,
	},
	{
		`set -x
animals=(dog, cat, otter)
for i in ${animals[@]}
do
   echo "hello ${i}"
done
`,
		`+ animals=(dog, cat, otter)
+ for i in ${animals[@]}
+ echo 'hello dog,'
hello dog,
+ for i in ${animals[@]}
+ echo 'hello cat,'
hello cat,
+ for i in ${animals[@]}
+ echo 'hello otter'
hello otter
`,
	},
	{
		`set -x
loop() {
    for i do
        echo "something with $i"
    done
}
loop 1 2 3`,
		`+ loop 1 2 3
+ for i in "$@"
+ echo 'something with 1'
something with 1
+ for i in "$@"
+ echo 'something with 2'
something with 2
+ for i in "$@"
+ echo 'something with 3'
something with 3
`,
	},
	{
		`set -x; animals=(dog, cat, otter); for i in ${animals[@]}; do echo "hello ${i}"; done`,
		`+ animals=(dog, cat, otter)
+ for i in ${animals[@]}
+ echo 'hello dog,'
hello dog,
+ for i in ${animals[@]}
+ echo 'hello cat,'
hello cat,
+ for i in ${animals[@]}
+ echo 'hello otter'
hello otter
`,
	},
	{
		`set -x; a=x"y"$z b=(foo bar $none '')`,
		"+ a=xy\n+ b=(foo bar $none '')\n",
	},
	{
		`set -x; for i in a b; do echo $i; done`,
		`+ for i in a b
+ echo a
a
+ for i in a b
+ echo b
b
`,
	},
	{
		`set -x; for i in $none_a $none_b; do echo $i; done`,
		``,
	},
	// case trace
	{
		`set -x; pet=dog; case $pet in 'dog') echo "barks";; *) echo "unknown";; esac`,
		`+ pet=dog
+ case $pet in
+ echo barks
barks
`,
	},
	{
		`set -x
pet="dog"
case $pet in
  dog)
    echo "barks"
    ;;
  *)
    echo "unknown"
    ;;
esac`,
		`+ pet=dog
+ case $pet in
+ echo barks
barks
`,
	},
	// arithmetic
	{
		`set -x
a=$(( 4 + 5 )); echo $a
a=$((3+5)); echo $a`,
		`+ a=9
+ echo 9
9
+ a=8
+ echo 8
8
`,
	},
	{
		`set -x;
let a=5+4; echo $a
let "a = 5 + 4"; echo $a
let a++; echo $a`,
		`+ let a=5+4
+ echo 9
9
+ let 'a = 5 + 4'
+ echo 9
9
+ let a++
+ echo 10
10
`,
	},
	// functions
	{
		`set -x; function with_function () { echo 'hello, world'; }; with_function`,
		`+ with_function
+ echo 'hello, world'
hello, world
`,
	},
	{
		`set -x; without_function () { echo 'hello, world'; }; without_function`,
		`+ without_function
+ echo 'hello, world'
hello, world
`,
	},
	{
		// globbing wildcard as function name
		`@() { echo "$@"; }; @ lala; function +() { echo "$@"; }; + foo`,
		"lala\nfoo\n",
	},
	{
		`      @() { echo "$@"; }; @ lala;`,
		"lala\n",
	},
	{
		// globbing wildcard as function name but with space after the name
		`+ () { echo "$@"; }; + foo; @ () { echo "$@"; }; @ lala; ? () { echo "$@"; }; ? bar`,
		"foo\nlala\nbar\n",
	},
	// mapfile, no process substitution yet on Windows
	{
		`mapfile -t -d "" < <(printf "a\0b\n"); for x in "${MAPFILE[@]}"; do echo "$x"; done`,
		"a\nb\n\n",
	},
	// Windows does not support having a `\n` in a filename
	{
		`> $'bar\nbaz'; echo bar*baz`,
		"bar\nbaz\n",
	},
}

var runTestsWindows = []runTest{
	{"[[ -n $PPID || $PPID -gt 0 ]]", ""}, // os.Getppid can be 0 on windows
	{"cmd() { :; }; cmd /c 'echo foo'", ""},
	{"cmd() { :; }; command cmd /c 'echo foo'", "foo\r\n"},
	{
		"GOSH_CMD=lookpath $GOSH_PROG",
		"cmd found\n",
	},
	{
		"localCase=camel; LocalCase=pascal; echo $localcase",
		"pascal\n",
	},
	{
		// Matching the env var name set as a global
		// in a case sensitive way.
		"$ENV_PROG | grep -i '^mixedCase_interp'",
		"mixedCase_INTERP_GLOBAL=value\n",
	},
	{
		// Overwriting the env var set as a global
		// in a case insensitive way.
		"MIXEDCASE_interp_global=replaced; echo $MIXEDCASE_interp_GLOBAL",
		"replaced\n",
	},
	{
		"MIXEDCASE_interp_global=replaced; $ENV_PROG | grep -i '^mixedcase_interp'",
		"MIXEDCASE_interp_global=replaced\n",
	},
}

// These tests are specific to 64-bit architectures, and that's fine. We don't
// need to add explicit versions for 32-bit.
var runTests64bit = []runTest{
	{"printf %i,%u -3 -3", "-3,18446744073709551613"},
	{"printf %o -3", "1777777777777777777775"},
	{"printf %x -3", "fffffffffffffffd"},
}

func init() {
	if runtime.GOOS == "windows" {
		runTests = append(runTests, runTestsWindows...)
	} else { // Unix-y
		runTests = append(runTests, runTestsUnix...)
	}
	if bits.UintSize == 64 {
		runTests = append(runTests, runTests64bit...)
	}
}

// ln -s: wine doesn't implement symlinks; see https://bugs.winehq.org/show_bug.cgi?id=44948
// process substitutions are not supported on Windows
var skipOnWindows = regexp.MustCompile(`ln -s|<\(`)

// process substitutions seemflaky on mac; see https://github.com/mvdan/sh/issues/576
var skipOnMac = regexp.MustCompile(`>\(|<\(`)

func skipIfUnsupported(tb testing.TB, src string) {
	switch {
	case runtime.GOOS == "windows" && skipOnWindows.MatchString(src):
		tb.Skipf("skipping non-portable test on windows")
	case runtime.GOOS == "darwin" && skipOnMac.MatchString(src):
		tb.Skipf("skipping non-portable test on mac")
	}
}

func TestRunnerRun(t *testing.T) {
	t.Parallel()

	p := syntax.NewParser()
	for _, c := range runTests {
		t.Run("", func(t *testing.T) {
			skipIfUnsupported(t, c.in)
			t.Logf("input: %q", c.in)

			// Parse first, as we reuse a single parser.
			file := parse(t, p, c.in)

			t.Parallel()

			tdir := t.TempDir()
			var cb concBuffer
			r, err := interp.New(interp.Dir(tdir), interp.StdIO(nil, &cb, &cb),
				// TODO: why does this make some tests hang?
				// interp.Env(expand.ListEnviron(append(os.Environ(),
				// 	"foo_NULL_BAR=foo\x00bar")...)),
				interp.ExecHandlers(testExecHandler),
			)
			if err != nil {
				t.Fatal(err)
			}
			ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
			defer cancel()
			if err := r.Run(ctx, file); err != nil {
				cb.WriteString(err.Error())
			}

			// Some builtins like "pushd" can show absolute paths as part of error messages.
			// Allow a very simple search-and-replace for the equivalent to "$PWD/a".
			want := strings.ReplaceAll(c.want, "ABS_PATH_A", filepath.Join(tdir, "a"))

			if i := strings.Index(want, " #"); i >= 0 {
				want = want[:i]
			}
			if got := cb.String(); got != want {
				if len(got) > 200 {
					got = "…" + got[len(got)-200:]
				}
				t.Fatalf("wrong output in %q:\nwant: %q\ngot:  %q",
					c.in, want, got)
			}
		})
	}
}

func TestRunnerUnsupported(t *testing.T) {
	t.Parallel()

	// Features from language variants that the interpreter does not
	// support, such as zsh, should error rather than panic.
	tests := []struct {
		lang syntax.LangVariant
		in   string
		want string
	}{
		{syntax.LangZsh, "echo x${}y", "unsupported\n"},
		{syntax.LangZsh, `echo "${}"`, "unsupported\n"},
		{syntax.LangZsh, "echo ${:-foo}", "unsupported\n"},
		{syntax.LangZsh, "echo ${+a}", "unsupported\n"},
		{syntax.LangZsh, "a=abc; echo ${a[(r)b]}", "unsupported\n"},
		{syntax.LangZsh, "() { echo anon; }", "unsupported\nexit status 1"},
		{syntax.LangZsh, "function { echo anon; }", "unsupported\nexit status 1"},
		{syntax.LangZsh, "function f g { echo multi; }", "unsupported\nexit status 1"},
		{syntax.LangZsh, "cat =(echo hi)", "unsupported\n"},
		{syntax.LangMirBSDKorn, "echo ${%a}", "unsupported\n"},
	}
	for _, tc := range tests {
		t.Run("", func(t *testing.T) {
			t.Parallel()
			t.Logf("input: %q", tc.in)
			p := syntax.NewParser(syntax.Variant(tc.lang))
			file := parse(t, p, tc.in)
			var cb concBuffer
			r, err := interp.New(interp.StdIO(nil, &cb, &cb))
			if err != nil {
				t.Fatal(err)
			}
			ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
			defer cancel()
			if err := r.Run(ctx, file); err != nil {
				cb.WriteString(err.Error())
			}
			if got := cb.String(); got != tc.want {
				t.Fatalf("wrong output in %q:\nwant: %q\ngot:  %q",
					tc.in, tc.want, got)
			}
		})
	}
}

func readLines(hc interp.HandlerContext) ([][]byte, error) {
	bs, err := io.ReadAll(hc.Stdin)
	if err != nil {
		return nil, err
	}
	if runtime.GOOS == "windows" {
		bs = bytes.ReplaceAll(bs, []byte("\r\n"), []byte("\n"))
	}
	bs = bytes.TrimSuffix(bs, []byte("\n"))
	return bytes.Split(bs, []byte("\n")), nil
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

var testBuiltinsMap = map[string]func(interp.HandlerContext, []string) error{
	"cat": func(hc interp.HandlerContext, args []string) error {
		if len(args) == 0 {
			if hc.Stdin == nil || hc.Stdout == nil {
				return nil
			}
			_, err := io.Copy(hc.Stdout, hc.Stdin)
			return err
		}
		for _, arg := range args {
			path := absPath(hc.Dir, arg)
			f, err := os.Open(path)
			if err != nil {
				return err
			}
			_, err = io.Copy(hc.Stdout, f)
			f.Close()
			if err != nil {
				return err
			}
		}
		return nil
	},
	"wc": func(hc interp.HandlerContext, args []string) error {
		bs, err := io.ReadAll(hc.Stdin)
		if err != nil {
			return err
		}
		if len(args) == 0 {
			fmt.Fprintf(hc.Stdout, "%7d", bytes.Count(bs, []byte("\n")))
			fmt.Fprintf(hc.Stdout, "%8d", len(bytes.Fields(bs)))
			fmt.Fprintf(hc.Stdout, "%8d\n", len(bs))
		} else if args[0] == "-c" {
			fmt.Fprintln(hc.Stdout, len(bs))
		} else if args[0] == "-l" {
			fmt.Fprintln(hc.Stdout, bytes.Count(bs, []byte("\n")))
		}
		return nil
	},
	"tr": func(hc interp.HandlerContext, args []string) error {
		if len(args) != 2 || len(args[1]) != 1 {
			return fmt.Errorf("usage: tr [-s -d] [character]")
		}
		squeeze := args[0] == "-s"
		char := args[1][0]
		bs, err := io.ReadAll(hc.Stdin)
		if err != nil {
			return err
		}
		for {
			i := bytes.IndexByte(bs, char)
			if i < 0 {
				hc.Stdout.Write(bs) // remaining
				break
			}
			hc.Stdout.Write(bs[:i]) // up to char
			bs = bs[i+1:]

			bs = bytes.TrimLeft(bs, string(char)) // remove repeats
			if squeeze {
				hc.Stdout.Write([]byte{char})
			}
		}
		return nil
	},
	"sort": func(hc interp.HandlerContext, args []string) error {
		lines, err := readLines(hc)
		if err != nil {
			return err
		}
		slices.SortFunc(lines, bytes.Compare)
		for _, line := range lines {
			fmt.Fprintf(hc.Stdout, "%s\n", line)
		}
		return nil
	},
	"grep": func(hc interp.HandlerContext, args []string) error {
		var rx *regexp.Regexp
		quiet := false
		caseInsensitive := false
		for _, arg := range args {
			if arg == "-q" {
				quiet = true
			} else if arg == "-i" {
				caseInsensitive = true
			} else if arg == "-E" {
			} else if rx == nil {
				if caseInsensitive {
					arg = "(?i)" + arg
				}
				rx = regexp.MustCompile(arg)
			} else {
				return fmt.Errorf("unexpected arg: %q", arg)
			}
		}
		lines, err := readLines(hc)
		if err != nil {
			return err
		}
		anyMatch := false
		for _, line := range lines {
			if rx.Match(line) {
				if quiet {
					return nil
				}
				anyMatch = true
				fmt.Fprintf(hc.Stdout, "%s\n", line)
			}
		}
		if !anyMatch {
			return interp.ExitStatus(1)
		}
		return nil
	},
	"sed": func(hc interp.HandlerContext, args []string) error {
		f := hc.Stdin
		switch len(args) {
		case 1:
		case 2:
			var err error
			f, err = os.Open(absPath(hc.Dir, args[1]))
			if err != nil {
				return err
			}
		default:
			return fmt.Errorf("usage: sed pattern [file]")
		}
		expr := args[0]
		if expr == "" || expr[0] != 's' {
			return fmt.Errorf("unimplemented")
		}
		sep := expr[1]
		expr = expr[2:]
		from := expr[:strings.IndexByte(expr, sep)]
		expr = expr[len(from)+1:]
		to := expr[:strings.IndexByte(expr, sep)]
		bs, err := io.ReadAll(f)
		if err != nil {
			return err
		}
		rx := regexp.MustCompile(from)
		bs = rx.ReplaceAllLiteral(bs, []byte(to))
		_, err = hc.Stdout.Write(bs)
		return err
	},
	"mkdir": func(hc interp.HandlerContext, args []string) error {
		for _, arg := range args {
			if arg == "-p" {
				continue
			}
			path := absPath(hc.Dir, arg)
			if err := os.MkdirAll(path, 0o777); err != nil {
				return err
			}
		}
		return nil
	},
	"rm": func(hc interp.HandlerContext, args []string) error {
		for _, arg := range args {
			if arg == "-r" {
				continue
			}
			path := absPath(hc.Dir, arg)
			if err := os.RemoveAll(path); err != nil {
				return err
			}
		}
		return nil
	},
	"ln": func(hc interp.HandlerContext, args []string) error {
		symbolic := args[0] == "-s"
		if symbolic {
			args = args[1:]
		}
		oldname := absPath(hc.Dir, args[0])
		newname := absPath(hc.Dir, args[1])
		if symbolic {
			return os.Symlink(oldname, newname)
		}
		return os.Link(oldname, newname)
	},
	"touch": func(hc interp.HandlerContext, args []string) error {
		filenames := args // create all arguments as filenames

		newTime := time.Now()
		if args[0] == "-t" {
			if len(args) < 3 {
				return fmt.Errorf("usage: touch [-t [[CC]YY]MMDDhhmm[.SS]] file")
			}
			filenames = args[2:] // treat the rest of the args as filenames

			arg := args[1]
			if len(arg) > 15 {
				return fmt.Errorf("usage: touch [-t [[CC]YY]MMDDhhmm[.SS]] file")
			}
			s, err := time.Parse("200601021504.05", arg)
			if err != nil {
				return err
			}
			newTime = s
		}

		for _, arg := range filenames {
			if strings.HasPrefix(arg, "-") {
				return fmt.Errorf("usage: touch [-t [[CC]YY]MMDDhhmm[.SS]] file")
			}
			path := absPath(hc.Dir, arg)
			// create the file if it does not exist
			f, err := os.OpenFile(path, os.O_CREATE, 0o666)
			if err != nil {
				return err
			}
			f.Close()
			// change the modification and access time
			if err := os.Chtimes(path, newTime, newTime); err != nil {
				return err
			}
		}
		return nil
	},
	"sleep": func(hc interp.HandlerContext, args []string) error {
		for _, arg := range args {
			// assume and default unit to be in seconds
			d, err := time.ParseDuration(fmt.Sprintf("%ss", arg))
			if err != nil {
				return err
			}
			time.Sleep(d)
		}
		return nil
	},
}

func testExecHandler(next interp.ExecHandlerFunc) interp.ExecHandlerFunc {
	return func(ctx context.Context, args []string) error {
		if fn := testBuiltinsMap[args[0]]; fn != nil {
			return fn(interp.HandlerCtx(ctx), args[1:])
		}
		return next(ctx, args)
	}
}

// Same as the syntax package.
var requireShells = os.Getenv("REQUIRE_SHELLS") == "1"

// koi-local: checkOracleTilde asks the oracle what it does rather than
// assuming from the platform, because assuming was wrong. Homebrew's bash
// resolves ~ from the password database and ignores a reassigned HOME; a
// vanilla bash built from source on the same Mac does not. The behavior
// belongs to the build, not the operating system, so the only reliable
// question is the one put to the bash that is actually about to run.
func checkOracleTilde() bool {
	out, err := exec.Command("bash", "-c", "HOME=/koi-oracle-probe; echo ~").Output()
	if err != nil {
		return false
	}
	return strings.TrimSpace(string(out)) != "/koi-oracle-probe"
}

// skipIfOracleGap skips the cases where bash itself, not the interpreter, is
// what varies between machines. Both are matched on the exact script: other
// cases combine HOME with ~ and do pass, and a loose predicate would skip
// those too and quietly cost coverage. Tracked in #271.
func skipIfOracleGap(t *testing.T, src string) {
	switch src {
	case `HOME='/*'; echo ~; echo "$HOME"`,
		`HOME=/foo; rel=/bar; echo ~/bar ~/'bar' ~/"bar" ~/$rel ~/"$rel"`,
		`HOME=/foo; echo ~ ~/ ~/'' ~'' ~""`:
		if oracleTildeIgnoresHome {
			t.Skip("this bash resolves ~ from the password database rather than from HOME")
		}
	case `echo foo >&- 2>&-; :`:
		// Unlike the tilde cases this one survives a source build, so it
		// really does look like the platform rather than the packaging.
		if runtime.GOOS == "darwin" {
			t.Skip("bash on darwin reports a write error for a closed fd that Linux bash does not")
		}
	}
}

// oracleRetries is how many extra times a racing case may ask bash. The
// one case that races was measured at roughly one wrong answer in three
// hundred runs on a machine under three times its core count in load, so
// five retries put a spurious failure far below the rate of every other
// thing that can go wrong in CI.
const oracleRetries = 5

// oracleRacesItself reports whether bash answers this script differently
// from run to run.
//
// Matched on the exact script, the way [skipIfOracleGap] is and for the
// same reason: the neighboring `wait -n` cases were measured too and are
// stable, so a predicate like "mentions wait" would hand a retry to cases
// that have earned a single-shot check.
//
//	(exit 3) & wait; wait -n; echo $?
//
// A bare `wait` reaps every job, so the `wait -n` after it has nothing
// left and answers 127. bash usually agrees and sometimes answers 3 --
// the job's own status -- because whether the job has left the table by
// then is not something bash sequences against `wait` returning. It is
// bash racing itself rather than disagreeing with the recorded answer:
// 300 runs under load gave 299 of the former and one of the latter, and
// `(exit 3) & p=$!; wait $p; wait -n` never varied at all.
func oracleRacesItself(src string) bool {
	return src == `(exit 3) & wait; wait -n; echo $?`
}

func TestRunnerRunConfirm(t *testing.T) {
	if testing.Short() {
		t.Skip("calling bash is slow")
	}
	if !hasBash53 {
		if requireShells {
			t.Fatal("bash 5.3 required to run")
		} else {
			t.Skip("bash 5.3 required to run")
		}
	}
	t.Parallel()

	if runtime.GOOS == "windows" {
		// For example, it seems to treat environment variables as
		// case-sensitive, which isn't how Windows works.
		t.Skip("bash on Windows emulates Unix-y behavior")
	}
	for _, c := range runTests {
		t.Run("", func(t *testing.T) {
			if strings.Contains(c.want, " #IGNORE") {
				return
			}
			skipIfUnsupported(t, c.in)
			skipIfOracleGap(t, c.in)
			t.Parallel()
			askBash := func() (string, error) {
				tdir := t.TempDir()
				ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
				defer cancel()
				cmd := exec.CommandContext(ctx, "bash")
				cmd.Dir = tdir
				cmd.Stdin = strings.NewReader(c.in)
				out, err := cmd.CombinedOutput()
				return string(out), err
			}
			out, err := askBash()
			if strings.Contains(c.want, " #JUSTERR") {
				// bash sometimes exits with status code 0 and
				// stderr "bash: ..." for an error
				fauxErr := strings.HasPrefix(out, "bash:")
				if err == nil && !fauxErr {
					t.Fatalf("wanted bash to error in %q", c.in)
				}
				return
			}
			got := out
			if err != nil {
				got += err.Error()
			}
			// A case whose subject is bash's own job reaping does not
			// answer the same way every time, so asking once turns a
			// property of bash into a coin flip (#317). Asking again is
			// the honest assertion for it -- bash must still produce
			// this answer, just not on demand -- and it stays scoped to
			// the exact scripts measured to race, so no other case has
			// its check weakened.
			for try := 0; got != c.want && try < oracleRetries && oracleRacesItself(c.in); try++ {
				out, err = askBash()
				got = out
				if err != nil {
					got += err.Error()
				}
			}
			if got != c.want {
				t.Fatalf("wrong bash output in %q:\nwant: %q\ngot:  %q",
					c.in, c.want, got)
			}
		})
	}
}

func TestRunnerOpts(t *testing.T) {
	t.Parallel()

	withPath := func(strs ...string) func(*interp.Runner) error {
		prefix := []string{
			"PATH=" + os.Getenv("PATH"),
			"ENV_PROG=" + os.Getenv("ENV_PROG"),
		}
		return interp.Env(expand.ListEnviron(append(prefix, strs...)...))
	}
	opts := func(list ...interp.RunnerOption) []interp.RunnerOption {
		return list
	}
	cases := []struct {
		opts     []interp.RunnerOption
		in, want string
	}{
		{
			nil,
			"$ENV_PROG | grep -i '^interp_global='",
			"INTERP_GLOBAL=value\n",
		},
		{
			opts(withPath()),
			"$ENV_PROG | grep -i '^interp_global='",
			"exit status 1",
		},
		{
			opts(withPath("INTERP_GLOBAL=bar")),
			"$ENV_PROG | grep -i '^interp_global='",
			"INTERP_GLOBAL=bar\n",
		},
		{
			opts(withPath("a=b")),
			"echo $a",
			"b\n",
		},
		{
			opts(withPath("A=b")),
			"$ENV_PROG | grep '^A='; echo $A",
			"A=b\nb\n",
		},
		{
			opts(withPath("A=b", "A=c")),
			"$ENV_PROG | grep '^A='; echo $A",
			"A=c\nc\n",
		},
		{
			opts(withPath("HOME=")),
			"echo $HOME",
			"\n",
		},
		{
			opts(withPath("PWD=foo")),
			"[[ $PWD == foo ]]",
			"exit status 1",
		},
		{
			opts(interp.Params("foo")),
			"echo $@",
			"foo\n",
		},
		{
			opts(interp.Params("-u", "--", "foo")),
			"echo $@; echo $unset",
			"foo\nunset: unbound variable\nexit status 1",
		},
		{
			opts(interp.Params("-u", "--", "foo")),
			"echo $@; echo ${unset:-default}",
			"foo\ndefault\n",
		},
		{
			opts(interp.Params("foo")),
			"set >/dev/null; echo $@",
			"foo\n",
		},
		{
			opts(interp.Params("foo")),
			"set -e; echo $@",
			"foo\n",
		},
		{
			opts(interp.Params("foo")),
			"set --; echo $@",
			"\n",
		},
		{
			opts(interp.Params("foo")),
			"set bar; echo $@",
			"bar\n",
		},
		{
			opts(interp.Env(expand.FuncEnviron(func(name string) string {
				if name == "foo" {
					return "bar"
				}
				return ""
			}))),
			"(echo $foo); echo x | echo $foo",
			"bar\nbar\n",
		},
	}
	p := syntax.NewParser()
	for _, c := range cases {
		t.Run("", func(t *testing.T) {
			skipIfUnsupported(t, c.in)
			file := parse(t, p, c.in)
			var cb concBuffer
			r, err := interp.New(append(c.opts,
				interp.StdIO(nil, &cb, &cb),
				interp.ExecHandlers(testExecHandler),
			)...)
			if err != nil {
				t.Fatal(err)
			}
			ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
			defer cancel()
			if err := r.Run(ctx, file); err != nil {
				cb.WriteString(err.Error())
			}
			if got := cb.String(); got != c.want {
				t.Fatalf("wrong output in %q:\nwant: %q\ngot:  %q",
					c.in, c.want, got)
			}
		})
	}
}

func TestRunnerContext(t *testing.T) {
	t.Parallel()

	cases := []string{
		"",
		"while true; do true; done",
		"until false; do true; done",
		"sleep 1000",
		"while true; do true; done & wait",
		"sleep 1000 & wait",
		"(while true; do true; done)",
		"$(while true; do true; done)",
		"while true; do true; done | while true; do true; done",
	}
	p := syntax.NewParser()
	for _, in := range cases {
		t.Run("", func(t *testing.T) {
			file := parse(t, p, in)
			ctx, cancel := context.WithCancel(t.Context())
			cancel()
			r, _ := interp.New()
			errChan := make(chan error)
			go func() {
				errChan <- r.Run(ctx, file)
			}()

			timeout := 500 * time.Millisecond
			select {
			case err := <-errChan:
				if err != nil && err != ctx.Err() {
					t.Fatal("Runner did not use ctx.Err()")
				}
			case <-time.After(timeout):
				t.Fatalf("program was not killed in %s", timeout)
			}
		})
	}
}

func TestCancelBlockedStdinRead(t *testing.T) {
	if runtime.GOOS == "windows" {
		// TODO: Why is this? The [os.File.SetReadDeadline] docs seem to imply that it should work
		// across all major platforms, and the file polling  implementation seems to be
		// for all posix platforms including Windows.
		// Our previous logic and tests with muesli/cancelreader did not test an os.Pipe
		// on Windows either, so skipping here is not any worse.
		t.Skip("os.Pipe on windows appears to not support cancellable reads")
	}
	t.Parallel()

	p := syntax.NewParser()
	file := parse(t, p, "read x")
	ctx, cancel := context.WithTimeout(t.Context(), 100*time.Millisecond)
	// Make the linter happy, even though we deliberately wait for the timeout.
	defer cancel()

	stdinRead, stdinWrite, err := os.Pipe()
	if err != nil {
		t.Fatalf("Error calling os.Pipe: %v", err)
	}
	defer func() {
		stdinWrite.Close()
		stdinRead.Close()
	}()
	r, _ := interp.New(interp.StdIO(stdinRead, nil, nil))
	now := time.Now()
	errChan := make(chan error)
	go func() {
		errChan <- r.Run(ctx, file)
	}()

	timeout := 500 * time.Millisecond
	select {
	case err := <-errChan:
		if err == nil || err.Error() != "exit status 1" || ctx.Err() != context.DeadlineExceeded {
			t.Fatalf("'read x' did not timeout correctly; err: %v, ctx.Err(): %v; dur: %v",
				err, ctx.Err(), time.Since(now))
		}
	case <-time.After(timeout):
		t.Fatalf("program was not killed in %s", timeout)
	}
}

func TestRunnerAltNodes(t *testing.T) {
	t.Parallel()

	in := "echo foo"
	file := parse(t, nil, in)
	want := "foo\n"
	nodes := []syntax.Node{
		file,
		file.Stmts[0],
		file.Stmts[0].Cmd,
	}
	for _, node := range nodes {
		var cb concBuffer
		r, _ := interp.New(interp.StdIO(nil, &cb, &cb))
		ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
		defer cancel()
		if err := r.Run(ctx, node); err != nil {
			cb.WriteString(err.Error())
		}
		if got := cb.String(); got != want {
			t.Fatalf("wrong output in %q:\nwant: %q\ngot:  %q",
				in, want, got)
		}
	}
}

func TestRunnerDir(t *testing.T) {
	t.Parallel()

	wd, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	t.Run("Missing", func(t *testing.T) {
		_, err := interp.New(interp.Dir("missing"))
		if err == nil {
			t.Fatal("expected New to error when Dir is missing")
		}
	})
	t.Run("NotDir", func(t *testing.T) {
		_, err := interp.New(interp.Dir("interp_test.go"))
		if err == nil {
			t.Fatal("expected New to error when Dir is not a dir")
		}
	})
	t.Run("NotDirAbs", func(t *testing.T) {
		_, err := interp.New(interp.Dir(filepath.Join(wd, "interp_test.go")))
		if err == nil {
			t.Fatal("expected New to error when Dir is not a dir")
		}
	})
	t.Run("Relative", func(t *testing.T) {
		// On Windows, it's impossible to make a relative path from one
		// drive to another. Use the parent directory, as that's for
		// sure in the same drive as the current directory.
		rel := ".." + string(filepath.Separator)
		r, err := interp.New(interp.Dir(rel))
		if err != nil {
			t.Fatal(err)
		}
		if !filepath.IsAbs(r.Dir) {
			t.Errorf("Runner.Dir is not absolute")
		}
	})
	// Ensure that we treat symlinks and short paths properly, especially
	// with Dir and globbing.
	t.Run("SymlinkOrShortPath", func(t *testing.T) {
		tdir := t.TempDir()

		realDir := filepath.Join(tdir, "real-long-dir-name")
		realFile := filepath.Join(realDir, "realfile")

		if err := os.Mkdir(realDir, 0o777); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(realFile, []byte(""), 0o666); err != nil {
			t.Fatal(err)
		}

		var altDir string
		if runtime.GOOS == "windows" {
			short, err := shortPathName(realDir)
			if err != nil {
				t.Fatal(err)
			}
			altDir = short
			// We replace tdir later, and it might have been shortened.
			tdir = filepath.Dir(altDir)
		} else {
			altDir = filepath.Join(tdir, "symlink")
			if err := os.Symlink(realDir, altDir); err != nil {
				t.Fatal(err)
			}
		}

		var b bytes.Buffer
		r, err := interp.New(interp.Dir(altDir), interp.StdIO(nil, &b, &b))
		if err != nil {
			t.Fatal(err)
		}
		file := parse(t, nil, "echo $PWD $PWD/*")
		ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
		defer cancel()
		if err := r.Run(ctx, file); err != nil {
			t.Fatal(err)
		}
		got := b.String()
		got = strings.ReplaceAll(got, tdir, "")
		got = strings.TrimSpace(got)
		want := `/symlink /symlink/realfile`
		if runtime.GOOS == "windows" {
			want = `\\REAL.{4} \\REAL.{4}\\realfile`
		}
		if !regexp.MustCompile(want).MatchString(got) {
			t.Fatalf("\nwant regexp: %q\ngot: %q", want, got)
		}
	})
}

func TestRunnerIncremental(t *testing.T) {
	t.Parallel()

	file := parse(t, nil, "echo foo; false; echo bar; exit 0; echo baz")
	want := "foo\nbar\n"
	var b bytes.Buffer
	r, _ := interp.New(interp.StdIO(nil, &b, &b))
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	for _, stmt := range file.Stmts {
		err := r.Run(ctx, stmt)
		if !errors.As(err, new(interp.ExitStatus)) && err != nil {
			// Keep track of unexpected errors.
			b.WriteString(err.Error())
		}
		if r.Exited() {
			break
		}
	}
	if got := b.String(); got != want {
		t.Fatalf("\nwant: %q\ngot:  %q", want, got)
	}
}

func TestRunnerIncrementalExitTrap(t *testing.T) {
	t.Parallel()

	file := parse(t, nil, "trap 'echo bye' EXIT\necho a\necho b\nexit 3\necho never")
	want := "a\nb\nbye\n"
	var b bytes.Buffer
	r, _ := interp.New(interp.StdIO(nil, &b, &b))
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	var exit interp.ExitStatus
	for _, stmt := range file.Stmts {
		err := r.Run(ctx, stmt)
		if err != nil && !errors.As(err, &exit) {
			b.WriteString(err.Error())
		}
		if r.Exited() {
			break
		}
	}
	if exit != 3 {
		t.Fatalf("want exit status 3, got %d", exit)
	}
	if got := b.String(); got != want {
		t.Fatalf("\nwant: %q\ngot:  %q", want, got)
	}
}

func TestRunnerResetFields(t *testing.T) {
	t.Parallel()

	tdir := t.TempDir()
	logPath := filepath.Join(tdir, "log")
	logFile, err := os.Create(logPath)
	if err != nil {
		t.Fatal(err)
	}
	defer logFile.Close()
	r, _ := interp.New(
		interp.Params("-f", "--", "first", tdir, logPath),
		interp.Dir(tdir),
		interp.ExecHandlers(testExecHandler),
	)
	// Check that using option funcs and Runner fields directly is still
	// kept by Reset.
	interp.StdIO(nil, logFile, os.Stderr)(r)
	r.Env = expand.ListEnviron(append(os.Environ(), "GLOBAL=foo")...)

	file := parse(t, nil, `
# Params set 3 arguments
[[ $# -eq 3 ]] || exit 10
[[ $1 == "first" ]] || exit 11

# Params set the -f option (noglob)
[[ -o noglob ]] || exit 12

# $PWD was set via Dir, and should be equal to $2
[[ "$PWD" == "$2" ]] || exit 13

# stdout should go into the log file, which is at $3
echo line1
echo line2
[[ "$(wc -l <$3)" == "2" ]] || exit 14

# $GLOBAL was set directly via the Env field
[[ "$GLOBAL" == "foo" ]] || exit 15

# Change all of the above within the script. Reset should undo this.
set +f -- newargs
cd
exec >/dev/null 2>/dev/null
GLOBAL=
export GLOBAL=
`)
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	for i := range 3 {
		if err := r.Run(ctx, file); err != nil {
			t.Fatalf("run number %d: %v", i, err)
		}
		r.Reset()
		// empty the log file too
		logFile.Truncate(0)
		logFile.Seek(0, io.SeekStart)
	}
}

func TestRunnerManyResets(t *testing.T) {
	t.Parallel()
	r, _ := interp.New()
	for range 5 {
		r.Reset()
	}
}

func TestRunnerFilename(t *testing.T) {
	t.Parallel()

	want := "f.sh\n"
	file, _ := syntax.NewParser().Parse(strings.NewReader("echo $0"), "f.sh")
	var b bytes.Buffer
	r, _ := interp.New(interp.StdIO(nil, &b, &b))
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	if err := r.Run(ctx, file); err != nil {
		t.Fatal(err)
	}
	if got := b.String(); got != want {
		t.Fatalf("\nwant: %q\ngot:  %q", want, got)
	}
}

func TestRunnerEnvNoModify(t *testing.T) {
	t.Parallel()

	env := expand.ListEnviron("one=1", "two=2")
	file := parse(t, nil, `echo -n "$one $two; "; one=x; unset two`)

	var b bytes.Buffer
	r, _ := interp.New(interp.Env(env), interp.StdIO(nil, &b, &b))
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	for range 3 {
		r.Reset()
		err := r.Run(ctx, file)
		if err != nil {
			t.Fatal(err)
		}
	}

	want := "1 2; 1 2; 1 2; "
	if got := b.String(); got != want {
		t.Fatalf("\nwant: %q\ngot:  %q", want, got)
	}
}

func TestRunnerASTNoModify(t *testing.T) {
	t.Parallel()

	file := parse(t, nil, "shopt -s expand_aliases; alias foo=echo\nfoo bar")
	printer := syntax.NewPrinter()
	var sb strings.Builder
	printer.Print(&sb, file)
	before := sb.String()

	var b bytes.Buffer
	r, _ := interp.New(interp.StdIO(nil, &b, &b))
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	if err := r.Run(ctx, file); err != nil {
		t.Fatal(err)
	}
	if want := "bar\n"; b.String() != want {
		t.Fatalf("want output %q, got %q", want, b.String())
	}

	sb.Reset()
	printer.Print(&sb, file)
	after := sb.String()
	if after != before {
		t.Fatalf("Run modified the AST:\nbefore: %q\nafter:  %q", before, after)
	}
}

func TestMalformedPathOnWindows(t *testing.T) {
	if runtime.GOOS != "windows" {
		t.Skip("Skipping windows test on non-windows GOOS")
	}
	tdir := t.TempDir()
	t.Parallel()

	path := filepath.Join(tdir, "test.cmd")
	script := []byte("@echo foo")
	if err := os.WriteFile(path, script, 0o777); err != nil {
		t.Fatal(err)
	}

	// set PATH to c:\tmp\dir instead of C:\tmp\dir
	volume := filepath.VolumeName(tdir)
	pathList := strings.ToLower(volume) + tdir[len(volume):]

	file := parse(t, nil, "test.cmd")
	var cb concBuffer
	r, _ := interp.New(interp.Env(expand.ListEnviron("PATH="+pathList)), interp.StdIO(nil, &cb, &cb))
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	if err := r.Run(ctx, file); err != nil {
		t.Fatal(err)
	}
	want := "foo\r\n"
	if got := cb.String(); got != want {
		t.Fatalf("wrong output:\nwant: %q\ngot:  %q", want, got)
	}
}

func TestReadShouldNotPanicWithNilStdin(t *testing.T) {
	t.Parallel()

	r, err := interp.New()
	if err != nil {
		t.Fatal(err)
	}

	f := parse(t, nil, "read foobar")
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	if err := r.Run(ctx, f); err == nil {
		t.Fatal("it should have returned an error")
	}
}

func TestRunnerVars(t *testing.T) {
	t.Parallel()

	r, err := interp.New()
	if err != nil {
		t.Fatal(err)
	}

	f := parse(t, nil, "foo=updated; BAR=new")
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	if err := r.Run(ctx, f); err != nil {
		t.Fatal(err)
	}

	if want, got := "updated", r.Vars["foo"].String(); got != want {
		t.Fatalf("wrong output:\nwant: %q\ngot:  %q", want, got)
	}
}

// TestRunnerAssocOrderSequence pins the one property of the recorded
// insertion sequence (#749) that no expansion can show: its length.
//
// Which place a key holds is settled by expand's own first-wins reading
// of the sequence, so a writer that re-recorded a key it already had
// would still list the array correctly — and would grow the sequence by
// one entry, and clone it, on every assignment to the same key. A loop
// that writes one key a thousand times is exactly that shape.
func TestRunnerAssocOrderSequence(t *testing.T) {
	t.Parallel()

	r, err := interp.New()
	if err != nil {
		t.Fatal(err)
	}
	f := parse(t, nil, "declare -A A=([k]=0 [k]=1 [j]=2);"+
		"for ((i = 0; i < 1000; i++)); do A[k]=$i; A[j]=$i; done")
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	if err := r.Run(ctx, f); err != nil {
		t.Fatal(err)
	}
	vr := r.Vars["A"]
	if len(vr.Map) != 2 {
		t.Fatalf("wrong map: %v", vr.Map)
	}
	if want := []string{"k", "j"}; !slices.Equal(vr.MapOrder, want) {
		t.Errorf("sequence grew or reordered:\nwant: %q\ngot:  %q", want, vr.MapOrder)
	}
}

func TestRunnerSubshell(t *testing.T) {
	t.Parallel()

	r1, err := interp.New()
	if err != nil {
		t.Fatal(err)
	}

	r2 := r1.Subshell()
	f1 := parse(t, nil, "PARENT=foo")
	f2 := parse(t, nil, "CHILD=bar")

	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	if err := r1.Run(ctx, f1); err != nil {
		t.Fatal(err)
	}
	if err := r2.Run(ctx, f2); err != nil {
		t.Fatal(err)
	}

	if want, got := "foo", r1.Vars["PARENT"].String(); got != want {
		t.Fatalf("wrong output:\nwant: %q\ngot:  %q", want, got)
	}
	if want, got := "bar", r2.Vars["CHILD"].String(); got != want {
		t.Fatalf("wrong output:\nwant: %q\ngot:  %q", want, got)
	}

	r3 := r2.Subshell()
	f3 := parse(t, nil, "CHILD=modified")
	if err := r3.Run(ctx, f3); err != nil {
		t.Fatal(err)
	}
	if want, got := "bar", r2.Vars["CHILD"].String(); got != want {
		t.Fatalf("wrong output:\nwant: %q\ngot:  %q", want, got)
	}
	if want, got := "modified", r3.Vars["CHILD"].String(); got != want {
		t.Fatalf("wrong output:\nwant: %q\ngot:  %q", want, got)
	}
}

func TestRunnerNonFileStdin(t *testing.T) {
	t.Parallel()

	var cb concBuffer
	r, err := interp.New(interp.StdIO(strings.NewReader("a\nb\nc\n"), &cb, &cb))
	if err != nil {
		t.Fatal(err)
	}
	file := parse(t, nil, "while read a; do echo $a; GOSH_CMD=print_ok $GOSH_PROG; done")
	ctx, cancel := context.WithTimeout(t.Context(), runnerRunTimeout)
	defer cancel()
	if err := r.Run(ctx, file); err != nil {
		cb.WriteString(err.Error())
	}
	// TODO: just like with heredocs, the first print_ok call consumes all stdin.
	qt.Assert(t, qt.Equals(cb.String(), "a\nexec ok\nb\nexec ok\nc\nexec ok\n"))
}
