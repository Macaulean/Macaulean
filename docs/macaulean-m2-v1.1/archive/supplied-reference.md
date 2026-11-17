# The Macaulay2 Language — Core Syntax and Basic Types

*A specification for implementers of a Macaulay2 interpreter*

---

## 0. Scope, status and conventions

### 0.1 What this document specifies

This document specifies the **core language** of Macaulay2 (M2): the part implemented by the
interpreter kernel in `M2/Macaulay2/d/` (written in the D language, `*.d`/`*.dd`). It covers

1. the **lexical structure** (§1),
2. the **grammar**, given normatively as an operator-precedence (Pratt) parser (§2),
3. **name binding and scoping** (§3),
4. the **translation of parse trees to executable code** (§4),
5. the **runtime values and built-in basic types** (§5),
6. the **evaluation semantics** of every construct and built-in operator (§6),
7. the **top-level read–eval–print loop** and file loading (§7).

It does **not** specify the library layer written in the Macaulay2 language itself
(`M2/Macaulay2/m2/*.m2`, loaded at start-up), even though users experience it as "the language".
That layer defines, for example, `method`, `MethodFunction`, `error`, `print`, `net`,
`toString`, `apply`, `scan`, `Set`, `Ring`s, `Matrix`, the `Print`/`AfterPrint` output hooks, options
processing, packages, and most binary methods for `|`, `_`, `**`, …  Where the core relies on
such library objects it names them as *library hooks*; a complete implementation must run the
`m2/` start-up files (or equivalents) on top of the core defined here.

The polynomial/matrix **engine** (`Raw*` types, `M2/Macaulay2/e/`) is outside the scope except
for naming its value types.

### 0.2 Normative source and version

The normative reference is the **1.26.06** source tree in `M2/M2/Macaulay2/d`. Examples marked
✔ were checked against a Macaulay2 **1.25.11** binary. Where that binary behaves differently
because it is older, this is noted; Appendix B lists the differences.

Source locations are cited as `file.d:line` for traceability. They are informative only.

### 0.3 Conventions

* "MUST", "MUST NOT", "SHOULD", "MAY" follow RFC 2119.
* Grammar symbols are in `monospace`; literal source text is in `"quotes"` or `monospace`.
* *Implementation notes* describe how the reference implementation does something when the
  observable behaviour does not force it. An implementation MAY do it differently.
* *Quirk* marks behaviour that is surprising, possibly accidental, but observable. A
  compatible implementation SHOULD reproduce it.
* `null` denotes the unique value of class `Nothing`.

---

## 1. Lexical structure

Source: `lex.d`, `ctype.d`, `parser.d` (literal conversion), `binding.d` (operator words).

### 1.1 Source text

Source text is a sequence of **bytes**. It is conventionally UTF-8, but the lexer works on
bytes. The only multibyte-aware rule is the one for mathematical-operator characters (§1.6). A
source unit is one of: a file, the standard input (interactive or not), or a string passed to
`value`, which is lexed as if a newline were appended.

### 1.2 Character classes

| class          | members                                                             |
|----------------|---------------------------------------------------------------------|
| *letter*       | `A`–`Z`, `a`–`z`, and **every byte 0x80–0xFF**                         |
| *digit*        | `0`–`9`                                                              |
| *alnum*        | letter ∪ digit ∪ { `$`, `'` }                                          |
| *white*        | space (0x20), tab (0x09), carriage return (0x0D)                     |
| *newline*      | line feed (0x0A)                                                      |
| *quote*        | `"`                                                                  |

Newline is **not** white space. It is a token (§1.10).

### 1.3 Comments and white space

Before each token the lexer repeatedly skips:

* white characters;
* **line comments**: `--` up to, but not including, the next newline (or end of input);
* **block comments**: `-*` … `*-`. They do **not nest**: the first `*-` ends the comment.
  An unterminated block comment is a lexical error ("EOF in block comment -* ... *- beginning
  here");
* a **shebang line**: if `#!` occurs at line 1, column 0, the rest of that line.

Note that `-*` always starts a comment, so `a -*b` is `a` followed by a comment.

### 1.4 Tokens

Each token carries: its *word* (the canonical interned string, with its parsing information,
§2.2), its source *position*, and a flag **followsNewline** that is true iff one or more newline
characters were skipped immediately before it (§1.10).

Words are **interned**: one word exists per distinct string. A word has a *type code*: `id`
(identifiers *and* operators), `int`, `real`, or `string`.

### 1.5 Token recognition order

After skipping white space and comments, the lexer examines the next character(s) and applies
the **first** matching rule:

1. end of input → **EOF** token;
2. newline → **NEWLINE** token (or **end-of-cell** in "full-lines" input mode, used by
   front ends such as TeXmacs);
3. the next two bytes begin a *mathematical-operator character* (§1.6) → a math-operator token;
4. a *letter* → an **identifier** (§1.7);
5. a *digit*, or `.` followed by a digit → a **number** (§1.8);
6. `///` → a **triple-slash string** (§1.9.2);
7. `"` → a **string** (§1.9.1);
8. otherwise → the **longest** operator or punctuation string from the fixed table in §1.11
   that is a prefix of the input. If none matches, it is a lexical error ("invalid character")
   and one byte is skipped.

Rule 6 precedes rule 8, so `a///b` starts a string, not `//`.

### 1.6 Mathematical-operator characters

A byte pair *b₁b₂* starts a math-operator character iff (with *c* = *b₁*·256 + *b₂*):

| condition on c                 | Unicode block covered                        |
|--------------------------------|----------------------------------------------|
| `c & 0xFFE0 == 0xC2A0`         | U+00A0–U+00BF (Latin-1 punctuation)          |
| `c == 0xC397` / `c == 0xC3B7`  | U+00D7 `×`, U+00F7 `÷`                        |
| `c & 0xFFFE == 0xE286`         | U+2180–U+21FF (arrows; also number forms)    |
| `c & 0xFFF8 == 0xE288`         | U+2200–U+23FF (math operators, misc. technical) |
| `c == 0xE29F`                  | U+27C0–U+27FF                                 |
| `c & 0xFFFC == 0xE2A4`         | U+2900–U+29FF                                 |
| `c & 0xFFF8 == 0xE2A8`         | U+2A00–U+2BFF                                 |

The token consists of the whole UTF-8 character: its length comes from the lead byte. If the
very next byte is `=`, that byte is appended as well. The resulting string is interned:

* if it names one of the three predefined Unicode operators `·` (U+00B7), `⊠` (U+22A0) or
  `⧢` (U+29E2), or their augmented forms `·=`, `⊠=`, `⧢=`, the token is that operator;
* otherwise the word gets **identifier** parse behaviour, so e.g. `∞` or `→` lexes as a
  one-character identifier. (`∞=` would likewise be an identifier word.)

### 1.7 Identifiers

```
identifier ::= letter alnum*
```

The identifier is maximal, but it also ends **before** any byte pair that starts a
math-operator character (§1.6). Examples: `x`, `x'`, `x$1`, `a1b2`, `αβ` (non-ASCII letters are
letters), `x'''`.

An identifier word whose string was given special parse behaviour (the reserved words of §2.3,
e.g. `if`, `then`, `and`, `not`, `SPACE`) is lexed exactly like an identifier. Only its parse
information differs. This is how keywords are implemented: **every keyword is simply an interned
word with non-default parse information**.

### 1.8 Numeric literals

```
number     ::= int-lit | real-lit
int-lit    ::= decimal | "0" ("b"|"B") bin+ | "0" ("o"|"O") oct+ | "0" ("x"|"X") hex+
decimal    ::= digit+
real-lit   ::= mantissa [ "p" digit+ ] [ ("e"|"E") ["+"|"-"] digit+ ]
             |  decimal "p" digit+ [ ("e"|"E") ["+"|"-"] digit+ ]
             |  decimal ("e"|"E") ["+"|"-"] digit+
mantissa   ::= digit+ "." digit*          -- "." not followed by another "."
             | digit* "." digit+
```

Exact algorithm (`lex.d:336`):

1. If the first character is `0` followed by `b`/`B` and a binary digit, consume the radix
   prefix and all binary digits. Likewise `o`/`O` with octal digits and `x`/`X` with hex digits.
   Otherwise consume all decimal digits. (A leading `.` consumes no digits here.)
2. Let *c* be the next character. The literal is **real** iff
   * the literal was decimal (no radix prefix) and *c* is `.` **not followed by another `.`**,
     or *c* is `p`, or *c* is `e`; **or**
   * *c* is `E`, regardless of radix. *Quirk*: `0b1E5` therefore lexes as one real-literal
     token and converts meaninglessly. Implementations SHOULD reject it.
3. For a real literal, consume in order: an optional `.` and following digits; an optional
   `p` that MUST be followed by at least one digit ("precision missing in floating point
   constant"); and an optional `e`/`E` that MUST be followed by digits, optionally signed
   ("exponent missing in floating point constant").
4. If a `.` immediately follows a real literal, a warning is issued. If a letter immediately
   follows any number (and does not begin a math-operator character), a warning is issued
   ("character 'x' immediately following number"). The letter still starts a new token, so
   `2x` means `2 x` (application, §6.3).

Consequences: `1..3` is `1`, `..`, `3` ✔. `1.` is a real ✔. `.5` is a real ✔. `x.5` is `x`
followed by the real `.5`.

**Values.**

* *int-lit*: an arbitrary-precision integer (`ZZ`), read in the indicated radix. Decimal
  literals with leading zeros are still decimal (`007` = 7).
* *real-lit*: a value of class `RR`. The precision is the number after `p` (in bits), or else
  the **current default precision** (53 unless changed at run time). The rest of the literal,
  with the `p…` part removed, is rounded to that precision as a decimal floating-point number
  (MPFR `mpfr_set_str`, base 10). If the precision after `p` overflows, evaluating the literal
  produces the error "expected precision to be a small non-negative integer".

Examples ✔: `1e3` → 1000 (an `RR`), `1p100` → `1` with 100-bit precision, `1.5p100e2` → 150,
`0x1F` → 31, `0b101` → 5, `0o17` → 15, `1e400` → 1e400 (MPFR has a wide exponent range).

### 1.9 String literals

#### 1.9.1 Double-quoted strings

A string runs from `"` to the next unescaped `"`. It MAY contain raw newlines. The backslash
escapes are:

| escape       | meaning                                                             |
|--------------|---------------------------------------------------------------------|
| `\n` `\t` `\r` `\a` `\b` `\v` `\f` | LF, TAB, CR, BEL (7), BS (8), VT (11), FF (12)   |
| `\e`, `\E`   | ESC (27)                                                              |
| `\"` `\\`    | the character itself                                                  |
| `\xHH`       | the byte with hex value HH (exactly 2 hex digits)                    |
| `\uHHHH`     | the UTF-8 encoding of code point U+HHHH (exactly 4 hex digits). A high surrogate `\uD8xx`–`\uDBxx` immediately followed by a low surrogate `\uDCxx`–`\uDFxx` combines into one supplementary code point. |
| `\o`, `\oo`, `\ooo` | the byte with octal value o… (1–3 octal digits, greedy; value taken mod 256) |

Any other character after `\` is a lexical error ("unknown escape sequence"). A `\x` or `\u`
with too few hex digits is also an error ("expected N more hex digit(s)"). After a string error
the lexer discards the rest of the line.

The value is a `String`, i.e. a byte string.

#### 1.9.2 Triple-slash strings

`///` starts a *verbatim* string: no escape processing takes place, and the content may span
lines. Doubled slashes let the content include runs of three or more slashes. The exact
algorithm (`lex.d:116`):

```
consume "///"
out := ""
loop
    ch := next character (consume it)          -- EOF here is an error
    while ch = '/' and the next three characters are "///":
        out := out + "/" ; consume 2 characters  -- ch is still '/'
    if ch = '/' and the next two characters are "//": break   -- closing "///"
    out := out + ch
consume 2 characters
```

Consequences: `//` inside is literal. Three consecutive slashes end the string. `////` inside
gives `///`, and 2k slashes (k ≥ 2) give k+1. A string ending in 1, 2, 3, … slashes is written
by closing with 5, 7, 9, … slashes. ✔ `///abc\d"e///` = `abc\d"e`.

### 1.10 Newlines and the `obeylines` mode

The lexer is called in one of two modes:

* **obeylines = true**: a newline is returned as a `NEWLINE` token.
* **obeylines = false**: newlines are skipped like white space, and the next real token gets
  `followsNewline = true`.

The parser (§2) decides the mode for each request. In short: newlines end statements at the
top level of a source unit, and are white space inside brackets and inside most compound
constructs.

The token peeked by the parser is cached. Once a token has been peeked in one mode, a later
request returns the cached token whatever mode that request asks for.

### 1.11 Operator and punctuation strings

These strings are recognised by longest match (rule 8 of §1.5):

```
(   )   [   ]   {   }   <|   |>   ;   ,
:=  =   <-  ->  =>  >>  <<  |-  ===>  <===  <==>  ==>  <==  ??
<   >   <=  >=  ===  ==  ?  =!=  !=  ~
||  :   |   ^^  &   ..  ..<  -  +  ++  **  *  /  \  \\  %  //  @  @@  @@?
#   #?  .   .?  ^  ^>  ^>=  ^<  ^<=  ^**  _  _>  _>=  _<  _<=  |_
!   ^!  _!  ^~  _~  ^*  _*  (*)
```

plus the **augmented assignment operators**: *op*`=` for each *op* in

```
<<  >>  ||  <==>  |-  ??  ==>  ===>  |  ^^  &  ..  ..<  -  +  ++  **  *  \\  /  \  %  //
@  @@  @@?  ~  |_  ^  _  ^**  ·  ⊠  ⧢
```

For example `+=`, `^**=`, `..<=`, `??=`, `||=`. The excluded operators are `==`, `<==`, `<===`,
`:`, SPACE, `or`, `and`, `xor`, `?`, and `_<`, `_<=`, `_>`, `_>=`, `^<`, `^<=`, `^>`, `^>=`.

*Quirk*: longest match can split things unexpectedly. For example `x<|y` lexes as `x`, `<|`,
`y`, and `a->-b` as `a`, `->`, `-`, `b`.

## 2. Syntax

Source: `parser.d`, `binding.d:150–376`, `parse.d:119–157`.

The Macaulay2 grammar is an **operator-precedence grammar**, and it is defined normatively by the
Pratt parser below. It cannot be written as a context-free BNF without losing fidelity, for four
reasons. Prefix operators bind with `max(context, own strength)`. Juxtaposition (application) is
an implicit infix operator triggered by the *next* token. Some operands may be empty. And newline
sensitivity depends on context. An informative EBNF approximation is given in §2.9.

### 2.1 Parse trees

| node                 | fields                                         | produced by |
|----------------------|------------------------------------------------|-------------|
| `Token`              | a single token (identifier, literal, operator word) | atoms |
| `Parentheses`        | `left`, `contents`, `right`                     | `( … )`, `[ … ]`, `{ … }`, `<\| … \|>` |
| `EmptyParentheses`   | `left`, `right`                                 | `()`, `[]`, `{}`, `<\|\|>` |
| `Adjacent`           | `lhs`, `rhs`                                    | juxtaposition `f x` |
| `Arrow`              | `lhs`, `rhs`                                    | `params -> body` |
| `Unary`              | `operator`, `rhs`                               | prefix operators |
| `Postfix`            | `lhs`, `operator`                               | postfix operators |
| `Binary`             | `lhs`, `operator`, `rhs`                        | infix operators |
| `Quote` / `GlobalQuote` / `ThreadQuote` / `LocalQuote` | `operator`, `rhs` (a token) | `symbol x`, `global x`, `threadLocal x`, `local x` |
| `IfThen`, `IfThenElse` | predicate, then, [else]                      | `if` |
| `WhileDo`, `WhileList`, `WhileListDo` | predicate, [list], [do]      | `while` |
| `For`                | variable, in, from, to, when, list, do (each optional) | `for` |
| `Try`, `TryThen`, `TryElse`, `TryThenElse`, `TryDo`, `TryThenDo` | primary, [then], [else], [except-variable, do] | `try` |
| `Catch`              | primary                                         | `catch` |
| `New`                | class, [of-parent], [from-initializer]          | `new` |
| `Dummy`              | position                                        | an *empty operand* |

`Dummy` marks an omitted operand. It can appear only where an **n-handler** (below) allows it:
the operands of `,` and `;`, and the arguments of `return`, `break`, `continue`, `throw`,
`step` and `finish`.

### 2.2 Parse information

Every word *w* carries four things:

* **lbp(w)** (called `precedence` in the source): the *left binding power*. An infix or postfix
  occurrence of *w* continues the current expression only while `lbp(w) > context`.
* **rbp(w)** (`binaryStrength`): the context in which the right operand of an infix *w* is
  parsed.
* **ubp(w)** (`unaryStrength`): the context in which the operand of a prefix *w* is parsed.
* **prefix handler** and **infix handler**: functions from §2.4.

Ordinary identifiers and all literals share one default: lbp = **62** (= *precSpace*), no
rbp/ubp, prefix handler `defaultunary`, infix handler `defaultbinary`.

### 2.3 The precedence table (normative)

Rows are in increasing lbp. "—" means *not applicable* (`nopr`, −1 in the source). The
*constructor* column names the helper in `binding.d` that defines the row's behaviour.

| lbp | tokens | rbp | ubp | prefix handler | infix handler | constructor |
|----:|--------|----:|----:|----------------|---------------|-------------|
| 2  | EOF                                   | 2  | —  | error        | nbinary  | nleftword |
| 4  | end-of-cell                           | 4  | —  | error        | nbinary  | nleftword |
| 6  | `)` `]` `}` `\|>`                        | —  | —  | error        | error    | (right bracket) |
| 8  | `;`                                   | 7  | —  | error        | nbinary  | nright |
| 8  | NEWLINE                               | 8  | —  | error        | nbinary  | nleftword |
| 10 | `,`                                   | 10 | 10 | nnunary      | nbinary  | nunarybinaryleft |
| 12 | `then` `else` `do` `list` `except`    | —  | 12 | error        | error    | token |
| 14 | `:=` `=` `<-` `=>` `>>` and all augmented *op*`=` | 13 | — | error | binary | binaryright |
| 14 | `->`                                  | 13 | —  | error        | arrow    | binaryright |
| 16 | `when` `of` `in` `from` `to`          | —  | 16 | error        | error    | token |
| 18 | `<<`                                  | 18 | 18 | unary        | binary   | unarybinaryleft |
| 20 | `\|-`                                  | 19 | 20 | unary        | binary   | unarybinaryright |
| 22 | `===>`                                | 21 | —  | error        | binary   | binaryright |
| 22 | `<===`                                | 21 | 22 | unary        | binary   | unarybinaryright |
| 24 | `<==>`                                | 23 | —  | error        | binary   | binaryright |
| 26 | `==>`                                 | 25 | —  | error        | binary   | binaryright |
| 26 | `<==`                                 | 25 | 26 | unary        | binary   | unarybinaryright |
| 28 | `or`                                  | 27 | —  | error        | binary   | binaryright |
| 28 | `??`                                  | 27 | 28 | unary        | binary   | unarybinaryright |
| 30 | `xor`                                 | 29 | —  | error        | binary   | binaryright |
| 32 | `and`                                 | 31 | —  | error        | binary   | binaryright |
| 34 | `not`                                 | —  | 34 | unary        | default  | unaryword |
| 36 | `<` `>` `<=` `>=` `?` `~`             | 35 | 36 | unary        | binary   | unarybinaryright |
| 36 | `===` `==` `=!=` `!=`                 | 35 | —  | error        | binary   | binaryright |
| 38 | `\|\|`                                  | 38 | —  | error        | binary   | binaryleft |
| 40 | `:`                                   | 39 | —  | error        | binary   | binaryright |
| 42 | `\|`                                   | 42 | —  | error        | binary   | binaryleft |
| 44 | `^^`                                  | 44 | —  | error        | binary   | binaryleft |
| 46 | `&`                                   | 46 | —  | error        | binary   | binaryleft |
| 48 | `..` `..<`                            | 48 | —  | error        | binary   | binaryleft |
| 50 | `-` `+`                               | 50 | 50 | unary        | binary   | unarybinaryleft |
| 50 | `++`                                  | 50 | —  | error        | binary   | binaryleft |
| 52 | `·`                                   | 52 | —  | error        | binary   | binaryleft |
| 54 | `**` `⊠` `⧢`                          | 54 | —  | error        | binary   | binaryleft |
| 56 | `[` `<\|`                              | —  | 6  | paren        | default  | (left bracket) |
| 58 | `*`                                   | 58 | 58 | unary        | binary   | unarybinaryleft |
| 58 | `/` `%` `//`                          | 58 | —  | error        | binary   | binaryleft |
| 58 | `\` `\\`                              | 57 | —  | error        | binary   | binaryright |
| 60 | `@`                                   | 59 | —  | error        | binary   | binaryright |
| 62 | identifiers, literals, math-operator identifiers | — | — | default | default | (parseWORD) |
| 62 | `(` `{`                               | —  | 6  | paren        | default  | (left bracket) |
| 62 | SPACE (the word; see §2.5.1)           | 61 | —  | error        | binary   | binaryright |
| 62 | `TEST` `time` `timing` `elapsedTime` `elapsedTiming` `breakpoint` `profile` `shield` `trap` | — | 12 | unary | default | special |
| 62 | `throw` `return` `break` `continue` `step` `finish` | — | 12 | nunary | default | special |
| 62 | `new`                                 | —  | 16 | new          | default  | special |
| 62 | `for`                                 | —  | 16 | for          | default  | special |
| 62 | `while` `if` `try` `catch`            | —  | 12 | while/if/try/catch | default | special |
| 62 | `symbol` `global` `threadLocal` `local` | — | 74 | quote     | default  | special |
| 64 | `(*)`                                 | —  | —  | error        | postfix  | postfix |
| 66 | `@@` `@@?`                            | 66 | —  | error        | binary   | binaryleft |
| 68 | `^~` `_~` `_*` `^*`                   | —  | —  | error        | postfix  | postfix |
| 70 | `^` `^>` `^>=` `^<` `^<=` `^**` `\|_` `_` `_>` `_>=` `_<` `_<=` `#?` `.` `.?` | 70 | — | error | binary | binaryleft |
| 70 | `#`                                   | 70 | **61** | unary     | binary   | unarybinaryleft (ubp overridden to precSpace−1) |
| 72 | `!` `^!` `_!`                         | —  | —  | error        | postfix  | postfix |

Read the table as follows:

* **binaryleft** (rbp = lbp) is left-associative; **binaryright** (rbp = lbp − 1) is
  right-associative. So `a^b^c` = `(a^b)^c` ✔, `a_b_c` = `(a_b)_c` ✔, `a:b:c` = `a:(b:c)` ✔,
  `a\b\c` = `a\(b\c)` ✔, `a@b@c` = `a@(b@c)` ✔, `a=>b=>c` = `a=>(b=>c)`, `a>>b>>c` = `a>>(b>>c)` ✔,
  `a<b<c` = `a<(b<c)`.
* A word with an "error" prefix handler cannot begin an expression. One with an "error" infix
  handler cannot follow one.
* The *keywords* are the identifier-shaped words in this table (`then` … `local`, `and`, `or`,
  `xor`, `not`, `SPACE`). Typing one where an operand is expected is a syntax error
  ("syntax error at 'then'").
* `symbol`, `global`, `threadLocal` and `local` have lbp 62, like every other word that begins an
  operand. (The source sets their "unary strength" to 74, but their handler never uses it.)

### 2.4 The parsing algorithm (normative)

The parser keeps a one-token lookahead buffer (§1.10). `peek(m)` returns the buffered token,
or lexes one in mode *m* and buffers it. `next(m)` returns and clears the buffer, or lexes one
in mode *m*. `ob` is the *obeylines* flag, passed down unchanged except where stated.

```
parse(prec, ob):                       -- an operand is required
    t := next(false)                   -- the first token of an operand always skips newlines
    return prefix(t)(t, prec, ob)

nparse(prec, ob):                      -- an operand may be empty
    t := peek(ob)
    if lbp(t) > prec: next(ob); return prefix(t)(t, prec, ob)
    else:             return Dummy(position of t)

accumulate(e, prec, ob):               -- the infix/postfix loop
    loop:
        t := peek(ob)
        if lbp(t) <= prec: return e
        next(ob)
        e := infix(t)(e, t, prec, ob)
```

Prefix handlers:

```
defaultunary(t, prec, ob)  = accumulate(Token t, prec, ob)
unary(t, prec, ob)         = accumulate(Unary(t, parse(max(prec, ubp(t)), ob)), prec, ob)
nunary(t, prec, ob)        = accumulate(Unary(t, nparse(ubp(t), ob)), prec, ob)       -- return, break, …
nnunary(t, prec, ob)       = if lbp(t) <= prec then error
                             else accumulate(Unary(t, nparse(ubp(t), ob)), prec, ob)  -- leading ","
paren(l, prec, ob):
    r := the right bracket matching l             -- ( ) [ ] { } <| |>
    if peek(false) = r: next(false); return accumulate(EmptyParentheses(l, r), prec, ob)
    e := parse(ubp(l) = 6, false)                 -- newlines are not significant inside brackets
    if next(false) ≠ r: error "expected r" (and "... to match this" at l)
    return accumulate(Parentheses(l, e, r), prec, ob)
error(t, …)                = syntax error "syntax error at 't'"
```

Infix handlers:

```
binary(lhs, t, prec, ob)   = Binary(lhs, t, parse(rbp(t), ob))          -- NB: no accumulate;
nbinary(lhs, t, prec, ob)  = Binary(lhs, t, nparse(rbp(t), ob))         -- the caller's loop continues
arrow(lhs, t, prec, ob)    = Arrow(lhs, parse(rbp(t), ob))
postfix(lhs, t, prec, ob)  = accumulate(Postfix(lhs, t), prec, ob)
default(lhs, t, prec, ob):                                              -- juxtaposition
    if followsNewline(t): error "missing semicolon or comma on previous line?"
    return Adjacent(lhs, prefix(t)(t, 61, ob))                          -- 61 = precSpace − 1
```

**Error recovery.** After a syntax error the parser discards input. In interactive or full-lines
mode it drops the buffered token. Otherwise it skips tokens while `lbp > prec`. The whole
statement is then abandoned (§7).

### 2.5 Derived rules and their consequences

#### 2.5.1 Juxtaposition (application)

Juxtaposition is the infix handler `default` belonging to the **following** token. It fires
only when that token has lbp > context and its infix handler is `default`. The tokens that can
begin an argument by juxtaposition are therefore:

* identifiers, literals, `(`, `{`, and the lbp-62 keywords (`if`, `for`, `new`, `symbol`,
  `time`, `return`, …). Here lbp = 62, so juxtaposition happens in any context below 62;
* `[` and `<|`, with lbp = 56. They start an argument only in a context below 56;
* `not`, with lbp = 34.

The right operand is parsed at context 61, so juxtaposition is **right-associative** and binds
tighter than every infix operator except those with lbp ≥ 62 (`@@`, the postfix operators, `^`,
`_`, `.`, `#`, …).

Examples ✔ (1.25.11):

| source        | parse                     |
|---------------|---------------------------|
| `f x y`       | `f (x y)` — so `f 1 2` fails, since `1 2` has no method |
| `f(x)(y)`     | `f ((x) (y))`             |
| `f x^2`       | `f (x^2)`                 |
| `f x!`        | `f (x!)`                  |
| `a - b c`     | `a - (b c)`               |
| `a b - c`     | `(a b) - c`               |
| `a * b c`     | `a * (b c)`               |
| `f -1`        | `f - 1` (binary minus, because `-` has a binary handler) |
| `#f x`        | `#(f x)` (the ubp of `#` is 61 < 62) |
| `-f x`        | `-(f x)`                  |
| `a*f[x]`      | `(a*f)[x]` (the operand of `*` is parsed at 58 ≥ 56, so `[` does not attach to `f`) |
| `f[x]`        | `f [x]` at top level       |

The word `SPACE` is interned with the parse information shown in §2.3 only so that the binary
operator "SPACE" exists as a *method key* (§6.5). Writing `SPACE` in source is a syntax error.

#### 2.5.2 Prefix operators

A prefix operator parses its operand at `max(context, ubp)`, then keeps accumulating at the
outer context. So `-a*b` = `-(a*b)` ✔, `-a+b` = `(-a)+b` ✔, `-a^2` = `-(a^2)`, `-a!` = `-(a!)` ✔,
`not a == b` = `not (a==b)` ✔, `not a and b` = `(not a) and b` ✔, `<<a<<b` = `(<<a)<<b` ✔.

#### 2.5.3 Postfix operators

`a^b!` = `a^(b!)` ✔. `a!^b` = `(a!)^b` ✔. `a^~ b` = `(a^~) b` ✔. `x (*)` is postfix `(*)`.

#### 2.5.4 Commas and semicolons

`,` (lbp 10) and `;` (lbp 8) are *n*-operators: their right operand, and for `,` also the left
operand (via prefix `nnunary`), may be **empty**. So `(1,2,)`, `(,1)`, `(a;)` and `(1,,2)` are all
well-formed. `,` is left-associative. `;` is right-associative, and it binds more loosely than
`,`: `(a; b, c)` = `(a; (b, c))`.

#### 2.5.5 Keyword forms

In the grammars below, **E**_p is "`parse(p, …)`". Clause bodies are parsed at 12, so they
extend over assignments and arrows (lbp 14) but stop at `,` `;` `then` `else` `do` `list`
`except` and closing brackets. "Mode *f*" means obeylines = false, and "mode *ob*" means the
mode inherited from the context.

```
if-expr    ::= "if" E₁₂(f) "then" E₁₂(ob) [ "else" E₁₂(ob) ]
                   -- "then" is read in mode f; "else" is looked for with peek(ob)
while-expr ::= "while" E₁₂(f) ( "do" E₁₂(ob)
                              | "list" E₁₂(ob) [ "do" E₁₂(ob) ] )
for-expr   ::= "for" E₁₆(f)
                 ( "in" E₁₆(f) | [ "from" E₁₆(f) ] [ "to" E₁₆(f) ] )
                 [ "when" E₁₆(f) ]
                 ( "do" E₁₂(ob) | "list" E₁₂(ob) [ "do" E₁₂(ob) ] )
try-expr   ::= "try" E₁₂(ob)
                 [ "then" E₁₂(ob) ]
                 [ "else" E₁₂(ob) | "except" E₁₂(ob) "do" E₁₂(ob) ]
                                     -- except/do is not allowed together with else
catch-expr ::= "catch" E₁₂(ob)
new-expr   ::= "new" E₁₆(ob) [ "of" E₁₆(ob) ] [ "from" E₁₆(ob) ]
quote-expr ::= ("symbol" | "global" | "threadLocal" | "local") T
                 -- T: the next token (mode f); it MUST have type code id, i.e. an identifier
                 -- or an operator word: "symbol +" and "symbol SPACE" are valid
special    ::= ("time" | "timing" | "elapsedTime" | "elapsedTiming" | "profile"
                | "shield" | "trap" | "breakpoint" | "TEST") E_max(ctx,12)(ob)
control    ::= ("return" | "break" | "continue" | "throw" | "step" | "finish") [ E₁₂ ]
```

Every keyword form is followed by `accumulate(result, context, ob)`, so for example
`(if a then b else c) + 1` works, and `if a then b else c + 1` puts `c + 1` in the else clause.

*Consequences:*

* In `for`, the variable is parsed at 16, so it stops at `in`, `from`, `to` and `when`, which
  all have lbp 16. The `in`/`from`/`to`/`when` clauses stop at `do`/`list`. At most one of `in`
  or `from/to` is allowed.
* `new` parses its clauses at 16, so `new T + new T` = `new (T + new T)` and
  `new A === new A` = `new (A === new A)` ✔. Write `(new T) + (new T)`.
* `try x then y`, `try x else y`, `try x then y else z`, `try x except e do y` and
  `try x then y except e do z` are the only combinations (`parser.d:454`).

#### 2.5.6 Function literals

```
arrow-expr ::= params "->" E₁₃
params     ::= identifier                   -- a "rest" parameter: receives the whole argument
             | "(" ")"                      -- no parameters
             | "(" identifier { "," identifier } ")"
```

The body is parsed at 13, so `->` is right-associative (`x -> y -> x+y`) and the body swallows
assignments, but it stops at `,` and `;`. `f = x -> x, 1` is the sequence `(f = (x -> x)), 1`.
Parameter-list validity is checked at binding time (§3.5), not by the parser.

#### 2.5.7 Newline sensitivity

Statements (§2.6) are parsed with obeylines = true. As a result:

1. A NEWLINE token (lbp 8) ends the current top-level statement, like `;`, unless the parser
   is currently in a sub-parse run in mode *f*. Those are: bracket contents, the predicate of
   `if`/`while`, and the variable and `in`/`from`/`to`/`when` clauses of `for`.
2. The **first token of every operand** is fetched with `next(false)`, so a line that ends
   with a binary or prefix operator (or `->`, `=`, `then`, `do`, `,` …) continues on the next
   line.
3. Outside brackets, a line that *begins* with a binary operator does **not** continue the
   previous statement.
4. `else`, the `do` after `list`, `of`, `from` (after `new`), and `then`/`else`/`except` after
   `try` are looked for with `peek(ob)`. At top level, then, **`else` at the start of a new
   line is not attached to a preceding `if`**: ✔ the `if` statement ends at the newline and
   the next line gives "syntax error at 'else'". Inside parentheses it is attached normally.
5. Inside brackets a newline is white space, **except** that a token that would start a
   juxtaposition after a newline is an error ("missing semicolon or comma on previous line?").
   So `(f\n x)` is an error, while `(f\n + x)` is `f + x`.

### 2.6 Statements

A source unit is a sequence of **statements**, parsed by the loop of §7:

```
unit      ::= { NEWLINE | ";" | statement terminator }  EOF
statement ::= E₈   (parse(8, obeylines = true))
terminator::= ";" | NEWLINE | end-of-cell | EOF
```

After a statement is parsed, the next token MUST be a terminator. Anything else, necessarily a
right bracket, gives "syntax error: unmatched )". A statement terminated by `;` is evaluated
but its value is not printed (§7).

### 2.7 Brackets

| brackets     | parse tree → value (§4)            |
|--------------|------------------------------------|
| `( … )`      | `Sequence`; a single element is just that element |
| `{ … }`      | `List`                              |
| `[ … ]`      | `Array`                             |
| `<\| … \|>`     | `AngleBarList`                      |

The contents are one expression parsed at 6, so they can include `;` and `,` sequences.

### 2.8 Operator words usable as values

Any operator word can be quoted with `symbol op` to obtain the corresponding **keyword** value.
Keywords are used as method keys (§6.5).

### 2.9 Informative EBNF approximation

The following approximation (lowest precedence first) is **not normative**. It ignores the
newline rules, the `max()` rule for prefix operators, and empty operands.

```
stmt    := seq
seq     := comma { ";" [comma] }                          -- right-assoc
comma   := [assign] { "," [assign] }                      -- left-assoc
assign  := lhs (":=" | "=" | "<-" | "=>" | ">>" | augop | "->") assign | ctrl
ctrl    := "if" … | "while" … | "for" … | "try" … | "catch" … | "new" … | kwunary | lo
lo      := "<<"-level … "or"/"??" … "xor" … "and" … "not" … comparison … "||" … ":" … "|" …
           "^^" … "&" … ".."… "+ - ++" … "·" … "** ⊠ ⧢" … bracket-arg(56) … "* / % // \ \\" …
           "@" … apply
apply   := post { post }                                  -- right-assoc juxtaposition
post    := atom { "(*)" | "@@" … | "^~ _~ ^* _*" | "^ _ . # …" operand | "! ^! _!" }
atom    := identifier | number | string | bracketed | "symbol" T | "global" T | …
```

## 3. Names, dictionaries and scopes (binding)

Source: `binding.d:418–954`, `expr.d:47–160`.

Between parsing and evaluation, each statement's parse tree goes through a **binding** pass
(`localBind`). It resolves every identifier token to a *symbol* and allocates storage for local
variables. Binding errors are reported, and the statement is then not evaluated.

### 3.1 Symbols

A **symbol** is a named storage location. Its attributes are: its name (word), the position of
its definition, the *frame id* of the scope that owns it, an index within that scope's frame, a
**protected** flag (assignment forbidden), a **thread-local** flag, and a flag that warns when
the symbol is used.

The value `SymbolClosure(frame, symbol)` is how a symbol appears at run time (class `Symbol`,
or `Keyword` for operator words and keywords, §5.4).

### 3.2 Dictionaries

A **dictionary** maps names to symbols. Each one has a frame id, a size (the number of symbols
it owns), a *protected* flag (no new symbols may be added), and an *outer* dictionary, which
may be itself for the outermost.

There are four kinds:

* **Global dictionaries** (frame id 0). They are chained together: the chain is the
  `dictionaryPath`, with the current package's dictionary first and `Core`'s later. All global
  symbols share one global frame. Thread-local global symbols live in a per-thread frame.
* **Static local dictionaries**. One is created for each file being loaded, for each string
  evaluated by `value`, and for each interactive session and debugger level. It has a single
  frame that grows as symbols are added. Its outer link is itself, so lookup falls through
  directly to the global chain.
* **Transient local dictionaries**, created by binding for function literals, `for` loops and
  `try … except`. Each run-time activation gets a fresh frame, except in the `for` case
  (§6.9).
* The dummy dictionary (internal).

### 3.3 Name lookup

To bind an identifier token *t* in dictionary *D*:

1. If *t* is a numeric literal, do nothing.
2. Walk *D*, *D*.outer, … until the chain ends, then walk the global chain. The first symbol
   named *t* found is the binding.
3. **If no symbol is found, a new *global* symbol is created**. It is created in the first
   non-protected dictionary of the global chain, normally the current package's or `User`'s.
   Its initial value is the symbol itself, unless the name is not a valid symbol name or the
   symbol is thread-local; the initial value is then `null`.
   So **an undefined identifier evaluates to itself**: `z` ⇒ `z` ✔. This happens at *binding
   time*, even for code that is never executed.

Operator tokens are looked up the same way, but a missing operator is never created. It is an
error ("undefined symbol"), which cannot happen for the built-in operators.

### 3.4 Scopes

Only these constructs open a new (transient) scope:

| construct | scope contains | bound in the *enclosing* scope |
|-----------|----------------|--------------------------------|
| `params -> body` | parameters, then `body` | — |
| `for v … when W list L do B` | `v`, `W`, `L`, `B` | the `in`, `from` and `to` clauses |
| `try P then S except v do B` | `v`, `B` | `P`, `S` |

`if`, `while`, `catch`, `new` and parentheses do **not** open scopes. A `:=` anywhere inside a
function body, even in an unexecuted branch, allocates a slot in that function's frame.

### 3.5 Binding of definitions

| form | effect at binding time |
|------|------------------------|
| `x := e` | A **new** symbol `x` is created in the *current* dictionary, even if one exists (a warning is given if the existing one is in the same scope: "local declaration of x shields variable with same name"). **Then** `e` is bound. So in `e`, `x` already refers to the new variable. *Quirk* ✔: in `x = 5; f = () -> (x := x + 1; x); f()` the rhs `x` is the **new**, `null`-valued local, so the call fails (no method for `null + 1`). Recursion `f := n -> … f(n-1) …` works for the same reason. |
| `x = e` | `x` is bound by ordinary lookup (§3.3), which may create a global. Then `e` is bound. |
| `(x, y, …) := e` / `(x, y, …) = e` | Each item that is an identifier is treated as in the two rows above. Any other item is bound as an ordinary expression. |
| `local x` | Look up `x` **only** in the current dictionary's own table, and create it there if absent. |
| `global x` | Bind `x` in the global chain (it may be created). |
| `threadLocal x` | As `global x`, but the symbol is thread-local. It is an error if a non-thread-local global with that name exists. |
| `symbol x` | Ordinary lookup (§3.3). |
| `e.x`, `e.?x` | `e` is bound normally. `x` MUST be an identifier and is bound in the **global** dictionary chain. Global binding is used even inside a scope that has a local `x`. |
| parameters `x ->`, `(x, y) ->` | Each parameter creates a new symbol in the function's new scope. Duplicate parameter names are an error. A single bare identifier `x ->` makes a *rest parameter* (§6.3). `(x) ->` is an ordinary 1-parameter function. `() ->` takes 0 parameters. Anything else is an error ("expected parenthesized argument list or symbol"). |
| `for v …`, `except v` | `v` MUST be a single identifier. It gets slot 0 of the new scope. |

### 3.6 Well-formedness of assignment left-hand sides

The binder checks the left operand of `=` and `:=`:

| left-hand side | `:=` allowed if | `=` allowed if |
|----------------|-----------------|----------------|
| identifier | always | always |
| other literal token | never ("expected a symbol to left of …") | never |
| `( … )` or `()` | always (parallel assignment) | always |
| `f x` (Adjacent) | always | always |
| `op x` (Unary) | *op* ∈ U | *op* ∈ U |
| `x op` (Postfix) | *op* ∈ P | *op* ∈ P |
| `x op y` (Binary) | *op* ∈ B | *op* ∈ B ∪ { `.`, `#` } |
| `new …` | always | never |
| anything else | "left hand side of assignment inappropriate" | same |

where

* **U** (operators with unary methods) = `*` `-` `+` `<<` `??` `<==` `<===` `~` `not` `|-` `?`
  `<` `>` `<=` `>=`;
* **P** (postfix) = `!` `^!` `_!` `(*)` `^*` `_*` `^~` `_~`;
* **B** (operators with binary methods) = `<<` `>>` `==` `?` `||` `<==>` `|-` `??` `==>` `===>`
  `<==` `<===` `:` `|` `^^` `&` `..` `..<` `-` `+` `++` `**` `*` `\\` `/` `\` `%` `//` `@` SPACE
  `@@` `@@?` `or` `and` `xor` `~` `|_` `^` `_` `^>` `_>` `^>=` `_>=` `^<` `_<` `^<=` `_<=` `^**`
  `·` `⊠` `⧢`.

For `x.y = e`, `y` MUST be an identifier.

## 4. From parse tree to code

Source: `convertr.d`. The bound tree is translated into a tree of *code* nodes, which §6
evaluates. The translation fixes several syntactic identities, and an implementation MUST
respect them whatever its internal representation.

### 4.1 Sequences of expressions

`separated(e, sep)` flattens a `,`- or `;`-tree into a list of elements:

* `Binary(a, sep, b)` → `separated(a) ++ separated(b)`;
* `Unary(sep, b)` (a leading separator) → `[null-code] ++ separated(b)`;
* `Dummy` (an empty operand) → `[null-code]`;
* anything else, *including* a parenthesized expression → `[convert(e)]`, with no further
  flattening.

Consequences ✔: `(1,)` is the 2-element sequence `(1, null)`. `(,1)` = `(null, 1)`.
`(1,,2)` = `(1, null, 2)`. `#(1,2,)` = 3. `(a;)` evaluates `a` and yields `null`.

### 4.2 Translation table

| parse tree | code |
|------------|------|
| integer / real / string literal | constant. A real literal whose precision is invalid becomes an *error* constant. |
| identifier | variable reference (global, thread-local, or local at (depth, index)) |
| `e₁, e₂, …` (a comma tree not in brackets) | **sequence** of `separated(·, ",")` |
| `e₁; e₂; …` | **semicolon block** of `separated(·, ";")` |
| `( c )` / `()` | **sequence** of `separated(c, ",")` / the empty sequence |
| `{ c }` / `{}` | **list** code |
| `[ c ]` / `[]` | **array** code |
| `<\| c \|>` / `<\|\|>` | **angle-bar list** code |
| `Adjacent(f, a)` | **apply**(f, a) |
| `params -> body` | **function literal** |
| `Unary(op, e)`, `Postfix(e, op)` | **unary op call**(op, e) |
| `Binary(e, op, f)` | **binary op call**(op, e, f), except for the cases below |
| `e . x`, `e .? x` | binary op call with right operand **the symbol x** (not its value) |
| assignments | see §4.3 |
| `symbol x`, `global x`, `threadLocal x`, `local x` | **symbol literal** (a `SymbolClosure` for that symbol in the appropriate frame) |
| `if`, `while`, `for`, `try`, `catch`, `new` | the corresponding control code |

After translation, a **sequence of length exactly 1 is replaced by its element** (`unseq`).
So `(e)` ≡ `e`, and `f(x)` is `f` applied to `x`, not to a 1-tuple. Lists, arrays and
angle-bar lists are *not* unwrapped: `{e}` is a 1-element list.

### 4.3 Assignment forms

| source | code | semantics |
|--------|------|-----------|
| `x = e`, `x := e` | store to variable | §6.6.1 |
| `(p₁,…,pₙ) = e`, `(p₁,…,pₙ) := e` | **parallel assignment** (lhs = `separated`) | §6.6.2 |
| `() = e`, `() := e` | parallel assignment with 0 targets | §6.6.2 |
| `x # k = e`, `x . s = e` | **element store** (x, k, e) | §6.6.3 |
| `x op y = e` (other binary op) | **install value** ((op, `=`), x, y, e) | §6.6.4 |
| `f x = e` | install value ((SPACE, `=`), f, x, e) | §6.6.4 |
| `op x = e`, `x op = e` (postfix) | **unary install value** ((op, `=`), x, e) | §6.6.4 |
| `x op y := e` | **install method** (op, x, y, e) | §6.5.3 |
| `f x := e` | install method (SPACE, f, x, e) | §6.5.3 |
| `op x := e`, `x op := e` | **unary install method** (op, x, e) | §6.5.3 |
| `new T := e` | install method (NewMethod, T) | §6.8 |
| `new T of P := e` | install (NewOfMethod, T, P) | §6.8 |
| `new T from I := e` | install (NewFromMethod, T, I) | §6.8 |
| `new T of P from I := e` | install (NewOfFromMethod, T, P, I) | §6.8 |
| `L op= e` (augmented) | **augmented assignment** (op, L, e) | §6.7 |

## 5. Values and basic types

Source: `parse.d:288–473` (the `Expr` union), `expr.d:245–353` (built-in classes),
`classes.dd`, `hashtables.dd`, `equality.dd`.

### 5.1 The value universe

Every run-time value is one of the following **representations**. An implementation is free
to choose its own concrete data structures.

| representation | contents | class (`class x`) |
|----------------|----------|-------------------|
| Boolean | `true` / `false` (unique values) | `Boolean` |
| Nothing | the unique value `null` | `Nothing` |
| ZZ | arbitrary-precision integer | `ZZ` |
| QQ | rational in lowest terms, denominator > 0 | `QQ` |
| RR | binary floating point with precision p ≥ 2 bits (MPFR) | `RR` |
| CC | pair of RR of equal precision | `CC` |
| RRi | interval of RR (MPFI) | `RRi` |
| CCi | complex interval | `CCi` |
| String | immutable byte string | `String` |
| Net | 2-D text block (list of rows, baseline) | `Net` |
| Sequence | immutable tuple of values | `Sequence` (always) |
| List | *(class C, elements, mutable?, hash)* | C (a descendant of `BasicList`) |
| HashTable | *(class C, parent P, table key→value, mutable?, hash)* | C (a descendant of `HashTable`) |
| SymbolClosure | *(frame, symbol)* | `Symbol`, or `Keyword` if the name is an operator or keyword |
| SymbolBody | a symbol without a frame | `SymbolBody` |
| FunctionClosure | *(frame, function code)*: a user function | `FunctionClosure` |
| CompiledFunction / CompiledFunctionClosure | built-in function (optionally with captured values) | `CompiledFunction` / `CompiledFunctionClosure` |
| FunctionBody / CompiledFunctionBody | code of a function without environment | `FunctionBody` / `CompiledFunctionBody` |
| DictionaryClosure | *(frame, dictionary)* | `GlobalDictionary` or `LocalDictionary` |
| Pseudocode / PseudocodeClosure | code (with frame) as a value | `Pseudocode` / `PseudocodeClosure` |
| Error | *(position, message, value, printed?, frame)* | `Error` or a subclass (§6.4) |
| SpecialExpr | *(class C, value v)*: v viewed as an instance of C | C |
| File, NetFile, Database, Task, Mutex, AtomicInt, Pointer, … | system objects | `File`, … |
| Raw… | engine objects (rings, matrices, …) | `RawRing`, `RawMatrix`, … |

**SpecialExpr** is how a non-list, non-hash-table value (typically a function) gets a
user-defined class. For example, a `MethodFunction` is a compiled function closure wrapped with
class `MethodFunction`. Applying a SpecialExpr applies its wrapped value (§6.3). `parent` of a
SpecialExpr is the parent of the wrapped value.

### 5.2 Classes, parents and types

Every value *x* has a **class**, `class x`, which is always a `HashTable`. Every `HashTable` has
a **parent** field. The **ancestors** of a class *C* are *C*, `parent C`, `parent parent C`, …,
ending at `Thing`, whose parent is `Thing` itself.

* `ancestor(A, B)` is true iff B is among the ancestors of A.
* `instance(x, T)` is `ancestor(class x, T)`.
* `parent x` is `x`'s parent field if *x* is a hash table, the wrapped value's parent for a
  SpecialExpr, and `Nothing` otherwise.
* A **type** is a hash table whose class is `Type` (or a descendant). Types are *mutable* hash
  tables, since `parent Type` = `MutableHashTable`. Methods are stored in them (§6.5).
* `basictype C` is the ancestor of *C* whose parent is `Thing`. The basic types are the direct
  children of `Thing`.

The built-in type hierarchy ("A ← B" means `parent B = A`):

```
Thing                                         (class Type, parent Thing)
├── HashTable                                 (class Type)
│   ├── MutableHashTable
│   │   ├── Type                               (every type's class; parent MutableHashTable)
│   │   │   ├── Ring
│   │   │   └── RingFamily
│   │   │       └── InexactFieldFamily
│   │   └── CacheTable
│   └── OptionTable
├── BasicList
│   ├── VisibleList
│   │   ├── List
│   │   ├── Sequence
│   │   ├── Array
│   │   └── AngleBarList
│   ├── MutableList
│   ├── Option                                 (x => y)
│   ├── Time
│   └── RingElement
├── Number
│   ├── ZZ, QQ                                 (class Ring)
│   └── InexactNumber
│       └── RR, CC, RRi, CCi                   (class InexactFieldFamily)
├── Function
│   ├── FunctionClosure
│   ├── CompiledFunction
│   └── CompiledFunctionClosure
├── Symbol
│   └── Keyword
├── Net
│   └── String
├── Dictionary
│   ├── GlobalDictionary
│   └── LocalDictionary
├── Pseudocode
│   └── PseudocodeClosure
├── FunctionBody
│   └── CompiledFunctionBody
├── Boolean, Nothing, Error, File, NetFile, Database, SymbolBody, Task, Pointer,
│   AtomicInt, Mutex, FileOutputSyncState, PythonObject, LibxmlNode, LibxmlAttribute,
│   MysqlConnection, MysqlField, MysqlResult
└── RawObject
    └── RawMonomial, RawMonomialOrdering, RawMonoid, RawMonomialIdeal, RawRing,
        RawRingElement, RawRingMap, RawFreeModule, RawMatrix, RawMutableMatrix,
        RawMutableComplex, RawComputation, RawStraightLineProgram, RawPathTracker,
        RawHomotopy, RawSLEvaluator, RawSLProgram, RawPointArray
```

Some checks against the tree ✔: `class Thing` = `Type`, `class Type` = `Type`,
`parent Type` = `MutableHashTable`, `parent ZZ` = `Number`, `class ZZ` = `Ring`,
`parent Thing` = `Thing`. Note that `Sequence` is **not** a `List`. Both are `VisibleList`s,
but a Sequence is a distinct representation whose class is always `Sequence`.

The kernel also predefines these constants: `true`, `false`, `null`, `stdio`, `stderr`,
`commandLine`, `environment`, … (see `setupconst` calls).

### 5.3 Mutability and hashing

* **Sequences, Strings, numbers, Booleans, `null`, symbols** are immutable.
* A **List** is mutable iff its class descends from `MutableList`. Only mutable lists support
  element assignment (§6.6.3).
* A **HashTable** is mutable iff it was created mutable. `new T` makes it mutable iff *T*
  descends from `MutableHashTable` (§6.8). Types are mutable.
* Every value has a hash code. For immutable composite values the hash is **structural**:
  equal (`===`) values have equal hashes. A mutable hash table or list gets a fresh serial
  number on creation, so its identity is its hash. `CacheTable`s have hash 0 and are all
  `===`-equal to each other.
* Hash tables are unordered. `keys` returns keys in bucket order, which is
  implementation-defined but deterministic.

### 5.4 Symbols and keywords

`symbol x` (or evaluating an unassigned global `x`, §3.3) yields a `SymbolClosure`. Its class
is `Keyword` if the word has non-default parse information (all operators and keywords, e.g.
`symbol +`, `symbol if`, `symbol SPACE`). Otherwise the class is `Symbol`. The value stored in
a symbol is read with `value s` and written with `s <- v` (§6.10).

Two symbol closures are `===`-equal iff they have the same symbol and the same frame. Global
symbols always use the global frame.

### 5.5 Strict equality `===`

`x === y` (and its negation `x =!= y`) is total: it never calls user methods, and it always
returns a Boolean, unless an operand evaluation errors. It is defined by (`equality.dd`):

* identical representations → `true`;
* ZZ/ZZ, QQ/QQ: numeric equality. **Different numeric representations are never `===`**, so
  `3 === 3.0` is `false` ✔ and `1/2 === 0.5` is `false` ✔;
* RR/RR, CC/CC, RRi/RRi, CCi/CCi: strict equality of value **and precision**. ✔
  `1.0p100 === 1.0p53` is `false`, although `==` is `true`;
* String/String: byte equality. Net/Net: equality of rows and baseline;
* Sequence/Sequence: equal length and elementwise `===`;
* List/List: both immutable, same class (by `===`), equal hash, equal length, elementwise `===`;
* HashTable/HashTable: same class and parent, both immutable, same entries. A mutable table is
  `===` only to itself;
* SymbolClosure: same symbol and frame. DictionaryClosure: same frame and dictionary.
  Pseudocode: same code (and frame);
* SpecialExpr: same class and `===` wrapped values;
* functions, files, `null`, Booleans, mutable engine objects: only identity;
* engine objects: engine equality where defined;
* anything else, including values of different representations → `false`.

### 5.6 Nets, strings and printing

`String` is a subclass of `Net`, and a string is a one-row net. How values *print* is defined
by the library (`net`, `toString`, and the `Print` hooks of §7). The core only needs to provide
the operations the library uses.

## 6. Evaluation

Source: `evaluate.d`, `actors*.d`, `hashtables.dd`, `classes.dd`.

### 6.1 Environments

Evaluation happens relative to a **current frame**. A frame is a vector of values plus a link
to its **outer frame**. A variable reference compiled as (depth *d*, index *i*) reads slot *i*
of the frame *d* links out. Globals live in the single global frame (per-thread for
`threadLocal` symbols). A slot never assigned holds `null`.

Required observable properties:

1. **Closures capture frames by reference.** ✔ `x := 10; f = () -> x; x = 20; f()` ⇒ 20.
   ✔ `g = () -> (n := 0; () -> (n = n+1)); c = g(); c(); c(); c()` ⇒ 3.
2. **Each function call gets a fresh frame**, holding the parameters followed by all `:=`
   locals of the body.
3. **A `for` loop allocates one frame for the whole loop.** The loop variable is overwritten
   in place on each iteration, so closures created in different iterations share it.
   ✔ `L = for i from 1 to 3 list (() -> i); apply(L, f -> f())` ⇒ `{3,3,3}`.
4. A `try … except v do B` allocates a frame for `v` when the handler runs.

*Implementation note*: the reference implementation computes frame depths statically and omits
frames for scopes with no variables. Any environment model that gives the properties above is
acceptable.

### 6.2 Outcomes: values and abrupt completions

Evaluation of any code yields either a **value** or an **abrupt completion**. The reference
implementation represents both uniformly: an abrupt completion is an `Error` record whose
*message* field distinguishes these kinds:

| kind | created by | carries | intercepted by |
|------|-----------|---------|----------------|
| **error** | failing operations, `error(…)` (library) | message, optional value, position | `try`, `trap`, `??` (§6.9); otherwise it reaches the top level, which prints it (§7) |
| **return** | `return [e]` | value (`null` if omitted) | the innermost enclosing **function application**; also `load`/`value`/the top level (§7) |
| **break** | `break [e]` | value or "none" | the innermost enclosing **loop** (`while`, `for`) |
| **continue** | `continue [e]` | value or "none" | the innermost enclosing **loop**; also the combining functions (`applyKeys` with merge, `merge`, `combine`), which treat it as "drop this key" |
| **throw** | `throw e` | value | the innermost enclosing **`catch`** |
| **step / finish / unwind** | debugger | — | the debugger (§7.3) |

These rules follow:

* Every construct that evaluates subexpressions checks each result. On an abrupt completion
  it stops at once and propagates it. Operands are evaluated **left to right**, and every
  operator evaluates its left operand before its right, except where §6.10 says otherwise.
* **`try` does not intercept return, break, continue or throw**, and interrupts are not
  catchable.
* A control abrupt completion that escapes to where no construct handles it (for example
  `break` outside a loop) is reported at top level as "unhandled break command" and so on.
* There is a recursion limit, 300 by default: a function application at a deeper nesting
  depth fails with "recursion limit of 300 exceeded". Implementations SHOULD provide a
  comparable limit.

When an **error** propagates out of code with a known source position and has not been
positioned yet, the position is recorded. The error is printed immediately with "--back trace--"
lines while it unwinds, unless errors are suppressed, as they are inside `try` (§7.3).

### 6.3 Function application

`f a` (**apply**): evaluate `f` first.

* If `f` is a **FunctionClosure** with *n* declared parameters:
  * if the argument code `a` is a sequence code (`(a₁,…,aₖ)` with k ≠ 1, including `()`),
    evaluate the *k* items left to right to get the arguments;
  * otherwise evaluate `a`. If the value is a `Sequence`, its elements are the arguments.
    Otherwise the single value is the one argument.
  * **Rest parameter** (`x -> …`): `x` is bound to the whole argument. That is a `Sequence`
    when there are 0 or ≥ 2 arguments or a sequence was passed, otherwise the single value.
    ✔ `f = x -> x; f()` ⇒ `()`, `f(1,2)` ⇒ `(1,2)`.
  * **Ordinary parameters**: the argument count MUST equal *n*, else the error "expected n
    argument(s), but got k". A single non-sequence argument counts as 1.
    ✔ `f = (x,y) -> x+y; s = (3,4); f s` ⇒ 7. `f {1,2}` is an error, since a list is one
    argument.
  * A fresh frame (§6.1) is created whose outer frame is the closure's frame. Parameters
    fill slots 0…n−1 and all other slots are `null`. The body is evaluated in it. A **return**
    completion becomes the result value. Other abrupt completions propagate.
* If `f` is a **CompiledFunction** or CompiledFunctionClosure: evaluate `a` to a single value
  (a sequence stays a sequence) and pass it to the built-in.
* If `f` is a **SpecialExpr** wrapping a function: apply the wrapped function as above. If it
  wraps a non-function: dispatch as in the next case.
* Otherwise evaluate `a` to *v* and call the **binary method** for SPACE on (`f`, *v*)
  (§6.5.1), with keys (SPACE, `class f`, `class v`). If none exists and `f` is a symbol, the
  error is "symbol 'f' has not been defined as a function". Otherwise it is "no method for
  adjacent objects". Example: `R x` where `R` is a ring is a library method on (Ring, …).

*Implementation note*: the reference implementation evaluates a tail call `g x` at the end of
a one-argument function body without growing the stack. It does not do this for general
calls.

### 6.4 Errors as values

`try … except e do …` and `trap` expose an error as a value of class `Error`. If the error's
value field holds a hash table descending from `Error`, the class is that table instead
(`classes.dd:122`). How errors are created and presented (`error`, the `Error` subclasses,
message formatting) is library-defined.

### 6.5 Operators and method dispatch

Every operator is implemented by a built-in routine. Many routines first handle some
combinations of basic types directly (§6.10), and otherwise **dispatch to a method** stored in
the class hierarchy. The *method key* of an operator is its keyword symbol (`symbol +`, …).

#### 6.5.1 Lookup

* **Unary** method for operator *op* on *x*: search the ancestors of `class x`, most specific
  first, for key *op*. The same lookup finds a method function keyed by a function *f*, as
  installed by `f T := …`.
* **Binary** method for *op* on (*x*, *y*):
  ```
  for L in ancestors(class x):          -- most specific first
      for R in ancestors(class y):
          if the key (op, L, R) is present: return its value
  return none
  ```
  The entry for (op, L, R) is stored in whichever of L, R has the greater internal hash. An
  implementation MAY store it anywhere, as long as lookup follows the loop order above.
* **Ternary / quaternary** methods, keyed (op, A, B, C[, D]), are searched analogously with
  nested loops, first argument outermost.
* **Nullary** methods (`f() := …`) live in a global table keyed by (f).

When no method is found, the result is an error such as "expected pair to have a method for
'+'" (binary) or "expected a method for 'op'" (unary).

#### 6.5.2 Calling

A found method *m* is applied like a function (§6.3), to the single argument *x* (unary), or
to the arguments (*x*, *y*) (binary), and so on.

#### 6.5.3 Installation: `:=` on operator forms

| source (after evaluating the operands) | installs |
|--------|----------|
| `op T := m` / `T op := m` (postfix) | key *op* in *T* (T MUST be a hash table) |
| `A op B := m` with A a type (a hash table whose parent is not `Nothing`) | key (op, A, B) |
| `f T := m` with f a function, or a hash table whose parent is `Nothing` | key *f* in *T* |
| `f (A, B) := m` / `f (A, B, C) := m` / `f (A, B, C, D) := m` | key (f, A, B[, C, D]) |
| `f () := m` | nullary key (f) |
| `A B := m` with A a type | key (SPACE, A, B) |

Here *m* MUST be a function, or `Type => function`. With the latter, the function is
installed and `Type` is recorded as the *typical value* in the global `typicalValues` table.
If *m* is a FunctionClosure without a rest parameter, its parameter count MUST equal the
number of types, plus 1 for **assignment methods**: keys of the form (op, `symbol =`), `<-`,
`GlobalAssignHook`, and the augmented operators *op*`=`. Otherwise the error is "expected
method for binary operator to be a function of 2 variables", and so on.

#### 6.5.4 Operators whose semantics are fixed by the core

These operators never dispatch, or they dispatch only under special keys:
`:=` `=` `<-` `->` `=>` `,` `;` `.` `.?` `#` `#?` `===` `=!=`, and `and` `or` `not` `??` for
Boolean or `null` operands. Their semantics are given in §6.6–6.10.

### 6.6 Assignment

The value of every assignment expression is the assigned value.

#### 6.6.1 Variables

`x = e` / `x := e`: evaluate `e`. If `x` is local, store it. If `x` is global:

1. If the symbol is **protected**, fail with "assignment to protected global variable 'x'".
   Built-in functions and constants such as `sin` and `true` are protected ✔.
2. Run the **global assignment hooks**, in this order:
   (a) the functions registered for this symbol in `globalAssignmentHooks`, called as (sym, new);
   (b) the method `GlobalReleaseHook` of the **old** value's class, called as (sym, old);
   (c) the method `GlobalAssignHook` of the **new** value's class, called as (sym, new).
   An error from any hook aborts the assignment. (The library uses (c) to give types and rings
   their names.)
3. Store the value.

#### 6.6.2 Parallel assignment

`(p₁,…,pₙ) = e` (or `:=`): evaluate `e` to *v*.

* If n = 1, the assignment behaves like `p₁ = v`, but a `Sequence` or list *v* of length 1 is
  unpacked first, and a sequence or list of any other length is an error.
* A `List` *v* (any class) is treated as its elements, and the result is rebuilt as a list of
  the same class. Otherwise *v* MUST be a `Sequence` of length exactly n, else
  "parallel assignment expected a sequence of length n".
* Each pᵢ is assigned vᵢ **in order**, as if by `pᵢ = vᵢ` (resp. `:=`). pᵢ may be a variable, an
  element form (`x#k`, `x.s`), an operator form (installing a value or method), a nested
  bracket (which recurses), a `new …` form (`:=` only), or **empty**, which skips the value.
  The first failure aborts.
* The result is the sequence (or list) of assigned values.

✔ `(a,b) = (b,a)` swaps. `(a,b) = (1,2,3)` is an error. Note that `(x) = (5,)` is an error:
`(5,)` has length 2 (§4.1).

#### 6.6.3 Element store: `x # k = e`, `x . s = e`

Evaluate `x`, then `k` (or take the symbol `s`), then `e`:

* **mutable List**: `k` MUST be a small integer. A negative `k` counts from the end. Storing
  past the end extends the list, padding with `null` ✔. An **immutable** list gives the error
  "assignment attempted to element of immutable list". A **Sequence** gives an error.
* **HashTable**: store the (key, value) pair. The table MUST be mutable, else "attempted to
  modify an immutable hash table".
* **Database**: string key and string value.
* **Dictionary**: `d#"name" = s` adds an alias `name` for the existing symbol `s`. The
  dictionary MUST be unprotected, and the name MUST be new.
* For `x.s = e`, `x` MUST be a hash table.

#### 6.6.4 Assignment to operator forms with `=`

`x op y = e` looks up the binary method ((op, `symbol =`), `class x`, `class y`) and applies
it to (x, y, e). `op x = e` looks up the unary method ((op, `symbol =`), `class x`) and applies
it to (x, e). `f x = e` uses op = SPACE. `x` and `y` are evaluated **before** `e`. With no method
the error is "expected pair to have an assignment method for 'op'".

### 6.7 Augmented assignment `L op= e`

1. If `L` is a parenthesized list `(l₁,…)`, evaluate `e` to a sequence of the same length and
   apply `lᵢ op= vᵢ` to each element.
2. `??=` is special: `L ??= e` means `L ?? (L = e)`. If `L` (evaluated under error suppression
   as in §6.9) is non-null, it is the result. Otherwise `L = e` is performed.
3. Otherwise evaluate `L` to *ℓ*. If `L` is `x#k` or `x.s` with `x` a hash table, `x` and the
   key are evaluated **once**, and `e` is evaluated **before** the lookup. A missing key is an
   error. For other forms, `L` is simply evaluated.
4. If `class ℓ` has a **method for the augmented operator key** *op*`=` (e.g. `symbol +=`),
   call it on (*ℓ*, value of `e`). If it returns anything other than the symbol `Default`,
   that is the result, **and no assignment happens**.
5. Otherwise compute *r* = *ℓ op v* by the ordinary operator semantics and assign *r* to `L`
   as in §6.6. `L` itself is not re-evaluated, but its operand subexpressions (e.g. `x`, `i` in
   `x_i`) are.

✔ `x = 1; x += 5` ⇒ 6. `x = {1}; x |= {2}` ⇒ `{1,2}`. `x = null; x ??= 7` ⇒ 7.

### 6.8 `new`

Let **makenew(T, P)** be the default construction:

* If `basictype T` is `HashTable`: make an empty hash table with class T and parent P. It is
  immutable if the first ancestor of T among {`HashTable`, `MutableHashTable`, `CacheTable`} is
  `HashTable`, mutable if `MutableHashTable`, and a cache table (hash 0) if `CacheTable`.
  (P = `Sequence` is an error.)
* If `basictype T` is `BasicList`: P MUST be `Nothing` ("expected Nothing as parent for list").
  The result is `()` if T is `Sequence`, else an empty list of class T, mutable iff T descends
  from `MutableList`.
* If `basictype T` is `Dictionary`: a new empty global dictionary.
* Otherwise it is an error.

Let **newClass(v, T[, P])** retag an existing value *v* as class *T*:

* hash table *v* (basictype of T is `HashTable` or `Number`): *v* itself if it already has
  class T (and parent P); otherwise a copy with class T (and parent P), mutable iff T
  descends from `MutableHashTable`;
* List/Sequence *v* (basictype of T is `BasicList` or `Number`): *v* if already of class T;
  the bare elements if T = `Sequence`; otherwise a list of class T with the same elements
  (copied), mutable iff T descends from `MutableList`. A parent other than `Nothing` is an
  error;
* any other *v*: *v* if `class v` = T; `SpecialExpr(T, v)` if T descends from `class v`; else
  the error "expected new class to be a specialization of the old one".

The four forms (T, P, I are evaluated left to right; T and P MUST be hash tables):

| form | if a method exists | otherwise |
|------|--------------------|-----------|
| `new T` | unary `NewMethod` on T: `newClass(m(T), T)` | `makenew(T, Nothing)` |
| `new T of P` | binary (NewOfMethod, T, P): `newClass(m(T,P), T, P)` | `makenew(T, P)` |
| `new T from x` | (NewFromMethod, T, class x): `newClass(m(T,x), T)`; else, if x is a sequence of length 2 or 3, the ternary/quaternary NewFromMethod on (T, class x₀, class x₁[, class x₂]) applied to (T, x₀, x₁[, x₂]) | if x is a list or hash table of class T: x (a copy if mutable); else `newClass(x, T)` |
| `new T of P from x` | ternary (NewOfFromMethod, T, P, class x): `newClass(m(T,P,x), T, P)` | similar, with parent P |

A new type is typically made with `new Type of X`. This is `makenew(Type, X)`: a mutable hash
table whose class is `Type` and whose parent is X.

### 6.9 Control constructs

**Semicolon block** `e₁; …; eₙ`: evaluate in order; the value is that of `eₙ`, which is `null`
if `eₙ` is empty.

**Sequence** `(e₁,…,eₙ)` (n ≠ 1): evaluate left to right into a `Sequence`.
**List / Array / AngleBarList**: the same, producing an immutable list of that class.

**if**: the predicate MUST evaluate to exactly `true` or `false`, else the error "expected true
or false" ✔ (`if 1 then 2` is an error). A missing else branch yields `null`.

**while P do B**: loop while P is `true`, evaluating B. The value is `null`. `break v` ends the
loop with value v, and `break` alone ends it with `null`. `continue` goes on to the next test.

**while P list L [do B]**: each time round, evaluate L and append its value to a result list,
then evaluate B. The value is the `List` of collected values. `continue` skips the append,
`continue v` appends v, `break` returns the list collected so far, and `break v` returns v.

**for**:

* `in X`: X MUST be a `List` (any class; its elements) or a `Sequence`. Otherwise X is
  **iterated**: `iterator X` is obtained via the `iterator` method of `class X` (a library
  hook). Values are then produced by the `next` method of the iterator's class, until it
  returns the symbol `StopIteration`. With no `iterator` method the error is "expected a list,
  sequence, or iterable object".
* `from a` / `to b`: a and b MUST be small integers. `from` defaults to 0, and with no `to`
  there is no upper bound. The variable takes a, a+1, …, b; the loop is empty if a > b.
  The `from`/`to`/`in` expressions are evaluated **once**, before the loop, `in` first or else
  `from` before `to`.
* Each iteration: assign the loop variable. If there is a `when W`, evaluate W: `false` **ends
  the loop** (it does not skip), and anything other than a Boolean is an error. Then, if there
  is a `list L`, evaluate L and collect its value (with `continue`/`break` treated as in
  `while … list`). Then evaluate `do B` if present.
* The value is the collected `List` if there is a `list` clause, else `null`. `break v` returns
  v.

✔ `for i to 3 list i` ⇒ `{0,1,2,3}`. `for i in {1,2,3,4,5} when i<4 list i` ⇒ `{1,2,3}`.

**try**: evaluate the primary with error messages suppressed. If it yields an **error** (not a
control completion, not an interrupt):

| form | on error | on success |
|------|----------|------------|
| `try P` | `null` | value of P |
| `try P else A` | A | value of P |
| `try P then S [else A]` | A (or `null`) | S (the value of P is discarded) |
| `try P [then S] except v do B` | B with `v` bound to the error object (§6.4) | S, or the value of P |

**catch P**: evaluate P. A **throw v** completion becomes the value v.

**trap P** (a keyword operator): returns `(value, null)` on success and `(null, errorObject)`
on error.

**x ?? y** (null coalescing): evaluate x as in `try`, where an error counts as `null`. If the
result is not `null` and its class has a unary `??` method, apply that method, whose result
replaces x. If the result is `null`, the value is y (evaluated only then); otherwise it is the
result. Unary `?? x` is just the first step. ✔ `null ?? 1` ⇒ 1, `3 ?? 1` ⇒ 3.

**return / break / continue / throw** create the abrupt completions of §6.2. Their operand is
evaluated first, and an error in it propagates instead.

**shield e**: evaluate e with interrupts deferred. **time e**, **timing e**, **elapsedTime
e**, **elapsedTiming e**: evaluate e and report or return CPU or elapsed time (`timing` returns
a `Time` list {seconds, value}). **profile**, **breakpoint** and **TEST** support profiling,
debugging and test registration.

### 6.10 Built-in operator semantics

Every row of this table falls back to method dispatch (§6.5) when its built-in cases don't
apply. "num" means any of ZZ, QQ, RR, CC, RRi, CCi. Unless stated otherwise, both operands are
evaluated, left first.

| operator | built-in behaviour |
|----------|--------------------|
| `x + y`, `x - y`, `x * y` | num × num with **type promotion** ZZ → QQ → RR → CC (intervals: RR → RRi, CC → CCi). A ZZ or QQ operand is converted at the **precision of the inexact operand**. Also defined on engine objects. |
| `+ x` | a number is returned unchanged; otherwise unary method `+` |
| `- x` | negation of numbers; otherwise unary method `-` |
| `* x` | unary method only |
| `x / y` | ZZ/ZZ and QQ-involving division give **QQ** (in lowest terms); a zero ZZ or QQ divisor is the error "division by zero"; inexact division follows MPFR/IEEE (e.g. division by 0.0 gives ±infinity) |
| `x // y` | ZZ//ZZ: q such that x = q·y + r with r = x % y; **x // 0 = 0** ✔. Otherwise a method (the library defines more cases). |
| `x % y` | ZZ%ZZ (installed as a method): r ∈ [0, \|y\|) with r ≡ x (mod y); **x % 0 = x** ✔. ✔ `(-5)%2` = 1, `5%(-3)` = 2, `(-5)//2` = −3, `(-5)//(-2)` = 3. |
| `x ^ y` | ZZ^ZZ: an exact power; a negative exponent gives QQ (0^neg is division by zero; exponent magnitude MUST fit a machine word); **0^0 = 1** ✔. QQ exponents with denominator 1 are exact; otherwise the result is inexact (a negative base with an odd denominator gives a real root, an even denominator gives CC). RR/CC use MPFR. |
| `x ! ` | factorial for ZZ (≥ 0), QQ and RR (installed methods); otherwise a method |
| `x == y` | num == num compares numerically across types ✔ (`3 == 3.0`, `1/2 == .5`). Symbol == Symbol is `===`. Boolean, String and Net compare by value. Sequence == Sequence is elementwise `==`. VisibleList == VisibleList requires the **same class** (else an error) and is elementwise. Otherwise a binary method, and a missing method is an **error**. |
| `x != y` | `not (x == y)` |
| `x === y`, `x =!= y` | §5.5 |
| `x ? y` | **comparison**: returns one of the keywords `<`, `>`, `==` or the symbol `incomparable`. Numbers compare numerically (NaN gives incomparable; intervals may give `<=`/`>=`). Strings use `strnumcmp`, a "natural" order in which embedded digit runs compare numerically (✔ `"a10" ? "a9"` is `>`). Symbols compare by name (same-named symbols compare `==`). Sequences compare lexicographically, a shorter prefix being `<`. Identical values give `==`. Otherwise the binary method `?`, whose result MUST be one of those four symbols. |
| `x < y`, `x > y`, `x <= y`, `x >= y` | defined through `?`: `<` is true iff `x ? y` is `<`; `<=` iff it is `<` or `==`; and so on. Unary forms dispatch to methods. *Quirk* ✔: `<=` and `>=` evaluate their **left operand twice** (`i = 0; (i = i+1) <= 5; i` ⇒ 2). |
| `x and y` | if x is `false` → `false` without evaluating y; if x is `true`, evaluate y, and a Boolean y is the result. Otherwise the binary method `and` on (x, y), with y evaluated. |
| `x or y` | if x is `true` → `true` without evaluating y; if x is `false`, as above. Otherwise the method `or`. |
| `x xor y` | method only (Booleans are handled by the library) |
| `not x` | Boolean negation; otherwise unary method `not` |
| `x .. y`, `x ..< y` | ZZ .. ZZ → the `Sequence` (x, x+1, …, y), empty if x > y ✔. `..<` excludes y. Otherwise a method. |
| `x => y` | an `Option`: a BasicList of class `Option` with elements {x, y} |
| `# x` | length: the element count of a Sequence or List, the entry count of a HashTable, the symbol count of a Dictionary, the **byte** count of a String, the row count of a Net. **No method fallback**: any other operand is an error. |
| `x # i` | subscript: for a Sequence, List, String (a 1-byte string) or Net (a row), a small integer, where −n ≤ i < n and negative indices count from the end (out of range is an error). For a HashTable, the value at key i ("key not found in hash table" if absent). A Dictionary takes a string and gives the symbol. A Database takes a string key. No method fallback. |
| `x #? i` | whether `x # i` would succeed; always `false` for `null` |
| `x . s` | x MUST be a hash table: equivalent to `x # (symbol s)`, where s is the **global** symbol s (§3.5) |
| `x .? s` | `x #? (symbol s)` for hash tables; `false` for anything else |
| `x <- y` | if x evaluates to a symbol: store y into the symbol's value (the symbol MUST not be protected unless it has hooks). Otherwise the method (`<-`, class x) applied to (x, y). |
| `x SPACE y` | application (§6.3) |
| all other operators | binary/unary/postfix method dispatch only: `\|` `\|\|` `&` `^^` `:` `++` `**` `\\` `\` `@` `@@` `@@?` `<<` `>>` `\|-` `==>` `===>` `<==` `<===` `<==>` `~` `_` `^>` `^>=` `^<` `^<=` `_>` `_>=` `_<` `_<=` `\|_` `^**` `·` `⊠` `⧢` (binary); `<<` `\|-` `<==` `<===` `~` `?` `<` `>` `<=` `>=` (unary); `!` `^!` `_!` `(*)` `^*` `_*` `^~` `_~` (postfix). The library (`m2/`) installs many methods on these, e.g. `String \| String` (concatenation), `List \| List`, `List + List`, `ZZ * List`. |

## 7. The top level

Source: `interp.dd`.

### 7.1 The read–eval loop

Every source unit (a file, stdin, a `value` string) is processed by the same loop. It runs in
a **static local dictionary** (§3.2) created for the unit, with its own frame.

```
loop:
    t := peek(obeylines = true)
    if t is EOF: finish (the result is the last value, for load/value)
    if t is NEWLINE or end-of-cell or ";": discard it; continue
    tree := parse(8, obeylines = true)
    if parse error: report; (non-interactive and stopping on errors: abort the unit); continue
    term := next(true)
    if term ∉ { ";", NEWLINE, end-of-cell, EOF }: error "syntax error: unmatched term"; continue
    if bind(tree) reports errors: skip this statement (in a file: abort the unit)
    code := convert(tree)
    call the BeforeEval hook
    v := evaluate(code)
    if v is an abrupt completion: handle it as in §7.2
    else if printing (interactive or `input`): run the printing hooks (§7.4), silenced if term = ";"
```

Consequences: `a; b` on one line is two statements, and `a;` suppresses printing. A statement
may span lines only as allowed by §2.5.7.

### 7.2 Abrupt completions at top level

* **error**: printed (with its position) unless already printed. In a file being loaded,
  loading stops and the error propagates to the caller of `load`/`needsPackage`. Interactively,
  or with "stop if error" off, the loop continues.
* **return v / break v / continue**: in `load` and `value`, ends the unit, with v as the unit's
  value. At the interactive top level it is reported as unhandled.
* The special symbol `end`: evaluating a statement whose value is `end` ends the unit
  immediately. (It is used to stop loading a file early.)

### 7.3 Error display and debugging (informative)

When an error first passes through code at a known position, it is printed immediately,
followed by one `--back trace--` line per enclosing call. If `debuggingMode` is on, a nested
interactive loop (the **debugger**) is entered in the dictionary of the failing frame. There,
`return v`, `break`, `continue`, `step n` and `finish` control resumption. Inside `try`, `trap`
and `??`, errors are suppressed, not printed.

### 7.4 Printing protocol (library hooks)

After a successful top-level evaluation with printing enabled, the core calls these methods on
the value *x*, looking each up in `class x`. Each hook key is a 2-element `List` {*mode*,
*hook*}, where *mode* is the current `topLevelMode`, normally the symbol `Standard`:

1. `{mode, AfterEval}` – its result replaces x (or the unmodified x if there is none);
2. `{mode, BeforePrint}` – its result, *p*, is what gets printed;
3. `{mode, Print}` applied to *p*, or `{mode, NoPrint}` if the statement ended with `;`;
4. `{mode, AfterPrint}`, or `{mode, AfterNoPrint}` after `;`, applied to x.

The standard library defines these, producing the familiar `o5 = …` / `o5 : Type` output and
the `oN` history variables. The prompt is also a library method: `{mode, InputPrompt}` or
`{mode, InputContinuationPrompt}`, installed in `ZZ` and applied to the line number.

### 7.5 `value` and `load`

* `value s` for a string: evaluate *s* (with a newline appended) as a source unit **in a new
  static dictionary** that does **not** see the caller's local variables. The result is the
  last statement's value, or the value of a `return`. `value sym` returns the symbol's stored
  value. `value` of pseudocode evaluates it.
* Loading a file creates a new static dictionary for the file, so `:=` variables at the top
  level of a file are **private to that file**, while `=` assigns globals. During loading the
  variables `currentFileName` and `currentFileDirectory` are set. On exit, the functions in the
  `fileExitHooks` list are called with `true`/`false` according to whether an error occurred.

### 7.6 Start-up

The executable evaluates an embedded start-up file (`startup.m2`), which loads the `Core`
package (`m2/*.m2`) and then processes the command line. The globally visible environment a
user sees is therefore the kernel's built-ins of §5–6 **plus** everything the `Core` package
exports.

---

## Appendix A. Keywords and reserved words

Identifier-shaped words with special parse behaviour. They cannot be used as variable names
(§1.7, §2.3):

```
and  or  xor  not
if  then  else
while  for  in  from  to  when  list  do
try  except  catch  throw
return  break  continue  step  finish
new  of
symbol  global  threadLocal  local
time  timing  elapsedTime  elapsedTiming  profile  shield  trap  breakpoint  TEST
SPACE
```

The following are ordinary but **protected** global symbols, so they are not reserved by the
grammar: `true`, `false`, `null`, `incomparable`, `StopIteration`, `end`, `NewMethod`,
`NewOfMethod`, `NewFromMethod`, `NewOfFromMethod`, `InverseMethod`, `GlobalAssignHook`,
`GlobalReleaseHook`, `BeforeEval`, `AfterEval`, `BeforePrint`, `Print`, `NoPrint`,
`AfterPrint`, `AfterNoPrint`, `InputPrompt`, `InputContinuationPrompt`, and every built-in
function name.

## Appendix B. Version differences observed (1.25.11 binary vs. 1.26.06 source)

| feature | 1.25.11 | 1.26.06 (this spec) |
|---------|---------|---------------------|
| `~` | postfix operator (`a~` = `(~ a)`) | prefix/infix `unarybinaryright` at lbp 36 |
| `try … except v do …` | absent | present (§2.5.5, §6.9) |
| `parse` built-in (returns parse trees) | absent | present |
| parallel assignment from a `List`, e.g. `(a,b) = {1,2}` | error | accepted (§6.6.2) |

Other probes behind this document matched the 1.26.06 source.
(✔ confirmed in 1.25.11: `class(6/3)` is `QQ`, newline-`else` is a top-level syntax error, and
RR `===` compares precision.)

## Appendix C. Map to the reference implementation

| topic | file(s) |
|-------|---------|
| character classes | `d/ctype.d` |
| lexer | `d/lex.d` |
| literal conversion, Pratt parser | `d/parser.d` |
| parse-tree and code types, value union | `d/parse.d` |
| operator table, binding | `d/binding.d` |
| parse tree → code | `d/convertr.d` |
| evaluator, application, assignment, control flow | `d/evaluate.d` |
| built-in classes, error helpers | `d/expr.d`, `d/classes.dd` |
| hash tables, method lookup and installation, `#` | `d/hashtables.dd` |
| strict equality | `d/equality.dd` |
| arithmetic, `and`/`or`/`not`, `..`, installs | `d/actors.d` |
| `new`, `newClass` | `d/actors2.dd` |
| `==`, `?`, `<`, sorting | `d/actors3.d` |
| misc. operators, `.`, `=>` | `d/actors5.d` |
| top-level loop, `value`, `load` | `d/interp.dd` |
| library layer | `m2/*.m2` (start at `m2/Core.m2`, `m2/loadsequence`) |

## Appendix D. Implementation checklist

An interpreter conforming to this document:

1. lexes per §1, including the math-operator rule, `///` strings and the number quirks;
2. implements the Pratt parser of §2.4 with the table of §2.3, including the obeylines/newline
   behaviour of §2.5.7;
3. binds names per §3: implicit global creation, `:=` locals, the four scope-creating forms;
4. applies the translation identities of §4 (unseq, empty operands as `null`);
5. provides the value representations and class hierarchy of §5;
6. evaluates per §6, with abrupt completions, frames shared by reference, method dispatch and
   installation, and the built-in operator cases;
7. runs the top-level protocol of §7;
8. then loads the Macaulay2 `Core` library on top, which supplies the rest of the language
   users know.
