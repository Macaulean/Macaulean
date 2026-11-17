# Macaulay2 core-language contract for Macaulean

**Version:** 1.1 — audit-integrated revision · **Date:** 29 September 2026  
**Status:** Working specification. Confirmed audit corrections are integrated; outstanding contracts are explicitly listed in §8. No complete native-conformance or verification claim is made.  
**Target:** M2 1.26.06, pinned to `Macaulay2/M2@1a37f6fe95badb1e5f99707a485503d213fd9d49`  
**Comparison baseline:** `Macaulean/Macaulean@994f0cb978108f7177508218c60f5b3a3baae2e3`

## 0. Scope, status and conventions

### 0.1 What this document specifies

This is the **single active language contract** in this revision. It retains the supplied reference's organization—lexing, grammar, binding, lowering, values, evaluation, and source units—while integrating the v1.0 front-end decisions and the audit's confirmed corrections. The original reference and v1.0 specification are archived unchanged. They are evidence/provenance, not additional normative layers that an implementer must mentally merge.

The companion `Macaulean-M2-architecture-v1.1.md` explains implementation and refinement choices. It does not override language rules. The grammar table here is generated from `m2-grammar-1.26.06.json` and checked for exact agreement. `CHANGELOG-v1.1.md` tracks every audit finding F01–F24 and distinguishes text corrections from remaining contract work.

The target includes the interpreter's lexical/syntactic language, source-ordered name resolution, runtime values, actor-controlled operator evaluation, native primitive interfaces, mutable reflection, and the source-unit protocol. A complete bootstrap boundary must distinguish:

| Boundary | What belongs here |
|---|---|
| **Native interpreter primitives** | D-registered operations, including native `apply`, `scan`, `override`, `frame`, `frames`, `localDictionaries`, method/dictionary operations, `symbolBody`, and `value'`; their contracts cannot be omitted merely because a library wraps or overloads them |
| **M2-language library** | Core/package source, wrappers, additional methods, presentation conventions, and algebraic constructions implemented in `.m2` files |
| **External primitives** | Operating-system, foreign-library, and algebra-engine implementations, with explicit calling/result/effect contracts at the interpreter boundary |

The library and external engine implementations are not reproduced here. Their **required interfaces remain obligations**. The audit established that the earlier primitive boundary was incomplete; §5.8 and the companion contract register record the identified interfaces without pretending they form an exhaustive bootstrap inventory. [Audit F01, F17](archive/audit.md)

The following levels remain goals, not achieved certifications:

| Level | Required evidence |
|---|---|
| **F — front end** | Byte lexing, complete grammar data/actions, binding including failure effects, and lowering |
| **K — core interpretation** | F plus fully contracted actors, native primitive/bootstrap interfaces, reflective state, and source-unit behavior |
| **L — library compatibility** | K plus the pinned Core startup and declared library/host/engine dependencies |

A missing contract or unsupported implementation capability is not an ordinary M2 error and cannot count as successful negative-test coverage. An input requiring an open contract has status **unresolved specification coverage**, not permission to choose convenient behavior. K cannot be frozen until the open core contracts in §8 are closed.

### 0.2 Sources and evidence

This revision uses the supplied reference, delivered v1.0 specification, the attached 24-finding audit, and the pinned-source excerpts documented by that audit. It is an integration of those findings, not a new independent native-source audit. No native M2 probes, Lean compilation, performance benchmark, or proof execution is claimed.

A historical **✔** is retained only where it appeared in the supplied reference: it records that reference's claimed probe against **1.25.11**, not a newly run test or evidence that a newer behavior was exercised. Appendix B preserves the reference's version distinctions. Newly added regression expectations are labeled source-derived and unexecuted.

Source names such as `evaluate.d:evalWhileListDoCode` identify the pinned implementation cited by the audit. Native links are given in Appendix C and `archive/audit.md`. Hashes of all archived inputs and generated files are included in `SHA256SUMS`.

### 0.3 Normative conventions and compatibility profiles

`MUST` and `MUST NOT` define requirements of the selected compatibility profile. A paragraph marked **Open contract** is a known specification gap, not a normative default. Pseudocode is mathematical notation, not compile-tested Lean code.

**PN — pinned-native profile** reproduces the audited, defined behavior of the pinned implementation, including awkward clause-specific control and hook rules. It does not require undefined behavior, memory corruption, or a crash. An unresolved native path is explicitly outside the certified domain until its contract is fixed.

**PS — portable/safe profile** shares PN rules except for the individually listed departures below. No general “clean up surprises” permission is granted:

| Deviation | PN/domain status | PS behavior |
|---|---|---|
| DEV-REAL-RADIX: malformed radix/real token, e.g. `0b1E5` | Tokenization is defined; the accidental decoded outcome is not established by these sources and is not claimed conforming | Recognize the same token, then reject it at literal decoding |
| DEV-DELIMITER-ALIAS: inherited Paren profile without a fixed delimiter spelling | No defined successful delimiter construction is claimed | Positioned syntax failure `InvalidDelimiterAlias` |
| DEV-FIELD-ALIAS: alias-created dot conversion with inconsistent lexical/global binding | No arbitrary reinterpretation or undefined location access is admitted | Reject at lowering validation with `InvalidFieldAlias` |

Profile selection must accompany every conformance run. `native` versus `transactional` worksheet execution is a separate axis: transaction rollback is a host-adapter feature and is not PN failure semantics. The default core semantics preserves state and effects already reached before a failure. [Audit F19](archive/audit.md)

`null` is the unique value of class `Nothing`. Bytes, source words, declaration identities, activations, and values are distinct concepts. Identity stability does not imply that `isMutable` returns false (§5.3).

---

## 1. Lexical structure

Source: `lex.d`, `ctype.d`, `parser.d` (literal conversion), `binding.d` (operator words).

<a id="rule-lex-bytes"></a>

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

<a id="rule-word-first"></a>

### 1.4 Tokens and first-registration-wins word history

A token carries its raw spelling/source slice, lexical category, byte position, and `followsNewline` flag. The flag records newline tokens skipped by the cursor, not an approximation based on whether arbitrary preceding comments contain line feeds. Identifier/operator tokens have lexical type `id`; integer, real, and string literals are separate occurrence categories.

Identifier/operator words are registered by exact byte spelling. **First registration wins:**

```text
internWord(key, requestedProfile):
    if key is already registered:
        return its existing immutable profile; do not overwrite it
    otherwise:
        record (key, requestedProfile); return that record
```

Register the built-in vocabulary before user input. Ordinary names and generic mathematical-operator words request GenericProfile; previously registered keywords retain their special profile. Record ordinary names too: a word already seen as generic must not acquire new parse behavior through a later dictionary alias. Numeric/string literal occurrences need not be interned.

A quoted symbol's canonical word, a dictionary entry's lookup spelling, and an occurrence's frozen lexical profile remain separate. Aliasing a dictionary name can request a copied profile, but cannot overwrite prior registration or add punctuation-trie paths (§3.8). A cached lookahead token retains the profile it had when read.

Source spelling and M2 strings are **bytes**, not Unicode-normalized strings. A valid-UTF-8 Lean String interface is only an adapter. Literal tokens retain source spelling; real constants are decoded during lowering at the then-current default precision (§4.2). Artificial EOF/EOC/NEWLINE tokens cannot be created by typing their diagnostic names.

This integrates the v1.0 R1/R2/R10 decisions; the archived supplied reference's blanket statement that all word occurrences are interned is not retained.

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
     token. Its accidental conversion result is outside the established PN domain; PS rejects it during decoding (DEV-REAL-RADIX, §0.3).
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
  the **default precision current at lowering** (53 unless changed). The rest of the literal,
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

The Macaulay2 grammar is defined by the stateful **Pratt parser** below. Prefix operators use
`max(context, own strength)`, juxtaposition is triggered by the following token, some operands
may be empty, and newline sensitivity is contextual. No impossibility claim about context-free
representations is needed. The EBNF in §2.9 is informative, not a substitute for the algorithm.

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



The finite action vocabulary is:

```text
Leading = error | default | unary | nunary | nnunary | paren
        | if | while | for | try | catch | new | quote(policy)
Trailing = error | default | binary | nbinary | postfix | arrow
QuotePolicy = ordinary | currentLocal | global | threadGlobal
Profile = (lbp, rbp, ubp, Leading, Trailing)
```

`None` in a strength field is native `nopr = -1`, not another ordinary binding power.
Parser reflection reports the native numerical strengths. `paren` uses the encountered
opening spelling and the fixed matching map; copying its profile does not register a new
delimiter pair. The four quotation policies belong respectively to `symbol`, `local`,
`global`, and `threadLocal` and must not be interchanged.

<a id="rule-grammar-table"></a>

### 2.3 The precedence table (normative)

This generated projection and `m2-grammar-1.26.06.json` must agree exactly. The manifest
contains 155 registered words (34 augmented), 57 named profiles, and three internal token
profiles. Unbounded ordinary spellings additionally use GenericProfile. Profile labels are
implementation/data labels, not M2 symbol identities.

<!-- BEGIN GENERATED GRAMMAR TABLE -->
| Words | lbp | rbp | ubp | Leading | Trailing | Quotation policy | Lexical route |
|---|---:|---:|---:|---|---|---|---|
| `)`, `]`, `\|>`, `}` | 6 | — | — | error | error | — | punctuation_trie |
| `;` | 8 | 7 | — | error | nbinary | — | punctuation_trie |
| `,` | 10 | 10 | 10 | nnunary | nbinary | — | punctuation_trie |
| `do`, `else`, `except`, `list`, `then` | 12 | — | 12 | error | error | — | identifier |
| `%=`, `&=`, `**=`, `*=`, `++=`, `+=`, `-=`, `..<=`, `..=`, `//=`, `/=`, `<<=`, `<==>=`, `===>=`, `==>=`, `>>=`, `??=`, `@=`, `@@=`, `@@?=`, `\=`, `\\=`, `^**=`, `^=`, `^^=`, `_=`, `\|-=`, `\|=`, `\|_=`, `\|\|=`, `~=` | 14 | 13 | — | error | binary | — | punctuation_trie |
| `->` | 14 | 13 | — | error | arrow | — | punctuation_trie |
| `:=`, `<-`, `=`, `=>`, `>>` | 14 | 13 | — | error | binary | — | punctuation_trie |
| `·=`, `⊠=`, `⧢=` | 14 | 13 | — | error | binary | — | math_operator |
| `from`, `in`, `of`, `to`, `when` | 16 | — | 16 | error | error | — | identifier |
| `<<` | 18 | 18 | 18 | unary | binary | — | punctuation_trie |
| `\|-` | 20 | 19 | 20 | unary | binary | — | punctuation_trie |
| `<===` | 22 | 21 | 22 | unary | binary | — | punctuation_trie |
| `===>` | 22 | 21 | — | error | binary | — | punctuation_trie |
| `<==>` | 24 | 23 | — | error | binary | — | punctuation_trie |
| `<==` | 26 | 25 | 26 | unary | binary | — | punctuation_trie |
| `==>` | 26 | 25 | — | error | binary | — | punctuation_trie |
| `??` | 28 | 27 | 28 | unary | binary | — | punctuation_trie |
| `or` | 28 | 27 | — | error | binary | — | identifier |
| `xor` | 30 | 29 | — | error | binary | — | identifier |
| `and` | 32 | 31 | — | error | binary | — | identifier |
| `not` | 34 | — | 34 | unary | default | — | identifier |
| `!=`, `=!=`, `==`, `===` | 36 | 35 | — | error | binary | — | punctuation_trie |
| `<`, `<=`, `>`, `>=`, `?`, `~` | 36 | 35 | 36 | unary | binary | — | punctuation_trie |
| `\|\|` | 38 | 38 | — | error | binary | — | punctuation_trie |
| `:` | 40 | 39 | — | error | binary | — | punctuation_trie |
| `\|` | 42 | 42 | — | error | binary | — | punctuation_trie |
| `^^` | 44 | 44 | — | error | binary | — | punctuation_trie |
| `&` | 46 | 46 | — | error | binary | — | punctuation_trie |
| `..`, `..<` | 48 | 48 | — | error | binary | — | punctuation_trie |
| `+`, `-` | 50 | 50 | 50 | unary | binary | — | punctuation_trie |
| `++` | 50 | 50 | — | error | binary | — | punctuation_trie |
| `·` | 52 | 52 | — | error | binary | — | math_operator |
| `**` | 54 | 54 | — | error | binary | — | punctuation_trie |
| `⊠`, `⧢` | 54 | 54 | — | error | binary | — | math_operator |
| `<\|`, `[` | 56 | — | 6 | paren | default | — | punctuation_trie |
| `%`, `/`, `//` | 58 | 58 | — | error | binary | — | punctuation_trie |
| `*` | 58 | 58 | 58 | unary | binary | — | punctuation_trie |
| `\`, `\\` | 58 | 57 | — | error | binary | — | punctuation_trie |
| `@` | 60 | 59 | — | error | binary | — | punctuation_trie |
| `(`, `{` | 62 | — | 6 | paren | default | — | punctuation_trie |
| `SPACE` | 62 | 61 | — | error | binary | — | identifier |
| `TEST`, `breakpoint`, `elapsedTime`, `elapsedTiming`, `profile`, `shield`, `time`, `timing`, `trap` | 62 | — | 12 | unary | default | — | identifier |
| `break`, `continue`, `finish`, `return`, `step`, `throw` | 62 | — | 12 | nunary | default | — | identifier |
| `catch` | 62 | — | 12 | catch | default | — | identifier |
| `for` | 62 | — | 16 | for | default | — | identifier |
| `global` | 62 | — | 74 | quote | default | global | identifier |
| `if` | 62 | — | 12 | if | default | — | identifier |
| `local` | 62 | — | 74 | quote | default | currentLocal | identifier |
| `new` | 62 | — | 16 | new | default | — | identifier |
| `symbol` | 62 | — | 74 | quote | default | ordinary | identifier |
| `threadLocal` | 62 | — | 74 | quote | default | threadGlobal | identifier |
| `try` | 62 | — | 12 | try | default | — | identifier |
| `while` | 62 | — | 12 | while | default | — | identifier |
| `(*)` | 64 | — | — | error | postfix | — | punctuation_trie |
| `@@`, `@@?` | 66 | 66 | — | error | binary | — | punctuation_trie |
| `^*`, `^~`, `_*`, `_~` | 68 | — | — | error | postfix | — | punctuation_trie |
| `#` | 70 | 70 | 61 | unary | binary | — | punctuation_trie |
| `#?`, `.`, `.?`, `^`, `^**`, `^<`, `^<=`, `^>`, `^>=`, `_`, `_<`, `_<=`, `_>`, `_>=`, `\|_` | 70 | 70 | — | error | binary | — | punctuation_trie |
| `!`, `^!`, `_!` | 72 | — | — | error | postfix | — | punctuation_trie |
| Ordinary identifier words and literals | 62 | — | — | default | default | — | generic / literal |
| Internal EOF | 2 | 2 | — | error | nbinary | — | internal |
| Internal EOC | 4 | 4 | — | error | nbinary | — | internal |
| Internal NEWLINE | 8 | 8 | — | error | nbinary | — | internal |
<!-- END GENERATED GRAMMAR TABLE -->

`—` means absent (`nopr`); all continuation tests are strict `lbp > context`.
Each augmented word has its exact registered base mapping; arbitrary `word=` is not a lexical rule.

Read the table as follows:

* **binaryleft** (rbp = lbp) is left-associative; **binaryright** (rbp = lbp − 1) is
  right-associative. So `a^b^c` = `(a^b)^c` ✔, `a_b_c` = `(a_b)_c` ✔, `a:b:c` = `a:(b:c)` ✔,
  `a\b\c` = `a\(b\c)` ✔, `a@b@c` = `a@(b@c)` ✔, `a=>b=>c` = `a=>(b=>c)`, `a>>b>>c` = `a>>(b>>c)` ✔,
  `a<b<c` = `a<(b<c)`.
* A word with an "error" prefix handler cannot begin an expression. One with an "error" infix
  handler cannot follow one.
* Only words with an error leading action are rejected in operand position. Leading
  keywords such as `if`, `not`, and `symbol` do begin expressions. Quotation consumes the
  next `id` token directly, including operator/keyword words; it does not call that token
  as a leading parser.
* `symbol`, `global`, `threadLocal` and `local` have lbp 62, like every other word that begins an
  operand. (The source sets their "unary strength" to 74, but their handler never uses it.)

<a id="rule-pratt-core"></a>

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

The word `SPACE` supplies the adjacency method key. Bare prefix `SPACE` is a syntax error,
but **`a SPACE b` is a valid binary expression**, whose actor evaluates adjacency.
`symbol SPACE` is valid. This retains the pinned-source correction from v1.0 R3.

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

<a id="rule-parameters"></a>

#### 2.5.6 Function literals

The parser produces `Arrow(lhs, parse(13,ob))` without validating the parameter tree.
The body therefore swallows assignment and nested arrows but stops at commas/semicolons.
`f = x -> x, 1` is `(f = (x -> x)), 1`. Parameter validity is a **binding** rule:

* A bare `id` atom is one rest parameter receiving the whole argument.
* Any `EmptyParentheses` node gives zero fixed parameters.
* Any `Parentheses` node accepts the same fixed-parameter token/comma-spine grammar:
  an `id` atom, or a canonical-comma Binary with a recursively valid left spine and an
  `id` right child. Duplicates, omitted operands, literals, nested delimiter nodes, and
  other operators are rejected.

The pinned binder does not inspect the delimiter kind here: round, square, brace, and
angle-bar forms are accepted for this parameter-tree role. This is not a promise that
a list/array **value** is an argument tuple. `(x) -> body` is a fixed-one-argument function;
`x -> body` is a rest-parameter function. The distinction survives lowering.

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

<a id="rule-unit-syntax"></a>

### 2.6 Statements

A source unit is a sequence of **statements**, parsed by the loop of §7:

```
unit      ::= { NEWLINE | end-of-cell | statement terminator } EOF
statement ::= E₈   (parse(8, obeylines = true))
terminator::= ";" | NEWLINE | end-of-cell | EOF
```

After a statement is parsed, the next token MUST be a terminator. Anything else, necessarily a
right bracket, gives "syntax error: unmatched )". A statement terminated by `;` is evaluated
with the NoPrint protocol (§7). A semicolon **at the start of a statement is not skipped**:
`;1` and the second semicolon in `1;;2` are syntax failures in the source-unit driver.
The `parse` utility is a different observation surface and must be tested separately.
[Audit F03](archive/audit.md)

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
**protected** flag, a **thread-local** flag, and `flagLookup`, which produces a binding
error when the flagged occurrence is looked up. Stable declaration/activation identity is
separate from assignment permission and the user-visible `isMutable` predicate (§5.3).

The value `SymbolClosure(frame, symbol)` is how a symbol appears at run time (class `Symbol`,
or `Keyword` for operator words and keywords, §5.4).

### 3.2 Dictionaries

A **dictionary** stores name-to-symbol entries, not just a deduplicated finite map. It has a
frame id, an entry count, a protected flag, and an outer dictionary. Repeated `:=` can add
another entry with the same name. Lookup selects the first matching entry under the native
entry order; counting/enumeration must retain the shadowed entries (§3.8). The outer link
may be self for the outermost scope.

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
| parameters `x ->`, delimited fixed parameters | Each parameter creates a new declaration in the function scope. The exact fixed/rest and all-four-delimiter validity rules are §2.5.6; duplicates are rejected. `(x) ->` is fixed-one; `x ->` is rest. |
| `for v …`, `except v` | `v` MUST be a single identifier. It gets slot 0 of the new scope. |

### 3.6 Well-formedness of assignment left-hand sides

The following table specifies accepted shapes. **It is not the error/effect schedule.**
For unary/postfix/binary targets, method-capability checks occur after binding the RHS;
invalid literal/other target branches can stop earlier. §3.7 fixes those traversal edges.
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

<a id="rule-bind-failure"></a>

### 3.7 Deterministic binding effects and error traversal

**BIND-FAILURE.** Binding has a reached state, ordered diagnostics, and an aggregate
`HadError` flag. Recording an error is not itself a short-circuit return. Conversely, an
explicit early-return branch does not bind children the native branch never visits.
The completed statement is not lowered or evaluated when `HadError` is set. Global word,
symbol, or layout effects already performed are retained. [Audit F07](archive/audit.md)

The successful and error-recording traversal share the following child order:

| Form | Ordered visits |
|---|---|
| Atom(id) | Ordinary lookup, creating a global on absence |
| Parentheses | Contents, same scope; empty does nothing |
| Adjacent | LHS, RHS |
| Generic Binary | LHS, operator lookup without creation, RHS |
| Unary / Postfix | Operator then operand / operand then operator |
| Quote | Ordinary-bind quoting word, then operand under the selected policy |
| If | Predicate, then branch, optional else; bind both branches regardless of execution |
| While | Predicate, collector when present, do-body when present |
| Arrow | Allocate child scope; parameters; body; finalize layout |
| For | `in` or `from` then `to` outside; child scope and variable; `when`, collector, do-body inside |
| Try | Primary, optional sequel; else in same scope or except variable/handler in child scope |
| Catch / New | Primary / class, parent, initializer |
| Dummy | Nothing |

Canonical `=`, `:=`, `.`, and `.?` have their source-word-sensitive special binding rules.
A word alias with the same profile is not automatically granted those source-word privileges.
Dot conversion also uses resolved-symbol identity; both identities survive until their
respective checks (§4.4). An absent operator is an error, not implicit global creation.

For canonical assignment, first look up the assignment operator. Then use this exact schedule:

| Target | Schedule and local stopping point |
|---|---|
| Id atom | Ordinary-bind (`=`) or fresh-declare (`:=`), then bind RHS |
| Non-id literal atom | Record invalid-symbol-target error and return from this assignment branch **without binding RHS** |
| Nonempty delimiter | Bind parallel list as below, then RHS |
| Empty delimiter | Bind RHS |
| Adjacent | Bind its left, its right, then RHS |
| Unary | Bind operator, operand, RHS; **then** record unsupported-unary-capability error if needed |
| Postfix | Bind operand, operator, RHS; **then** capability check |
| Binary | Bind left, operator, right (globally for canonical dot), RHS; **then** capability and dot-shape checks |
| New with `:=` | Bind class, parent, initializer, RHS |
| New with `=` or other inappropriate target | Record inappropriate-target error; do not visit that branch's RHS |

An error recorded in an earlier ordinary child does not by itself cancel later listed visits.
After all listed visits the branch returns. Parameter errors likewise accumulate along the
native prescribed traversal; no duplicate-name error can be used to silently erase already
allocated declarations. Unestablished low-level failure cases remain OC-BIND, not optional
continuation behavior.

Parallel declaration follows the **canonical comma spine**, not a recursive “declare every
identifier below any bracket” traversal:

```text
parallelItem(e, declare):
    Id atom       -> fresh local when declare; ordinary lookup otherwise
    literal atom  -> record error
    other tree    -> ordinary bind of that tree
parallelList(e, declare):
    Unary(comma,r)    -> bind operator; parallelItem(r,declare)
    Binary(l,comma,r) -> parallelList(l,declare); bind operator; parallelItem(r,declare)
    other            -> parallelItem(e,declare)
```

Example required by BIND-FAILURE: binding `#AuditTarget := AuditRhsAfterInvalidMethod`
creates the RHS global before reporting that this unary method target is unsupported.
This source-derived expectation is not an executed native result.

<a id="rule-dict-history"></a>

### 3.8 Dictionary entries, aliases and visibility history

**DICT-HISTORY.** Separate three observations: name lookup, retained entry storage, and
frame layout. A fresh local declaration allocates a new SymbolId/slot and prepends a new
entry even when that name exists. It does not delete the earlier entry or rewrite old code.
`#dictionary` counts retained entries; dictionary enumeration must not silently deduplicate
same-name entries. `values` returns symbol/keyword references, not cell contents; `pairs`
associates each entry's lookup spelling with its symbol reference. A fast name index is a
view of the entry store, not a replacement for its cardinality/history. Exact enumeration
order follows the implementation's declared native/portable observation policy, not an
invented universal sorted order. [Audit F15](archive/audit.md)

The global path is ordered, contains global dictionaries without duplicates, and has a
writable dictionary. Implicit creation chooses its first unprotected member. Visibility
changes affect later resolution only; previously resolved references retain their targets.
A declaration's original scope is provenance, not an exclusive package-ownership claim.

For `d#"name" = s`: evaluate dictionary, key, RHS; validate shapes and compatible frame;
require an unprotected dictionary; call first-wins word registration with the canonical
word's profile; check key absence; insert an alias entry for the **same symbol**. No
canonical renaming, arbitrary parse callback, or punctuation-trie extension occurs.
A duplicate-key failure can occur after word registration. Earlier word history therefore
matters even after unsuccessful alias insertion. The profile used on an occurrence and
the canonical profile used by symbol reflection need not be the same.

Removing visibility does not invalidate a symbol value or direct reference. **Open
contract OC-DICT:** exact erase behavior across canonical-name buckets, aliases, retained
entries and all rehash/enumeration effects must be fixed before reflective dictionary
conformance is claimed; replacing this with “delete all aliases” is not authorized.

<a id="rule-address-identity"></a>

### 3.9 Logical state and address identity

The semantic state contains exact word history, dictionary entries/path, declarations,
logical activation/storage graphs, values/objects, source-unit state, hooks, and reached
effects. A declaration has stable canonical spelling, slot/provenance, protection and
thread metadata. A reified symbol denotes a declaration **and a particular activation**.

An ordinary reference can lower to a direct global location, a lexical `(depth,slot)`, or
a thread-global slot resolved in the executing thread. Reification recovers the selected
declaration and live address without reading the stored value. Thread reification captures
the current thread's cell; ordinary thread-global reads remain thread-relative.

`(FrameId,slot)` is an adequate logical cell address. A machine may use flattened CellIds,
inline slots, or metadata side tables; it need not allocate both a frame object and an
additional object for every cell. Logical identities cannot be reassigned while still
observable. Physical allocation and reclamation are architecture choices constrained by
symbols, closures, dictionary values, snapshots, and reflective backing views (§5.7).
[Audit F23](archive/audit.md)

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
| integer / real / string literal | Decode exact/raw spelling to a constant. Real precision is selected at lowering, not invocation; an invalid precision becomes a positioned error constant. PS malformed-radix rejection is §0.3. |
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

At code construction, a **sequence-code of length exactly 1 is replaced by its element** (`unseq`); this does not erase singleton Sequence values manufactured at runtime.
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

<a id="rule-lower-identity"></a>

### 4.4 Resolved code and operator identities

The logical code vocabulary is: constants/error constants, direct reads, symbol reification,
sequence/list/array/angle-bar construction, semicolon blocks, function templates, application,
unary/postfix and binary actor calls, assignment plans, augmented assignment, If, While,
For, Try, Catch, and the four New combinations. This covers every tree family without
requiring one native D constructor per optimized instruction.

A function template carries a declaration/layout identity, fixed/rest convention, parameter
count, layout, body, code identity and source mapping. Bare `break`/`continue` preserve an
**omitted operand**, distinct from an explicit expression evaluating to null. In separators
and containers the same Dummy tree instead lowers to an ordinary null constant.

Assignment plans distinguish variable, recursive parallel, index, globally quoted field,
unary/postfix/binary method target, application target, and constructor target. Mixed nested
targets retain bound code and shape until the native runtime target check; they are not
restricted to names. Tables §4.3 and §6.6 determine each plan's behavior.

Keep **encountered word identity and resolved SymbolId** through lowering. Canonical source
commas/semicolons flatten; aliases do not become those separators merely by copying profiles.
Canonical source `=`/`:=` determines declaration/assignment lowering, while native dot
conversion additionally tests the selected dot symbol. Inconsistent alias-created global-key
references must not be reinterpreted as convenient valid fields (§0.3).

Actors receive operand **code**, not necessarily evaluated values. They retain native
short-circuiting, suppression, repeated evaluation and primitive-before-method paths.
`BinOp.add` may remain an optimized instruction for a proved case; it is not the identity
of source `+`. Names disappear from ordinary hot reads only after validated resolution.

The physical reference may omit redundant SymbolIds when direct addressing plus metadata
preserves reification, diagnostics and reflection. The architecture document gives the
refinement boundary rather than imposing per-slot objects. [Audit F23](archive/audit.md)

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

<a id="rule-mutability"></a>

### 5.3 Mutability, stable identity and hashing

**MUTABILITY.** Do not conflate a stable identity/hash with `isMutable` or with the ability
to update a symbol's binding. The native predicate is:

| Representation | `isMutable` |
|---|---|
| HashTable | Its stored Mutable flag |
| List-family representation | Its stored Mutable flag |
| SymbolClosure (Symbol or Keyword) | `not symbol.Protected` |
| DictionaryClosure | `not dictionary.Protected` |
| Database | Its stored Mutable flag |
| Every other representation in this predicate | false |

An unprotected symbol can report mutable while remaining the same declaration/activation
identity and hash-table key after assignment. `protect` changes the predicate, not the
symbol identity. [Audit F09](archive/audit.md)

Sequences, strings and scalar values have no element-store mutation. A List's construction
selects mutability using its class hierarchy; runtime stores consult the stored flag.
Hash-table mutability is determined on construction/retagging as §6.8 prescribes. Types
are mutable hash tables. Do not recompute mutability from a later class-table change in
place of consulting the object flag.

Immutable composite hashing is structural subject to class/parent rules; strict-equal
values must have matching hashes. Mutable objects have stable identity hashes, but a hash
is not a portable proof of object identity. CacheTable hashing has a special zero case;
its **equality still checks class and parent first** (§5.5), and is not universal equality
of all cache objects. [Audit F10](archive/audit.md)

Hash-table enumeration is not a universally sorted order. The declared implementation
policy and any exposed hash/serial/order observations constrain representation changes.
Dictionary entry cardinality/history is separately specified in §3.8.

### 5.4 Symbols and keywords

`symbol x` (or evaluating an unassigned global `x`, §3.3) yields a `SymbolClosure`. Its class
is `Keyword` if the word has non-default parse information (all operators and keywords, e.g.
`symbol +`, `symbol if`, `symbol SPACE`). Otherwise the class is `Symbol`. The value stored in
a symbol is read with `value s` and written with `s <- v` (§6.10).

Two symbol closures are `===`-equal iff they have the same symbol and the same frame. Ordinary
global symbols use the global frame; thread-global reification uses its actual thread frame.

<a id="rule-cache-equality"></a>

### 5.5 Strict equality `===`

`x === y` (and its negation `x =!= y`) does not use user-defined equality methods.
The ordinary core cases below return Booleans. Do not infer totality across external
engine equality failures or Error objects embedded in composites; those boundary cases
remain OC-EQUALITY. The following cases summarize `equality.dd`:

* identical representations → `true`;
* ZZ/ZZ, QQ/QQ: numeric equality. **Different numeric representations are never `===`**, so
  `3 === 3.0` is `false` ✔ and `1/2 === 0.5` is `false` ✔;
* RR/RR, CC/CC, RRi/RRi, CCi/CCi: strict equality of value **and precision**. ✔
  `1.0p100 === 1.0p53` is `false`, although `==` is `true`;
* String/String: byte equality. Net/Net: equality of rows and baseline;
* Sequence/Sequence: equal length and elementwise `===`;
* List/List: both immutable, same class (by `===`), equal hash, equal length, elementwise `===`;
* **HashTable/HashTable, ordered branch:** object identity succeeds first; unequal hashes
  fail; different class or parent identities fail; then hash zero with the **exact**
  CacheTable class succeeds. Only after that special case do mutable tables fail distinct-
  object comparison. Ordinary immutable tables proceed to the native structural entry
  comparison. A subclass is not automatically admitted by the exact-class cache branch.
  In particular, direct CacheTable objects with different parents are unequal.
  [Audit F10](archive/audit.md);
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

<a id="rule-frame-view"></a>

### 5.7 Reflective storage interfaces

**FRAME-VIEW.** `frame`/`frames` are not printing conveniences. For a non-global frame,
the pinned implementation returns a **MutableList wrapper around the backing value
sequence**, rather than copying the values. Writes to an existing slot in that shared
sequence can be observed through a closure reading the captured variable. For a global
frame the wrapper is empty to avoid bypassing global protection. [Audit F14](archive/audit.md)

| Input to `frame` | Selected backing environment |
|---|---|
| Empty argument sequence | Current local frame |
| Symbol reference | Its captured frame |
| FunctionClosure | Its captured environment, not a new call frame |
| PseudocodeClosure | Its captured frame |
| CompiledFunctionClosure | Its captured environment sequence |
| CompiledFunction | Empty environment |
| SpecialExpr | Delegate to wrapped value |
| Unsupported argument shape | Native argument error |

`frames` returns the outer-chain sequence of such views from the selected frame; the
compiled-closure case has its one captured environment view and a plain compiled function
has its empty view. `localDictionaries` exposes the corresponding dictionary/frame
closures, not maps of current values. A frame exposed only by these interfaces remains
observable and live.

An implementation must preserve the backing-sequence alias relation, not just an equal
list of values. Logical scope creation does not authorize showing an extra empty frame
where native inspection omits it. The view of an empty transient scope must follow the
native observable chain used by the actual closure/current frame.

**Open contract OC-FRAME:** the audit establishes existing-slot sharing and global hiding,
not a full rule for stale wrappers after backing-array replacement, capacity, out-of-range
extension, all empty-frame/debugger combinations, or every invalid argument. These cases
must be contracted and probed before full reflection conformance; neither “always live
frame proxy” nor “detached copy” is an authorized substitute.

<a id="rule-bootstrap-boundary"></a>

### 5.8 Native bootstrap interface register

**BOOTSTRAP-BOUNDARY.** A complete K implementation needs an exhaustive interface manifest.
`bootstrap-contracts.json` is the **identified-interface register for this revision**, not
that completed inventory. It records evidence status and open fields rather than inventing
arities or primitive results not established by the attached sources. [Audit F01, F17](archive/audit.md)

For each required export the final contract must enumerate: exact export/binding kind;
initial value/protection; argument packing and accepted representations; result; operand
and callback schedule; state effects; error/control behavior; reflection/aliasing effects;
host requests; and platform/numerical parameters. Overloads and library wrappers do not
remove the obligation for their native base primitive.

| Identified native interface | Established here | Outstanding coverage |
|---|---|---|
| `apply`, `scan`, `override` | Native D implementations/registrations exist; not exclusively library-defined | Complete accepted forms, callback/control behavior, result classes, failures |
| `isMutable` | Representation predicate in §5.3 | Native execution evidence |
| `frame`, `frames`, `localDictionaries` | Captured/live views, global hiding and chain requirement, §5.7 | OC-FRAME boundary cases |
| `symbolBody` | Declaration-only identity, forgetting activation | Full invalid-input/export contract |
| Native `value'` and its library-facing `value` | Symbol/current-cell, pseudocode and string source-unit roles; §7.5 | Wrapper/bootstrap inventory and remaining input/effect cases |
| `installMethod`, method lookup, nullary/typical-value tables | Native class-table authority and lookup/install rules, §6.5 | Complete exported arities and Option-installation error behavior |
| Dictionary/path/alias/query operations | Search, registration, retained entry/cardinality rules, §3 | Complete erase/rehash/query contracts, OC-DICT |
| Host/engine/native numeric interfaces | Their presence at the boundary is an obligation, not an implementation here | Exact catalog and pinned external contracts |

**Open contract OC-BOOTSTRAP:** inventory all D registrations and their initial bindings
before K/L can be certified. This revision corrects the boundary error but does not claim
that enumerating the known examples completes the inventory.

## 6. Evaluation

Source: `evaluate.d`, `actors*.d`, `hashtables.dd`, `classes.dd`.

<a id="rule-runtime-config"></a>

### 6.0 Configurations, effects and contract boundaries

The interpreter can be specified using configurations
`Eval(code, environment, continuation)`, `Deliver(completion, continuation)`,
`HostRequest(request, continuation)`, and `Done(completion)`, each paired with reached
state and ordered effects. Continuations must distinguish at least strict operand
sequencing, function return, each loop form/clause, try suppression/catchability,
comparison second-evaluation inspection, assignment-hook stages, and source-unit stages.
These are semantic distinctions, not mandatory machine allocation types.

Every defined transition retains state already produced. An implementation budget
suspension is separate from a language completion; it cannot be caught by M2 `try` or
turned into null. A pending host request is not a completed operand value. Default
strict propagation applies only where a more specific actor/continuation rule does not
say otherwise. In particular §§6.9.1, 6.9.2 and 6.10.1 are not instances of a uniform
“catch all control at the innermost construct” rule.

The attached evidence does not supply all native primitive/actor transitions. §8 names
those open contracts. Thus this is a single **partially closed** transition contract,
not a claim that an ActorId or HostRequest signature already defines every transition.
Implementations must report rule-level coverage. A future refinement theorem must name
the closed subset it covers until those obligations are discharged. [Audit F24](archive/audit.md)

### 6.1 Environments

Evaluation happens relative to a **current frame**. A frame is a vector of values plus a link
to its **outer frame**. A variable reference compiled as (depth *d*, index *i*) reads slot *i*
of the frame *d* links out. Globals live in the single global frame (per-thread for
`threadLocal` symbols). A slot never assigned holds `null`.

Required observable properties:

1. **Closures capture frames by reference.** ✔ `x := 10; f = () -> x; x = 20; f()` ⇒ 20.
   ✔ `g = () -> (n := 0; () -> (n = n+1)); c = g(); c(); c(); c()` ⇒ 3.
2. Each function call has a fresh **logical activation** for its parameters/locals. Native
   empty-frame elision and the exact reflective chain must be preserved by the observation
   projection (§5.7); a logical activation is not a mandate to expose an extra frame.
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
| **break** | `break [e]` | value or omitted operand | The loop/clause cases in §6.9.1; domain expressions are outside those handlers |
| **continue** | `continue [e]` | value or omitted operand | Only the loop **clause-specific handlers** in §6.9.1; native combining functions have their own primitive contracts, not a universal loop rule |
| **throw** | `throw e` | value | the innermost enclosing **`catch`** |
| **step / finish / unwind** | debugger actors | optional value as applicable | Debugger/source-unit policies; step/finish also satisfy the pinned `try` catchability predicate when suppression remains active (§6.9.2) |

These rules follow:

* Strict operand continuations propagate an abrupt result while retaining reached effects.
  **This is not universal:** the second left evaluation of `<=`/`>=` is inspected without a
  blanket Error/transfer check (§6.10.1). Clause-specific control, native callback primitives,
  and augmented-target schedules have their own rules. Ordinary binary evaluation is left
  first only where the actor specifies that schedule.
* **`try` excludes return, break, either continue form, unwind, and throw**; step and finish
  are not in that exclusion set. Catchability also depends on suppression/interrupt state
  (§6.9.2), not solely on a proposed Error-versus-Control datatype.
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

<a id="rule-method-authority"></a>

#### 6.5.5 One authoritative method/object store

**METHOD-AUTHORITY.** Method entries are the actual observable entries of the native
class/object tables. Nullary methods and typical-value records are likewise designated
user-visible table objects, not independent hidden semantic registries. Direct allowed
M2 mutations of those entries affect subsequent lookup immediately. A separate index or
dispatch cache is derived, and may be invalidated/rebuilt; it cannot disagree with the
visible table and remain authoritative. [Audit F18](archive/audit.md)

For binary methods use the native placement policy already specified in §6.5.1: the
entry resides in the greater-hash operand class (the RHS table on a tie in the audited
binary branch), and lookup uses the same placement rule while traversing ancestors.
Unary entries are in their class table. Higher-arity placements must preserve the
native observable table policy, not merely produce the same call result.

Cache guards cover method-entry writes, class/parent changes and all other mutable lookup
dependencies. A conservative global epoch is an implementation option, not an extra
language object. Failed installation's effects on `typicalValues`, including ignored
recursive results in Option wrappers, remain OC-INSTALL until independently contracted.

<a id="rule-assign-result"></a>

### 6.6 Assignment

Assignment results are **per form**, not universally the supplied RHS:

| Form | Result |
|---|---|
| Direct variable or element store | Stored value on success |
| Custom operator/application/indirect assignment method | The invoked method's result |
| Augmented method that intercepts fallback | That method's result, with no implicit fallback store |
| Parallel assignment | Actual per-target results; a single target is unwrapped, multiple targets preserve the specified sequence/list result class |

The more specific rules below govern errors and partial effects. [Audit F13](archive/audit.md)

<a id="rule-assign-hook-schedule"></a>

#### 6.6.1 Variables

**ASSIGN-HOOK-SCHEDULE.** For `x = e` or a resolved variable `x := e`, evaluate `e` first.
A local assignment updates its addressed cell directly. For a global assignment:

1. Check symbol protection. Failure returns the protected-variable error without running
   hooks or performing the final store; already completed RHS effects remain.
2. Read the old value and **look up/capture its class's GlobalReleaseHook now**.
3. Look up the symbol-specific entry in `globalAssignmentHooks` under `symbolBody x`.
   If present, invoke its function, or listed functions in order, as `(symbol x,new)`.
4. Invoke the **captured** release method, if any, as `(symbol x,old)`.
5. **Now** look up the new value's class GlobalAssignHook, and invoke it as `(symbol x,new)`.
6. Store the new value in the global/thread-global cell and return it.

An error stops subsequent steps, but does not undo earlier RHS/hook mutations or output.
Invocation order is not lookup order: a symbol-specific hook that replaces the release
method does not change the method already captured for this assignment. Changes to the
new assignment method made before step 5 do affect that later lookup. [Audit F08](archive/audit.md)

**Indirect `<-` remains distinct.** Evaluate its left then right. If the left value is a
symbol and a symbol-specific hook entry exists, use the native global-assignment routine.
Otherwise check protection and directly update the captured symbol cell; do not add the
class hook path merely because the symbol is global. Non-symbol left values use the
specified `<-` method path. This preserves v1.0 R9 rather than merging all stores.

<a id="rule-parallel-result"></a>

#### 6.6.2 Parallel assignment

Evaluate RHS once. Let `n` be the number of target code items after immediate separator
flattening. If `n=1`, a scalar RHS is treated as one value; a Sequence or List RHS must
have exactly one element, which is selected. For other counts a Sequence or List must
have length `n`. A List records its class for reconstruction, then supplies its elements.

Assign each target in order using the corresponding direct-store, custom assignment,
method-installation, recursive delimiter, constructor, or omitted-target rule. An omitted
target returns that supplied item without a store. Stop on the first failure, retaining
earlier effects. Targets can be mixed and nested as §4.3 specifies.

The result collects the **returned per-target results**, not a blind copy of the original
RHS. For `n=1`, return the single result directly—even when RHS was a one-element List.
For `n≠1`, return a Sequence, or a List of the remembered RHS class. With zero targets
and a matching empty RHS, return the corresponding empty result. [Audit F13](archive/audit.md)

`(a,b)=(b,a)` swaps. A length mismatch is an error. `(x)=(5,)` fails because `(5,)` has two
elements. Unsupported nested target kinds fail at their native runtime check; the parser
must not eliminate mixed target shapes in advance.

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

<a id="rule-augment-schedule"></a>

### 6.7 Augmented assignment `L op= e`

Augmented assignment is not a universally valid macro `L = L op e`. It has native target-
specific evaluation, method interception, caching and fallback rules.

**AUGMENT-SCHEDULE.** Obtain the exact registered base operator for the augmented symbol.
Sequence/list/array/angle-bar target code uses recursive augmented parallel assignment;
RHS values are evaluated once and supplied itemwise under its arity/result rules. A single
augmented parallel target wraps its RHS as one item; it does not inherit every ordinary
parallel unpacking rule. [Audit F12, F13](archive/audit.md)

For a scalar target:

| Target path | Initial evaluation/selection order |
|---|---|
| Ordinary variable/other expression | Evaluate L once to its old value; evaluate RHS when interception or fallback needs it |
| `container # key`, where container evaluates to a HashTable | **Evaluate container → evaluate RHS → evaluate key → lookup/lock**. Cache container, key and RHS for this path |
| `container . name`, with a HashTable | Evaluate container → RHS → form globally reified field key → lookup/lock |
| `#`/dot target whose container is not a HashTable | Reuse the initially evaluated container for that first target read; preserve the subsequent fallback target schedule rather than applying the hash-table cache policy |
| `L ??= e` | Error-suppress/nullify L first. A non-null result returns immediately without RHS/store. The null case takes the native coalescing-assignment fallback path, not the ordinary old-value binary path |

For the ordinary augmented path, after obtaining the old value, look up a unary method
under the **augmented operator key** in that value's class. If present, obtain RHS if not
already cached and invoke the method on old value and RHS. A normal result completes the
operation with no implicit store unless it is a SymbolClosure whose **canonical word bytes
are exactly `Default`**. That test does not require a particular global SymbolId, namespace,
or activation. Such a symbol requests fallback. An abrupt method result propagates after
required lock cleanup. [Audit F11](archive/audit.md)

Fallback computes the ordinary base actor on the already obtained old value and cached
RHS/code, then assigns via the native target rule. For the hash-table path, update the
cached entry and unlock without re-evaluating container/key. Other operator/application
paths may re-evaluate target subexpressions while invoking their assignment methods;
these are not automatically lvalue references. The coalescing null case assigns RHS
without applying an ordinary binary base computation.

Locks are implementation machinery, but exclusion of callback effects, release on
failure, and evaluation order must agree with the selected native contract. Remaining
parallel/coalescing/alias/error boundary cases not established by the audit are OC-AUGMENT;
no completed full augmented-actor claim is made for those cases.

Required source-derived regression (not executed):

```m2
i=0; T=new MutableHashTable from {0=>10,1=>20};
T#i += (i=1;5);
(T#0,T#1)
```

The result is predicted to be `(10,25)` because the key reads `i` after the RHS updates it.
[Audit F12](archive/audit.md)

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

**while P do B** tests P and executes B while P is true; normal termination returns null.
**while P list L [do B]** normally evaluates/collects L, then optional B; normal termination
returns the collected List. **Abrupt behavior is the clause-specific matrix in §6.9.1**,
not a catch-all handler surrounding the loop. In particular, `while-list` and
`while-list-do` differ even for a bare break in the predicate. [Audit F04](archive/audit.md)

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
  is a `list L`, evaluate L and collect according to §6.9.1. Then evaluate `do B` if present,
  including after collector continue as that matrix directs.
* The value is the collected `List` if there is a `list` clause, else `null`. `break v` returns
  v.

✔ `for i to 3 list i` ⇒ `{0,1,2,3}`. `for i in {1,2,3,4,5} when i<4 list i` ⇒ `{1,2,3}`.

**try**: evaluate the primary with error messages suppressed. Apply the exact
`catchableByTry` predicate in §6.9.2; it is not simply “Error but no control completion.”
For a caught result or normal success:

| form | on error | on success |
|------|----------|------------|
| `try P` | `null` | value of P |
| `try P else A` | A | value of P |
| `try P then S [else A]` | A (or `null`) | S (the value of P is discarded) |
| `try P [then S] except v do B` | B with `v` bound to the error object (§6.4) | S, or the value of P |

**catch P**: evaluate P. A **throw v** completion becomes the value v.

**trap P** uses the same catchability predicate: `(value,null)` on normal success;
`(null,errorObject)` for a caught result; propagate an uncaught abrupt completion.

**x ?? y** (null coalescing): evaluate x using §6.9.2; a **caught** error/transfer counts
as null, while an uncaught result follows the native nullify path. If the
result is not `null` and its class has a unary `??` method, apply that method, whose result
replaces x. If the result is `null`, the value is y (evaluated only then); otherwise it is the
result. Unary `?? x` is just the first step. ✔ `null ?? 1` ⇒ 1, `3 ?? 1` ⇒ 3.

**return / break / continue / throw** create the abrupt completions of §6.2. Their operand is
evaluated first, and an error in it propagates instead.

**shield e**: evaluate e with interrupts deferred. **time e**, **timing e**, **elapsedTime
e**, **elapsedTiming e**: evaluate e and report or return CPU or elapsed time (`timing` returns
a `Time` list {seconds, value}). **profile**, **breakpoint** and **TEST** support profiling,
debugging and test registration.

<a id="rule-loop-clause"></a>

#### 6.9.1 Exact loop-clause completion matrix

**LOOP-CLAUSE.** “Propagate” exits this loop implementation with the same completion and
reached state; an enclosing construct may then handle it. `Continue(None)` is bare continue;
`Continue(Some(null))` is explicit-null continue and is different. The matrix is derived
from the pinned evaluator, not inferred from conventional loop semantics. [Audit F04](archive/audit.md)

| Loop form / active clause | Bare continue | Continue(value) | Bare break |
|---|---|---|---|
| `while P do B`: P | Propagate | Propagate | Return null |
| `while P do B`: B | Next test | Propagate | Return null |
| `while P list L`: P | Propagate | Propagate | Return null, even after earlier collection |
| `while P list L`: L | Skip append, next test | Append value, next test | Return collected list |
| `while P list L do B`: P | Propagate | Propagate | Return collected list |
| `while P list L do B`: L | Skip append, then execute B | Append value, then execute B | Return collected list |
| `while P list L do B`: B | Propagate | Propagate | Return collected list |
| `for`: when clause | Propagate | Propagate | Return collected list, or null without collection |
| `for`: collector | Skip append, then optional do | Append value, then optional do | Return collected list |
| `for`: do clause | Next iteration | Propagate | Return collected list, or null without collection |

At each handled-break position, `break value` returns that value, including explicit null.
Other abrupt completions at these positions propagate. An append already performed before
a failing do clause is not retroactively undone. For-domain evaluation occurs before the
loop frame/body and does not gain these handlers. Iterator acquisition/next-specific
failure paths remain OC-ITERATOR and must not be guessed from the matrix.

These two loops therefore have different source-predicted results:

```m2
i=0; a=while (if i==1 then break else true) list (i=i+1);
i=0; b=while (if i==1 then break else true) list (i=i+1) do null;
(a,b)
```

`a` is null; `b` is `{1}`. This is an unexecuted source-derived regression.

<a id="rule-try-catchability"></a>

#### 6.9.2 `try` suppression and catchability

**TRY-CATCHABILITY.** Save the previous suppression flag and enable suppression before
evaluating the primary. If evaluation has disabled suppression, do not classify its
result as caught. Otherwise restore the saved flag, then apply this predicate:

| Delivered result | Caught? |
|---|---|
| Normal value | No; success path |
| Ordinary runtime Error | Yes |
| Return, Break, Continue (either form), Unwind, Throw | No; propagate |
| Step, Step-with-value, Finish | **Yes**, when suppression remains active |
| Interrupt / host resource suspension | Not caught as an ordinary M2 error |

A typed completion model must preserve enough native error/transfer metadata to expose
a caught step/finish through `except` or `trap`. It must not manufacture an unrelated
ordinary Error record merely because its datatype split is different. The debugger's
full resumption/interrupt policy remains OC-DEBUG; these catchability branches are fixed.
[Audit F05](archive/audit.md)

For an uncaught abrupt result, propagate before evaluating a `then`/`else`/handler clause.
For normal success, run a present sequel or return the primary value. For a caught result,
run else, or allocate the except frame and bind the caught error object, or return null
when neither exists. Source-derived prediction: `try finish 3 else 7` returns `7`.

### 6.10 Built-in operator semantics

This table retains the supplied reference's core-case summaries. Fallback occurs **only
where the particular row/actor admits it**; `#`, strict equality and other fixed operations
are not given a method fallback by a blanket rule. "num" denotes ZZ, QQ, RR, CC, RRi, CCi.
The detailed numeric/backend and full actor catalog remains OC-ACTOR/OC-NUMERIC; these
summaries must not be presented as exhaustive contracts for every cross-type/error case.
The audited operand/control schedules override any ordinary left-first shorthand.

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
| `x < y`, `x > y`, `x <= y`, `x >= y` | `<`/`>` select strict comparison results; `<=`/`>=` use the exact two-evaluation and interval-sensitive actor in §6.10.1. Do not substitute a generic comparison-result membership check or a blanket propagation check. Unary forms dispatch as specified. |
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

<a id="rule-compare-second"></a>

#### 6.10.1 The native `<=` and `>=` actor

**COMPARE-SECOND.** These actors have a source-observable second evaluation that is not a
normal strict-operand continuation. [Audit F06](archive/audit.md)

```text
comparison = compareop(lhs, rhs)       # first lhs, then rhs
if comparison is abrupt: propagate it
second = evaluate(lhs)                 # retain its effects/diagnostics
if second is a normal RRi value:
    degenerate = strictEquality(leftEndpoint(second), rightEndpoint(second))
else:
    use the non-interval branch, even when second is an Error/transfer
```

Once the second evaluation has **delivered** a result, select the Boolean from the first
comparison `comparison`:

| Actor | Second result is a nondegenerate RRi | Second result is a degenerate RRi or is not an RRi |
|---|---|---|
| `<=` | true for `<` or `<=`; false otherwise | true for `<`, `==`, or `<=`; false otherwise |
| `>=` | true for `>` or `>=`; false otherwise | true for `>`, `==`, or `>=`; false otherwise |

The pinned source lacks an Error branch on the second result. A second delivered error
or control transfer therefore reaches the non-interval branch; its prior effects and
any emitted diagnostics remain. Do not extend this into permission to swallow a pending
host request, implementation budget exhaustion, or a host-level abort that never returns
a delivered operand result. Nested debugger/interrupt mechanics remain OC-DEBUG.

Source-derived, unexecuted regression:

```m2
n=0; f=()->(n=n+1; if n==1 then 1 else error "second");
r=try(f()<=2);
(r,n)
```

The predicted result is `(true,2)` under the outer error suppression. A conventional
monadic bind on the second evaluation would incorrectly change that result.

## 7. The top level

Source: `interp.dd:readeval4`, `readeval`, `load`, `value` and the audit's source excerpts.

<a id="rule-unit-step"></a>

### 7.1 The read–eval loop

**UNIT-STEP.** A file, value string, interactive session, or frontend unit has a static local
scope/frame, cursor with one-token lookahead, last value and output policy. The driver does:

```text
peek(true)
EOF -> finish with lastvalue or null according to returnLastvalue
NEWLINE or EOC -> consume and repeat
otherwise:
    tree = parse(8,true)
    consume one terminator from { ';', NEWLINE, EOC, EOF }
    bind tree in this source-unit scope
    if binding failed: follow §7.2 and do not execute this tree
    lower at current literal precision
    run unqualified BeforeEval(null)
    execute according to the stage-failure policy below
    handle completion or printing protocol
    resume from reached state and cursor
```

There is **no initial semicolon skip**. `a; b` is two statements because the first semicolon
terminates `a`; `;a` and `a;;b` fail at a semicolon beginning a statement. By contrast `(a;)`
is a semicolon block whose last operand is omitted/null. [Audit F03](archive/audit.md)

Do not prebind or decode a whole file against its initial environment. Effects of one
statement—including word registration, dictionary path and default precision—affect the
next. A token already legitimately peeked retains its old classification. Parsing/binding
errors retain effects already reached, but a failed statement is not evaluated.

<a id="rule-unit-failure"></a>

### 7.2 Stage failures and abrupt completions

**UNIT-FAILURE.** Let `stop = stopIfError or returnIfError`; keep the separate flag
`stopIfBreakReturnContinue`. Do not substitute a single generic Except handler for the
following policies. [Audit F16](archive/audit.md)

| Stage/result | `stop` true | Non-stopping path |
|---|---|---|
| Lexical/syntax error | Return phase failure | Recover using lexical/parser mode; retain reached effects and diagnostics |
| Binding error | Noninteractive source returns binding failure | Interactive source flushes/recovers according to native policy; never evaluate failed tree |
| BeforeEval error | Return annotated hook error | Record error, **continue to evaluate this statement** |
| Evaluation produces ordinary Error | Report if needed; return error | Record/report; continue next source input; no normal printing pipeline |
| AfterEval error | Return annotated hook error | Set `lastvalue = null`; continue printing pipeline |
| BeforePrint error | Return annotated hook error | Keep `printvalue = null`; continue Print/NoPrint with null; retain lastvalue |
| Print/NoPrint error | Return annotated hook error | Record error; continue AfterPrint/AfterNoPrint with lastvalue |
| AfterPrint/AfterNoPrint error | Return annotated hook error | Record error; continue next source input |

Binding's noninteractive-abort branch is not made optional by non-stopping runtime mode.
Actual source counters, all lexical-recovery/interrupt branches, and debugger resumption
remain OC-UNIT/OC-DEBUG where the audit does not establish a complete transition table.
The audited hook-stage choices above are mandatory, not unresolved.

For an evaluation transfer in `{return, break, either continue, step, step-with-value,
finish, throw}`, `stopIfBreakReturnContinue` requests returning that transfer immediately.
Otherwise the driver follows its report/stop path. An unwind result is handled separately
by replacing lastvalue with null. A normal result equal to the distinguished `end` input
sentinel ends the unit with null before the output pipeline.

Wrappers are not the driver. `load`/native value-string processing unwrap Return, Break,
both Continue forms, Step, Step-with-value and Finish to their payload (the native omitted
sentinel becomes null). **Throw is not in that unwrap set**. An interactive unhandled
transfer is reported according to driver flags; being a typed control result is not
permission for an invented wrapper to consume it.

### 7.3 Error display and debugging

Error messages and backtrace updates carry phase, source position and reached state.
Suppression changes both display and catchability (§6.9.2). A debugger can inspect live
captured state (§5.7); it is not a detached printed snapshot. Full debugger resumption,
interrupts, timer cancellation and source-position rewriting are **OC-DEBUG**, not defined
by simply naming `DebugControl` or passing an unconstrained host callback.

<a id="rule-hook-keys"></a>

### 7.4 Printing and evaluation hooks

**HOOK-KEYS.** The exact keys/arguments are:

| Hook stage | Method key | Argument | Normal result use |
|---|---|---|---|
| BeforeEval | `BeforeEval` (unqualified) | null | Ignore result; failure policy is §7.2 |
| AfterEval, with printing enabled | `AfterEval` (unqualified) | lastvalue | Replace lastvalue |
| BeforePrint | `{mode, BeforePrint}` | lastvalue | Replace printvalue |
| Print or NoPrint | `{mode, Print}` or `{mode, NoPrint}` | printvalue | Ignore result |
| AfterPrint or AfterNoPrint | `{mode, AfterPrint}` or `{mode, AfterNoPrint}` | lastvalue | Ignore result |

Unqualified means **not** `{mode,AfterEval}` or `{mode,BeforeEval}`. The absence of a hook
returns the input value for the native runmethod helper. BeforeEval runs after lowering.
After successful evaluation, when printing is enabled, the driver refreshes its captured
mode if topLevelMode changed, constructs the mode-qualified printing keys, and then runs
the stages above. Hook failure substitutions/continuation are not inferred from success
behavior; use §7.2. [Audit F02, F16](archive/audit.md)

A terminating semicolon selects NoPrint and AfterNoPrint; it does not skip evaluation,
AfterEval or BeforePrint. The library supplies ordinary history/output formatting, but
the driver's invocation protocol is a native requirement. Prompt lookup remains
`{mode,InputPrompt}` / `{mode,InputContinuationPrompt}` in ZZ with the line number.

<a id="rule-file-exit"></a>

### 7.5 Value strings, loading, exit hooks and close failures

Native `value'` reads a SymbolClosure's captured cell; evaluates Pseudocode in its relevant
current/captured frame; and evaluates a byte string, with appended newline, in a **new
static dictionary**, not an implicit caller-local lexical environment. SpecialExpr wraps
are delegated as in the native primitive. The library-facing `value` wrapper and all
remaining accepted/error cases belong in the bootstrap register, not an assumed builtin
with the same printed name.

Loading also creates a file-local static dictionary. Top-level `:=` names are local to
that unit, while ordinary assignment resolves through the usual rules. Save/set/restore
current file name/directory and relevant source context around the driver. Preserve the
file's closures and symbols after return when referenced elsewhere.

**FILE-EXIT.** Save outer fileExitHooks and install a fresh list for the unit. After the
driver returns, classify whether its raw result is a native Error representation; invoke
the current exit-hook list in order with that Boolean. The native raw test includes
error-represented transfers before wrapper unwrapping. Continue through hook failures,
remembering the last exit error; previously remembered unprinted exit errors are reported
when superseded. Restore the saved hook list. The last exit error, if any, replaces the
driver result. [Audit F16](archive/audit.md)

The file wrapper then attempts required close even when the driver returned an Error.
For a normal driver/exit result, close failure becomes an error; for an already returned
Error/transfer, the raw result and recognized-transfer unwrapping take precedence over
that close status. The recognized unwrap set is §7.2. Value strings restore their saved
currentString state and use the corresponding transfer-unwrapping rule, without a file
close. Do not treat close failure as rollback of prior effects.

These rules integrate the audited wrapper paths. Complete OS/file primitive interfaces,
all failed-open/interactive/frontend cases, and their exact diagnostics remain OC-HOST /
OC-UNIT. An unavailable external service must not be returned as an empty successful file.

### 7.6 Start-up

The executable's embedded startup loads Core and processes the command line. The visible
user language is therefore native registrations **plus** library definitions and methods.
This does not justify classifying native `apply`, `scan` or reflection as library-only.
Before claiming K/L, enumerate every required native registration and host contract (§5.8).
Successful parsing of a package does not establish successful Core bootstrap.

## 8. Open contracts, observations and conformance evidence

<a id="rule-open-contracts"></a>

### 8.1 Explicit remaining contracts

The following items are **not fixed by the attached audit**. Known rules in earlier
sections are already requirements; an open item does not reopen a confirmed correction.
The remaining items block a claim that the full runtime contract is complete. They are
tracked in `open-contracts.json` with the relevant audit findings. No additional native
research or execution was performed to invent their missing outcomes in this revision.

| Contract ID | Area | Required closure work |
|---|---|---|
| `OC-BOOTSTRAP` | All native exports and initial bindings | Inventory every required D registration and specify binding/protection, calling convention, argument/result/effect/error behavior. The identified register is not exhaustive. |
| `OC-ACTOR` | Complete per-actor transitions | Close every runtime actor and primitive case; define default actors, bootstrap attachments and fallback, rather than treating an ActorId name as a transition rule. |
| `OC-NUMERIC` | Numeric and platform parameters | Pin precision, rounding, cross-representation dispatch, intervals, NaNs/infinities, machine-size bounds and backend-error behavior for each required numerical primitive. |
| `OC-HOST` | External interface inventory | Enumerate typed host/engine requests, accepted arguments, results, errors, trace and state effects. External implementation may be excluded, interface semantics may not. |
| `OC-BIND` | Remaining binding-error edges and accounting | Complete all low-level lookup/parameter/creation failures, lookup counters and continuation edges beyond the audited assignment schedules; no generic fail-fast default. |
| `OC-WORD-VALID` | Native name validity and malformed byte tails | State the full predicate controlling self-valued creation and edge byte-scanning behavior, including malformed UTF-8/math-operator tails, before certifying those inputs. |
| `OC-FRAME` | Reflection beyond established shared slots | Specify backing-array replacement/stale views, size/capacity/extension, empty-frame observation and all invalid-input/debugger variants. Existing-slot sharing and global hiding are already required. |
| `OC-DICT` | Erase, rehash and entry observations | Finish canonical-name/alias erase behavior and entry-order/rehash/keys policies. Preserve shadowed entries and counts; do not substitute a deduplicated name map. |
| `OC-UNIT` | Remaining source-unit failure transitions | Finish complete driver-flag/kind/phase table, lexical recovery and exact diagnostics beyond the audited hook, transfer, exit-hook and close schedules. |
| `OC-DEBUG` | Debugger and interruption | Specify suppression changes, raw-transfer/error metadata, resumption, interrupt delivery and source-position behavior. The audited step/finish catchability is already fixed. |
| `OC-INSTALL` | Method installation error side effects | Resolve ignored recursive-installation results in Option wrappers and exact typicalValues state after each failure; full reflected entry/arity contracts remain required. |
| `OC-ITERATOR` | Iterator acquisition and next failures | Contract next/acquisition outcomes and loop-frame restoration before entering ordinary For clauses; do not infer this from the body completion matrix. |
| `OC-EQUALITY` | Error/external equality boundaries | Resolve Error values inside composites and backend equality errors; the corrected CacheTable branch does not establish universal equality totality. |
| `OC-AUGMENT` | Remaining augmented edge cases | Complete coalescing, parallel, alias-created and failure/cleanup branches beyond the audited evaluation schedule and canonical-name Default predicate. |

In particular, fixing the audit's concrete counterexamples is not a proof that there are
no additional discrepancies. Residual cases listed in the audit remain residual cases,
not promoted source-confirmed user-program results. [Audit §10 and F24](archive/audit.md)

### 8.2 Observation contracts and rule IDs

Conformance compares consumed source/cursor, accepted tree view, selected bindings,
completion, returned value/class, reached visible state and ordered diagnostic/host/hook
observations appropriate to the test. A namespace mutation or frame-slot write can be
observable through a later input even when it produces no immediate output.

Internal allocations may be renamed under an abstraction relation only while preserving
exposed symbol, activation, hash/serial, alias, object and enumeration observations. Do
not require arbitrary native pointer addresses as portable values; do not erase an
actually exported numeric identity by an unqualified renaming argument.

`rule-index.json` gives stable rule IDs and section anchors. The language text supplies
the rule; JSON fixtures describe tests of it. A copied table, fixture count or successful
schema check is not independent native evidence.

<a id="rule-conformance-records"></a>

### 8.3 Test records and coverage

`audit-regressions-v1.1.json` supplies typed **unexecuted** source and configuration
fixtures for the corrected rules. Source fixtures identify exact source bytes, starting
assumptions, entry API/mode and typed projected observations. Configuration fixtures
specify a controlled continuation/table state; they still need a runner/native adapter.
No fixture is labeled observed or passing. The original 146-case prose plan is archived
unchanged and is not treated as an independently executable oracle.

Each executed native record must eventually include the pinned version/build,
initialization, complete source or fixture setup, exit status, stdout/stderr bytes,
observed phase/completion/state projection and failure classification. Budget exhaustion,
unsupported serialization and missing implementation are separate from an expected M2
error. Expected results must be checked independently of the implementation under test.

Still required: all-word leading/trailing tests; complete operator-pair boundary cases;
all clause and delimiter combinations; malformed/error phase cases; all declared native
primitive contracts; mutation/reflection/alias histories; and host/engine boundary
contracts. The stable rule IDs support coverage accounting but do not manufacture it.
[Audit F21](archive/audit.md)

<a id="rule-structural-checks"></a>

### 8.4 Structural validation, negative controls and proof status

`validate_spec.py` checks active document/manifest agreement, the fixed per-word quote
policies, lexical routes, first-wins registration, terminator/skip sets, all tracked audit
IDs, open-contract references, fixture schema/evidence labels, source provenance hashes,
HTML source binding and the declared checksum manifest. It also compares the 121 base
words to the **archived supplied-reference table**; this metric is deliberately not
called native-source extraction.

`test_validator.py` demonstrates that main-table drift and a wrong `symbol` quote policy
are rejected **even after recomputing checksums**. A well-typed but wrong arithmetic
expected value remains acceptable to structural validation, explicitly demonstrating
that behavioral truth is not checked. The generated reports distinguish these outcomes.
[Audit F20](archive/audit.md)

No F/K/L implementation conformance, Lean compilation, benchmark, kernel proof or native
M2 execution is established by this revision. A future theorem must refer to a uniquely
defined closed rule set and state its coverage. One-way soundness is insufficient:
finite specification executions must also be obtainable with sufficient resources.
The separate architecture document explains this refinement plan without pretending
that the still-open runtime relation has already been completed.

## Appendix A. Keywords and reserved words

Identifier-shaped words with special parse behavior in ordinary expression positions.
The table determines whether each can begin/continue an expression; they are not all
prefix errors. Quotation can consume any lexical `id` word directly (§2.5.5). This list
is not a substitute for those contextual rules:

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

This revised contract's corrections are grounded in `archive/audit.md`, findings F01–F24,
which records the pinned source functions, distinctions between confirmed mismatches and
open contracts, and the original unexecuted probe status. The source links below are
traceability, not a claim they were newly fetched or executed for this revision.

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

The target completion checklist below is **not an achieved conformance claim**. All
open contracts in §8 must be closed for the relevant level, and independent tests must
then establish the implementation behavior. A target implementation:

1. lexes per §1, including the math-operator rule, `///` strings and the number quirks;
2. implements the Pratt parser of §2.4 with the table of §2.3, including the obeylines/newline
   behaviour of §2.5.7;
3. binds names per §3, including reached effects on binding failure, three transient
   scope-creating constructs and static source-unit scopes;
4. applies the translation identities of §4 (unseq, empty operands as `null`);
5. provides §5 values/classes, the native mutability/equality predicates, dictionary
   history, live reflection contracts, and the completed bootstrap interface inventory;
6. evaluates per §6, including clause-specific completion handlers, try catchability,
   comparison second-evaluation behavior, hook lookup time, augmented-target schedules,
   per-form assignment results, and one authoritative visible method/object store;
7. runs the top-level protocol of §7;
8. then loads the Macaulay2 `Core` library on top, which supplies the rest of the language
   users know.
