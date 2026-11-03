import Macaulean.Interpreter.Parser

/-!
# Located REPL input

The adapter stops at one M2 input boundary, not at an arbitrary Lean whitespace
boundary. The Pratt grammar remains `Parser.parseTreeExpr`; token spelling is
handled by the same lexical primitives as `Lexer.lex`.
-/

namespace Macaulean.M2
namespace Input

structure Span where
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq, Inhabited

structure LocatedToken where
  token : Token
  span : Span
  deriving Repr, Inhabited

structure Tokens where
  located : Array LocatedToken := #[]
  /-- First byte after the input terminator, relative to this input. -/
  stop : Nat := 0
  silent : Bool := false
  deriving Inhabited

structure Parsed where
  tokens : Tokens
  tree : Parser.Tree
  deriving Inhabited

/-- Byte width of the consumed prefix. Source ranges must not count Unicode characters. -/
private def consumedBytes (before after : List Char) : Nat :=
  (String.ofList (before.take (before.length - after.length))).utf8ByteSize

private def push (acc : Array LocatedToken) (t : Token) (start stop : Nat) :=
  acc.push ⟨t, ⟨start, stop⟩⟩

/-- Every recursive call consumes a character; fuel bounds all scanning. -/
private def scanAux : Nat → List Char → Nat → Nat → Bool → Array LocatedToken →
    Except String Tokens
  | 0, _, _, _, _, _ => .error "M2 input reader ran out of fuel"
  | _ + 1, [], pos, _, _, acc => .ok ⟨acc, pos, false⟩
  | fuel + 1, c :: cs, pos, depth, pending, acc =>
    if c = '\n' then
      if depth = 0 && !pending then .ok ⟨acc, pos + 1, false⟩
      else scanAux fuel cs (pos + 1) depth pending (push acc .newline pos (pos + 1))
    else if c = ' ' ∨ c = '\t' ∨ c = '\r' then
      scanAux fuel cs (pos + 1) depth pending acc
    else if c = '-' ∧ cs.head? = some '-' then
      let tail := Lexer.dropComment cs
      let stop := pos + consumedBytes (c :: cs) tail
      scanAux fuel tail stop depth pending acc
    else if c.isDigit then
      let (n, tail) := Lexer.number (c :: cs)
      if tail.head?.any (fun d => d = '.' ∨ d = 'p' ∨ d = 'e' ∨ d = 'E') then
        .error "floating point literals are not supported"
      else
        let stop := pos + consumedBytes (c :: cs) tail
        scanAux fuel tail stop depth false (push acc (.num n) pos stop)
    else if Lexer.isIdentStart c then
      let (letters, tail) := Lexer.span Lexer.isIdentChar cs
      let word := String.ofList (c :: letters)
      let stop := pos + word.utf8ByteSize
      scanAux fuel tail stop depth false (push acc (.ident word) pos stop)
    else
      match Lexer.symbol (c :: cs) with
      | none => .error s!"unsupported character '{c}'"
      | some (sym, tail) =>
        let stop := pos + consumedBytes (c :: cs) tail
        if sym = .semi ∧ depth = 0 then .ok ⟨acc, stop, true⟩
        else
          let depth := if sym = .lparen then depth + 1
            else if sym = .rparen then depth - 1 else depth
          let pending := (Parser.infixInfo sym).isSome
          scanAux fuel tail stop depth pending (push acc (.sym sym) pos stop)

/-- Read exactly one input, leaving the remaining file to Lean's command loop. -/
def scan (source : String) : Except String Tokens :=
  let chars := source.toList
  scanAux (chars.length + 1) chars 0 0 false #[]

/-- Parse through the same concrete tree parser used by the string interpreter. -/
def parse (source : String) : Except String Parsed := do
  let tokens ← scan source
  let tree ← Parser.parseInputTree (tokens.located.toList.map (·.token))
  return ⟨tokens, tree⟩

end Input
end Macaulean.M2
