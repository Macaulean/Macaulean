import Macaulean.Interpreter.Parser

/-! # Located single-input reader, including polynomial-ring brackets -/
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
  stop : Nat := 0
  silent : Bool := false
  deriving Inhabited
structure Parsed where
  tokens : Tokens
  tree : Parser.Tree
  deriving Inhabited
private def consumedBytes (before after : List Char) : Nat :=
  (String.ofList (before.take (before.length - after.length))).utf8ByteSize
private def push (acc : Array LocatedToken) (t : Token) (start stop : Nat) :=
  acc.push ⟨t, ⟨start, stop⟩⟩
private def continues : Token → Bool
  | .sym .kwIf | .sym .kwThen | .sym .kwElse | .sym .kwNot | .sym .kwLocal => true
  | .sym .comma | .sym .kwReturn => false
  | .sym sym => (Parser.infixInfo sym).isSome | _ => false
private def scanAux : Nat → List Char → Nat → Nat → Nat → Bool → Array LocatedToken → Except String Tokens
  | 0, _, _, _, _, _, _ => .error "M2 input reader ran out of fuel"
  | _ + 1, [], pos, _, _, _, acc => .ok ⟨acc, pos, false⟩
  | fuel + 1, c :: cs, pos, depth, predicates, pending, acc =>
    if c = '\n' then
      if depth = 0 && predicates = 0 && !pending then .ok ⟨acc, pos + 1, false⟩
      else scanAux fuel cs (pos + 1) depth predicates pending (push acc .newline pos (pos + 1))
    else if c = ' ' ∨ c = '\t' ∨ c = '\r' then scanAux fuel cs (pos + 1) depth predicates pending acc
    else if c = '-' ∧ cs.head? = some '-' then
      let tail := Lexer.dropComment cs
      let stop := pos + consumedBytes (c :: cs) tail
      scanAux fuel tail stop depth predicates pending acc
    else if c.isDigit then
      let (n, tail) := Lexer.number (c :: cs)
      if Lexer.floatSuffix tail then .error "floating point literals are not supported"
      else
        let stop := pos + consumedBytes (c :: cs) tail
        scanAux fuel tail stop depth predicates false (push acc (.num n) pos stop)
    else if Lexer.isIdentStart c then
      let (letters, tail) := Lexer.span Lexer.isIdentChar cs
      let word := String.ofList (c :: letters)
      let token := Lexer.identifierToken word
      let stop := pos + word.utf8ByteSize
      let predicates := match token with
        | .sym .kwIf => predicates + 1 | .sym .kwThen => predicates - 1 | _ => predicates
      scanAux fuel tail stop depth predicates (continues token) (push acc token pos stop)
    else match Lexer.symbol (c :: cs) with
      | none => .error s!"unsupported character '{c}'"
      | some (sym, tail) =>
        let stop := pos + consumedBytes (c :: cs) tail
        if sym = .semi ∧ depth = 0 then .ok ⟨acc, stop, true⟩
        else
          let depth := if sym = .lparen ∨ sym = .lbrace ∨ sym = .lbracket then depth + 1
            else if sym = .rparen ∨ sym = .rbrace ∨ sym = .rbracket then depth - 1 else depth
          scanAux fuel tail stop depth predicates (continues (.sym sym)) (push acc (.sym sym) pos stop)
def scan (source : String) : Except String Tokens :=
  let chars := source.toList
  scanAux (chars.length + 1) chars 0 0 0 false #[]
def parse (source : String) : Except String Parsed := do
  let tokens ← scan source
  let tree ← Parser.parseInputTree (tokens.located.toList.map (·.token))
  return ⟨tokens, tree⟩
end Input
end Macaulean.M2
