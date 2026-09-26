import Macaulean.Interpreter.Value

/-!
# Typed value transport for independent differential checks

This format is deliberately NOT M2 source: a preorder stream of class tags,
lengths, and scalar payloads preserves all nested classes. Decoding invokes
neither the interpreter nor either frontend parser. Malformed/truncated/extra
payloads and unsupported classes fail explicitly.
-/
namespace Macaulean.M2
namespace Value

mutual

def toWire : Value → List String
  | .zz n => ["ZZ", toString n]
  | .qq q => ["QQ", toString q.num, toString q.den]
  | .bool b => ["Boolean", toString b]
  | .null => ["Nothing"]
  | .list xs => ["List", toString xs.length] ++ elementsWire xs
  | .sequence xs => ["Sequence", toString xs.length] ++ elementsWire xs

def elementsWire : List Value → List String
  | [] => []
  | x :: xs => toWire x ++ elementsWire xs

end

mutual

def readWire : Nat → List String → Except String (Value × List String)
  | 0, _ => .error "value wire decoder ran out of fuel"
  | fuel + 1, tokens =>
    match tokens with
    | "ZZ" :: n :: rest =>
      match n.toInt? with
      | some n => .ok (.zz n, rest) | none => .error "invalid wire integer"
    | "QQ" :: n :: d :: rest =>
      match n.toInt?, d.toNat? with
      | some n, some d =>
        if d = 0 then .error "zero wire denominator"
        else .ok (.qq (mkRat n d), rest)
      | _, _ => .error "invalid wire rational"
    | "Boolean" :: "true" :: rest => .ok (.bool true, rest)
    | "Boolean" :: "false" :: rest => .ok (.bool false, rest)
    | "Nothing" :: rest => .ok (.null, rest)
    | "List" :: n :: rest => do
      let some n := n.toNat? | .error "invalid wire list length"
      let (xs, rest) ← readElements fuel n rest
      return (.list xs, rest)
    | "Sequence" :: n :: rest => do
      let some n := n.toNat? | .error "invalid wire sequence length"
      let (xs, rest) ← readElements fuel n rest
      return (.sequence xs, rest)
    | _ => .error "unsupported or truncated value wire data"

def readElements : Nat → Nat → List String → Except String (List Value × List String)
  | _, 0, rest => .ok ([], rest)
  | 0, _ + 1, _ => .error "value wire decoder ran out of fuel"
  | fuel + 1, n + 1, tokens => do
    let (x, rest) ← readWire fuel tokens
    let (xs, rest) ← readElements fuel n rest
    return (x :: xs, rest)

end

def ofWire (tokens : List String) : Except String Value := do
  let (v, rest) ← readWire (2 * tokens.length + 2) tokens
  if rest.isEmpty then return v else .error "trailing value wire data"

end Value
end Macaulean.M2
