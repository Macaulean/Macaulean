import MRDI
import Macaulean.Polynomial.Basic
import Lean

open Lean Json MRDI Macaulean

/-
  Note: For now we make the decision not to make Mon and PolyTerm have instance of MrdiType.
-/

def encodeMon (m : Mon n) : MrdiEncodeM Json := do
  pure <| toJson <| m.powers.map toString

def encodePolyTerm [MrdiType R] (t : PolyTerm R n) : MrdiEncodeM Json := do
  let coeffJson ← MrdiType.encode t.coefficient
  let monJson ← encodeMon t.monomial
  pure <| .arr #[coeffJson, monJson]

def decodeMon? : Json → MrdiDecodeM (Except String (Mon n))
  | .arr powersJson =>
    let powers? := powersJson.map getStr?
    match (powers?.mapM id).map Array.toList with
    | .ok powers =>
      match powers.mapM String.toNat? with
      | .some powers =>
        if h : powers.length = n
        then pure <| .ok <| Mon.mk powers h
        else pure <| .error s!"Expected an array of length {n}"
      | _ => pure <| .error s!"Expected an array of Naturals as powers"
    | .error s => pure <| .error s
  | _ => pure <| .error "Expected an array of Naturals as powers"

def decodeTerm? [MrdiType R] : Json →  ExceptT String MrdiDecodeM (PolyTerm R n)
  | .arr #[c, m] => do
    let coeff : R ← MrdiType.decode? c
    let mon ← decodeMon? m
    pure <| PolyTerm.mk coeff mon
  | _ => throw "Expected a pair of a coefficient and a monoial"

instance [MrdiType R] : MrdiType (Polynomial R n) where
  mrdiType := .parameterized "Polynomial" (toJson <| MrdiType.mrdiType R) --TODO encode the n as well
  encode poly := do
    .arr <$> List.toArray <$> poly.terms.mapM encodePolyTerm
  decode?
    | .arr elems => do
      (elems.mapM (decodeTerm? (R := R) (n := n))).runK
        (ok := fun terms => pure <| .ok <| Polynomial.mk terms.toList)
        (error := fun err => pure <| .error err)
    | _ => pure <| .error s!"Expected an Array of terms"

namespace Macaulean.Polynomial.Expr

mutual
  /-- Encode the expression tree without normalizing or flattening it. -/
  def encode [MrdiType R] : Expr R n → MrdiEncodeM Json
    | .sum terms => do pure <| .arr #[.str "sum", .arr (← encodeList terms).toArray]
    | .product factors => do pure <| .arr #[.str "product", .arr (← encodeList factors).toArray]
    | .pow p k => do pure <| .arr #[.str "pow", ← encode p, .str (toString k)]
    | .term t => do pure <| .arr #[.str "term", ← encodePolyTerm t]
  def encodeList [MrdiType R] : List (Expr R n) → MrdiEncodeM (List Json)
    | [] => pure []
    | p :: ps => do pure <| (← encode p) :: (← encodeList ps)
end

/-- Budget derived from the compact JSON character count by `decode?`; not a fixed
limit on supported expression depth. Coefficients use their own MRDI decoder. -/
def decodeWithFuel? [MrdiType R] : Nat → Json → ExceptT String MrdiDecodeM (Expr R n)
  | 0, _ => throw "Polynomial.Expr: exhausted JSON nesting budget"
  | fuel+1, .arr #[.str "sum", .arr terms] =>
    do return .sum (← terms.mapM (decodeWithFuel? fuel)).toList
  | fuel+1, .arr #[.str "product", .arr factors] =>
    do return .product (← factors.mapM (decodeWithFuel? fuel)).toList
  | fuel+1, .arr #[.str "pow", p, .str exponent] => do
    let some k := exponent.toNat? | throw "Polynomial.Expr: expected a natural exponent string"
    return .pow (← decodeWithFuel? fuel p) k
  | _+1, .arr #[.str "term", t] => .term <$> decodeTerm? t
  | _+1, _ => throw "Polynomial.Expr: expected a tagged sum, product, pow, or term"

def decode? [MrdiType R] (json : Json) : MrdiDecodeM (Except String (Expr R n)) :=
  (decodeWithFuel? (json.compress.length + 1) json).run

end Macaulean.Polynomial.Expr

instance [MrdiType R] : MrdiType (Polynomial.Expr R n) where
  mrdiType := .parameterized "Macaulean.Polynomial.Expr" (.mkObj [
    ("coefficient", toJson (MrdiType.mrdiType R)), ("variables", .str (toString n))])
  encode := Polynomial.Expr.encode
  decode? := Polynomial.Expr.decode?
