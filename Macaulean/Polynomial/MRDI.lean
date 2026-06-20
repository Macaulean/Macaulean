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

instance [MrdiType R] : MrdiType (Polynomial.Expr R n) := sorry
