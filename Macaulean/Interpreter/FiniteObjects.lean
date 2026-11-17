import Macaulean.Algebra.FinitePolynomialData

namespace Macaulean.M2.Finite
open Lean
abbrev Raw := Algebra.FinitePolynomialData.Raw

structure RingInfo where
  id : Nat
  offset : Nat
  names : List String
  deriving Repr, DecidableEq, Inhabited, ToExpr

def RingInfo.display (r : RingInfo) : String :=
  s!"GF({r.offset+2})[" ++ ", ".intercalate r.names ++ "]"

/-- Runtime containers are data. Field and Gröbner guarantees must be checked
at mathematical export/certification boundaries. -/
inductive Object where
  | field (offset : Nat)
  | scalar (offset residue : Nat)
  | ring (info : RingInfo)
  | poly (info : RingInfo) (terms : Raw)
  | ideal (info : RingInfo) (generators : List Raw)
  | row (info : RingInfo) (entries : List Raw)
  | matrix (info : RingInfo) (columns : Nat) (entries : List (List Raw))
  | basis (info : RingInfo) (input generators : List Raw) (representations : List (List Raw))
  deriving Repr, DecidableEq, Inhabited, ToExpr

def Object.ring? : Object → Option RingInfo
  | .ring r | .poly r _ | .ideal r _ | .row r _ | .matrix r .. | .basis r .. => some r
  | _ => none

def Object.className : Object → String
  | .field _ => "Type" | .scalar p _ => s!"GF({p+2})"
  | .ring _ => "PolynomialRing" | .poly r _ => r.display
  | .ideal .. => "Ideal" | .row .. | .matrix .. => "Matrix" | .basis .. => "GroebnerBasis"

def polynomialText (r : RingInfo) (ts : Raw) : String :=
  if ts.isEmpty then "0" else
  " + ".intercalate (ts.map fun (c,ns) =>
    let mon := "*".intercalate ((r.names.zip ns).filterMap fun (x,n) =>
      if n = 0 then none else some (if n = 1 then x else s!"{x}^{n}"))
    if mon.isEmpty then toString c else if c = 1 then mon else s!"{c}*{mon}")

def Object.toM2String : Object → String
  | .field p => s!"GF({p+2})" | .scalar _ c => toString c
  | .ring r => r.display | .poly r ts => polynomialText r ts
  | .ideal r gs => "ideal(" ++ ", ".intercalate (gs.map (polynomialText r)) ++ ")"
  | .row r gs => "matrix{{" ++ ", ".intercalate (gs.map (polynomialText r)) ++ "}}"
  | .matrix r _ rows => "matrix{" ++ ", ".intercalate (rows.map fun row =>
      "{" ++ ", ".intercalate (row.map (polynomialText r)) ++ "}") ++ "}"
  | .basis _ _ gs _ => s!"GroebnerBasis[{gs.length} generators]"
end Macaulean.M2.Finite
