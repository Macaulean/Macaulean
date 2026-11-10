import Lean
import Macaulean.Interpreter.Value

/-! First-order reification for kernel-checked execution equalities.
Session-relative ring IDs are never imported from a foreign process. -/
namespace Macaulean.M2
open Lean
deriving instance ToExpr for Polynomials.Primitive

def algebraRingExpr (r : Polynomials.RingInfo) : Expr :=
  mkApp2 (mkConst ``Polynomials.RingInfo.mk) (toExpr r.id) (toExpr r.names)
def algebraRatExpr (q : Rat) : Expr :=
  mkApp2 (mkConst ``mkRat) (toExpr q.num) (toExpr q.den)
def rawPolynomialExpr : Polynomials.Raw → Expr
  | [] => mkApp (mkConst ``List.nil [0])
      (mkApp2 (mkConst ``Prod [0,0]) (mkConst ``Rat) (mkApp (mkConst ``List [0]) (mkConst ``Nat)))
  | (c, ns) :: rest =>
    let nt := mkApp (mkConst ``List [0]) (mkConst ``Nat)
    let pt := mkApp2 (mkConst ``Prod [0,0]) (mkConst ``Rat) nt
    let pair := mkApp4 (mkConst ``Prod.mk [0,0]) (mkConst ``Rat) nt (algebraRatExpr c) (toExpr ns)
    mkApp3 (mkConst ``List.cons [0]) pt pair (rawPolynomialExpr rest)
def rawPolynomialsExpr : List Polynomials.Raw → Expr
  | [] => mkApp (mkConst ``List.nil [0]) (mkConst ``Polynomials.Raw)
  | p :: ps => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Polynomials.Raw)
      (rawPolynomialExpr p) (rawPolynomialsExpr ps)
def algebraObjectExpr : Polynomials.Object → Expr
  | .rationals => mkConst ``Polynomials.Object.rationals
  | .ring r => mkApp (mkConst ``Polynomials.Object.ring) (algebraRingExpr r)
  | .poly r p => mkApp2 (mkConst ``Polynomials.Object.poly) (algebraRingExpr r) (rawPolynomialExpr p)
  | .ideal r ps => mkApp2 (mkConst ``Polynomials.Object.ideal) (algebraRingExpr r) (rawPolynomialsExpr ps)
  | .row r ps => mkApp2 (mkConst ``Polynomials.Object.row) (algebraRingExpr r) (rawPolynomialsExpr ps)
  | .builtin p => mkApp (mkConst ``Polynomials.Object.builtin) (toExpr p)
end Macaulean.M2
