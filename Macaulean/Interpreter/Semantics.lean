import Macaulean.Interpreter.Run

/-!
# Semantics of the integer fragment

The interpreter is meant to *be* the semantics of the language, so these
theorems check that it behaves as expected on the arithmetic fragment:

* `IntExpr.evalTerm_toTerm`: on terms built from integer literals, `+`, `-`,
  `*`, `//`, `%`, prefix `-` and `^` with a natural-number exponent, the
  interpreter computes exactly the corresponding operations on `Int`.
* `quot_rem_spec`: Macaulay2's `//` and `%` on `ZZ` are Euclidean division
  (the remainder lies in `[0, |b|)`), and they are uniquely determined by this.
* `div_spec`: `/` on `ZZ` gives the element of `QQ` that equals `a` after
  multiplying by `b`.
-/

namespace Macaulean.M2

open Value

/-- Integer expressions. -/
inductive IntExpr where
  | lit (n : Int)
  | neg (a : IntExpr)
  | add (a b : IntExpr)
  | sub (a b : IntExpr)
  | mul (a b : IntExpr)
  | quot (a b : IntExpr)
  | rem (a b : IntExpr)
  | pow (a : IntExpr) (k : Nat)

namespace IntExpr

/-- The intended meaning of an integer expression. -/
def denote : IntExpr → Int
  | lit n => n
  | neg a => -a.denote
  | add a b => a.denote + b.denote
  | sub a b => a.denote - b.denote
  | mul a b => a.denote * b.denote
  | quot a b => a.denote / b.denote
  | rem a b => a.denote % b.denote
  | pow a k => a.denote ^ k

/-- The corresponding Macaulay2 term. -/
def toTerm : IntExpr → Term
  | lit n => .int n
  | neg a => .unop .neg a.toTerm
  | add a b => .binop .add a.toTerm b.toTerm
  | sub a b => .binop .sub a.toTerm b.toTerm
  | mul a b => .binop .mul a.toTerm b.toTerm
  | quot a b => .binop .quot a.toTerm b.toTerm
  | rem a b => .binop .rem a.toTerm b.toTerm
  | pow a k => .binop .pow a.toTerm (.int k)

/-- The interpreter computes integer expressions correctly, in any environment,
and leaves the environment unchanged. -/
theorem evalTerm_toTerm (t : IntExpr) (env : Env) :
    evalTerm t.toTerm env = .ok (zz t.denote, env) := by
  induction t <;>
    simp_all [toTerm, denote, evalTerm, evalBinOp, evalUnOp, bind, Except.bind, pure, Except.pure]

theorem evalProgram_toTerm (t : IntExpr) : evalProgram t.toTerm = .ok (zz t.denote) := by
  simp [evalProgram, evalTerm_toTerm, Functor.map, Except.map]

end IntExpr

/-- `//` and `%` on `ZZ` satisfy the Euclidean division property. -/
theorem quot_rem_spec (a b : Int) (hb : b ≠ 0) :
    ∃ q r, evalBinOp .quot (zz a) (zz b) = .ok (zz q) ∧
      evalBinOp .rem (zz a) (zz b) = .ok (zz r) ∧
      a = b * q + r ∧ 0 ≤ r ∧ r < b.natAbs :=
  ⟨a / b, a % b, rfl, rfl, (Int.mul_ediv_add_emod a b).symm, Int.emod_nonneg a hb,
    Int.emod_lt a hb⟩

/-- The Euclidean division property determines `q` and `r`, so `quot_rem_spec`
pins down `//` and `%` completely (for nonzero divisors). -/
theorem quot_rem_unique {a b q r : Int} (hb : b ≠ 0)
    (h : a = b * q + r) (h0 : 0 ≤ r) (h1 : r < b.natAbs) :
    evalBinOp .quot (zz a) (zz b) = .ok (zz q) ∧
      evalBinOp .rem (zz a) (zz b) = .ok (zz r) := by
  have ⟨hq, hr⟩ : a / b = q ∧ a % b = r := by
    rcases Int.lt_or_gt_of_ne hb with hneg | hpos
    · exact (Int.ediv_emod_unique' hneg).2 ⟨by omega, h0, by omega⟩
    · exact (Int.ediv_emod_unique hpos).2 ⟨by omega, h0, by omega⟩
  simp [evalBinOp, hq, hr]

/-- Division by zero with `//` and `%` does not fail: `a // 0 = 0` and `a % 0 = a`. -/
theorem quot_rem_zero (a : Int) :
    evalBinOp .quot (zz a) (zz 0) = .ok (zz 0) ∧
      evalBinOp .rem (zz a) (zz 0) = .ok (zz a) := by
  simp [evalBinOp]

/-- `/` on `ZZ` lands in `QQ`, and multiplying the quotient back gives `a`. -/
theorem div_spec (a b : Int) (hb : b ≠ 0) :
    ∃ q : Rat, evalBinOp .div (zz a) (zz b) = .ok (qq q) ∧ q * b = a := by
  have hb' : (b : Rat) ≠ 0 := by simpa using hb
  exact ⟨a / b, by simp [evalBinOp, Value.toRat?, hb'], Rat.div_mul_cancel hb'⟩

/-- `/` by zero is an error. -/
theorem div_zero (a : Int) : evalBinOp .div (zz a) (zz 0) = .error .divByZero := by
  simp [evalBinOp, Value.toRat?]

end Macaulean.M2
