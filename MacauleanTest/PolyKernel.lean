/-
  Kernel-evaluation smoke tests for `Macaulean.Polynomial`.

  `mergeTerms` is fuel-indexed structural recursion precisely so that the
  *kernel* can unfold it; `decide +kernel` on the polynomial operations is
  therefore the property this file pins down.  (With the previous
  `WellFounded.fix` merge every one of these goals got stuck.)
-/
import Macaulean.Polynomial.Lemmas

namespace MacauleanTest.PolyKernel

open Macaulean Macaulean.Polynomial

set_option maxRecDepth 10000

def x : Mon 3 := Mon.ofPowersN 3 [1, 0, 0]
def y : Mon 3 := Mon.ofPowersN 3 [0, 1, 0]
def z : Mon 3 := Mon.ofPowersN 3 [0, 0, 1]

/-- `2x + 3y + 5z`, in grevlex-descending order. -/
def p : Polynomial Int 3 := ⟨[⟨2, x⟩, ⟨3, y⟩, ⟨5, z⟩]⟩

/-- `x - y`. -/
def q : Polynomial Int 3 := ⟨[⟨1, x⟩, ⟨-1, y⟩]⟩

theorem mul_len : (p.mul q).terms.length = 5 := by decide +kernel
theorem add_len : (p.add p).terms.length = 3 := by decide +kernel
/-- `sub` cancels the coefficients but leaves the terms; stripping the zeros is
`removeZeros`' job, and the reflective checker does it once, at the end. -/
theorem sub_self : (p.sub p).terms.length = 3 := by decide +kernel
theorem sub_self_zero : removeZeros (p.sub p).terms = [] := by decide +kernel
theorem neg_len : p.neg.terms.length = 3 := by decide +kernel
theorem smul_len : ((3 : Int) • p).terms.length = 3 := by decide +kernel
theorem pow_len : (p.pow 4).terms.length = 15 := by decide +kernel
theorem beq_refl : (p.mul q == p.mul q) = true := by decide +kernel

/-- Multiplication is commutative on the nose in this normal form. -/
theorem mul_comm_beq : (p.mul q == q.mul p) = true := by decide +kernel

-- All of the above go through the kernel with no extra axioms.
#print axioms mul_len
#print axioms pow_len
#print axioms mul_comm_beq

end MacauleanTest.PolyKernel
