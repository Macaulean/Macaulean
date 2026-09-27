import Macaulean.Polynomial.Basic

/-!
Kernel-evaluable arithmetic in the existing polynomial representation.
The backend's newer mergeTerms/mulTerms definitions depend computationally on
Classical.choice. Use first-order list operations followed by its normalizer
instead; do not replace kernel checking by native_decide.
-/
namespace Macaulean.M2.KernelPolynomial

def add (p q : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  (⟨p.terms ++ q.terms⟩ : Macaulean.Polynomial Rat n).normalize

def sub (p q : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  add p q.neg

def mul (p q : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  (⟨p.terms.flatMap fun t =>
    Macaulean.Polynomial.mulMonTerms t.coefficient t.monomial q.terms⟩ :
    Macaulean.Polynomial Rat n).normalize

def pow (p : Macaulean.Polynomial Rat n) : Nat → Macaulean.Polynomial Rat n
  | 0 => ⟨[⟨1, Macaulean.Mon.unit⟩]⟩
  | k + 1 => mul p (pow p k)

end Macaulean.M2.KernelPolynomial
