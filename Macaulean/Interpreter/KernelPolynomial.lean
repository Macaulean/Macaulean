import Macaulean.Polynomial.Basic

/-!
# Kernel-evaluable arithmetic in Macaulean's polynomial representation

The current backend normalizer uses a sorting implementation that does not reduce
on this toolchain's kernel path. These structural list operations retain the same
coefficient/monomial representation and grevlex comparator. They do not use a
foreign engine, an opaque evaluator, or native_decide.
-/
namespace Macaulean.M2.KernelPolynomial

/-- Insert into decreasing grevlex order, combining equal monomials. -/
def insert (t : Macaulean.PolyTerm Rat n) :
    List (Macaulean.PolyTerm Rat n) → List (Macaulean.PolyTerm Rat n)
  | [] => if t.coefficient = 0 then [] else [t]
  | u :: us =>
    match t.monomial.grevlex u.monomial with
    | .gt => if t.coefficient = 0 then u :: us else t :: u :: us
    | .eq =>
      let c := t.coefficient + u.coefficient
      if c = 0 then us else ⟨c,u.monomial⟩ :: us
    | .lt => u :: insert t us

def normalize (p : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  ⟨p.terms.foldl (fun ts t => insert t ts) []⟩

def add (p q : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  normalize ⟨p.terms ++ q.terms⟩
def sub (p q : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  add p q.neg

def mul (p q : Macaulean.Polynomial Rat n) : Macaulean.Polynomial Rat n :=
  normalize ⟨p.terms.flatMap fun t =>
    Macaulean.Polynomial.mulMonTerms t.coefficient t.monomial q.terms⟩

def pow (p : Macaulean.Polynomial Rat n) : Nat → Macaulean.Polynomial Rat n
  | 0 => ⟨[⟨1,Macaulean.Mon.unit⟩]⟩
  | k + 1 => mul p (pow p k)
end Macaulean.M2.KernelPolynomial
