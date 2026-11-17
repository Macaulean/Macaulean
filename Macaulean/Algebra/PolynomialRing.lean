import Macaulean.Algebra.CoefficientField
import Macaulean.Algebra.Polynomial

/-! Ring-indexed mathematical presentations shared by rational and prime-field
worksheets. Ring identity and the ordered variable names are retained explicitly.
The current polynomial arithmetic and basis interface use grevlex throughout. -/
namespace Macaulean.Algebra

inductive MonomialOrder where
  | grevlex
  deriving Repr, DecidableEq

structure PolynomialRing where
  coefficients : CoefficientField
  id : Nat
  names : List String

/-- The bridge currently has one fixed monomial order, shared with the runtime. -/
def PolynomialRing.monomialOrder (_ : PolynomialRing) : MonomialOrder := .grevlex

instance : Inhabited PolynomialRing := ⟨⟨.rationals,0,[]⟩⟩
instance : Inhabited CoefficientField := ⟨.rationals⟩

structure RingPolynomial (ring : PolynomialRing) where
  data : Macaulean.Polynomial ring.coefficients.Carrier ring.names.length

instance : Inhabited (RingPolynomial ring) := ⟨⟨⟨[]⟩⟩⟩

def RingPolynomial.coeff (p : RingPolynomial ring) (m : Mon ring.names.length) : ring.coefficients.Carrier :=
  Polynomial.coefficient p.data m

def RingPolynomial.Equivalent (p q : RingPolynomial ring) : Prop :=
  Polynomial.Equivalent p.data q.data

structure IdealPresentation (ring : PolynomialRing) where
  generators : List (RingPolynomial ring)

instance : Inhabited (IdealPresentation ring) := ⟨⟨[]⟩⟩

def IdealPresentation.meaning (I : IdealPresentation ring) : Ideal ring.coefficients.Carrier ring.names.length :=
  Ideal.span (I.generators.map RingPolynomial.data)

def IdealPresentation.Member (I : IdealPresentation ring) (p : RingPolynomial ring) : Prop :=
  I.meaning.contains p.data

end Macaulean.Algebra
