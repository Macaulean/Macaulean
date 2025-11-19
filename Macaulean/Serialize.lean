import MRDI.Poly

open MRDI

namespace Lean.Grind.CommRing

def Mon.serialize : Mon → Monomial
  | .unit => #[]
  | .mult p m => m.serialize |>.push p

def Poly.serialize : Poly → PolynomialData
  | .num k => #[⟨k, #[]⟩]
  | .add k m p => p.serialize.push ⟨k, m.serialize⟩

end Lean.Grind.CommRing
