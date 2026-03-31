import MRDI.Basic
import MRDI.Poly

open Lean Json

namespace MRDI.CAS

/-! # MRDI Profile: Objects, Problems, Results

Three-layer MRDI type system for CAS communication:
- **Objects**: Mathematical structures (rings, elements, ideals). No computational parameters.
- **Problems**: Computational requests bundling objects with algorithmic parameters.
- **Results**: What the backend computed, including method details for the handler to adapt.
-/

-- ============================================================================
-- Layer 1: Mathematical Objects
-- ============================================================================

inductive CoeffDomain where
  | nat | int | rat
  | primeField (p : Nat)
  | named (name : String) (params : Json := .null)
  deriving BEq, ToJson, FromJson

structure PolyRing where
  coeff : CoeffDomain
  vars : Array String
  deriving BEq, ToJson, FromJson

structure RingElement where
  ring : PolyRing
  data : MRDI.PolynomialData
  deriving BEq, ToJson, FromJson

structure RingIdeal where
  ring : PolyRing
  generators : Array MRDI.PolynomialData
  deriving BEq, ToJson, FromJson

-- ============================================================================
-- Layer 2: CAS Problems
-- ============================================================================

inductive MonomialOrder where
  | lex | grlex | grevlex
  | named (name : String)
  deriving BEq, ToJson, FromJson

structure ReductionProblem where
  element : RingElement
  ideal : RingIdeal
  order : MonomialOrder := .grevlex
  deriving BEq, ToJson, FromJson

structure FactorizationProblem where
  n : Nat
  deriving BEq, ToJson, FromJson

-- ============================================================================
-- Layer 3: CAS Results
-- ============================================================================

structure ReductionResult where
  method : String
  quotients : Array MRDI.PolynomialData
  remainder : MRDI.PolynomialData
  deriving BEq, ToJson, FromJson

structure FactorizationResult where
  factors : Array (Nat × Nat)
  deriving BEq, ToJson, FromJson

structure GroebnerBasisProblem where
  ring : PolyRing
  generators : Array MRDI.PolynomialData
  order : MonomialOrder := .grevlex
  deriving BEq, ToJson, FromJson

structure GroebnerBasisResult where
  generators : Array MRDI.PolynomialData
  deriving BEq, ToJson, FromJson

-- ============================================================================
-- MrdiType instances (kind-level descriptors, ring context in payload)
-- ============================================================================

instance : MrdiType CoeffDomain where
  mrdiType := .string "MRDI.CAS.CoeffDomain"
  decode? := trivialDecode? (.string "MRDI.CAS.CoeffDomain")

instance : MrdiType PolyRing where
  mrdiType := .string "MRDI.CAS.PolyRing"
  decode? := trivialDecode? (.string "MRDI.CAS.PolyRing")

instance : MrdiType RingElement where
  mrdiType := .string "ring_element"
  decode? := trivialDecode? (.string "ring_element")

instance : MrdiType RingIdeal where
  mrdiType := .string "ring_ideal"
  decode? := trivialDecode? (.string "ring_ideal")

instance : MrdiType MonomialOrder where
  mrdiType := .string "MRDI.CAS.MonomialOrder"
  decode? := trivialDecode? (.string "MRDI.CAS.MonomialOrder")

instance : MrdiType ReductionProblem where
  mrdiType := .string "reduction_problem"
  decode? := trivialDecode? (.string "reduction_problem")

instance : MrdiType FactorizationProblem where
  mrdiType := .string "factorization_problem"
  decode? := trivialDecode? (.string "factorization_problem")

instance : MrdiType ReductionResult where
  mrdiType := .string "reduction_result"
  decode? := trivialDecode? (.string "reduction_result")

instance : MrdiType FactorizationResult where
  mrdiType := .string "factorization_result"
  decode? := trivialDecode? (.string "factorization_result")

instance : MrdiType GroebnerBasisProblem where
  mrdiType := .string "groebner_basis_problem"
  decode? := trivialDecode? (.string "groebner_basis_problem")

instance : MrdiType GroebnerBasisResult where
  mrdiType := .string "groebner_basis_result"
  decode? := trivialDecode? (.string "groebner_basis_result")

end MRDI.CAS
