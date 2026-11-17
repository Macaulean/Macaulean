import Macaulean.Verification.ReductionValues

/-! Shape preservation of the production primitives used for cancellation. -/
namespace Macaulean.M2.Verification.ReductionTypes
open Views Polynomials

private theorem encoded_of_dimensions (raw : Raw)
    (dimensions : ∀ t ∈ raw, t.2.length = n) :
    ∃ p : Macaulean.Polynomial Rat n, encode p = raw := by
  induction raw with
  | nil => exact ⟨⟨[]⟩,rfl⟩
  | cons t ts ih =>
    obtain ⟨p,hp⟩ := ih (fun t ht => dimensions t (List.mem_cons_of_mem _ ht))
    refine ⟨⟨⟨t.1,⟨t.2,dimensions t List.mem_cons_self⟩⟩ :: p.terms⟩,?_⟩
    change t :: encode p = t :: ts
    rw [hp]

private theorem normalized_shape (raw out : Raw)
    (success : normalized n raw = .ok out) :
    ∃ p : Macaulean.Polynomial Rat n, out = encode p := by
  unfold normalized at success
  cases hd : decode n raw with
  | error e => simp [hd, bind, Except.bind] at success
  | ok p =>
    simp only [hd, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at success
    exact ⟨KernelPolynomial.normalize p,success.symm⟩

private theorem monomial_dimension (raw : Raw) (c : Rat) (powers : List Nat)
    (success : monomial n raw = .ok (c,powers)) : powers.length = n := by
  unfold monomial at success
  cases hn : normalized n raw with
  | error e => simp [hn, bind, Except.bind] at success
  | ok terms =>
    obtain ⟨p,hp⟩ := normalized_shape raw terms hn
    simp only [hn, bind, Except.bind] at success
    cases terms with
    | nil => cases success
    | cons t ts =>
      cases ts with
      | cons u us => cases success
      | nil =>
        have ht : t = (c,powers) := Except.ok.inj success
        subst t
        exact encode_dimension p (c,powers) (by rw [← hp]; exact List.mem_cons_self)

/-- Successful narrow monomial division cannot truncate the exponent dimension. -/
theorem quotient_shape (p q out : Raw)
    (success : monomialQuotient n p q = .ok out) :
    ∃ poly : Macaulean.Polynomial Rat n, out = encode poly := by
  unfold monomialQuotient at success
  cases hp : monomial n p with
  | error e => simp [hp, bind, Except.bind] at success
  | ok a =>
    rcases a with ⟨a,x⟩
    cases hq : monomial n q with
    | error e => simp [hp, hq, bind, Except.bind] at success
    | ok b =>
      rcases b with ⟨b,y⟩
      simp only [hp, hq, bind, Except.bind] at success
      split at success
      · have shape := Except.ok.inj success
        subst out
        obtain ⟨poly,he⟩ := encoded_of_dimensions [(a/b,(x.zip y).map fun (i,j) => i-j)]
          (n := n) (by
            intro t ht
            simp only [List.mem_singleton] at ht
            subst t
            simp [List.length_zip, monomial_dimension p a x hp, monomial_dimension q b y hq])
        exact ⟨poly,he.symm⟩
      · cases success

/-- The leading coefficient is always a rational scalar, including at zero. -/
theorem lead_coefficient (p : Views.Polynomial r) :
    ∃ c : Rat, callPrimitive .leadCoefficient p.value = .ok (.qq c) := by
  refine ⟨((encode (KernelPolynomial.normalize p.data)).head?.map (·.1)).getD 0,?_⟩
  simp [callPrimitive, unaryArg, unpack, asPolynomial, normalize_bridge, liftError,
    Except.mapError, Views.Polynomial.value, Views.Polynomial.raw,
    bind, Except.bind, pure, Except.pure]

/-- A successful leading-monomial result stays in the input ring and dimension. -/
theorem lead_monomial (p : Views.Polynomial r) (v : Value)
    (success : callPrimitive .leadMonomial p.value = .ok v) :
    ∃ out : Views.Polynomial r, v = out.value := by
  simp only [callPrimitive, unaryArg, unpack, asPolynomial, normalize_bridge, liftError,
    Except.mapError, Views.Polynomial.value, Views.Polynomial.raw,
    bind, Except.bind, pure, Except.pure] at success
  cases ht : (encode (KernelPolynomial.normalize p.data)).head? with
  | none => simp [ht] at success
  | some t =>
    rcases t with ⟨c,ns⟩
    simp only [ht, Except.ok.injEq] at success
    have dimension := encode_dimension (KernelPolynomial.normalize p.data) (c,ns)
      (List.mem_of_head? ht)
    exact ⟨⟨⟨[⟨1,⟨ns,dimension⟩⟩]⟩⟩,success.symm⟩

/-- Successful primitive quotient results retain the ring identity, not merely
an isomorphic ring or a truncated list of exponents. -/
theorem monomial_quotient (p q : Views.Polynomial r) (v : Value)
    (success : callPrimitive .monomialQuotient (.sequence [p.value,q.value]) = .ok v) :
    ∃ out : Views.Polynomial r, v = out.value := by
  simp [callPrimitive, binaryArgs, unpack, common, polyRing?, Polynomials.cast,
    Views.Polynomial.value, Views.Polynomial.raw, Option.or,
    normalize_bridge, liftError, Except.mapError, bind, Except.bind,
    pure, Except.pure] at success
  cases hq : monomialQuotient r.names.length
      (encode (KernelPolynomial.normalize p.data)) (encode (KernelPolynomial.normalize q.data)) with
  | error e => simp [hq] at success
  | ok raw =>
    obtain ⟨out,he⟩ := quotient_shape _ _ raw hq
    simp only [hq, Except.ok.injEq] at success
    exact ⟨⟨out⟩,by rw [← success]; change Value.algebra (.poly r raw) = _; rw [he]; rfl⟩

/-- Rational scaling in the production evaluator always returns a same-ring
polynomial. This is the final operator in the cancellation coefficient. -/
theorem scalar_mul (c : Rat) (p : Views.Polynomial r) :
    ∃ out : Views.Polynomial r, evalBinOp .mul (.qq c) p.value = .ok out.value := by
  obtain ⟨scalar,hs⟩ := encoded_of_dimensions (constant r.names.length c)
    (n := r.names.length) (by
      intro t ht
      unfold constant at ht
      split at ht
      · cases ht
      · simp only [List.mem_singleton] at ht
        subst t
        simp)
  refine ⟨⟨KernelPolynomial.normalize (KernelPolynomial.mul
    (KernelPolynomial.normalize scalar)
    (KernelPolynomial.normalize (KernelPolynomial.normalize p.data)))⟩,?_⟩
  simp [evalBinOp, evalBinary, matrixView?, Option.isSome, common, polyRing?, Option.or, Polynomials.cast, scalar?,
    Views.Polynomial.value, Views.Polynomial.raw,
    normalize_bridge, liftError, Except.mapError, bind, Except.bind,
    pure, Except.pure, arithmetic, ← hs, mul_bridge]

private theorem index_value_member (xs : List Value) (i : Int) (v : Value)
    (success : indexValue xs i = .ok v) : v ∈ xs := by
  unfold indexValue at success
  cases hn : normalizedIndex xs.length i with
  | none => simp [hn] at success
  | some j =>
    cases hv : xs[j]? with
    | none => simp [hn,hv] at success
    | some x =>
      simp only [hn,hv,pure,Except.pure,Except.ok.injEq] at success
      subst x
      exact List.mem_of_getElem? hv

/-- Successful indexing selects an existing element, including negative indices. -/
theorem index_member (xs : List Value) (i v : Value)
    (success : evalBinOp .index (.list xs) i = .ok v) : v ∈ xs := by
  cases i <;> try (simp [evalBinOp, evalBinary] at success)
  case zz i => exact index_value_member xs i v success

open ProofJobs.RuntimeReduction in
/-- Cancellation can only select one of the supplied represented reducers. -/
theorem selected_reducer (gs : List (RepresentedReducer r n)) (i v : Value)
    (success : evalBinOp .index (.list (gs.map RepresentedReducer.value)) i = .ok v) :
    ∃ g ∈ gs, v = g.value := by
  obtain ⟨g,hg,eq⟩ := List.mem_map.mp (index_member _ i v success)
  exact ⟨g,hg,eq.symm⟩

end Macaulean.M2.Verification.ReductionTypes
