import Macaulean.Verification.Views

/-!
# A small explicit specification vocabulary

Every schema is partial correctness on successful returns. These definitions are
proof targets, never axioms. Their deterministic descriptions enumerate both the
claims and the missing claims. Adding a schema is a semantic change that must be
reviewed; a human approval selects a schema, not its truth.
-/
namespace Macaulean.M2.Verification.Contracts
open Views Polynomials

inductive Kind where
  | polynomialIdentity | orderedRemainder | linearCombination
  deriving Repr, DecidableEq, Inhabited

def Kind.name : Kind → String
  | .polynomialIdentity => "polynomialIdentity"
  | .orderedRemainder => "orderedRemainder"
  | .linearCombination => "linearCombination"

def Kind.parse : String → Option Kind
  | "polynomialIdentity" => some .polynomialIdentity
  | "orderedRemainder" => some .orderedRemainder
  | "linearCombination" => some .linearCombination
  | _ => none

def all : List Kind := [.polynomialIdentity, .orderedRemainder, .linearCombination]
def version : String := "macaulean.intent.v1"

/-- Domain and postcondition share the same checked input views. -/
def Domain : Kind → Value → Prop
  | .polynomialIdentity, arg => ∃ r p, readPolynomial r arg = .ok p
  | .orderedRemainder, arg => ∃ r f generators fv gv,
      arg = .sequence [fv,gv] ∧ readPolynomial r fv = .ok f ∧
      readRow r generators.length gv = .ok (Row.mk generators rfl)
  | .linearCombination, arg => ∃ r n, ∃ (row gs : Row r n), ∃ rv gv,
      arg = .sequence [rv,gv] ∧ readRow r n rv = .ok row ∧ readRow r n gv = .ok gs

/-- Equality of polynomials, not equality of their chosen sparse representations. -/
def IdentityPost (arg result : Value) : Prop := ∃ r p q,
  readPolynomial r arg = .ok p ∧ readPolynomial r result = .ok q ∧ Equivalent p q

/-- No uniqueness or independence of generator order is asserted. -/
def RemainderPost (arg result : Value) : Prop := ∃ r f remainder generators fv gv,
  arg = .sequence [fv,gv] ∧ readPolynomial r fv = .ok f ∧
  readRow r generators.length gv = .ok (Row.mk generators rfl) ∧
  readPolynomial r result = .ok remainder ∧ OrderedRemainder f remainder generators

def CombinationPost (arg result : Value) : Prop := ∃ r n, ∃ (row gs : Row r n), ∃ p rv gv,
  arg = .sequence [rv,gv] ∧ readRow r n rv = .ok row ∧ readRow r n gv = .ok gs ∧
  readPolynomial r result = .ok p ∧
  ∀ powers, p.coeff powers = linearCoefficient row.values gs.values powers

def Post : Kind → Value → Value → Prop
  | .polynomialIdentity => IdentityPost
  | .orderedRemainder => RemainderPost
  | .linearCombination => CombinationPost

/-- Contract at an explicitly identified lexical state. Fuel exhaustion and other
errors are not successful returns; this is NOT a total-correctness theorem. -/
def Statement (kind : Kind) (fn : Value) (state : Runtime.State) : Prop :=
  ∀ arg, Domain kind arg → ∀ fuel result after,
    Runtime.call fuel fn arg state = .ok (result,after) → Post kind arg result

structure Description where
  title : String
  inputs : List String
  guarantees : List String
  limitations : List String
  formal : String
  deriving Repr, Inhabited

def describe (kind : Kind) : Description := {
  title := match kind with
    | .polynomialIdentity => "Polynomial identity"
    | .orderedRemainder => "Polynomial remainder (no canonical choice)"
    | .linearCombination => "Coefficient-row linear combination"
  inputs := match kind with
    | .polynomialIdentity => ["One polynomial p in a fixed runtime QQ polynomial ring R."]
    | .orderedRemainder => ["Arguments (f, G): a polynomial and a list, sequence or generator row.",
        "Every generator belongs to the same runtime QQ polynomial ring as f.",
        "The monomial order is the polynomial layer's fixed grevlex order."]
    | .linearCombination => ["Arguments (a, G): coefficient and generator rows of equal length.",
        "Every entry is a polynomial in the same runtime QQ polynomial ring.",
        "Scalar entries must be explicitly promoted to that ring."]
  guarantees := match kind with
    | .polynomialIdentity => ["On successful return: the result is in R and has exactly the coefficients of p."]
    | .orderedRemainder => ["On successful return r: r belongs to the same ring as f.",
        "f - r is a polynomial linear combination of the supplied generators.",
        "No nonzero term of r is divisible by a leading monomial of a nonzero generator."]
    | .linearCombination => ["On successful return p: p is in the common ring.",
        "p equals the sum of a_i * G_i, coefficient by coefficient; no row entries are discarded."]
  limitations := ["Partial correctness only: termination and error-freedom are not claimed.",
    "No heap/frame/effect-preservation property is claimed.",
    "No reduction strategy, unique remainder or order independence is claimed.",
    "Intent approval is not a proof, an axiom, or authentication of a person's identity."]
  formal := "Macaulean.M2.Verification.Contracts.Statement " ++ kind.name ++ " fn state"
}

def render (kind : Kind) : String :=
  let d := describe kind
  d.title ++ "\nSchema: " ++ version ++ "\nInputs\n" ++ "\n".intercalate d.inputs ++
  "\nOn successful return\n" ++ "\n".intercalate d.guarantees ++
  "\nNot claimed\n" ++ "\n".intercalate d.limitations ++ "\nFormal target: " ++ d.formal

theorem successful_return (kind : Kind) (fn : Value) (s : Runtime.State)
    (h : Statement kind fn s) (arg : Value) (hd : Domain kind arg)
    (fuel : Nat) (result : Value) (after : Runtime.State)
    (he : Runtime.call fuel fn arg s = .ok (result,after)) : Post kind arg result :=
  h arg hd fuel result after he

theorem identity_post_same_ring (arg result : Value) (h : IdentityPost arg result) :
    ∃ r p q, readPolynomial r arg = .ok p ∧ readPolynomial r result = .ok q := by
  obtain ⟨r,p,q,hp,hq,_⟩ := h
  exact ⟨r,p,q,hp,hq⟩

end Macaulean.M2.Verification.Contracts
