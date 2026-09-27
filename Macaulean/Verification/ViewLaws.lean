import Macaulean.Verification.Views

/-!
# Lossless coefficient-row views

These are representation laws, not algorithm specifications. A typed row has
exactly its advertised dimension; converting it to a supported M2 collection and
reading it back neither truncates entries nor changes polynomial data. No
normalization, inferred scalar promotion, or foreign ring identification is used.
-/
namespace Macaulean.M2.Verification.Views

/-- A lossless M2 list presentation of a dimension-indexed polynomial row. -/
def Row.value (row : Row r n) : Value := .list (row.values.map Polynomial.value)

/-- Preserve M2's distinct sequence class rather than treating it as a list. -/
def Row.sequenceValue (row : Row r n) : Value := .sequence (row.values.map Polynomial.value)

theorem readPolynomials_roundtrip (ps : List (Polynomial r)) :
    readPolynomials r (ps.map Polynomial.value) = .ok ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [readPolynomials, polynomial_roundtrip, ih]

theorem row_roundtrip (row : Row r n) :
    readRow r n row.value = .ok row := by
  cases row with
  | mk values h =>
    simp [Row.value, readRow, readPolynomials_roundtrip, h]

theorem row_sequence_roundtrip (row : Row r n) :
    readRow r n row.sequenceValue = .ok row := by
  cases row with
  | mk values h =>
    simp [Row.sequenceValue, readRow, readPolynomials_roundtrip, h]

theorem row_wrong_length (row : Row r n) (m : Nat) (h : n ≠ m) :
    readRow r m row.value = .error "coefficient-row view: wrong length" := by
  simp [Row.value, readRow, readPolynomials_roundtrip, row.size_eq, h]

theorem row_sequence_wrong_length (row : Row r n) (m : Nat) (h : n ≠ m) :
    readRow r m row.sequenceValue = .error "coefficient-row view: wrong length" := by
  simp [Row.sequenceValue, readRow, readPolynomials_roundtrip, row.size_eq, h]

theorem polynomial_value_injective (p q : Polynomial r) (h : p.value = q.value) : p = q := by
  have same := congrArg (readPolynomial r) h
  simpa only [polynomial_roundtrip, Except.ok.injEq] using same

theorem row_value_injective (a b : Row r n) (h : a.value = b.value) : a = b := by
  have same := congrArg (readRow r n) h
  simpa only [row_roundtrip, Except.ok.injEq] using same

theorem row_sequence_value_injective (a b : Row r n)
    (h : a.sequenceValue = b.sequenceValue) : a = b := by
  have same := congrArg (readRow r n) h
  simpa only [row_sequence_roundtrip, Except.ok.injEq] using same

end Macaulean.M2.Verification.Views
