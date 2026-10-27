import Lean

/-- Lemmas that turn production M2 operations on represented values into ordinary
mathematics. `m2_unfold` simplifies with this set; tag lemmas for new value views
(e.g. polynomials) with `@[m2_simp]`. -/
register_simp_attr m2_simp
