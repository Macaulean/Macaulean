import MacauleanTest.MathematicalExport

/-! Mathematical objects and theorems survive imports without a live worksheet. -/
example : MathematicalExportTest.I_math.Member MathematicalExportTest.f_math :=
  MathematicalExportTest.membership

example : FiniteMathematicalExportTest.I_math.Member FiniteMathematicalExportTest.f_math :=
  FiniteMathematicalExportTest.membership

example : Lean.Grind.Field FiniteMathematicalExportTest.K_math.Carrier := inferInstance
