import Macaulean.Verification

namespace ExposureWithVerification
open M2
keep = p -> p;
#m2_contract "keep" polynomialIdentity
example : (M2Generated.keep 32 (.zz 17)).map Prod.fst = .ok (.zz 17) := by decide
set_option m2.intent.enabled false in
other = x -> x+1;
example : (M2Generated.other 32 (.zz 17)).map Prod.fst = .ok (.zz 18) := by decide
run_cmd do
  unless (← Macaulean.M2.DSL.getSession).nextInput == 3 do
    throwError "the indexed frontend executed an input more than once"
  unless (← Lean.findDeclarationRanges? ``M2Generated.keep).isSome do
    throwError "generated definition lacks a source location"
end ExposureWithVerification
