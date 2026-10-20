import Macaulean.Verification
import Macaulean.Verification.Examples.GcdTranslation.Semantics

/-!
# Existing DSL surface and the missing whole-loop/export connection

Run with `lake env lean Examples/GcdTranslation/Worksheet.lean`.
This worksheet deliberately executes only source constructs supported by the
current fork. The function below exposes ONE iteration for inspection. It is
not a substitute for the while-containing gcd function in gcd.m2.

TODO(GCD-01): after production while support, interpret the exact gcd.m2 source
through this same DSL and invoke its gcdEuclid closure.
TODO(GCD-09): expose versioned source/code/state/run/translation-Prop declarations
using LibraryCompiler/Verification snapshot machinery; a Prop is not a proof.
-/
open M2

gcdExampleAbs = (n) -> if n < 0 then -n else n;

gcdExampleStep = (a, b) -> (
    r := a % b;
    a = b;
    b = r;
    (a, b)
);

gcdExampleAbs(-1071)
gcdExampleStep(1071, 462)
gcdExampleStep(462, 147)
gcdExampleStep(147, 21)

-- These are ordinary Lean declarations from the detailed worked example.
-- The complete-source automatic exporter remains GCD-09; no command is invented.
#check Macaulean.M2.Verification.Examples.GcdTranslation.sourceText
#check Macaulean.M2.Verification.Examples.GcdTranslation.lowered
#check Macaulean.M2.Verification.Examples.GcdTranslation.result
#check Macaulean.M2.Verification.Examples.GcdTranslation.Source.Graph
#check Macaulean.M2.Verification.Examples.GcdTranslation.TODO.BodyTranslation

-- TODO: prove this proposition. Do not use native evaluation of a few arguments,
-- intent approval, or an admitted theorem as the proof of the universal claim.
-- The exact type to inhabit is:
-- Macaulean.M2.Verification.Examples.GcdTranslation.TODO.BodyTranslation
