import Macaulean.SumOfSquares

-- Simple univariate
example {x : Rat} : IsSumOfSquares (x ^ 2 + 1) := by m2sos

-- Multivariate
example {x y : Rat} : IsSumOfSquares (x ^ 2 + y ^ 2) := by m2sos

-- Weighted coefficients required (x² + xy + y² = (3/4)(x+y)² + (1/4)(x-y)²)
example {x y : Rat} : IsSumOfSquares (x ^ 2 + x * y + y ^ 2) := by m2sos

-- TODO: 3-variable test causes a PANIC in String.toNat! during deserialization
-- example {x y z : Rat} :
--     IsSumOfSquares ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by m2sos
