-- Monic GCD of two polynomials in the same univariate QQ ring.
-- These functions execute in the ordinary Lean M2 evaluator.
-- Use normalForm: polynomial % only supports single-term divisors.

m2gcdLoop = (f,g) ->
    if g == 0 then (
        if f == 0 then f else f/(leadCoefficient f)) else
    m2gcdLoop(g,normalForm(f,{g}));

gcd = input -> (
    data := m2GCDInputs input;
    m2gcdLoop(data#0,data#1));
