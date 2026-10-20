-- Euclidean algorithm: source artifact for the translation-preservation example.
-- Macaulean defines its own semantics. Native M2 is not the proof specification.
-- TODO(GCD-01): wire while/do through the existing parser, Term, Lexical.Code,
-- runtime, DSL lowering, source rendering, and verification indexing.
-- The baseline does NOT parse this complete file yet. Do not replace this loop
-- by a recursive helper or a built-in gcd and call that source preservation.
-- TODO(GCD-02): use the explicit source-defined abs helper in the example's
-- isolated environment; do not silently assume an external CAS implementation.

abs = (n) -> if n < 0 then -n else n;

gcdEuclid = (a, b) -> (
    a = abs a;
    b = abs b;

    while b != 0 do (
        r := a % b;
        a = b;
        b = r
    );

    a
);

-- Invocation fixtures belong in separate fresh sessions from the declaration:
-- gcdEuclid(1071, 462)    -- 21
-- gcdEuclid(-1071, 462)   -- 21
-- gcdEuclid(0, 0)        -- 0
-- These comments are expected outputs, not a report of native-M2 execution.
