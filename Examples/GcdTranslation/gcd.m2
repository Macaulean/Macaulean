-- Source artifact for Macaulean's designed language, not a native-D contract.
-- DESIGN-PARSE: parse these exact bytes through the Word/Profile frontend.
-- The current executable example starts from the explicitly labelled Surface
-- fixture, not from a claim that the old DSL parser recognizes this language.

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

-- Invocation tests pass exact integer inputs independently of source parsing:
-- gcdEuclid(1071, 462)    -- expected 21
-- gcdEuclid(-1071, 462)   -- expected 21
-- gcdEuclid(0, 0)        -- expected 0
-- No native M2 run is asserted by these comments.
