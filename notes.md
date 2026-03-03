#   Macaulean, February 2026


## 2026-02-17 Tue - Term 2, Week 6

Can we find a computation for which grind does not finish, but a Groebner basis would make it go through?

## 2026-02-24 Tue - Term 2, Week 7

Ways of getting smaller Groebner bases/ certificates?

Certificates for being in the radical

Macaulay2 code for simplifying the benchmark test (probably some form of AI hallucination)

```macaulay2
-- Simplified form of g by introducing subexpressions

-- Declare the ring (adjust coefficient field if you want ZZ/QQ/etc.)
R = QQ[a,b,c,k,r,u,x,y,z];

-- Step 1: shift
s = u + r;

-- Step 2: repeated quadratic shifts
D = s^2 - 1;
E = s^2 - 2;

-- Linear-in-(x,y) block
L = k*x + D*y;

-- Long coefficient block
M = 2*u*k*a^2
  + u*E*a*b
  + (r*s - 2)*k*a*c
  + (2 - s*(u + 2*r))*b*c
  - u*k*c^2;

-- Core repeated expression
A = L*c^2 + M*z;

-- Other repeated factor
B = r*(s*a - c)*(s*b + k*c)*z;

-- The simplified g
g = (r*A + u*B)^4 * y^2
  - 4*r^4*k^2*z^2 * ( r^2*A^3*B + (1 - u^2 - r^2)*A^2*B^2 + u^2*A*B^3 );

-- optional: show g
g
```

---

## 2026-03-03 Tue - Term 2, Week 8

Logistics about ICMS, visits to London and Warwick, summer intern

`grind`: what kind of Groebner basis computation it does.

The subalgebra approach was not successful.
We could distill a question and ask Bhavik about kernel tricks to speed up the computation.

Example (over $\mathbb{Q}$): the singular locus of $x ^ 2 + y ^ 2 - 1 = 0$, via proving that $1$ is in the ideal.

Think about how to work over fields other than $\mathbb{Q}$.

Possibly find examples from computer vision of good, representative targets?

---
