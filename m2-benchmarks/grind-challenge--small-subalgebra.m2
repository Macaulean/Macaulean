-*
one way to rewrite g from "benchmark.m2" (using chatgpt)
*-
load "benchmark.m2"

-- apparently deleting whitespace helps chatpgt
g'noSpaces=(r*((k*x+((u+r)^2-1)*y)*c^2+(2*u*k*a^2+u*((u+r)^2-2)*a*b+(r*(u+r)-2)*k*a*c+(2-(u+r)*(u+2*r))*b*c-u*k*c^2)*z)+r*((u+r)*a-c)*((u+r)*b+k*c)*z*u)^4*y^2-r^2*2^2*k^2*z^2*(r^2*(((k*x+((u+r)^2-1)*y)*c^2+(2*u*k*a^2+u*((u+r)^2-2)*a*b+(r*(u+r)-2)*k*a*c+(2-(u+r)*(u+2*r))*b*c-u*k*c^2)*z)^3*(r*((u+r)*a-c)*((u+r)*b+k*c)*z))+(1-u^2-r^2)*(((k*x+((u+r)^2-1)*y)*c^2+(2*u*k*a^2+u*((u+r)^2-2)*a*b+(r*(u+r)-2)*k*a*c+(2-(u+r)*(u+2*r))*b*c-u*k*c^2)*z)^2*(r*((u+r)*a-c)*((u+r)*b+k*c)*z)^2)+u^2*((k*x+((u+r)^2-1)*y)*c^2+(2*u*k*a^2+u*((u+r)^2-2)*a*b+(r*(u+r)-2)*k*a*c+(2-(u+r)*(u+2*r))*b*c-u*k*c^2)*z)*(r*((u+r)*a-c)*((u+r)*b+k*c)*z)^3);

-- Macaulay2: set up the "new g'noSpaces" using the polynomial-circuit/CSE variables

t  = u + r;
t2 = t^2;
c2 = c^2;

p1 = k*x;
p2 = t2*y;
p3 = y;
P  = p1 + p2 - p3;

m1 = u*k*a^2;
m2 = u*t2*a*b;
m3 = u*a*b;
m4 = r*t*k*a*c;
m5 = k*a*c;
m6 = b*c;
m7 = t*u*b*c;
m8 = t*r*b*c;
m9 = u*k*c2;

M = 2*m1 + m2 - 2*m3 + m4 - 2*m5 + 2*m6 - m7 - 2*m8 - m9;

A1 = P*c2;
A2 = M*z;
A  = A1 + A2;

L1 = t*a - c;
L2 = t*b + k*c;
B  = L1*L2*z;
S  = r*B;

Q = A + u*B;

Tmain = (r*Q)^4 * (y^2);

C = 1 - u^2 - r^2;
Bracket = (r^2)*(A^3)*S + C*(A^2)*(S^2) + (u^2)*A*(S^3);

Coef = 4*(r^2)*(k^2)*(z^2);

g'simpleTerms = Tmain - Coef*Bracket;

subexprVars = {t, t2, c2, p1, p2, p3, P, m1, m2, m3, m4, m5, m6, m7, m8, m9, M, A1, A2, A, L1, L2, B, S, Q, Tmain, C, Bracket, Coef}

end
restart
R = ZZ/32003[u,r,k,x,y,z,a,b,c]

load "grind-challenge--small-subalgebra.m2"
assert(g'noSpaces == g)
assert(g'simpleTerms == g)

-- how about throwing all ingredients in an LLM?
assert(g % I == 0)
q = quotient(matrix{{g}},gens I);
assert(gens I * q - g == 0)
inputString = {"f1","f2","f3","f4","g","q"} / (name-> name | " = " | toString value name);
length\inputString -- hmm...

-- how about taking all subexpressions of g and 
-- looking at them modulo I?
subexprVars / (var -> first degree var  => first degree (var % I)) // VerticalList
-- hmm... there is only one place where degree drops (by 2)


