-- Define the ring with entries of the Essential Matrix E (e11-e33)
FF = QQ
R = FF[e11,e12,e13,e21,e22,e23,e31,e32,e33];
E = matrix {{e11,e12,e13},{e21,e22,e23},{e31,e32,e33}};

-- Demazure cubics: 9 cubic constraints from the condition that E has rank 2
EEt = E * transpose(E);
traceEEt = EEt_(0,0) + EEt_(1,1) + EEt_(2,2);
DemazureConstraints = flatten entries (2 * EEt * E - traceEEt * E);

-- The determinant constraint: det(E) = 0
detConstraint = det E;

-- Combine all constraints into an ideal
I = ideal(DemazureConstraints | {detConstraint});

-- (This is not part of the benchmark, but we can generate an instance of this 
-- multiprojective problem with input from (P^2)^10, i.e., 5 point correspondences
--)
-- Generate 5 random point correspondences (x_i, x_i')
-- Each pair consists of 3D unit vectors (homogeneous coordinates)
randomPoints = n -> apply(n, i -> (
    {random FF, random FF, 1}, -- x_i
    {random FF, random FF, 1}  -- x_i'
));
pts = randomPoints 5; 

-- Define the 5 epipolar constraints: x_i^T E x_i' = 0
epipolarConstraints = apply(pts, p -> (
    v1 = matrix {p#0};
    v2 = transpose matrix {p#1};
    (v1 * E * v2)_{0,0}
));

-- Add the epipolar constraints (5 linear forms) to the ideal
J = I + ideal epipolarConstraints 

end
restart
load "5pts-relative-pose.m2"
dim I
degree I
G = gb(I,ChangeMatrix=>true);
change = getChangeMatrix G
assert(gens G == gens I * change)
-- BENCHMARK: prove that I has degree 10
-- step 1: show that G is a Groebner basis of I