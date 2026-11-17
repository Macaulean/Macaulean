import MacauleanMathlib
open M2

K = GF(5);
R = K[x,y];
I = ideal(x^2-y,x*y-1);
f = x^3-1;
G = gb I;

#m2_export "K" as K_math
#m2_export "R" as R_math
#m2_export "I" as I_math
#m2_export "f" as f_math
#m2_membership "f" in "I" as f_in_I
#m2_groebner "G" for "I" as gb_correct

example : Lean.Grind.Field K_math.Carrier := inferInstance
example : K_math.characteristic = 5 := rfl
example : I_math.Member f_math := f_in_I

example :
    (Macaulean.Verification.Mathlib.grevlexOrder 2).IsGroebnerBasis
      (Macaulean.M2.Verification.GroebnerViews.basisMeaning gb_correct.idealEquality.basis)
      (Macaulean.M2.Verification.GroebnerViews.idealMeaning gb_correct.idealEquality.ideal) :=
  gb_correct

#m2_import I_math as "Iagain"
Gagain = gb Iagain;
#m2_groebner "Gagain" for "Iagain" as certified_again
#m2_export "Iagain" as returned
example : returned = I_math := rfl
