import Macaulean.Interpreter.Check

/-! Native reference probes for the restricted QQ/grevlex polynomial fragment.
These are converted to explicit assertions as the implementation lands. -/
namespace Macaulean.M2.PolynomialReference
open Lean Elab Command

run_cmd do
  let server ← globalM2Server
  for source in #[
      "(local ax; rr:=QQ[ax]; {toString rr,toString ax,toString class ax})",
      "(ax:=7; rr:=QQ[ax]; toString rr)",
      "(ax:=null; rr:=QQ[ax]; toString rr)",
      "(rr:=QQ[bx]; ss:=QQ[bx]; {rr===ss,ring bx===ss})",
      "(rr:=QQ[cx]; cw:=cx; ss:=QQ[cw]; {toString ss,toString cw,toString cx,ring cw===rr,ring cx===ss})",
      "(rr:=QQ[]; {toString rr,numgens rr,gens rr})",
      "(rr:=QQ[dx,dx]; toString rr)",
      "(rr:=QQ[ex,ey]; {leadCoefficient(0*ex),leadMonomial(0*ex),leadTerm(0*ex),exponents(0*ex)})",
      "(rr:=QQ[fx,fy]; p:=2/3*fx^2*fy-4*fy+1; {toString class leadCoefficient p,toExternalString leadCoefficient p,toExternalString leadMonomial p,listForm p,exponents p})",
      "(rr:=QQ[gx,gy]; {(gx^2*gy)//gx,(gx+gy)//gx,lcm(gx^2*gy,gx*gy^2)})",
      "(rr:=QQ[hx]; {toString ring ideal 0,toString ring ideal {},toString ring ideal(),toString ring ideal(0*hx)})",
      "(rr:=QQ[ix,iy]; toExternalString gens gb ideal(ix^2-iy,ix*iy-1))",
      "(rr:=QQ[jx]; ss:=QQ[jx]; (gens rr)#0+jx)",
      "(rr:=QQ[kx]; {toString class rr,toString class ideal(kx),toString class gens ideal(kx),toString class gb ideal(kx)})"
    ] do
    let result : List String ← server.sendRequest "evalValue" [source]
    logInfo m!"POLYNOMIAL_REFERENCE {repr source}: {repr result}"
end Macaulean.M2.PolynomialReference
