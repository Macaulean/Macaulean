import Macaulean.Interpreter.Check
namespace Macaulean.M2.PolynomialAliasReference
open Lean Elab Command
run_cmd do
  for source in #[
    "(ar:=QQ[axProbe];ap:=axProbe;{baseName ap==symbol axProbe,baseName ap==symbol ap})",
    "(ar:=QQ[axProbe];ap:=axProbe;as:=QQ[ap];{ring ap==as,ring axProbe==ar,baseName(as_0)==symbol ap,baseName(as_0)==symbol axProbe})",
    "(ar:=QQ[axProbe];ap:=axProbe;ls:={ap};as:=QQ[ls];{ring ap==as,ring axProbe==as,baseName(as_0)==symbol ap,baseName(as_0)==symbol axProbe})",
    "(ar:=QQ[axProbe];ap:=axProbe;as:=QQ[(ap)];{ring ap==as,ring axProbe==as,baseName(as_0)==symbol ap,baseName(as_0)==symbol axProbe})",
    "(ar:=QQ[axProbe];ap:=axProbe;as:=QQ[axProbe+0];{ring ap==as,ring axProbe==as})",
    "(ar:=QQ[axProbe];ap:=axProbe+1;as:=QQ[ap];numgens as)",
    "(ar:=QQ[axProbe];apGlobalProbe=axProbe;as:=QQ[apGlobalProbe];{ring apGlobalProbe==as,ring axProbe==ar,baseName(as_0)==symbol apGlobalProbe})"
  ] do
    match ← queryM2 source with
    | .error e => throwError "native alias probe transport failed: {e}"
    | .ok .error => logInfo m!"ALIAS_PROBE {source}: NATIVE_ERROR"
    | .ok (.ok v) => logInfo m!"ALIAS_PROBE {source}: {v.toM2String}"
end Macaulean.M2.PolynomialAliasReference
