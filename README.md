# Macaulean

The project [Bridging proof and computation](https://www.renaissancephilanthropy.org/bridging-proof-and-computation-a-verified-leanmacaulay2-interface) integrates the theorem-proving capabilities of Lean with the computational power of Macaulay2.

We are working on a tactic for Lean that, on appropriate goals, calls Macaulay2 to perform a computation and then uses the result of the computation to produce a proof of the goal.

Initially, we would like the tactic to cover:
* ideal membership and
* factorisation (for integers, polynomials,...).

Once these initial goals are achieved, the infrastructure that we will develop should make it easier to add more features.

We are supported by [AI For Math fund](https://www.renaissancephilanthropy.org/ai-for-math-fund).

## How to install Macaulay2

### macOS
```
brew install Macaulay2/tap/M2
```

### Ubuntu
```
sudo add-apt-repository ppa:macaulay2/macaulay2
sudo apt install macaulay2
```

### Other systems
See the [wiki](https://github.com/Macaulay2/M2/wiki).

## Links

* [LeanM2](https://github.com/riyazahuja/lean-m2) (+ [fork](https://github.com/mattrobball/leanm2_fork))
* [Lean-Oscar](https://github.com/todbeibrot/Lean-Oscar)
* [mrdi file format](https://arxiv.org/abs/2309.00465)

##  Tests (Lean)

From command line:
```
lake build MacauleanTest
```

## Pure M2 worksheet: QQ polynomials

`import Macaulean.Interpreter.DSL` followed by `open M2` enables bare inputs such
as `R = QQ[x,y];` and `(x+y)^2`. Polynomial execution uses pure Lean, not the
external M2 server. See [the polynomial interface and verification boundary](docs/m2-polynomials.md)
and [the checked worksheet](MacauleanTest/InterpreterPolynomialsDSL.lean).

## Verified polynomial GCD

For the univariate GCD implementation, proved input-derived execution budget,
total correctness, and reusable worksheet certificates, see
[GCD verification](docs/m2-gcd.md).

## Lean definitions from M2 worksheets

Bindings written under `open M2` automatically get persistent Lean declarations.
Use `#m2_definition "f"` to find a binding's latest export, then `#print` its
Lean definition, lowered `.code`, or generated `.definition` theorem. Data exports
use native Lean types where available; function exports execute their captured
M2 program with explicit fuel and return both result and state. Reassignments get
new immutable revisions so existing Lean proofs keep their meaning.

See [the executable example](Examples/DefinitionExposure.lean) and
[definition exposure](docs/m2-definition-exposure.md) for naming, imports,
polynomial views, examples of proofs, and the current interpreter-backed boundary.
