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

## Loading the JSONRPC/MRDI packages (Macaulay2)

Suppose you have cloned the Macaulean repository to `/path/to/Macaulean`.
### Load packages

```m2
path = append(path, "/path/to/Macaulean/m2")
needsPackage "JSONRPC"
needsPackage "MRDI"
```

### Test packages

```m2
check "JSONRPC"
check "MRDI"
```

##  Tests (Lean)

From command line:
```
lake build MacauleanTest
```
