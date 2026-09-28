# Linux proof-worker prerequisites

The proof runner requires Linux, bubblewrap, Python 3 and the pinned Lean
installation. The namespace sandbox is mandatory. No failure path runs candidate
tactics directly on the host or switches to the host network.

On Debian/Ubuntu:

```sh
sudo apt-get update
sudo apt-get install -y bubblewrap python3
```

## Ubuntu's AppArmor user-namespace restriction

Ubuntu 24.04 and later can allow creating a user namespace while denying the
capabilities needed to configure it. The exact observed CI failure was:

```text
bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted
```

On a dedicated development VM/worker, install and load the distribution's
bubblewrap-specific profile. This is a host-administration step; the proof runner
never does it automatically or invokes sudo.

```sh
sudo apt-get install -y apparmor-profiles apparmor-utils
sudo install -m 0644 \
  /usr/share/apparmor/extra-profiles/bwrap-userns-restrict \
  /etc/apparmor.d/bwrap-userns-restrict
sudo apparmor_parser -r /etc/apparmor.d/bwrap-userns-restrict
```

The global `kernel.apparmor_restrict_unprivileged_userns` setting stays enabled.
CI records its value before and after and requires equality. The upstream
profile allows the sandbox helper to construct namespaces and restricts the
capabilities of the program it launches. Review the installed distribution
profile before applying it to a shared workstation: it affects other consumers
of `/usr/bin/bwrap`, not just Macaulean.

References: [Ubuntu's security documentation](https://documentation.ubuntu.com/security/security-features/privilege-restriction/apparmor/)
and [the upstream AppArmor profile](https://gitlab.com/apparmor/apparmor/-/blob/master/profiles/apparmor/profiles/extras/bwrap-userns-restrict).
Use your distribution's installed profile, not an unpinned download copied from
that moving upstream branch.

Then run:

```sh
bash scripts/m2_proof_smoke.sh
```

A missing profile, unavailable namespace support, compiler failure, timeout, or
missing output must leave the smoke test red. Do not disable AppArmor globally,
add `--share-net`, run the candidate as root, or remove sandbox requirements to
obtain a green result.

## Lean thread stacks and virtual memory

The pinned Lean 4.33.1 runtime normally reserves 1 GiB per runtime thread. The
worker explicitly sets `LEAN_STACK_SIZE_KB=65536`, `LEAN_NUM_THREADS=1`, and the
shell options `-j1 -s65536`. The shell's own thread setting matters; changing
only the environment variable did not fix the original startup failure.

The default `RLIMIT_AS` budget is **16 GiB of virtual address space per process**.
That includes file-backed `.olean` and `.ir` mappings, not just resident heap
memory. The former 4 GiB cap prevented the complete Lean environment from
loading; Lean reported a failed `.ir` read after exhausting mapping/allocation
space. This is not a claim that a proof needs 16 GiB of physical RAM.

The runner accepts `--memory-mib` to set another finite virtual-space budget.
A too-small budget is a failed attempt, never accepted evidence. CPU, wall-time,
file-size and process limits remain enabled. These are per-process resource
limits, not an aggregate cgroup quota for a shared host; use a dedicated worker
or VM for untrusted candidates.

Worker failures identify the retained stderr path. The smoke script also prints
bounded tails of all worker diagnostics on failure; complete stdout, stderr,
exit status and timeout status remain in `ci-evidence/`.

## macOS and containers

The editor/source review can be used in the normal Lean environment, but this
worker implementation uses Linux namespaces. Use a Linux VM or remote Linux
host for the full pipeline. No native macOS worker is claimed. Container runtimes
may impose additional namespace restrictions; an arbitrary Docker configuration
is not asserted to work. The native CI gate uses a Linux VM, not a nested Docker
sandbox.

The [human/agent walkthrough](m2-proof-smoke.md) describes approval, candidate
construction, retained diagnostics and independent editor replay.
