# FiniteLean vendored source closure

This directory contains the shared-library source modules listed in the enclosing package's `LIBRARY-MODULES.txt`. The snapshot is identified by the enclosing `SHA256SUMS` and its dependency revisions by `UPSTREAM-PINS.json`; it is built through the enclosing `lean/` package.

The entropy results in this snapshot are finite dimensional. `QIT.mlog`, `QIT.relEnt` and `Houghton.vN` use natural logarithms (nats). The relative-entropy conjugation, joint-convexity and partial-trace theorems have the positive-definiteness assumptions shown by their types; extended-valued relative entropy for arbitrary singular states is outside this snapshot. Strong subadditivity is proved for all finite Hermitian positive-semidefinite trace-one density matrices. `QIT.integralRep` proves the `IntegralRep` interface; `relEnt_jointlyConvex_of` retains that interface as an explicit, internally dischargeable premise. The two compatibility bridges preserve the retained finite-matrix definitions exactly. No infinite-dimensional operator-entropy bridge is claimed.

Run these commands from the enclosing `lean/` directory, with Lean 4.35.0 on PATH:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M6144 Audit.lean
```

See `lean/README.md` from the repository root for the checked scope and the trust base, and `lean/AXIOMS.txt` for the axiom output.
