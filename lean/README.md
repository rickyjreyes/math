# Lean supporting formalizations

This Lean 4 and Mathlib project proves **six elementary supporting statements**. Its green check mark does **not** certify the main research manuscripts. No nonlinear PDE theorem, full spectral identity with integrals, compactness argument or S004 canonical count is claimed to be formalized here.

- [Precise theorem source](MathProofs/Elementary.lean)
- [Statement-by-statement family mapping](formalization.yaml)
- [Build workflow](../.github/workflows/lean.yml)
- [Separate WCT Lean research](https://github.com/rickyjreyes/wct-lean)

```bash
cd lean
lake update
lake exe cache get
lake build
```

Lean and Mathlib release are pinned to v4.23.0. Dependency resolution produces a lockfile, which is not yet committed.
