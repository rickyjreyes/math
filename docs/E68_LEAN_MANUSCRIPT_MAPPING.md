# E68: exact manuscript-to-Lean proof mapping

**Issue:** [#41](https://github.com/rickyjreyes/math/issues/41) · **PR:** [#50](https://github.com/rickyjreyes/math/pull/50).

Pinned versions: Lean 4.23.0, Mathlib 4.23.0. The baseline `E68Scaling` and `E68CriticalGradient` passed [focused CI](https://github.com/rickyjreyes/math/actions/runs/40632112750) and supporting CI at commit `6df2eab1`. The smooth-profile and weak-H1 modules passed full Lean CI at d083c2f2. The strict n=1 energy contradiction is full-project Lean verified. Exact n>2 smooth localized-gradient-energy contradiction passed full project CI at `087e05f8` on October 29, 2026.

| Manuscript obligation | Lean mapping | Scope / blocker |
|---|---|---|
| Exact dimensional classification: n=2 | `two_dimensional_local_gradient_energy`; newly added `WeakH1Field` with distributional test identity and `weakH1_two_dimensional_local_energy` | Strong and distributional weak-gradient modules pass full pinned Lean CI. Direct equivalence with a chosen Mathlib Sobolev-space representation remains unproved. |
| n=1 explicit `C_c^∞((-1,1))` field | `compactOneDim`, `compactOneDim_smooth`, `compactOneDim_hasCompactSupport`, `compactOneDim_support_in_unit_interval`, `compactOneDim_nonconstant` | **PROVED and verified**: positive actual whole-line squared derivative energy, support containment, exact ball/global integral equality at R≥1 and uniform C/R contradiction in `E68OneDimEnergy.lean`. |
| n>2 smooth concentration, every C>0 | `compactProfile`, `smoothConcentration`, `smoothConcentration_smooth`, `smoothConcentration_hasCompactSupport`, `smooth_concentration_scaling_obstruction` | **PROVED and verified**: `E68ScaledGradient.lean` gives actual Fréchet-gradient integral scaling, normalized R-independent energy and R² mass. `E68SmoothCounterexample.lean` proves support inside B_R, ball/full-space energy equality, and `no_uniform_E68_for_smooth_concentrations` for every n>2. This covers the smooth proposition only. |
| n>2 single singular H¹ field | No faithful Lean declaration yet | Need radial cutoff, Riesz power weak-gradient identification across zero, polar integrals, fixed-field small-ball divergence |
| Corrected E68′ | `local_critical_gradient_norm`, `euclidean_ball_volume_scaling` | Genuine measure/Lp results checked; exact real Bochner-integral inequality with `omega_n^{1-2/n} R^{n-2}` remains |
| Conditional admissible-class corollary | No complete Lean result yet | Need combine corrected E68′ with an **independently assumed** uniform Lⁿ/H¹ estimate; never infer this from unrestricted H¹ |
| H², n=3,4 | No complete Lean result yet | Need genuine whole-space Sobolev embedding, interpolation in n=3 and L⁴ bound in n=4, with exact norms |
| H², n>4 counterexample | `high_dimensional_H2_scaling_obstruction` | Algebraic obstruction checked; construct actual smooth rescaled H² fields and prove all derivative integrals |

**Dimension status:** n=2 uniform estimate and n=1 and n>2 **smooth actual-function** failures are now Lean verified. The n>2 stronger fixed singular weak-H¹ counterexample, corrected E68′, H² consequences and the exact full manuscript iff classification remain open. `main_theorem_formalized` must stay **false**. No discrete or numerical surrogate qualifies.

## 2026-10-28 execution checkpoint

- Exact C-infinity compact bump, its nonzero derivative, integrable and strictly positive whole-line squared derivative energy: **full-project Lean PASS** at `d083c2f2` ([CI](https://github.com/rickyjreyes/math/actions/runs/40720089883)).
- Genuine support containment, equality of ball and whole-line derivative integrals for radius at least one, and impossibility of a single uniform `C/R` bound: **focused Lean module PASS** at `146c4d9a`; full build pending ([CI](https://github.com/rickyjreyes/math/actions/runs/40721010142)).
- Open: nontrivial n>2 continuum concentration energy identities; singular H1 profile; complete dimension iff; corrected E68-prime in real energy form; H2 embeddings and obstructions. `main_theorem_formalized` remains **false**.

## October 29, 2026: exact smooth n>2 counterexample now verified

**Pinned PR head:** `087e05f8a3083fcb2d7564d4a3bc7e30a79eee8d`.

All five workflows passed **at this exact SHA**:
- [E68 issue-specific CI, including full root project build, #40933787546](https://github.com/rickyjreyes/math/actions/runs/40933787546)
- [Full supporting-theorems CI #40933787521](https://github.com/rickyjreyes/math/actions/runs/40933787521)
- [M6B root regression #40933787523](https://github.com/rickyjreyes/math/actions/runs/40933787523)
- [F09 source verification #40933787515](https://github.com/rickyjreyes/math/actions/runs/40933787515)
- [PDF publication workflow #40933787542](https://github.com/rickyjreyes/math/actions/runs/40933787542)

New declarations in `E68SmoothCounterexample.lean`:
- `smoothConcentration_tsupport_inside_ball`
- `smoothConcentration_gradient_support_inside_ball`
- `smoothConcentration_ball_energy_eq_global`
- **`no_uniform_E68_for_smooth_concentrations`**.

The latter is a *literal* continuum Lebesgue ball-integral counterexample for the specified compactly supported smooth concentration family in every n>2, not just the earlier algebraic scaling contradiction. This discharges the paper's smooth-concentration proposition. The fixed singular weak-H¹ single-field counterexample and the corrected E68′/H² statements are separate remaining obligations.

**Do not mark** `main_theorem_formalized: true` or close issue #41 until those distinct missing proofs are completed and the original main theorem with its full quantifiers is kernel-verified.
