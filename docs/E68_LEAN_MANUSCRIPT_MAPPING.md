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

## Full E68 claim inventory, re-audited after merging current main

**Formalization policy:** A checked theorem covering smooth functions is not a theorem covering all Sobolev equivalence classes. A checked extended-Lp seminorm estimate is not by itself the displayed real-valued corrected energy integral. The manuscript is unchanged.

| Manuscript location and assertion | Exact mathematical scope | Lean declaration / imported module | Verification / missing work |
|---|---|---|---|
| Section 1, E68 definition and inhomogeneous H1 norm | Exists finite C_n, for **every** ψ ∈ H¹(Rⁿ), every R>0 and every center x0, integral over B_R(x0) ≤ C_n R^(n−2) (||ψ||₂²+||∇ψ||₂²) | No single full-domain declaration | **OPEN:** full Sobolev class and actual weak-gradient quotient |
| Theorem 1, iff n=2 | For every integer n≥1, uniform E68(n) iff n=2 | `ReyesMath.E68.smoothE68_iff_two` in `MathProofs/E68SmoothClassification.lean` only for the C∞ compact real subclass, n≥2 | **OPEN** for full H¹ equivalence classes and n=1 as a unified iff |
| Theorem 1, n=2, C₂=1 | Every center, every R>0, every ψ∈H¹(R²); energy on B_R ≤ whole-space H¹ energy | `ReyesMath.E68.weakH1_two_dimensional_local_energy` in `MathProofs/E68WeakH1.lean`, and `ReyesMath.E68.two_dimensional_local_gradient_energy` in `MathProofs/E68Scaling.lean` | Existing weak-gradient and strong-derivative inequalities checked; representation bridge to canonical H¹ remains **OPEN** |
| Theorem 1, n=1 nonconstant compact bump | A specific ψ∈C_c∞((-1,1)), derivative energy A>0, ball integral A for all R≥1, no C/R bound | `ReyesMath.E68.compactOneDim_deriv_energy_positive`, `compactOneDim_deriv_ball_energy_eq_global`, `compactOneDim_forbids_uniform_inverse_radius_energy` in `MathProofs/E68OneDimEnergy.lean` | Existing actual-integral claims **VERIFIED** on earlier PR head |
| Theorem 1, n=1 all smooth fields | No single constant controls all C_c∞(R) fields, all centers and radii | `ReyesMath.E68.no_uniform_E68_on_smooth_fields_one_dimensional` in `MathProofs/E68OneDimEnergy.lean` | Newly implemented; **PENDING exact-head CI** |
| Theorem 1, singular n>2 ψ | 0<a<(n−2)/2; ψ=χ(|x|)|x|^(−a), with cutoff =1 in B1, zero outside B2 | None | **OPEN:** actual radial cutoff and singular field |
| Theorem 1, singular L²/gradient integrals | For n>2, integrals over B1 are σ_(n−1)/(n−2a) and σ_(n−1)a²/(n−2−2a) | None | **OPEN:** polar integration and finiteness |
| Theorem 1, singular weak derivative | ∇ψ=−a|x|^(−a−2)x away from 0; boundary term O(ε^(n−1−a))→0; ψ∈H¹ | None | **OPEN:** actual distributional proof, cutoff annulus, equivalence-class membership |
| Theorem 1, fixed-field blowup | For every 0<R<1, integral of |∇ψ|² over B_R = c R^(n−2−2a); R^(2−n) energy = c R^(−2a)→∞ | None | **OPEN:** one fixed H¹ field, no field-dependent C |
| Proposition 2, smooth concentration | Every n>2, every C>0, ∃ψ∈C_c∞ and R>0 violating E68, with ψ_R(x)=R^(1−n/2)φ(x/R) | `ReyesMath.E68.no_uniform_E68_for_smooth_concentrations` in `MathProofs/E68SmoothCounterexample.lean` | **VERIFIED** with actual Fréchet derivative and Lebesgue ball integral on earlier PR head |
| Proposition 2, exact scaling | A=∫|∇φ|²>0, ∫|∇ψ_R|²=A, ∫|ψ_R|²=R² B, ball energy=A | `ReyesMath.E68.smoothConcentration_gradient_energy_constant`, `smoothConcentration_mass_R_sq`, `smoothConcentration_ball_energy_eq_global` in `E68ScaledGradient.lean`, `E68SmoothCounterexample.lean` | **VERIFIED** on earlier PR head |
| Strengthened smooth obstruction and n≥2 iff | Universal radius, center, field quantifiers on C_c∞(Rⁿ;R), n≥2 | `ReyesMath.E68.no_uniform_E68_on_smooth_fields`, `ReyesMath.E68.smoothE68_iff_two` in `E68SmoothClassification.lean` | Newly implemented; **PENDING exact-head CI** |
| Theorem 3, corrected E68' | For every n>2, every ψ∈H¹ with ∇ψ∈Lⁿ, center, R>0: ∫_ball|∇ψ|² ≤ ω_n^(1−2/n) R^(n−2)||∇ψ||_n² | `ReyesMath.E68.local_critical_gradient_norm` and `euclidean_ball_volume_scaling` in `E68CriticalGradient.lean` | Existing **VERIFIED** extended-Lp and ball volume components; complete real-valued E68' **OPEN** |
| Corollary 4, admissible class | Every n>2 and admissible A⊆H¹ with independently proved ||∇ψ||_n ≤ K||ψ||_H1, for all ψ∈A, centers, R>0, bound with ω_n^(1−2/n)K² | None | **OPEN** until corrected E68' and class bridge complete |
| Remark after Corollary 4 | H¹ membership alone does **not** imply universal Lⁿ gradient control | Smooth concentration counterexample, `E68SmoothCounterexample.lean` | The unrestricted-E68 failure is verified; an explicit no-H¹→Lⁿ theorem remains **OPEN** |
| Corollary 5, H² for n=3,4 | Every ψ∈H²(Rⁿ), every center and R>0, some C_n independent of ψ, center, R | None | **OPEN:** Sobolev embedding and n=3 L²–L⁶ interpolation |
| Proposition 6, H² fails for n>4 | For every n>4, no C works for all C_c∞ and all R>0, using u_R(x)=R^(2−n/2)φ(x/R) and first/second derivative integrals | `ReyesMath.E68.high_dimensional_H2_scaling_obstruction` in `E68Scaling.lean` | Algebraic consequence **VERIFIED**; actual H² smooth concentration and all derivative integrals **OPEN** |
| Representative and integral invariance | If representatives and distributional gradients are equal a.e., H¹ energy integrals agree | `ReyesMath.E68.WeakH1Field.field_memLp`, `gradient_memLp`, `energies_eq_of_ae_eq` in `E68WeakH1.lean` | Newly implemented, **PENDING exact-head CI**; uniqueness of distributional derivatives still **OPEN** |
| Section 6 status and scope | E68 refuted for unrestricted n≠2, E68' under Lⁿ, H² n=3,4; no dynamics claimed | Corresponding entries above | Editorial synopsis; no extra physics/dynamical theorem encoded |

**Remaining central obstruction:** To certify the full iff, it is sufficient to complete a genuine H¹ equivalence-class bridge for the n=2 bound and establish that the smooth counterexamples embed in that H¹ class. However, the manuscript **also explicitly claims** the stronger fixed singular field, the corrected E68' inequality and H² consequences, each of which remains an independent acceptance criterion even after an iff proof. No theorem in this mapping assumes E68 or its corrected conclusion as an axiom.

**CI caveat:** This inventory distinguishes previously verified declarations from new source declarations. All new declarations are provisional until the complete project and focused workflows return success at the exact final SHA.
