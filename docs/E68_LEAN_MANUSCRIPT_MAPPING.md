# E68: exact manuscript-to-Lean proof mapping

**Issue:** [#41](https://github.com/rickyjreyes/math/issues/41) · **PR:** [#50](https://github.com/rickyjreyes/math/pull/50).

Pinned versions: Lean 4.23.0, Mathlib 4.23.0. The baseline `E68Scaling` and `E68CriticalGradient` passed [focused CI](https://github.com/rickyjreyes/math/actions/runs/40632112750) and supporting CI at commit `6df2eab1`. Later files are unverified, not completed proofs.

| Manuscript obligation | Lean mapping | Scope / blocker |
|---|---|---|
| Exact dimensional classification: n=2 | `two_dimensional_local_gradient_energy`; newly added `WeakH1Field` with distributional test identity and `weakH1_two_dimensional_local_energy` | Strong derivative baseline checked. Weak H¹ representation is a genuine distributional definition but **new module not current-head CI-checked**; needs compatibility check with any chosen Mathlib Sobolev space |
| n=1 explicit `C_c^∞((-1,1))` field | `compactOneDim`, `compactOneDim_smooth`, `compactOneDim_hasCompactSupport`, `compactOneDim_support_in_unit_interval`, `compactOneDim_nonconstant` | Actual bump field added but no positive derivative-energy integral, exact support-integral equality for large R, or quantified failure proof |
| n>2 smooth concentration, every C>0 | `compactProfile`, `smoothConcentration`, `smoothConcentration_smooth`, `smoothConcentration_hasCompactSupport`, `smooth_concentration_scaling_obstruction` | Actual functions added; need analytic Jacobian, gradient scaling, positive energy integral, support and complete universal-constant counterexample |
| n>2 single singular H¹ field | No faithful Lean declaration yet | Need radial cutoff, Riesz power weak-gradient identification across zero, polar integrals, fixed-field small-ball divergence |
| Corrected E68′ | `local_critical_gradient_norm`, `euclidean_ball_volume_scaling` | Genuine measure/Lp results checked; exact real Bochner-integral inequality with `omega_n^{1-2/n} R^{n-2}` remains |
| Conditional admissible-class corollary | No complete Lean result yet | Need combine corrected E68′ with an **independently assumed** uniform Lⁿ/H¹ estimate; never infer this from unrestricted H¹ |
| H², n=3,4 | No complete Lean result yet | Need genuine whole-space Sobolev embedding, interpolation in n=3 and L⁴ bound in n=4, with exact norms |
| H², n>4 counterexample | `high_dimensional_H2_scaling_obstruction` | Algebraic obstruction checked; construct actual smooth rescaled H² fields and prove all derivative integrals |

**Dimension status:** n=2 has a proved strong-gradient result; n=1 and n>2 are analytically refuted in the manuscript but their actual function-space Lean counterexamples remain open. `main_theorem_formalized` must stay **false**. No discrete or numerical surrogate qualifies.
