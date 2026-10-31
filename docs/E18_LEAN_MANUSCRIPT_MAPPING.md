# E18: manuscript-to-Lean certification

**Issue:** [#37](https://github.com/rickyjreyes/math/issues/37) · **PR:** [#75](https://github.com/rickyjreyes/math/pull/75) · **Manuscript:** [`papers/wct-e18-exact-gradient-lyapunov/main.tex`](../papers/wct-e18-exact-gradient-lyapunov/main.tex) (R. J. Reyes; PR #75 adds Proposition 2 and the density argument of Proposition 3).

Pinned versions: Lean 4.23.0, Mathlib v4.23.0. Entry point: [`lean/MathProofs/E18Certification.lean`](../lean/MathProofs/E18Certification.lean) (namespace `ReyesMath.E18Cert`). Dependency audit: [`lean/E18CertificationAudit.lean`](../lean/E18CertificationAudit.lean).

Propositions 1–3, Theorem E18 and both corollaries are kernel-checked Lean declarations with the manuscript's quantifiers:

* every dimension `d ≤ 3` (the manuscript's `1 ≤ d ≤ 3` is included) and every side `L > 0` of the flat torus `𝕋_L^d`;
* every `ε > 0` and every real `α`;
* every real `c₁, c₂`; `c₁, c₂ ≥ 0` exactly where the manuscript uses it (nonnegativity, Corollary 2).

The setting is the Fourier space `H²(𝕋_L^d; ℂ)` (`Σ_k (1+|ξ_k|²)²|ψ̂_k|² < ∞`) as a real Banach space, with:

* the Sobolev embedding `H² ⊂ C(𝕋_L^d)`, proved for `d ≤ 3`;
* the Fourier operators `∂_j` and `Δ`, proved to be the classical operators on `C²` fields;
* the physical volume `dx`, of total mass `L^d`.

The energy is the actual nonlinear energy with the corrected real denominator `D(ρ) = ρ + ε²e^{−2αρ}` (not the older complex denominator). Its derivative is a genuine `HasFDerivAt` on `H²`, with:

* the explicit quadratic remainder on bounded sets;
* a derivative that is locally Lipschitz in operator norm, so `ℰ ∈ C¹`.

For `ψ ∈ H⁴` the `L²` representative `G[ψ]` is proved for **every** `h ∈ H²`, including `F(|ψ|²)Δψ ∈ H²`. The Lyapunov theorem assumes only the stated trajectory. It does not assume a first variation, a representation, a chain rule or a rate identity.

There are no `sorry`, `admit`, new axioms or `native_decide`, and no finite-dimensional or numerical surrogate. No hypothesis is equivalent to a conclusion. All 207 declarations of the fourteen E18 modules depend only on `propext`, `Classical.choice` and `Quot.sound`. No manuscript assertion was found to be false, so no correction is needed.

Reproduce:

```bash
cd lean
lake update && lake exe cache get
lake build MathProofs.E18Certification
lake env lean E18CertificationAudit.lean   # 207 declarations, each: [propext, Classical.choice, Quot.sound]
lake build                                  # complete project
```

## The objects in the statements

| Manuscript object | Lean | Module |
|---|---|---|
| `Ω = 𝕋^d`, `dx` | `TorusL2.Tor L d = Fin d → AddCircle L`, `volume`; `volume = L^d · μ L d` (`TorusL2.volume_eq_smul_μ`) with `μ L d` the Haar probability measure | `TorusFourier` |
| `H²(𝕋^d; ℂ)_ℝ`, `‖ψ‖_{H²}` | `BandPass.ell2 d = ℓ²(ℤ^d; ℂ)` with `ι₁ = BandPass.iota L 1 : c ↦ Σ c_k(1+|ξ_k|²)^{−1}e_k`, an isometry onto `{A : InH 1 A}` (`norm_H_iota`, `inH_iff`); `ℰ` and `DE` are defined on `ell2 d` as a real normed space | `BandPassFlow` |
| `H⁴(𝕋^d)` | `BandPass.InH 2 A`; `H⁴` coordinates `ι₂ = iota L 2`, and `E18.J4` with `ι₂ c = ι₁(J4 c)` (`E18.iota_two`) | `BandPassFlow`, `E18Lyapunov` |
| `ψ(x)` | the continuous representative `BandPass.Phi L hd ψ : C(𝕋_L^d, ℂ)`, `= ι₁ψ` a.e. (`iota_ae_eq_Phi`), `‖Φψ‖_∞ ≤ S‖ψ‖_{H²}` (`norm_Phi_le`, `E18.sob`) | `BandPassFlow`, `E18Frechet` |
| `∂_jψ`, `Δψ` | `BandPass.Dj L j ψ = dpart j (ι₁ψ)` and `BandPass.DL L ψ = lap (ι₁ψ)` (multipliers `iξ_j` and `−|ξ|²`); classical on `C²` fields (`E18.dpart_ae_eq_of_hasPartial`, `E18.lap_ae_eq_of_hasPartial`) | `BandPassFlow`, `E18Representative` |
| `D`, `F`, `D′`, `F′`, `F″` | `E18FourierEnergy.D`, `E18FourierEnergy.F`, `E18WeightDerivative.Dprime`, `E18WeightDerivative.Fprime`, `E18.Fsecond = deriv Fprime` | `E18FourierEnergy`, `E18WeightDerivative`, `E18WeightBounds` |
| `R_ε`, `Θ_ε[ψ] = −(Δψ)R_ε(ψ)` | `ReyesMath.E26.Rε ε α` (shared with M2/E17, E26 and E69); `F(|z|²) = |R_ε(z)|²` (`E18.F_norm_sq`) | `RegularizedCurvatureL2`, `E18WeightBounds` |
| `ℰ[ψ]` | `E18FourierEnergy.energy hd c₁ c₂ ε α ψ = L^d(c₁Σ_j‖∂_jψ‖²_μ + c₂∫F(|ψ|²)|Δψ|²dμ)`, equal to `∫(c₁|∇ψ|² + c₂F(|ψ|²)|Δψ|²) dx` (`E18.energy_eq_volume`) | `E18FourierEnergy`, `E18Frechet` |
| `DE(ψ) ∈ 𝓛_ℝ(H², ℝ)` | `E18.DE L hd hε α c₁ c₂ ψ : ell2 d →L[ℝ] ℝ` | `E18Frechet` |
| `G[ψ] = δℰ/δψ̄` | `E18.Gt c₁ c₂ ε α A = −c₁ΔA + c₂Δ(Wt A) + c₂ Vt A`, with `Wt A = F(|A|²)ΔA` and `Vt A = F′(|A|²)A|ΔA|²` (a.e., `E18.regularity`) | `E18Regularity` |
| `(u, v)_ℝ = Re∫u v̄ dx` | `BandPass.rinner u v` | `BandPassFlow` |
| `ψ ∈ C¹([0,T]; H⁴)`, `∂_tψ` | `c : ℝ → ell2 d` with `HasDerivWithinAt c (c' t) (Icc 0 T) t` and `ContinuousOn c' (Icc 0 T)`; `ψ(t) = ι₂ c(t)`, `∂_tψ(t) = ι₂ c′(t)` | `E18Lyapunov` |

## Assertion-by-assertion mapping

All declarations are in `lean/MathProofs/`, imported by `lean/MathProofs.lean`. They are checked by:

* `.github/workflows/lean-e18.yml`: hole check, a build of each E18 module, the certification, the axiom audit, `lake build MathProofs` and the complete project;
* `.github/workflows/lean.yml`: the complete project.

| # | Manuscript assertion | Fully qualified declaration | Hypotheses and quantifier order | Module |
|---|---|---|---|---|
| 1 | §1: `D(ρ) > 0` for `ρ ≥ 0` | `ReyesMath.E18Cert.weight` (part 1); `ReyesMath.E18FourierEnergy.D_pos` | `∀ ε > 0, ∀ α, ∀ ρ ≥ 0` | `E18FourierEnergy` |
| 2 | Proof of Prop. 1: `F` is smooth and nonnegative on `[0, ∞)`; also `F ≤ M_{ε,α}²` and `F(0) = 0` | `E18Cert.weight` (parts 2, 3, 5); `ReyesMath.E18FourierEnergy.F_nonneg`, `ReyesMath.E18.contDiffOn_F`, `E18.F_le`, `E18.F_zero` | `∀ ε > 0, ∀ α`, on `[0, ∞)` | `E18FourierEnergy`, `E18WeightBounds` |
| 3 | (energy): the two forms `|Θ_ε[ψ]|² = F(|ψ|²)|Δψ|²` | `ReyesMath.E18.F_norm_sq`; `E18Cert.energy_well_defined` (part 3) | `∀ ε > 0, ∀ α, ∀ z ∈ ℂ` | `E18WeightBounds`, `E18Certification` |
| 4 | **Proposition 1**: for `ψ ∈ H²` the energy is finite and nonnegative | `ReyesMath.E18Cert.energy_well_defined`; `E18.integrable_energy_density` (integrable density for `dx`), `E18.energy_eq_volume`, `E18.energy_eq_volume_field`, `E18FourierEnergy.curvature_integrable`, `E18FourierEnergy.energy_nonneg` | `∀ L > 0, ∀ d ≤ 3, ∀ ε > 0, ∀ α, c₁, c₂, ∀ ψ ∈ H²`; nonnegativity for `c₁, c₂ ≥ 0` | `E18FourierEnergy`, `E18Frechet` |
| 5 | (Fprime): `D′`, `F′ = (D − 2ρD′)/D³ = (ε²e^{−2αρ}(1+4αρ) − ρ)/D³` | `E18Cert.weight` (parts 6–9); `ReyesMath.E18WeightDerivative.D_hasDerivAt`, `F_hasDerivAt`, `FprimeRaw_eq`; `ReyesMath.E18.Fprime_eq_quotient` | `∀ ε > 0, ∀ α, ∀ ρ ≥ 0` (formulas `∀ ρ`) | `E18WeightDerivative`, `E18WeightBounds` |
| 6 | Proof of Prop. 2: `F, F′, F″` bounded on compact subsets of `[0, ∞)`; Taylor's theorem with `|B| ≤ Cδ²` | `E18Cert.weight` (parts 10–14); `ReyesMath.E18.Fprime_hasDerivAt`, `continuousOn_Fsecond`, `bound_Fprime`, `lipschitz_F`, `lipschitz_Fprime`, `taylor_F`, `weight_variation_bound` | `∀ ε > 0, ∀ α, ∀ A`, uniformly for `a, b ∈ [0, A]` | `E18WeightBounds`, `E18Frechet` |
| 7 | Proof of Prop. 2: the exact six-term remainder after subtracting the linear part | `ReyesMath.E18VariationAlgebra.weighted_laplacian_remainder` (used verbatim), `norm_sq_add`; `ReyesMath.E18.six_bound`, `rem_pointwise` | pointwise, `∀ z, z₁, w, w₁ ∈ ℂ` | `E18VariationAlgebra`, `E18Frechet` |
| 8 | **Proposition 2**, (frechet): the explicit real-linear derivative | `ReyesMath.E18Cert.frechet` (part 1); `ReyesMath.E18.DE_apply_volume`, `DE_apply`, `inner_Wcoef` | `∀ ψ, h ∈ H²` | `E18Frechet` |
| 9 | (frechet-remainder): `|ℰ[ψ+h] − ℰ[ψ] − DE(ψ)[h]| ≤ C_M‖h‖²_{H²}` for `‖ψ‖ ≤ M`, `‖h‖ ≤ 1` | `E18Cert.frechet` (part 2); `ReyesMath.E18.energy_remainder` (any `‖h‖ ≤ M`), `curvJ_remainder`, `integral_norm_mul_norm_le` (Cauchy–Schwarz) | `∀ M, ∃ C_M ≥ 0, ∀ ψ h` with `‖ψ‖ ≤ M`, `‖h‖ ≤ 1`; `C_M` is fixed before `ψ` and `h` | `E18Frechet` |
| 10 | `ℰ` is Fréchet differentiable, `DE(ψ)` is the derivative | `E18Cert.frechet` (part 3); `ReyesMath.E18.hasFDerivAt_energy`, `fderiv_energy` | `∀ ψ ∈ H²` | `E18Frechet` |
| 11 | The derivative is locally Lipschitz in operator norm; `ℰ ∈ C¹` | `E18Cert.frechet` (parts 4–6); `ReyesMath.E18.DE_lipschitz`, `opNorm_sub_le_of_remainder`, `continuous_DE`, `contDiff_energy` | `∀ M, ∃ C, ∀ ψ φ` with `‖ψ‖, ‖φ‖ ≤ M`: `‖DE ψ − DE φ‖ ≤ C‖ψ − φ‖` | `E18Frechet` |
| 12 | **Proposition 3**, proof: for `ψ ∈ H⁴`, `F(|ψ|²)Δψ ∈ H²` and its Laplacian is in `L²`; `F′(|ψ|²)ψ|Δψ|² ∈ L²` | `ReyesMath.E18Cert.variation` (parts 1–6); `ReyesMath.E18.regularity`, `rep_facts`, `weight_facts`, `leibniz` | `∀ d ≤ 3, ∀ ε > 0, ∀ α, ∀ ψ ∈ H⁴` | `E18Regularity`, `E18Leibniz` |
| 13 | (first-gradient): periodic integration by parts `Σ_j⟨∂_jψ, ∂_jh⟩ = −⟨Δψ, h⟩` | `E18Cert.variation` (part 7); `ReyesMath.BandPass.sum_inner_Dj` | `∀ ψ, h ∈ H²` | `BandPassFlow` |
| 14 | `Δ` is self-adjoint on `𝕋^d` | `E18Cert.variation` (part 8); `ReyesMath.E18.inner_lap_comm` | `∀ u, v ∈ H²` | `E18Representative` |
| 15 | (G): `DE(ψ)[h] = 2 Re∫ G[ψ] h̄ dx` for the full Fréchet derivative and every `h ∈ H²` | `E18Cert.variation` (part 9); `ReyesMath.E18.DE_eq_volume`, `DE_eq_inner`, `Wcoef_eq` | `∀ ψ` with `ι₁ψ ∈ H⁴`, `∀ h ∈ H²` | `E18Representative` |
| 16 | (convention): `δℰ/δψ̄` is one half of the real `L²` gradient | `ReyesMath.E18Cert.remark_factor_two` (part 1); `ReyesMath.E18.real_gradient_eq` (`∇_ℝℰ = 2G`, unique), `G_real_gradient_iff` (`G` represents `DE ψ` only if `G = 0`) | `∀ ψ` with `ι₁ψ ∈ H⁴` | `E18Representative` |
| 17 | **Theorem E18**, (rate): `dℰ/dt = −2‖G‖²_{L²} = −2‖∂_tψ‖²_{L²} ≤ 0` | `ReyesMath.E18Cert.main_theorem` (parts 1–3); `ReyesMath.E18.energy_rate`, `e18_lyapunov_H4` | `∀ T`, `ψ ∈ C¹([0,T]; H⁴)` solving `∂_tψ = −G[ψ]` in `L²`; `∀ t ∈ [0, T]` (one-sided at the endpoints) | `E18Lyapunov` |
| 18 | (integrated): `ℰ[ψ(t₂)] + 2∫_{t₁}^{t₂}‖G‖²ds = ℰ[ψ(t₁)]` | `E18Cert.main_theorem` (part 4); `ReyesMath.E18.e18_lyapunov`; `ReyesMath.E18IntegratedBalance.actual_energy_balance` with its hypotheses discharged | `∀ 0 ≤ t₁ ≤ t₂ ≤ T` | `E18Lyapunov`, `E18IntegratedBalance` |
| 19 | `ℰ[ψ(t₂)] ≤ ℰ[ψ(t₁)]` | `E18Cert.main_theorem` (part 5, `AntitoneOn` on `[0, T]`) | `∀ t₁ ≤ t₂` in `[0, T]` | `E18Lyapunov` |
| 20 | Theorem E18 under weaker hypotheses: `ψ ∈ C¹([0,T]; H²)`, `ψ(t) ∈ H⁴` | `ReyesMath.E18Cert.main_theorem_H2`; `ReyesMath.E18.e18_lyapunov` | `∀ T`, the trajectory in `H²` coordinates | `E18Lyapunov` |
| 21 | **Corollary 1**: `dℰ/dt = 0 ⇔ G[ψ(t)] = 0 ⇔ ∂_tψ(t) = 0`; nonstationary slices have strictly negative derivative | `ReyesMath.E18Cert.zero_dissipation`; `E18Cert.main_theorem` (parts 6–8: also constancy of `ℰ` on `[t₁, t₂]` forces `G ≡ 0` there, and strict descent); `ReyesMath.E18FlowChainRule.zero_dissipation_iff_stationary`, `stationary_iff_zero_velocity` | `∀ t ∈ [0, T]`; `∀ 0 ≤ t₁ < t₂ ≤ T` | `E18Certification`, `E18Lyapunov` |
| 22 | **Corollary 2**: `∫₀^∞‖G[ψ(t)]‖²dt ≤ ℰ[ψ(0)]/2` | `ReyesMath.E18Cert.finite_dissipation` (also integrability on `(0, ∞)` and `2∫₀ᵀ ≤ ℰ[ψ(0)]` on every `[0, T]`); `ReyesMath.E18.e18_global_dissipation`, `e18_finite_dissipation` | `c₁, c₂ ≥ 0`, `ψ ∈ C¹([0, ∞); H⁴)` solving the flow; existence of such a solution is a hypothesis | `E18Lyapunov` |
| 23 | Remark (nonperiodic domains): the boundary term `B[h]` on smooth bounded domains | — | not formalized (see below) | — |
| 24 | Remark (factor of two): `∇_ℝℰ = 2G`; the flow `∂_tψ = −∇_ℝℰ` obeys `dℰ/dt = −‖∇_ℝℰ‖²` | `E18Cert.remark_factor_two` | `∀ ψ ∈ H⁴`; along any trajectory with `∂_tψ = −2G` | `E18Certification` |
| 25 | Scope (ii): no uniform parabolicity, since `F(0) = 0` | `ReyesMath.E18Cert.remark_degenerate_weight`; `E18.F_zero` | `∀ ψ, x` with `ψ(x) = 0` | `E18Certification` |
| 26 | Scope: an arbitrary evolution gives only `dℰ/dt = 2 Re∫ G X̄ dx` | `ReyesMath.E18Cert.remark_arbitrary_evolution`; `ReyesMath.E18.energy_rate_general` | any differentiable `H²` evolution with `ψ(t) ∈ H⁴` | `E18Lyapunov` |
| 27 | Scope (i), (iii)–(v): no existence, convergence, localization or derivation from WCT dynamics | — | editorial: every dynamical statement is conditional on a given trajectory; the flow is not identified with any physical-time WCT equation | — |

The Fourier operators are tied to classical derivatives by `ReyesMath.E18Cert.remark_classical_derivatives`.

## How the proofs go

* **The field space.** `ψ ∈ ℓ²(ℤ^d)` stands for `A = ι₁ψ ∈ H²`, with `‖A‖_{H²} = ‖ψ‖`. For `d ≤ 3`, `Σ_k(1+|ξ_k|²)^{−2} < ∞` makes the Fourier series of `A` converge uniformly to the continuous representative `Φψ`, with `‖Φψ‖_∞ ≤ S‖ψ‖`. The operators `∂_j` and `Δ` are bounded from `ℓ²` to `L²`, with norm at most `1`.
* **The remainder.** Pointwise, put `a = |ψ|²`, `a′ = |ψ+h|² = a + 2Re(ψ̄h) + |h|²`, `w = Δψ`, `w₁ = Δh`.
  * The six-term identity `weighted_laplacian_remainder` writes the remainder exactly, with `dw = F′(a)·2Re(ψ̄h)` and `B = F(a′) − F(a) − dw`.
  * The uniform Taylor bound on `[0, (F₀+Δ)²]` gives `|B| ≤ (K(2F₀+Δ)² + K₁)δ²`, with `δ = ‖Φh‖_∞`.
  * AM–GM gives `|remainder| ≤ P δ²|w|² + Q|w₁|²`.
  * Integrating, the remainder is at most `P δ²‖Δψ‖² + Q‖Δh‖² ≤ C_M‖h‖²`.
  * The gradient part is exactly `Σ_j‖∂_jh‖²`.
* **The Lipschitz derivative.** The argument is abstract (`opNorm_sub_le_of_remainder`). Suppose a function has a quadratic remainder bound `C‖h‖²` uniformly on a ball. Expand around `ψ`, `φ` and `φ + (ψ − φ)` with increments of norm `t = ‖ψ − φ‖`. This gives `|(Df ψ − Df φ)h| ≤ 6Ct²` for `‖h‖ = t`, hence `‖Df ψ − Df φ‖ ≤ 6C‖ψ − φ‖`. With `C = C_{4M}` this proves Lipschitz continuity on every ball, and `ContDiff ℝ 1` follows.
* **The representative.** For `ψ ∈ H⁴` the coefficients satisfy `Σ_k|ψ̂_k|(1+|ξ_k|²) < ∞`, so `ψ`, `∂_jψ`, `∂_j∂_jψ` and `Δψ` have continuous representatives with classical partial derivatives (`rep_facts`).
  * The weight `F(|ψ|²)` then has continuous partials of order `≤ 2` (`weight_facts`, which uses `F″`).
  * The Leibniz rule `Δ(wu) = wΔu + 2∇w·∇u + (Δw)u` (`leibniz`) gives `F(|ψ|²)Δψ ∈ H²`. Its proof pairs `wu` with the modes `e_k` and moves the derivatives by periodic integration by parts, which follows from translation invariance of the Haar measure (`cfun_hasPartial`, `integral_dpart_conj`).
  * `DE ψ h = 2L^d Re⟨ι₁h, G⟩` then follows from `sum_inner_Dj`, the self-adjointness `inner_lap_comm`, `W_ψ = 2F(|A|²)ΔA` and an a.e. computation of the density term.
* **Theorem E18.** `hasFDerivAt_energy` and `DE_eq_inner` discharge the hypotheses of the PR's conditional reductions `E18FlowChainRule.hasDerivWithinAt_actual_negative_gradient` and `E18IntegratedBalance.actual_energy_balance`.
  * The rate is the Banach-space chain rule.
  * The integrated identity is the fundamental theorem of calculus, with `t ↦ G(ψ(t)) = −∂_tψ(t)` continuous.
  * If `ℰ(t₂) = ℰ(t₁)`, then the continuous nonnegative dissipation vanishes a.e. on `[t₁, t₂]`, hence everywhere there.
  * Corollary 2 bounds the interval integrals uniformly in `T` and passes to `(0, ∞)`.
  * The manuscript's hypothesis `ψ ∈ C¹([0,T]; H⁴)` is reduced to the `H²` statement with `J`, because `ι₂ = ι₁ ∘ J`.

## Not formalized

* **Remark (nonperiodic domains).** The boundary contribution `B[h]` on a smooth bounded domain needs the divergence theorem on such domains. Mathlib v4.23.0 has it only for boxes. The remark concerns a different domain class, and no torus statement depends on it. On the torus the integration-by-parts identities hold with no boundary term (rows 13–14).

## Verification

* Local, pinned toolchain:
  * `lake build MathProofs.E18Certification`;
  * `lake build MathProofs` and the complete project `lake build` (7389 jobs, exit 0);
  * `lake env lean E18CertificationAudit.lean`, with 207 of 207 declarations on `[propext, Classical.choice, Quot.sound]`;
  * no `sorry`, `admit`, `axiom` or `native_decide` in any E18 module.
* Exact-head CI: recorded in `lean/formalization.yaml` and [PR #75](https://github.com/rickyjreyes/math/pull/75).

## Lean conventions that differ in form from the manuscript

* `ℰ`, `DE` and `G` act on `H²` coordinates `ψ ∈ ℓ²(ℤ^d)` and on the field `A = ι₁ψ ∈ L²`. The `H²` norm of the manuscript is `‖ψ‖`.
* A trajectory `ψ ∈ C¹([0,T]; H⁴)` is a `C¹` curve `c` of `H⁴` coordinates with `ψ(t) = ι₂c(t)`. Its energy is `ℰ` at the `H²` coordinates `J c(t)`. Derivatives at `t = 0` and `t = T` are one-sided, within `[0, T]`.
* Integrals `∫ … dx` are over `volume` on `𝕋_L^d`, so `‖G‖²_{L²(Ω)} = ∫|G|² dx = L^d‖G‖²_μ`. The normalized `μ` appears only inside definitions, and the conversion is proved, not assumed. Every integral is shown to be of an integrable function.
* `Wt`, `Vt` and `Gt` are defined on all of `L²` (an `L²` class is formed when the function is square-integrable, `0` otherwise). Every statement about them assumes `ψ ∈ H⁴`, where `regularity` proves square-integrability.
* `d ≤ 3` includes the degenerate `d = 0`. The rate identity and its consequences hold for all real `c₁, c₂`. Nonnegativity and Corollary 2 use `c₁, c₂ ≥ 0`, as fixed in the manuscript.
