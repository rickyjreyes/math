import MathProofs.E18Lyapunov

/-!
# E18 certification: exact Lyapunov descent for the corrected curvature energy

The certification interface for the manuscript *E18: Exact Lyapunov Descent for the Regularized
WCT Curvature Energy* (`papers/wct-e18-exact-gradient-lyapunov`, R. J. Reyes), issue #37. Each
declaration states one assertion of the manuscript for the actual energy
`ℰ[ψ] = ∫_{𝕋_L^d} (c₁|∇ψ|² + c₂F(|ψ|²)|Δψ|²) dx`, `F(ρ) = ρ/(ρ + ε²e^{−2αρ})²`, on the Fourier
space `H²(𝕋_L^d; ℂ)` (`d ≤ 3`, `ε > 0` fixed), in its isometric model `ψ ∈ ℓ²(ℤ^d)`, `A = ι₁ψ`,
`‖ψ‖ = ‖A‖_{H²}`. The mapping is `docs/E18_LEAN_MANUSCRIPT_MAPPING.md`.

* `weight`: `D > 0`, `0 ≤ F ≤ M²`, `F` smooth on `[0, ∞)`, `F(0) = 0`, `F(|z|²) = |R_ε(z)|²`,
  the exact `F′` in both manuscript forms, `F″` continuous, and the bounds on every `[0, A]`.
* `energy_well_defined` (Proposition 1).
* `frechet` (Proposition 2): the explicit real derivative, the quadratic remainder on bounded
  `H²` sets, `HasFDerivAt`, a locally Lipschitz derivative, `ℰ ∈ C¹`.
* `variation` (Proposition 3): `F(|ψ|²)Δψ ∈ H²`, every term of `G` in `L²`, the periodic
  integration-by-parts identities, and `DE ψ h = 2 Re∫ G h̄ dx` for every `h ∈ H²`.
* `main_theorem` (Theorem E18, for `ψ ∈ C¹([0, T]; H⁴)`), `main_theorem_H2` (the same under the
  weaker hypothesis `ψ ∈ C¹([0, T]; H²)`, `ψ(t) ∈ H⁴`), `zero_dissipation` (Corollary 1),
  `finite_dissipation` (Corollary 2).
* `remark_factor_two`, `remark_arbitrary_evolution`, `remark_degenerate_weight`,
  `remark_classical_derivatives`.

Scope (as in the manuscript): the trajectory is a hypothesis; nothing asserts existence,
uniqueness, global existence, convergence or asymptotic stability, physical validity, or a uniform
`ε → 0` limit; the flow is the variational `L²` gradient flow of `ℰ` and is not identified with
any independently proposed physical-time WCT dynamics. The nonperiodic-domain boundary-term
remark is not formalized (the torus has no boundary terms).
-/

open Filter Topology MeasureTheory Set InnerProductSpace intervalIntegral
open scoped ComplexConjugate

noncomputable section

namespace ReyesMath

namespace E18Cert

open TorusL2 BandPass E18FourierEnergy E18WeightDerivative E18

variable {L : ℝ} [hL : Fact (0 < L)] {d : ℕ}

/-- **The curvature weight.** For `ε > 0`: `D(ρ) = ρ + ε²e^{−2αρ} > 0` and `0 ≤ F(ρ) ≤ M_{ε,α}²`
on `[0, ∞)`; `F(0) = 0`; `F(|z|²) = |R_ε(z)|²`; `F` is smooth on `[0, ∞)`;
`F′ = (D − 2ρD′)/D³ = (ε²e^{−2αρ}(1 + 4αρ) − ρ)/D³`; `F″` exists and is continuous on
`[0, ∞)`; on every `[0, A]`, `F′` and `F″` are bounded and the second-order Taylor remainder of `F`
is `O((b − a)²)` uniformly. -/
theorem weight {ε : ℝ} (hε : 0 < ε) (α : ℝ) :
    (∀ ρ : ℝ, 0 ≤ ρ → 0 < D ε α ρ) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → 0 ≤ F ε α ρ ∧ F ε α ρ ≤ Mw ε α ^ 2) ∧
    F ε α 0 = 0 ∧
    (∀ z : ℂ, F ε α (‖z‖ ^ 2) = ‖E26.Rε ε α z‖ ^ 2) ∧
    ContDiffOn ℝ ⊤ (F ε α) (Ici 0) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → HasDerivAt (F ε α) (Fprime ε α ρ) ρ) ∧
    (∀ ρ : ℝ, HasDerivAt (D ε α) (Dprime ε α ρ) ρ) ∧
    (∀ ρ : ℝ, Fprime ε α ρ = (D ε α ρ - 2 * ρ * Dprime ε α ρ) / D ε α ρ ^ 3) ∧
    (∀ ρ : ℝ, Fprime ε α ρ =
      (ε ^ 2 * Real.exp (-2 * α * ρ) * (1 + 4 * α * ρ) - ρ) / (D ε α ρ) ^ 3) ∧
    (∀ ρ : ℝ, 0 ≤ ρ → HasDerivAt (Fprime ε α) (Fsecond ε α ρ) ρ) ∧
    ContinuousOn (Fsecond ε α) (Ici 0) ∧
    (∀ A : ℝ, ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ t ∈ Icc 0 A, |Fprime ε α t| ≤ K₁) ∧
    (∀ A : ℝ, ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ a ∈ Icc 0 A, ∀ b ∈ Icc 0 A,
      |Fprime ε α b - Fprime ε α a| ≤ K₂ * |b - a|) ∧
    (∀ A : ℝ, ∃ K : ℝ, 0 ≤ K ∧ ∀ a ∈ Icc 0 A, ∀ b ∈ Icc 0 A,
      |F ε α b - F ε α a - Fprime ε α a * (b - a)| ≤ K * (b - a) ^ 2) :=
  ⟨fun _ hρ => D_pos hε hρ α, fun _ hρ => ⟨F_nonneg ε α hρ, F_le hε α hρ⟩, F_zero ε α,
    F_norm_sq hε α, (contDiffOn_F ε α).mono fun _ hρ => mem_Uw hε α hρ,
    fun _ hρ => F_hasDerivAt hε hρ α, D_hasDerivAt ε α, Fprime_eq_quotient ε α,
    fun _ => rfl, fun _ hρ => Fprime_hasDerivAt (mem_Uw hε α hρ),
    (continuousOn_Fsecond ε α).mono fun _ hρ => mem_Uw hε α hρ, bound_Fprime hε α,
    lipschitz_Fprime hε α, taylor_F hε α⟩

/-- **Proposition 1 (well-defined, nonnegative energy).** For every `ψ ∈ H²(𝕋_L^d; ℂ)`,
`d ≤ 3`, `ε > 0`: the energy density is integrable for the physical volume `dx` (so `ℰ[ψ]` is
a genuine finite integral, not the value of a divergent one), `ℰ[ψ]` equals
`∫ (c₁|∇ψ|² + c₂F(|ψ|²)|Δψ|²) dx` and `∫ (c₁|∇ψ|² + c₂|Θ_ε[ψ]|²) dx`,
`Θ_ε[ψ] = −(Δψ)R_ε(ψ)`, and `ℰ[ψ] ≥ 0` for `c₁, c₂ ≥ 0`. The physical volume is
`dx = L^d · μ` with `μ` the normalized (probability) Haar measure of `𝕋_L^d`. -/
theorem energy_well_defined (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ) (ψ : ell2 d) :
    Integrable (fun x : Tor L d => c₁ * ∑ j : Fin d, ‖(Dj L j ψ : L2 L d) x‖ ^ 2 +
      c₂ * (F ε α (‖Phi L hd ψ x‖ ^ 2) * ‖(DL L ψ : L2 L d) x‖ ^ 2)) ∧
    E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α ψ =
      ∫ x : Tor L d, (c₁ * ∑ j : Fin d, ‖(dpart j (iota L 1 ψ) : L2 L d) x‖ ^ 2 +
        c₂ * (F ε α (‖(iota L 1 ψ : L2 L d) x‖ ^ 2) * ‖(lap (iota L 1 ψ) : L2 L d) x‖ ^ 2)) ∧
    E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α ψ =
      ∫ x : Tor L d, (c₁ * ∑ j : Fin d, ‖(dpart j (iota L 1 ψ) : L2 L d) x‖ ^ 2 +
        c₂ * ‖-((lap (iota L 1 ψ) : L2 L d) x) * E26.Rε ε α ((iota L 1 ψ : L2 L d) x)‖ ^ 2) ∧
    (0 ≤ c₁ → 0 ≤ c₂ → 0 ≤ E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α ψ) ∧
    (volume : Measure (Tor L d)) = ENNReal.ofReal (L ^ d) • μ L d ∧
    IsProbabilityMeasure (μ L d) := by
  refine ⟨integrable_energy_density hd hε α c₁ c₂ ψ, energy_eq_volume_field hd hε α c₁ c₂ ψ, ?_,
    fun h1 h2 => energy_nonneg hd c₁ c₂ ε α h1 h2 ψ, volume_eq_smul_μ, inferInstance⟩
  rw [energy_eq_volume_field hd hε α c₁ c₂ ψ]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [norm_mul, norm_neg, mul_pow, ← F_norm_sq hε, mul_comm (‖(lap (iota L 1 ψ) : L2 L d) x‖ ^ 2)]

/-- **Proposition 2 (real Fréchet differentiability on `H²`).** `ℰ : H²(𝕋_L^d; ℂ)_ℝ → ℝ` has the
real-linear derivative
`DE ψ h = 2c₁ Re∫∇ψ·∇h̄ + 2c₂ Re∫F(|ψ|²)Δψ Δh̄ + 2c₂ Re∫F′(|ψ|²)ψ|Δψ|² h̄`; for every `M` there is
`C_M` with `|ℰ[ψ+h] − ℰ[ψ] − DE ψ h| ≤ C_M‖h‖²_{H²}` whenever `‖ψ‖_{H²} ≤ M`, `‖h‖_{H²} ≤ 1`;
`ℰ` is Fréchet differentiable; the derivative is locally Lipschitz in operator norm; `ℰ ∈ C¹`. -/
theorem frechet (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ) :
    (∀ ψ h : ell2 d, DE L hd hε α c₁ c₂ ψ h =
      2 * c₁ * ∑ j : Fin d,
          (∫ x : Tor L d, (Dj L j ψ : L2 L d) x * conj ((Dj L j h : L2 L d) x)).re +
        2 * c₂ * (∫ x : Tor L d, (F ε α (‖Phi L hd ψ x‖ ^ 2) : ℂ) * (DL L ψ : L2 L d) x *
          conj ((DL L h : L2 L d) x)).re +
        2 * c₂ * (∫ x : Tor L d, (Fprime ε α (‖Phi L hd ψ x‖ ^ 2) : ℂ) * Phi L hd ψ x *
          ((‖(DL L ψ : L2 L d) x‖ ^ 2 : ℝ) : ℂ) * conj (Phi L hd h x)).re) ∧
    (∀ M : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ h : ell2 d, ‖ψ‖ ≤ M → ‖h‖ ≤ 1 →
      |E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (ψ + h) -
        E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α ψ - DE L hd hε α c₁ c₂ ψ h| ≤
          C * ‖h‖ ^ 2) ∧
    (∀ ψ : ell2 d, HasFDerivAt (E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α)
      (DE L hd hε α c₁ c₂ ψ) ψ) ∧
    (∀ M : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ φ : ell2 d, ‖ψ‖ ≤ M → ‖φ‖ ≤ M →
      ‖DE L hd hε α c₁ c₂ ψ - DE L hd hε α c₁ c₂ φ‖ ≤ C * ‖ψ - φ‖) ∧
    Continuous (DE L hd hε α c₁ c₂) ∧
    ContDiff ℝ 1 (E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α) := by
  refine ⟨DE_apply_volume hd hε α c₁ c₂, fun M => ?_, hasFDerivAt_energy hd hε α c₁ c₂,
    DE_lipschitz hd hε α c₁ c₂, continuous_DE hd hε α c₁ c₂, contDiff_energy hd hε α c₁ c₂⟩
  obtain ⟨C, hC0, hC⟩ := energy_remainder (L := L) hd hε α c₁ c₂ (max M 1)
  exact ⟨C, hC0, fun ψ h hψ hh =>
    hC ψ h (hψ.trans (le_max_left _ _)) (hh.trans (le_max_right _ _))⟩

/-- **Proposition 3 (full complex variational derivative).** For `ψ ∈ H⁴(𝕋_L^d; ℂ)`, `d ≤ 3`:
`F(|ψ|²)Δψ ∈ H²`, the nonlinear summand `F′(|ψ|²)ψ|Δψ|²` is in `L²`, and the summands of
`G[ψ] = −c₁Δψ + c₂Δ(F(|ψ|²)Δψ) + c₂F′(|ψ|²)ψ|Δψ|²` are these functions; the periodic
integration-by-parts identities `Σ_j⟪∂_jψ, ∂_jh⟫ = −⟪Δψ, h⟫` and `⟪u, Δv⟫ = ⟪Δu, v⟫` (`u, v ∈ H²`)
hold; and the Fréchet derivative is represented on **every** `h ∈ H²`:
`DE ψ h = 2 Re∫ G[ψ] h̄ dx`. -/
theorem variation (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ) {ψ : ell2 d}
    (h4 : InH 2 (iota L 1 ψ)) :
    MemLp (fun x => (F ε α (‖(iota L 1 ψ : L2 L d) x‖ ^ 2) : ℂ) *
      (lap (iota L 1 ψ) : Tor L d → ℂ) x) 2 (μ L d) ∧
    (Wt ε α (iota L 1 ψ) : Tor L d → ℂ) =ᵐ[μ L d]
      (fun x => (F ε α (‖(iota L 1 ψ : L2 L d) x‖ ^ 2) : ℂ) * (lap (iota L 1 ψ) : Tor L d → ℂ) x) ∧
    InH 1 (Wt ε α (iota L 1 ψ)) ∧
    MemLp (fun x => (Fprime ε α (‖(iota L 1 ψ : L2 L d) x‖ ^ 2) : ℂ) * (iota L 1 ψ : L2 L d) x *
      ((‖(lap (iota L 1 ψ) : Tor L d → ℂ) x‖ ^ 2 : ℝ) : ℂ)) 2 (μ L d) ∧
    (Vt ε α (iota L 1 ψ) : Tor L d → ℂ) =ᵐ[μ L d]
      (fun x => (Fprime ε α (‖(iota L 1 ψ : L2 L d) x‖ ^ 2) : ℂ) * (iota L 1 ψ : L2 L d) x *
        ((‖(lap (iota L 1 ψ) : Tor L d → ℂ) x‖ ^ 2 : ℝ) : ℂ)) ∧
    Gt c₁ c₂ ε α (iota L 1 ψ) = -((c₁ : ℂ) • lap (iota L 1 ψ)) +
      (c₂ : ℂ) • lap (Wt ε α (iota L 1 ψ)) + (c₂ : ℂ) • Vt ε α (iota L 1 ψ) ∧
    (∀ k : ell2 d, ∑ j, ⟪Dj L j ψ, Dj L j k⟫_ℂ = -⟪DL L ψ, iota L 1 k⟫_ℂ) ∧
    (∀ u v : L2 L d, InH 1 u → InH 1 v → ⟪u, lap v⟫_ℂ = ⟪lap u, v⟫_ℂ) ∧
    (∀ h : ell2 d, DE L hd hε α c₁ c₂ ψ h =
      2 * (∫ x, (Gt c₁ c₂ ε α (iota L 1 ψ) : L2 L d) x * conj ((iota L 1 h : L2 L d) x)).re) := by
  obtain ⟨hmW, hW, hW1, hmV, hV, -⟩ := regularity (L := L) hd hε α h4
  exact ⟨hmW, hW, hW1, hmV, hV, rfl, sum_inner_Dj ψ, fun u v hu hv => inner_lap_comm hu hv,
    DE_eq_volume hd hε α c₁ c₂ h4⟩

/-- **Theorem E18 (conditional exact Lyapunov descent).** Let `ψ ∈ C¹([0, T]; H⁴(𝕋_L^d; ℂ))`
(the `C¹` curve `c` of `H⁴` coordinates, `ψ(t) = ι₂c(t)`) solve `∂ₜψ = −G[ψ]` in `L²`. Then
`dℰ/dt = −2∫|G|² dx = −2∫|∂ₜψ|² dx ≤ 0`, `ℰ[ψ(t₂)] + 2∫_{t₁}^{t₂}∫|G|² dx dt = ℰ[ψ(t₁)]` for
`0 ≤ t₁ ≤ t₂ ≤ T`, `ℰ[ψ(t)]` is nonincreasing, zero dissipation is equivalent to `G = 0` and to
`∂ₜψ = 0`, equal energies at `t₁ < t₂` force `G ≡ 0` on `[t₁, t₂]`, and the descent is strict
otherwise. (`J c(t)` are the `H²` coordinates of `ψ(t)`.) -/
theorem main_theorem (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ) {T : ℝ}
    {c c' : ℝ → ell2 d} (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (c' t) (Icc 0 T) t)
    (hc' : ContinuousOn c' (Icc 0 T))
    (hflow : ∀ t ∈ Icc 0 T, iota L 2 (c' t) = -Gt c₁ c₂ ε α (iota L 2 (c t))) :
    (∀ t ∈ Icc 0 T, HasDerivWithinAt
      (fun u => E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c u)))
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2) (Icc 0 T) t) ∧
    (∀ t ∈ Icc 0 T, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 =
      ∫ x, ‖(iota L 2 (c' t) : L2 L d) x‖ ^ 2) ∧
    (∀ t ∈ Icc 0 T, -2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 ≤ 0) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
      E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c t₂)) +
          2 * ∫ t in t₁..t₂, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 =
        E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c t₁))) ∧
    AntitoneOn (fun t => E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c t))) (Icc 0 T) ∧
    (∀ t ∈ Icc 0 T,
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 = 0 ↔
        Gt c₁ c₂ ε α (iota L 2 (c t)) = 0) ∧
      (Gt c₁ c₂ ε α (iota L 2 (c t)) = 0 ↔ iota L 2 (c' t) = 0)) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ T →
      E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c t₂)) =
        E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c t₁)) →
      ∀ t ∈ Icc t₁ t₂, Gt c₁ c₂ ε α (iota L 2 (c t)) = 0) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ < t₂ → t₂ ≤ T →
      (∃ t ∈ Icc t₁ t₂, Gt c₁ c₂ ε α (iota L 2 (c t)) ≠ 0) →
      E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c t₂)) <
        E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c t₁))) :=
  e18_lyapunov_H4 hd hε α c₁ c₂ hc hc' hflow

/-- **Theorem E18 under weaker hypotheses**: `ψ ∈ C¹([0, T]; H²)` (in the `ℓ²` model) with
`ψ(t) ∈ H⁴` for every `t`, solving `∂ₜψ = −G[ψ]` in `L²`; the same conclusions. -/
theorem main_theorem_H2 (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ) {T : ℝ}
    {γ γ' : ℝ → ell2 d} (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (γ' t) (Icc 0 T) t)
    (hγ' : ContinuousOn γ' (Icc 0 T)) (h4 : ∀ t ∈ Icc 0 T, InH 2 (iota L 1 (γ t)))
    (hflow : ∀ t ∈ Icc 0 T, iota L 1 (γ' t) = -Gt c₁ c₂ ε α (iota L 1 (γ t))) :
    (∀ t ∈ Icc 0 T, HasDerivWithinAt
      (fun u => E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (γ u))
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2) (Icc 0 T) t) ∧
    (∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ T →
      E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (γ t₂) +
          2 * ∫ t in t₁..t₂, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2 =
        E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (γ t₁)) ∧
    AntitoneOn (fun t => E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (γ t)) (Icc 0 T) := by
  obtain ⟨h1, -, -, h4', h5, -⟩ := e18_lyapunov hd hε α c₁ c₂ hγ hγ' h4 hflow
  exact ⟨h1, h4', h5⟩

/-- **Corollary 1 (zero instantaneous dissipation).** Under the hypotheses of Theorem E18, at each
`t`: `dℰ/dt = 0 ⇔ G[ψ(t)] = 0 ⇔ ∂ₜψ(t) = 0`; a nonstationary time slice has strictly negative
energy derivative. -/
theorem zero_dissipation (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ) {T : ℝ}
    {c c' : ℝ → ell2 d} (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (c' t) (Icc 0 T) t)
    (hc' : ContinuousOn c' (Icc 0 T))
    (hflow : ∀ t ∈ Icc 0 T, iota L 2 (c' t) = -Gt c₁ c₂ ε α (iota L 2 (c t))) :
    ∀ t ∈ Icc 0 T,
      (-2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 = 0 ↔
        Gt c₁ c₂ ε α (iota L 2 (c t)) = 0) ∧
      (Gt c₁ c₂ ε α (iota L 2 (c t)) = 0 ↔ iota L 2 (c' t) = 0) ∧
      (iota L 2 (c' t) ≠ 0 → -2 * ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 < 0) := by
  obtain ⟨-, -, hle, -, -, hiff, -⟩ := main_theorem hd hε α c₁ c₂ hc hc' hflow
  intro t ht
  refine ⟨(hiff t ht).1, (hiff t ht).2, fun hne => lt_of_le_of_ne (hle t ht) fun h0 => hne ?_⟩
  exact (hiff t ht).2.1 ((hiff t ht).1.1 h0)

/-- **Corollary 2 (finite accumulated dissipation).** For `c₁, c₂ ≥ 0` and a solution as in
Theorem E18 on every `[0, T]` (here: `ψ ∈ C¹([0, ∞); H⁴)`), `t ↦ ∫|G[ψ(t)]|² dx` is integrable
on `(0, ∞)` and `∫₀^∞ ∫|G[ψ(t)]|² dx dt ≤ ℰ[ψ(0)]/2`; on each `[0, T]`,
`2∫₀ᵀ∫|G|² dx dt ≤ ℰ[ψ(0)]`. -/
theorem finite_dissipation (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) {c c' : ℝ → ell2 d}
    (hc : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt c (c' t) (Ici 0) t) (hc' : ContinuousOn c' (Ici 0))
    (hflow : ∀ t ∈ Ici (0 : ℝ), iota L 2 (c' t) = -Gt c₁ c₂ ε α (iota L 2 (c t))) :
    IntegrableOn (fun t => ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 ≤
      E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c 0)) / 2 ∧
    ∀ T : ℝ, 0 < T →
      2 * ∫ t in (0 : ℝ)..T, ∫ x, ‖(Gt c₁ c₂ ε α (iota L 2 (c t)) : L2 L d) x‖ ^ 2 ≤
        E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (J4 L (c 0)) := by
  have hγ : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => J4 L (c t)) (J4 L (c' t)) (Ici 0) t :=
    fun t ht => hasDerivWithinAt_clm (J4 L) (hc t ht)
  have hγ' : ContinuousOn (fun t => J4 L (c' t)) (Ici 0) := (J4 L).continuous.comp_continuousOn hc'
  have h4 : ∀ t ∈ Ici (0 : ℝ), InH 2 (iota L 1 (J4 L (c t))) :=
    fun t _ => (inH_iff 2 _).2 ⟨c t, (iota_two (c t)).symm⟩
  have hfl : ∀ t ∈ Ici (0 : ℝ), iota L 1 (J4 L (c' t)) = -Gt c₁ c₂ ε α (iota L 1 (J4 L (c t))) :=
    fun t ht => by simp only [← iota_two]; exact hflow t ht
  have hg := e18_global_dissipation hd hε α c₁ c₂ hc₁ hc₂ hγ hγ' h4 hfl
  simp only [← iota_two] at hg
  refine ⟨hg.1, hg.2, fun T hT => ?_⟩
  have sub : Icc 0 T ⊆ Ici 0 := Icc_subset_Ici_self
  have h := e18_finite_dissipation hd hε α c₁ c₂ hc₁ hc₂ hT
    (fun t ht => (hγ t (sub ht)).mono sub) (hγ'.mono sub) (fun t ht => h4 t (sub ht))
    (fun t ht => hfl t (sub ht))
  simp only [← iota_two] at h
  exact h

/-- **Remark (factor of two).** With `(u, v)_ℝ = Re∫ u v̄ dx`, the real Hilbert gradient of `ℰ` is
`∇_ℝℰ = 2G` (and it is the unique such element of `L²`); `G` itself represents `DE ψ` only when
`G = 0`; and along the flow `∂ₜψ = −∇_ℝℰ` one has `dℰ/dt = −‖∇_ℝℰ‖²_{L²(dx)}`. -/
theorem remark_factor_two (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ) :
    (∀ ψ : ell2 d, InH 2 (iota L 1 ψ) →
      (∀ h : ell2 d, DE L hd hε α c₁ c₂ ψ h =
        rinner ((2 : ℂ) • Gt c₁ c₂ ε α (iota L 1 ψ)) (iota L 1 h)) ∧
      (∀ R : L2 L d, (∀ h : ell2 d, DE L hd hε α c₁ c₂ ψ h = rinner R (iota L 1 h)) →
        R = (2 : ℂ) • Gt c₁ c₂ ε α (iota L 1 ψ)) ∧
      ((∀ h : ell2 d, DE L hd hε α c₁ c₂ ψ h =
        rinner (Gt c₁ c₂ ε α (iota L 1 ψ)) (iota L 1 h)) ↔ Gt c₁ c₂ ε α (iota L 1 ψ) = 0)) ∧
    (∀ {γ : ℝ → ell2 d} {γ' : ell2 d} {s : Set ℝ} {t : ℝ}, HasDerivWithinAt γ γ' s t →
      InH 2 (iota L 1 (γ t)) →
      iota L 1 γ' = -((2 : ℂ) • Gt c₁ c₂ ε α (iota L 1 (γ t))) →
      HasDerivWithinAt (fun u => E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (γ u))
        (-∫ x, ‖((2 : ℂ) • Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x‖ ^ 2) s t) := by
  refine ⟨fun ψ h4 => ⟨(real_gradient_eq hd hε α c₁ c₂ h4).1,
    (real_gradient_eq hd hε α c₁ c₂ h4).2, G_real_gradient_iff hd hε α c₁ c₂ h4⟩,
    fun {γ γ' s t} hγ h4 hflow => ?_⟩
  have h := energy_rate_general hd hε α c₁ c₂ hγ h4
  rw [hflow, integral_mul_conj_volume, inner_neg_left, inner_smul_left] at h
  rw [integral_norm_sq_vol, norm_smul]
  convert h using 1
  have hGG := inner_self_eq_norm_sq (𝕜 := ℂ) (Gt c₁ c₂ ε α (iota L 1 (γ t)))
  rw [RCLike.re_to_complex] at hGG
  rw [map_ofNat, Complex.norm_ofNat, ← Complex.ofReal_pow, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    mul_neg, Complex.neg_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hGG]
  ring

/-- **Remark (arbitrary evolutions).** Along any differentiable `H²` evolution with `ψ(t) ∈ H⁴`,
`dℰ/dt = 2 Re∫ G[ψ] ∂ₜψ̄ dx`, which has no fixed sign without the gradient-flow equation. -/
theorem remark_arbitrary_evolution (hd : d ≤ 3) {ε : ℝ} (hε : 0 < ε) (α c₁ c₂ : ℝ)
    {γ : ℝ → ell2 d} {γ' : ell2 d} {s : Set ℝ} {t : ℝ} (hγ : HasDerivWithinAt γ γ' s t)
    (h4 : InH 2 (iota L 1 (γ t))) :
    HasDerivWithinAt (fun u => E18FourierEnergy.energy (L := L) hd c₁ c₂ ε α (γ u))
      (2 * (∫ x, (Gt c₁ c₂ ε α (iota L 1 (γ t)) : L2 L d) x *
        conj ((iota L 1 γ' : L2 L d) x)).re) s t :=
  energy_rate_general hd hε α c₁ c₂ hγ h4

/-- **Remark (degenerate weight; no uniform parabolicity).** `F(0) = 0`, so the curvature weight
`F(|ψ|²)` vanishes wherever `ψ` does. -/
theorem remark_degenerate_weight (hd : d ≤ 3) {ε : ℝ} (α : ℝ) (ψ : ell2 d) (x : Tor L d)
    (hx : Phi L hd ψ x = 0) : F ε α (‖Phi L hd ψ x‖ ^ 2) = 0 := by
  rw [hx, norm_zero, zero_pow two_ne_zero, F_zero]

/-- **Remark (the Fourier operators are the classical ones).** On fields with continuous classical
partial derivatives, the Fourier `∂_j` and `Δ` used in `ℰ` and `G` are the classical `∂_j` and
`Σ_j ∂_j∂_j`. -/
theorem remark_classical_derivatives {ψ : L2 L d} {f : Tor L d → ℂ} {fj fjj : Fin d → Tor L d → ℂ}
    (hf : Continuous f) (hfj : ∀ j, Continuous (fj j)) (hfjj : ∀ j, Continuous (fjj j))
    (hψ : (ψ : Tor L d → ℂ) =ᵐ[μ L d] f) (h1 : ∀ j, HasPartial j f (fj j))
    (h2 : ∀ j, HasPartial j (fj j) (fjj j)) :
    (∀ j, (dpart j ψ : Tor L d → ℂ) =ᵐ[μ L d] fj j) ∧
    (lap ψ : Tor L d → ℂ) =ᵐ[μ L d] fun x => ∑ j, fjj j x :=
  ⟨fun j => dpart_ae_eq_of_hasPartial hf (hfj j) hψ (h1 j),
    lap_ae_eq_of_hasPartial hf hfj hfjj hψ h1 h2⟩

end E18Cert

end ReyesMath
