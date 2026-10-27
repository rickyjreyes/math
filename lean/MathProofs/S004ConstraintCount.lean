import Mathlib

/-!
# Complete constraint count for the regular higher-derivative S004 scalar (F02)

Formalization of Lemmas 1–2 and the theorem of
`papers/s004-complex-scalar-constraint-count/main.tex`, together with the canonical
energy and charge statements, for the fixed-flat-background sector on the regular
patch `ρ = |X|² > 0` with `ε, κ, θ > 0`, `γ² < 4κθ` (`Model.Hyp`).

The canonical structure is ultralocal: as in the manuscript, the common spatial
delta distribution is suppressed and the analysis is carried out per spatial point.
Spatial derivatives enter only through `b = ΔX`, `g = |∇X|²` and the functional
derivative `δH₀/δX`, which the preservation theorem treats as an arbitrary value.

* `Lphys_eq_neg_Lorig`: the original complex density equals `−𝓛_phys` in real components.
* `accHessian_eq`, `accHessian_det_pos`: the acceleration Hessian computed from the
  actual second Fréchet derivative is `−2κF I₂`, `det = 4κ²F² > 0`.
* `momentum_X`, `momentum_V`, `momentum_lam`, `momentum_V_iff`, `legendre_image`:
  the canonical momenta of the first-order density are `p_X = λ`, `p_V = −F(2κV̇ − Ab)`,
  `p_λ = 0`; the Legendre image is exactly `{p_X = λ, p_λ = 0}` (four primary constraints).
* `diracMatrix_eq`, `diracMatrix_det`, `no_first_class`: the Dirac matrix is
  `[[0, −I], [I, 0]]` with determinant one; no first-class combination exists.
* `preservation_Xi`, `preservation_Phi`, `preservation_iff`, `no_secondary_constraints`:
  preservation fixes `u = V`, `w = −δH₀/δX` uniquely, so no secondary constraints arise.
* `finrank_phase`, `finrank_constraintSurface`, `reducedEmbed_*`, `diracBracket_*`,
  `constraint_count`: twelve canonical dimensions, an eight-dimensional reduced phase
  space with canonical pairs `(X, p_X), (V, p_V)`, and `N_conf = (12 − 0 − 4)/2 = 4`.
* `H0_eq_legendre`, `totalHam_on_surface`, `Hphys_unbounded_below`, `momentum_term_neg`:
  the partial Legendre transform and the unbounded canonical energy.
* `charge_generates`, `Hphys_rot_invariant`, `charge_not_constraint`: the global `U(1)`
  charge generates constant phase rotations, is a symmetry, and is not a constraint.
-/

open InnerProductSpace

namespace ReyesMath

namespace S004

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- Model data: weight parameters `ε, α`, couplings `κ, θ, γ`, and an arbitrary
potential `V(ρ)`. -/
structure Model where
  ε : ℝ
  α : ℝ
  κ : ℝ
  θ : ℝ
  γ : ℝ
  pot : ℝ → ℝ

/-- The hypotheses `ε > 0, κ > 0, θ > 0, γ² < 4κθ`. -/
structure Model.Hyp (M : Model) : Prop where
  ε_pos : 0 < M.ε
  κ_pos : 0 < M.κ
  θ_pos : 0 < M.θ
  disc : M.γ ^ 2 < 4 * M.κ * M.θ

namespace Model

variable (M : Model)

/-- `D(ρ) = ρ + ε² e^{−2αρ}`. -/
noncomputable def D (ρ : ℝ) : ℝ := ρ + M.ε ^ 2 * Real.exp (-2 * M.α * ρ)
/-- `F(ρ) = ρ / D(ρ)²`. -/
noncomputable def F (ρ : ℝ) : ℝ := ρ / M.D ρ ^ 2
/-- `A = 2κ + γ`. -/
def A : ℝ := 2 * M.κ + M.γ
/-- `C = κ + θ + γ`. -/
def C : ℝ := M.κ + M.θ + M.γ
/-- `B⊥ = C − A²/(4κ) = θ − γ²/(4κ)`. -/
noncomputable def Bperp : ℝ := M.θ - M.γ ^ 2 / (4 * M.κ)

variable {M}

theorem F_pos (h : M.Hyp) {ρ : ℝ} (hρ : 0 < ρ) : 0 < M.F ρ := by
  have hD : 0 < M.D ρ := by
    unfold D
    have := h.ε_pos
    positivity
  exact div_pos hρ (pow_pos hD 2)

theorem Bperp_eq (h : M.Hyp) : M.Bperp = M.C - M.A ^ 2 / (4 * M.κ) := by
  have := h.κ_pos
  unfold Bperp C A
  field_simp
  ring

theorem Bperp_pos (h : M.Hyp) : 0 < M.Bperp := by
  have hκ := h.κ_pos
  have := h.disc
  unfold Bperp
  rw [sub_pos, div_lt_iff₀ (by positivity)]
  linarith

end Model

/-- Real components `(Re z, Im z)` of a complex number. -/
noncomputable def realVec (z : ℂ) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.re, z.im]

theorem inner_realVec (z w : ℂ) : inner ℝ (realVec z) (realVec w) = z.re * w.re + z.im * w.im := by
  simp [realVec, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The original S004 density at a point, with signature `(−,+,…,+)`:
`∂_μψ̄ ∂^μψ − V(ρ) + F(ρ)[κ|□ψ|² + θ|Δψ|² + γ Re(□ψ · conj Δψ)]`, `□ψ = −ψ_ττ + Δψ`. -/
noncomputable def Lorig (M : Model) {d : ℕ} (ψ ψτ ψττ Δψ : ℂ) (gradψ : Fin d → ℂ) : ℝ :=
  (-‖ψτ‖ ^ 2 + ∑ k, ‖gradψ k‖ ^ 2) - M.pot (‖ψ‖ ^ 2) +
    M.F (‖ψ‖ ^ 2) * (M.κ * ‖-ψττ + Δψ‖ ^ 2 + M.θ * ‖Δψ‖ ^ 2 +
      M.γ * ((-ψττ + Δψ) * (starRingEnd ℂ) Δψ).re)

/-- The physical real-component density (eq. `realL`), as a function of
`X, V = ∂_τX, a = ∂_τ²X, b = ΔX` and `g = |∇X|²`. -/
noncomputable def Lphys (M : Model) (X V a b : E2) (g : ℝ) : ℝ :=
  inner ℝ V V - g + M.pot (inner ℝ X X) -
    M.F (inner ℝ X X) * (M.κ * inner ℝ a a - M.A * inner ℝ a b + M.C * inner ℝ b b)

theorem norm_sq_eq_inner_realVec (z : ℂ) : ‖z‖ ^ 2 = inner ℝ (realVec z) (realVec z) := by
  rw [inner_realVec, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

/-- `𝓛_phys = −𝓛_orig` in real components. -/
theorem Lphys_eq_neg_Lorig (M : Model) {d : ℕ} (ψ ψτ ψττ Δψ : ℂ) (gradψ : Fin d → ℂ) :
    Lphys M (realVec ψ) (realVec ψτ) (realVec ψττ) (realVec Δψ) (∑ k, ‖gradψ k‖ ^ 2) =
      -Lorig M ψ ψτ ψττ Δψ gradψ := by
  unfold Lphys Lorig
  simp only [inner_realVec, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  unfold Model.A Model.C
  ring

/-- Derivative of the density in the acceleration. -/
theorem hasFDerivAt_Lphys_acc (M : Model) (X V b : E2) (g : ℝ) (a : E2) :
    HasFDerivAt (fun a => Lphys M X V a b g)
      (-M.F (inner ℝ X X) • (M.κ • ((2:ℝ) • innerSL ℝ a) - M.A • innerSL ℝ b)) a := by
  unfold Lphys
  have h1 : HasFDerivAt (fun a : E2 => inner ℝ a a) ((2:ℝ) • innerSL ℝ a) a := by
    have := (hasFDerivAt_id a).inner ℝ (hasFDerivAt_id a)
    convert this using 1
    ext v
    simp [two_smul, real_inner_comm]
  have h2 : HasFDerivAt (fun a : E2 => inner ℝ a b) (innerSL ℝ b) a := by
    have := (hasFDerivAt_id a).inner ℝ (hasFDerivAt_const b a)
    convert this using 1
    ext v
    simp [real_inner_comm]
  have := (((h1.const_mul M.κ).sub (h2.const_mul M.A)).add_const
    (M.C * inner ℝ b b)).const_mul (M.F (inner ℝ X X))
  have := this.const_sub (inner ℝ V V - g + M.pot (inner ℝ X X))
  convert this using 1
  ext v
  simp

/-- The acceleration Hessian `∂²𝓛_phys/∂aᵢ∂aⱼ`, computed from the actual second
Fréchet derivative of the density. -/
noncomputable def accHessian (M : Model) (X V b : E2) (g : ℝ) (a : E2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => fderiv ℝ (fun a' => fderiv ℝ (fun a'' => Lphys M X V a'' b g) a') a
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- **Lemma (regular acceleration Hessian)**: `H_acc = −2κF(ρ) I₂` at every point. -/
theorem accHessian_eq (M : Model) (X V b : E2) (g : ℝ) (a : E2) :
    accHessian M X V b g a = (-2 * M.κ * M.F (inner ℝ X X)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hfd : (fun a' => fderiv ℝ (fun a'' => Lphys M X V a'' b g) a') =
      fun a' => -M.F (inner ℝ X X) • (M.κ • ((2:ℝ) • innerSL ℝ a') - M.A • innerSL ℝ b) :=
    funext fun a' => (hasFDerivAt_Lphys_acc M X V b g a').fderiv
  have h2 : HasFDerivAt
      (fun a' : E2 => -M.F (inner ℝ X X) • (M.κ • ((2:ℝ) • innerSL ℝ a') - M.A • innerSL ℝ b))
      (-M.F (inner ℝ X X) • (M.κ • ((2:ℝ) • innerSL ℝ))) a := by
    have hl : HasFDerivAt (fun a' : E2 => innerSL ℝ a') (innerSL ℝ) a := (innerSL ℝ).hasFDerivAt
    have := (((hl.const_smul (2 : ℝ)).const_smul M.κ).sub_const (M.A • innerSL ℝ b)).const_smul
      (-M.F (inner ℝ X X))
    convert this using 1
  ext i j
  simp only [accHessian, hfd, h2.fderiv]
  simp [Matrix.one_apply, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  split_ifs <;> ring

theorem accHessian_det (M : Model) (X V b : E2) (g : ℝ) (a : E2) :
    (accHessian M X V b g a).det = 4 * M.κ ^ 2 * M.F (inner ℝ X X) ^ 2 := by
  rw [accHessian_eq, Matrix.det_smul, Matrix.det_one]
  simp
  ring

/-- On the patch `ρ > 0` the higher-time Legendre map is pointwise invertible. -/
theorem accHessian_det_pos (M : Model) (h : M.Hyp) (X V b : E2) (g : ℝ) (a : E2)
    (hρ : 0 < inner ℝ X X) : 0 < (accHessian M X V b g a).det := by
  rw [accHessian_det]
  have := h.κ_pos
  have := M.F_pos h hρ
  positivity

/-! ### First-order reduction and the Legendre map -/

/-- The first-order auxiliary density `𝓛₁ = 𝓛_phys(X, V, V̇, ΔX) + λ·(Ẋ − V)`. -/
noncomputable def L1 (M : Model) (b : E2) (g : ℝ) (X V lam Xd Vd _lamd : E2) : ℝ :=
  Lphys M X V Vd b g + inner ℝ lam (Xd - V)

/-- The canonical momentum conjugate to a velocity: the Riesz vector of the partial
Fréchet derivative of the density with respect to that velocity. -/
noncomputable def momentum (f : E2 → ℝ) (v : E2) : E2 :=
  (InnerProductSpace.toDual ℝ E2).symm (fderiv ℝ f v)

theorem momentum_of_hasFDerivAt {f : E2 → ℝ} {v p : E2} {D : E2 →L[ℝ] ℝ}
    (hf : HasFDerivAt f D v) (hD : ∀ w, D w = inner ℝ p w) : momentum f v = p := by
  rw [momentum, hf.fderiv]
  apply (InnerProductSpace.toDual ℝ E2).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext x
  simp [hD]

variable (M : Model) (b : E2) (g : ℝ) (X V lam Xd Vd lamd : E2)

/-- `p_X = ∂𝓛₁/∂Ẋ = λ`. -/
theorem momentum_X : momentum (fun Xd => L1 M b g X V lam Xd Vd lamd) Xd = lam := by
  have h := ((hasFDerivAt_const lam Xd).inner ℝ ((hasFDerivAt_id Xd).sub_const V)).const_add
    (Lphys M X V Vd b g)
  refine momentum_of_hasFDerivAt (D := (innerSL ℝ lam)) ?_ (fun w => by simp)
  unfold L1
  convert h using 1
  ext v
  simp

/-- `p_V = ∂𝓛₁/∂V̇ = −F(ρ)(2κV̇ − A b)`. -/
theorem momentum_V :
    momentum (fun Vd => L1 M b g X V lam Xd Vd lamd) Vd =
      -M.F (inner ℝ X X) • ((2 * M.κ) • Vd - M.A • b) := by
  have h := (hasFDerivAt_Lphys_acc M X V b g Vd).add_const (inner ℝ lam (Xd - V))
  refine momentum_of_hasFDerivAt h (fun w => ?_)
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, innerSL_apply,
    inner_smul_left, inner_sub_left, smul_eq_mul, RCLike.conj_to_real]
  ring

/-- `p_λ = ∂𝓛₁/∂λ̇ = 0`. -/
theorem momentum_lam : momentum (fun lamd => L1 M b g X V lam Xd Vd lamd) lamd = 0 := by
  refine momentum_of_hasFDerivAt (D := 0) ?_ (fun w => by simp)
  unfold L1
  exact hasFDerivAt_const _ _

/-- The acceleration momentum relation is solvable: `p_V = −F(2κV̇ − Ab)` iff
`V̇ = (A/2κ) b − p_V/(2κF)` (eq. `invert`). -/
theorem momentum_V_iff (h : M.Hyp) (hρ : 0 < inner ℝ X X) (pV : E2) :
    momentum (fun Vd => L1 M b g X V lam Xd Vd lamd) Vd = pV ↔
      Vd = (M.A / (2 * M.κ)) • b - (1 / (2 * M.κ * M.F (inner ℝ X X))) • pV := by
  rw [momentum_V]
  have hF := M.F_pos h hρ
  have hκ := h.κ_pos
  constructor
  · rintro rfl
    ext i
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rintro rfl
    ext i
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- The Legendre map of the first-order density. -/
noncomputable def legendre (X V lam Xd Vd lamd : E2) : E2 × E2 × E2 :=
  (momentum (fun Xd => L1 M b g X V lam Xd Vd lamd) Xd,
    momentum (fun Vd => L1 M b g X V lam Xd Vd lamd) Vd,
    momentum (fun lamd => L1 M b g X V lam Xd Vd lamd) lamd)

/-- **Primary constraints.**  On the regular patch `ρ > 0`, the image of the Legendre map
over a configuration `(X, V, λ)` is exactly `{p_X = λ, p_λ = 0}`: four real primary
constraints, and no constraint on `p_V`. -/
theorem legendre_image (h : M.Hyp) (hρ : 0 < inner ℝ X X) :
    Set.range (fun v : E2 × E2 × E2 => legendre M b g X V lam v.1 v.2.1 v.2.2) =
      {p | p.1 = lam ∧ p.2.2 = 0} := by
  ext ⟨pX, pV, pl⟩
  simp only [Set.mem_range, Set.mem_setOf_eq, legendre, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨Xd', Vd', lamd', h1, _, h3⟩
    rw [momentum_X] at h1
    rw [momentum_lam] at h3
    exact ⟨h1.symm, h3.symm⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨0, (M.A / (2 * M.κ)) • b - (1 / (2 * M.κ * M.F (inner ℝ X X))) • pV, 0,
      momentum_X M b g X V pX 0 _ 0, ?_, momentum_lam M b g X V pX 0 _ 0⟩
    exact (momentum_V_iff M b g X V pX 0 _ 0 h hρ pV).2 rfl

/-! ### The canonical phase space and the Dirac matrix -/

/-- The pointwise canonical phase space: `q = (X, V, λ)`, `p = (p_X, p_V, p_λ)`,
twelve real dimensions. -/
abbrev Phase := (Fin 3 → E2) × (Fin 3 → E2)

/-- Block projections `q_blk`, `p_blk`. -/
noncomputable def qblk (blk : Fin 3) : Phase →L[ℝ] E2 :=
  (ContinuousLinearMap.proj blk).comp (ContinuousLinearMap.fst ℝ _ _)

noncomputable def pblk (blk : Fin 3) : Phase →L[ℝ] E2 :=
  (ContinuousLinearMap.proj blk).comp (ContinuousLinearMap.snd ℝ _ _)

/-- Canonical coordinate functions. -/
noncomputable def qc (blk : Fin 3) (i : Fin 2) : Phase →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp (qblk blk)

noncomputable def pc (blk : Fin 3) (i : Fin 2) : Phase →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp (pblk blk)

/-- Coordinate directions. -/
noncomputable def eq' (blk : Fin 3) (i : Fin 2) : Phase :=
  (Pi.single blk (EuclideanSpace.single i 1), 0)

noncomputable def ep (blk : Fin 3) (i : Fin 2) : Phase :=
  (0, Pi.single blk (EuclideanSpace.single i 1))

/-- Partial derivatives along canonical coordinates. -/
noncomputable def dq (f : Phase → ℝ) (z : Phase) (blk : Fin 3) (i : Fin 2) : ℝ :=
  fderiv ℝ f z (eq' blk i)

noncomputable def dp (f : Phase → ℝ) (z : Phase) (blk : Fin 3) (i : Fin 2) : ℝ :=
  fderiv ℝ f z (ep blk i)

/-- The canonical Poisson bracket `{f, g} = Σ (∂f/∂q ∂g/∂p − ∂f/∂p ∂g/∂q)`. -/
noncomputable def pb (f g : Phase → ℝ) (z : Phase) : ℝ :=
  ∑ blk, ∑ i, (dq f z blk i * dp g z blk i - dp f z blk i * dq g z blk i)

theorem dq_clm (ℓ : Phase →L[ℝ] ℝ) (z : Phase) (blk : Fin 3) (i : Fin 2) :
    dq ℓ z blk i = ℓ (eq' blk i) := by
  simp [dq, ContinuousLinearMap.fderiv]

theorem dp_clm (ℓ : Phase →L[ℝ] ℝ) (z : Phase) (blk : Fin 3) (i : Fin 2) :
    dp ℓ z blk i = ℓ (ep blk i) := by
  simp [dp, ContinuousLinearMap.fderiv]

theorem qc_eq' (b b' : Fin 3) (i i' : Fin 2) :
    qc b i (eq' b' i') = if b = b' ∧ i = i' then 1 else 0 := by
  by_cases hb : b = b'
  · subst hb
    simp [qc, qblk, eq', EuclideanSpace.single_apply]
  · simp [qc, qblk, eq', hb]

theorem qc_ep (b b' : Fin 3) (i i' : Fin 2) : qc b i (ep b' i') = 0 := by
  simp [qc, qblk, ep]

theorem pc_ep (b b' : Fin 3) (i i' : Fin 2) :
    pc b i (ep b' i') = if b = b' ∧ i = i' then 1 else 0 := by
  by_cases hb : b = b'
  · subst hb
    simp [pc, pblk, ep, EuclideanSpace.single_apply]
  · simp [pc, pblk, ep, hb]

theorem pc_eq' (b b' : Fin 3) (i i' : Fin 2) : pc b i (eq' b' i') = 0 := by
  simp [pc, pblk, eq']

/-- Bracket of two linear functions. -/
theorem pb_clm (ℓ₁ ℓ₂ : Phase →L[ℝ] ℝ) (z : Phase) :
    pb ℓ₁ ℓ₂ z = ∑ blk, ∑ i, (ℓ₁ (eq' blk i) * ℓ₂ (ep blk i) - ℓ₁ (ep blk i) * ℓ₂ (eq' blk i)) := by
  simp [pb, dq_clm, dp_clm]

/-- Canonical brackets `{q, p} = δ`. -/
theorem pb_qc_pc (b b' : Fin 3) (i i' : Fin 2) (z : Phase) :
    pb (qc b i) (pc b' i') z = if b = b' ∧ i = i' then 1 else 0 := by
  rw [pb_clm]
  simp only [qc_eq', qc_ep, pc_ep, pc_eq', mul_zero, sub_zero]
  fin_cases b <;> fin_cases b' <;> fin_cases i <;> fin_cases i' <;>
    simp [Fin.sum_univ_two]

/-- The primary constraints `Φᵢ = p_{Xᵢ} − λᵢ`. -/
noncomputable def Phi (i : Fin 2) : Phase →L[ℝ] ℝ := pc 0 i - qc 2 i

/-- The primary constraints `Ξᵢ = p_{λᵢ}`. -/
noncomputable def Xi (i : Fin 2) : Phase →L[ℝ] ℝ := pc 2 i

/-- The four primary constraints, in the order `(Φ₁, Φ₂, Ξ₁, Ξ₂)`. -/
noncomputable def constraints : Fin 4 → Phase →L[ℝ] ℝ := ![Phi 0, Phi 1, Xi 0, Xi 1]

/-- The Dirac matrix of the primary constraints. -/
noncomputable def diracMatrix (z : Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => pb (constraints a) (constraints b) z

theorem diracMatrix_eq (z : Phase) :
    diracMatrix z = !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0] := by
  ext a b
  simp only [diracMatrix, pb_clm]
  fin_cases a <;> fin_cases b <;>
    simp [constraints, Phi, Xi, qc_eq', qc_ep, pc_ep, pc_eq', Fin.sum_univ_three,
      Fin.sum_univ_two]

/-- **Lemma (all four primary constraints are second class)**: `det 𝒞 = 1`. -/
theorem diracMatrix_det (z : Phase) : (diracMatrix z).det = 1 := by
  rw [diracMatrix_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  change -(![0, 0, 0, -1] : Fin 4 → ℝ) 3 = 1
  simp

/-- No nonzero linear combination of the primary constraints is first class. -/
theorem no_first_class (z : Phase) (v : Fin 4 → ℝ)
    (hv : ∀ b, ∑ a, v a * diracMatrix z a b = 0) : v = 0 := by
  have h := fun b => hv b
  simp only [diracMatrix_eq, Fin.sum_univ_four] at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp at h0 h1 h2 h3
  ext a
  fin_cases a <;> simp <;> linarith

/-! ### Preservation of the primary constraints: no secondary constraints -/

/-- Projection onto the reduced coordinates `(X, V, p_X, p_V)`. -/
noncomputable def redProj : Phase →L[ℝ] E2 × E2 × E2 × E2 :=
  (qblk 0).prod ((qblk 1).prod ((pblk 0).prod (pblk 1)))

/-- The multiplier part `u·Φ + w·Ξ` of the total Hamiltonian, a linear function. -/
noncomputable def multiplierPart (u w : E2) : Phase →L[ℝ] ℝ :=
  ∑ i, (u i • Phi i + w i • Xi i)

/-- The total Hamiltonian density `H_T = H₀ + λ·V + u·Φ + w·Ξ`, for an arbitrary
differentiable `H₀` of the reduced variables `(X, V, p_X, p_V)`.  (In the field theory
`∂H₀/∂X` is the full functional derivative `δH₀/δX`; it enters only as an arbitrary
value below.) -/
noncomputable def totalHam (h : E2 × E2 × E2 × E2 → ℝ) (u w : E2) (z : Phase) : ℝ :=
  h (redProj z) + inner ℝ (qblk 2 z) (qblk 1 z) + multiplierPart u w z

/-- `∂H₀/∂Xᵢ`. -/
noncomputable def gradX (h : E2 × E2 × E2 × E2 → ℝ) (y : E2 × E2 × E2 × E2) (i : Fin 2) : ℝ :=
  fderiv ℝ h y (EuclideanSpace.single i 1, 0, 0, 0)

theorem hasFDerivAt_totalHam {h : E2 × E2 × E2 × E2 → ℝ} {z : Phase}
    (hh : DifferentiableAt ℝ h (redProj z)) (u w : E2) :
    HasFDerivAt (totalHam h u w)
      ((fderiv ℝ h (redProj z)).comp redProj +
        (fderivInnerCLM ℝ (qblk 2 z, qblk 1 z)).comp ((qblk 2).prod (qblk 1)) +
        multiplierPart u w) z := by
  have h1 := hh.hasFDerivAt.comp z redProj.hasFDerivAt
  have h2 := (qblk 2).hasFDerivAt.inner ℝ (qblk 1).hasFDerivAt (x := z)
  have h3 := (multiplierPart u w).hasFDerivAt (x := z)
  exact (h1.add h2).add h3

theorem fderiv_totalHam_apply {h : E2 × E2 × E2 × E2 → ℝ} {z : Phase}
    (hh : DifferentiableAt ℝ h (redProj z)) (u w : E2) (e : Phase) :
    fderiv ℝ (totalHam h u w) z e =
      fderiv ℝ h (redProj z) (redProj e) + inner ℝ (qblk 2 z) (qblk 1 e) +
        inner ℝ (qblk 2 e) (qblk 1 z) + multiplierPart u w e := by
  rw [(hasFDerivAt_totalHam hh u w).fderiv]
  simp [fderivInnerCLM_apply]
  ring

theorem qblk_eq' (b b' : Fin 3) (i : Fin 2) :
    qblk b (eq' b' i) = if b = b' then EuclideanSpace.single i 1 else 0 := by
  by_cases h : b = b'
  · subst h
    simp [qblk, eq']
  · simp [qblk, eq', h]

theorem qblk_ep (b b' : Fin 3) (i : Fin 2) : qblk b (ep b' i) = 0 := by
  simp [qblk, ep]

theorem pblk_ep (b b' : Fin 3) (i : Fin 2) :
    pblk b (ep b' i) = if b = b' then EuclideanSpace.single i 1 else 0 := by
  by_cases h : b = b'
  · subst h
    simp [pblk, ep]
  · simp [pblk, ep, h]

theorem pblk_eq' (b b' : Fin 3) (i : Fin 2) : pblk b (eq' b' i) = 0 := by
  simp [pblk, eq']

/-- `{Ξᵢ, f} = −∂f/∂λᵢ` for every `f`. -/
theorem pb_Xi (f : Phase → ℝ) (z : Phase) (i : Fin 2) : pb (Xi i) f z = -dq f z 2 i := by
  simp only [pb, dq_clm, dp_clm, Xi, pc_eq', pc_ep, zero_mul, zero_sub]
  fin_cases i <;> simp [Fin.sum_univ_two]

/-- `{Φᵢ, f} = −∂f/∂p_{λᵢ} − ∂f/∂Xᵢ` for every `f`. -/
theorem pb_Phi (f : Phase → ℝ) (z : Phase) (i : Fin 2) :
    pb (Phi i) f z = -dp f z 2 i - dq f z 0 i := by
  simp only [pb, dq_clm, dp_clm, Phi, ContinuousLinearMap.sub_apply, pc_eq', pc_ep, qc_eq',
    qc_ep]
  fin_cases i <;> simp [Fin.sum_univ_two]

theorem Phi_eq' (j : Fin 2) (b : Fin 3) (i : Fin 2) :
    Phi j (eq' b i) = -(if 2 = b ∧ j = i then 1 else 0) := by
  simp [Phi, pc_eq', qc_eq']

theorem Phi_ep (j : Fin 2) (b : Fin 3) (i : Fin 2) :
    Phi j (ep b i) = if 0 = b ∧ j = i then 1 else 0 := by
  simp [Phi, pc_ep, qc_ep]

theorem Xi_eq' (j : Fin 2) (b : Fin 3) (i : Fin 2) : Xi j (eq' b i) = 0 := by
  simp [Xi, pc_eq']

theorem Xi_ep (j : Fin 2) (b : Fin 3) (i : Fin 2) :
    Xi j (ep b i) = if 2 = b ∧ j = i then 1 else 0 := by
  simp [Xi, pc_ep]

theorem multiplierPart_apply (u w : E2) (e : Phase) :
    multiplierPart u w e = ∑ i, (u i * Phi i e + w i * Xi i e) := by
  simp [multiplierPart]

theorem dq_totalHam_lam {h : E2 × E2 × E2 × E2 → ℝ} {z : Phase}
    (hh : DifferentiableAt ℝ h (redProj z)) (u w : E2) (i : Fin 2) :
    dq (totalHam h u w) z 2 i = qblk 1 z i - u i := by
  have hred : redProj (eq' 2 i) = 0 := by
    simp [redProj, qblk_eq', pblk_eq']
  rw [dq, fderiv_totalHam_apply hh, hred, map_zero, qblk_eq', qblk_eq', multiplierPart_apply]
  simp only [Phi_eq', Xi_eq', if_true, if_neg (by decide : (1 : Fin 3) ≠ 2), inner_zero_right,
    zero_add, mul_zero, add_zero]
  rw [EuclideanSpace.inner_single_left]
  fin_cases i <;> simp <;> ring

theorem dp_totalHam_lam {h : E2 × E2 × E2 × E2 → ℝ} {z : Phase}
    (hh : DifferentiableAt ℝ h (redProj z)) (u w : E2) (i : Fin 2) :
    dp (totalHam h u w) z 2 i = w i := by
  have hred : redProj (ep 2 i) = 0 := by
    simp [redProj, qblk_ep, pblk_ep]
  rw [dp, fderiv_totalHam_apply hh, hred, map_zero, qblk_ep, qblk_ep, multiplierPart_apply]
  simp only [Phi_ep, Xi_ep, inner_zero_right, inner_zero_left, zero_add]
  fin_cases i <;> simp

theorem dq_totalHam_X {h : E2 × E2 × E2 × E2 → ℝ} {z : Phase}
    (hh : DifferentiableAt ℝ h (redProj z)) (u w : E2) (i : Fin 2) :
    dq (totalHam h u w) z 0 i = gradX h (redProj z) i := by
  have hred : redProj (eq' 0 i) = (EuclideanSpace.single i 1, 0, 0, 0) := by
    simp [redProj, qblk_eq', pblk_eq']
  rw [dq, fderiv_totalHam_apply hh, hred, qblk_eq', qblk_eq', multiplierPart_apply]
  simp only [Phi_eq', Xi_eq', if_neg (by decide : (1 : Fin 3) ≠ 0),
    if_neg (by decide : (2 : Fin 3) ≠ 0), inner_zero_right, inner_zero_left, add_zero]
  simp [gradX]

/-- Preservation of `Ξᵢ`: `{Ξᵢ, H_T} = uᵢ − Vᵢ`. -/
theorem preservation_Xi {h : E2 × E2 × E2 × E2 → ℝ} {z : Phase}
    (hh : DifferentiableAt ℝ h (redProj z)) (u w : E2) (i : Fin 2) :
    pb (Xi i) (totalHam h u w) z = u i - qblk 1 z i := by
  rw [pb_Xi, dq_totalHam_lam hh]
  ring

/-- Preservation of `Φᵢ`: `{Φᵢ, H_T} = −∂H₀/∂Xᵢ − wᵢ`. -/
theorem preservation_Phi {h : E2 × E2 × E2 × E2 → ℝ} {z : Phase}
    (hh : DifferentiableAt ℝ h (redProj z)) (u w : E2) (i : Fin 2) :
    pb (Phi i) (totalHam h u w) z = -gradX h (redProj z) i - w i := by
  rw [pb_Phi, dp_totalHam_lam hh, dq_totalHam_X hh]
  ring

/-- **No secondary constraints.** At every phase-space point, the preservation conditions
of all four primary constraints are equivalent to fixing the multipliers,
`u = V` and `w = −∂H₀/∂X`; they impose no condition on the canonical variables. -/
theorem preservation_iff {h : E2 × E2 × E2 × E2 → ℝ} {z : Phase}
    (hh : DifferentiableAt ℝ h (redProj z)) (u w : E2) :
    (∀ i, pb (Xi i) (totalHam h u w) z = 0 ∧ pb (Phi i) (totalHam h u w) z = 0) ↔
      u = qblk 1 z ∧ ∀ i, w i = -gradX h (redProj z) i := by
  simp only [preservation_Xi hh, preservation_Phi hh, sub_eq_zero]
  constructor
  · intro H
    refine ⟨?_, fun i => by linarith [(H i).2]⟩
    ext i
    exact (H i).1
  · rintro ⟨rfl, hw⟩ i
    exact ⟨rfl, by linarith [hw i]⟩

/-- The Dirac algorithm terminates at the primary stage: the preservation conditions have
exactly one multiplier solution at every phase-space point. -/
theorem no_secondary_constraints {h : E2 × E2 × E2 × E2 → ℝ} (hh : Differentiable ℝ h)
    (z : Phase) :
    ∃! uw : E2 × E2, ∀ i, pb (Xi i) (totalHam h uw.1 uw.2) z = 0 ∧
      pb (Phi i) (totalHam h uw.1 uw.2) z = 0 := by
  set w₀ : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![-gradX h (redProj z) 0, -gradX h (redProj z) 1]
  have hw₀ : ∀ i, w₀ i = -gradX h (redProj z) i := by
    intro i
    fin_cases i <;> simp [w₀]
  refine ⟨(qblk 1 z, w₀), (preservation_iff (hh _) _ _).2 ⟨rfl, hw₀⟩, ?_⟩
  rintro ⟨u, w⟩ H
  obtain ⟨hu, hw⟩ := (preservation_iff (hh _) u w).1 H
  simp only [Prod.mk.injEq]
  refine ⟨hu, ?_⟩
  ext i
  rw [hw i, hw₀ i]

/-! ### Counting degrees of freedom -/

/-- The linear map collecting the four primary constraints. -/
noncomputable def constraintMap : Phase →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.pi fun a => ((constraints a : Phase →L[ℝ] ℝ) : Phase →ₗ[ℝ] ℝ)

/-- The primary constraint surface `{Φ = 0, Ξ = 0}`, a linear subspace. -/
noncomputable def constraintSurface : Submodule ℝ Phase := LinearMap.ker constraintMap

theorem mem_constraintSurface (z : Phase) :
    z ∈ constraintSurface ↔ ∀ i, Phi i z = 0 ∧ Xi i z = 0 := by
  simp only [constraintSurface, LinearMap.mem_ker, constraintMap]
  constructor
  · intro h i
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    simp [constraints] at h0 h1 h2 h3
    fin_cases i
    · exact ⟨h0, h2⟩
    · exact ⟨h1, h3⟩
  · intro h
    funext a
    fin_cases a
    · simpa [constraints] using (h 0).1
    · simpa [constraints] using (h 1).1
    · simpa [constraints] using (h 0).2
    · simpa [constraints] using (h 1).2

theorem finrank_E2 : Module.finrank ℝ E2 = 2 := finrank_euclideanSpace_fin

/-- Twelve real canonical dimensions per spatial point. -/
theorem finrank_phase : Module.finrank ℝ Phase = 12 := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype]
  simp

/-- A vector with prescribed components. -/
noncomputable def vec2 (x y : ℝ) : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

@[simp] theorem vec2_zero (x y : ℝ) : vec2 x y 0 = x := by simp [vec2]
@[simp] theorem vec2_one (x y : ℝ) : vec2 x y 1 = y := by simp [vec2]


theorem constraintMap_surjective : Function.Surjective constraintMap := by
  intro t
  refine ⟨(0, ![vec2 (t 0) (t 1), 0, vec2 (t 2) (t 3)]), ?_⟩
  funext a
  fin_cases a <;> simp [constraintMap, constraints, Phi, Xi, pc, qc, pblk, qblk]

/-- The reduced phase space has eight real dimensions per spatial point. -/
theorem finrank_constraintSurface : Module.finrank ℝ constraintSurface = 8 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker constraintMap
  rw [LinearMap.range_eq_top.2 constraintMap_surjective, finrank_top, Module.finrank_fin_fun,
    finrank_phase] at hrn
  unfold constraintSurface
  omega

/-- The reduced phase space is parametrized by the four canonical pairs
`(X, p_X), (V, p_V)`: eliminating `(λ, p_λ)` via `λ = p_X`, `p_λ = 0`. -/
noncomputable def reducedEmbed (y : E2 × E2 × E2 × E2) : Phase :=
  (![y.1, y.2.1, y.2.2.1], ![y.2.2.1, y.2.2.2, 0])

theorem reducedEmbed_mem (y : E2 × E2 × E2 × E2) : reducedEmbed y ∈ constraintSurface := by
  rw [mem_constraintSurface]
  intro i
  simp [reducedEmbed, Phi, Xi, pc, qc, pblk, qblk]

theorem redProj_reducedEmbed (y : E2 × E2 × E2 × E2) : redProj (reducedEmbed y) = y := by
  simp [redProj, reducedEmbed, qblk, pblk]

theorem reducedEmbed_redProj {z : Phase} (hz : z ∈ constraintSurface) :
    reducedEmbed (redProj z) = z := by
  rw [mem_constraintSurface] at hz
  obtain ⟨q, p⟩ := z
  have hl : p 0 = q 2 := by
    ext i
    have h := (hz i).1
    change p 0 i - q 2 i = 0 at h
    linarith
  have hp : p 2 = 0 := by
    ext i
    have h := (hz i).2
    change p 2 i = 0 at h
    exact h
  change (![q 0, q 1, p 0], ![p 0, p 1, 0]) = (q, p)
  refine Prod.ext ?_ ?_
  · funext b
    fin_cases b
    · rfl
    · rfl
    · change p 0 = q 2
      exact hl
  · funext b
    fin_cases b
    · rfl
    · rfl
    · change (0 : E2) = p 2
      exact hp.symm

/-! ### Dirac brackets on the reduced phase space -/

/-- The inverse of the Dirac matrix. -/
def diracInv : Matrix (Fin 4) (Fin 4) ℝ := !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

theorem diracInv_mul (z : Phase) : diracInv * diracMatrix z = 1 := by
  rw [diracMatrix_eq]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [diracInv, Matrix.mul_apply, Fin.sum_univ_four]

theorem diracMatrix_inv (z : Phase) : (diracMatrix z)⁻¹ = diracInv :=
  Matrix.inv_eq_left_inv (diracInv_mul z)

/-- The Dirac bracket `{f, g}_D = {f, g} − {f, c_a} (𝒞⁻¹)_{ab} {c_b, g}`. -/
noncomputable def diracBracket (f g : Phase → ℝ) (z : Phase) : ℝ :=
  pb f g z - ∑ a, ∑ b, pb f (constraints a) z * (diracMatrix z)⁻¹ a b *
    pb (constraints b) g z

/-- Constraints hold strongly for the Dirac bracket. -/
theorem diracBracket_constraint (f : Phase → ℝ) (z : Phase) (c : Fin 4) :
    diracBracket f (constraints c) z = 0 := by
  have key : ∀ a, ∑ b, (diracMatrix z)⁻¹ a b * pb (constraints b) (constraints c) z =
      if a = c then 1 else 0 := by
    intro a
    have := congrFun (congrFun (diracInv_mul z) a) c
    rw [Matrix.mul_apply] at this
    rw [diracMatrix_inv]
    simpa [diracMatrix, Matrix.one_apply] using this
  unfold diracBracket
  have hsum : ∑ a, ∑ b, pb f (constraints a) z * (diracMatrix z)⁻¹ a b *
      pb (constraints b) (constraints c) z = pb f (constraints c) z := by
    simp_rw [mul_assoc, ← Finset.mul_sum, key]
    simp
  rw [hsum, sub_self]

theorem pb_clm_comm (ℓ₁ ℓ₂ : Phase →L[ℝ] ℝ) (z : Phase) : pb ℓ₂ ℓ₁ z = -pb ℓ₁ ℓ₂ z := by
  rw [pb_clm, pb_clm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem pb_qc_qc (b b' : Fin 3) (i i' : Fin 2) (z : Phase) : pb (qc b i) (qc b' i') z = 0 := by
  rw [pb_clm]
  simp [qc_ep]

theorem pb_pc_pc (b b' : Fin 3) (i i' : Fin 2) (z : Phase) : pb (pc b i) (pc b' i') z = 0 := by
  rw [pb_clm]
  simp [pc_eq']

theorem pb_constraint_pcX (c : Fin 4) (j : Fin 2) (z : Phase) :
    pb (constraints c) (pc 0 j) z = 0 := by
  rw [pb_clm]
  fin_cases c <;> simp [constraints, Phi, Xi, qc_eq', qc_ep, pc_eq', pc_ep, Fin.sum_univ_three]

theorem pb_V_constraint (i : Fin 2) (c : Fin 4) (z : Phase) :
    pb (qc 1 i) (constraints c) z = 0 := by
  rw [pb_clm]
  fin_cases c <;> simp [constraints, Phi, Xi, qc_eq', qc_ep, pc_eq', pc_ep]

/-- On the reduced phase space `(X, p_X)` is a canonical pair. -/
theorem diracBracket_X_pX (i j : Fin 2) (z : Phase) :
    diracBracket (qc 0 i) (pc 0 j) z = if i = j then 1 else 0 := by
  unfold diracBracket
  simp only [pb_constraint_pcX, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [pb_qc_pc]
  simp

/-- On the reduced phase space `(V, p_V)` is a canonical pair. -/
theorem diracBracket_V_pV (i j : Fin 2) (z : Phase) :
    diracBracket (qc 1 i) (pc 1 j) z = if i = j then 1 else 0 := by
  unfold diracBracket
  simp only [pb_V_constraint, zero_mul, Finset.sum_const_zero, sub_zero]
  rw [pb_qc_pc]
  simp

/-- The two canonical pairs are mutually independent for the Dirac bracket. -/
theorem diracBracket_X_pV (i j : Fin 2) (z : Phase) :
    diracBracket (qc 0 i) (pc 1 j) z = 0 := by
  unfold diracBracket
  have hc : ∀ c, pb (constraints c) (pc 1 j) z = 0 := by
    intro c
    rw [pb_clm]
    fin_cases c <;> simp [constraints, Phi, Xi, qc_eq', qc_ep, pc_eq', pc_ep, Fin.sum_univ_three]
  simp only [hc, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [pb_qc_pc]
  simp

theorem diracBracket_V_pX (i j : Fin 2) (z : Phase) :
    diracBracket (qc 1 i) (pc 0 j) z = 0 := by
  unfold diracBracket
  simp only [pb_V_constraint, zero_mul, Finset.sum_const_zero, sub_zero]
  rw [pb_qc_pc]
  simp

theorem diracBracket_X_X (i j : Fin 2) (z : Phase) :
    diracBracket (qc 0 i) (qc 0 j) z = 0 := by
  unfold diracBracket
  rw [diracMatrix_inv, pb_qc_qc]
  simp only [pb_clm, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [constraints, diracInv, Phi, Xi, qc_eq', qc_ep, pc_eq', pc_ep, Fin.sum_univ_two]

theorem diracBracket_V_V (i j : Fin 2) (z : Phase) :
    diracBracket (qc 1 i) (qc 1 j) z = 0 := by
  unfold diracBracket
  simp only [pb_V_constraint, zero_mul, Finset.sum_const_zero, sub_zero]
  exact pb_qc_qc _ _ _ _ _

/-! ### Canonical energy -/

/-- The acceleration solving the momentum relation (eq. `invert`). -/
noncomputable def accOfMomentum (M : Model) (b X pV : E2) : E2 :=
  (M.A / (2 * M.κ)) • b - (1 / (2 * M.κ * M.F (inner ℝ X X))) • pV

/-- The partial Legendre transform `𝓗₀` in the acceleration (eq. `H0`). -/
noncomputable def H0 (M : Model) (b : E2) (g : ℝ) (X V pV : E2) : ℝ :=
  -inner ℝ V V + g - M.pot (inner ℝ X X) - inner ℝ pV pV / (4 * M.κ * M.F (inner ℝ X X)) +
    M.A / (2 * M.κ) * inner ℝ pV b + M.Bperp * M.F (inner ℝ X X) * inner ℝ b b

/-- `𝓗₀ = p_V · V̇ − 𝓛_phys` at the acceleration determined by `p_V`. -/
theorem H0_eq_legendre (M : Model) (h : M.Hyp) (b : E2) (g : ℝ) (X V pV : E2)
    (hρ : 0 < inner ℝ X X) :
    H0 M b g X V pV =
      inner ℝ pV (accOfMomentum M b X pV) - Lphys M X V (accOfMomentum M b X pV) b g := by
  have hF := M.F_pos h hρ
  have hκ := h.κ_pos
  unfold H0 Lphys accOfMomentum Model.Bperp
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_comm b pV]
  unfold Model.A Model.C
  field_simp
  ring

/-- The canonical Hamiltonian on the reduced phase space (eq. `Hphys`), in the
reduced coordinates `y = (X, V, p_X, p_V)`. -/
noncomputable def Hphys (M : Model) (b : E2) (g : ℝ) (y : E2 × E2 × E2 × E2) : ℝ :=
  inner ℝ y.2.2.1 y.2.1 + H0 M b g y.1 y.2.1 y.2.2.2

/-- On the constraint surface the total Hamiltonian is the canonical Hamiltonian. -/
theorem totalHam_on_surface (M : Model) (b : E2) (g : ℝ) (u w : E2) {z : Phase}
    (hz : z ∈ constraintSurface) :
    totalHam (Hphys M b g ∘ fun y => (y.1, y.2.1, 0, y.2.2.2)) u w z = Hphys M b g (redProj z) := by
  have hz' := (mem_constraintSurface z).1 hz
  have hmult : multiplierPart u w z = 0 := by
    rw [multiplierPart_apply]
    simp [(hz' _).1, (hz' _).2]
  have hlam : qblk 2 z = pblk 0 z := by
    ext i
    have := (hz' i).1
    simp [Phi, pc, qc] at this
    linarith
  unfold totalHam Hphys
  rw [hmult, add_zero, hlam]
  simp [redProj, Function.comp]
  ring

/-- The canonical energy is unbounded below: `p_X · V` is linear in an unconstrained
momentum (the Ostrogradsky obstruction). -/
theorem Hphys_unbounded_below (M : Model) (b : E2) (g : ℝ) (X V pV : E2) (hV : V ≠ 0)
    (c : ℝ) : ∃ pX : E2, Hphys M b g (X, V, pX, pV) < c := by
  have hVV : 0 < inner ℝ V V := real_inner_self_pos.2 hV
  refine ⟨((c - 1 - H0 M b g X V pV) / inner ℝ V V) • V, ?_⟩
  simp only [Hphys, inner_smul_left, RCLike.conj_to_real]
  field_simp
  linarith

/-- The acceleration-momentum contribution `−|p_V|²/(4κF)` is negative for `p_V ≠ 0`. -/
theorem momentum_term_neg (M : Model) (h : M.Hyp) (X pV : E2) (hρ : 0 < inner ℝ X X)
    (hp : pV ≠ 0) : -(inner ℝ pV pV / (4 * M.κ * M.F (inner ℝ X X))) < 0 := by
  have := real_inner_self_pos.2 hp
  have := M.F_pos h hρ
  have := h.κ_pos
  have : 0 < inner ℝ pV pV / (4 * M.κ * M.F (inner ℝ X X)) := by positivity
  linarith

/-! ### The global `U(1)` charge -/

/-- The rotation `J(x₀, x₁) = (−x₁, x₀)` generating constant phase rotations. -/
noncomputable def Jlin : E2 →ₗ[ℝ] E2 where
  toFun x := vec2 (-x 1) (x 0)
  map_add' x y := by
    ext i
    fin_cases i <;> simp [vec2]; ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [vec2]

noncomputable def Jc : E2 →L[ℝ] E2 := LinearMap.toContinuousLinearMap Jlin

theorem Jc_apply (x : E2) : Jc x = vec2 (-x 1) (x 0) := rfl

/-- The global charge density `𝒬 = p_X · JX + p_V · JV`. -/
noncomputable def charge (z : Phase) : ℝ :=
  inner ℝ (pblk 0 z) (Jc (qblk 0 z)) + inner ℝ (pblk 1 z) (Jc (qblk 1 z))

theorem fderiv_charge_apply (z e : Phase) :
    fderiv ℝ charge z e =
      inner ℝ (pblk 0 z) (Jc (qblk 0 e)) + inner ℝ (pblk 0 e) (Jc (qblk 0 z)) +
        (inner ℝ (pblk 1 z) (Jc (qblk 1 e)) + inner ℝ (pblk 1 e) (Jc (qblk 1 z))) := by
  have h0 := (pblk 0).hasFDerivAt.inner ℝ (Jc.comp (qblk 0)).hasFDerivAt (x := z)
  have h1 := (pblk 1).hasFDerivAt.inner ℝ (Jc.comp (qblk 1)).hasFDerivAt (x := z)
  have hc : HasFDerivAt charge _ z := h0.add h1
  rw [hc.fderiv]
  simp [fderivInnerCLM_apply]

/-- `{q_{b,i}, f} = ∂f/∂p_{b,i}`. -/
theorem pb_qc_left (f : Phase → ℝ) (z : Phase) (b : Fin 3) (i : Fin 2) :
    pb (qc b i) f z = dp f z b i := by
  simp only [pb, dq_clm, dp_clm, qc_eq', qc_ep, zero_mul, sub_zero]
  fin_cases b <;> fin_cases i <;> simp [Fin.sum_univ_two]

/-- `{p_{b,i}, f} = −∂f/∂q_{b,i}`. -/
theorem pb_pc_left (f : Phase → ℝ) (z : Phase) (b : Fin 3) (i : Fin 2) :
    pb (pc b i) f z = -dq f z b i := by
  simp only [pb, dq_clm, dp_clm, pc_eq', pc_ep, zero_mul, zero_sub]
  fin_cases b <;> fin_cases i <;> simp [Fin.sum_univ_two]

theorem inner_single_Jc (x : E2) (i : Fin 2) :
    inner ℝ x (Jc (EuclideanSpace.single i 1)) = -Jc x i := by
  fin_cases i <;> simp [Jc_apply, PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.single_apply]

/-- `𝒬` generates the constant phase rotation: `{X, 𝒬} = JX`, `{V, 𝒬} = JV`,
`{p_X, 𝒬} = J p_X`, `{p_V, 𝒬} = J p_V`, and it does not act on `(λ, p_λ)`. -/
theorem charge_generates (z : Phase) (i : Fin 2) :
    pb (qc 0 i) charge z = Jc (qblk 0 z) i ∧ pb (qc 1 i) charge z = Jc (qblk 1 z) i ∧
      pb (pc 0 i) charge z = Jc (pblk 0 z) i ∧ pb (pc 1 i) charge z = Jc (pblk 1 z) i ∧
      pb (qc 2 i) charge z = 0 ∧ pb (pc 2 i) charge z = 0 := by
  simp only [pb_qc_left, pb_pc_left, dp, dq, fderiv_charge_apply, qblk_ep, pblk_ep, qblk_eq',
    pblk_eq']
  simp [EuclideanSpace.inner_single_left, inner_single_Jc]

/-- The phase rotation by angle `η`. -/
noncomputable def rot (η : ℝ) (x : E2) : E2 :=
  vec2 (Real.cos η * x 0 - Real.sin η * x 1) (Real.sin η * x 0 + Real.cos η * x 1)

theorem inner_rot (η : ℝ) (x y : E2) : inner ℝ (rot η x) (rot η y) = inner ℝ x y := by
  simp only [rot, PiLp.inner_apply, Fin.sum_univ_two, vec2_zero, vec2_one, RCLike.inner_apply,
    conj_trivial]
  have := Real.sin_sq_add_cos_sq η
  linear_combination (x 0 * y 0 + x 1 * y 1) * this

/-- The canonical Hamiltonian is invariant under the global phase rotation applied to all
fields (including `ΔX`). -/
theorem Hphys_rot_invariant (M : Model) (b : E2) (g η : ℝ) (X V pX pV : E2) :
    Hphys M (rot η b) g (rot η X, rot η V, rot η pX, rot η pV) = Hphys M b g (X, V, pX, pV) := by
  simp only [Hphys, H0, inner_rot]

/-- The charge is not a constraint: it does not vanish on the constraint surface. -/
theorem charge_not_constraint : ∃ z ∈ constraintSurface, charge z ≠ 0 := by
  refine ⟨reducedEmbed (vec2 1 0, 0, vec2 0 1, 0), reducedEmbed_mem _, ?_⟩
  simp [charge, reducedEmbed, qblk, pblk, Jc_apply, PiLp.inner_apply, Fin.sum_univ_two]

/-- **Theorem (four regular real configuration degrees of freedom).**  Per spatial point:
twelve canonical dimensions; exactly four primary constraints; Dirac matrix of
determinant one, so all four are second class and none is first class; preservation
fixes all multipliers, so there are no secondary constraints; the reduced phase space
has dimension `12 − 4 = 8`, with canonical pairs `(X, p_X), (V, p_V)`; Dirac's count
`N_conf = (12 − 2·0 − 4)/2 = 4`, two more than an ordinary complex scalar. -/
theorem constraint_count :
    Module.finrank ℝ Phase = 12 ∧
    (∀ z, (diracMatrix z).det = 1) ∧
    (∀ z (v : Fin 4 → ℝ), (∀ b, ∑ a, v a * diracMatrix z a b = 0) → v = 0) ∧
    (∀ {h : E2 × E2 × E2 × E2 → ℝ}, Differentiable ℝ h → ∀ z, ∃! uw : E2 × E2,
      ∀ i, pb (Xi i) (totalHam h uw.1 uw.2) z = 0 ∧ pb (Phi i) (totalHam h uw.1 uw.2) z = 0) ∧
    Module.finrank ℝ constraintSurface = 8 ∧
    (Module.finrank ℝ Phase - 2 * 0 - 4) / 2 = 4 ∧
    (Module.finrank ℝ Phase - 2 * 0 - 4) / 2 - 2 = 2 := by
  refine ⟨finrank_phase, diracMatrix_det, no_first_class,
    fun hh z => no_secondary_constraints hh z, finrank_constraintSurface, ?_, ?_⟩ <;>
    rw [finrank_phase]

end S004

end ReyesMath
