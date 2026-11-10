import Mathlib

/-!
# GC01: an explicit unstable non-minimizing periodic cubic-quintic mode

For the exact fourth-order cubic-quintic Hamiltonian evolution
 i psi_t = (Delta+k^2)^2 psi - beta |psi|^2 psi + gamma |psi|^4 psi,
a homogeneous nonzero background psi=e^(-i omega t) sqrt(s) is
admissible on a periodic torus, with
 omega=k^4-beta*s+gamma*s^2.

Real/imaginary perturbations have Fourier-block symbol
  u_t = Lminus(q)*v,    v_t = -Lplus(q)*u.
The local nonlinear derivative in the real direction is
  -3 beta s+5 gamma s^2, while the imaginary coefficient is
  -beta s+gamma s^2.

At beta=gamma=k=s=q=1, omega=1, Lminus=-1 and Lplus=+1.
The explicit (u,v)=(1,-1) has eigenvalue +1: a growing REAL
linearized Fourier mode, instead of a stable imaginary eigenvalue.

This is an EXACT finite Fourier-symbol obstruction to claiming that
all stationary states of the periodic equation are spectrally stable.
It does not establish nonlinear orbital instability on the periodic
function space, nor transfer to nonzero whole-space H2 backgrounds.
-/

namespace ReyesMath.CubicQuinticPeriodicMode

/-- The local cubic-quintic frequency shift at squared amplitude s. -/
def nonlinearFrequency (beta gamma s : ℝ) : ℝ :=
  -beta * s + gamma * s ^ 2

/-- The exact homogeneous relative-equilibrium frequency. -/
def standingFrequency (beta gamma k s : ℝ) : ℝ :=
  k ^ 4 + nonlinearFrequency beta gamma s

/-- Derivative of the real-direction cubic-quintic nonlinearity. -/
def realNonlinearCoefficient (beta gamma s : ℝ) : ℝ :=
  nonlinearFrequency beta gamma s + 2 * s * (-beta + 2 * gamma * s)

/-- Real and imaginary nonlinear coefficients are different. -/
theorem realNonlinearCoefficient_exact (beta gamma s : ℝ) :
    realNonlinearCoefficient beta gamma s = -3 * beta * s + 5 * gamma * s ^ 2 := by
  unfold realNonlinearCoefficient nonlinearFrequency
  ring

/-- Imaginary-sector Fourier-block coefficient for a homogeneous
relative equilibrium, with q the Fourier spatial wavenumber magnitude. -/
def Lminus (beta gamma k s q : ℝ) : ℝ :=
  (k ^ 2 - q ^ 2) ^ 2 -
    standingFrequency beta gamma k s + nonlinearFrequency beta gamma s

/-- Real-sector coefficient for the same stationary background. -/
def Lplus (beta gamma k s q : ℝ) : ℝ :=
  (k ^ 2 - q ^ 2) ^ 2 -
    standingFrequency beta gamma k s + realNonlinearCoefficient beta gamma s

theorem Lminus_exact (beta gamma k s q : ℝ) :
    Lminus beta gamma k s q = q ^ 4 - 2 * k ^ 2 * q ^ 2 := by
  unfold Lminus standingFrequency nonlinearFrequency
  ring

theorem Lplus_exact (beta gamma k s q : ℝ) :
    Lplus beta gamma k s q =
      q ^ 4 - 2 * k ^ 2 * q ^ 2 - 2 * beta * s + 4 * gamma * s ^ 2 := by
  unfold Lplus standingFrequency realNonlinearCoefficient nonlinearFrequency
  ring

/-- The linearized two-component real Fourier block. -/
def block (Lm Lp : ℝ) (uv : ℝ × ℝ) : ℝ × ℝ :=
  (Lm * uv.2, -Lp * uv.1)

/-- If the real and imaginary stiffnesses have opposite signs, there
is a strictly positive real eigenvalue with a nonzero real eigenvector.
This is spectral instability of the declared 2x2 Fourier block. -/
theorem positive_growth_eigenpair (Lm Lp : ℝ) (h : Lm * Lp < 0) :
    ∃ lambda : ℝ, 0 < lambda ∧
      block Lm Lp (Lm, lambda) =
        (lambda * Lm, lambda * lambda) := by
  have hpos : 0 ≤ -(Lm * Lp) := by linarith
  let lambda : ℝ := Real.sqrt (-(Lm * Lp))
  have hlambda : 0 < lambda := Real.sqrt_pos.mpr (by linarith)
  have hsquare : lambda ^ 2 = -(Lm * Lp) := Real.sq_sqrt hpos
  refine ⟨lambda, hlambda, ?_⟩
  apply Prod.ext
  · simp only [block, Prod.fst, Prod.snd]
    ring
  · simp only [block, Prod.fst, Prod.snd]
    nlinarith [hsquare]

/-- Exact periodic test point: the homogeneous standing wave frequency is 1,
and the unit Fourier mode has opposite-sign linearized stiffnesses. -/
theorem unit_background_symbols :
    standingFrequency 1 1 1 1 = 1 ∧
      Lminus 1 1 1 1 1 = -1 ∧ Lplus 1 1 1 1 1 = 1 := by
  norm_num [standingFrequency, nonlinearFrequency, Lminus, Lplus,
    realNonlinearCoefficient]

/-- A positive eigenvalue +1 exists at the exact unit periodic parameters.
The eigenvector (u,v)=(1,-1) is not the zero perturbation. -/
theorem unit_background_growing_mode :
    block (Lminus 1 1 1 1 1) (Lplus 1 1 1 1 1) (1, -1) =
      ((1 : ℝ) * 1, (1 : ℝ) * (-1)) := by
  norm_num [block, Lminus, Lplus, standingFrequency,
    nonlinearFrequency, realNonlinearCoefficient]


/-! ## Exact exponentially growing linearized mode -/

/-- The two real Fourier amplitudes of the growing linearized mode. -/
noncomputable def growingU (t : ℝ) : ℝ := Real.exp t

noncomputable def growingV (t : ℝ) : ℝ := -(Real.exp t)

/-- The positive-growth Fourier eigenvector generates a classical solution
of the EXACT frozen two-dimensional linearized mode equation, rather
than just an algebraic eigenpair. -/
theorem growingMode_solves_linearized_system (t : ℝ) :
    HasDerivAt growingU (Lminus 1 1 1 1 1 * growingV t) t ∧
    HasDerivAt growingV (-(Lplus 1 1 1 1 1 * growingU t)) t := by
  constructor
  · have h := Real.hasDerivAt_exp t
    convert h using 1 <;>
      norm_num [growingU, growingV, Lminus, standingFrequency,
        nonlinearFrequency]
  · have h := (Real.hasDerivAt_exp t).neg
    convert h using 1 <;>
      norm_num [growingU, growingV, Lplus, standingFrequency,
        nonlinearFrequency, realNonlinearCoefficient]

/-- The real Fourier amplitude is strictly larger at every later time.
This is genuine exponential growth of the linearized finite-mode solution,
not by itself nonlinear instability of the full field PDE. -/
theorem growingMode_amplifies (s t : ℝ) (hst : s < t) :
    growingU s < growingU t := by
  exact Real.exp_lt_exp.mpr hst

/-- The explicit initial mode is the eigenvector used in the algebraic
instability theorem. -/
theorem growingMode_initial :
    growingU 0 = 1 ∧ growingV 0 = -1 := by
  norm_num [growingU, growingV]


/-! ## Exact real growth-rate classification away from the zero threshold -/

/-- If the two linearized Fourier stiffnesses have the SAME sign, their
product is positive and the real Fourier block has no nonzero real
eigenvector at any real growth exponent. This does not prove nonlinear
orbital stability or exclude algebraic/neutral growth at a zero eigenvalue. -/
theorem no_real_growth_eigenvector_of_positive_product
    (Lm Lp lambda u v : ℝ)
    (hprod : 0 < Lm * Lp)
    (hu : Lm * v = lambda * u)
    (hv : -Lp * u = lambda * v) :
    u = 0 ∧ v = 0 := by
  have hcoef : 0 < lambda ^ 2 + Lm * Lp :=
    add_pos_of_nonneg_of_pos (sq_nonneg lambda) hprod
  have hfirst : Lm * v - lambda * u = 0 := sub_eq_zero.mpr hu
  have hsecond : -Lp * u - lambda * v = 0 := sub_eq_zero.mpr hv
  have hzero : (lambda ^ 2 + Lm * Lp) * u = 0 := by
    calc
      (lambda ^ 2 + Lm * Lp) * u =
          -lambda * (Lm * v - lambda * u) -
            Lm * (-Lp * u - lambda * v) := by ring
      _ = 0 := by rw [hfirst, hsecond]; ring
  have hu0 : u = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hcoef)
  have hLm : Lm ≠ 0 := by
    intro h
    have hfalse : (0 : ℝ) < 0 := by simpa [h] using hprod
    exact (lt_irrefl (0 : ℝ)) hfalse
  have hv0 : v = 0 := by
    have hz : Lm * v = 0 := by simpa [hu0] using hu
    exact (mul_eq_zero.mp hz).resolve_left hLm
  exact ⟨hu0, hv0⟩

/-- Exact model-specific spectral dichotomy away from the degenerate
\`Lminus*Lplus = 0\` boundary: a negative product has a positive real
growth eigenvalue, while a positive product has no nonzero real
growth eigenvector. The full periodic PDE stability classification is
a separate function-space problem. -/
theorem nondegenerate_fourier_growth_dichotomy
    (Lm Lp : ℝ) (hzero : Lm * Lp ≠ 0) :
    (Lm * Lp < 0 ∧
      ∃ lambda : ℝ, 0 < lambda ∧
        block Lm Lp (Lm, lambda) =
          (lambda * Lm, lambda * lambda)) ∨
    (0 < Lm * Lp ∧
      ∀ lambda u v : ℝ,
        Lm * v = lambda * u →
        -Lp * u = lambda * v →
        u = 0 ∧ v = 0) := by
  rcases lt_or_gt_of_ne hzero with hneg | hpos
  · exact Or.inl ⟨hneg, positive_growth_eigenpair Lm Lp hneg⟩
  · exact Or.inr ⟨hpos, fun lambda u v hu hv =>
      no_real_growth_eigenvector_of_positive_product Lm Lp lambda u v hpos hu hv⟩

/-! ## Complete wave-number window for the explicit unit background -/

/-- The real-direction stiffness is STRICTLY positive at every real wave
number for the homogeneous unit CQ background. This is a global
polynomial theorem, not a numerical scan over modes. -/
theorem unit_background_Lplus_positive (q : ℝ) :
    0 < Lplus 1 1 1 1 q := by
  rw [Lplus_exact]
  nlinarith [sq_nonneg (q ^ 2 - 1)]

/-- The imaginary-direction stiffness factorizes exactly. -/
theorem unit_background_Lminus_factor (q : ℝ) :
    Lminus 1 1 1 1 q = q ^ 2 * (q ^ 2 - 2) := by
  rw [Lminus_exact]
  ring

/-- Necessary-and-sufficient **real Fourier growth window** at
beta=gamma=k=s=1: the spectral block has a positive real growth
exponent exactly when 0<q²<2. The endpoints q=0 and q²=2
are degenerate and must not be falsely classified as stable.
This does NOT claim nonlinear orbital instability. -/
theorem unit_background_growth_window_iff (q : ℝ) :
    Lminus 1 1 1 1 q * Lplus 1 1 1 1 q < 0 ↔
      0 < q ^ 2 ∧ q ^ 2 < 2 := by
  have hp := unit_background_Lplus_positive q
  rw [unit_background_Lminus_factor]
  constructor
  · intro h
    have hminus : q ^ 2 * (q ^ 2 - 2) < 0 := by
      by_contra hn
      have hnon : 0 ≤ q ^ 2 * (q ^ 2 - 2) := le_of_not_gt hn
      have hprod := mul_nonneg hnon hp.le
      linarith
    have hqpos : 0 < q ^ 2 := by
      by_contra hn
      have hqnon : q ^ 2 ≤ 0 := le_of_not_gt hn
      have hqzero : q ^ 2 = 0 := le_antisymm hqnon (sq_nonneg q)
      rw [hqzero] at hminus
      norm_num at hminus
    have hqlt : q ^ 2 < 2 := by
      by_contra hn
      have hge : 0 ≤ q ^ 2 - 2 := by linarith
      have hmul := mul_nonneg hqpos.le hge
      linarith
    exact ⟨hqpos, hqlt⟩
  · rintro ⟨hqpos, hqlt⟩
    have hm : q ^ 2 * (q ^ 2 - 2) < 0 :=
      mul_neg_of_pos_of_neg hqpos (by linarith)
    exact mul_neg_of_neg_of_pos hm hp

/-- Every real Fourier wave number in the strict unstable band admits
an explicit nonzero growing real eigenvector. -/
theorem unit_background_growth_eigenpair_on_band
    (q : ℝ) (hq0 : 0 < q ^ 2) (hq2 : q ^ 2 < 2) :
    ∃ lambda : ℝ, 0 < lambda ∧
      block (Lminus 1 1 1 1 q) (Lplus 1 1 1 1 q)
        (Lminus 1 1 1 1 q, lambda) =
      (lambda * Lminus 1 1 1 1 q, lambda * lambda) := by
  apply positive_growth_eigenpair
  exact (unit_background_growth_window_iff q).2 ⟨hq0, hq2⟩

/-- The two band endpoints are genuine *zero* imaginary-sector stiffness,
so a strict positive-growth claim must not include them. -/
theorem unit_background_growth_thresholds
    (q : ℝ) (hq : q = 0 ∨ q ^ 2 = 2) :
    Lminus 1 1 1 1 q = 0 := by
  rw [unit_background_Lminus_factor]
  rcases hq with hzero | htwo
  · rw [hzero]
    norm_num
  · rw [htwo]
    ring

/-- Outside the closed growth band, all nonzero Fourier blocks have
positive stiffness product and no nonzero REAL exponential eigenvector.
This is strictly weaker than nonlinear or orbital stability. -/
theorem unit_background_no_real_growth_outside_band
    (q : ℝ) (hq : 2 < q ^ 2) :
    ∀ lambda u v : ℝ,
      Lminus 1 1 1 1 q * v = lambda * u →
      -Lplus 1 1 1 1 q * u = lambda * v →
      u = 0 ∧ v = 0 := by
  have hm : 0 < Lminus 1 1 1 1 q := by
    rw [unit_background_Lminus_factor]
    have hqpos : 0 < q ^ 2 := by linarith
    exact mul_pos hqpos (by linarith)
  have hp := unit_background_Lplus_positive q
  have hprod : 0 < Lminus 1 1 1 1 q * Lplus 1 1 1 1 q :=
    mul_pos hm hp
  intro lambda u v hu hv
  exact no_real_growth_eigenvector_of_positive_product
    (Lminus 1 1 1 1 q) (Lplus 1 1 1 1 q) lambda u v hprod hu hv

end ReyesMath.CubicQuinticPeriodicMode
