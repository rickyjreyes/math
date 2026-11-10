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
  · simp only [block, Prod.fst]
    ring
  · simp only [block, Prod.snd]
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

end ReyesMath.CubicQuinticPeriodicMode
