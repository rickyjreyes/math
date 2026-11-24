import MathProofs.GC01VortexEstimates

/-! GC01: exact scalar pieces of the continuum angular spectral reduction.
The radial operator domains, spectral theory, and integration are separate
analytical obligations. These declarations do not assert continuum certification. -/
namespace ReyesMath.GC01SpectralReduction

/-- Nonlinear part of the normalized action density (E + ω M)/2. -/
def potential (β γ a b : ℝ) : ℝ :=
  -β / 4 * (a^2 + b^2)^2 + γ / 6 * (a^2 + b^2)^3

/-- Pointwise real Hessian of the same density. -/
def hessian (β γ a b x y : ℝ) : ℝ :=
  (-β * (a^2+b^2) + γ * (a^2+b^2)^2) * (x^2+y^2) +
  (-2*β + 4*γ*(a^2+b^2)) * (a*x+b*y)^2

/-- Exact central difference, including the higher order terms. -/
theorem central_difference (β γ a b x y t : ℝ) :
    potential β γ (a+t*x) (b+t*y) +
    potential β γ (a-t*x) (b-t*y) - 2*potential β γ a b =
    t^2 * hessian β γ a b x y +
      t^4 * ((-β/2 + γ*(a^2+b^2))*(x^2+y^2)^2 +
        4*γ*(a*x+b*y)^2*(x^2+y^2)) +
      t^6 * (γ/3)*(x^2+y^2)^3 := by
  unfold potential hessian
  ring

/-- Exact decomposition of the shifted Hessian into sums of squares. -/
theorem shifted_hessian_identity (β γ a b x y : ℝ) :
    (a^2+b^2) * (20*γ*hessian β γ a b x y + 9*β^2*(x^2+y^2)) =
    (10*γ*(a^2+b^2)-3*β)^2*(a*x+b*y)^2 +
    (5*(2*γ*(a^2+b^2)-β)^2+4*β^2)*(a*y-b*x)^2 := by
  unfold hessian
  ring

/-- Uniform lower bound -9β²/(20γ) for the nonlinear Hessian. -/
theorem hessian_lower (β γ a b x y : ℝ) (hγ : 0 < γ) :
    20*γ*hessian β γ a b x y + 9*β^2*(x^2+y^2) ≥ 0 := by
  have hs : 0 ≤ a^2+b^2 := by positivity
  rcases eq_or_lt_of_le hs with hz | hp
  · have ha2 : a*a = 0 := by nlinarith [sq_nonneg b]
    have hb2 : b*b = 0 := by nlinarith [sq_nonneg a]
    have ha : a = 0 := (mul_eq_zero.mp ha2).elim id id
    have hb : b = 0 := (mul_eq_zero.mp hb2).elim id id
    simp [ha, hb, hessian] <;> positivity
  · have hprod : 0 ≤ (a^2+b^2) *
        (20*γ*hessian β γ a b x y + 9*β^2*(x^2+y^2)) := by
      rw [shifted_hessian_identity]
      positivity
    by_contra! hn
    exact (not_lt_of_ge hprod) (mul_neg_of_pos_of_neg hp hn)

/-- High angular momentum bound: x = sqrt(T), y = sqrt(M),
a = C R² / j², b = k². The cutoff is quantitative, including k ≠ 0. -/
theorem high_mode_coercivity (x y a b ω : ℝ)
    (hc : a*b + a^2/2 ≤ ω/4) :
    x^2 + (ω/2-a*b)*y^2 - a*x*y ≥ x^2/2 + ω/4*y^2 := by
  have h := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg y)
  nlinarith only [h, sq_nonneg (x-a*y)]

/-- Algebra behind the paired angular eigenproblem: its diagonal potential
is the mean of radial and tangential coefficients; coupling is half their
difference. -/
theorem angular_coefficients (β γ s : ℝ) :
    ((-3*β*s+5*γ*s^2)+(-β*s+γ*s^2))/2 = -2*β*s+3*γ*s^2 ∧
    ((-3*β*s+5*γ*s^2)-(-β*s+γ*s^2))/2 = -β*s+2*γ*s^2 := by
  constructor <;> ring

/-- Negative definite Hamiltonian quadratic energy need not yield real growth:
the generator (x,y) ↦ (-y,x) preserves x²+y² exactly. -/
theorem negative_energy_rotation (x y : ℝ) :
    2*x*(-y) + 2*y*x = 0 ∧ -(x^2+y^2) ≤ 0 := by
  constructor
  · ring
  · nlinarith [sq_nonneg x, sq_nonneg y]

/-- The same rotation generator has no nonzero real eigenvector. This is
a finite-dimensional counterexample, not a PDE stationary profile. -/
theorem rotation_no_real_eigenvector (x y λ : ℝ)
    (hx : -y = λ*x) (hy : x = λ*y) : x = 0 ∧ y = 0 := by
  have h : λ^2*y = -y := by
    calc
      λ^2*y = λ*(λ*y) := by ring
      _ = λ*x := by rw [← hy]
      _ = -y := hx.symm
  have hf : (λ^2+1)*y = 0 := by nlinarith only [h]
  have hp : 0 < λ^2+1 := by positivity
  have hy0 : y = 0 := (mul_eq_zero.mp hf).resolve_left (ne_of_gt hp)
  exact ⟨by simpa [hy0] using hy, hy0⟩

end ReyesMath.GC01SpectralReduction
