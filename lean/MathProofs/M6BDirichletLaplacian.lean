import Mathlib
import MathProofs.M6BStationary

/-!
# M6B: exact continuum Laplacian of the manuscript's Dirichlet fields

Derivatives below are ordinary one-dimensional real derivatives of smooth
functions, combined as the Cartesian Laplacian ∂ₓ² + ∂ᵧ² on ℝ².
No sampled grid, finite difference, or formal Laplace-eigenvalue hypothesis
enters the theorem.
-/

noncomputable section
namespace ReyesMath.M6B

private theorem deriv_sin_linear_const (k a x : ℝ) :
    deriv (fun t : ℝ => Real.sin (k * t) * a) x =
      k * Real.cos (k * x) * a := by
  have hlin : HasDerivAt (fun t : ℝ => k * t) k x := by
    convert (hasDerivAt_id x).const_mul k using 1 <;> ring
  have h := ((Real.hasDerivAt_sin (k * x)).comp x hlin).mul_const a
  convert h.deriv using 1 <;> ring

private theorem deriv_cos_linear_const (k a x : ℝ) :
    deriv (fun t : ℝ => k * Real.cos (k * t) * a) x =
      -(k ^ 2) * Real.sin (k * x) * a := by
  have hlin : HasDerivAt (fun t : ℝ => k * t) k x := by
    convert (hasDerivAt_id x).const_mul k using 1 <;> ring
  have h := (((Real.hasDerivAt_cos (k * x)).comp x hlin).const_mul k).mul_const a
  convert h.deriv using 1 <;> ring

/-- The actual second derivative of the smooth sine function of scaled argument. -/
theorem second_deriv_sine_product (k a x : ℝ) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => Real.sin (k * s) * a) t) x =
      -(k ^ 2) * Real.sin (k * x) * a := by
  have hfun : (fun t : ℝ =>
      deriv (fun s : ℝ => Real.sin (k * s) * a) t) =
      (fun t : ℝ => k * Real.cos (k * t) * a) := by
    funext t
    exact deriv_sin_linear_const k a t
  rw [hfun]
  exact deriv_cos_linear_const k a x

/-- The two-variable separable sine mode in the actual manuscript. -/
def sineMode (k l c x y : ℝ) : ℝ :=
  Real.sin (k * x) * (Real.sin (l * y) * c)

/-- Actual Cartesian two-dimensional Laplacian, using iterated
partial derivatives in each coordinate. -/
def laplaceReal (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => deriv (fun s => f s y) t) x +
  deriv (fun t => deriv (fun s => f x s) t) y

/-- A separable sine mode is a classical Laplacian eigenfunction. -/
theorem laplace_sineMode (k l c x y : ℝ) :
    laplaceReal (sineMode k l c) x y =
      -(k ^ 2 + l ^ 2) * sineMode k l c x y := by
  have hfirst :
      deriv (fun t => deriv (fun s => sineMode k l c s y) t) x =
      -(k ^ 2) * Real.sin (k * x) * (Real.sin (l * y) * c) := by
    change deriv (fun t =>
      deriv (fun s => Real.sin (k * s) * (Real.sin (l * y) * c)) t) x = _
    exact second_deriv_sine_product k (Real.sin (l * y) * c) x
  have hfun : (fun t : ℝ => sineMode k l c x t) =
      (fun t : ℝ => Real.sin (l * t) * (Real.sin (k * x) * c)) := by
    funext t
    unfold sineMode
    ring
  have hsecond :
      deriv (fun t => deriv (fun s => sineMode k l c x s) t) y =
      -(l ^ 2) * Real.sin (l * y) * (Real.sin (k * x) * c) := by
    rw [show (fun t => deriv (fun s => sineMode k l c x s) t) =
      (fun t => deriv (fun s => Real.sin (l * s) *
        (Real.sin (k * x) * c)) t) from by
          funext t
          exact congrArg (fun f : ℝ → ℝ => deriv f t) hfun]
    exact second_deriv_sine_product l (Real.sin (k * x) * c) y
  unfold laplaceReal
  rw [hfirst, hsecond]
  unfold sineMode
  ring

/-- Cartesian Laplacian of a complex field, componentwise. -/
def laplaceComplex (ψ : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  Complex.mk (laplaceReal (fun s t => (ψ s t).re) x y)
    (laplaceReal (fun s t => (ψ s t).im) x y)

/-- The *actual* ψ₊ field satisfies Δψ₊ = -5ψ₊ at every point. -/
theorem squarePlus_laplace (c x y : ℝ) :
    laplaceComplex (squarePlus c) x y = -5 * squarePlus c x y := by
  have hre : (fun s t => (squarePlus c s t).re) = sineMode 1 2 c := by
    funext s t
    simp [squarePlus, squareModeF, sineMode]
    ring
  have him : (fun s t => (squarePlus c s t).im) = sineMode 2 1 c := by
    funext s t
    simp [squarePlus, squareModeG, sineMode]
    ring
  unfold laplaceComplex
  rw [hre, him, laplace_sineMode, laplace_sineMode]
  apply Complex.ext
  · simp [squarePlus, squareModeF, sineMode, Complex.mul_re]
    ring
  · simp [squarePlus, squareModeG, sineMode, Complex.mul_im]
    ring

/-- The *actual* ψ₋ field satisfies Δψ₋ = -5ψ₋ at every point. -/
theorem squareMinus_laplace (c x y : ℝ) :
    laplaceComplex (squareMinus c) x y = -5 * squareMinus c x y := by
  have hre : (fun s t => (squareMinus c s t).re) = sineMode 1 2 c := by
    funext s t
    simp [squareMinus, squareModeF, sineMode]
    ring
  have him : (fun s t => (squareMinus c s t).im) = sineMode 2 1 (-c) := by
    funext s t
    simp [squareMinus, squareModeG, sineMode]
    ring
  unfold laplaceComplex
  rw [hre, him, laplace_sineMode, laplace_sineMode]
  apply Complex.ext
  · simp [squareMinus, squareModeF, sineMode, Complex.mul_re]
    ring
  · simp [squareMinus, squareModeG, sineMode, Complex.mul_im]
    ring

/-- The exact nonlinear curvature maps of the two smooth fields coincide,
using their *computed* Cartesian Laplacians (no eigenjet assumption). -/
theorem stationary_curvature_equal
    (ε α S c x y : ℝ) :
    curvature ε α 0 S (squarePlus c x y)
        (laplaceComplex (squarePlus c) x y) =
      curvature ε α 0 S (squareMinus c x y)
        (laplaceComplex (squareMinus c) x y) := by
  rw [squarePlus_laplace, squareMinus_laplace]
  exact square_equal_eigen_curvature ε α 0 S c x y

end ReyesMath.M6B
