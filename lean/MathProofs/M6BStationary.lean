import Mathlib
import MathProofs.M6BCurvature

/-!
# M6B: exact trigonometric stationary counterexample, algebraic layer

The two square Dirichlet eigenmodes in the manuscript are given
*explicitly* by sin(x)sin(2y) and sin(2x)sin(y).
Here we prove the two complex fields have exactly the same intensity
and cannot be related by any constant phase. These statements are for
the actual trigonometric fields, not a finite sample surrogate.

Pending to finish the main theorem: the actual Laplacian eigenvalue,
boundary regularity, and exact L² mass integral on (0,π)².
-/

noncomputable section

namespace ReyesMath.M6B

def squareModeF (x y : ℝ) : ℝ :=
  Real.sin x * Real.sin (2 * y)

def squareModeG (x y : ℝ) : ℝ :=
  Real.sin (2 * x) * Real.sin y

def squarePlus (c x y : ℝ) : ℂ :=
  Complex.mk (c * squareModeF x y) (c * squareModeG x y)

def squareMinus (c x y : ℝ) : ℂ :=
  Complex.mk (c * squareModeF x y) (-c * squareModeG x y)

/-- Complex conjugation reverses the imaginary mode and preserves
pointwise intensity, at *every* point of the square. -/
theorem square_intensity_eq (c x y : ℝ) :
    Complex.normSq (squarePlus c x y) =
      Complex.normSq (squareMinus c x y) := by
  simp [squarePlus, squareMinus, Complex.normSq_apply]

private theorem modeF_P :
    squareModeF (Real.pi / 2) (Real.pi / 4) = 1 := by
  unfold squareModeF
  have h : (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [h]
  norm_num

private theorem modeG_P :
    squareModeG (Real.pi / 2) (Real.pi / 4) = 0 := by
  unfold squareModeG
  have h : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
  rw [h, Real.sin_pi]
  ring

private theorem modeF_Q :
    squareModeF (Real.pi / 4) (Real.pi / 2) = 0 := by
  unfold squareModeF
  have h : (2 : ℝ) * (Real.pi / 2) = Real.pi := by ring
  rw [h, Real.sin_pi]
  ring

private theorem modeG_Q :
    squareModeG (Real.pi / 4) (Real.pi / 2) = 1 := by
  unfold squareModeG
  have h : (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [h]
  norm_num

/-- There is no constant complex phase (not even of arbitrary modulus)
turning the plus field into the minus field, for nonzero amplitude c.
The proof uses the two actual points inside (0,π)². -/
theorem square_not_related_by_constant_phase (c : ℝ) (hc : c ≠ 0) :
    ¬ ∃ u : ℂ, ∀ x y : ℝ,
      squareMinus c x y = u * squarePlus c x y := by
  rintro ⟨u, h⟩
  have hP := h (Real.pi / 2) (Real.pi / 4)
  have hQ := h (Real.pi / 4) (Real.pi / 2)
  have hP' : (c : ℂ) = u * (c : ℂ) := by
    simpa [squarePlus, squareMinus, modeF_P, modeG_P] using hP
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hu : u = 1 := by
    have hh : (u - 1) * (c : ℂ) = 0 := by
      calc
        (u - 1) * (c : ℂ) = u * (c : ℂ) - (c : ℂ) := by ring
        _ = 0 := by rw [← hP']; ring
    rcases mul_eq_zero.mp hh with ha | hb
    · exact sub_eq_zero.mp ha
    · exact False.elim (hc' hb)
  rw [hu, one_mul] at hQ
  have him := congrArg Complex.im hQ
  simp [squareMinus, squarePlus, modeF_Q, modeG_Q] at him
  exact hc (by linarith)

/-- The two actual trigonometric fields have equal stationary curvature
when evaluated at their shared Laplace eigenvalue -5. -/
theorem square_equal_eigen_curvature (ε α lam S c x y : ℝ) :
    curvature ε α lam S (squarePlus c x y) (-5 * squarePlus c x y) =
      curvature ε α lam S (squareMinus c x y) (-5 * squareMinus c x y) :=
  equal_intensity_eigenjets ε α lam S _ _ (square_intensity_eq c x y)

/-- The four edges of the manuscript's closed Dirichlet square. -/
def onSquareEdge (x y : ℝ) : Prop :=
  x = 0 ∨ x = Real.pi ∨ y = 0 ∨ y = Real.pi

/-- Both actual trigonometric modes vanish on every edge. -/
theorem square_modes_dirichlet (x y : ℝ) (h : onSquareEdge x y) :
    squareModeF x y = 0 ∧ squareModeG x y = 0 := by
  rcases h with hx | hx | hy | hy
  · subst x
    simp [squareModeF, squareModeG]
  · subst x
    simp [squareModeF, squareModeG]
  · subst y
    simp [squareModeF, squareModeG]
  · subst y
    simp [squareModeF, squareModeG]

/-- Both explicit complex modes have the exact homogeneous Dirichlet data. -/
theorem square_fields_dirichlet (c x y : ℝ) (h : onSquareEdge x y) :
    squarePlus c x y = 0 ∧ squareMinus c x y = 0 := by
  obtain ⟨hf, hg⟩ := square_modes_dirichlet x y h
  simp [squarePlus, squareMinus, hf, hg]
  rfl

end ReyesMath.M6B
