import Mathlib
import MathProofs.M6BStationaryTheorem

/-!
# M6B forcing: exact real-valued smooth stationary source on the square

The source is the manuscript's explicit F_m(x,y), not a free
forcing or an assumed equality. The wave amplitude is the exact
arbitrary-prescribed-positive-mass normalization.
-/

noncomputable section
namespace ReyesMath.M6B

def density (m x y : ℝ) : ℝ :=
  (amplitude m) ^ 2 *
    (Real.sin x ^ 2 * Real.sin (2 * y) ^ 2 +
      Real.sin (2 * x) ^ 2 * Real.sin y ^ 2)

theorem density_eq_normSq (m x y : ℝ) :
    density m x y = Complex.normSq (squarePlus (amplitude m) x y) := by
  exact (square_normSq_formula (amplitude m) x y).symm

theorem density_nonneg (m x y : ℝ) : 0 ≤ density m x y := by
  rw [density_eq_normSq]
  exact Complex.normSq_nonneg _

/-- The real forcing F_m=5 A_m / (A_m+ε²exp(-2αA_m)). -/
def prescribedForcing (ε α m : ℝ) (p : ℝ × ℝ) : ℝ :=
  5 * density m p.1 p.2 /
    (density m p.1 p.2 +
      ε ^ 2 * Real.exp (-2 * α * density m p.1 p.2))

theorem prescribedForcing_smooth (ε α m : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ⊤ (prescribedForcing ε α m) := by
  have hDne : ∀ p : ℝ × ℝ,
      density m p.1 p.2 +
        ε ^ 2 * Real.exp (-2 * α * density m p.1 p.2) ≠ 0 := by
    intro p
    have h := denominator_pos ε α 0 1 (density m p.1 p.2)
      hε (by norm_num) (by norm_num) (density_nonneg m p.1 p.2)
    exact ne_of_gt (by simpa [denominator_canonical] using h)
  have hn : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => 5 * density m p.1 p.2) := by
    unfold density
    fun_prop
  have hd : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => density m p.1 p.2 +
        ε ^ 2 * Real.exp (-2 * α * density m p.1 p.2)) := by
    unfold density
    fun_prop
  exact ContDiff.div hn hd hDne

/-- Exact eigenjet identity for the canonical regularized curvature,
with an *explicit real* value. -/
theorem canonical_eigenjet_forcing (ε α : ℝ) (z : ℂ) :
    curvature ε α 0 1 z (-5 * z) =
      (((5 * Complex.normSq z) /
        (Complex.normSq z + ε ^ 2 *
          Real.exp (-2 * α * Complex.normSq z)) : ℝ) : ℂ) := by
  have hsq : z * (starRingEnd ℂ) z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  unfold curvature
  rw [denominator_canonical]
  calc
    -((-5 * z) * (starRingEnd ℂ) z) /
        ((Complex.normSq z + ε ^ 2 *
          Real.exp (-2 * α * Complex.normSq z) : ℝ) : ℂ) =
      (5 * (z * (starRingEnd ℂ) z)) /
        ((Complex.normSq z + ε ^ 2 *
          Real.exp (-2 * α * Complex.normSq z) : ℝ) : ℂ) := by ring
    _ = _ := by
      rw [hsq]
      push_cast
      ring

theorem stationary_plus_has_prescribed_forcing (ε α m x y : ℝ) :
    canonicalStationaryMap ε α (squarePlus (amplitude m)) x y =
      (prescribedForcing ε α m (x, y) : ℂ) := by
  unfold canonicalStationaryMap
  rw [squarePlus_laplace, canonical_eigenjet_forcing]
  simp only [prescribedForcing, ← density_eq_normSq]

theorem stationary_minus_has_prescribed_forcing (ε α m x y : ℝ) :
    canonicalStationaryMap ε α (squareMinus (amplitude m)) x y =
      (prescribedForcing ε α m (x, y) : ℂ) := by
  rw [← stationary_plus_has_prescribed_forcing]
  exact (stationary_curvature_equal ε α 1 (amplitude m) x y).symm

end ReyesMath.M6B
