import Mathlib
import MathProofs.M6BCurvature

/-!
# M6B structural smoothness of the actual complex two-jet constitutive map

The jet coordinates (z,w) are the field value and its Cartesian
Laplacian.  This proves the full C∞ real-differentiable regularized
closure on all complex jets, including nodes. All denominators are
proved positive; no nonvanishing-field hypothesis is needed.
-/

noncomputable section

namespace ReyesMath.M6B

/-- For admissible λ≥0, the exact nonlinear quotient is C∞ as a
real map from the complex field/Laplacian jet ℂ×ℂ to ℂ. -/
theorem curvature_contDiff (ε α lam S : ℝ)
    (hε : 0 < ε) (hlam : 0 ≤ lam) (hS : 0 < S) :
    ContDiff ℝ ⊤ (fun p : ℂ × ℂ => curvature ε α lam S p.1 p.2) := by
  have hz : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.1) := by fun_prop
  have hw : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.2) := by fun_prop
  have hn : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => Complex.normSq p.1) := by
    simpa only [Complex.normSq_eq_norm_sq] using hz.norm_sq
  have hA : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ =>
        Real.exp (-2 * α * Complex.normSq p.1)) :=
    (hn.const_mul (-2 * α)).exp
  have hSden : ∀ p : ℂ × ℂ, S + Complex.normSq p.1 ≠ 0 := by
    intro p
    have hn0 := Complex.normSq_nonneg p.1
    exact ne_of_gt (by linarith)
  have hfrac : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ =>
        lam * Complex.normSq p.1 / (S + Complex.normSq p.1)) :=
    (hn.const_mul lam).div (contDiff_const.add hn) hSden
  have hD : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ => denominator ε α lam S (Complex.normSq p.1)) := by
    unfold denominator
    exact hn.add ((hA.const_mul (ε ^ 2)).mul (contDiff_const.add hfrac))
  have hDc : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ =>
        ((denominator ε α lam S (Complex.normSq p.1) : ℝ) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hD
  have hDne : ∀ p : ℂ × ℂ,
      (((denominator ε α lam S (Complex.normSq p.1) : ℝ) : ℂ)) ≠ 0 := by
    intro p
    have h := denominator_pos ε α lam S (Complex.normSq p.1)
      hε hlam hS (Complex.normSq_nonneg p.1)
    exact_mod_cast h.ne'
  have hconj : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => (starRingEnd ℂ) p.1) := by
    simpa using (Complex.conjCLE.contDiff.comp hz)
  have hnum : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ => -(p.2 * (starRingEnd ℂ) p.1)) :=
    (hw.mul hconj).neg
  simpa only [curvature, neg_div] using hnum.div hDc hDne

end ReyesMath.M6B
