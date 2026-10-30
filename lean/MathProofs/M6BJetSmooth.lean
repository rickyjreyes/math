import Mathlib
import MathProofs.M6BCurvature

/-!
# Exact C∞ regularity of the nonlinear M6B complex jet closure

The real-smooth jet map is (z,w) ↦ -w conjugate(z)/D(|z|²).
The proof uses the strictly positive regularization denominator and
the real-linear continuous complex structure; node values are allowed.
-/

noncomputable section

namespace ReyesMath.M6B

theorem curvature_contDiff (ε α lam S : ℝ)
    (hε : 0 < ε) (hlam : 0 ≤ lam) (hS : 0 < S) :
    ContDiff ℝ ⊤ (fun p : ℂ × ℂ => curvature ε α lam S p.1 p.2) := by
  have hz : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.1) := by fun_prop
  have hw : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.2) := by fun_prop
  have hn : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => Complex.normSq p.1) := by
    simpa only [Complex.normSq_eq_norm_sq] using (ContDiff.norm_sq (𝕜 := ℂ) hz)
  have hSpos : ∀ p : ℂ × ℂ, S + Complex.normSq p.1 ≠ 0 := by
    intro p
    have hnonneg := Complex.normSq_nonneg p.1
    exact ne_of_gt (by linarith)
  have hfrac : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ =>
        lam * Complex.normSq p.1 / (S + Complex.normSq p.1)) := by
    have ha := ContDiff.const_smul lam hn
    have hb : ContDiff ℝ ⊤
        (fun p : ℂ × ℂ => S + Complex.normSq p.1) :=
      (contDiff_const (c := S)).add hn
    have hc := ContDiff.div ha hb hSpos
    simpa only [smul_eq_mul] using hc
  have hExp : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ => Real.exp (-2 * α * Complex.normSq p.1)) := by
    have h := ContDiff.const_smul (-2 * α) hn
    simpa only [smul_eq_mul] using h.exp
  have hden : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ => denominator ε α lam S (Complex.normSq p.1)) := by
    have hfac : ContDiff ℝ ⊤
        (fun p : ℂ × ℂ => 1 + lam * Complex.normSq p.1 / (S + Complex.normSq p.1)) :=
      (contDiff_const (c := (1 : ℝ))).add hfrac
    have hmul := (ContDiff.const_smul (ε ^ 2) hExp).mul hfac
    have h := hn.add hmul
    simpa [denominator, smul_eq_mul] using h
  have hdenNZ : ∀ p : ℂ × ℂ,
      denominator ε α lam S (Complex.normSq p.1) ≠ 0 := by
    intro p
    exact ne_of_gt (denominator_pos ε α lam S (Complex.normSq p.1)
      hε hlam hS (Complex.normSq_nonneg p.1))
  have hdenInv : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ =>
        (denominator ε α lam S (Complex.normSq p.1))⁻¹) :=
    ContDiff.inv hden hdenNZ
  have hdenComplex : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ =>
        (((denominator ε α lam S (Complex.normSq p.1))⁻¹ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hdenInv
  have hconj : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ => (starRingEnd ℂ) p.1) := by
    simpa using (Complex.conjCLE.contDiff.comp hz)
  have hnum : ContDiff ℝ ⊤
      (fun p : ℂ × ℂ => -(p.2 * (starRingEnd ℂ) p.1)) :=
    (hw.mul hconj).neg
  have hresult := hnum.mul hdenComplex
  convert hresult using 1
  funext p
  simp [curvature, div_eq_mul_inv]

end ReyesMath.M6B
