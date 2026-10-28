import Mathlib
import MathProofs.M6BDirichletLaplacian

/-!
# Genuine C∞ regularity of M6B sine fields on all of ℝ²

The fields are explicitly the manuscript's trigonometric functions.
Smoothness on all of ℝ² implies smoothness on the closed Dirichlet square.
-/

noncomputable section
open scoped ContDiff

namespace ReyesMath.M6B

theorem squareModeF_smooth :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => squareModeF p.1 p.2) := by
  unfold squareModeF
  fun_prop

theorem squareModeG_smooth :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => squareModeG p.1 p.2) := by
  unfold squareModeG
  fun_prop

theorem squarePlus_smooth (c : ℝ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => squarePlus c p.1 p.2) := by
  have hr : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => c * squareModeF p.1 p.2) := by
    unfold squareModeF
    fun_prop
  have hi : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => c * squareModeG p.1 p.2) := by
    unfold squareModeG
    fun_prop
  have hp := hr.prodMk hi
  have h := Complex.equivRealProdCLM.symm.contDiff.comp hp
  convert h using 1
  funext p
  rfl

theorem squareMinus_smooth (c : ℝ) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => squareMinus c p.1 p.2) := by
  have hr : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => c * squareModeF p.1 p.2) := by
    unfold squareModeF
    fun_prop
  have hi : ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => -c * squareModeG p.1 p.2) := by
    unfold squareModeG
    fun_prop
  have hp := hr.prodMk hi
  have h := Complex.equivRealProdCLM.symm.contDiff.comp hp
  convert h using 1
  funext p
  simp [squareMinus]
  ring

end ReyesMath.M6B
