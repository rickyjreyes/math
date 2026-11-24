import MathProofs.GC11Coercivity
import MathProofs.BandPassFlow

/-!
# GC11: integrated coercivity on the actual two-dimensional torus

Uses the maintained Fourier Sobolev realization and its continuous
representative, not a finite-dimensional truncation.
Conservation along the Hamiltonian flow remains a separate obligation.
-/
noncomputable section
open MeasureTheory
namespace ReyesMath
namespace GC11TorusEnergy

open GC11Coercivity BandPass TorusL2

variable (L : ℝ) [Fact (0 < L)]

/-- Squared carrier radius and dot product with an actual torus sideband. -/
def carrierSq (K : Fin 2 → ℝ) : ℝ := K 0 ^ 2 + K 1 ^ 2

def carrierDot (K : Fin 2 → ℝ) (n : Fin 2 → ℤ) : ℝ :=
  K 0 * xi L n 0 + K 1 * xi L n 1

theorem carrierSq_nonneg (K : Fin 2 → ℝ) : 0 ≤ carrierSq K := by
  unfold carrierSq
  positivity

theorem carrierDot_sq_le (K : Fin 2 → ℝ) (n : Fin 2 → ℤ) :
    carrierDot L K n ^ 2 ≤ carrierSq K * xi2 L n := by
  unfold carrierDot carrierSq xi2
  rw [Fin.sum_univ_two]
  nlinarith [sq_nonneg (K 0 * xi L n 1 - K 1 * xi L n 0)]

/-- Carrier tangent-subtracted kinetic symbol, evaluated on the full lattice. -/
def g (k : ℝ) (K : Fin 2 → ℝ) (n : Fin 2 → ℤ) : ℝ :=
  excess k (carrierSq K) (xi2 L n) (carrierDot L K n)

theorem g_nonneg {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 ≤ carrierSq K)
    (n : Fin 2 → ℤ) : 0 ≤ g L k K n :=
  excess_nonneg hq (xi2_nonneg n)

theorem g_upper (k : ℝ) (K : Fin 2 → ℝ) (n : Fin 2 → ℤ) :
    g L k K n ≤ (2 + 10 * carrierSq K) * wt L n ^ 2 := by
  have hcs := carrierDot_sq_le L K n
  have hs : 0 ≤ xi2 L n := xi2_nonneg n
  have hq := carrierSq_nonneg K
  have hks := mul_nonneg (sq_nonneg k) hs
  have hqs := mul_nonneg hq hs
  have hqss := mul_nonneg hq (sq_nonneg (xi2 L n))
  unfold g wt
  rw [excess_eq]
  nlinarith [sq_nonneg (xi2 L n - 2 * carrierDot L K n)]

/-- Explicit constant in the lower derivative-energy estimate. -/
def Ckin (k q : ℝ) : ℝ := 2 + (1 + 4 * k ^ 2 + 4 * q) / (2 * (q - k ^ 2))

theorem Ckin_pos {k q : ℝ} (hq : k ^ 2 < q) : 0 < Ckin k q := by
  have hq0 : 0 ≤ q := (sq_nonneg k).trans hq.le
  have hd : 0 < q - k ^ 2 := sub_pos.mpr hq
  unfold Ckin
  positivity

theorem derivative_bound {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 < carrierSq K)
    (n : Fin 2 → ℤ) :
    xi2 L n + xi2 L n ^ 2 ≤ Ckin k (carrierSq K) * g L k K n := by
  have hd : 0 < 2 * (carrierSq K - k ^ 2) := by linarith
  have hnum : 0 ≤ 1 + 4 * k ^ 2 + 4 * carrierSq K := by
    linarith [sq_nonneg k, carrierSq_nonneg K]
  have hlow : 2 * (carrierSq K - k ^ 2) * xi2 L n ≤ g L k K n :=
    excess_lower _ _ _ _
  have hfour : xi2 L n ^ 2 ≤
      2 * g L k K n + (4 * k ^ 2 + 4 * carrierSq K) * xi2 L n :=
    fourth_order_bound (carrierDot_sq_le L K n)
  have hs : xi2 L n ≤ g L k K n / (2 * (carrierSq K - k ^ 2)) :=
    (le_div_iff₀ hd).2 (by simpa [mul_comm] using hlow)
  have hm := mul_le_mul_of_nonneg_left hs hnum
  unfold Ckin
  calc
    xi2 L n + xi2 L n ^ 2 ≤ 2 * g L k K n +
        (1 + 4 * k ^ 2 + 4 * carrierSq K) * xi2 L n := by linarith
    _ ≤ 2 * g L k K n + (1 + 4 * k ^ 2 + 4 * carrierSq K) *
        (g L k K n / (2 * (carrierSq K - k ^ 2))) := by linarith
    _ = _ := by ring

def kinetic (k : ℝ) (K : Fin 2 → ℝ) (A : TorusL2.L2 L 2) : ℝ :=
  ∑' n, g L k K n * ‖coef A n‖ ^ 2

def derivativeEnergy (A : TorusL2.L2 L 2) : ℝ :=
  ∑' n, (xi2 L n + xi2 L n ^ 2) * ‖coef A n‖ ^ 2

theorem summable_kinetic {k : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 ≤ carrierSq K) {A : TorusL2.L2 L 2} (hA : InH 1 A) :
    Summable (fun n => g L k K n * ‖coef A n‖ ^ 2) := by
  have hw : Summable (fun n => wt L n ^ 2 * ‖coef A n‖ ^ 2) := by
    simpa [InH] using hA
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (g_nonneg L hq n) (sq_nonneg _)) (fun n => ?_)
    (hw.mul_left (2 + 10 * carrierSq K))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (g_upper L k K n) (sq_nonneg _)

theorem summable_derivative {A : TorusL2.L2 L 2} (hA : InH 1 A) :
    Summable (fun n => (xi2 L n + xi2 L n ^ 2) * ‖coef A n‖ ^ 2) := by
  have hw : Summable (fun n => wt L n ^ 2 * ‖coef A n‖ ^ 2) := by
    simpa [InH] using hA
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hw
  · have hs : 0 ≤ xi2 L n := xi2_nonneg n
    positivity
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hs : 0 ≤ xi2 L n := xi2_nonneg n
    unfold wt
    nlinarith

theorem kinetic_nonneg {k : ℝ} {K : Fin 2 → ℝ} (hq : k ^ 2 ≤ carrierSq K)
    (A : TorusL2.L2 L 2) : 0 ≤ kinetic L k K A := by
  unfold kinetic
  exact tsum_nonneg fun n => mul_nonneg (g_nonneg L hq n) (sq_nonneg _)

/-- Full-lattice integrated estimate on the existing H² Sobolev space. -/
theorem derivativeEnergy_le {k : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 < carrierSq K) {A : TorusL2.L2 L 2} (hA : InH 1 A) :
    derivativeEnergy L A ≤ Ckin k (carrierSq K) * kinetic L k K A := by
  unfold derivativeEnergy kinetic
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_derivative L hA)
    ((summable_kinetic L hq.le hA).mul_left _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (derivative_bound L hq n) (sq_nonneg _)

/-- Density energy using the existing H² continuous representative. -/
def density (rho : ℝ) (c : ell2 2) : ℝ :=
  ∫ x, (‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2 - rho) ^ 2 ∂(μ L 2)

def densityPotential (beta gamma rho : ℝ) (c : ell2 2) : ℝ :=
  ∫ x, relativePotential beta gamma rho (‖Phi L (by decide : 2 ≤ 3) c x‖ ^ 2) ∂(μ L 2)

def relEnergy (k beta gamma rho : ℝ) (K : Fin 2 → ℝ) (c : ell2 2) : ℝ :=
  kinetic L k K (iota L 1 c) + densityPotential L beta gamma rho c

theorem density_nonneg (rho : ℝ) (c : ell2 2) : 0 ≤ density L rho c := by
  unfold density
  exact integral_nonneg fun x => sq_nonneg _

theorem densityPotential_lower {beta gamma rho : ℝ} (hg : 0 ≤ gamma) (c : ell2 2) :
    (2 * gamma * rho / 3 - beta / 2) * density L rho c ≤
      densityPotential L beta gamma rho c := by
  unfold density densityPotential
  rw [← integral_const_mul]
  apply integral_mono
  · apply integrable_of_continuous
    fun_prop
  · apply integrable_of_continuous
    unfold relativePotential potential densitySlope
    fun_prop
  · intro x
    exact relativePotential_lower hg (sq_nonneg _)

/-- Actual Fourier and integrated density energies are jointly controlled.
No conservation-law hypothesis is hidden in the estimate. -/
theorem integrated_coercivity {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 < carrierSq K) (hg : 0 ≤ gamma)
    (hrho : 3 * beta < 4 * gamma * rho) (c : ell2 2) :
    derivativeEnergy L (iota L 1 c) +
      Ckin k (carrierSq K) * (2 * gamma * rho / 3 - beta / 2) * density L rho c ≤
    Ckin k (carrierSq K) * relEnergy L k beta gamma rho K c := by
  have hH : InH 1 (iota L 1 c) := (inH_iff 1 _).2 ⟨c, rfl⟩
  have hk := derivativeEnergy_le L hq hH
  have hp := densityPotential_lower L hg c
  have hm := mul_le_mul_of_nonneg_left hp (Ckin_pos hq).le
  unfold relEnergy
  rw [mul_add]
  linarith

/-- Energy stability along any conserving trajectory in the actual Fourier H² space.
The Hamiltonian existence/conservation bridge is explicitly still required. -/
theorem conserved_energy_bound {k beta gamma rho : ℝ} {K : Fin 2 → ℝ}
    (hq : k ^ 2 < carrierSq K) (hg : 0 ≤ gamma)
    (hrho : 3 * beta < 4 * gamma * rho) (u : ℝ → ell2 2)
    (hc : ∀ t, relEnergy L k beta gamma rho K (u t) =
      relEnergy L k beta gamma rho K (u 0)) (t : ℝ) :
    derivativeEnergy L (iota L 1 (u t)) +
      Ckin k (carrierSq K) * (2 * gamma * rho / 3 - beta / 2) * density L rho (u t) ≤
    Ckin k (carrierSq K) * relEnergy L k beta gamma rho K (u 0) := by
  rw [← hc t]
  exact integrated_coercivity L hq hg hrho (u t)

end GC11TorusEnergy
end ReyesMath
