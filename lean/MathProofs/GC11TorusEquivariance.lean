import MathProofs.GC11TorusCarrier

/-!
# GC11: exact spatial Fourier equivariance of the nonlinear carrier transform

All statements use the full torus, normalized Haar measure and actual
continuous representatives. Translation and unit-modulus modulation
are treated exactly; no Galerkin truncation or nonlinear closure axiom.
-/
noncomputable section
open MeasureTheory Complex
open scoped ComplexConjugate
namespace ReyesMath
namespace GC11TorusEquivariance

open BandPass TorusL2 GC11Coercivity GC11TorusEnergy
  GC11TorusHamiltonian GC11TorusCarrier

variable (L : ℝ) [Fact (0 < L)]

theorem emode_translate (n : Fin 2 → ℤ) (x a : Tor L 2) :
    emode (L := L) n (x + a) = emode n x * emode n a := by
  simp only [emode, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem emode_conj_cancel (n : Fin 2 → ℤ) (x : Tor L 2) :
    emode (L := L) n x * conj (emode n x) = 1 := by
  rw [Complex.mul_conj', norm_emode_apply]
  norm_num

theorem translate_mp (a : Tor L 2) :
    MeasurePreserving (fun x : Tor L 2 => x + a) (μ L 2) (μ L 2) := by
  unfold μ
  exact measurePreserving_pi _ _ fun i => measurePreserving_add_right _ (a i)

theorem integral_translate (a : Tor L 2) (f : Tor L 2 → ℂ) :
    (∫ x, f (x + a) ∂(μ L 2)) = ∫ x, f x ∂(μ L 2) :=
  (translate_mp L a).integral_comp (MeasurableEquiv.addRight a).measurableEmbedding f

/-- Laboratory field at an arbitrary translation and temporal phase. -/
def labField (m : Fin 2 → ℤ) (a : Tor L 2) (phase : ℂ)
    (F : C(Tor L 2, ℂ)) : C(Tor L 2, ℂ) where
  toFun x := phase * emode m x * F (x - a)
  continuous_toFun := continuous_const.mul (emode (L := L) m).continuous |>.mul
    (F.continuous.comp (continuous_id.sub continuous_const))

theorem labField_apply (m : Fin 2 → ℤ) (a : Tor L 2) (phase : ℂ)
    (F : C(Tor L 2, ℂ)) (x : Tor L 2) :
    labField L m a phase F x = phase * emode m x * F (x - a) := rfl

theorem labField_norm (m : Fin 2 → ℤ) (a : Tor L 2) {phase : ℂ}
    (hp : ‖phase‖ = 1) (F : C(Tor L 2, ℂ)) (x : Tor L 2) :
    ‖labField L m a phase F x‖ = ‖F (x - a)‖ := by
  rw [labField_apply, norm_mul, norm_mul, hp, norm_emode_apply, one_mul, one_mul]

theorem labField_add (m : Fin 2 → ℤ) (a : Tor L 2) (phase : ℂ)
    (F H : C(Tor L 2, ℂ)) :
    labField L m a phase (F + H) = labField L m a phase F + labField L m a phase H := by
  ext x
  simp only [labField_apply, ContinuousMap.add_apply, mul_add]

theorem labField_smul (m : Fin 2 → ℤ) (a : Tor L 2) (phase c : ℂ)
    (F : C(Tor L 2, ℂ)) :
    labField L m a phase (c • F) = c • labField L m a phase F := by
  ext x
  simp only [labField_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem coef_fieldL2 (F : C(Tor L 2, ℂ)) (n : Fin 2 → ℤ) :
    coef (fieldL2 L F) n = ∫ x, F x * conj (emode n x) ∂(μ L 2) := by
  unfold coef fieldL2
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ L 2) F] with x hx
  rw [hx]

/-- Exact Fourier transform of the modulated and translated field. -/
theorem coef_labField (m n : Fin 2 → ℤ) (a : Tor L 2) (phase : ℂ)
    (F : C(Tor L 2, ℂ)) :
    coef (fieldL2 L (labField L m a phase F)) (m + n) =
      (phase * conj (emode n a)) * coef (fieldL2 L F) n := by
  rw [coef_fieldL2, coef_fieldL2]
  rw [← integral_translate L a
    (fun x => labField L m a phase F x * conj (emode (m+n) x))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [labField_apply, add_sub_cancel_right, BandPass.emode_add, map_mul]
  have hc := emode_conj_cancel L m (x+a)
  rw [emode_translate L n x a, map_mul]
  calc
    _ = (emode m (x+a) * conj (emode m (x+a))) *
      ((phase * conj (emode n a)) * (F x * conj (emode n x))) := by ring
    _ = _ := by rw [hc, one_mul]

/-- The chemical-potential subtraction is exactly reversed under a
unit-modulus modulation, pointwise on the original continuous field. -/
theorem original_nonlinear_lab (beta gamma rho : ℝ) (m : Fin 2 → ℤ)
    (a : Tor L 2) {phase : ℂ} (hp : ‖phase‖ = 1)
    (F : C(Tor L 2, ℂ)) :
    originalNonlinearMap L beta gamma (labField L m a phase F) =
      labField L m a phase (nonlinearMap L beta gamma rho F +
        (densitySlope beta gamma rho : ℂ) • F) := by
  ext x
  change (densitySlope beta gamma (‖labField L m a phase F x‖ ^ 2) : ℂ) *
    labField L m a phase F x = _
  rw [labField_norm L m a hp, labField_apply, labField_apply]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  change _ = phase * emode m x *
    (((densitySlope beta gamma (‖F (x-a)‖ ^ 2) - densitySlope beta gamma rho : ℝ) : ℂ) *
      F (x-a) + (densitySlope beta gamma rho : ℂ) * F (x-a))
  push_cast
  ring

theorem fieldL2_add (F H : C(Tor L 2, ℂ)) :
    fieldL2 L (F+H) = fieldL2 L F + fieldL2 L H := by
  unfold fieldL2
  exact map_add _ _ _

theorem fieldL2_smul (z : ℂ) (F : C(Tor L 2, ℂ)) :
    fieldL2 L (z • F) = z • fieldL2 L F := by
  unfold fieldL2
  exact map_smul _ _ _

/-- Exact original nonlinear Fourier coefficient in laboratory coordinates.
Here the right-hand forcing is the SAME nonlinear map as in the strong
carrier-frame equation, with the chemical term restored. -/
theorem original_nonlinear_coef (beta gamma rho : ℝ) (m n : Fin 2 → ℤ)
    (a : Tor L 2) {phase : ℂ} (hp : ‖phase‖ = 1) (c : ell2 2) :
    coef (fieldL2 L (originalNonlinearMap L beta gamma
      (labField L m a phase (BandPass.Phi L (by decide : 2 ≤ 3) c)))) (m+n) =
      (phase * conj (emode n a)) *
        (coef (nonlinear L beta gamma rho c) n +
          (densitySlope beta gamma rho : ℂ) * coef (iota L 1 c) n) := by
  rw [original_nonlinear_lab L beta gamma rho m a hp, coef_labField,
    fieldL2_add, fieldL2_smul, coef_add, coef_smul]
  rfl

end GC11TorusEquivariance
end ReyesMath
