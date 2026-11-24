import MathProofs.BandPassFlow
import PVNP.TorusWellPosed

/-!
# GC11: reuse of the verified PVNP periodic H² solver

PVNP PR #40, verified head 924f7866ab991638153b19507dfbc72c4a1a69cf,
already proves the original periodic cubic–quintic equation globally
well posed. Its physical coefficients use Lebesgue orthonormalization
on the square, whereas TorusL2 uses probability Haar measure. The
bridge below changes the lattice index and divides coefficients by L;
it does NOT identify the two norms without the normalization factor.
This module deliberately does not import the unverified GC11 chain.
-/
noncomputable section
open MeasureTheory Complex
namespace ReyesMath
namespace GC11PVNPBridge

open BandPass TorusL2

variable (L : ℝ) [Fact (0 < L)]

/-- The index identification, with no truncation of either lattice. -/
def pairIndex : (Fin 2 → ℤ) ≃ PVNP.Torus.Z2 where
  toFun n := (n 0, n 1)
  invFun p := ![p.1, p.2]
  left_inv n := by funext i; fin_cases i <;> rfl
  right_inv p := by cases p; rfl

@[simp] theorem pairIndex_apply (n : Fin 2 → ℤ) : pairIndex n = (n 0, n 1) := rfl

theorem qf_match (n : Fin 2 → ℤ) : PVNP.Torus.qf L (pairIndex n) = BandPass.xi2 L n := by
  simp [PVNP.Torus.qf, PVNP.Torus.xi1, PVNP.Torus.xi2, BandPass.xi2, BandPass.xi, Fin.sum_univ_two]

theorem wt_match (n : Fin 2 → ℤ) : PVNP.Torus.wt L (pairIndex n) = BandPass.wt L n := by
  unfold PVNP.Torus.wt BandPass.wt
  rw [qf_match]

theorem omega_match (k : ℝ) (n : Fin 2 → ℤ) :
    PVNP.Torus.om L (k ^ 2) (pairIndex n) = (BandPass.xi2 L n - k ^ 2) ^ 2 := by
  unfold PVNP.Torus.om
  rw [qf_match]
  ring

-- Fix the lattice and summand types before invoking the equivalence.
-- This avoids expensive inference through the two lp subtype aliases.
set_option maxHeartbeats 2000000 in
def reindex (v : PVNP.Torus.ℓ2) : BandPass.ell2 2 := by
  let f : (Fin 2 → ℤ) → ℂ := fun n => v (pairIndex n)
  have hs : Summable (fun n : Fin 2 → ℤ => ‖f n‖ ^ 2) := by
    change Summable (fun n : Fin 2 → ℤ => ‖v (pairIndex n)‖ ^ 2)
    exact (pairIndex.summable_iff (f := fun p : PVNP.Torus.Z2 => ‖v p‖ ^ 2)).2
      (PVNP.Torus.summable_sq v)
  exact ⟨f, (BandPass.memℓp_two_iff (f := f)).2 hs⟩

set_option maxHeartbeats 2000000 in
def unindex (c : BandPass.ell2 2) : PVNP.Torus.ℓ2 := by
  let f : PVNP.Torus.Z2 → ℂ := fun p => c (pairIndex.symm p)
  have hs : Summable (fun p : PVNP.Torus.Z2 => ‖f p‖ ^ 2) := by
    change Summable (fun p : PVNP.Torus.Z2 => ‖c (pairIndex.symm p)‖ ^ 2)
    exact (pairIndex.symm.summable_iff (f := fun n : Fin 2 → ℤ => ‖c n‖ ^ 2)).2
      (BandPass.hasSum_sq_ell2 c).summable
  exact PVNP.Torus.mk f hs

@[simp] theorem reindex_apply (v : PVNP.Torus.ℓ2) (n : Fin 2 → ℤ) :
    reindex v n = v (pairIndex n) := rfl

@[simp] theorem unindex_apply (c : BandPass.ell2 2) (p : PVNP.Torus.Z2) :
    unindex c p = c (pairIndex.symm p) := rfl

theorem norm_reindex (v : PVNP.Torus.ℓ2) : ‖reindex v‖ = ‖v‖ := by
  have h : ‖reindex v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [BandPass.norm_sq_ell2, PVNP.Torus.norm_sq_eq]
    exact pairIndex.tsum_eq (fun p => ‖v p‖ ^ 2)
  nlinarith [norm_nonneg (reindex v), norm_nonneg v]

/-- Conversion from physical Lebesgue-normalized H² to the probability
Haar-normalized H² state space. -/
def toMath (v : PVNP.Torus.ℓ2) : BandPass.ell2 2 := ((L : ℂ)⁻¹) • reindex v

def toPVNP (c : BandPass.ell2 2) : PVNP.Torus.ℓ2 := (L : ℂ) • unindex c

@[simp] theorem toMath_apply (v : PVNP.Torus.ℓ2) (n : Fin 2 → ℤ) :
    toMath L v n = (L : ℂ)⁻¹ * v (pairIndex n) := by
  simp only [toMath, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, reindex_apply]

@[simp] theorem toPVNP_apply (c : BandPass.ell2 2) (p : PVNP.Torus.Z2) :
    toPVNP L c p = (L : ℂ) * c (pairIndex.symm p) := by
  simp only [toPVNP, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, unindex_apply]

theorem L_ne : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < L).ne'

@[simp] theorem toMath_toPVNP (c : BandPass.ell2 2) :
    toMath L (toPVNP L c) = c := by
  ext n
  rw [toMath_apply, toPVNP_apply, Equiv.symm_apply_apply, ← mul_assoc,
    inv_mul_cancel₀ (L_ne L), one_mul]

@[simp] theorem toPVNP_toMath (v : PVNP.Torus.ℓ2) :
    toPVNP L (toMath L v) = v := by
  ext p
  rw [toPVNP_apply, toMath_apply, Equiv.apply_symm_apply, ← mul_assoc,
    mul_inv_cancel₀ (L_ne L), one_mul]

theorem norm_toMath (v : PVNP.Torus.ℓ2) : ‖toMath L v‖ = L⁻¹ * ‖v‖ := by
  rw [toMath, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Fact.out : 0 < L), norm_reindex]

/-- The representation conversion is bounded complex-linear, hence
preserves trajectory continuity. -/
def toMathCLM : PVNP.Torus.ℓ2 →L[ℂ] BandPass.ell2 2 :=
  LinearMap.mkContinuous
    { toFun := toMath L
      map_add' := by intro a b; ext n; simp [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := by intro a b; ext n; simp [lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul, mul_left_comm] }
    L⁻¹ (fun v => (norm_toMath L v).le)

theorem continuous_toMath : Continuous (toMath L) := (toMathCLM L).continuous

theorem coef_toMath (v : PVNP.Torus.ℓ2) (n : Fin 2 → ℤ) :
    coef (iota L 1 (toMath L v)) n = (L : ℂ)⁻¹ * PVNP.Torus.co L v (pairIndex n) := by
  rw [coef_iota, pow_one, toMath_apply, ← wt_match]
  unfold PVNP.Torus.co
  push_cast
  rw [div_eq_mul_inv]
  ring

/-- The quotient map from the original fundamental-box coordinates. -/
def quotientPoint (x : ℝ × ℝ) : Tor L 2 := fun j =>
  ((![x.1, x.2] : Fin 2 → ℝ) j : AddCircle L)

theorem quotientPoint_surjective : Function.Surjective (quotientPoint L) := by
  intro x
  have h : ∀ j : Fin 2, ∃ a : ℝ, (a : AddCircle L) = x j := by
    intro j
    exact QuotientAddGroup.mk_surjective (x j)
  choose a ha using h
  refine ⟨(a 0,a 1), ?_⟩
  funext j
  fin_cases j
  · exact ha 0
  · exact ha 1

theorem emode_match (n : Fin 2 → ℤ) (x : ℝ × ℝ) :
    TorusL2.emode (L := L) n (quotientPoint L x) = PVNP.Torus.emode L (pairIndex n) x := by
  unfold quotientPoint
  rw [TorusL2.emode_coe, PVNP.Torus.emode, PVNP.Torus.e1, PVNP.Torus.e1, ← Complex.exp_add]
  congr 1
  simp [pairIndex_apply, Fin.sum_univ_two]
  push_cast
  field_simp [L_ne L]
  <;> ring

/-- Exact equality of continuous representatives, including the factor
L in the orthonormal Fourier series on the physical box. -/
theorem field_match (v : PVNP.Torus.ℓ2) (x : ℝ × ℝ) :
    BandPass.Phi L (by decide : 2 ≤ 3) (toMath L v) (quotientPoint L x) =
      PVNP.Torus.field L (PVNP.Torus.co L v) x := by
  have h := (hasSum_Phi (L := L) (by decide : 2 ≤ 3) (toMath L v)).mapL
    (ContinuousMap.evalCLM ℂ (quotientPoint L x))
  change HasSum (fun n : Fin 2 → ℤ =>
    (toMath L v n * ((BandPass.wt L n)⁻¹ : ℂ)) * TorusL2.emode n (quotientPoint L x))
    (BandPass.Phi L (by decide : 2 ≤ 3) (toMath L v) (quotientPoint L x)) at h
  rw [← h.tsum_eq]
  unfold PVNP.Torus.field
  rw [← pairIndex.tsum_eq (fun p => PVNP.Torus.co L v p * PVNP.Torus.emode L p x), ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [toMath_apply, emode_match, ← wt_match]
  unfold PVNP.Torus.co
  push_cast
  rw [div_eq_mul_inv]
  ring

/-- Original, unshifted physical nonlinearity as a continuous field. -/
def physicalNonlin (beta gamma : ℝ) (F : C(Tor L 2, ℂ)) : C(Tor L 2, ℂ) where
  toFun x := PVNP.Torus.fnl beta gamma (F x)
  continuous_toFun := by
    simp only [PVNP.Torus.fnl_eq]
    exact (Complex.continuous_ofReal.comp
      (((continuous_const : Continuous (fun _ : Tor L 2 => -beta)).mul
        (F.continuous.norm.pow 2)).add
        ((continuous_const : Continuous (fun _ : Tor L 2 => gamma)).mul
          (F.continuous.norm.pow 4)))).mul F.continuous

theorem nonlin_match (beta gamma : ℝ) (v : PVNP.Torus.ℓ2) :
    BandPass.Phi L (by decide : 2 ≤ 3) (toMath L (PVNP.Torus.Fnl L beta gamma v)) =
      physicalNonlin L beta gamma (BandPass.Phi L (by decide : 2 ≤ 3) (toMath L v)) := by
  ext x
  obtain ⟨y, rfl⟩ := quotientPoint_surjective L x
  change _ = PVNP.Torus.fnl beta gamma (BandPass.Phi L (by decide : 2 ≤ 3)
    (toMath L v) (quotientPoint L y))
  rw [field_match, field_match, PVNP.Torus.field_Fnl (Fact.out : 0 < L)]

def physicalNonlinL2 (beta gamma : ℝ) (c : BandPass.ell2 2) : TorusL2.L2 L 2 :=
  ContinuousMap.toLp (E := ℂ) 2 (μ L 2) ℂ
    (physicalNonlin L beta gamma (BandPass.Phi L (by decide : 2 ≤ 3) c))

theorem physicalNonlin_coef (beta gamma : ℝ) (v : PVNP.Torus.ℓ2) (n : Fin 2 → ℤ) :
    coef (physicalNonlinL2 L beta gamma (toMath L v)) n =
      (L : ℂ)⁻¹ * PVNP.Torus.fc L (fun x => PVNP.Torus.fnl beta gamma (PVNP.Torus.field L (PVNP.Torus.co L v) x))
        (pairIndex n) := by
  unfold physicalNonlinL2
  rw [← nonlin_match, toLp_Phi, coef_toMath, PVNP.Torus.fc_fnl (Fact.out : 0 < L)]

/-- Continuous H² trajectories satisfying the original PDE at every
Fourier coefficient of the actual continuous field. -/
def IsLabSolution (k beta gamma : ℝ) (u : ℝ → BandPass.ell2 2) : Prop :=
  Continuous u ∧ ∀ t n, HasDerivAt (fun s => coef (iota L 1 (u s)) n)
    (-Complex.I * ((((BandPass.xi2 L n - k ^ 2) ^ 2 : ℝ) : ℂ) *
      coef (iota L 1 (u t)) n + coef (physicalNonlinL2 L beta gamma (u t)) n)) t

/-- The already kernel-checked periodic solver supplies a solution in
the exact normalized Haar Fourier representation used by GC11. -/
theorem pvnp_to_lab {k beta gamma : ℝ} {v : ℝ → PVNP.Torus.ℓ2}
    (hv : PVNP.Torus.IsSolution L (k ^ 2) beta gamma v) :
    IsLabSolution L k beta gamma (fun t => toMath L (v t)) := by
  refine ⟨(continuous_toMath L).comp hv.1, ?_⟩
  intro t n
  have h := (hv.2 t (pairIndex n)).const_mul ((L : ℂ)⁻¹)
  simp only [coef_toMath, physicalNonlin_coef]
  rw [omega_match] at h
  convert h using 1 <;> ring

/-- Global existence for every H² initial state, with no extra H⁴ or
strong differentiability hypothesis, via the existing verified solver. -/
theorem global_lab_exists {k beta gamma : ℝ} (hg : 0 < gamma)
    (c : BandPass.ell2 2) :
    ∃ u : ℝ → BandPass.ell2 2, u 0 = c ∧ IsLabSolution L k beta gamma u := by
  obtain ⟨v, hv, _⟩ := PVNP.Torus.global_wellposed (κ := k^2) (β := beta)
    (Fact.out : 0 < L) hg (toPVNP L c)
  refine ⟨fun t => toMath L (v t), ?_, pvnp_to_lab L hv.2⟩
  change toMath L (v 0) = c
  rw [hv.1, toMath_toPVNP]

/-- Exact mass normalization between the two representations. -/
theorem mass_match (v : PVNP.Torus.ℓ2) :
    ‖iota L 1 (toMath L v)‖ ^ 2 = L⁻¹ ^ 2 * PVNP.Torus.mass L v := by
  rw [TorusL2.norm_sq_eq_tsum, PVNP.Torus.mass, ← tsum_mul_left]
  rw [← pairIndex.tsum_eq (fun p => L⁻¹ ^ 2 * ‖PVNP.Torus.co L v p‖ ^ 2)]
  apply tsum_congr
  intro n
  rw [coef_toMath, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Fact.out : 0 < L), mul_pow]

theorem mass_conserved_lab {k beta gamma : ℝ} {v : ℝ → PVNP.Torus.ℓ2}
    (hv : PVNP.Torus.IsSolution L (k^2) beta gamma v) (t : ℝ) :
    ‖iota L 1 (toMath L (v t))‖ ^ 2 = ‖iota L 1 (toMath L (v 0))‖ ^ 2 := by
  simp only [mass_match, (PVNP.Torus.conservation (Fact.out : 0 < L) hv t).1]


theorem norm_toPVNP (c : BandPass.ell2 2) : ‖toPVNP L c‖ = L * ‖c‖ := by
  have h := norm_toMath L (toPVNP L c)
  rw [toMath_toPVNP] at h
  have hL : L ≠ 0 := (Fact.out : 0 < L).ne'
  calc
    ‖toPVNP L c‖ = L * (L⁻¹ * ‖toPVNP L c‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hL, one_mul]
    _ = L * ‖c‖ := by rw [← h]

def toPVNPCLM : BandPass.ell2 2 →L[ℂ] PVNP.Torus.ℓ2 :=
  LinearMap.mkContinuous
    { toFun := toPVNP L
      map_add' := by intro a b; ext p; simp [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := by intro a b; ext p; simp [lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul, mul_left_comm] }
    L (fun c => (norm_toPVNP L c).le)

theorem continuous_toPVNP : Continuous (toPVNP L) := (toPVNPCLM L).continuous

theorem co_toPVNP (c : BandPass.ell2 2) (n : Fin 2 → ℤ) :
    PVNP.Torus.co L (toPVNP L c) (pairIndex n) =
      (L : ℂ) * coef (iota L 1 c) n := by
  have h := coef_toMath L (toPVNP L c) n
  rw [toMath_toPVNP] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (L_ne L), one_mul]

theorem fc_toPVNP (beta gamma : ℝ) (c : BandPass.ell2 2) (n : Fin 2 → ℤ) :
    PVNP.Torus.fc L (fun x => PVNP.Torus.fnl beta gamma
      (PVNP.Torus.field L (PVNP.Torus.co L (toPVNP L c)) x)) (pairIndex n) =
      (L : ℂ) * coef (physicalNonlinL2 L beta gamma c) n := by
  have h := physicalNonlin_coef L beta gamma (toPVNP L c) n
  rw [toMath_toPVNP] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (L_ne L), one_mul]

/-- Inverse correspondence: every laboratory Fourier solution in the
normalized H² representation satisfies the already verified PVNP
solution predicate after scaling and relabeling. -/
theorem lab_to_pvnp {k beta gamma : ℝ} {u : ℝ → BandPass.ell2 2}
    (hu : IsLabSolution L k beta gamma u) :
    PVNP.Torus.IsSolution L (k ^ 2) beta gamma (fun t => toPVNP L (u t)) := by
  refine ⟨(continuous_toPVNP L).comp hu.1, ?_⟩
  intro t p
  let n := pairIndex.symm p
  have hp : pairIndex n = p := pairIndex.apply_symm_apply p
  rw [← hp]
  simp only [co_toPVNP, fc_toPVNP, omega_match]
  have h := (hu.2 t n).const_mul (L : ℂ)
  convert h using 1 <;> ring

theorem global_lab_wellposed {k beta gamma : ℝ} (hg : 0 < gamma)
    (c : BandPass.ell2 2) :
    ∃! u : ℝ → BandPass.ell2 2, u 0 = c ∧ IsLabSolution L k beta gamma u := by
  obtain ⟨v, hv, huniq⟩ := PVNP.Torus.global_wellposed (κ := k^2) (β := beta)
    (Fact.out : 0 < L) hg (toPVNP L c)
  refine ⟨fun t => toMath L (v t), ⟨by change toMath L (v 0) = c; rw [hv.1, toMath_toPVNP], pvnp_to_lab L hv.2⟩, ?_⟩
  intro u hu
  have he := huniq (fun t => toPVNP L (u t))
    ⟨by change toPVNP L (u 0) = toPVNP L c; rw [hu.1], lab_to_pvnp L hu.2⟩
  funext t
  have ht := congrFun he t
  rw [← ht, toMath_toPVNP]

/-- Normalized laboratory Hamiltonian. The potential is evaluated on the
physical pullback to the fundamental box, with the explicit L⁻² factor;
the kinetic term uses the normalized Haar Fourier coefficients. -/
def labHam (k beta gamma : ℝ) (c : BandPass.ell2 2) : ℝ :=
  (∑' n, (BandPass.xi2 L n - k ^ 2) ^ 2 * ‖coef (iota L 1 c) n‖ ^ 2) +
    L⁻¹ ^ 2 * ∫ x, PVNP.Torus.nfun beta gamma
      (BandPass.Phi L (by decide : 2 ≤ 3) c (quotientPoint L x)) ∂PVNP.Torus.box L

theorem ham_match (k beta gamma : ℝ) (v : PVNP.Torus.ℓ2) :
    labHam L k beta gamma (toMath L v) =
      L⁻¹ ^ 2 * PVNP.Torus.ham L (k ^ 2) beta gamma v := by
  unfold labHam PVNP.Torus.ham PVNP.Torus.pot
  simp only [field_match, mul_add]
  congr 1
  rw [PVNP.Torus.norm_sq_eq, ← tsum_mul_left]
  rw [← pairIndex.tsum_eq (fun p => L⁻¹ ^ 2 * ‖PVNP.Torus.Ac L (k ^ 2) v p‖ ^ 2)]
  apply tsum_congr
  intro n
  rw [coef_toMath, PVNP.Torus.Ac_apply, qf_match, norm_mul, norm_mul,
    norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Fact.out : 0 < L), mul_pow, mul_pow, sq_abs]
  ring

theorem lab_conservation {k beta gamma : ℝ} {u : ℝ → BandPass.ell2 2}
    (hu : IsLabSolution L k beta gamma u) (t : ℝ) :
    ‖iota L 1 (u t)‖ ^ 2 = ‖iota L 1 (u 0)‖ ^ 2 ∧
      labHam L k beta gamma (u t) = labHam L k beta gamma (u 0) := by
  have hv := lab_to_pvnp L hu
  have hm := mass_conserved_lab L hv t
  have hh := (PVNP.Torus.conservation (Fact.out : 0 < L) hv t).2
  constructor
  · simpa only [toMath_toPVNP] using hm
  · have h1 := ham_match L k beta gamma (toPVNP L (u t))
    have h0 := ham_match L k beta gamma (toPVNP L (u 0))
    rw [toMath_toPVNP] at h1 h0
    rw [h1, h0, hh]

end GC11PVNPBridge
end ReyesMath
