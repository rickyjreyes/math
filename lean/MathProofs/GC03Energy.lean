import MathProofs.CubicQuinticFlow
import MathProofs.FourierMultiplierL2

/-!
GC03: candidate real-power energy coercivity for the actual pure dispersion
Hamiltonian. Finite-integrability hypotheses are explicit because the Bochner
integral is total. No general evolution or critical continuation is asserted.
This source requires compilation and audit.
-/

open MeasureTheory
namespace ReyesMath.GC03Energy

/-- The lower power can be absorbed by the higher one and a mass term. -/
theorem power_absorption {a b r s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 1 < r) (hrs : r < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      a * x ^ (r + 1) ≤ b * x ^ (s + 1) + C * x ^ (2 : ℕ) := by
  have hsr : 0 < s - r := sub_pos.mpr hrs
  have hab : 0 < a / b := div_pos ha hb
  let R : ℝ := (a / b) ^ (s - r)⁻¹
  have hR : 0 < R := Real.rpow_pos_of_pos hab _
  have hRp : R ^ (s - r) = a / b :=
    Real.rpow_inv_rpow hab.le hsr.ne'
  let C : ℝ := a * R ^ (r - 1)
  have hC : 0 ≤ C := mul_nonneg ha.le (Real.rpow_nonneg hR.le _)
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hrn : 0 ≤ r - 1 := by linarith
  have hsn : 0 ≤ s - 1 := by linarith
  have hxr : x ^ (r + 1) = x ^ (2 : ℕ) * x ^ (r - 1) := by
    rw [← Real.rpow_two x, ← Real.rpow_add_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 2) hrn]
    congr 1
    ring
  have hxs : x ^ (s + 1) = x ^ (2 : ℕ) * x ^ (s - 1) := by
    rw [← Real.rpow_two x, ← Real.rpow_add_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 2) hsn]
    congr 1
    ring
  have hsx : 0 ≤ x ^ (s - 1) := Real.rpow_nonneg hx _
  by_cases h : x ≤ R
  · have hpow := Real.rpow_le_rpow hx h hrn
    have hle : a * x ^ (r - 1) ≤ C := mul_le_mul_of_nonneg_left hpow ha.le
    have hmul := mul_le_mul_of_nonneg_left hle (sq_nonneg x)
    have hbpos : 0 ≤ b * x ^ (s - 1) * x ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg hb.le hsx) (sq_nonneg x)
    rw [hxr, hxs]
    nlinarith only [hmul, hbpos]
  · have hpow := Real.rpow_le_rpow hR.le (le_of_lt (lt_of_not_ge h)) hsr.le
    rw [hRp] at hpow
    have hba : a ≤ b * x ^ (s - r) := by
      have h' := (div_le_iff₀ hb).mp hpow
      simpa [mul_comm] using h'
    have hsplit : x ^ (s - 1) = x ^ (s - r) * x ^ (r - 1) := by
      rw [← Real.rpow_add_of_nonneg hx hsr.le hrn]
      congr 1
      ring
    have hmul := mul_le_mul_of_nonneg_right hba (Real.rpow_nonneg hx (r - 1))
    have hle : a * x ^ (r - 1) ≤ b * x ^ (s - 1) := by
      rw [hsplit]
      simpa only [mul_assoc] using hmul
    have hmul2 := mul_le_mul_of_nonneg_left hle (sq_nonneg x)
    have hcp : 0 ≤ C * x ^ (2 : ℕ) := mul_nonneg hC (sq_nonneg x)
    rw [hxr, hxs]
    nlinarith only [hmul2, hcp]

/-- The potential integral on an arbitrary measure space. -/
theorem integrated_absorption {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {a b r s : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 1 < r) (hrs : r < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : X → ℂ,
      Integrable (fun x => ‖f x‖ ^ (2 : ℕ)) μ →
      Integrable (fun x => ‖f x‖ ^ (r + 1)) μ →
      Integrable (fun x => ‖f x‖ ^ (s + 1)) μ →
      a * (∫ x, ‖f x‖ ^ (r + 1) ∂μ) ≤
        b * (∫ x, ‖f x‖ ^ (s + 1) ∂μ) +
        C * (∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ) := by
  obtain ⟨C, hC, h⟩ := power_absorption ha hb hr hrs
  refine ⟨C, hC, ?_⟩
  intro f h2 hrl hsl
  have hle := integral_mono (hrl.const_mul a)
    ((hsl.const_mul b).add (h2.const_mul C))
    (fun x => h (‖f x‖) (norm_nonneg _))
  simpa only [integral_add (hsl.const_mul b) (h2.const_mul C),
    integral_const_mul] using hle

open ReyesMath.Sobolev

/-- Kinetic energy form for (-Delta)^p, using the repository Fourier convention. -/
noncomputable def kineticDensity {d : ℕ} (p : ℕ) (u : L2 d)
    (ξ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  qS ξ ^ p * ‖FU u ξ‖ ^ (2 : ℕ)

noncomputable def kinetic {d : ℕ} (p : ℕ) (u : L2 d) : ℝ :=
  ∫ ξ, kineticDensity p u ξ

noncomputable def moment {d : ℕ} (a : ℝ) (u : L2 d) : ℝ :=
  ∫ x, ‖u x‖ ^ a

/-- The actual finite-energy domain, with explicit integral obligations. -/
def FiniteEnergy {d : ℕ} (p : ℕ) (r s : ℝ) (u : L2 d) : Prop :=
  Integrable (kineticDensity p u) ∧
    Integrable (fun x => ‖u x‖ ^ (2 : ℕ)) ∧
    Integrable (fun x => ‖u x‖ ^ (r + 1)) ∧
    Integrable (fun x => ‖u x‖ ^ (s + 1))

noncomputable def energy {d : ℕ} (p : ℕ) (β γ r s : ℝ) (u : L2 d) : ℝ :=
  kinetic p u / 2 - β / (r + 1) * moment (r + 1) u +
    γ / (s + 1) * moment (s + 1) u

/-- Exact Hamiltonian estimate for every dimension, order and real power pair. -/
theorem energy_coercivity {d : ℕ} (p : ℕ) {β γ r s : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 < r) (hrs : r < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : L2 d, FiniteEnergy p r s u →
      kinetic p u / 2 + γ / (2 * (s + 1)) * moment (s + 1) u ≤
        energy p β γ r s u + C * (∫ x, ‖u x‖ ^ (2 : ℕ)) := by
  have hrp : 0 < r + 1 := by linarith
  have hsp : 0 < s + 1 := by linarith
  have ha : 0 < β / (r + 1) := div_pos hβ hrp
  have hb : 0 < γ / (2 * (s + 1)) := div_pos hγ (by positivity)
  obtain ⟨C, hC, h⟩ := integrated_absorption
    (volume : Measure (EuclideanSpace ℝ (Fin d))) ha hb hr hrs
  refine ⟨C, hC, ?_⟩
  intro u hu
  obtain ⟨_, h2, hrl, hsl⟩ := hu
  have hp := h (fun x => u x) h2 hrl hsl
  change β / (r + 1) * moment (r + 1) u ≤
    γ / (2 * (s + 1)) * moment (s + 1) u +
      C * (∫ x, ‖u x‖ ^ (2 : ℕ)) at hp
  have hcoeff : γ / (s + 1) = 2 * (γ / (2 * (s + 1))) := by
    field_simp
    <;> ring
  unfold energy
  rw [hcoeff]
  linarith

/-- Existing exact GC03 subcase (not a new generalized flow proof). -/
theorem cubic_quintic_d2_p2 {β γ : ℝ} (hγ : 0 < γ) (u₀ : H2 2) :
    ∃! u : ℝ → H2 2, IsSolution β γ 0 u ∧ u 0 = u₀ :=
  global_wellposed hγ u₀


/-- Exact supercritical scaling inequality, with dimension and order realified. -/
theorem supercritical_scaling_iff {d p s : ℝ} (hs : 1 < s) :
    p < d / 2 - 2 * p / (s - 1) ↔
      4 * p < (d - 2 * p) * (s - 1) := by
  have h : 0 < s - 1 := sub_pos.mpr hs
  constructor
  · intro hp
    have h' : 2 * p / (s - 1) < d / 2 - p := by linarith
    have h'' := (div_lt_iff₀ h).mp h'
    nlinarith only [h'']
  · intro hp
    have h' : 2 * p < (d / 2 - p) * (s - 1) := by
      nlinarith only [hp]
    have h'' := (div_lt_iff₀ h).mpr h'
    linarith

/-- The interval of singular exponents in the analytic Sobolev witness is
nonempty exactly above the critical scaling boundary. This is scalar
arithmetic, not a formal proof of the singular function's Sobolev membership. -/
theorem singular_exponent_window_iff {d p s : ℝ} (hs : 1 < s) :
    (∃ ell : ℝ, d / (s + 1) ≤ ell ∧ ell < d / 2 - p) ↔
      4 * p < (d - 2 * p) * (s - 1) := by
  have h : 0 < s + 1 := by linarith
  constructor
  · rintro ⟨ell, hlo, hhi⟩
    have h' := (div_lt_iff₀ h).mp (lt_of_le_of_lt hlo hhi)
    nlinarith only [h']
  · intro hp
    have h' : d < (d / 2 - p) * (s + 1) := by
      nlinarith only [hp]
    exact ⟨d / (s + 1), le_rfl, (div_lt_iff₀ h).mpr h'⟩

/-- Uniform kinetic bound for any trajectory satisfying the finite-energy
and mass/energy bounds, with no assumption of a continuation theorem. -/
theorem trajectory_kinetic_bound {d : ℕ} (p : ℕ) {β γ r s : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 < r) (hrs : r < s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T : Type} (u : T → L2 d) (M E : ℝ),
        (∀ t, FiniteEnergy p r s (u t)) →
        (∀ t, (∫ x, ‖u t x‖ ^ (2 : ℕ)) ≤ M) →
        (∀ t, energy p β γ r s (u t) ≤ E) →
        ∀ t, kinetic p (u t) ≤ 2 * (E + C * M) := by
  obtain ⟨C, hC, h⟩ := energy_coercivity (d := d) p hβ hγ hr hrs
  refine ⟨C, hC, ?_⟩
  intro T u M E hf hm he t
  have hc := h (u t) (hf t)
  have hmass := mul_le_mul_of_nonneg_left (hm t) hC
  have hpos : 0 ≤ moment (s + 1) (u t) := by
    unfold moment
    exact integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg (u t x)) _)
  have hcoef : 0 ≤ γ / (2 * (s + 1)) := by
    have : 0 < s + 1 := by linarith
    positivity
  have hterm := mul_nonneg hcoef hpos
  linarith only [hc, hmass, he t, hterm]


/-- A uniform positive energy loss at every hypothetical restart bounds their
number. This is the discrete counting step only, not the PDE defect theorem. -/
theorem energy_drop_count (e : ℕ → ℝ) (δ : ℝ) (N : ℕ)
    (h : ∀ i < N, e (i + 1) + δ ≤ e i) :
    e N + (N : ℝ) * δ ≤ e 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hs := h n (Nat.lt_succ_self n)
    push_cast
    linarith only [hn, hs]

/-- Conditional restart count for actual Fourier Hamiltonian values. The
positive loss at each restart must be established by the separate PDE proof. -/
theorem finite_energy_drop_count {d : ℕ} (p : ℕ) {β γ r s : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 < r) (hrs : r < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ → L2 d) (N : ℕ) (M δ : ℝ),
      FiniteEnergy p r s (u N) →
      (∫ x, ‖u N x‖ ^ (2 : ℕ)) ≤ M →
      (∀ i < N, energy p β γ r s (u (i + 1)) + δ ≤
        energy p β γ r s (u i)) →
      (N : ℝ) * δ ≤ energy p β γ r s (u 0) + C * M := by
  obtain ⟨C, hC, h⟩ := energy_coercivity (d := d) p hβ hγ hr hrs
  refine ⟨C, hC, ?_⟩
  intro u N M δ hf hm hd
  have hk : 0 ≤ kinetic p (u N) := by
    unfold kinetic kineticDensity
    exact integral_nonneg (fun ξ => mul_nonneg
      (pow_nonneg (qS_nonneg ξ) p) (sq_nonneg _))
  have hp : 0 ≤ moment (s + 1) (u N) := by
    unfold moment
    exact integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg (u N x)) _)
  have hcoef : 0 ≤ γ / (2 * (s + 1)) := by
    have : 0 < s + 1 := by linarith
    positivity
  have hpos := mul_nonneg hcoef hp
  have hlow := h (u N) hf
  have hmass := mul_le_mul_of_nonneg_left hm hC
  have hcount := energy_drop_count (fun i => energy p β γ r s (u i)) δ N hd
  linarith only [hk, hpos, hlow, hmass, hcount]

end ReyesMath.GC03Energy

#print axioms ReyesMath.GC03Energy.power_absorption
#print axioms ReyesMath.GC03Energy.integrated_absorption
#print axioms ReyesMath.GC03Energy.energy_coercivity
#print axioms ReyesMath.GC03Energy.cubic_quintic_d2_p2
#print axioms ReyesMath.GC03Energy.supercritical_scaling_iff
#print axioms ReyesMath.GC03Energy.singular_exponent_window_iff
#print axioms ReyesMath.GC03Energy.trajectory_kinetic_bound
#print axioms ReyesMath.GC03Energy.energy_drop_count
#print axioms ReyesMath.GC03Energy.finite_energy_drop_count
