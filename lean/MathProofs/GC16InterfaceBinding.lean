import MathProofs.GC16BulkBinding

/-! GC16: optimized finite increment and algebraic interface-gap transfer.
Candidate until exact Lean build and audit. The continuum cell-counting
estimate used in the analytical dossier is NOT assumed to be kernel proved. -/

open Filter Topology MeasureTheory Set
namespace ReyesMath.GC16InterfaceBinding
open Sobolev Sobolev.H2 StrictBinding GC16Shell GC16BulkBinding
variable {β γ k : ℝ}

/-- Excess energy per mass above the exact bulk floor. -/
noncomputable def bulkDensity (β γ k m : ℝ) : ℝ :=
  Imin β γ k m / m + bulk β γ

theorem bulkDensity_pos (hβ : 0 < β) (hγ : 0 < γ) {b : ℝ} (hb : 0 < b) :
    0 < bulkDensity β γ k b := by
  have hC := bulk_pos hβ hγ
  let s := bulk β γ / (β * b)
  have hs : 0 < s := div_pos hC (mul_pos hβ hb)
  have he : β * s * b = bulk β γ := by
    dsimp [s]
    field_simp [hβ.ne', hb.ne']
  have hsmall : β * s * b ≤ 2 * bulk β γ := by linarith only [he, hC]
  have h := inf_bulk_gap (β := β) (γ := γ) (k := k) hβ hγ hb hs hsmall
  have hd := (le_div_iff₀ hb).2 h
  have hmin : 0 < min (s ^ 2) (bulk β γ / 2) :=
    lt_min (by positivity) (by positivity)
  unfold bulkDensity
  linarith only [hd, hmin]

/-- Optimize the shifted-coupling parameter in the already verified increment
estimate. No value-function derivative or attainment is required. -/
theorem optimized_increment (hβ : 0 < β) (hγ : 0 < γ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    Imin β γ k (a + b) - Imin β γ k b ≤
      a * (-bulk β γ + 2 * bulk β γ * (a / b) +
        7 * bulkDensity β γ k b +
        8 * Real.sqrt (bulk β γ * bulkDensity β γ k b)) := by
  let C := bulk β γ
  let f := bulkDensity β γ k b
  have hC : 0 < C := bulk_pos hβ hγ
  have hf : 0 < f := bulkDensity_pos hβ hγ hb
  let z := Real.sqrt (f / C)
  have hz : 0 < z := Real.sqrt_pos.2 (div_pos hf hC)
  have hzsq : z ^ 2 = f / C := Real.sq_sqrt (div_nonneg hf.le hC.le)
  have hfz : C * z ^ 2 = f := by
    have h := (eq_div_iff hC.ne').1 hzsq
    linarith only [h]
  have hsqrt : Real.sqrt (C * f) = C * z := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hC.le hf.le)
      (mul_nonneg hC.le hz.le)).2
    rw [mul_pow]
    nlinarith only [congrArg (fun x : ℝ => C * x) hfz]
  have hfdiv : f / z = C * z := by
    apply (div_eq_iff hz.ne').2
    nlinarith only [hfz]
  let δ := β * z
  have hδ : 0 < δ := mul_pos hβ hz
  have hr1 : β / δ = 1 / z := by
    dsimp [δ]
    field_simp [hβ.ne', hz.ne']
  have hr2 : δ / β = z := by
    dsimp [δ]
    field_simp [hβ.ne']
  let t := 1 + a / b
  have ht : 1 ≤ t := by dsimp [t]; linarith [div_pos ha hb]
  have ht2 : t ≤ 2 := by
    dsimp [t]
    linarith [(div_le_one hb).2 hab]
  have hd : t - 1 = a / b := by dsimp [t]; ring
  have hm : (t - 1) * b = a := by
    rw [hd]
    field_simp [hb.ne']
  have htb : t * b = a + b := by nlinarith only [hm]
  have hi := inf_increment_bound (β := β) (γ := γ) (k := k) hβ hγ hb hδ ht ht2
  change Imin β γ k (t * b) - Imin β γ k b ≤ (t - 1) * b *
    (-C + 2 * C * (t - 1) + (7 + 4 * (β / δ)) * f + 4 * C * (δ / β)) at hi
  have he : (7 + 4 * (β / δ)) * f + 4 * C * (δ / β) =
      7 * f + 8 * Real.sqrt (C * f) := by
    rw [hr1, hr2, hsqrt]
    calc
      _ = 7 * f + 4 * (f / z) + 4 * C * z := by ring
      _ = _ := by rw [hfdiv]; ring
  have he' : -C + 2 * C * (t - 1) + (7 + 4 * (β / δ)) * f +
      4 * C * (δ / β) = -C + 2 * C * (a / b) + 7 * f + 8 * Real.sqrt (C * f) := by
    rw [hd]
    linarith only [he]
  rw [htb, hm, he'] at hi
  exact hi

/-- A general split certificate using the true bulk defect at both masses. -/
theorem strict_split_of_optimized_margin (hβ : 0 < β) (hγ : 0 < γ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hmargin : 2 * bulk β γ * (a / b) + 7 * bulkDensity β γ k b +
      8 * Real.sqrt (bulk β γ * bulkDensity β γ k b) < bulkDensity β γ k a) :
    Imin β γ k (a + b) < Imin β γ k a + Imin β γ k b := by
  have hi := optimized_increment (β := β) (γ := γ) (k := k) hβ hγ ha hb hab
  have hmul := mul_lt_mul_of_pos_left hmargin ha
  have he : a * (bulkDensity β γ k a - bulk β γ) = Imin β γ k a := by
    unfold bulkDensity
    field_simp [ha.ne'] <;> ring
  nlinarith only [hi, hmul, he]

/-- Algebraic consequence of the continuum cell-counting estimate.
This theorem does not establish that estimate. -/
theorem mass_bound_to_surface_gap {m F L : ℝ} (hm : 0 < m)
    (hF : 0 ≤ F) (hL : 0 < L) (hcell : m ≤ L * (F + F ^ 2)) :
    min (m / (2 * L)) (Real.sqrt (m / (2 * L))) ≤ F := by
  by_cases h : F ≤ 1
  · have hsq : F ^ 2 ≤ F := by
      nlinarith only [mul_nonneg hF (sub_nonneg.mpr h)]
    have hmul := mul_le_mul_of_nonneg_left hsq hL.le
    have hd : m / (2 * L) ≤ F := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * L)).2
      nlinarith only [hcell, hmul]
    exact (min_le_left _ _).trans hd
  · have hsq : F ≤ F ^ 2 := by
      nlinarith only [mul_nonneg hF (sub_nonneg.mpr (le_of_not_ge h))]
    have hmul := mul_le_mul_of_nonneg_left hsq hL.le
    have hd : m / (2 * L) ≤ F ^ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * L)).2
      nlinarith only [hcell, hmul]
    have hs := Real.sqrt_le_sqrt hd
    rw [Real.sqrt_sq hF] at hs
    exact (min_le_right _ _).trans hs

/-- Pass a fieldwise cell-counting inequality to the exact constrained infimum.
The hypothesis is precisely the analytical-to-Lean correspondence still needed. -/
theorem inf_surface_gap_of_cell_bound (hβ : 0 < β) (hγ : 0 < γ)
    {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (hcell : ∀ U : H2 2, M U = m →
      m ≤ L * ((energy β γ k U + bulk β γ * m) +
        (energy β γ k U + bulk β γ * m) ^ 2)) :
    min (m / (2 * L)) (Real.sqrt (m / (2 * L))) ≤
      Imin β γ k m + bulk β γ * m := by
  obtain ⟨U, hUm, _⟩ := NegativeEnergy.exists_negative (β := β) (γ := γ) (k := k) hβ hm
  have hne : (energy β γ k '' {U | M U = m}).Nonempty := ⟨_, U, hUm, rfl⟩
  have h : min (m / (2 * L)) (Real.sqrt (m / (2 * L))) - bulk β γ * m ≤
      Imin β γ k m := by
    apply le_csInf hne
    rintro _ ⟨V, hVm, rfl⟩
    have he := energy_ge_mass β γ k hγ V
    change -bulk β γ * M V ≤ energy β γ k V at he
    rw [hVm] at he
    have hF : 0 ≤ energy β γ k V + bulk β γ * m := by linarith only [he]
    have hg := mass_bound_to_surface_gap hm hF hL (hcell V hVm)
    linarith only [hg]
  linarith only [h]

end ReyesMath.GC16InterfaceBinding

#print axioms ReyesMath.GC16InterfaceBinding.bulkDensity_pos
#print axioms ReyesMath.GC16InterfaceBinding.optimized_increment
#print axioms ReyesMath.GC16InterfaceBinding.strict_split_of_optimized_margin
#print axioms ReyesMath.GC16InterfaceBinding.mass_bound_to_surface_gap
#print axioms ReyesMath.GC16InterfaceBinding.inf_surface_gap_of_cell_bound
