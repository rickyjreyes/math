import MathProofs.GC06NearZeroShell

/-!
GC06 / GC16: a larger all-split strict-binding interval obtained by combining
the virial identity with the Fourier sup bound, then chaining local amplitude
comparisons. No minimizer existence is assumed. Candidate until kernel checked.
-/

open Filter Topology Complex InnerProductSpace MeasureTheory Set
open scoped Topology

namespace ReyesMath.GC06VirialBinding
open Sobolev Sobolev.H2 StrictBinding
variable {β γ k : ℝ}

/-- A self-consistent bound on the ratio S/Q, retaining the virial sign. -/
theorem stationary_ratio (hβ : 0 < β) (hγ : 0 < γ) {m c : ℝ}
    (hc : 0 < c) (hB : 0 < β / 4 - γ / 3 * c)
    (hmargin : k ^ 2 * m / 4 + (β / 4 - γ / 3 * c) * m ^ 2 / 16 ≤ c)
    (W : H2 2) (hM : 0 < M W) (hMm : M W ≤ m)
    (hW : IsStationary β γ k W) : S W ≤ c * Q W := by
  let x := Real.sqrt (M W * D W)
  let B := β / 4 - γ / 3 * c
  have hB0 : 0 ≤ B := hB.le
  have hx2 : x ^ 2 = M W * D W := Real.sq_sqrt (mul_nonneg hM.le (D_nonneg W))
  have hQ := Q_le_of_ae_bound W (ae_sup_bound_opt W)
  change Q W ≤ x / 4 * M W at hQ
  have hSQ := S_le W
  change S W ≤ x / 4 * Q W at hSQ
  have hK := K_le_sqrt W
  change K W ≤ x at hK
  by_contra! hbad
  have hqpos := Q_pos W hM
  have hcx : c < x / 4 := by
    by_contra! h
    have hh := mul_le_mul_of_nonneg_right h hqpos.le
    linarith only [hh, hbad, hSQ]
  have hxpos : 0 < x := by linarith
  have hSlo := mul_lt_mul_of_pos_left hbad (show 0 < γ / 3 by positivity)
  have hKmul := mul_le_mul_of_nonneg_left hK (sq_nonneg k)
  have hD : D W ≤ k ^ 2 * x + B * Q W := by
    unfold IsStationary at hW
    dsimp [B]
    nlinarith only [hW, hSlo, hKmul]
  have hDm := mul_le_mul_of_nonneg_right hD hM.le
  have hQm := mul_le_mul_of_nonneg_left hQ (mul_nonneg (show 0 ≤ B from hB0) hM.le)
  have hprod : x * x ≤ (k ^ 2 * M W + B * M W ^ 2 / 4) * x := by
    nlinarith only [hx2, hDm, hQm]
  have hxup : x ≤ k ^ 2 * M W + B * M W ^ 2 / 4 := by
    by_contra! hh
    have hp := mul_lt_mul_of_pos_right hh hxpos
    linarith only [hp, hprod]
  have hkM := mul_le_mul_of_nonneg_left hMm (sq_nonneg k)
  have hMsq := pow_le_pow_left₀ hM.le hMm 2
  have hBM := mul_le_mul_of_nonneg_left hMsq hB0
  change k ^ 2 * m / 4 + B * m ^ 2 / 16 ≤ c at hmargin
  linarith only [hxup, hkM, hBM, hmargin, hcx]

/-- The uniform ratio bound can be chosen strictly below the amplitude-scaling
critical ratio whenever k²m < 3β/γ. -/
theorem exists_ratio (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m) (hk : k ^ 2 * m < 3 * β / γ) :
    ∃ c : ℝ, 0 < c ∧ c < 3 * β / (4 * γ) ∧
      ∀ W : H2 2, 0 < M W → M W ≤ m → IsStationary β γ k W → S W ≤ c * Q W := by
  let r := 3 * β / (4 * γ)
  let den := 2 + γ * m ^ 2 / 48
  let d := (r - k ^ 2 * m / 4) / den
  let c := r - d
  have hr4 : 4 * r = 3 * β / γ := by dsimp [r]; ring
  have hr_eq : γ / 3 * r = β / 4 := by
    dsimp [r]
    field_simp [hγ.ne']
    <;> ring
  have hgap : 0 < r - k ^ 2 * m / 4 := by linarith only [hk, hr4]
  have hden : 0 < den := by dsimp [den]; positivity
  have hd : 0 < d := div_pos hgap hden
  have hdeq : d * den = r - k ^ 2 * m / 4 := by
    dsimp only [d]
    field_simp [hden.ne']
  have hden1 : 1 < den := by
    dsimp [den]
    have hh : 0 ≤ γ * m ^ 2 / 48 := by positivity
    linarith
  have hdd := mul_lt_mul_of_pos_left hden1 hd
  have hkm : 0 ≤ k ^ 2 * m / 4 := by positivity
  have hc : 0 < c := by dsimp [c]; linarith only [hdd, hdeq, hkm]
  have hcr : c < r := by dsimp [c]; linarith
  have hcoefeq : β / 4 - γ / 3 * c = γ / 3 * d := by
    dsimp only [c]
    linarith only [hr_eq]
  have hcoef : 0 < β / 4 - γ / 3 * c := by rw [hcoefeq]; positivity
  have hceq : c = k ^ 2 * m / 4 + d * (1 + γ * m ^ 2 / 48) := by
    change d * (2 + γ * m ^ 2 / 48) = r - k ^ 2 * m / 4 at hdeq
    dsimp only [c]
    nlinarith only [hdeq]
  have hmargin : k ^ 2 * m / 4 + (β / 4 - γ / 3 * c) * m ^ 2 / 16 ≤ c := by
    rw [hcoefeq, hceq]
    nlinarith only [hd.le]
  refine ⟨c, hc, hcr, ?_⟩
  intro W hWm hWmm hW
  exact stationary_ratio hβ hγ hc hcoef hmargin W hWm hWmm hW

/-- Strict decrease for a small amplitude increment, using a uniform ratio
bound on dilation-stationary fields. -/
theorem local_comparison (hβ : 0 < β) (hγ : 0 < γ) {a b c : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hratio : ∀ W : H2 2, M W = a → IsStationary β γ k W → S W ≤ c * Q W)
    (hstep : γ * (b / a + 1) / 3 * c < β / 2) :
    Imin β γ k b / b < Imin β γ k a / a := by
  let t := b / a
  have ht : 1 < t := (one_lt_div ha).2 hab
  have ht0 : 0 < t := by linarith
  have hb : 0 < b := ha.trans hab
  have hta : t * a = b := by dsimp [t]; field_simp [ha.ne']
  let h := 1 - (γ * (t + 1) / 3 * c) / (β / 2)
  have hh : 0 < h := by
    dsimp only [h]
    apply sub_pos.mpr
    exact (div_lt_one (by positivity)).2 hstep
  have hhalf : β / 2 * h = β / 2 - γ * (t + 1) / 3 * c := by
    dsimp only [h]
    field_simp [hβ.ne']
    <;> ring
  let C := 1 + (t - 1) * h
  have hCgt : 1 < C := by
    dsimp [C]
    have hp := mul_pos (sub_pos.mpr ht) hh
    linarith
  have hC : 0 < C := by linarith
  let J := Imin β γ k a
  have hJ : J < 0 := (NegativeEnergy.negative_constrained_energy (k := k) hβ hγ ha).2
  have hkey : Imin β γ k b / t ≤ C * J := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨U, hUm, hUlt⟩ := exists_energy_lt (γ := γ) (k := k) hβ ha
      (ε := ε / (2 * C)) (by positivity)
    change energy β γ k U < J + ε / (2 * C) at hUlt
    obtain ⟨W, hWm, hWle, hWst⟩ := exists_stationary_dil k hβ hγ U (by rw [hUm]; exact ha)
    rw [hUm] at hWm
    obtain ⟨V, hVm, hVE⟩ := exists_scaled (β := β) (γ := γ) (k := k) W (t := t) ht0.le
    have hSQ := hratio W hWm hWst
    have hcoef : 0 ≤ γ * (t + 1) / 3 := by positivity
    have hSQ' := mul_le_mul_of_nonneg_left hSQ hcoef
    have hhalfQ := congrArg (fun z : ℝ => z * Q W) hhalf
    have hbound : -β / 2 * Q W + γ * (t + 1) / 3 * S W ≤ -(β / 2 * h) * Q W := by
      nlinarith only [hSQ', hhalfQ]
    have hEW : -β / 2 * Q W ≤ energy β γ k W := by
      rw [energy_eq]
      have hS : 0 ≤ γ / 3 * S W := by positivity
      linarith only [T_nonneg k W, hS]
    have hEW' := mul_le_mul_of_nonneg_left hEW hh.le
    have hbound' : -β / 2 * Q W + γ * (t + 1) / 3 * S W ≤ h * energy β γ k W := by
      nlinarith only [hbound, hEW']
    have hmul := mul_le_mul_of_nonneg_left hbound'
      (mul_nonneg ht0.le (sub_nonneg.mpr ht.le))
    have heq : energy β γ k V - t * energy β γ k W =
        t * (t - 1) * (-β / 2 * Q W + γ * (t + 1) / 3 * S W) := by
      rw [hVE, energy_eq β γ k W]
      ring
    have hscaled : energy β γ k V / t ≤ C * energy β γ k W := by
      apply (div_le_iff₀ ht0).2
      dsimp only [C]
      nlinarith only [heq, hmul]
    have hIb : Imin β γ k b ≤ energy β γ k V :=
      Imin_le_energy hγ (by rw [hVm, hWm, hta])
    have h1 := div_le_div_of_nonneg_right hIb ht0.le
    have h2 : C * energy β γ k W ≤ C * (J + ε / (2 * C)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hWle, hUlt]) hC.le
    have h3 : C * (J + ε / (2 * C)) = C * J + ε / 2 := by
      field_simp [hC.ne']
    linarith only [h1, hscaled, h2, h3, hε]
  have hCJ : C * J < J := by
    have hp := mul_pos (sub_pos.mpr hCgt) (neg_pos.mpr hJ)
    nlinarith only [hp]
  have hbdiv : Imin β γ k b / b = Imin β γ k b / t / a := by
    rw [div_div, hta]
  rw [hbdiv]
  exact div_lt_div_of_pos_right (hkey.trans_lt hCJ) ha

/-- Finite chaining of uniform local strict comparisons on a real interval. -/
theorem chain_strict (f : ℝ → ℝ) {a b d : ℝ} (hab : a < b) (hd : 0 < d)
    (hlocal : ∀ x y : ℝ, a ≤ x → x < y → y ≤ b → y - x ≤ d → f y < f x) :
    f b < f a := by
  have hchain : ∀ n : ℕ, ∀ y : ℝ, a < y → y ≤ b → y - a ≤ (n : ℝ) * d → f y < f a := by
    intro n
    induction n with
    | zero =>
      intro y hay hy hdist
      norm_num at hdist
      linarith
    | succ n ih =>
      intro y hay hy hdist
      by_cases hstep : y - a ≤ d
      · exact hlocal a y le_rfl hay hy hstep
      · let z := y - d
        have haz : a < z := by dsimp [z]; linarith
        have hzy : z < y := by dsimp [z]; linarith
        have hzd : z - a ≤ (n : ℝ) * d := by
          push_cast at hdist
          dsimp [z]
          linarith only [hdist]
        have hf := hlocal z y haz.le hzy hy (by dsimp [z]; linarith)
        exact hf.trans (ih z haz (hzy.le.trans hy) hzd)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / d)
  exact hchain n b hab le_rfl ((div_lt_iff₀ hd).mp hn).le

/-- Strict decrease throughout the entire larger interval, including all
positive masses at k=0. -/
theorem energy_per_mass_strict (hβ : 0 < β) (hγ : 0 < γ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hk : k ^ 2 * b < 3 * β / γ) :
    Imin β γ k b / b < Imin β γ k a / a := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨c, hc, hcr, hratio⟩ := exists_ratio hβ hγ hb hk
  let r := 3 * β / (4 * γ)
  let l := r / c
  have hl : 1 < l := (one_lt_div hc).2 hcr
  let d := (l - 1) * a
  have hd : 0 < d := mul_pos (sub_pos.mpr hl) ha
  apply chain_strict (fun x => Imin β γ k x / x) hab hd
  intro x y hax hxy hyb hdist
  have hx : 0 < x := ha.trans_le hax
  have hxm : x ≤ b := hxy.le.trans hyb
  have hm := mul_le_mul_of_nonneg_left hax (sub_nonneg.mpr hl.le)
  have hyl : y ≤ l * x := by
    dsimp only [d] at hdist
    nlinarith only [hm, hdist]
  have htl : y / x ≤ l := (div_le_iff₀ hx).2 hyl
  have hlc : l * c = r := by dsimp only [l]; field_simp [hc.ne']
  have htc := mul_le_mul_of_nonneg_right htl hc.le
  have htr : (y / x + 1) * c < 2 * r := by
    change c < r at hcr
    nlinarith only [htc, hlc, hcr]
  have hr_eq : γ / 3 * (2 * r) = β / 2 := by
    dsimp [r]
    field_simp [hγ.ne']
    <;> ring
  have hstep := mul_lt_mul_of_pos_left htr (show 0 < γ / 3 by positivity)
  apply local_comparison hβ hγ hx hxy
  · intro W hWm hWst
    exact hratio W (by rw [hWm]; exact hx) (by rw [hWm]; exact hxm) hWst
  · nlinarith only [hstep, hr_eq]

theorem strict_binding_virial (hβ : 0 < β) (hγ : 0 < γ) {m a : ℝ}
    (hm : 0 < m) (hk : k ^ 2 * m < 3 * β / γ) (ha : 0 < a) (ham : a < m) :
    Imin β γ k m < Imin β γ k a + Imin β γ k (m - a) := by
  have hb : 0 < m - a := by linarith
  have e1 := energy_per_mass_strict hβ hγ ha ham hk
  have e2 := energy_per_mass_strict hβ hγ hb (show m - a < m by linarith) hk
  have f1 : a * (Imin β γ k m / m) < Imin β γ k a := by
    have h := mul_lt_mul_of_pos_left e1 ha
    rwa [mul_div_cancel₀ _ ha.ne'] at h
  have f2 : (m - a) * (Imin β γ k m / m) < Imin β γ k (m - a) := by
    have h := mul_lt_mul_of_pos_left e2 hb
    rwa [mul_div_cancel₀ _ hb.ne'] at h
  have hsum : a * (Imin β γ k m / m) + (m - a) * (Imin β γ k m / m) =
      Imin β γ k m := by field_simp; ring
  linarith

theorem compactness_virial (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m) (hk : k ^ 2 * m < 3 * β / γ) {u : ℕ → H2 2}
    (hM : ∀ n, M (u n) = m)
    (hE : Tendsto (fun n => energy β γ k (u n)) atTop (𝓝 (Imin β γ k m))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → EuclideanSpace ℝ (Fin 2),
      ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m ∧
      Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) atTop (𝓝 0) :=
  WholeSpace.compactness_of_binding hβ hγ hm
    (fun a ha ham => strict_binding_virial hβ hγ hm hk ha ham) hM hE

theorem exists_minimizer_virial (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m) (hk : k ^ 2 * m < 3 * β / γ) :
    ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m :=
  WholeSpace.exists_minimizer_of_binding hβ hγ hm
    (fun a ha ham => strict_binding_virial hβ hγ hm hk ha ham)

theorem exists_minimizer_zero_all_mass (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m) : ∃ U : H2 2, M U = m ∧ energy β γ 0 U = Imin β γ 0 m :=
  exists_minimizer_virial hβ hγ hm (by simp; positivity)

end ReyesMath.GC06VirialBinding

#print axioms ReyesMath.GC06VirialBinding.stationary_ratio
#print axioms ReyesMath.GC06VirialBinding.exists_ratio
#print axioms ReyesMath.GC06VirialBinding.local_comparison
#print axioms ReyesMath.GC06VirialBinding.chain_strict
#print axioms ReyesMath.GC06VirialBinding.energy_per_mass_strict
#print axioms ReyesMath.GC06VirialBinding.strict_binding_virial
#print axioms ReyesMath.GC06VirialBinding.compactness_virial
#print axioms ReyesMath.GC06VirialBinding.exists_minimizer_virial
#print axioms ReyesMath.GC06VirialBinding.exists_minimizer_zero_all_mass
