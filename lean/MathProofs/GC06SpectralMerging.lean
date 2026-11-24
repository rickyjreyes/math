import MathProofs.GC16InterfaceBinding

/-! GC06 unrestricted spectral merging: exact amplitude/infimum algebra and
the low-density Hessian sign. The analytic spectral and profile-decomposition
hypotheses are explicit; this file does not certify the all-mass theorem. -/

open Filter Topology Set MeasureTheory
namespace ReyesMath.GC06SpectralMerging
open Sobolev Sobolev.H2 StrictBinding
variable {β γ k : ℝ}

/-- Exact mass-amplitude polynomial in the original F01 model. -/
noncomputable def amp (β γ k : ℝ) (U : H2 2) (t : ℝ) : ℝ :=
  t * T k U - β / 2 * (t ^ 2 * Q U) + γ / 3 * (t ^ 3 * S U)

/-- The amplitude derivative divided by the original mass. For a weak
Euler-Lagrange solution, testing its equation with U identifies this scalar
with the Lagrange multiplier. That PDE correspondence is not proved here. -/
noncomputable def multiplier (β γ k : ℝ) (U : H2 2) : ℝ :=
  (T k U - β * Q U + γ * S U) / M U

theorem amp_one (U : H2 2) : amp β γ k U 1 = energy β γ k U := by
  rw [energy_eq]
  unfold amp
  ring

/-- Ordinary subadditivity is an explicit continuum obligation. -/
theorem mass_deletion_comparison (hβ : 0 < β) (hγ : 0 < γ) (U : H2 2)
    (hM : 0 < M U) (hU : energy β γ k U = Imin β γ k (M U))
    (hsub : ∀ a b : ℝ, 0 < a → 0 < b →
      Imin β γ k (a + b) ≤ Imin β γ k a + Imin β γ k b)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    amp β γ k U 1 < amp β γ k U t := by
  have ha := mul_pos ht hM
  have hb := mul_pos (sub_pos.mpr ht1) hM
  have hsum : t * M U + (1 - t) * M U = M U := by ring
  have hs := hsub _ _ ha hb
  rw [hsum] at hs
  have hn := (NegativeEnergy.negative_constrained_energy (k := k) hβ hγ hb).2
  obtain ⟨V, hVm, hVe⟩ := exists_scaled (β := β) (γ := γ) (k := k) U ht.le
  have hi := Imin_le_energy (β := β) (k := k) hγ hVm
  change energy β γ k V = amp β γ k U t at hVe
  rw [amp_one, hU]
  linarith only [hs, hn, hi, hVe]

/-- Any two attained profiles saturating ordinary subadditivity minimize the
exact mass-transfer polynomial at zero. -/
theorem mass_exchange_comparison (hγ : 0 < γ) (U V : H2 2)
    (hMu : 0 < M U) (hMv : 0 < M V)
    (hU : energy β γ k U = Imin β γ k (M U))
    (hV : energy β γ k V = Imin β γ k (M V))
    (heq : Imin β γ k (M U + M V) =
      Imin β γ k (M U) + Imin β γ k (M V))
    (hsub : ∀ a b : ℝ, 0 < a → 0 < b →
      Imin β γ k (a + b) ≤ Imin β γ k a + Imin β γ k b)
    {h : ℝ} (hlo : -M U < h) (hhi : h < M V) :
    amp β γ k U 1 + amp β γ k V 1 ≤
      amp β γ k U (1 + h / M U) + amp β γ k V (1 - h / M V) := by
  have ha : 0 < M U + h := by linarith
  have hb : 0 < M V - h := by linarith
  have ht : 0 < 1 + h / M U := by
    rw [show 1 + h / M U = (M U + h) / M U by field_simp [hMu.ne']]
    exact div_pos ha hMu
  have hs : 0 < 1 - h / M V := by
    rw [show 1 - h / M V = (M V - h) / M V by field_simp [hMv.ne']]
    exact div_pos hb hMv
  obtain ⟨W, hWm, hWe⟩ := exists_scaled (β := β) (γ := γ) (k := k) U ht.le
  obtain ⟨Z, hZm, hZe⟩ := exists_scaled (β := β) (γ := γ) (k := k) V hs.le
  have hWm' : M W = M U + h := by
    rw [hWm]
    field_simp [hMu.ne'] <;> ring
  have hZm' : M Z = M V - h := by
    rw [hZm]
    field_simp [hMv.ne'] <;> ring
  have hw := Imin_le_energy (β := β) (k := k) hγ hWm'
  have hz := Imin_le_energy (β := β) (k := k) hγ hZm'
  have hi := hsub _ _ ha hb
  rw [show M U + h + (M V - h) = M U + M V by ring, heq] at hi
  change energy β γ k W = amp β γ k U (1 + h / M U) at hWe
  change energy β γ k Z = amp β γ k V (1 - h / M V) at hZe
  rw [amp_one, amp_one, hU, hV]
  linarith only [hw, hz, hi, hWe, hZe]

/-- Scalar sign needed for the angular Helmholtz threshold test. The variables
are density, squared perturbation norm, and real overlap, respectively. -/
theorem low_density_hessian (hβ : 0 < β) (hγ : 0 < γ)
    {ρ z p : ℝ} (hρ : 0 ≤ ρ) (hz : 0 ≤ z) (hd : ρ ≤ β / (4 * γ)) :
    (-β * ρ + γ * ρ ^ 2) * z + (-2 * β + 4 * γ * ρ) * p ^ 2
      ≤ -(3 * β / 4) * ρ * z := by
  have h4' := (le_div_iff₀ (by positivity : 0 < 4 * γ)).mp hd
  have h4 : 4 * γ * ρ ≤ β := by nlinarith only [h4']
  have hcoef : -2 * β + 4 * γ * ρ ≤ 0 := by linarith
  have hcoef' : -β * ρ + γ * ρ ^ 2 ≤ -(3 * β / 4) * ρ := by
    nlinarith only [mul_le_mul_of_nonneg_right h4 hρ]
  have h1 := mul_le_mul_of_nonneg_right hcoef' hz
  have h2 := mul_nonpos_of_nonpos_of_nonneg hcoef (sq_nonneg p)
  linarith only [h1, h2]

/-- Exact obstruction reduction: the analytical finite-cluster extraction
must supply a pair of attained profiles saturating ordinary subadditivity
whenever some split fails. The analytical spectral merging must exclude such
a pair. Neither continuum input is disguised as an axiom. -/
theorem all_binding_of_pair_exclusion
    (hcluster : ∀ m a : ℝ, 0 < m → 0 < a → a < m →
      ¬ Imin β γ k m < Imin β γ k a + Imin β γ k (m - a) →
      ∃ U V : H2 2, 0 < M U ∧ 0 < M V ∧
        energy β γ k U = Imin β γ k (M U) ∧
        energy β γ k V = Imin β γ k (M V) ∧
        Imin β γ k (M U + M V) = Imin β γ k (M U) + Imin β γ k (M V))
    (hmerge : ∀ U V : H2 2, 0 < M U → 0 < M V →
      energy β γ k U = Imin β γ k (M U) →
      energy β γ k V = Imin β γ k (M V) →
      Imin β γ k (M U + M V) ≠ Imin β γ k (M U) + Imin β γ k (M V))
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) (ham : a < m) :
    Imin β γ k m < Imin β γ k a + Imin β γ k (m - a) := by
  by_contra hn
  obtain ⟨U, V, hMu, hMv, hU, hV, heq⟩ := hcluster m a hm ha ham hn
  exact hmerge U V hMu hMv hU hV heq

end ReyesMath.GC06SpectralMerging
