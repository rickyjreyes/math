import MathProofs.OrbitalStability

/-!
# GC01: isolated individual orbits and the exact dilation obstruction

Candidate extension of F01. The isolation hypothesis concerns the geometry of
the minimizing set, not the evolution. No assertion of uniqueness or of
instability from negative energy curvature is made. The second theorem family
uses the exact H² dilation identity, not a periodic Fourier surrogate.
-/

open Filter Topology Set
namespace ReyesMath
namespace GC01IndividualOrbit
open Sobolev Sobolev.H2 OrbitalStability

local notation "R2" => EuclideanSpace ℝ (Fin 2)
variable {β γ k : ℝ}

/-- Multiplication by any unit complex number and spatial translation. -/
def orbit (φ : H2 2) : Set (H2 2) :=
  {v | ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ y : R2, v = H2.smul c (translate y φ)}

theorem orbit_nonempty (φ : H2 2) : (orbit φ).Nonempty :=
  ⟨H2.smul 1 (translate 0 φ), 1, by simp, 0, rfl⟩

theorem orbit_subset_Gset {m : ℝ} {φ : H2 2} (hφ : φ ∈ Gset β γ k m) :
    orbit φ ⊆ Gset β γ k m := by
  rintro v ⟨c, hc, y, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [M_smul, hc, one_pow, one_mul, M_translate]
    exact hφ.1
  · rw [energy_eq, T_smul, Q_smul, S_smul, hc]
    simp only [one_pow, one_mul]
    rw [← energy_eq, energy_translate]
    exact hφ.2

theorem distX_triangle_left {E : Set (H2 2)} (hE : E.Nonempty) (u v : H2 2) :
    distX u E ≤ distH2 u v + distX v E := by
  by_contra! h
  obtain ⟨g, hg, hd⟩ := exists_of_distX_lt hE
    (show distX v E < distX u E - distH2 u v by linarith)
  linarith [distX_le hg, distH2_triangle u v g]

theorem distX_mono {A B : Set (H2 2)} (hA : A.Nonempty) (hAB : A ⊆ B)
    (u : H2 2) : distX u B ≤ distX u A := by
  by_contra! h
  obtain ⟨g, hg, hd⟩ := exists_of_distX_lt hA h
  exact (not_lt_of_ge (distX_le (hAB hg))) hd

theorem continuous_distX_solution {E : Set (H2 2)} (hE : E.Nonempty)
    {u : ℝ → H2 2} (hu : IsSolution β γ k u) :
    Continuous (fun t => distX (u t) E) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun s => norm_nonneg _) (fun s => ?_) (hu.1 t)
  rw [Real.norm_eq_abs, abs_le]
  have h1 := distX_triangle_left hE (u s) (u t)
  have h2 := distX_triangle_left hE (u t) (u s)
  rw [distH2_comm (u t) (u s)] at h2
  exact ⟨by linarith, by linarith⟩

/-- A single phase-translation orbit which is isolated inside the full minimizing
set is stable, even if other minimizing orbits exist. Perturbations may change
mass. The conclusion quantifies over the original global whole-space flow. -/
theorem isolated_orbit_stability (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m) (hmB : m ≤ StrictBinding.mB β γ k) {φ : H2 2}
    (hφ : φ ∈ Gset β γ k m) {r : ℝ} (hr : 0 < r)
    (hiso : ∀ g ∈ Gset β γ k m, distX g (orbit φ) < r → g ∈ orbit φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ℝ → H2 2, IsSolution β γ k u →
      distX (u 0) (orbit φ) < δ →
      BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} => distX (u t) (orbit φ)) ∧
      (⨆ t : {t : ℝ // 0 ≤ t}, distX (u t) (orbit φ)) < ε := by
  let η : ℝ := min r ε / 8
  have hη : 0 < η := div_pos (lt_min hr hε) (by norm_num)
  have hηr : 8 * η ≤ r := by
    dsimp [η]
    linarith [min_le_left r ε]
  have hηε : 8 * η ≤ ε := by
    dsimp [η]
    linarith [min_le_right r ε]
  obtain ⟨δ₀, hδ₀, hcore⟩ := stable_core hβ hγ hm hmB hη
  have hO := orbit_nonempty φ
  have hG : (Gset β γ k m).Nonempty := ⟨φ, hφ⟩
  refine ⟨min δ₀ η, lt_min hδ₀ hη, fun u hu h0 => ?_⟩
  have hinit : distX (u 0) (orbit φ) < η := h0.trans_le (min_le_right _ _)
  have hset : ∀ t, distX (u t) (Gset β γ k m) < η := fun t =>
    hcore (u 0) (u t) (conservation hu t).1 (conservation hu t).2
      (lt_of_le_of_lt (distX_mono hO (orbit_subset_Gset hφ) (u 0))
        (h0.trans_le (min_le_left _ _)))
  have hcont := continuous_distX_solution hO hu
  have hall : ∀ t : ℝ, 0 ≤ t → distX (u t) (orbit φ) < 2 * η := by
    intro t ht
    by_contra! hfar
    have hmid : 2 * η ∈ Icc (distX (u 0) (orbit φ)) (distX (u t) (orbit φ)) :=
      ⟨by linarith, hfar⟩
    obtain ⟨s, _, hs⟩ := intermediate_value_Icc ht hcont.continuousOn hmid
    obtain ⟨g, hg, hd⟩ := exists_of_distX_lt hG (hset s)
    have hnear := distX_triangle_left hO g (u s)
    rw [distH2_comm g (u s)] at hnear
    have hgo : g ∈ orbit φ := hiso g hg (by linarith)
    have hle : distX (u s) (orbit φ) ≤ distH2 (u s) g := distX_le hgo
    linarith
  have hbd : ∀ t : {t : ℝ // 0 ≤ t}, distX (u t) (orbit φ) ≤ 2 * η :=
    fun t => (hall t t.property).le
  refine ⟨⟨2 * η, ?_⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hbd t
  · exact lt_of_le_of_lt (ciSup_le hbd) (by linarith)

/-- The exact global mass-preserving dilation energy gap at a virial-stationary
profile. The hypothesis is the repository's dilation identity, not the full
weak stationary PDE; deriving it for every weak stationary profile is separate. -/
theorem stationary_dilation_gap {U : H2 2} (hU : IsStationary β γ k U)
    {lam : ℝ} (hlam : 0 < lam) :
    energy β γ k (dil hlam U) - energy β γ k U =
      (D U + γ / 3 * S U) * (lam ^ 2 - 1) ^ 2 := by
  rw [energy_dil, energy_expand]
  unfold IsStationary at hU
  have hB : 2 * k ^ 2 * K U + β / 2 * Q U = 2 * (D U + γ / 3 * S U) := by
    linarith
  rw [hB]
  ring

/-- No nontrivial mass-preserving isotropic dilation lowers energy at a
positive-mass virial-stationary profile in the cubic-quintic model. This is
not a claim of positivity in all constrained Hessian directions. -/
theorem stationary_dilation_strict (hγ : 0 < γ) {U : H2 2}
    (hM : 0 < M U) (hU : IsStationary β γ k U)
    {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    energy β γ k U < energy β γ k (dil hlam U) := by
  have hP : 0 < D U + γ / 3 * S U :=
    add_pos_of_nonneg_of_pos (D_nonneg U) (mul_pos (by positivity) (S_pos U hM))
  have hne2 : lam ^ 2 - 1 ≠ 0 := by
    intro hz
    have hprod : (lam - 1) * (lam + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · exact hne (by linarith)
    · linarith
  have hp : 0 < (D U + γ / 3 * S U) * (lam ^ 2 - 1) ^ 2 :=
    mul_pos hP (sq_pos_of_ne_zero hne2)
  rw [← stationary_dilation_gap hU hlam] at hp
  linarith

end GC01IndividualOrbit
end ReyesMath
