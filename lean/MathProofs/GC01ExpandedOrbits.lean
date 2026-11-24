import MathProofs.GC01IndividualOrbit
import MathProofs.GC06VirialBinding
import MathProofs.GC16ShellBinding

/-! Propagate the merged binding improvements to individual-orbit stability.
Isolation is still required. Candidate until exact build and axiom audit. -/
open Filter Topology Set
namespace ReyesMath.GC01ExpandedOrbits
open Sobolev Sobolev.H2 OrbitalStability GC01IndividualOrbit
variable {β γ k : ℝ}

/-- The individual minimizing orbit theorem needs binding, not the original
mass ceiling. -/
theorem isolated_orbit_stability_of_binding (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m)
    (hbind : ∀ a : ℝ, 0 < a → a < m → Imin β γ k m < Imin β γ k a + Imin β γ k (m - a))
    {φ : H2 2}
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
  obtain ⟨δ₀, hδ₀, hcore⟩ := stable_core_of_binding hβ hγ hm hbind hη
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
  letI : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  have hbd : ∀ t : {t : ℝ // 0 ≤ t}, distX (u t) (orbit φ) ≤ 2 * η :=
    fun t => (hall t t.property).le
  refine ⟨⟨2 * η, ?_⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hbd t
  · exact lt_of_le_of_lt (ciSup_le hbd) (by linarith)


/-- Combine the two verified sufficient regions without weakening either. -/
theorem binding_of_either (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m)
    (hcover : m ≤ GC16Shell.mShell β γ ∨ k ^ 2 * m ≤ 3 * β / γ) :
    ∀ a : ℝ, 0 < a → a < m → Imin β γ k m < Imin β γ k a + Imin β γ k (m - a) := by
  intro a ha ham
  rcases hcover with h | h
  · exact GC16Shell.strict_binding_shell hβ hγ hm h ha ham
  · exact GC06VirialBinding.strict_binding_closed hβ hγ hm h ha ham

theorem exists_minimizer_expanded (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m)
    (hcover : m ≤ GC16Shell.mShell β γ ∨ k ^ 2 * m ≤ 3 * β / γ) :
    ∃ U : H2 2, M U = m ∧ energy β γ k U = Imin β γ k m :=
  WholeSpace.exists_minimizer_of_binding hβ hγ hm (binding_of_either hβ hγ hm hcover)

theorem orbital_stability_expanded (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m)
    (hcover : m ≤ GC16Shell.mShell β γ ∨ k ^ 2 * m ≤ 3 * β / γ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ℝ → H2 2, IsSolution β γ k u →
      distX (u 0) (Gset β γ k m) < δ →
      BddAbove (Set.range fun t => distX (u t) (Gset β γ k m)) ∧
      ⨆ t, distX (u t) (Gset β γ k m) < ε :=
  orbital_stability_of_binding hβ hγ hm (binding_of_either hβ hγ hm hcover) hε

theorem isolated_orbit_stability_expanded (hβ : 0 < β) (hγ : 0 < γ) {m : ℝ}
    (hm : 0 < m)
    (hcover : m ≤ GC16Shell.mShell β γ ∨ k ^ 2 * m ≤ 3 * β / γ)
    {φ : H2 2} (hφ : φ ∈ Gset β γ k m) {r : ℝ} (hr : 0 < r)
    (hiso : ∀ g ∈ Gset β γ k m, distX g (orbit φ) < r → g ∈ orbit φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ℝ → H2 2, IsSolution β γ k u →
      distX (u 0) (orbit φ) < δ →
      BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} => distX (u t) (orbit φ)) ∧
      (⨆ t : {t : ℝ // 0 ≤ t}, distX (u t) (orbit φ)) < ε :=
  isolated_orbit_stability_of_binding hβ hγ hm (binding_of_either hβ hγ hm hcover)
    hφ hr hiso hε

end ReyesMath.GC01ExpandedOrbits

#print axioms ReyesMath.GC01ExpandedOrbits.isolated_orbit_stability_of_binding
#print axioms ReyesMath.GC01ExpandedOrbits.binding_of_either
#print axioms ReyesMath.GC01ExpandedOrbits.exists_minimizer_expanded
#print axioms ReyesMath.GC01ExpandedOrbits.orbital_stability_expanded
#print axioms ReyesMath.GC01ExpandedOrbits.isolated_orbit_stability_expanded
