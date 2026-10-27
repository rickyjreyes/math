import Mathlib

/-!
# Cazenave–Lions orbital-stability reduction

An *abstract*, fully quantified orbital-stability implication.  It is
independent of which equation generates the flow:

1. Near the minimizing set, both mass and energy are uniformly near
   their constrained-minimum values.
2. Any state with nearly correct mass and nearly minimizing energy is
   close to the minimizing set.  For an actual Hamiltonian this must
   follow from concentration-compactness and strong H² precompactness
   modulo translations.
3. A globally defined flow conserves mass and energy.

Then the minimizing set is orbitally stable for that flow.  This lemma
does not establish (2) for the cubic–quintic fourth-order PDE or
construct its global H² flow; those obligations remain open.
-/

namespace ReyesMath
namespace OrbitalStabilityCriterion

variable {X : Type*} [MetricSpace X]

/-- Being within tolerance of a set, avoiding assumptions about a
set-distance infimum being attained. -/
def Near (S : Set X) (u : X) (ε : ℝ) : Prop :=
  ∃ v ∈ S, dist u v < ε

/-- The exact abstract compactness + conservation orbital-stability theorem. -/
theorem orbital_stability_of_near_minimizers
    (S : Set X) (flow : ℝ → X → X) (mass energy : X → ℝ)
    (m I : ℝ)
    (hnear : ∀ δ > 0, ∃ η > 0, ∀ u : X, Near S u η →
      |mass u - m| < δ ∧ energy u < I + δ)
    (hcompact : ∀ ε > 0, ∃ δ > 0, ∀ u : X,
      |mass u - m| < δ → energy u < I + δ → Near S u ε)
    (hmass : ∀ t u, mass (flow t u) = mass u)
    (henergy : ∀ t u, energy (flow t u) = energy u) :
    ∀ ε > 0, ∃ η > 0, ∀ u : X, Near S u η →
      ∀ t : ℝ, Near S (flow t u) ε := by
  intro ε hε
  obtain ⟨δ, hδ, hgood⟩ := hcompact ε hε
  obtain ⟨η, hη, hcontrols⟩ := hnear δ hδ
  refine ⟨η, hη, ?_⟩
  intro u hu t
  obtain ⟨hmu, heu⟩ := hcontrols u hu
  apply hgood (flow t u)
  · simpa only [hmass t u] using hmu
  · simpa only [henergy t u] using heu

end OrbitalStabilityCriterion
end ReyesMath
