import MathProofs.V18MiddleFloor

/-!
# F09: derivatives of the ACTUAL clipped middle observation function

The original source-matched 31-dimensional forward model includes a
nonsmooth max-floor at 10⁻¹². It is not legitimate to differentiate
the raw middle formula and silently equate that derivative with the
physical observation derivative unless the floor is inactive.

V18MiddleFloor establishes strict interiority for all five frozen
middle outputs. This module proves the generic local max derivative
lemma and then transports the five 31-coordinate source derivative
identities to the actual clipped middle model.
-/

noncomputable section
namespace ReyesMath.V18MiddleClipped

open Filter
open scoped Topology

/-- Differentiating max(f,c) is legitimate at a point where f is
strictly above c. The proof establishes equality on a neighborhood. -/
theorem hasDerivAt_max_of_gt
    (f : ℝ → ℝ) (c d x : ℝ)
    (hder : HasDerivAt f d x) (hcl : c < f x) :
    HasDerivAt (fun y => max (f y) c) d x := by
  have hnhds : Set.Ioi c ∈ 𝓝 (f x) := isOpen_Ioi.mem_nhds hcl
  have hev : ∀ᶠ y in 𝓝 x, c < f y :=
    hder.continuousAt.eventually_mem hnhds
  have heq : (fun y => max (f y) c) =ᶠ[𝓝 x] f :=
    hev.mono (fun y hy => max_eq_left (le_of_lt hy))
  exact hder.congr_of_eventuallyEq heq

variable (p : V18Forward.Params) (n : ℕ)
variable (h : (1e-12 : ℝ) < V18Forward.middleRaw p n)
include h

/-- The five actual observed middle partial derivatives are exactly
the selected analytic Jacobian row when the floor is inactive. -/
theorem offset_derivative :
    HasDerivAt
      (fun x => V18Forward.middle (Function.update p (14 : Fin 31) x) n)
      1 (p 14) := by
  have hraw := V18Forward.middle_offset_coordinate_derivative n p
  change HasDerivAt
    (fun x => max (V18Forward.middleRaw (Function.update p (14 : Fin 31) x) n)
      (1e-12 : ℝ)) 1 (p 14)
  apply hasDerivAt_max_of_gt _ _ _ _ hraw
  simpa only [Function.update_eq_self] using h

theorem quad_derivative :
    HasDerivAt
      (fun x => V18Forward.middle (Function.update p (15 : Fin 31) x) n)
      ((n : ℝ) ^ 2) (p 15) := by
  have hraw := V18Forward.middle_quad_coordinate_derivative n p
  change HasDerivAt
    (fun x => max (V18Forward.middleRaw (Function.update p (15 : Fin 31) x) n)
      (1e-12 : ℝ)) ((n : ℝ) ^ 2) (p 15)
  apply hasDerivAt_max_of_gt _ _ _ _ hraw
  simpa only [Function.update_eq_self] using h

theorem amplitude_derivative :
    HasDerivAt
      (fun x => V18Forward.middle (Function.update p (9 : Fin 31) x) n)
      (Real.sin ((5.0632 : ℝ) * n + p 12)) (p 9) := by
  have hraw := V18Forward.middle_amp_coordinate_derivative n p
  change HasDerivAt
    (fun x => max (V18Forward.middleRaw (Function.update p (9 : Fin 31) x) n)
      (1e-12 : ℝ)) (Real.sin ((5.0632 : ℝ) * n + p 12)) (p 9)
  apply hasDerivAt_max_of_gt _ _ _ _ hraw
  simpa only [Function.update_eq_self] using h

theorem phase_derivative :
    HasDerivAt
      (fun x => V18Forward.middle (Function.update p (12 : Fin 31) x) n)
      (p 9 * Real.cos ((5.0632 : ℝ) * n + p 12)) (p 12) := by
  have hraw := V18Forward.middle_phase_coordinate_derivative n p
  change HasDerivAt
    (fun x => max (V18Forward.middleRaw (Function.update p (12 : Fin 31) x) n)
      (1e-12 : ℝ))
      (p 9 * Real.cos ((5.0632 : ℝ) * n + p 12)) (p 12)
  apply hasDerivAt_max_of_gt _ _ _ _ hraw
  simpa only [Function.update_eq_self] using h

theorem harmonic_derivative :
    HasDerivAt
      (fun x => V18Forward.middle (Function.update p (13 : Fin 31) x) n)
      (Real.sin ((9.4062 : ℝ) * n)) (p 13) := by
  have hraw := V18Forward.middle_harmonic_coordinate_derivative n p
  change HasDerivAt
    (fun x => max (V18Forward.middleRaw (Function.update p (13 : Fin 31) x) n)
      (1e-12 : ℝ))
      (Real.sin ((9.4062 : ℝ) * n)) (p 13)
  apply hasDerivAt_max_of_gt _ _ _ _ hraw
  simpa only [Function.update_eq_self] using h

/-- All five selected derivative identities apply at each of the five
frozen middle observations, without any unclipped assumption. -/
theorem all_frozen_middle_coordinate_derivatives
    (alpha epsilon : ℝ) (i : Fin 5) :
    let p := V18Forward.frozen alpha epsilon
    let n := ((![12,19,53,73,91] : Fin 5 → ℕ) i)
    HasDerivAt
        (fun x => V18Forward.middle (Function.update p (14 : Fin 31) x) n)
        1 (p 14) ∧
    HasDerivAt
        (fun x => V18Forward.middle (Function.update p (15 : Fin 31) x) n)
        ((n : ℝ)^2) (p 15) ∧
    HasDerivAt
        (fun x => V18Forward.middle (Function.update p (9 : Fin 31) x) n)
        (Real.sin ((5.0632 : ℝ)*n + p 12)) (p 9) ∧
    HasDerivAt
        (fun x => V18Forward.middle (Function.update p (12 : Fin 31) x) n)
        (p 9 * Real.cos ((5.0632 : ℝ)*n + p 12)) (p 12) ∧
    HasDerivAt
        (fun x => V18Forward.middle (Function.update p (13 : Fin 31) x) n)
        (Real.sin ((9.4062 : ℝ)*n)) (p 13) := by
  dsimp
  have hn := V18MiddleFloor.every_middle_observable_unclipped alpha epsilon i
  exact ⟨offset_derivative _ _ hn, quad_derivative _ _ hn,
    amplitude_derivative _ _ hn, phase_derivative _ _ hn,
    harmonic_derivative _ _ hn⟩

end ReyesMath.V18MiddleClipped
