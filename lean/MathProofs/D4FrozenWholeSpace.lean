import Mathlib
import MathProofs.OrbitalStability

/-!
# Frozen D4 parameters inside the kernel-checked whole-space chain (Task 2)

The frozen D4 problem (`geometry_of_resonance/docs/d4_frozen_review/PROOF.md`, eq. (2)) uses
`H(u) = ‖(Δ+k²)u‖² − (β/2)‖u‖⁴_{L⁴} + (γ/3)‖u‖⁶_{L⁶}` on `H²(ℝ²; ℂ)` with the exact dyadics

* `k = 1`,
* `β = γ = 4608178181141995 / 2^50` (`0x1.05f1d178c75ebp+2`),
* `m_D4 = 1432536998431173 / 2^49` (`0x1.45b8a0bad2714p+1` ≈ 2.54469689485712).

This is the same functional as `ReyesMath.Sobolev.energy` (see `StrictBinding.energy_eq`), with
mass `M(u) = ‖u‖₂²` and `I(m) = Imin β γ k m`.

* `d4_mass_lt_mB`: `m_D4 < m_B = 3β/(γ√(k⁴ + 3β²/(32γ))) ≈ 2.5503`. This reuses the existing
  `StrictBinding.frozen_parameters`, which already proved this inequality and strict binding
  at these exact dyadics.
* `d4_frozen_main` (**new**): `OrbitalStability.main` at the frozen parameters. This gives finite negative
  infimum, strict binding `I(m) < I(μ) + I(m−μ)` for **every** `0 < μ < m_D4`, existence of
  minimizers, compactness of minimizing sequences modulo translations, global `H²`
  well-posedness with conservation, and orbital stability of the minimizing *set*.
* `d4_strict_binding`: the strict-binding clause on its own.

**Scope and separation.**
* This is the *whole-space* problem. Nothing here identifies a whole-space minimizer with the
  periodic D4 numerical root or any finite-grid state. "D4" names the source parameters only. No
  square symmetry is imposed.
* Not proved here: the **quantitative** split deficit
  `I(μ) + I(m−μ) − I(m) > min(μ, m−μ)/400000` of PROOF.md (1). From `StrictBinding.gap` it would
  follow once an explicit lower bound for `−I(s)` (an explicit negative trial energy) is
  formalized. `NegativeEnergy.exists_negative` is only existential, so that lemma is the precise
  remaining obligation.
* Physical relevance to WCT is not asserted.
-/

namespace ReyesMath

namespace D4Frozen

open Sobolev Sobolev.H2

/-- Frozen nonlinear coefficient `β = γ`. -/
noncomputable def coeff : ℝ := 4608178181141995 / 1125899906842624

/-- Frozen mass `m_D4`. -/
noncomputable def mass : ℝ := 1432536998431173 / 562949953421312

theorem coeff_pos : 0 < coeff := by unfold coeff; norm_num

theorem mass_pos : 0 < mass := by unfold mass; norm_num

/-- The frozen mass lies in the kernel-checked strict-binding range. Reused from the existing
`StrictBinding.frozen_parameters` (which proves the strict inequality `m₀ < m_B`). -/
theorem d4_mass_lt_mB : mass < StrictBinding.mB coeff coeff 1 := by
  have h := StrictBinding.frozen_parameters.1
  simpa only [mass, coeff] using h

theorem d4_mass_le_mB : mass ≤ StrictBinding.mB coeff coeff 1 := d4_mass_lt_mB.le

/-- **Frozen D4 whole-space theorem**: `OrbitalStability.main` at the exact frozen parameters. -/
theorem d4_frozen_main :
    ((-(3 * coeff ^ 2 / (16 * coeff)) * mass ≤ Imin coeff coeff 1 mass ∧
        Imin coeff coeff 1 mass < 0) ∧
      ∀ a, 0 < a → a < mass →
        Imin coeff coeff 1 mass < Imin coeff coeff 1 a + Imin coeff coeff 1 (mass - a)) ∧
    ((OrbitalStability.Gset coeff coeff 1 mass).Nonempty ∧
      ∀ u : ℕ → H2 2, (∀ n, M (u n) = mass) →
        Filter.Tendsto (fun n => energy coeff coeff 1 (u n)) Filter.atTop
          (nhds (Imin coeff coeff 1 mass)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : ℕ → EuclideanSpace ℝ (Fin 2),
          ∃ U ∈ OrbitalStability.Gset coeff coeff 1 mass,
            Filter.Tendsto (fun n => distH2 (translate (y n) (u (φ n))) U) Filter.atTop
              (nhds 0)) ∧
    ((∀ u₀ : H2 2, ∃! u : ℝ → H2 2, IsSolution coeff coeff 1 u ∧ u 0 = u₀) ∧
      ∀ u : ℝ → H2 2, IsSolution coeff coeff 1 u → ∀ t,
        M (u t) = M (u 0) ∧ energy coeff coeff 1 (u t) = energy coeff coeff 1 (u 0)) ∧
    ∀ ε > 0, ∃ δ > 0, ∀ u : ℝ → H2 2, IsSolution coeff coeff 1 u →
      OrbitalStability.distX (u 0) (OrbitalStability.Gset coeff coeff 1 mass) < δ →
      BddAbove (Set.range fun t =>
        OrbitalStability.distX (u t) (OrbitalStability.Gset coeff coeff 1 mass)) ∧
      ⨆ t, OrbitalStability.distX (u t) (OrbitalStability.Gset coeff coeff 1 mass) < ε :=
  OrbitalStability.main coeff_pos coeff_pos mass_pos d4_mass_le_mB

/-- Strict binding at the frozen D4 mass, for every split (same as
`StrictBinding.frozen_parameters.2`, restated with named constants). -/
theorem d4_strict_binding {μ : ℝ} (hμ : 0 < μ) (hμm : μ < mass) :
    Imin coeff coeff 1 mass < Imin coeff coeff 1 μ + Imin coeff coeff 1 (mass - μ) :=
  StrictBinding.strict_binding coeff_pos coeff_pos mass_pos d4_mass_le_mB hμ hμm

end D4Frozen

end ReyesMath
