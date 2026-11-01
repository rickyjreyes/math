# Task 2: audit of the fourth-order cubic–quintic confinement theorem chain

Scope: the whole-space problem on `H²(ℝ²; ℂ)` for
`H(u) = ‖(Δ + k²)u‖² − (β/2)‖u‖⁴_{L⁴} + (γ/3)‖u‖⁶_{L⁶}`, `M(u) = ‖u‖²₂`,
`I(m) = inf{H(u) : M(u) = m}`, and the flow `i∂ₜu = (Δ+k²)²u − β|u|²u + γ|u|⁴u`.
This is an **independent model Hamiltonian**. It is not the canonical WCT/S004 action, and no
physical claim follows from it.

## 1. Definitions audited (one functional, one parameter set, throughout)

| Object | Lean | Module |
|---|---|---|
| State space `H²(ℝ²;ℂ)`: closure of Schwartz triples `(φ, ∇φ, Δφ)` in `L²×(L²)²×L²` | `Sobolev.H2 2` | SobolevH2 |
| Mass `M(u) = ‖u‖²₂` (squared norm, not the torus mean) | `Sobolev.H2.M` | SobolevH2 |
| `T(u) = ‖Δu + k²u‖²` (coefficient 1, `k⁴M` retained via `T_eq`) | `StrictBinding.T`, `T_eq` | StrictBinding |
| `H = T − (β/2)Q + (γ/3)S` | `energy`, `StrictBinding.energy_eq` | NegativeEnergy, StrictBinding |
| `I(m) = sInf (H '' {M = m})` | `Imin` | NegativeEnergy |
| Minimizing set `𝒢_m`, `dist_X(v, E) = inf_{g∈E} ‖v − g‖_{H²}` | `OrbitalStability.Gset`, `distX` | OrbitalStability |
| Solutions: `u ∈ C(ℝ; H²)` solving the PDE against every Schwartz test function | `Sobolev.IsSolution` | CubicQuinticFlow |

Every theorem in the chain below is stated for `energy β γ k` and `Imin β γ k` with the same
`(β, γ, k)`. Lean's typing enforces this. There is no silent change of functional, norm or
normalization between steps.

## 2. Principal theorem chain (all kernel-checked, `β, γ > 0`, every `k`)

1. **Coercivity**: `H ≥ T − (3β²/16γ)M`, and `H²` is bounded on sets of bounded mass and energy
   (`OrbitalStability.coercivity`, `bounded_of_mass_energy`).
2. **Negativity**: `−(3β²/16γ)m ≤ I(m) < 0` for all `m > 0`
   (`NegativeEnergy.negative_constrained_energy`).
3. **Dilation-stationary minimizing sequences** and the exact square identity
   (`StrictBinding.exists_stationary_minimizing_seq`, `stationary_square`).
4. **Quantitative energy-per-mass gap** (`StrictBinding.gap`), and from it **strict binding**
   for `0 < m ≤ m_B = 3β/(γ√(k⁴ + 3β²/(32γ)))` (`StrictBinding.strict_binding`).
5. **Compactness modulo translations, and existence** (`WholeSpaceMinimizers`: `compactness`,
   `main`).
6. **Global `H²` well-posedness, continuous dependence and conservation**
   (`CubicQuinticFlow`: `global_wellposed`, `continuous_dependence`, `conservation`;
   `OrbitalStability.global_flow`). The evolution is **proved, not assumed**: Picard–Lindelöf
   with truncation, an a-priori bound from coercivity, and a clopen continuation argument.
7. **Cazenave–Lions orbital stability of the set `𝒢_m`** (`OrbitalStability.stable_core`,
   `orbital_stability`), and the combined **`OrbitalStability.main`**.

## 3. Frozen D4 parameters (`MathProofs/D4FrozenWholeSpace.lean`, new)

`k = 1`, `β = γ = 4608178181141995/2^50`, `m_D4 = 1432536998431173/2^49 ≈ 2.54469689485712`.

| Theorem | Content |
|---|---|
| `d4_mass_lt_mB` | `m_D4 < m_B ≈ 2.5503` (reuses the existing `StrictBinding.frozen_parameters`) |
| `d4_strict_binding` | `I(m_D4) < I(μ) + I(m_D4 − μ)` for every `0 < μ < m_D4` |
| **`d4_frozen_main`** | All of `OrbitalStability.main` at the frozen parameters: finite negative infimum, strict binding, existence, compactness modulo translations, global flow with conservation, orbital stability of `𝒢_{m_D4}` |

## 4. Machine dependency audit (`scripts_audit/DependencyAudit.lean`)

The audit walks every constant used transitively by each root and keeps the `ReyesMath`
declarations, grouped by module. It runs in CI. Result at this commit:

| Root | Constants (transitive) | Project declarations | Axioms |
|---|---|---|---|
| `OrbitalStability.main` | 53,873 | 653 in 10 modules: SobolevH2 101, FreeEvolution 138, H2Algebra 104, CubicQuinticFlow 90, WholeSpaceMinimizers 85, NegativeEnergy 81, StrictBinding 38, OrbitalStability 10, CurvatureNonattainment 5, UVWholeSpace 1 | `propext`, `Classical.choice`, `Quot.sound` |
| `D4Frozen.d4_frozen_main` | 53,886 | the above + D4FrozenWholeSpace 7 + `frozen_parameters` | same |
| `D4Frozen.d4_strict_binding` | 50,905 | 217 in 5 modules | same |

There is no `sorry`, `admit`, local axiom or `native_decide`. Mathlib is pinned at `v4.23.0`.

## 5. Separations that are kept

* **Whole space vs. periodic D4 root.** Everything here is on `ℝ²`. The periodic D4 numerical
  state (torus `L = 42`, wct-pde) is a different problem. No theorem identifies a whole-space
  minimizer with it, and "D4" names only the parameter source. Square symmetry is not imposed.
* **Set vs. profile stability.** Orbital stability is proved for the *set* `𝒢_m`. Uniqueness,
  radial symmetry and positivity of minimizers are **not** proved.

## 6. Remaining obligations (open)

1. **Quantitative split deficit.** `I(μ) + I(m−μ) − I(m) > min(μ, m−μ)/400000`
   (`geometry_of_resonance/docs/d4_frozen_review/PROOF.md`, eq. (1)) is **not** in Lean. Its
   current certificate is exact rational arithmetic in Python. The precise missing Lean
   ingredient is an explicit lower bound for `−I(s)`, i.e. an explicit negative trial energy
   such as the anisotropic Gaussian of PROOF.md §2. `NegativeEnergy.exists_negative` is only
   existential. With such a bound, `StrictBinding.gap` would give the deficit by scalar
   interval arithmetic.
2. A consolidated manuscript that matches this inventory line by line has not been produced
   in this change.
3. Independent reproducible build: CI (`.github/workflows/lean.yml`) runs `lake build` plus
   this audit.
