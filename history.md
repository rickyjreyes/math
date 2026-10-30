# Version history

## 2026-10-30 — Foundational WCT research framing

- Clarified the purpose of mathematical formalization and adversarial testing as advancing the continuing foundational WCT program, without a compulsory engineering-only pivot.
- Added an interpretation policy for affirmative results, scoped no-go statements, constructive next tests and physical-bridge obligations.
- Applied that policy across the entry-point documentation, overview and GC research workflow and templates, without changing mathematical proofs or statuses. Tracking issue [#70](https://github.com/rickyjreyes/math/issues/70).


## 2026-10-30 — Lean certification of seven analytic manuscripts and families F11, F12

- Certified E62, E58, M2/E17, E26, M3/E57, E61 and E16, together with the F11 companions E13/E14 and E59. Every theorem, proposition, corollary and lemma is an exported Lean declaration about the manuscript's actual objects, and so is every remark that makes a mathematical assertion. The objects are the unitary Fourier transform on `L²(ℝ^d)`, `H^{2k}` by Fourier weights, `H²(Ω)` by weak derivatives, unbounded operators with their natural domains, and the torus Fourier basis.
- Added a shared Swift–Hohenberg layer: `(Δ + k⋆²)²` is self-adjoint on `H⁴`, `σ(r − a(Δ + k⋆²)²) = (−∞, r]`, and the semigroup has exactly this generator with `‖e^{tL_r}‖ = e^{rt}`. The E61 and M3/E57 certifications are built on it.
- Ported the E13/E14 band-pass module. Restored the main build after the [PR #60](https://github.com/rickyjreyes/math/pull/60) merge by fixing E61ExactNorm and E17GlobalBound.
- No manuscript statement was false, so no manuscript text changed. Beyond the manuscripts, the E26 constant `1/δ` is proved sharp.
- `AnalyticCertificationAudit.lean` audits all 135 declarations cited in the certification report. Each uses only `propext`, `Classical.choice` and `Quot.sound`. The focused workflow now runs this audit.
- `lean/formalization.yaml` now marks F11 and F12 complete and records the E58, E61, M3/E57 and M2/E17 manuscripts. The inventory is 136 modules and 2,522 theorem/lemma declarations. Correspondence tables are in `docs/ANALYTIC_CERTIFICATION_2026-10-30.md`.

## 2026-10-27 — Review and correct the full v18 parameter map

- Restored middle-frequency coordinates 10 and 11 in the 31-parameter real forward map, proved their coordinate derivatives, and defined the actual Fréchet Jacobian with its structural nullity and directional-derivative theorems.
- Proved strict floor inactivity at all five frozen middle observations and derivatives of the clipped outputs in all seven middle coordinates. Removed an accidentally inherited auxiliary hypothesis from the frozen-output aggregate theorem.
- Widened the external interval certificate to enclose nominal decimals and exact stored binary64 inputs, and verified the inner heavy light-floor branch. The nonzero-minor conclusion survives; it remains outside Lean.
- Recorded 64 imported project modules, 1,515 theorem/lemma declarations, and 13/14 complete original manuscripts. F09 remains incomplete, including its full derivative identification, middle determinant proof and conditional nonlinear level-set proposition.

## 2026-10-27 — Frozen v18 analytic Jacobian formalization (partial)

- Imported kernel-checked light and heavy 3×3 blocks; generic 3+5+3 block determinant identity; derived the five selected middle-sector source partial derivatives and recorded their exact 5×5 matrix.
- The interval-certified trigonometric middle determinant and full clipped 31-parameter source-model derivative remain to be proved inside Lean. F09 completion flag remains false.


## 2026-10-27 — Lean formalization of the isolated Fourier shell (F10)

- Formalized the isolated-Fourier-shell manuscript (F10) on all of `L²(ℝ^d)`: Plancherel's theorem (the unitary extension of the Schwartz-space Fourier transform, identified with the Fourier integral on `L¹ ∩ L²`, in the manuscript's normalization), the shell theorem for essential and for distributional support, the Helmholtz corollary for distributional solutions, the polynomial-dispersion corollary, the general-multiplier remark, and the wave-packet proposition.

## 2026-10-27 — Lean formalization of orbital stability (F01)

- Formalized the orbital-stability manuscript (F01) end to end on `H²(ℝ²)`: the free group `e^{-it(Δ+k²)²}` on Schwartz space, `L²` and `H²`; the `H²(ℝ²)` algebra and the cubic–quintic nonlinearity; global well-posedness with continuous dependence on the data and conservation of mass and energy (an interaction-picture Picard–Lindelöf construction with a radial truncation); and Lyapunov stability of the full minimizing set for `0 < m ≤ m_B`, including perturbations that change the mass.
- `lean/formalization.yaml` now marks the orbital-stability manuscript, and with it the F01 family, as formalized.

## 2026-10-27 — Integrate whole-space Lean proofs and analytic v18 rank certification

- Combined later whole-space H² minimizer compactness, curvature nonattainment and torus Fourier-leakage well-posedness proofs with all main-line supporting Lean modules and the mathematical compendium.
- Added a source-pinned interval-arithmetic certificate of exact rank 11 and nullity 20 for the frozen 31→11 v18 Jacobian, distinct from Lean kernel formalization.
- Preserved earlier curvature-weight positivity/abstract nonattainment lemmas as CurvatureLegacy for compatibility.
- Added intrinsic scalar-metric, L² Plancherel-conditional shell, quartic near-minimizer nonvanishing and conditional orbital-stability Lean modules.
- Global PDE H² well-posedness/stability, smooth cotangent tensor construction, canonical L² Fourier realization and Lean model-specific rank certificate remain open.


## 2026-10-26 — Mathematical compendium, Volume I

- Added a separate `compendium/` reference series beginning with the 25-ID elementary mathematical foundations, with LaTeX source, per-volume notes, canonical-registry cross-references, and a reproducible PDF build.
- Classified standard mathematical identities, conditional counting hypotheses, and physical interpretation distinctly; the compendium is not an F-series original research preprint or a completed Lean formalization.
- Indexed the compendium in README and CONTENTS and extended the PDF publishing workflow to build the PDF beside its source.

## 2026-10-26 — E68 localized gradient-energy proof

- Added complete Manuscript 4 E68 source: refutes unrestricted $H^1$ local-energy bound for $n\ne2$ over all radii, and proves a corrected $L^n$-gradient estimate with an $H^2$ result for $n=3,4$.
- Analytic results only, not Lean-formalized; no claim of physical confinement or nonlinear-PDE stability.

## 2026-10-26 — M6B exact nonuniqueness counterexamples

- Added a standalone manuscript proving the structural nonuniqueness of the regularized nonlinear curvature closure and noninjectivity of the canonical stationary curvature map modulo global phase, at fixed Dirichlet data and mass.
- The result does not establish nonuniqueness for the M7 initial-value problem; the manuscript is not Lean-formalized.
- Integrated source, preprint notes, catalogue, and overview.

## 2026-10-26 — E26 regularized-curvature L2 estimate

- Added the complete E26 proof and counterexample as a standalone LaTeX manuscript (F12).
- Stated the essential denominator-separation hypothesis for the historical additive denominator and distinguished it from the corrected modulus-squared M2/E17 regularization.
- Registered the result in the catalogue, overview and Lean coverage manifest as analytic and not Lean-formalized.


## 2026-10-26 — E61 continuum spectral threshold

- Added the complete linear Swift--Hohenberg continuum threshold proof (E61), covering spectrum, semigroup stability, unstable annulus, periodic-domain correction and centered versus uncentered parameters.
- Indexed the LaTeX source and PDF workflow in the catalogue, README and overview.
- The result is analytic and not claimed as Lean-formalized or as a nonlinear pattern existence theorem.

## 2026-10-26 — E13/E14 band-pass gradient flow

- Added the full periodic Swift--Hohenberg band-pass gradient-flow proof (family F11), including the exact Wirtinger/real-$L^2$ normalization, fourth-order integration by parts, energy dissipation, and Fourier-shell preference.
- Updated catalogue, overview, build count and PDF workflow for 15 manuscripts in 11 families.
- Classified the result as analytic and not Lean-formalized; no physical parent-theory derivation is claimed.

## 2026-10-26 — Structured manuscript collection

- Catalogued all 14 preexisting LaTeX manuscripts into 10 families.
- Added a navigable manuscript map and overview PDF source.
- Added an automated pipeline for committing reproducible PDF builds to main and uploading run artifacts.
- Added a Lean 4 + Mathlib project containing explicitly scoped *supporting* algebraic proofs and a family-level coverage manifest.
- Preserved the original mathematical manuscript content; no PDE theorem has been relabeled as fully Lean-formalized.

Future errata and withdrawals will link previous Git revisions instead of silently rewriting the historical record.

## 2026-10-26 — E62 spectral concentration proof

- Added Manuscript 1 E62 as family F11, with discrete and continuous-spectrum bounds and equality conditions.
- Distinguished the kinematic normalized-energy claim from unproved time-monotone band selection.
- Updated the reproducible PDF catalogue and build counts from 14 to 15, without asserting that this new manuscript is Lean-formalized in this repository.
