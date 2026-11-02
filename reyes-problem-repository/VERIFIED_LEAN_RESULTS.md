# ✅ COMPLETE: Verified Lean results

**20 ranked mathematical result modules with located source files.** A green **✅ COMPLETE** marks an existing *exact-scope Lean result*, **not** completion of every broader Reyes GC problem, proof of physical WCT, or independent worldwide novelty certification.

> **Status convention:** ✅ **COMPLETE (Lean theorem)** = the stated result has an existing formal proof module and is reported complete within its defined hypotheses. 🟡 **PARTIAL (GC question)** = the broader problem requires more work. ⚪ **CANDIDATE (GC question)** = not formally accepted as resolved. The [GC machine registry](problem_registry.json) controls GC status, not this table.

**Source inspection (2026-11-02):** all 20 linked source modules were located directly in their repositories. Existing project proof/audit documentation supplies their formalization status. **No new cross-repository Lean build or independent mathematical novelty review was performed for this catalogue update.**

## Completed exact-scope results

| Rank | Result | Formalization | Precisely what is complete | GC association, not GC completion |
|---:|---|---|---|---|
| 1 | [OrbitalStability.lean](../lean/MathProofs/OrbitalStability.lean) | ✅ **COMPLETE** | Full-set orbital stability for 2D fourth-order cubic–quintic minimizers in the specified mass range. | GC01 (partial) |
| 2 | [StrictBinding.lean](../lean/MathProofs/StrictBinding.lean) | ✅ **COMPLETE** | Strict mass subadditivity on the explicit sufficient mass range, including frozen parameters. | GC06, GC16 (partial) |
| 3 | [CubicQuinticFlow.lean](../lean/MathProofs/CubicQuinticFlow.lean) | ✅ **COMPLETE** | Global H² well-posedness, conservation, and continuous dependence on ℝ². | GC03 (partial), GC46 (possible full match) |
| 4 | [CurvatureNonattainment.lean](../lean/MathProofs/CurvatureNonattainment.lean) | ✅ **COMPLETE** | Whole-space nonattainment and strict spreading for the specified positive curvature energy. | GC07 (related, not a full answer) |
| 5 | [E68Classification.lean](../lean/MathProofs/E68Classification.lean) | ✅ **COMPLETE** | The specified H¹ localized-gradient estimate holds precisely in dimension 2. | GC10 (related estimate, not general confinement classification) |
| 6 | [V18Identifiability.lean](../lean/MathProofs/V18Identifiability.lean) | ✅ **COMPLETE** | 20-dimensional local equal-observation fiber in the specified 31-parameter clipped map. | GC26 (partial) |
| 7 | [L2Fourier.lean](../lean/MathProofs/L2Fourier.lean) | ✅ **COMPLETE** | Unitary L² Fourier construction and exact-shell exclusion. | GC14 (related, not full) |
| 8 | [R16_AuxiliaryEquivalence.lean](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/lean/ReleaseProofs/R16_AuxiliaryEquivalence.lean) | ✅ **COMPLETE** | Auxiliary reformulation preserves the Hamiltonian obstruction for the specified temporal-jet representative. | GC21/GC24 (related restricted obstruction) |
| 9 | [E57L2Semigroup.lean](../lean/MathProofs/E57L2Semigroup.lean) | ✅ **COMPLETE** | Exact bounded-operator Fourier semigroup law and contraction on L². | GC48 (related, scope review required) |
| 10 | [M6BClosureTheorem.lean](../lean/MathProofs/M6BClosureTheorem.lean) | ✅ **COMPLETE** | Infinitely many admissible smooth regularized constitutive closures. | GC08 (partial negative resolution) |
| 11 | [Randomization.lean](https://github.com/rickyjreyes/photodiode/blob/main/formal/PhotodiodeProtocol/Randomization.lean) | ✅ **COMPLETE** | Exact type-I error control under the stated randomization or exchangeability hypotheses. | No exact GC match |
| 12 | [BlockEnclosure.lean](https://github.com/rickyjreyes/wct-pde/blob/main/formal/D4Certificates/BlockEnclosure.lean) | ✅ **COMPLETE** | Conditional operator-norm enclosure and sound finite-certificate checker. | GC50 (related; no production operator certificate implied) |
| 13 | [SplitSATCapacity.lean](https://github.com/rickyjreyes/PVNP/blob/main/lean/PVNP/SplitSATCapacity.lean) | ✅ **COMPLETE** | Exact split-SAT construction and finite-alphabet communication capacity bound. | No exact GC match |
| 14 | [R18_Onset.lean](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/lean/ReleaseProofs/R18_Onset.lean) | ✅ **COMPLETE** | No primary finite-q static onset in the specified homogeneous S004 sector. | GC23 (related obstruction) |
| 15 | [R18_CanonicalObstruction.lean](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/lean/ReleaseProofs/R18_CanonicalObstruction.lean) | ✅ **COMPLETE** | Static spatial-selection obstruction and scoped pole positivity. | GC23 (related obstruction) |
| 16 | [V18Rank.lean](../lean/MathProofs/V18Rank.lean) | ✅ **COMPLETE** | Exact rank 11 and nullity 20 for the defined observation derivative. | GC26 (partial) |
| 17 | [Communication.lean](https://github.com/rickyjreyes/PVNP/blob/main/lean/PVNP/Communication.lean) | ✅ **COMPLETE** | Exponential transcript-count lower bound for the stated deterministic communication model. | No exact GC match |
| 18 | [MultiBlock.lean](https://github.com/rickyjreyes/Wavelock/blob/main/lean/WaveLockProofs/MultiBlock.lean) | ✅ **COMPLETE** | Specified multiblock absorption properties and structural collision limitations. | No exact GC match |
| 19 | [M6BClosureFieldWitness.lean](../lean/MathProofs/M6BClosureFieldWitness.lean) | ✅ **COMPLETE** | Distinguishes admissible curvature closures on a smooth continuum field. | GC08 (supports partial negative resolution) |
| 20 | [R16_CompletionClasses.lean](https://github.com/rickyjreyes/geometry_of_resonance/blob/main/lean/ReleaseProofs/R16_CompletionClasses.lean) | ✅ **COMPLETE** | Delimited higher-derivative failure class and separate competing spatial action. | GC21/GC24 (related, not full classification) |

## Most relevant GC questions

| GC problem | Completed mathematical evidence | GC status | Remaining boundary |
|---|---|---|---|
| [GC01](problems/01-wave-dynamics/GC01.md) | ✅ **COMPLETE** full-set minimizer orbital-stability theorem | ⚪ Candidate | Classify all standing waves, including excited states |
| [GC03](problems/01-wave-dynamics/GC03.md) | ✅ **COMPLETE** global H² evolution for the stated ℝ² equation | ⚪ Candidate | Classify the larger PDE parameter family and blow-up cases |
| [GC06](problems/02-confinement-curvature/GC06.md) | ✅ **COMPLETE** minimizer existence and strict binding on sufficient mass range | ⚪ Candidate | Determine all parameter and mass regimes |
| [GC08](problems/02-confinement-curvature/GC08.md) | ✅ **COMPLETE** closure nonuniqueness theorem and smooth-field witness | 🟡 Partially resolved | Classify closure laws under additional axioms and audit exact GC correspondence |
| [GC16](problems/04-variational-solitons/GC16.md) | ✅ **COMPLETE** strict binding for an explicit sufficient range | ⚪ Candidate | Determine all masses |
| [GC26](problems/06-inverse-observation-control/GC26.md) | ✅ **COMPLETE** exact rank 11, nullity 20, and nonlinear local non-identifiability | ⚪ Candidate | Global injectivity and all-parameter classification |
| [GC46](problems/10-lean-certified-analysis/GC46.md) | ✅ **COMPLETE** global existence, uniqueness, continuous dependence and conservation theorem | ⚪ Candidate, possible full match | Exact GC-to-Lean acceptance and CI correspondence review not yet recorded |

**Important:** The same Lean theorem can support several GC questions; these are **20 theorem modules, not 20 different solved GC questions**. Result completeness, GC problem completeness, and mathematical originality are three different statuses.

## Current GC registry, unchanged

- **300** candidate research entries in the catalogue.
- **299** marked `candidate` and **1** marked `partially_resolved` (GC08).
- **0** marked `resolved` and **0** accepted formal [completion records](completion_records.json).

Use the [adoption index](GC65_ADOPTION.md) for the initial 65 problem-to-source links, and the [verification contract](WORKFLOW.md) before changing an entire GC status. A completed theorem should remain visibly green even if its encompassing GC challenge stays open.
