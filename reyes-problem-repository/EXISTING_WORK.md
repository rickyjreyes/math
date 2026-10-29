# Adoption inventory: existing results and research issues

**Purpose:** Link existing research to the GC corpus **without copying proof code, moving papers, changing theorem status, or creating duplicate GitHub issues**. Links below indicate *related material only*. They are **not** a completed issue-to-Lean correspondence audit, and none is presented as the full GC problem being solved.

[Workflow](WORKFLOW.md) · [Original dossiers](flagship/) · [300 problems](ROADMAP_300.md) · [Manuscript catalogue](../CONTENTS.md) · [Lean source](../lean/MathProofs)

| GC | Existing issue | Related Lean modules | Existing manuscript source | Adoption assessment |
|:--|:--|:--|:--|:--|
| [GC01](problems/01-wave-dynamics/GC01.md) | [#54](https://github.com/rickyjreyes/math/issues/54), milestone | [OrbitalStability.lean](../lean/MathProofs/OrbitalStability.lean) | [Orbital stability](../papers/orbital-stability-fourth-order-cubic-quintic/main.tex) | Existing minimizer stability is narrower than the requested classification of all standing waves and excited states |
| [GC06](problems/02-confinement-curvature/GC06.md) | [#55](https://github.com/rickyjreyes/math/issues/55), milestone | [WholeSpaceMinimizers.lean](../lean/MathProofs/WholeSpaceMinimizers.lean), [StrictBinding.lean](../lean/MathProofs/StrictBinding.lean) | [Whole-space minimizers](../papers/whole-space-fourth-order-cubic-quintic-minimizers/main.tex), [strict binding](../papers/strict-subadditivity-fourth-order-cubic-quintic/main.tex) | Existing sufficient mass regimes and binding results do not automatically classify the whole parameter space |
| [GC11](problems/03-spectral-scattering/GC11.md) | [#56](https://github.com/rickyjreyes/math/issues/56), milestone | [DispersionMinimum.lean](../lean/MathProofs/DispersionMinimum.lean) | [Positive wave-number minimum](../papers/exact-positive-wavenumber-minimum/main.tex) | Linear spectral-minimum results do not establish nonlinear unique wavelength selection |
| [GC36](problems/08-topology-multicomponent/GC36.md) | [#57](https://github.com/rickyjreyes/math/issues/57), milestone | No matched module established in this audit | No matched manuscript established in this audit | Freeze the dynamical knot model and distinguish static from orbital stability |
| [GC43](problems/09-computability-complexity/GC43.md) | [#58](https://github.com/rickyjreyes/math/issues/58), milestone | No matched module established in this repository audit | No matched manuscript established in this audit | Reversible conservative phase-cell universality is not certified by unrelated TM results |
| [GC08](problems/02-confinement-curvature/GC08.md) | No dedicated GC issue linked yet | [M6BClosureTheorem.lean](../lean/MathProofs/M6BClosureTheorem.lean) | [Curvature closure nonuniqueness](../papers/m6b-nonlinear-curvature-nonuniqueness/main.tex) | Unrestricted uniqueness has a known counterexample; classification under further axioms remains open for review |

Existing Lean modules, publications and other research issues in the repository may be relevant to additional GC problems. **No absence claim is made** for any unmapped problem. The table is a small pilot, not a comprehensive adoption audit of every Lean declaration or paper.

## Adoption procedure

1. Search the [manuscript catalogue](../CONTENTS.md), [Lean project](../lean/MathProofs) and existing GitHub issues before opening a new research task.
2. In the GitHub issue, record the *exact* theorem declaration and frozen assumptions covered by the prior work; identify all missing assumptions and unresolved cases separately.
3. Do not mark a GC complete based on a path match, a similar title, or a passing `lake build` alone.
4. If a complete correspondence is reviewed and approved, add a [completion record](completion_records.json) and update the GC status in a PR. Reuse the existing source and do not modify its manuscript unless a separately justified correction is needed.
5. Keep milestone issues distinct from the parent problem. A milestone may be fully resolved while a parent GC remains a research candidate.

**Existing work is credit, not debt.** The open invitation adds possibilities for collaboration without requiring outside contributions or retrospective rewriting.
