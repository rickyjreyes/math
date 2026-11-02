# Contributing mathematical work

**Proofs, counterexamples, corrections and serious mathematical criticism are welcome.** Contributors are not required to accept Wave Confinement Theory, and a negative result is valuable when its assumptions and consequences are stated precisely. Original contributions retain attribution.

**[Overview](README.md) · [300 problems](ROADMAP_300.md) · [Verified results](VERIFIED_LEAN_RESULTS.md) · [Research papers](../CONTENTS.md)**

## Choose a mathematical question

Find a GC identifier in the [subject-organized index](ROADMAP_300.md) and read its individual problem page. The original GC01–GC65 entries have preserved mathematical statements. GC66–GC300 are exploratory questions: **first define a precise mathematical problem** before claiming to have solved one.

Before starting, look for a matching [GitHub issue](https://github.com/rickyjreyes/math/issues), existing [Lean source](../lean/MathProofs), and established prior literature. A relevant theorem may already exist. Cite it instead of duplicating it.

## Submit a result

A mathematical submission should state, as applicable:

1. **Exact claim:** equation or operator, domain, hypotheses, function spaces, parameter range, and all quantifiers.
2. **Proof or counterexample:** a readable mathematical derivation, exact construction, or Lean 4 declaration, including its dependencies.
3. **Comparison:** the closest existing work and an explicit explanation of what your argument adds, recovers, corrects, or refutes.
4. **Scope:** which part of the GC question is answered and which parts remain unsettled.
5. **Reproducibility:** code, tested Lean commit and CI result when formal verification is claimed, plus any optional manuscript.

Use an existing issue if it covers your contribution, and submit a pull request to the appropriate source. Otherwise use the [research contribution issue form](https://github.com/rickyjreyes/math/issues/new?template=grand_challenge.yml) or, for a newly scoped research problem, the [GC issue form](https://github.com/rickyjreyes/math/issues/new?template=gc_problem.yml). Check for duplicates first.

## What counts as complete?

**✅ Complete Lean theorem:** the exact formal statement has a checked proof and its hypotheses are visible. This is distinct from a proof about physical reality and from establishing worldwide novelty.

**GC question resolved:** only when every frozen acceptance criterion for that entire question is met, the relevant Lean evidence and paper statements match the claim, and the reviewed resolution is entered in the registry. A theorem for one parameter regime is an important result, but not necessarily an answer for all regimes. A verified no-go result applies only to the models it actually excludes.

Lean is required for newly claimed **formally verified** GC resolution records, but conventional analytical work, prior-art discoveries and partial results can be discussed and developed independently. Manuscripts are optional. Use **“Refs #N”** or **“Part of #N”** for partial progress, not **“Closes #N”** unless the precise issue requirements are met.

## Further details

The full [verification workflow](WORKFLOW.md) specifies issue scope, exact theorem declaration names, reviewer correspondence, successful CI runs, PR format and closure policy. [Technical documentation](docs/README.md) links the machine-readable adoption records, archived notes, validation scripts and editorial materials.

Independent formal mathematics, numerical calculations and experimental WCT claims remain different types of evidence. Make their boundaries explicit. Corrections and counterexamples should be recorded, not hidden. No prizes or guaranteed publication are offered.
