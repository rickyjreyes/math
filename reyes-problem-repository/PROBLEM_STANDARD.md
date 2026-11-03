# Reyes problem standard: six-part mathematical review

**Version:** 2.0, November 2, 2026. Applies to all 300 GC entries. [Full roadmap](ROADMAP_300.md) · [Case-by-case review queue](formal-reviews/REVIEW_QUEUE.md) · [Research methodology](METHOD.md) · [Evidence/status registry](STATUS.md).

This standard distinguishes a **formal mathematical question**, an **existing theorem**, an **analytically answered frozen benchmark**, and a **newly solved Lean-checked research obligation**. These are not interchangeable. Publication of a formatted review page alone establishes none of them.

## The six required sections

1. **Canonical mathematical statement and model freeze.** Write the exact equation, energy, operator, boundary/initial conditions, domain, function spaces, topologies, coefficient ranges and symmetries. Use one named benchmark, not an unquantified model family. Include the complete logical quantifiers and a nonvacuity check. If a proposed class may be empty, say so. Preserve the original question separately, and label changes as revisions rather than replacing its history.
2. **Closest known results and novelty filter.** For each relevant source, identify the paper/theorem, actual equation, dimension, regularity, assumptions, conclusion, and precise overlap/difference. A subject-level citation is **only a literature lead**, not independent clearance. Check established mathematical theorems, prior repository formalizations, trivial subcases, constants, scaling, and explicit counterexamples. Include date and search scope when claiming a formal novelty audit.
3. **Precise quantified problem.** Write a single decision/classification target: “Determine whether [claim with quantifiers]; if yes prove sufficient and, where requested, necessary conditions, if no give an admissible counterexample or obstruction.” Do not conflate existence with conditional stability or a linear coefficient with nonlinear dynamics.
4. **Resolution criterion.** Specify what proves/refutes the **whole frozen statement**. A verified result in a smaller coefficient/mass/domain class is a partial result. An analytic calculation is recorded as such until independent checking. Lean verification adds a kernel-checked declaration/axiom audit and a theorem-to-statement correspondence review, not automatic scientific novelty.
5. **Two to four falsifiable first milestones.** Each milestone must be strictly narrower, with an exact input, measurable conclusion and failure case. Reusing a subject-level checklist without specializing the actual mathematical object does not satisfy this requirement.
6. **Status recommendation.** Choose **Candidate (formal)**, **Refined draft**, **Withdraw/merge as established**, or **Analytically answered within frozen scope**. State why. Recommendations **do not change** the official machine registry without approval and the [completion workflow](WORKFLOW.md).

## Minimum quality gate

| Gate | Pass only if |
|:--|:--|
| Model | Equation/operator and all domains, coefficients and spaces are explicit |
| Nonvacuity | Required objects exist or a conditional/negative formulation is honest |
| Mathematics | The exact quantified conclusion and its counterexample are well-defined |
| Prior art | Actual matching theorems and their hypothesis differences are documented |
| Evidence | Analytical derivations, Lean declarations, simulations and hardware claims are separated |
| Milestones | At least two concrete, falsifiable subclaims, not generic study recommendations |
| Review | Status recommendation is justified and the original text is preserved |

**P0:** resolve conceptual category mismatch, possible known answer or critical unquantified hypothesis before any novelty claim. **P1\*:** perform the individual high-priority scoping action in the October 30 audit. **P1:** perform model-specific freeze and source comparison. Every remaining missing gate is explicitly recorded; a template with six headings is not a clearance certificate.

## Current scope of the upgrade

All **300 existing structured research reviews** remain linked from the roadmap. **23 individual reviews** now have specialist case-specific v2 analysis, including **all 15 P0 items**, GC250 and selected high-priority PDE, spectral and variational cases. The other **213 GC65–GC300 scoped entries** retain their original mathematical targets, first tests and explicit scoping objections, but **not** a certified individual full-text literature review. GC01–GC64 preserve the original formal statements and associated structured reviews.

The review queue distinguishes what received a genuine case-specific revision from what still needs individual specialist work.

### Findings requiring careful separation

- **GC82, GC103, GC105:** have proposed direct analytic proofs/explicit evaluations for their frozen benchmark statements. They are recorded as **provisional analytical results**, pending independent checking and any relevant Lean correspondence, not upgraded registry completions.
- **GC200, GC212, GC247, GC248, GC250, GC252:** their core statements are classical or elementary, although formalizing them in Lean can be a legitimate research-engineering goal.
- **GC278, GC286:** finite-model algebra and an energy-accounting inequality are not physical hardware demonstrations.
- **GC66:** the corrected isolated-mode gap is frequency-dependent, and its required nonzero standing wave must actually be constructed.

Do **not** equate the low-confidence 1–10 **difficulty** ratings with acceptance of novelty, correctness, physical relevance, or proof completion.

## Source precedence

The historical [GC statements](FORMAL_PROBLEMS.md), [scoped GC65–GC300 models](scoped/README.md), underlying exact mathematics, and [machine registry](problem_registry.json) retain their authority. The new [formal-review pages](formal-reviews/README.md) are a reviewed *proposed interpretation* and an evidence audit trail. Any conflicting model equation must be reconciled explicitly before activating a formal theorem or changing status.
