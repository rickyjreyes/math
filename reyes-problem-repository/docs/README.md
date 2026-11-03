# Technical documentation
**New, November 2, 2026:** [Negative-result mathematical scope and proof-correspondence audit](../../docs/NEGATIVE_RESULT_SCOPE_AUDIT_2026-11-02.md), covering foundational S004, spectral, curvature-regularity, inverse, and computation-model obstructions. The review preserves the original Lean proofs and canonical GC questions, and records incomplete verification gates.


This page collects the **research administration, audit and provenance material** for the [Reyes Problem Repository](../README.md). It is retained for reproducibility and review but is not necessary for reading the mathematical questions.

## Core research resources

| Resource | Purpose |
|---|---|
| [300-problem index](../ROADMAP_300.md) | Public problem catalogue organized by subject |
| [Verified Lean results](../VERIFIED_LEAN_RESULTS.md) | Finished exact-scope theorems and links to source code |
| [Original 65 statements](../FORMAL_PROBLEMS.md) | Unmodified canonical mathematical statements |
| [Manuscript catalogue](../../CONTENTS.md) | Research manuscripts, PDFs and formal source files |
| [Contributing](../CONTRIBUTING.md) | Short guide for external mathematical contributions |

## Status, evidence and traceability

| Resource | What it records |
|---|---|
| [Research status snapshot](../STATUS.md) | Current GC-level status for all 300 research questions |
| [Problem registry](../problem_registry.json) | Machine-readable source of truth for statuses and question identifiers |
| [65-problem adoption map](../GC65_ADOPTION.md) | Correspondence candidates between GC01–GC65 and earlier proofs |
| [Existing work inventory](../EXISTING_WORK.md) | Provenance and cautions about scope overlap |
| [Machine-readable source links](../existing_work_links.json) | GC01–GC65 link metadata for the validator |
| [Completion records](../completion_records.json) | Accepted full or partial GC issue-resolution evidence |
| [Verification contract](../WORKFLOW.md) | Required theorem, commit, CI and correspondence evidence |

## Program notes and historical research

| Resource | Purpose |
|---|---|
| [Research method](../METHOD.md) | Editorial and mathematical screening criteria |
| [Literature leads](../LITERATURE.md) | Initial references and research context, not proof of novelty |
| [Screening](../SCREENING.md) | Initial flagship evaluation |
| [Foundational shortlist](../FOUNDATIONAL_SHORTLIST.md) | 25 screening priorities, not independently certified open problems |
| [Candidate activation](../CANDIDATE_ACTIVATION.md) | How newer sketch problems become precise theorem targets |
| [Research notebook](../NOTEBOOK.md) | Working notes |
| [WCT morphogenesis](../MORPHOGENESIS_PROGRAM.md) | Cross-cutting mathematical research program |
| [Organization dynamics](../ORGANIZATION_DYNAMICS.md) | Additional emergence and organization models |
| [Original problem folders](../problems/README.md) | Twelve discipline folders with 25 problems each |

## Reproducibility

Validation tools remain in [`scripts/`](../scripts/), and existing GitHub Actions workflows continue to use their original paths. **Administrative files were not relocated or deleted** because their filenames and relative paths are used by validators and historical links. This documentation hub removes them from the *public reading path* without breaking those references.

No green completion label on a Lean source implies that the corresponding GC question, physical hypothesis, or novelty assessment is complete. [Return to the research overview](../README.md).
