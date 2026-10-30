# Contributing to The Reyes Problem Repository

This is an **open invitation**, not a requirement for the research to progress. The continuing foundational WCT program welcomes independent proof, criticism and constructive model development; contributors do not have to endorse its physical hypotheses. The existing researcher continues working; outside mathematicians, physicists, computer scientists and AI-assisted collaborators can contribute when they have substantive results. Contributors receive attribution for their original work. **Proving a conjecture false is as welcome as proving it true, with the precise scope of that falsification recorded.** [Research direction](../RESEARCH_DIRECTION.md).

[300 problems](ROADMAP_300.md) · [Issue, PR, Lean and paper workflow](WORKFLOW.md) · [Existing work](EXISTING_WORK.md) · [Editorial standards](METHOD.md) · [Research status](STATUS.md)

## Before starting a problem

1. Choose a GC ID from [the roadmap](ROADMAP_300.md) and inspect its [problem folder](problems/README.md). GC01–GC65 have existing mathematical statements; GC66–GC300 are preliminary prompts that require [scope-first activation](CANDIDATE_ACTIVATION.md) before declaring a theorem.
2. Search GitHub **issues and PRs** for the GC ID and for related mathematical formalization issues. In particular, GC01, GC06, GC11, GC36 and GC43 already have research tasks. **Do not open a duplicate.**
3. Check existing Lean modules and manuscripts using the [complete 65-problem adoption index](GC65_ADOPTION.md), [adoption inventory](EXISTING_WORK.md), [Lean source](../lean/MathProofs) and [manuscript catalogue](../CONTENTS.md). An existing theorem can be cited and adopted by reference. Do not reprove it just to satisfy an issue.
4. Check the closest established mathematical literature and natural counterexamples. Preserve a record of what has or has not been reviewed.

## Contribute like a software engineer

**A GitHub issue is the research task.** Its scope should say whether it represents an entire GC classification, one frozen milestone, or preliminary scope/literature work. The issue must give the exact model, function spaces, parameter domains, quantifiers, acceptance criteria, and previous results or identify these as outstanding scoping work.

**A pull request is the contribution.** Reuse an open issue, and cite each theorem or counterexample the PR addresses. Use `Refs #N` or `Part of #N` for partial progress. Use `Closes #N` only when the precise *issue*, not merely a related lemma, is fully answered.

**Lean 4 is required for a claim of formal GC completion.** Cite the exact source file and fully qualified declaration; the repository's existing `lean/` build must pass and a mathematical reviewer must confirm the Lean statement meets the issue's acceptance criteria. Lean proves the encoded proposition; it cannot check that an issue's prose, manuscript and physical claims are all equivalent.

**Papers are optional.** New papers can use the existing `papers/` and `preprints/` conventions. If a paper claims formal verification, link the exact Lean declaration and commit and reconcile hypotheses, conclusion, and theorem scope. Label any unformalized mathematical argument, numerical evidence, or physical interpretation separately. Do not change an existing manuscript just to make the GC catalogue appear complete.

**Partial results count.** A special-case theorem, formal lemma, counterexample, established-prior-art finding, or reproducible falsification may be merged while the parent problem remains open. A scoped milestone issue can close without closing the entire GC question.

## Issue and PR templates

- [Existing contribution issue form](https://github.com/rickyjreyes/math/issues/new?template=grand_challenge.yml): report a finding, correction, theorem, or counterexample when no existing task covers it.
- [Scoped GC problem issue form](https://github.com/rickyjreyes/math/issues/new?template=gc_problem.yml): open an issue only after checking existing GC and Lean issues and recording the acceptance criteria.
- [PR template](../.github/PULL_REQUEST_TEMPLATE.md): provide exact claim, issue references, prior work, Lean proof/CI evidence, correspondence review, optional paper, and remaining limitations.
- [Safe local draft issue renderer](scripts/render_gc_issue.py): run `python3 reyes-problem-repository/scripts/render_gc_issue.py GC52` at the repository root; it does **not** open a GitHub issue. It declines a known existing issue to prevent duplicates.

## Evidence, review and closure

1. Freeze the exact issue statement, acceptance criteria and scope before declaring a full solution.
2. Submit a proof or counterexample in Lean, or **adopt** an existing theorem by reference, with an exact declaration and successful CI run.
3. Explicitly compare the formal statement to every item in the issue. Include prior-art comparisons and known counterexamples.
4. If there is a paper, identify which claims correspond exactly to Lean and which claims are outside the formal verification.
5. After review, update the issue and, where appropriate, the [problem registry](problem_registry.json), [STATUS.md](STATUS.md), and [completion evidence index](completion_records.json). Do not add a resolution record without proof and correspondence evidence.
6. Close **only the matched issue scope**. Preserve unresolved parent questions and historic revisions.

The [workflow contract](WORKFLOW.md) defines the final evidence fields. The structural [record checker](scripts/validate_completion_records.py) validates links and metadata, **not** mathematical correctness. Existing Lean CI continues to check compiled theorems; reviewers are responsible for semantic correspondence.

## Interpreting a proof or counterexample

Document exactly which assumptions and model class a negative result excludes, what broader physical or mathematical hypotheses remain unresolved, and a follow-up proof or experiment where possible. If none is known, say so. Do not use this requirement to shield a refuted claim or manufacture an unsupported repair. Positive mathematical results also require independent physical evidence for physical conclusions.

## Authorship and integrity

Attribution follows original mathematical contributions, Git history, PR discussion, and any independent publications. Contributors are not required to endorse Wave Confinement Theory or give up ownership of their independently written results. Follow the repository's licenses and respect authors' publication rights. No monetary rewards or guaranteed publication are offered.

Do not silently weaken a conjecture, misrepresent existing mathematics as new, conflate numerical simulations with analytic proofs, or advertise unreviewed GC candidates as verified open problems. Public issues can be indexed; do not post secrets or private unpublished work without permission.

**Anyone can contribute, and the research program continues even when no one else does.**
