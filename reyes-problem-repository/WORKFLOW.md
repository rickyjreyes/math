# GitHub Issue, Lean, and Paper Workflow

The Reyes Problem Repository is an **open invitation** to work on mathematical questions connected to an ongoing, independently conducted research program. Its 300 entries are research candidates, not 300 certified novel open problems. Work continues whether or not outside contributors join. Contributors receive credit for their own work, including results that disprove or narrow an original conjecture.

**No replacement architecture:** The existing source files under `lean/`, `papers/`, and `preprints/` remain where they are. Existing papers and verified results are not reclassified as incomplete just because a broader GC question remains open. The GC layer tracks questions, evidence and remaining obligations. It never silently edits a Lean theorem or manuscript to match a GC issue.

## One research task, familiar developer workflow

1. **Find the GC problem file.** Use [the 300-problem roadmap](ROADMAP_300.md), and check the [adoption inventory](EXISTING_WORK.md) for existing proof modules, papers and issues.
2. **Reuse the existing issue.** Search GitHub for the exact `[GCxx]` identifier and related mathematical/formalization issues before creating one. GC01, GC06, GC11, GC36 and GC43 already have research issues. Do not bulk-create hundreds of issues for unreviewed questions.
3. **Freeze the acceptance criterion.** A problem or subtask issue identifies a versioned statement, equation, parameters, spaces, quantifiers, claimed resolution (theorem or counterexample), and a list of obligations. A GC roadmap *candidate* may first need a scope/literature issue before it can be a solvable theorem.
4. **Contribute via a pull request.** A PR cites the issue, describes exactly which obligation it addresses, compares earlier results, and points to the exact Lean module and theorem declaration. An existing verified theorem may be **adopted by reference**, without copying or reproving it.
5. **Run existing Lean CI.** The existing `lean/` project and its full `lake build` checks remain the source for machine-checking. The proof must not depend on `sorry`, `admit`, or new unreviewed axioms. A green build establishes the encoded theorem, not by itself that the issue's entire mathematical claim has been proved.
6. **Review correspondence.** A reviewer compares every issue obligation against the exact Lean declaration, including hypotheses and direction of implication. Check that a counterexample really refutes the quantified statement. A solution to a special case is recorded as partial progress, not a full resolution.
7. **Optional paper.** A paper is welcome but not mandatory. If used, it should cite a specific Lean declaration and commit, identify its formally verified claims, and clearly distinguish extra analytic, numerical, or physical discussion. It cannot silently present a stronger theorem as Lean verified. Existing manuscripts are linked, not rewritten merely to satisfy this process.
8. **Update status, then close the correct issue.** A milestone/task issue can close when its own frozen scope has been checked; the parent GC may remain open. Close a whole-problem issue only after every full-scope acceptance criterion is satisfied, its Lean verification and correspondence review are documented, and the [problem registry](problem_registry.json) is updated in the same reviewed PR.

## Scope matters: problem versus milestone

The repository already has issues [#54](https://github.com/rickyjreyes/math/issues/54), [#55](https://github.com/rickyjreyes/math/issues/55), [#56](https://github.com/rickyjreyes/math/issues/56), [#57](https://github.com/rickyjreyes/math/issues/57) and [#58](https://github.com/rickyjreyes/math/issues/58). Their titles and closure criteria concern *research milestones*. Finishing such a milestone does **not** automatically finish GC01, GC06, GC11, GC36 or GC43 as a whole.

A valid contribution may be a formal lemma, special-case theorem, negative result, corrected hypothesis, prior-art comparison, or a complete solution. Do not write `Closes #N` on a PR unless **that exact issue's** acceptance criteria are fully met. Use `Refs #N` or `Part of #N` otherwise.

## Evidence and verification contract

| Evidence type | What it establishes | What it does not establish |
|:--|:--|:--|
| A compiled Lean declaration | The elaborated proposition has a checked proof, subject to its trusted axioms and dependencies | That the proposition matches a broader English conjecture |
| A reviewed issue-to-theorem mapping | The formal statement satisfies particular frozen obligations | That a different problem or all possible generalizations are solved |
| A published paper | Research exposition and attributed mathematical claims | Automatically equivalent claims to any cited Lean theorem |
| A simulation or experiment | Results for the stated setup and its measurements | A universal mathematical proof or untested physical interpretation |
| A literature review | Documented prior work for the scope examined | A guarantee of worldwide novelty |

The [resolution record](completion_records.json) is an optional, machine-readable index for **newly accepted full or partial resolutions**. No entries are pre-populated: existing manuscripts must undergo correspondence review before being adopted as verified GC completions. The [validation script](scripts/validate_completion_records.py) checks record format and local links. Only Lean CI checks proof compilation, and reviewers still check mathematical equivalence.

### Required resolution evidence

- GC ID, exact issue URL, whether the issue is a **milestone** or **whole problem**, and the frozen statement/acceptance criteria.
- Lean source path, exact fully qualified theorem declaration, exact commit SHA, and corresponding successful Lean CI run.
- Linked PR and an identifiable reviewer statement that the Lean declaration matches each closed obligation.
- Verdict: proved or refuted, plus a list of remaining obligations or an explicit statement that none remain within the frozen scope.
- Optional paper path and an exact manuscript claim reference, plus a classification of unformalized discussion.
- Updated human [status](STATUS.md) and machine [registry](problem_registry.json) when the GC-level status changes.

Only the exact identified obligations are verified. Absence of a manuscript is not a blocker. Absence of proof correspondence **is** a blocker to declaring formal completion.

## Adopt existing mathematics first

Before assigning an issue to a new proof effort, inspect [existing-artifact links](EXISTING_WORK.md). If a prior Lean declaration already proves the exact claim, cite the original module, fully qualified declaration, original commit and CI record. A new PR can update the issue/adoption record without duplicating the theorem. If the old proof only treats one parameter range, keep the larger issue open and credit that narrower result.

If an existing paper predates this workflow, it is not retrospectively invalidated. The adoption record should describe the overlap accurately; corrections to a manuscript require their own separate research review.

## Attribution and participation

The author of an original theorem, counterexample, formalization or manuscript keeps appropriate attribution. The repository does not require contributors to endorse Wave Confinement Theory or transfer ownership of their independent discoveries. Link authors, PRs, papers and versions accurately. Results inconsistent with a hypothesis are welcome and scientifically useful.

Contributing is optional. The program is designed to support its original researcher working alone as well as outside researchers and AI-assisted contributions, all through the same issue, PR and Lean checks.
