# Activating GC66–GC300 without rewriting the research

**Current state (2026-10-30):** GC66–GC300 retain 235 historical research sketches. The [new 236-file scoped collection for GC65–GC300](scoped/README.md) provides independently reviewable **proposed** mathematical formulations, not certification that every statement is correct, original or unsolved. The registry continues to label them candidates pending further scrutiny.

**Policy:** Preserve the original drafts and use each versioned scoped model as a starting point. Review internal consistency, nonvacuity, nearest known mathematics and the exact theorem-to-issue match before declaring it frozen or solvable. Amend models explicitly by version rather than silently rewriting historical questions.

## Scope-first checklist

1. **Choose the existing GC file:** Read its current title, research question, suggested test and parent IDs. Keep the permanent ID and original draft wording as historical context.
2. **Search existing sources:** First check [the original 65 source adoption map](GC65_ADOPTION.md), [Lean formalization status](../lean/formalization.yaml), [manuscripts](../CONTENTS.md), existing GitHub issues and scholarly literature. Search across other research repositories where relevant, without assuming a similarly named theorem establishes the claim.
3. **Freeze the model and hypotheses:** Specify the exact equation or operator, domain, initial/boundary conditions, function spaces, parameter ranges and all quantifiers. Separate physical hypotheses from purely mathematical statements.
4. **Choose the issue type:** If the model is not yet precise, open a **scoping task**. When precise, create a **whole-problem issue** or a smaller verifiable milestone, citing the GC source and searching for duplicates first. Never label a newly generated conjecture as already verified open.
5. **Define success in advance:** A proof or counterexample must meet an explicit acceptance checklist. Include the small cases that could refute the claim, and avoid changing the target merely because an attempt fails.
6. **Contribute in either direction:** Paper → Lean or Lean → optional paper. A PR can add a partial analytic result without calling the full issue verified. For *formal completion*, provide the exact Lean declaration and successful CI run, plus independent review that it meets the frozen issue statement.
7. **Preserve history and attribution:** Corrections and new subproblems belong in linked issues and PRs. Do not move or replace existing papers or formal proofs. A milestone can close even when the parent GC stays open.

## Illustrative activation of GC66

[GC66: Internal-mode radiation damping](problems/01-wave-dynamics/GC66.md) currently asks whether an isolated internal mode near a localized excited state radiates energy.

Before opening a proof-completion issue, fix **which excited state exists**, the stationary equation and spectral assumptions, a precise meaning of isolated internal mode and continuous spectrum, the nonlinear resonance condition, and the time-asymptotic damping norm. The proposed first test is to compute a resonance coupling coefficient or exhibit a symmetry forcing it to vanish.

Until those are fixed, the honest task is *scope and literature review*, not a claim that a particular universal damping theorem is unsolved.

## Draft an issue, do not generate hundreds

At the repository root:

```bash
python3 reyes-problem-repository/scripts/render_gc_issue.py GC66
```

This prints a **draft**, not an opened GitHub issue. You must check all existing issues manually, including related problems in other repositories. The generator rejects GC IDs already linked to an existing GC issue in the adoption register. The existing [GC problem issue form](https://github.com/rickyjreyes/math/issues/new?template=gc_problem.yml) captures the exact claim and acceptance criteria.

## Do not confuse stages

- A **candidate outline** is an interesting research direction.
- A **frozen mathematical problem** is a definite theorem or counterexample target.
- A **paper** presents an argument and may precede or follow Lean.
- A **Lean-checked theorem** establishes the proposition that it encodes.
- A **resolved GC issue** additionally requires a reviewed match to every frozen issue obligation.

This staged process leaves the existing 235 problem sketches untouched, keeps the door open for outside contributions, and allows new mathematical problems to grow out of real verified research.
