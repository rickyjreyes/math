# Activating a GC research question

**Problem quality standard:** [Six-part formal question, literature and proof checklist](PROBLEM_STANDARD.md) · [Current scoping queue](formal-reviews/REVIEW_QUEUE.md).

**Short operational guide.** For the full scoping and literature method use [METHOD.md](METHOD.md); for issue, pull-request, Lean, and review requirements use [WORKFLOW.md](WORKFLOW.md). This page stays because it contains the **GC-specific entry route and issue generator**. It is not a second mathematical status policy.

**Current corpus (November 2, 2026):** [ROADMAP_300.md](ROADMAP_300.md) covers 300 questions; [scoped/README.md](scoped/README.md) contains **236 existing GC65–GC300 scoped dossiers**. GC66–GC300 have proposed precise targets but remain unreviewed candidate research questions. None becomes a new, globally verified open problem merely because a scoped dossier exists. The 1–10 [difficulty ratings](DIFFICULTY_RUBRIC.md) measure subjective research burden, not proof completion.

## Activate one candidate

1. **Choose a fixed ID and read both files:** start from [the roadmap](ROADMAP_300.md), follow the original problem under `problems/`, and inspect its `scoped/GCxx.md` formulation (GC65–GC300) or the original [formal statements](FORMAL_PROBLEMS.md) (GC01–GC65). The scoped statement is not automatically the final accepted problem.
2. **Check for solved subclaims before doing work:** read [existing source and proof mappings](EXISTING_WORK.md), [exact-scope verified results](VERIFIED_LEAN_RESULTS.md), [the GC65 adoption inventory](GC65_ADOPTION.md), prior issues, and [the literature ledger](LITERATURE.md). Do not duplicate an existing theorem or confuse a partial source proof with full GC closure.
3. **Freeze the issue obligation:** record the exact equation or algorithm, domain, regularity, parameter values/ranges, quantifiers, nonvacuity, known counterexamples, literature comparisons and a precise yes/no or quantified milestone. [October 30 scoping objections](SCOPING_AUDIT_GC65_GC300_2026-10-30.md) must be addressed, especially P0 concerns.
4. **Draft a GitHub issue without opening one automatically:**

   ```bash
   python3 reyes-problem-repository/scripts/render_gc_issue.py GC66
   ```

   Search for an existing GC or mathematically equivalent issue before opening another. The [issue form](https://github.com/rickyjreyes/math/issues/new?template=gc_problem.yml) captures the target and evidence.
5. **Verify only what is proved:** a PR cites its specific issue obligation, source theorem, exact Lean declaration/commit and CI when applicable. A narrower result may close its milestone **without** marking its parent GC solved. Update [STATUS.md](STATUS.md), [problem_registry.json](problem_registry.json) and [completion_records.json](completion_records.json) only when their respective review requirements are satisfied.

## Before the GC catalogue

Use [NOTEBOOK.md](NOTEBOOK.md) for new, speculative questions, negative findings or conceptual forks that do **not** yet warrant a numbered GC. The notebook is a discovery log, not a second registry. Preserve refuted ideas and their source citations rather than deleting inconvenient results.

**Evidence rule:** Formal proof, numerical observation, novelty assessment and physical validation are separate claims. Retain original theorem authorship and unchanged historical questions.
