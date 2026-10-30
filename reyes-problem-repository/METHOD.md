# Method: from candidate questions to rigorous research problems

[The Reyes Problem Repository](README.md) · [Current register](STATUS.md) · [Candidate notebook](NOTEBOOK.md) · [Literature ledger](LITERATURE.md) · [How to contribute](CONTRIBUTING.md)

This is a **free and open mathematical research workflow** for developing and critically testing mathematical foundations of the continuing WCT program. Independent proof does not require endorsing WCT's physical claims; it is a way to advance, correct and constrain them, not to replace the founding objective. It borrows organizational ideas from collaborative problem notebooks, selective landmark problem lists and research surveys. It does not claim any historical mathematician endorsed the questions. See [research direction](../RESEARCH_DIRECTION.md).

## Separate five layers

1. **Notebook hypothesis:** a possible pattern, analogy, identity, obstruction, or question. May be false or ill-posed.
2. **Candidate research problem:** a mathematical question with a proposed model and falsifiable tests.
3. **Literature-checked problem:** terms frozen and closest prior work inspected sufficiently to make a qualified scope statement. One or two citations are only an *initial* review.
4. **Verified open problem:** a narrowly formulated statement not settled by the literature examined, with explicit search scope, date, and independent critical review. This label does not guarantee global novelty.
5. **Resolved problem:** a full proof, counterexample, impossibility theorem, or established existing result answering the **specific frozen statement**. For any *newly claimed formally completed GC issue*, the [GC proof contract](WORKFLOW.md) additionally requires a Lean-checked result and reviewed issue-to-theorem correspondence. This contract is not retroactive to pre-existing manuscripts.

Do not promote an item by popularity, AI confidence, a graph, a numeric simulation, or passing CI alone.

## A repeatable seven-step workflow

### 1. Record

Add the candidate to [NOTEBOOK.md](NOTEBOOK.md), preserving its original motivation and any possible counterexample. Do not number a speculative note as an established open conjecture.

### 2. Freeze the question

Create a dossier with **equations, domains, parameter intervals, initial/boundary data, quantified claim, topology, and complete resolution criteria**. If a model is not yet fixed, mark **model pending**, not "formally stated."

### 3. Search for earlier work

Search publisher sites, arXiv, MathSciNet/zbMATH when accessible, Google Scholar or free alternatives, and existing repository sources. Record each paper's exact model, assumptions, result, and differences in [LITERATURE.md](LITERATURE.md) or the dossier. Citation ≠ proof of novelty.

### 4. Test, challenge and refine the model

Seek affirmative existence or construction proofs alongside counterexamples. Check zero/constant states, scaling, dimensions, parameter boundaries, symmetries, loss of compactness, degenerate cases, and limiting regimes. A valid counterexample is a result, but it refutes only the quantified claim. Record the failed assumptions, the broader questions still unsettled and the next constructive test. Retain withdrawn claims in the historical record; do not quietly change the frozen target.

### 5. Apply a Smale-style quality screen

Score each dimension **0–3** only after evidence exists. Blank = not assessed, not zero.

| Criterion | 0 | 1 | 2 | 3 |
|:--|:--|:--|:--|:--|
| **Precision** | No model | Model sketched | Frozen with gaps | Fully quantified and falsifiable |
| **Prior-art clearance** | No review | Leads collected | Focused comparison done | Independent checked review with scope |
| **Mathematical consequence** | Unexplained | Local interest | Useful broad connection | Resolution changes a recognized structural question |
| **Tractability of first step** | None | Vague | Explicit test | Reproducible proof/counterexample target |
| **Evidence discipline** | Conflated claims | Some separation | Clear qualifiers | Analytic/Lean/numeric/physical statuses auditable |

**Maximum 15**, but there is **no automatic novelty threshold**. Prefer five consequential and well-scoped flagship questions to fifty unexamined grand claims. Never label a problem "verified open" from a score alone.

### 6. Publish and invite criticism

Use free GitHub issues (one topic per issue), discussions if the repository owner enables them, source files, Lean 4, and optional free preprint/archive services that accept the work. Attribute contributors and preserve correction history.

### 7. Record resolution

A newly claimed **formally completed GC task** is closed only when its exact frozen issue scope is answered by a Lean-checked result and reviewer-confirmed correspondence. A narrow milestone issue may close even if the larger GC problem remains open. Record the theorem or counterexample, source, proof assumptions, Lean build, correspondence review, and issue/PR. Preserve existing established mathematical results without reclassifying them retroactively. If a stronger generalization remains, create a **new** problem version rather than quietly changing the goalposts.

## Constructive interpretation of negative findings

For significant obstructions, record the exact statement and scope; whether it defeats a particular construction, a whole defined model class or the intended physical hypothesis; any **unresolved** alternatives; and the next concrete mathematical or empirical test. If no plausible alternative is known, state this clearly. Do not relabel a refuted theory as successful, and do not generalize a special-case obstruction into a universal WCT no-go. The same standard applies to positive results: mathematical existence, stability or spectral properties require a separate physical bridge before being described as experimentally valid.

## Explicit status transitions

- `candidate`: proposed, neither comprehensive literature search nor precise model audit completed.
- `scoping`: exact statement and admissible model are being frozen.
- `literature_checked`: closest relevant results compared; gap report dated.
- `open_verified`: conditional and qualified assessment after critical review; not a claim of absolute worldwide priority.
- `partially_resolved`: nontrivial specific part answered but broader classification still pending.
- `resolved`: exact problem resolved analytically or by a documented existing theorem.
- `withdrawn`: ill-posed, duplicative, or superseded; explanation retained.

The machine-readable [problem_registry.json](problem_registry.json) is the source of truth for status. Edit the register in the same PR as any status change. The validation script checks IDs, links, and formats but cannot determine whether a conjecture is original or true.

## No-cost toolchain

- **GitHub:** hosting, versioning, issue discussion, attribution and code review.
- **Lean 4/Mathlib:** precise formal proof checking; the theorem encoded must match the manuscript.
- **Python standard library and GitHub Actions:** syntax/inventory validation.
- **arXiv / Zenodo:** optional scholarly distribution or archival deposit, subject to their terms; none of these releases is automatic.
- **MathOverflow:** focused research-level questions after checking existing answers; not bulk catalogue advertising.

## Attribution

Cite the original article for an earlier theorem, credit the person discovering a counterexample, and record external corrections without changing authorship of pre-existing results. Do not misrepresent a suggested problem as a theorem already proved or as a discovery with century-scale difficulty.

## Three-hundred-question folder corpus (2026-10-29)

- **Original scoped statements, GC01–GC65:** Canonical text remains in [FORMAL_PROBLEMS.md](FORMAL_PROBLEMS.md), with mirrored individual files.
- **New research sketches, GC66–GC300:** Each has its own file in one of [12 subject folders](problems/README.md) containing a question and first decisive proof or counterexample target. Neither model completeness nor novelty is claimed.
- **Screening shortlist, 25:** [FOUNDATIONAL_SHORTLIST.md](FOUNDATIONAL_SHORTLIST.md) tracks prospective foundational importance, without promoting problem status.
- **One source of machine truth:** [problem_registry.json](problem_registry.json) contains all 300 permanent IDs, paths, and evidence statuses; the index and status table mirror it.
- **Quality gate:** A plausible prompt cannot become `open_verified` solely because an LLM proposes it, because its computation runs, or because a formal proof of a *different* theorem compiles. Each promotion requires exact hypotheses, prior work, a falsification test, and mathematical review.

Adding more topics is not itself scientific progress. Favor stronger mathematical connections, precise disproofs and new theorems rather than maximizing the number of entries.

## The issue / PR / Lean integration layer

[WORKFLOW.md](WORKFLOW.md) is the canonical non-disruptive contract. [EXISTING_WORK.md](EXISTING_WORK.md) links already-existing source modules and papers to a small pilot of existing GC issues without declaring the broader problems solved. New [completion records](completion_records.json) start empty and require exact Lean declaration, commit, CI and issue-to-theorem review. The workflow supplements existing Lean and paper conventions; it does not relocate, duplicate or modify completed mathematics. Outside participation is welcome but optional, and contributor attribution is preserved.
