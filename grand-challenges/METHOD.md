# Method: from candidate questions to rigorous research problems

[Problem book](README.md) · [Current register](STATUS.md) · [Candidate notebook](NOTEBOOK.md) · [Literature ledger](LITERATURE.md) · [How to contribute](CONTRIBUTING.md)

This is a **free and open mathematical research workflow**, borrowing useful organizational ideas from collaborative problem notebooks, selective landmark problem lists, and referenced research surveys. It does not claim any historical mathematician endorsed the questions in this repository.

## Separate five layers

1. **Notebook hypothesis:** a possible pattern, analogy, identity, obstruction, or question. May be false or ill-posed.
2. **Candidate research problem:** a mathematical question with a proposed model and falsifiable tests.
3. **Literature-checked problem:** terms frozen and closest prior work inspected sufficiently to make a qualified scope statement. One or two citations are only an *initial* review.
4. **Verified open problem:** a narrowly formulated statement not settled by the literature examined, with explicit search scope, date, and independent critical review. This label does not guarantee global novelty.
5. **Resolved problem:** a full proof, counterexample, impossibility theorem, or established existing result answering the **specific frozen statement**. Lean validation concerns the encoded theorem only.

Do not promote an item by popularity, AI confidence, a graph, a numeric simulation, or passing CI alone.

## A repeatable seven-step workflow

### 1. Record

Add the candidate to [NOTEBOOK.md](NOTEBOOK.md), preserving its original motivation and any possible counterexample. Do not number a speculative note as an established open conjecture.

### 2. Freeze the question

Create a dossier with **equations, domains, parameter intervals, initial/boundary data, quantified claim, topology, and complete resolution criteria**. If a model is not yet fixed, mark **model pending**, not "formally stated."

### 3. Search for earlier work

Search publisher sites, arXiv, MathSciNet/zbMATH when accessible, Google Scholar or free alternatives, and existing repository sources. Record each paper's exact model, assumptions, result, and differences in [LITERATURE.md](LITERATURE.md) or the dossier. Citation ≠ proof of novelty.

### 4. Try to disprove it

Check zero/constant states, scaling, dimensions, parameter boundaries, symmetries, loss of compactness, degenerate cases, and limiting regimes. A found counterexample is a positive result. Retain withdrawn claims in the historical record.

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

A problem is closed only when its exact version is answered. Store the theorem or counterexample, source, proof assumptions, verification status, and a link to the issue/PR. If a stronger generalization remains, create a **new** problem version rather than quietly changing the goalposts.

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
