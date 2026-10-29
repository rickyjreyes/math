# Contributing to the Reyes Problem Repository

This is an open, no-prize, continuously evolving mathematical research repository. **Criticism, prior-art corrections, counterexamples and strengthened problem statements are as valuable as proposed proofs.**

[Catalogue](README.md) · [Precise questions](FORMAL_PROBLEMS.md) · [Method and promotion rules](METHOD.md) · [Status register](STATUS.md)

## Contribute through GitHub

1. Read the exact problem statement and check its [flagship dossier](flagship/) when available.
2. Search for related existing results. Cite the **specific theorem and assumptions**, not just a paper title.
3. [Open a GitHub issue](https://github.com/rickyjreyes/math/issues/new) or submit a pull request. Include the GC number and select a contribution type: prior work, counterexample, proof, formalization, model correction, or numerical falsification.
4. Describe the mathematical model, spaces, quantifiers, and the **precise claim** your contribution addresses.
5. Link reproducible calculations or Lean source where relevant. Lean proofs must compile without unacknowledged axioms or placeholders, and the theorem must match the claimed statement.
6. Request an explicit status change in `problem_registry.json` only if justified by evidence. A partial case does not automatically settle a full classification problem.

## Issue format

**GC identifier:** GCxx  
**Contribution type:** Literature / Counterexample / Proof / Lean / Numerical / Scope correction  
**Exact statement being discussed:**  
**Claim and assumptions:**  
**Closest known references, with links and theorem numbers:**  
**Proof or counterexample / reproducibility links:**  
**What this does NOT establish:**  
**Proposed catalogue status change, if any:**

A ready-to-fill GitHub issue form is available from the repository's new-issue chooser once the PR adding it is merged.

## Editorial safeguards

- Do not claim mathematical novelty or century-scale difficulty without adequate comparison to the literature.
- Do not erase counterexamples or superseded formulations.
- Do not mistake numerical simulations for global PDE proofs.
- Do not conflate kernel-checked Lean statements with broader physical validity.
- Respect authorship, licensing, and quotations; link to publications instead of copying entire papers.
- Public issues and pull requests may be indexed by search engines. Never include secrets or private unpublished material without permission.

## Recognition instead of prizes

This project offers **no monetary rewards**. Attribution is through public issue and pull-request history, cited papers and theorem references, and credit for definitive counterexamples, corrections, or proofs.
