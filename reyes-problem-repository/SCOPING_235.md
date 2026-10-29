# GC66–GC300: Research Candidate Activation

The **235 new problems are preliminary research directions**, not verified globally open conjectures or fully quantified formal statements. Their existing prose and first decisive targets are retained intact. This page explains how to turn one into a precise mathematical issue when a researcher or AI system starts working on it.

[300-problem roadmap](ROADMAP_300.md) · [Existing 65 problems and prior work](EXISTING_WORK_65.md) · [Issue ↔ Lean ↔ optional paper workflow](WORKFLOW.md) · [Contributions](CONTRIBUTING.md)

## Activate only when someone wants to work on the question

1. **Read the candidate and its parent GC problems.** Find the research motivation, proposed model, and `first_test` in [the canonical registry](problem_registry.json). A suggested first test is not a full theorem.
2. **Search for earlier mathematics and existing GitHub issues.** Find related Lean declarations, manuscripts and relevant established literature. Reuse a sufficiently matching issue instead of automatically creating 235 new GitHub issues.
3. **Freeze the mathematical object.** Specify equations or formal transition rules, spatial domain, parameters, boundary/initial conditions, function spaces, assumptions, norms and solution concept. Distinguish the existing program's current mathematics from a genuinely new model.
4. **State the exact claim and its quantifiers.** Define which data vary, what conclusion is asserted, and what is an admissible counterexample. A single provable milestone and a full classification can be separate issues.
5. **Falsify early.** Test trivial and degenerate cases, symmetries, units, parameter boundaries, known no-go theorems, numerical artifacts and prior literature. Record uncertainty about originality explicitly.
6. **Create an issue only after scoping.** Use [the GC issue form](https://github.com/rickyjreyes/math/issues/new?template=gc_problem.yml), or generate a **local preview without creating an issue** with `python3 reyes-problem-repository/scripts/render_gc_issue.py GC277`. If literature review is incomplete, the issue is for scoping, not a verified open conjecture.
7. **Submit a PR when there is a result.** Mathematical exposition can come first or follow the formalization. For a claimed GC completion, require a specific Lean declaration, commit, successful CI and mathematical issue-to-theorem correspondence review. An optional paper cannot overstate the Lean result.
8. **Promote based on evidence, not volume.** Preserve `candidate` until scope and prior art justify an update. Closing a narrow issue does not mean the original GC question has been fully resolved.

## Four concrete examples

### [GC66: Internal-mode radiation damping](problems/01-wave-dynamics/GC66.md)

The question proposes radiation of an excited-state internal mode into the continuous spectrum of a fourth-order cubic–quintic flow. Freeze a specific stationary profile or explicit existence hypothesis, the linearized operator, spectral/resonance conditions, a radiation observable and the actual nonlinear coupling coefficient. A first theorem might establish a nonzero coupling under those hypotheses or prove a symmetry obstruction. Existing orbital stability of a minimizer set does not settle the excited-mode question.

### [GC220: P-completeness of local-wave reachability](problems/09-computability-complexity/GC220.md)

Publish the exact finite-state rule, encoding, time representation (unary/binary), allowed initial states, target predicate and input size. P-completeness requires both membership in P and a valid logspace reduction from a P-complete problem, unless a better complexity classification is found. Without a fixed rule, the question is not a single decision problem.

### [GC277: Interference-based XOR robustness](problems/12-photonic-wave-computing/GC277.md)

Freeze the phase-to-intensity transfer function, Boolean phase encoding, optical power constraints, detector threshold, noise model (deterministic bounds versus probability law) and interpretation of truth-table correctness. First prove sufficient margins and then their sharpness. A simulated XOR truth table alone does not certify arbitrary optical noise or hardware.

### [GC300: Full-stack verified photonic arithmetic](problems/12-photonic-wave-computing/GC300.md)

Fix compiler semantics, a physical gate/circuit transfer law, error budgets, detector decision and calibration assumptions. A Lean composition theorem can then prove that accepted component certificates imply a correct decoded result. Physical calibration measurements remain separate evidence and should not be described as deduced from Lean.

## Paper ↔ Lean remains bidirectional

A paper-first contributor can submit a new theorem and formalize it; a Lean-first contributor can derive and kernel-check a result and later publish exposition. **Formal GC closure**, however, requires the frozen issue and exact formal declaration to agree. Partially supported, counterexample, model-correction and prior-art PRs are welcome without claiming the entire GC resolved.

The purpose is not to manufacture busywork for future mathematicians or AI systems. A candidate is worth activating when it leads to a meaningful mathematical result, useful obstruction, or a credible direction for the ongoing scientific program.
