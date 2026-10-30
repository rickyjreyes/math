# WCT research direction and interpretation

## Foundational objective

This repository is the mathematical and formal-verification component of an ongoing Wave Confinement Theory (WCT) research program. Its long-term objective is to investigate whether confinement, resonance, phase dynamics, curvature, and nonlinear field structure can support a mathematically consistent, experimentally testable account of fundamental physical phenomena. It also develops mathematics useful independently of those physical hypotheses.

**Mathematical independence and adversarial verification are methods for advancing and correcting WCT, not an abandonment of foundational physics or a compulsory pivot to engineering.** Optics, acoustics, computation and control are complementary applications, not replacements for the physical objective.

These objectives are open research questions, not established physical conclusions.

## Evidence layers

| Evidence | Establishes | Does not establish alone |
| --- | --- | --- |
| Lean proof | The exact formalized proposition under its encoded assumptions and trusted dependencies | A broader manuscript, a model's physical validity, or WCT as a whole |
| Analytical proof | An argument about a declared mathematical model, subject to independent review | Kernel verification without exact formal correspondence |
| Simulation | Behavior of a specified computation or numerical model | A universal theorem or physical confirmation |
| Physical measurement | Evidence for a testable physical claim in its measured regime | Universal validity of the proposed framework |

An independently defined Hamiltonian may support minimizers and orbital stability without already being derived from a physically consistent parent field theory. This is a missing bridge, not a theorem that the bridge is impossible.

## Positive and negative results: the scope rule

1. **State the quantified claim.** Identify equation, model version, spaces, parameters, domains, assumptions and inference.
2. **Limit the conclusion to that scope.** A counterexample or impossibility theorem rules out the specified construction or class. It does not automatically rule out other field structures, every WCT model, or a physical program.
3. **Preserve genuine failures.** Do not hide a counterexample, change a frozen claim quietly or invent a successful repair. If a theorem genuinely excludes the relevant entire class or hypothesis, say so.
4. **Extract a constructive next test.** Specify which assumptions caused the failure, which alternatives remain **unsettled**, and a meaningful next theorem, model construction or discriminating experiment. When no plausible alternative is known, say that instead of inventing one.
5. **Apply equal discipline to successes.** A mathematical theorem is not experimental validation. Any claimed connection to physical observations requires a separate derivation, predictions and tests.

This is a standard of constructive adversarial research, not permission to move the goalposts indefinitely. A negative answer may genuinely defeat a hypothesis.

### Examples

- **F08:** The positive-sign real-part scalar-gradient Gram tensor cannot by itself have Lorentzian signature. This does not rule out every other possible metric with additional structure. Any alternative requires an independent construction and physical justification.
- **E68:** The unrestricted local gradient-energy estimate fails in specified dimensions and regularity classes. Corrected estimates are distinct results; the obstruction is not a proof that every form of wave localization fails.
- **F01:** Strict binding, constrained minimizers and orbital stability are mathematical results for an independent fourth-order Hamiltonian. A ghost-free parent derivation, applicability to nature and discriminating observations remain open.
- **F09:** Identifiability limitations refer to the particular observation map, not all possible experiments or physical dynamics.

## Constructive physical bridges still to investigate

- Consistent parent-field formulations and an explicit physical degree-of-freedom count, including ghost freedom in the regimes claimed.
- Viable relativistic or geometric constructions, without assuming a blocked scalar-gradient tensor can supply them.
- Localization, lifetime, dimensional behavior and perturbation stability of solutions to the actual proposed equations.
- Empirical predictions with error budgets and measurements capable of distinguishing WCT-inspired models from existing models.

No item above is certified merely by this repository's existing mathematical results.

## Repository-wide editorial policy

- Frame work as **rigorous development, critical testing, constructive refinement and possible empirical validation** of a continuing foundational program.
- Label claims **proved**, **refuted under explicit assumptions**, **partially resolved**, **conjectural**, or **empirically supported** as appropriate.
- For significant obstructions, record: exact failed statement; how widely it applies; what remains open; next mathematical or experimental test (or why none is known); and implications for the relevant physical hypothesis.
- Do not promote a model-specific no-go into a program-wide no-go without a theorem covering that wider class.
- Do not present independently verified mathematics as physical confirmation. Do not presume an alternative is viable because an old one fails.
- Contributors are not required to endorse WCT, and negative results must receive full credit and accurate reporting.
- Preserve theorem statements, manuscript history, exact Lean inventories and the frozen scope of individual research issues. The framing policy does not change any of them.

See [manuscript catalogue](CONTENTS.md), [formalization status](lean/formalization.yaml), and [problem workflow](reyes-problem-repository/WORKFLOW.md).
