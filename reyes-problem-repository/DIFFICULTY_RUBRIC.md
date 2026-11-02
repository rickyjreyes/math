# Difficulty ratings for the Reyes Problem Repository

**Version:** editorial v1, 2026-11-02. **Coverage:** GC01–GC300. The 300 scores in [ROADMAP_300.md](ROADMAP_300.md) and [problem_registry.json](problem_registry.json) are **provisional, low-confidence judgments**. No mathematically defensible objective difficulty score exists for a question whose final model and prior art have not been independently reviewed.

## Scale

| Score | Estimated work required after scoping |
|:--:|:--|
| 1–3 | Standard calculation or elementary adaptation; the original question may already be known |
| 4–5 | Focused technical argument or a small proof-assistant formalization |
| 6–7 | Substantial theorem, controlled computational certificate, or multistep formal development |
| 8–9 | Advanced nonlinear/spectral/variational analysis or substantial theory integration |
| 10 | Long research-program scale; major unresolved proof dependencies or genuinely hard classification |

Scores estimate **the burden of a rigorous attempt under a specified mathematical model**, not the probability that the result is true, original, currently open, physically real, or important. Two experts may differ by two or more points. A narrow milestone can be easier than the broader GC question.

## Method and limitations

The initial scores are a **rule-guided editorial baseline**, calibrated by subject (PDE dynamics, spectral/variational geometry, constrained field theory, inverse problems, pattern formation, topology, computation, formalization, multiscale limits and photonics), then adjusted for breadth and words such as “universal,” “sharp,” “long-time,” “finite,” “local,” or “certified.” A small number of distinctive cases receive explicit human-readable editorial overrides (e.g. GC200's classical fixed-winding calculation and GC278's detector/nonlinearity distinction). No empirical duration estimates or proven hardness reductions are implied.

All 300 values have `difficulty_confidence: low_unreviewed`. **Difficulty is not progress**: a theorem may be fully Lean-checked in a narrower scope while the GC classification is still open. The GC66–GC300 records retain `candidate`, `not_reviewed`, and `novelty_established: false`.

Before citing a score as research planning evidence, freeze all spaces, operators, parameters and quantifiers, search the literature, identify one decisive milestone, and obtain independent mathematical review. A known solved or ill-posed question should be relabeled or rephrased after review rather than celebrated as difficult.

See [METHOD.md](METHOD.md), the [October 30 scoping audit](SCOPING_AUDIT_GC65_GC300_2026-10-30.md), and [CANDIDATE_ACTIVATION.md](CANDIDATE_ACTIVATION.md).
