# Lean verification and maintenance

Run all commands from `lean/` with the pinned toolchain.

| Task | Command |
|---|---|
| Full maintained library | `lake build` |
| General dependency audit | `lake env lean scripts_audit/DependencyAudit.lean` |
| F09 / GC26 | `lake env lean F09Audit.lean` |
| GC01 individual orbit | `lake env lean GC01IndividualOrbitAudit.lean` |
| GC01 vortex estimates | `lake env lean GC01VortexAudit.lean` |
| GC01 spectral reduction | `lake env lean GC01SpectralAudit.lean` |
| GC06 shell binding | `lake env lean GC06ShellAudit.lean` |
| GC06 / GC16 / GC01 continuation | `lake env lean GC06GC16GC01ContinuationAudit.lean` |
| GC08 curvature closures | `lake env lean GC08Audit.lean` |
| Analytic certifications | `lake env lean AnalyticCertificationAudit.lean` |
| E18 | `lake env lean E18CertificationAudit.lean` |
| E68 | `lake env lean E68CertificationAudit.lean` |
| E69 | `lake env lean E69CertificationAudit.lean` |
| Refresh navigation | `python scripts_audit/generate_catalog.py` |
| Check navigation | `python scripts_audit/generate_catalog.py --check` |

Focused workflows under [`.github/workflows`](../../.github/workflows) define build prerequisites, expected roots and allowed axioms. Run the corresponding `lake build MathProofs.<Module>` before standalone audits when needed. The two existing Python GC axiom checkers consume the corresponding audit logs; consult their workflows for exact invocation. Do not interpret a successful catalogue check as a proof audit.

[Complete module catalogue](../catalog/README.md) · [Formalization status](../formalization.yaml)
