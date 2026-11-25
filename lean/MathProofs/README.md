# MathProofs source library

[Browse every module by subject](../catalog/README.md). The `.lean` files retain their existing import paths (`MathProofs.<Module>`) so published references, audit scripts and downstream projects remain valid.

Add new proof modules to the master import tree when appropriate, assign them in `../catalog/topics.json` if not already covered by a prefix, regenerate the catalogue from `lean/`, and run the applicable Lean builds and axiom audits. Catalogue membership alone is not evidence of kernel verification.
