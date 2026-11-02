# Research post graphics

Four conceptual scientific illustrations accompanying Richard J. Reyes's fourth-order cubic–quintic mathematical research.

**Evidence classification:** The PNG figures are schematic editorial illustrations, not numerical PDE solutions, numerical energy surfaces, computed trajectories, or physical experimental evidence. Mathematical claims must be interpreted within the hypotheses of the cited Lean declarations and manuscripts.

## Figures

| Figure | File | Supporting formalization |
| --- | --- | --- |
| Orbital stability | `orbital-stability.png` | [OrbitalStability.lean](../../../lean/MathProofs/OrbitalStability.lean) |
| Existence, strict binding and orbital stability | `existence-binding-stability.png` | [WholeSpaceMinimizers.lean](../../../lean/MathProofs/WholeSpaceMinimizers.lean), [StrictBinding.lean](../../../lean/MathProofs/StrictBinding.lean), [OrbitalStability.lean](../../../lean/MathProofs/OrbitalStability.lean) |
| Whole-space localization without a cavity | `wave-without-walls.png` | [WholeSpaceMinimizers.lean](../../../lean/MathProofs/WholeSpaceMinimizers.lean) |
| Strict binding | `strict-binding.png` | [StrictBinding.lean](../../../lean/MathProofs/StrictBinding.lean) |

The four image files are not present in this commit; this index records their planned filenames and proof correspondence without implying that they have already been uploaded.

## Mathematical scope

For the specified fourth-order focusing-cubic/defocusing-quintic variational model on `H²(ℝ²; ℂ)`, within its explicit mass and parameter range:

- **Existence:** constrained energy minimizers exist in unbounded two-dimensional space, with compactness of minimizing sequences modulo translations.
- **Strict binding:** `I(m) < I(μ) + I(m − μ)` for `0 < μ < m ≤ m_B`.
- **Orbital stability:** sufficiently near the full minimizing set, solutions stay near that set in `H²` for all time, under the specified global evolution.

These are mathematical results about the stated model, not a physical validation of Wave Confinement Theory. The graphics must not be presented as solver-produced output.
