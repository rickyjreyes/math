# E26 — Conditional regularized-curvature \(L^2\) estimate

[PDF](paper.pdf) · [LaTeX](../../papers/regularized-curvature-l2-bound/main.tex)

Family: **F12** (E26; manuscript 2). This proof concerns the **historical additive-denominator operator**, distinct from the corrected phase-covariant M2/E17 regularization. For \(\psi\in H^2(\Omega;\mathbb C)\), the regularized curvature operator
\[
\Theta_\varepsilon[\psi]
=-\frac{\Delta\psi}{\psi+\varepsilon e^{-\alpha|\psi|^2}}
\]
obeys
\[
\|\Theta_\varepsilon[\psi]\|_{L^2}
\leq \delta^{-1}\|\Delta\psi\|_{L^2}
\]
**provided** the modulus of the entire denominator is at least \(\delta>0\) almost everywhere. The manuscript gives explicit sufficient conditions, and a smooth counterexample showing that \(\varepsilon>0\) by itself does not ensure the estimate for signed/complex fields.

**Status:** analytic proof under explicit hypothesis; not independently peer-reviewed. Lean-formalized in [RegularizedCurvatureL2](../../lean/MathProofs/RegularizedCurvatureL2.lean) (`ReyesMath.E26.e26`; see [lean/formalization.yaml](../../lean/formalization.yaml)): the theorem, both corollaries, the remark, the counterexample, the corrected-multiplier bound and the scope statement. The CI [build script](../../scripts/build_pdfs.sh) publishes the PDF on a successful main-branch run.
