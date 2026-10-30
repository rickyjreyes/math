# Frozen model conventions, version 1
These conventions are mathematical definitions, not existence or novelty claims. Each GC scope file further restricts the model. An existential claim about a state does **not** silently assume that state exists.

## W: fourth-order cubic–quintic Schrödinger flow
On \(\mathbb R^2\), \(u:\mathbb R\times\mathbb R^2\to\mathbb C\), set
\[
i\partial_tu=(\Delta+1)^2u-|u|^2u+|u|^4u.\tag{W}
\]
Initial data lie in \(H^2(\mathbb R^2;\mathbb C)\). Whenever global flow is requested, existence on the stated time interval must be proved or separately assumed as part of the proposition. Set
\[
M(u)=\int|u|^2,\quad E_W(u)=\int\left(|(\Delta+1)u|^2-\frac12|u|^4+\frac13|u|^6\right).
\]
The symmetry group \(G=\mathbb R^2\times S^1\) acts by translation and constant phase. Distances to standing-wave orbits use the \(H^2\) norm.
A standing wave \(u(t)=e^{-i\omega t}\phi\) must satisfy
\[
F_\omega(\phi):=(\Delta+1)^2\phi-|\phi|^2\phi+|\phi|^4\phi-\omega\phi=0
\]
in \(L^2\), with \(\phi\in H^4\), \(\omega\in\mathbb R\).
For real \(\phi\), the real Hessian blocks are
\(L_+=(\Delta+1)^2-3\phi^2+5\phi^4-\omega\) and
\(L_-=(\Delta+1)^2-\phi^2+\phi^4-\omega\), acting on \(L^2\) with domain \(H^4\). Let \(\mathcal A_\phi=J\operatorname{diag}(L_+,L_-)\), \(J=\begin{psmallmatrix}0&1\\-1&0\end{psmallmatrix}\).

## K: regularized phase curvature and constrained energy
For \(d=2\), \(\varepsilon>0\), and \(u\in H^2(\mathbb R^2;\mathbb C)\), set
\[
j(u)=\operatorname{Im}(\bar u\nabla u),\quad K_\varepsilon(u)=\nabla\cdot\frac{j(u)}{\varepsilon+|u|^2}.
\]
Derivatives are distributional, with \(K_\varepsilon(u)\in L^2\) for the specified \(H^2\) class. Define \(E_{\alpha,\varepsilon}(u)=E_W(u)+\alpha\int|K_\varepsilon(u)|^2\) for \(\alpha\ge0\). Do **not** conflate \(\operatorname{div}(j/(\varepsilon+|u|^2))\) with its curl: these detect different vortex effects.

## S: fourth-order spectral operator
On \(L^2(\mathbb R^2)\), take \(H_V=(\Delta+1)^2+V\), domain \(H^4\), where \(V\in L^\infty(\mathbb R^2;\mathbb R)\) and is specified per problem. With \(V\) decaying, the reference essential spectrum is \([0,\infty)\). Whenever a threshold resonance is mentioned, a weighted-space definition must be given in the scope file.

## Decision and evidence standard
A well-defined question may have an answer already known in the literature or a negative answer. **Well-defined does not mean open.** Each file freezes a concrete binary existence, classification, or quantitative target, defines a decisive negative case, and requires separate prior-art comparison before labelling it an open problem. The original GC candidate texts are preserved unchanged.
