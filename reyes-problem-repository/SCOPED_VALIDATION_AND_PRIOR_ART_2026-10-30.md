# Mathematical cross-check and prior-art screen for scoped GC65–GC300

**2026-10-30 | review record v1.** This is an internal, reproducible verification and literature triage, **not external peer review and not 236 independently proved problems**. It documents which exact claims have been checked, which remain candidate specifications, and why the catalogue can be published as *problems for review* but not as a list of established unsolved conjectures. The scoped file index and registry checker cover all 236 entries.

## Re-derived mathematical conclusions (specific models only)

| GC | Re-check | Outcome | Scope of certificate |
|---|---|---|---|
| GC200 | For S¹ maps on a rectangular torus in winding class (m,n), write the phase differential as \(2\pi(m/L_x,n/L_y)+\nabla f\), where f is periodic. Cross terms integrate to zero, so \(E=2\pi^2(m^2L_y/L_x+n^2L_x/L_y)+\frac12\int|\nabla f|^2\). | **Established exact minimum** and minimizers unique modulo constant phase. | Classical analytic argument, not new and not Lean-checked here. |
| GC197 | A smooth homotopy for which y remains a regular value induces a compact smooth inverse-image cobordism whose projection to the time interval has no critical points; regular-value links are carried by an isotopy. | Non-isotopic regular-value preimage links **obstruct** the restricted homotopy, although equal Hopf integers imply ordinary homotopy. | Necessary obstruction; not a complete knot/framing classification. |
| GC212 | Each sample path continuous in \(C(S^3,S^2)\) is literally a homotopy. | Its Hopf integer is constant at every time along that path. | Known topology; no stochastic-PDE continuity theorem proved. |
| GC233 | The previous connected unweighted \(\lambda_2\) gap had only the high branch due to Fiedler's lower bound. The revised gap \(20/n^2\) versus \(80/n^2\) with n≥5 has witnesses P₅ and K₅: \(\lambda_2(P_5)=(3-\sqrt5)/2<20/25\), \(\lambda_2(K_5)=5>80/25\). | **Both revised promise cases exist.** | Nonvacuity and explicit eigenvalues, not a complexity lower bound. |
| GC277 | For phase difference errors at most \(2\varepsilon\), correct parity has intensity ≤\(\sin^2\varepsilon\), wrong parity ≥\(\cos^2\varepsilon\). With decoded 1 iff signal \(>1/2\), robust XOR follows from \(\sin^2\varepsilon+\delta<1/2\). | Exact **sufficient worst-case noise margin** within the model. | Idealized phase and detector law only. |
| GC278 | The passive unitary network sends vacuum inputs z=0 to zero output amplitude. Threshold \(|(Uz)_1|^2>\tau\) with \(\tau\ge0\) returns 0 on input 00, but NAND(0,0)=1. | **No-reference NAND impossible** in the stated class. | Reference-assisted variant not settled by this argument. |
| GC299 | A zero-temperature amplitude-damping channel discards a present photon with probability q. Equally likely vacuum/one-photon input gives wrong reset probability (1−q)/2. | \(q\ge1-2p\) and mean emitted photons \(q/2\) for this restricted model. | Does not derive universal thermodynamic photon-loss bounds. |
| GC242 | At \((\omega,u)=(1,1)\), \(F=(\Delta+1)^2u-u^3+u^5-\omega u\) vanishes; its u-derivative has Fourier symbol \((1-|k|^2)^2+1\ge1\). | Base point and linear invertibility are valid. | Banach-space C¹ implicit-function and a Lean proof remain separate tasks. |

## Defects detected and disposition

1. **GC233 (blocking, corrected on the branch):** previous connected-unweighted promise was tautological. The revised `n≥5` thresholds admit both branches, as explicitly checked above.
2. **GC191 (blocking, corrected on the branch):** \(u_t=u-(1+\Delta)^2u-u^3\) has **positive** linear growth on \(|k|=1\); the corrected critical flow is \(u_t=-(1+\Delta)^2u-u^3\).
3. **GC221 (clarified on the branch):** an exact-prefix oracle reveals the T+1-st bit of the doubling-map decision with p=T+1. An approximate-real oracle needs a margin promise; these two data models must not be conflated.
4. **GC172 (clarified on the branch):** a mode observer cannot use an unmeasured true cubic residual as a closed implementation. The corrected observer uses its own estimated modes and explicit residual terms.
5. **GC160 (source-path check):** the actual Lean definition lives in `lean/MathProofs/V18FullForward.lean`, **not** `V18Forward.lean`. The 20-dimensional fiber result is in `lean/MathProofs/V18Identifiability.lean`. Correct the broken source pointer before release.
6. **GC189 (pending):** on an infinite cylinder stripe bulk energies diverge, so define an energy *density on finite truncations* and a finite renormalized limit. The variable-coefficient Euler–Lagrange operator is \((\Delta+k^2)^*(\Delta+k^2)\), including k derivatives, rather than the naive fourth-order constant-coefficient formula.

## Focused published-literature comparison

| GC family | Source and exact overlap | Classification |
|---|---|---|
| GC196 / GC198 / GC206 | A. Guerra, X. Lamy, K. Zemas, *Global Minimality of the Hopf Map in the Faddeev–Skyrme Model with Large Coupling Constant*, *Communications in Mathematical Physics* 407, 171 (2026), https://doi.org/10.1007/s00220-026-05702-5 . This proves a Hopf-map minimization/uniqueness result for specified geometry and coupling. | **Prior theorem, exact parameter comparison required.** Do not imply every Hopf minimization problem is novel. |
| GC197 / GC203 / GC209 / GC212 | Classical \(\pi_3(S^2)\cong\mathbb Z\), the Hopf invariant and homotopy invariance. See A. Hatcher-related homotopy treatment, https://virtualmath1.stanford.edu/~ralph/bookR3.pdf (Hopf fibration calculation), and the references therein. | **Classical foundation;** restricted regular-value isotopy and dynamical control are separately framed targets. |
| GC167 | W. D. Montgomery, *Phase retrieval and the polarization identity*, *Optics Letters* 2, 120–121 (1978), https://doi.org/10.1364/OL.2.000120 . | **Classical interference/phase-retrieval technique;** a particular minimal measurement theorem requires exact comparison. |
| GC233 | B. Mohar, *The Laplacian Spectrum of Graphs*, §6, https://www.sfu.ca/~mohar/Papers/Spec.pdf , records Fiedler's lower bound \(\lambda_2\ge2\eta(G)(1-\cos(\pi/n))\). | **Known graph spectral bounds;** the weighted promise decision is a computation benchmark unless strengthened. |
| GC234 / GC299 | P. Faist et al., *The minimal work cost of information processing*, *Nature Communications* 6, 7669 (2015), https://doi.org/10.1038/ncomms8669 . | **Established thermodynamic information-work framework;** don't claim a new universal reset bound. |
| GC205 | Su–Schrieffer–Heeger chiral chain and bulk–boundary zero-mode correspondence are standard models. | **Established baseline;** novelty would require a precise new defect class or result, with dedicated literature search. |
| GC235 / GC247 / GC252 | Fourier–Plancherel, unitarity of complete wave operators, and LaSalle convergence under compactness are classical. | **Known mathematics, possible valuable Lean formalization**, not newly open mathematical conjectures. |
| GC160 / GC165 / GC246 | Exact existing `V18FullForward.lean`, `V18Rank.lean`, `V18Identifiability.lean` and accompanying F09 manuscript in this repository. | **Existing project results;** only stronger rank-strata or clipping boundary questions remain research candidates. |

## Honest release classifications

- **236/236:** a candidate scoped file exists, with an index and structural validator.
- **Selected explicit claims above:** analytic cross-checks provided, and defects disclosed.
- **All 236 mathematically certified:** **NO**. A syntax/inventory CI check is not a domain, topology, existence, nonvacuity, theorem or Lean proof audit.
- **All 236 novel and not already solved:** **NO**. The table contains affirmative evidence of substantial classical/prior-art overlap. A per-claim specialist literature search remains necessary.
- **Permissible public wording:** '236 scoped research candidates and formalization targets for review' or 'a mathematical challenge repository under active verification', **not** '236 verified unsolved novel problems'.

Keep this record with any merge; do not promote registry statuses without claim-specific supporting evidence.
