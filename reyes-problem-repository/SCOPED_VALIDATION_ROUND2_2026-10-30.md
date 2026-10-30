# Targeted mathematical validation, round 2

**2026-10-30.** This report follows the merged [PR #69](https://github.com/rickyjreyes/math/pull/69) and the existing [round-one audit](SCOPED_VALIDATION_AND_PRIOR_ART_2026-10-30.md).

This round independently examined GC167, GC196, GC201, and GC278. It identifies **two substantive mathematical defects** (GC196, GC201) and gives complete elementary proofs for **two exact finite-dimensional models** (GC167, GC278). It is **not** a 236-item independent research-quality certification, and it does not change the original registry statuses.

| Entry | Before | Mathematical issue / result | After |
|---|---|---|---|
| GC196 | Claimed possible Q^(3/4) *upper* bound on fixed compact S³ | On compact S³ the Hodge inequality and Hopf integral give \(|Q|\le C E\), hence \(I_Q\ge c|Q|\); a global \(O(|Q|^{3/4})\) upper bound is impossible | Corrected large-Q growth question without a false upper exponent |
| GC201 | Full SO(3) conjugation equivariance on S³ and standard action on S² | q=1 is fixed in domain, while S² has no SO(3)-fixed point, so no equivariant maps exist | Restricted to an S¹ subgroup under which the Hopf map is actually equivariant |
| GC167 | Asked whether four intensity measurements identify C² vectors modulo phase | Four intensities recover zz* by the complex polarization identity; omission of **each** one admits explicit collision | Mathematically resolved as known phase-retrieval benchmark |
| GC278 | Asked whether passive no-reference optics can implement NAND, and reference-assisted case | No-reference 00 is impossible; with first row (2,-1,-1)/sqrt(6), a single reference and threshold 1/12 give NAND truth table exactly | Both finite idealized cases resolved |

## Verified external overlap

- R. S. Ward, *Hopf solitons on compact manifolds*, J. Math. Phys. 59, 022904 (2018), https://doi.org/10.1063/1.5006891 : compact domain features a **linear topological lower bound**, unlike the \(3/4\) noncompact scaling.
- A. Guerra, X. Lamy, K. Zemas, *Global Minimality of the Hopf Map in the Faddeev–Skyrme Model with Large Coupling Constant*, Commun. Math. Phys. 407, 171 (2026), https://doi.org/10.1007/s00220-026-05702-5 : charge-one Hopf minimization under stated coupling assumptions.
- W. D. Montgomery, *Phase retrieval and the polarization identity*, Opt. Lett. 2 (1978), 120–121, https://doi.org/10.1364/OL.2.000120 : classical interference phase retrieval.

## Publication implications

Problem **scoping** is complete (236/236 files), and [PR #69](https://github.com/rickyjreyes/math/pull/69) is merged. Independent mathematical checking is **partial**. Two scoped targets needed fundamental correction in this round, which demonstrates why completeness of file coverage cannot be treated as research novelty validation. GC167 and GC278 are known/elementary solved targets, suitable for Lean benchmarks, not unverified open conjectures. All further novelty assertions require matching each **exact** model to prior results.
