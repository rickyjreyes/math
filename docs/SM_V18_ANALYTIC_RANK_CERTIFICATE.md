# Exact analytic rank of the frozen v18 31-to-11 sensitivity map

**Status:** reproducible interval-arithmetic certificate and exact symbolic block
factorization; **not Lean-kernel formalized**. The input data are pinned to
[the frozen v18 source at commit 5a4c58a](https://github.com/rickyjreyes/geometry_of_resonance/blob/5a4c58a4206005ad9d46ee2951069186490b01f1/SM_Spectrum/_terms_perfection_v18.py).
The original [finite-difference audit](https://github.com/rickyjreyes/geometry_of_resonance/blob/5a4c58a4206005ad9d46ee2951069186490b01f1/SM_Spectrum/audit_v18_identifiability.py)
reported numerical rank 11; the present certificate uses **analytic derivatives**, not
finite-difference rank thresholds.

## Theorem (exact row rank on the frozen active branch)

Consider the continuous, piecewise-smooth real-coefficient v18 observation
map from 31 parameters to the 11 outputs with indices

- Light: `(1,2,3)` (the original zero target at `n=0` is excluded);
- Middle: `(12,19,53,73,91)`;
- Heavy: `(95,96,123)`.

Take exactly the 29 stored coefficient values in the pinned source and
the historically optimized suppression parameters, with
`5.172 ≤ alpha_decay ≤ 5.173` and `epsilon_cutoff = 5`.
On this parameter interval, all 11 active outputs are strictly above the
`1e-12` clipping floor. The exact real Jacobian has rank **11**, so its
kernel has dimension **20**. This proves local *linearized* nullity, not
global non-identifiability or predictive validity.

### Proof

Select the following 11 columns of the 31-dimensional Jacobian, in the
same order as the output blocks:

| Output block | Chosen parameters | Number |
| --- | --- | --- |
| Light | `m0`, `theta`, `gamma` | 3 |
| Middle | `offset`, `quad`, `amp`, `phase`, `harmonic` | 5 |
| Heavy | `boson_nonlin1_scale`, `wz_break_scale`, `higgs_offset` | 3 |

The 11×11 minor is block lower triangular: the light outputs depend on
light coefficients but not middle/heavy ones; middle outputs depend only on
middle coefficients; heavy outputs may additionally depend on light
coefficients but not middle ones. Hence its determinant is the product of
three diagonal-block determinants.

**Light block.** Put `D_n = (1 + exp(alpha_decay * (n-epsilon_cutoff)))^(-1)`,
which is strictly positive. The three analytic derivative rows are

`epsilon_n * D_n * (n/(n+1), n^2, n^3)`,

where `epsilon_1 = epsilon_2 = 1` and the frozen
`epsilon_3 = 0.0048`. Exact rational arithmetic yields

`det([(n/(n+1), n^2, n^3)]_(n=1,2,3)) = 9`.

Therefore `det(L) = 9 * 0.0048 * D_1 * D_2 * D_3 > 0`.

**Middle block.** Let `A=2241.1`, `s1=5.0632`, `s2=9.4062`,
`phase=1.6469`. The five analytic derivative rows are

`(1, n^2, sin(s1*n+phase), A*cos(s1*n+phase), sin(s2*n))`.

An outward-rounded interval determinant gives

`21,220,606.4210508780 < det(M) < 21,220,606.4210508781`.

**Heavy block.** Let `p=-1.189`, `angle=-1.264`, `phase=4.685`.
The three analytic derivative rows are

`((n/100)^p, 1_{n in {95,96}} sin(angle*n+phase), 1_{n=123})`.

An outward-rounded interval determinant gives

`1.2178964326641464 < det(H) < 1.2178964326641466`.

For the stated live-parameter interval, the full selected determinant
satisfies the strict enclosure

`1,116,446.29 < det(J_selected) < 1,116,446.38`.

It is nonzero; thus the 31-column Jacobian has rank at least 11. Since it
has only 11 rows, its rank is exactly 11. Rank–nullity gives
`31 − 11 = 20` kernel dimensions. QED.

## Reproduction and limitations

```bash
python -m pip install mpmath==1.3.0
python scripts/v18_analytic_rank_certificate.py \
  --source ../geometry_of_resonance/SM_Spectrum/_terms_perfection_v18.py
```

The `--source` verification checks the Git blob SHA of the historical
source, its stored coefficient arrays, its optimizer success and live-parameter
interval, the exact 11 output labels, and inactive clipping branches. Without
`--source`, the interval minor is checked against the documented frozen
constants but the source/optimizer link is explicitly unverified.

Interval arithmetic is implemented with `mpmath.iv`, not a Lean theorem prover.
The exact symbolic block decomposition and rational light determinant are
independent of the original finite-difference SVD. This result certifies the
**local derivative rank** of the *specified frozen empirical fit*. It does not
show that 20 different global parameter vectors give identical spectra, that
physical mass predictions generalize beyond the fitted indices, or that model
eigenmodes are independently identified.

**Lean status:** the general ≥20 nullity lemma in
`MathProofs/LocalIdentifiability.lean` is already kernel-checkable.
An exact Lean representation of the frozen real-valued model and certified
transcendental interval determinants is still required before setting F09
`main_theorem_formalized: true`.
