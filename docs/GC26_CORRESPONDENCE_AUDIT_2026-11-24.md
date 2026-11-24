# GC26 correspondence and scoped resolution audit (2026-11-24)

## Decision

The fixed exact-real 31-to-11 ambient model is **resolved negatively**: no parameter is locally identifiable, no fiber point is isolated, and global injectivity fails. The original GC26 wording in FORMAL_PROBLEMS.md leaves Theta and N unspecified, and calls the clipped model analytic; the actual map is continuous and piecewise analytic, not globally analytic across floors. No 31-coordinate optimizer box or arbitrary augmented observation family is supplied. Do not replace these unspecified hypotheses with invented ones.

The only historical specified constrained domain is alpha in [0,50], epsilon in [0,5], with all other 29 coefficients fixed. Its classification below is analytically complete; the essential scalar lemmas are kernel-verified, but the assembled relative-neighborhood equivalence is not an audited declaration. Thus the catalogue entry should be **partially_resolved**, with the ambient scope explicitly complete. #103 retains only the historical integrated theorem/correspondence and repository verification gate; generic component topology (#112) and observation-design work (#113, GC27) are separate extensions, not GC26 closure conditions. Do not reopen or duplicate F09 or its ambient proofs.

## Reproducible evidence

- Merged PR #105: https://github.com/rickyjreyes/math/pull/105
- Exact checked head: 1a57f380b5179423c165b22ba8c59f65493b91de; merge b3db95f021ca139999d494f602a6e89cac6ba17b.
- Owner-supplied Lean 4.23.0 Windows verification: https://github.com/rickyjreyes/math/pull/105#issuecomment-7127329594 . Focused lake build completed (7233 jobs); F09Audit printed all 45 roots (10 F09, 35 GC26), standard axioms only: propext, Classical.choice, Quot.sound. This is a documented local verification, not a new independent run.
- Hosted focused workflow run 45364011755 was queued at audit time. The workflow contract requires successful Lean CI and reviewed correspondence before whole-issue formal closure; do not invent a green hosted run.
- Source: lean/MathProofs/GC26GlobalIdentifiability.lean, lean/F09Audit.lean; F09 paper papers/sm-v18-local-identifiability-obstruction/main.tex. Original GC26 statement is preserved.

## Exact declaration correspondence

All names below are in ReyesMath.V18Forward.

| Acceptance claim | Declaration and exact scope |
|---|---|
| All-point non-isolation | observed_all_points_nonisolated: for every p and ambient neighborhood U, exists q in U, q != p and observed q = observed p |
| Global noninjectivity | observed_not_injective: not Function.Injective observed |
| Exact aliases | observed_update_quarkAmp, observed_update_quarkPower, observed_shiftHiggs, observed_invisibleFamily; independent family by invisibleFamily_injective |
| Unbounded fiber | observed_unbounded_coordinate_fiber: arbitrarily large coordinate 16 in every fiber |
| Relative non-isolation | observed_relative_nonisolated: conditional on arbitrarily close admissible changes of coordinate 16; not a universal result for every subset |
| Floor and nested floor | floor_eq_iff, nested_floor_eq_iff: exact scalar necessary and sufficient conditions |
| Generic full rank is insufficient | generic_rank_counterexample: x^2 has nonzero derivative off zero and colliding ±1; generic means open dense here |
| Rank obstruction | augmented_rank_obstruction: fewer than 31 rows force positive kernel dimension; topological injectivity bound is separate |
| Open plateau | observed_constant_near_plateau: eventually constant all-floor output in a neighborhood of plateauCenter |
| Global image | observed_range_exact: range is [10^-12,infinity)^11 |
| Canonical reduction | observed_canonicalInvisible, canonicalInvisible_zero_coords, invisible_reconstruct |
| Historical row reduction | historical_equal_iff_light, historical_heavy_constant, historical_heavy_light_floor |
| Historical logits and thresholds | historical_lightRaw, historical_numerator_bounds, historical_threshold_bounds, historical_light_active_iff, logistic_floor_logit_eq |
| Historical uniqueness and degeneracy | historical_two_active_unique, historical_zero_alpha |
| Historical interval geometry | historical_active_prefix, historical_one_active_interval, historical_exceptional_endpoint |

The rank counterexample can be lifted to the original input dimension by (x1,...,x31) -> (x1^2,x2,...,x31): rank 31 off x1=0, but not globally injective. This lifting is analytical, not a separate audited Lean declaration. For the actual model full column rank is impossible; full row rank occurs at the frozen vectors and is compatible with exact noninjectivity.

## Identifiability definitions and exact historical answer

In S with its subspace topology, global point identification means F^-1(F(p)) intersect S = {p}; local point identification means p is isolated in that fiber; neighborhood injectivity means a relative neighborhood of p has injective restriction. The latter implies local point identification but not necessarily global point identification. Global injectivity means all fibers are singletons. These notions must not be interchanged.

Let c=10^-12, a=alpha, t=a(1-epsilon), h_i=log(A_i/c-1) with A_i the exact fixed historical numerators. The rectangle becomes 0<=a<=50, -4a<=t<=a, with the entire a=0 edge represented by (0,0). The audited threshold bounds imply 0<h3<h1<h2<40 and h1>20. The eleven-output equality reduces to three light outputs max(A_i/(1+exp((i-1)a+t)),c); active rows form prefixes.

- a>0 and a+t<h2: rows 1 and 2 strictly active, hence globally unique in the historical rectangle and relatively neighborhood-injective. Two logits give t and a, and epsilon=1-t/a. These strict inequalities are relatively open, so the conclusion holds even at the rectangle's boundary.
- a=0: fiber is exactly the entire epsilon edge. The two active logits force any competitor to have a=0. Neither isolated nor neighborhood-injective.
- t<h1 and a+t>=h2: only row 1 active. Fix t; the fiber is a segment in a from max(0,t,-t/4,h2-t) to 50. Since t<h1<h2, the lower endpoint is positive. The exceptional singleton is exactly t=h2-50, a=50, epsilon=2-h2/50. All other such points have non-isolated fibers. No point of this stratum is relatively neighborhood-injective: interpolate its (a,t) with (49,0), a strict interior one-active point; arbitrarily close points in the stratum admit a nontrivial constant-t segment. This argument includes the exceptional singleton.
- t>=h1: all rows floored, the fiber is the entire polygon with t>=h1, 0<=a<=50, -4a<=t<=a. Interpolation toward (49,48) yields distinct arbitrarily close points except at that point, which itself lies in the interior. No isolated fiber or relative neighborhood injectivity.

Thus relative neighborhood injectivity iff a>0 and a(2-epsilon)<h2. Singleton (equivalently isolated) fibers iff that condition holds OR (a,epsilon)=(50,2-h2/50). The exceptional point is a model-specific example where local point identification does not imply neighborhood injectivity. This paragraph assembles already verified roots analytically; do not label the assembled theorem kernel-checked.

## Further explicit constrained domain (analytical)

For any fixed values of the other 27 coordinates, allow only p16,p18,p27,p28 to vary over closed finite nonempty intervals. Write u=p27, v=p28, k=123/124, and let K be the fixed part of the final heavy raw output after its inner light floor. The first ten outputs are constant and the last is max(K+ku+v,c). Hence every fiber is the product of the two entire unused-coordinate intervals and the intersection of the Higgs rectangle with ku+v=y-K if y>c or ku+v<=c-K if y=c.

If either unused interval is nondegenerate, no point is isolated, including endpoints. With both fixed and both Higgs intervals nondegenerate, an above-floor fiber is a singleton exactly at the minimum and maximum corners of ku+v. A floor fiber is a singleton exactly when c-K equals the minimum of ku+v; it is empty when strictly below that minimum. All other nonempty fibers are non-isolated (convex segments or polygons). No neighborhood injectivity on this two-dimensional rectangle, including corners, since each relative neighborhood contains a nonempty open rectangle and a continuous scalar map cannot inject that rectangle into R.

If both unused intervals are singleton and exactly one Higgs interval is nondegenerate, write s for its coordinate, w>0 for its slope, B for the fixed offset, s in [l,r]. F is relatively neighborhood-injective at s if B+ws>c, or at s=l with B+wl=c. The above-floor fibers are singleton; the floor fiber is singleton iff c=B+wl, and otherwise any nonempty floor fiber is a nondegenerate initial interval. When both Higgs intervals are singleton the whole domain is a singleton. This is an explicit mathematical prior, not a claim about a historical physical parameter box.

## Quotient and augmentation

Q sets coordinates 16,18,27 to zero and sends coordinate 28 to p28+(123/124)p27. Its kernel is the three-dimensional invisible direction subspace. The checked reconstruction and affine continuity identify R^31 with the canonical slice times R^3, and each fiber with its slice fiber times R^3. The quotient by this subspace is R^28; it is not the entire observation quotient because further aliases remain. This topological conclusion is analytical.

For any specified S and extra observation map G, (F,G) is injective on S iff G is injective on each F-fiber intersect S. Necessity and sufficiency follow directly by comparing equal ordered pairs. A continuous augmentation on an ambient open set needs total output dimension >=31 (invariance of domain); at the frozen rank-11 point, appending the 20 complementary coordinate projections gives an invertible augmented derivative and local injectivity. The open all-floor plateau forces at least 31 *additional* continuous scalar outputs for global ambient injectivity, sharp if arbitrary coordinate measurements are allowed. These dimension and sufficiency arguments are analytical; the derivative obstruction and plateau are audited. No guarantee for unspecified physical observations.

Generic disconnectedness is a distinct topology theorem; #112 records the existing proof strategy and exact limitations. Arbitrary additional priors or measurements require explicitly frozen domains and are tracked in #113. They do not change the already answered ambient question.

## Acceptance and limitations

The original fixed ambient model has a rigorous negative answer, independent of rank, floor or boundary branch. The only specifically documented historical prior has an exact analytical classification supported by verified scalar roots. The formal catalogue remains partial until its constrained-domain correspondence is accepted under the existing workflow. No novelty, physical spectrum validation, new Lean execution, or full CI success claimed. This audit preserves the original GC26 question and does not add arbitrary domains, global component enumeration or sensor-design requirements to it.
