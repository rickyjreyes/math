# GC06 / GC16 / GC26: closure audit and direct equality-pair reduction

Date: 2026-11-24. This document distinguishes an analytical proof, a candidate Lean implementation, a locally checked theorem, and a fully accepted GC record. The frozen statements in FORMAL_PROBLEMS.md are unchanged. No novelty claim.

## GC06 and GC16: exact domain and dependency simplification

Original F01 model: complex H^2(R^2), real k, beta,gamma>0, M(u)=||u||_2^2=m>0, E=T-beta Q/2+gamma S/3, T=||(Delta+k²)u||_2², Q=||u||_4^4, S=||u||_6^6, I(m)=inf E on the mass shell. GC16 seeks strict subadditivity for every positive split; GC06 seeks attainment and characterization of loss of compactness. GC01 minimizing-set stability follows from strict binding and existing global flow/conservation, but this does not settle individual or excited-state stability.

### 1. Ordinary subadditivity

For arbitrary f,z in L²(R²), translations of f by y_n with |y_n| tending to infinity tend weakly to zero. Proof: approximate f,z in L² by compactly supported continuous functions F,Z. Their inner product after a sufficiently large translation is exactly zero. Unitary translation and Cauchy–Schwarz bound the original inner product by ||z-Z|| ||F||+||z|| ||f-F||, uniformly in n; take approximation error to zero.

For U,V in H² of positive masses a,b, take W_n=U+V(.+y_n). The val and lap components converge weakly to U, and W_n is bounded in H². The merged mass and energy splitting lemmas therefore give M(W_n)→a+b and E(W_n)→E(U)+E(V). The merged mass-correction lemma gives I(a+b)≤lim E(W_n). Taking approximate minimizers at a and b proves ordinary subadditivity for every positive split. This does not assume strict binding, attained infima, or existence of compactly supported minimizing fields.

### 2. One attained subprofile at every positive mass

Fix m>0. Negativity, coercivity, local nonvanishing and weak profile extraction are already established in WholeSpaceMinimizers. For a translated minimizing sequence W_n, extract a nonzero weak profile U at mass x>0. Hilbert splitting implies x≤m. For x<m, let V_n=W_n-U; then M(V_n)→m-x>0 and the exact mass-correction lemma gives liminf E(V_n)≥I(m-x). Energy splitting gives
I(m)≥E(U)+I(m-x)≥I(x)+I(m-x)≥I(m).
All inequalities are equalities, so U is attained at x and the x,m-x split saturates ordinary subadditivity. If x=m, the residual has vanishing mass and bounded H², hence Q,S→0 and liminf E(V_n)≥0. Again U attains I(m).

Only a single weak profile is needed; no termination of a multi-cluster algorithm is required for this result.

### 3. Two profiles suffice

Suppose strict binding fails at m=a+b, a,b>0. Ordinary subadditivity gives I(m)=I(a)+I(b). Apply section 2 independently to minimizing sequences at a and b, producing U,V with masses x≤a, y≤b, both positive and both attained. Each side splits exactly into its attained subprofile and residual infimum, if that residual mass is positive. Subadditivity gives
I(m)≤I(x+y)+I(a-x)+I(b-y)≤I(x)+I(y)+I(a-x)+I(b-y)=I(m).
Omit terms with zero residual (or handle the four cases separately); no definition of I(0) is needed. Therefore I(x+y)=I(x)+I(y). Conversely, an attained equality pair directly violates strict binding. This proves equivalence between universal binding and nonexistence of an attained equality pair, with no finite-cluster hypothesis.

In particular, the all-mass analytical argument in GC06_ALL_MASS_SPECTRAL_MERGING_2026-11-24.md can replace its section 6 reduction by this direct proof. If its spectral exclusion of attained equality pairs is valid, universal binding follows, then full attainment and compactness of all minimizing sequences. In that case the noncompact cluster classification is vacuous on the positive-coefficient domain. If binding fails, the exact classification of compactness failures and the separate finite-cluster theorem remain relevant; they are not presumed kernel-checked.

### 4. Exact Lean implementation boundary

New candidate module MathProofs.GC06PairExtraction:

- weak_translate_zero, exists_weak_translates: L² translation limit from compact-support approximation.
- pair_upper_of_weak_translates, subadditive_of_weak_translates, ordinary_subadditive: original infimum, no altered energy.
- attained_profile_of_weak, exists_attained_submass, equality_of_subprofiles, pair_of_failed_split, exact_pair_of_failed_split: two-profile reduction, using the merged profile, mass-correction and Brezis–Lieb infrastructure.
- binding_of_spectral_exclusion, confinement_of_spectral_exclusion, compactness_of_spectral_exclusion, stability_of_spectral_exclusion: consequences with ordinary subadditivity explicit.
- all_binding_iff_no_equality_pair, all_mass_confinement_of_no_equality_pair, all_mass_compactness_of_no_equality_pair, all_mass_stability_of_no_equality_pair: ordinary subadditivity discharged by the new proof; only spectral pair exclusion remains an explicit substantive hypothesis.

The integrated audit contains 44 roots (26 earlier owner-verified plus 18 candidates). No new local kernel success is asserted. The actual all-mass theorem is not claimed compiled because NoEqualityPair remains a hypothesis of the last three consequences.

## 5. Independent analytical correspondence check of the spectral route

The following is a source/argument audit, not independent referee acceptance of the entire continuum theorem.

- The threshold test requires a real constrained Hessian of E-lambda M on the exact H² mass tangent space. At lambda=0 and k≠0, high angular Bessel Helmholtz modes have exterior negative potential contribution dominating the positive bounded core. The cutoff annulus kinetic cost tends to zero for each fixed angular index. The order of limits (angular index fixed first, cutoff radius tending to infinity second) is essential. Multiplication by a global phase enforces the real mass tangent condition without altering the sign bound. The full PDE and Hessian derivation must still be formalized.
- Negative lambda is the bottom-of-spectrum gap needed for the shifted resolvent. With tau=sqrt(-lambda), the characteristic polynomial is (z·z-k²)^2+tau²; the two disjoint smooth complex quadrics have minimal imaginary distance alpha>0. The K0 resolvent bounds and truncated exponential weights justify decay at each q<alpha; no decay beyond the characteristic tube is assumed.
- The noncancellation argument invokes Herbst–Skibsted, *Decay of eigenfunctions of elliptic PDE's*, 2013 preprint Theorem 1.4, https://data.math.au.dk/publications/pp/2013/math-pp-2013-03.pdf (printed page 3), also https://arxiv.org/abs/1306.6878v1. I checked the actual theorem text and page. The degree-four real elliptic Q and V1=0 satisfy the polynomial-symbol and differentiated-potential hypotheses. V2=-beta|u|²+gamma|u|⁴ decays exponentially by the preceding estimate and hence satisfies the required O(|x|^(-2-delta)) bound for any delta>0. A nonzero eigenfunction therefore cannot have infinite exponential L² decay rate. This is a valid external analytical input at the stated scope, not an in-repository Lean theorem. Published reference: Advances in Mathematics 270 (2015), 138–180, doi:10.1016/j.aim.2014.11.001 (correct the earlier endpoint 170).
- Holomorphic division by the two simple characteristic factors must be justified on the connected tube intersections; use w=z1+i z2 with w nonzero and v=s/w. If both minimal-circle source traces vanish, the one-variable identity theorem gives cancellation on both entire intersections, hence division and a larger holomorphic tube; Fourier inversion iterates the decay. The external spectral theorem rules out all-rate decay. This is the indispensable remaining noncancellation step.
- Pairwise rotation/conjugation aligns nonzero source traces at a common complex characteristic point. The shifted action is expanded with shared multiplier; the leading interaction survives with coefficient 2 Re(e^{i theta}B), while all terms of mixed degree at least two in each field are O(e^{-2q|y|}). Exact mass correction contributes only the same second-order error because both individual amplitude derivatives vanish. Equality would bound |B| by that error, which forces an impossible holomorphic Fourier continuation across the noncancelled pole. The correct phase is allowed by the original complex H² model. The interaction must be checked on exactly normalized trial fields and all constants uniform in phase.

Remaining formal work is the continuum Lagrange multiplier and Hessian, threshold Bessel/cutoff estimate, weighted resolvent, holomorphic tube and source noncancellation (including a formal proof of the cited external theorem or a replacement), and phase-interaction estimate. Do not introduce these results as custom axioms. The present proof chain has one named unresolved target, not a claim that all its underlying analysis is already formalized.

Related literature comparison already cited in the strict-binding manuscript: Fernández–Jeanjean–Mandel–Mariș, JDE 330 (2022), 1–65; Ma–Chang–Feng, EJDE 2024 no.29, 1–20. Compare the exact focusing/defocusing competing powers, negative second-order dispersion coefficient, complex H² and all-mass scope before making a novelty claim; these prior citations alone do not establish novelty.

## 6. GC26 specified-domain correspondence and acceptance

The original GC26 asks local injectivity for the fixed clipped spectral map and whether generic full rank implies global injectivity. Its wording leaves Theta and N unspecified; the exact model fixes R³¹→R¹¹ (continuous, piecewise analytic), and the historical constrained domain fixes the alpha/epsilon rectangle with the other 29 parameters frozen. Do not silently enlarge the problem to arbitrary physical sensor maps.

- Merged #105, exact head 1a57f380b5179423c165b22ba8c59f65493b91de: observed_all_points_nonisolated, observed_not_injective and generic_rank_counterexample. Every ambient point has another point of equal output in every neighborhood, implying no local neighborhood injectivity; generic nonzero derivative of x² away from zero does not imply global injectivity. The example lifts analytically to dimension 31 by adding identity coordinates. The actual observation map cannot have full column rank.
- Merged #117, exact head 0974c5d677c2769b95666e18e41a118890181aee: historical_complete_classification and historical_exceptional_not_neighborhood_injective. This gives all three identification notions, all boundary strata and the exceptional singleton. The owner-supplied exact-head record reports a 7,234-job successful build and 57 audited roots (10 F09, 35 earlier GC26, 12 historical); all use only standard axioms. Evidence: https://github.com/rickyjreyes/math/pull/117#issuecomment-7129133692.
- Original issue https://github.com/rickyjreyes/math/issues/103 is closed. #112 and #113 are explicitly separate extensions; neither changes the original problem.
- The existing successful local verification is adequate to credit the original specified-domain mathematical and local-kernel accomplishment. The workflow additionally requires a successful hosted Lean CI run and reviewed correspondence for accepted completion_records.json. Exact-head F09 run https://github.com/rickyjreyes/math/actions/runs/45376758923 was queued at inspection; full Lean checks were pending/queued. Do not manufacture a successful URL/conclusion. The current status remains partially_resolved pending this procedural gate; no remaining mathematical classification on the specified domains is required.
- Do not add a completion record, promote to fully resolved, or reopen #103 for unrelated extensions until the actual acceptance evidence is available. The pending evidence record is separate from the accepted index. This preserves the existing verification contract without moving the mathematical goalpost.

## 7. Issue closure boundaries

GC06 #55 is a narrower research milestone; #81 requires exact encoded parameter regions, endpoints, exclusion scope and frozen D4 correspondence. Their prior local proofs deserve credit and are documented in the ledger. Final issue closure must follow their existing acceptance criteria, not merely the 44-root candidate build or the analytical all-mass claim. GC16's all-mass theorem shares the same NoEqualityPair obligation; no duplicate problem is created. GC26 #103 is already closed. No pending issue or accepted record is artificially closed here.
