import MathProofs.E69Certification

/-!
Reproducible dependency audit of the E69 certification (`MathProofs/E69Certification.lean`,
issue #40, manuscript `papers/high-regularity-bounded-curvature-e69/main.tex`). It covers every
declaration cited in `docs/E69_LEAN_MANUSCRIPT_MAPPING.md`. Each one must depend on no axioms
other than `propext`, `Classical.choice` and `Quot.sound`. Run
`lake env lean E69CertificationAudit.lean` after `lake build MathProofs.E69Certification`; the
focused workflow `.github/workflows/lean-e69.yml` does this on every pull request. This file adds
no declarations to the maintained library.
-/

-- The certification interface
#print axioms ReyesMath.E69Cert.reciprocal
#print axioms ReyesMath.E69Cert.sobolev_space
#print axioms ReyesMath.E69Cert.laplacian
#print axioms ReyesMath.E69Cert.fourier_inversion
#print axioms ReyesMath.E69Cert.embedding
#print axioms ReyesMath.E69Cert.main_theorem
#print axioms ReyesMath.E69Cert.remark_dimensions
#print axioms ReyesMath.E69Cert.remark_domains
#print axioms ReyesMath.E69Cert.remark_fixed_regularization
#print axioms ReyesMath.E69Cert.remark_regularizer
-- The Sobolev spaces H^s(ℝⁿ) of real order
#print axioms ReyesMath.E69.integrable_jw_neg
#print axioms ReyesMath.E69.integral_norm_sq
#print axioms ReyesMath.E69.memHs_zero
#print axioms ReyesMath.E69.hsNorm_zero
#print axioms ReyesMath.E69.MemHs.mono
#print axioms ReyesMath.E69.hsNorm_mono
#print axioms ReyesMath.E69.norm_le_hsNorm
#print axioms ReyesMath.E69.memHs_iff_memLp
#print axioms ReyesMath.E69.hsNorm_eq_norm_toLp
#print axioms ReyesMath.E69.MemHs.add
#print axioms ReyesMath.E69.MemHs.smul
#print axioms ReyesMath.E69.mem_Hs
#print axioms ReyesMath.E69.hsNorm_add_le
#print axioms ReyesMath.E69.hsNorm_smul
#print axioms ReyesMath.E69.hsNorm_eq_zero_iff
#print axioms ReyesMath.E69.integrable_jw_mul_schwartz
#print axioms ReyesMath.E69.memHs_toL2
-- The Laplacian
#print axioms ReyesMath.E69.FU_toL2
#print axioms ReyesMath.E69.FUS_lapS
#print axioms ReyesMath.E69.FU_lap
#print axioms ReyesMath.E69.lap_weight_le
#print axioms ReyesMath.E69.memHs_lap
#print axioms ReyesMath.E69.hsNorm_lap_le
#print axioms ReyesMath.E69.lap_toL2
#print axioms ReyesMath.E69.lap_toL2_ae
#print axioms ReyesMath.E69.inner_toL2_lap
#print axioms ReyesMath.E69.eq_lap_of_weak
#print axioms ReyesMath.E69.isWeakLaplacian_lap
-- Fourier inversion and the embedding H^r ↪ L^∞
#print axioms ReyesMath.E69.fourierL2_symm_eq
#print axioms ReyesMath.E69.fourier_dilF
#print axioms ReyesMath.E69.FU_symm_ae_eq
#print axioms ReyesMath.E69.fourierUinv_eq
#print axioms ReyesMath.E69.ae_eq_fourierUinv
#print axioms ReyesMath.E69.norm_fourierUinv_le
#print axioms ReyesMath.E69.continuous_fourierUinv
#print axioms ReyesMath.E69.Cemb_pos
#print axioms ReyesMath.E69.integrable_FU
#print axioms ReyesMath.E69.integral_norm_FU_le
#print axioms ReyesMath.E69.embedding
-- The reciprocal and Theorem E69
#print axioms ReyesMath.E69.denom_pos
#print axioms ReyesMath.E69.Rε_apply
#print axioms ReyesMath.E69.Rε_zero
#print axioms ReyesMath.E69.norm_Rε_le_Mea
#print axioms ReyesMath.E69.norm_Rε_regimes
#print axioms ReyesMath.E69.continuous_Rε
#print axioms ReyesMath.E69.Theta_congr_ae
#print axioms ReyesMath.E69.aestronglyMeasurable_Theta
#print axioms ReyesMath.E69.Cns_pos
#print axioms ReyesMath.E69.lap_linf
#print axioms ReyesMath.E69.e69
-- The remarks
#print axioms ReyesMath.E69.ofReal_le_eLpNorm_top
#print axioms ReyesMath.E69.not_memLp_top_of_unbounded
#print axioms ReyesMath.E69.thresholds
#print axioms ReyesMath.E69.h2_linf
#print axioms ReyesMath.E69.lap_add
#print axioms ReyesMath.E69.lap_smul
#print axioms ReyesMath.E69.memHs_resolv
#print axioms ReyesMath.E69.lap_resolv
#print axioms ReyesMath.E69.memLp_hsing
#print axioms ReyesMath.E69.hsing_large
#print axioms ReyesMath.E69.norm_Rε_ge
#print axioms ReyesMath.E69.h2_insufficient
#print axioms ReyesMath.E69.theta_bound_of_linf
#print axioms ReyesMath.E69.laplacian_norm_sq_sub
#print axioms ReyesMath.E69.lapS_qS
#print axioms ReyesMath.E69.norm_Rε_real_ge
#print axioms ReyesMath.E69.no_uniform_in_eps
#print axioms ReyesMath.E69.not_uniform_bound
#print axioms ReyesMath.E69.oldDen_zero_alpha
#print axioms ReyesMath.E69.oldDen_vanishes
#print axioms ReyesMath.E69.oldDen_inv_unbounded
-- The flat torus
#print axioms ReyesMath.E69Torus.summable_int_one_add_sq_rpow
#print axioms ReyesMath.E69Torus.prod_rpow_le_gen
#print axioms ReyesMath.E69Torus.summable_wt_rpow_neg
#print axioms ReyesMath.E69Torus.hsNormT_zero
#print axioms ReyesMath.E69Torus.MemHsT.mono
#print axioms ReyesMath.E69Torus.hsNormT_mono
#print axioms ReyesMath.E69Torus.coef_lapT
#print axioms ReyesMath.E69Torus.memHsT_lap
#print axioms ReyesMath.E69Torus.hsNormT_lap_le
#print axioms ReyesMath.E69Torus.summable_norm_coef
#print axioms ReyesMath.E69Torus.toLp_rep
#print axioms ReyesMath.E69Torus.ae_eq_rep
#print axioms ReyesMath.E69Torus.norm_rep_le
#print axioms ReyesMath.E69Torus.embeddingT
#print axioms ReyesMath.E69Torus.e69_torus
