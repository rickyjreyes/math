import MathProofs.E68Certification

/-!
Reproducible dependency audit of the E68 certification (`MathProofs/E68Certification.lean`,
issue #41, manuscript `papers/localized-gradient-energy-e68/main.tex`). It covers every
declaration cited in `docs/E68_LEAN_MANUSCRIPT_MAPPING.md`. Each one must depend on no axioms
other than `propext`, `Classical.choice` and `Quot.sound`. Run
`lake env lean E68CertificationAudit.lean` after `lake build MathProofs.E68Certification`; the
focused workflow `.github/workflows/lean-e68.yml` does this on every pull request. This file adds
no declarations to the maintained library.
-/

-- The certification interface
#print axioms ReyesMath.E68Cert.bridge
#print axioms ReyesMath.E68Cert.classification
#print axioms ReyesMath.E68Cert.classification_center
#print axioms ReyesMath.E68Cert.classification_L2
#print axioms ReyesMath.E68Cert.dimension_two
#print axioms ReyesMath.E68Cert.dimension_one
#print axioms ReyesMath.E68Cert.singular_field
#print axioms ReyesMath.E68Cert.smooth_concentration
#print axioms ReyesMath.E68Cert.corrected
#print axioms ReyesMath.E68Cert.admissible
#print axioms ReyesMath.E68Cert.remark_3_3
#print axioms ReyesMath.E68Cert.sobolev_three
#print axioms ReyesMath.E68Cert.sobolev_four
#print axioms ReyesMath.E68Cert.h2_localized
#print axioms ReyesMath.E68Cert.h2_failure_smooth
#print axioms ReyesMath.E68Cert.h2_failure
#print axioms ReyesMath.E68Cert.h2_scaling
-- The Sobolev space H¹ and the classification
#print axioms ReyesMath.E68.IsH1.ae_eq_grad
#print axioms ReyesMath.E68.IsH1.congr_ae
#print axioms ReyesMath.E68.isH1_of_contDiff
#print axioms ReyesMath.E68.memH1_iff_exists_weakH1Field
#print axioms ReyesMath.E68.isH1_iff_isWeakDeriv
#print axioms ReyesMath.E68.isH1_of_H2
#print axioms ReyesMath.E68.IsH1.smul_test
#print axioms ReyesMath.E68.e68_iff_two
#print axioms ReyesMath.E68.e68Holds0_iff_two
#print axioms ReyesMath.E68.e68L2_iff_two
#print axioms ReyesMath.E68.e68_two
#print axioms ReyesMath.E68.not_e68_one
#print axioms ReyesMath.E68.not_e68_one_of_line
#print axioms ReyesMath.E68.not_e68_of_two_lt
-- Radial integration and the singular field
#print axioms ReyesMath.E68.integrable_fun_norm_of_integrableOn
#print axioms ReyesMath.E68.setIntegral_ball_rpow
#print axioms ReyesMath.E68.sphereArea_eq
#print axioms ReyesMath.E68.Singular.contDiffAt_psi
#print axioms ReyesMath.E68.Singular.gradient_psi_of_lt_one
#print axioms ReyesMath.E68.Singular.memLp_psi
#print axioms ReyesMath.E68.Singular.memLp_gradC
#print axioms ReyesMath.E68.Singular.weak_deriv
#print axioms ReyesMath.E68.Singular.isH1
#print axioms ReyesMath.E68.Singular.isH1_update
#print axioms ReyesMath.E68.Singular.integral_sq_ball_one
#print axioms ReyesMath.E68.Singular.integral_grad_sq_ball_one
#print axioms ReyesMath.E68.Singular.integral_grad_sq_ball_sphere
#print axioms ReyesMath.E68.Singular.blowup
#print axioms ReyesMath.E68.Singular.no_constant
#print axioms ReyesMath.E68.Singular.defeats_every_constant
#print axioms ReyesMath.E68.Singular.not_e68Holds0
#print axioms ReyesMath.E68.Singular.not_e68
-- E68′, Corollary 3.2, Remark 3.3
#print axioms ReyesMath.E68.eLpNorm_ball_le
#print axioms ReyesMath.E68.ball_energy_le
#print axioms ReyesMath.E68.e68_corrected
#print axioms ReyesMath.E68.e68_apriori
#print axioms ReyesMath.E68.e68_admissible
#print axioms ReyesMath.E68.no_apriori_bound_on_H1
-- The Sobolev embedding for weak H¹
#print axioms ReyesMath.E68.gradVec_conv
#print axioms ReyesMath.E68.eLpNorm_gradVec_conv_le
#print axioms ReyesMath.E68.gns_gradVec
#print axioms ReyesMath.E68.sobolev_of_hasCompactSupport
#print axioms ReyesMath.E68.sobolev_H1
#print axioms ReyesMath.E68.memLp_of_isH1
-- H²
#print axioms ReyesMath.E68.isH2_of_contDiff
#print axioms ReyesMath.E68.eLpNorm_three_le
#print axioms ReyesMath.E68.grad_bound_three
#print axioms ReyesMath.E68.grad_bound_four
#print axioms ReyesMath.E68.e68_H2
#print axioms ReyesMath.E68.integral_dilateH2_sq
#print axioms ReyesMath.E68.integral_gradVec_dilateH2_sq
#print axioms ReyesMath.E68.integral_hess_dilateH2_sq
#print axioms ReyesMath.E68.not_e68_H2_smooth
#print axioms ReyesMath.E68.not_e68_H2
