import MathProofs.E18Certification

/-!
Reproducible dependency audit of the E18 certification (`MathProofs/E18Certification.lean`,
issue #37, manuscript `papers/wct-e18-exact-gradient-lyapunov/main.tex`). It covers every
declaration of the fourteen E18 modules, in particular every declaration cited in
`docs/E18_LEAN_MANUSCRIPT_MAPPING.md`. Each one must depend on no axioms other than `propext`,
`Classical.choice` and `Quot.sound`. Run `lake env lean E18CertificationAudit.lean` after
`lake build MathProofs.E18Certification`; the focused workflow `.github/workflows/lean-e18.yml`
does this on every pull request. This file adds no declarations to the maintained library.
-/

-- The certification interface (`MathProofs/E18Certification.lean`)
#print axioms ReyesMath.E18Cert.weight
#print axioms ReyesMath.E18Cert.energy_well_defined
#print axioms ReyesMath.E18Cert.frechet
#print axioms ReyesMath.E18Cert.variation
#print axioms ReyesMath.E18Cert.main_theorem
#print axioms ReyesMath.E18Cert.main_theorem_H2
#print axioms ReyesMath.E18Cert.zero_dissipation
#print axioms ReyesMath.E18Cert.finite_dissipation
#print axioms ReyesMath.E18Cert.remark_factor_two
#print axioms ReyesMath.E18Cert.remark_arbitrary_evolution
#print axioms ReyesMath.E18Cert.remark_degenerate_weight
#print axioms ReyesMath.E18Cert.remark_classical_derivatives
-- The weight and the energy on the Fourier H² model (`MathProofs/E18FourierEnergy.lean`)
#print axioms ReyesMath.E18FourierEnergy.D
#print axioms ReyesMath.E18FourierEnergy.F
#print axioms ReyesMath.E18FourierEnergy.D_pos
#print axioms ReyesMath.E18FourierEnergy.F_nonneg
#print axioms ReyesMath.E18FourierEnergy.energy
#print axioms ReyesMath.E18FourierEnergy.curvature_integrable
#print axioms ReyesMath.E18FourierEnergy.energy_nonneg
-- The exact derivative F′ (`MathProofs/E18WeightDerivative.lean`)
#print axioms ReyesMath.E18WeightDerivative.Dprime
#print axioms ReyesMath.E18WeightDerivative.Fprime
#print axioms ReyesMath.E18WeightDerivative.D_hasDerivAt
#print axioms ReyesMath.E18WeightDerivative.FprimeRaw
#print axioms ReyesMath.E18WeightDerivative.F_hasDerivAt_raw
#print axioms ReyesMath.E18WeightDerivative.FprimeRaw_eq
#print axioms ReyesMath.E18WeightDerivative.F_hasDerivAt
-- The exact six-term variation algebra (`MathProofs/E18VariationAlgebra.lean`)
#print axioms ReyesMath.E18VariationAlgebra.norm_sq_add
#print axioms ReyesMath.E18VariationAlgebra.density_remainder
#print axioms ReyesMath.E18VariationAlgebra.laplacian_density_remainder
#print axioms ReyesMath.E18VariationAlgebra.weighted_laplacian_remainder
-- The gradient-energy chain rule (`MathProofs/E18EnergyGradient.lean`)
#print axioms ReyesMath.E18EnergyGradient.gradientEnergy
#print axioms ReyesMath.E18EnergyGradient.hasDerivWithinAt_gradientEnergy
-- The chain rule and the rate reduction (`MathProofs/E18FlowChainRule.lean`)
#print axioms ReyesMath.E18FlowChainRule.hasDerivWithinAt_actual_energy
#print axioms ReyesMath.E18FlowChainRule.hasDerivWithinAt_actual_negative_gradient
#print axioms ReyesMath.E18FlowChainRule.zero_dissipation_iff_stationary
#print axioms ReyesMath.E18FlowChainRule.stationary_iff_zero_velocity
-- The integrated balance reduction (`MathProofs/E18IntegratedBalance.lean`)
#print axioms ReyesMath.E18IntegratedBalance.actual_energy_balance
#print axioms ReyesMath.E18IntegratedBalance.finite_interval_dissipation_bound
-- Bounds, smoothness and Taylor estimates of the weight (`MathProofs/E18WeightBounds.lean`)
#print axioms ReyesMath.E18.Fsecond
#print axioms ReyesMath.E18.Mw
#print axioms ReyesMath.E18.F_zero
#print axioms ReyesMath.E18.continuous_D
#print axioms ReyesMath.E18.contDiff_D
#print axioms ReyesMath.E18.F_norm_sq
#print axioms ReyesMath.E18.F_le
#print axioms ReyesMath.E18.Uw
#print axioms ReyesMath.E18.isOpen_Uw
#print axioms ReyesMath.E18.mem_Uw
#print axioms ReyesMath.E18.Fprime_eq_quotient
#print axioms ReyesMath.E18.F_hasDerivAt_of_ne
#print axioms ReyesMath.E18.continuousOn_F
#print axioms ReyesMath.E18.contDiffOn_F
#print axioms ReyesMath.E18.contDiffOn_Fprime
#print axioms ReyesMath.E18.continuousOn_Fprime
#print axioms ReyesMath.E18.Fprime_hasDerivAt
#print axioms ReyesMath.E18.continuousOn_Fsecond
#print axioms ReyesMath.E18.bound_Fprime
#print axioms ReyesMath.E18.lipschitz_F
#print axioms ReyesMath.E18.lipschitz_Fprime
#print axioms ReyesMath.E18.taylor_F
-- The Fréchet derivative, quadratic remainder and C¹ regularity (`MathProofs/E18Frechet.lean`)
#print axioms ReyesMath.E18.sob
#print axioms ReyesMath.E18.sob_nonneg
#print axioms ReyesMath.E18.norm_Phi_apply_le
#print axioms ReyesMath.E18.norm_opS_le
#print axioms ReyesMath.E18.norm_DL_le
#print axioms ReyesMath.E18.norm_Dj_le
#print axioms ReyesMath.E18.integral_norm_mul_norm_le
#print axioms ReyesMath.E18.integrable_norm_mul_norm
#print axioms ReyesMath.E18.integrable_pairC
#print axioms ReyesMath.E18.pairC
#print axioms ReyesMath.E18.pairC_apply
#print axioms ReyesMath.E18.toL2'
#print axioms ReyesMath.E18.coeFn_toL2'
#print axioms ReyesMath.E18.memLp_mul_continuous
#print axioms ReyesMath.E18.continuous_F_comp
#print axioms ReyesMath.E18.continuous_Fprime_comp
#print axioms ReyesMath.E18.Ucoef
#print axioms ReyesMath.E18.integrable_Ucoef
#print axioms ReyesMath.E18.Wcoef
#print axioms ReyesMath.E18.coeFn_Wcoef
#print axioms ReyesMath.E18.re_mul_ofReal_conj
#print axioms ReyesMath.E18.inner_Wcoef
#print axioms ReyesMath.E18.DE
#print axioms ReyesMath.E18.DE_apply
#print axioms ReyesMath.E18.Pc
#print axioms ReyesMath.E18.Qc
#print axioms ReyesMath.E18.Pc_nonneg
#print axioms ReyesMath.E18.Qc_nonneg
#print axioms ReyesMath.E18.abs_add6
#print axioms ReyesMath.E18.abs_re_conj_mul_le
#print axioms ReyesMath.E18.six_bound
#print axioms ReyesMath.E18.weight_variation_bound
#print axioms ReyesMath.E18.rem_pointwise
#print axioms ReyesMath.E18.curvJ_remainder
#print axioms ReyesMath.E18.curv
#print axioms ReyesMath.E18.energy_eq_curv
#print axioms ReyesMath.E18.integrable_W_term
#print axioms ReyesMath.E18.Ucoef_mul_re
#print axioms ReyesMath.E18.energy_remainder
#print axioms ReyesMath.E18.hasFDerivAt_energy
#print axioms ReyesMath.E18.opNorm_sub_le_of_remainder
#print axioms ReyesMath.E18.DE_lipschitz
#print axioms ReyesMath.E18.continuous_DE
#print axioms ReyesMath.E18.fderiv_energy
#print axioms ReyesMath.E18.contDiff_energy
#print axioms ReyesMath.E18.integrable_energy_density
#print axioms ReyesMath.E18.energy_eq_volume
#print axioms ReyesMath.E18.energy_eq_volume_field
#print axioms ReyesMath.E18.re_integral_volume
#print axioms ReyesMath.E18.re_integral_mul_conj
#print axioms ReyesMath.E18.re_ofReal_mul_mul_conj
#print axioms ReyesMath.E18.re_ofReal_mul_mul_ofReal_mul_conj
#print axioms ReyesMath.E18.DE_apply_volume
-- Classical calculus and periodic integration by parts on the torus (`MathProofs/E18TorusCalculus.lean`)
#print axioms ReyesMath.E18.instAddRightInvariantμ
#print axioms ReyesMath.E18.sh
#print axioms ReyesMath.E18.sh_zero
#print axioms ReyesMath.E18.sh_add
#print axioms ReyesMath.E18.HasPartial
#print axioms ReyesMath.E18.HasPartialR
#print axioms ReyesMath.E18.HasPartial.at
#print axioms ReyesMath.E18.HasPartial.add
#print axioms ReyesMath.E18.HasPartial.sub
#print axioms ReyesMath.E18.HasPartial.mul
#print axioms ReyesMath.E18.HasPartial.const_mul
#print axioms ReyesMath.E18.HasPartial.conj
#print axioms ReyesMath.E18.HasPartial.sum
#print axioms ReyesMath.E18.HasPartialR.ofReal
#print axioms ReyesMath.E18.HasPartialR.add
#print axioms ReyesMath.E18.HasPartialR.mul
#print axioms ReyesMath.E18.HasPartialR.const_mul
#print axioms ReyesMath.E18.HasPartialR.comp
#print axioms ReyesMath.E18.HasPartial.normSq
#print axioms ReyesMath.E18.HasPartial.re_conj_mul
#print axioms ReyesMath.E18.emode_add
#print axioms ReyesMath.E18.emode_sh
#print axioms ReyesMath.E18.hasDerivAt_emode_sh
#print axioms ReyesMath.E18.hasPartial_emode
#print axioms ReyesMath.E18.conj_emode_mul_self
#print axioms ReyesMath.E18.cfun
#print axioms ReyesMath.E18.coef_eq_cfun
#print axioms ReyesMath.E18.cfun_congr_ae
#print axioms ReyesMath.E18.cfun_translate
#print axioms ReyesMath.E18.cfun_hasPartial
#print axioms ReyesMath.E18.integrable_mul_continuous
#print axioms ReyesMath.E18.hasSum_integral_mul_conj
#print axioms ReyesMath.E18.integral_dpart_conj
#print axioms ReyesMath.E18.ser
#print axioms ReyesMath.E18.norm_term_le
#print axioms ReyesMath.E18.continuous_ser
#print axioms ReyesMath.E18.serC
#print axioms ReyesMath.E18.summable_serC
#print axioms ReyesMath.E18.serC_apply
#print axioms ReyesMath.E18.toLp_serC
#print axioms ReyesMath.E18.coef_toLp_serC
#print axioms ReyesMath.E18.ae_eq_serC
#print axioms ReyesMath.E18.cfun_ser
#print axioms ReyesMath.E18.ae_eq_ser
#print axioms ReyesMath.E18.hasPartial_ser
-- The Leibniz rule for the Fourier Laplacian (`MathProofs/E18Leibniz.lean`)
#print axioms ReyesMath.E18.inH_one_iff
#print axioms ReyesMath.E18.memℓp_dpart
#print axioms ReyesMath.E18.coef_dpart
#print axioms ReyesMath.E18.memℓp_dpart_dpart
#print axioms ReyesMath.E18.coef_dpart_dpart
#print axioms ReyesMath.E18.lap_eq_sum
#print axioms ReyesMath.E18.coeFn_sum
#print axioms ReyesMath.E18.integrable_cfun_term
#print axioms ReyesMath.E18.integral_conj_basic
#print axioms ReyesMath.E18.integral_conj_add
#print axioms ReyesMath.E18.integral_conj_smul
#print axioms ReyesMath.E18.cfun_eq_integral
#print axioms ReyesMath.E18.HasPartial.congr'
#print axioms ReyesMath.E18.leibniz
-- H⁴ regularity of the variational derivative (`MathProofs/E18Regularity.lean`)
#print axioms ReyesMath.E18.memLp_of_continuous
#print axioms ReyesMath.E18.Wt
#print axioms ReyesMath.E18.Vt
#print axioms ReyesMath.E18.Gt
#print axioms ReyesMath.E18.abs_xi_le_wt
#print axioms ReyesMath.E18.xi_sq_le_wt
#print axioms ReyesMath.E18.summable_coef_mul_wt
#print axioms ReyesMath.E18.summable_of_le_wt
#print axioms ReyesMath.E18.cD
#print axioms ReyesMath.E18.cDD
#print axioms ReyesMath.E18.cL
#print axioms ReyesMath.E18.norm_cD
#print axioms ReyesMath.E18.norm_cDD
#print axioms ReyesMath.E18.norm_cL
#print axioms ReyesMath.E18.rep_facts
#print axioms ReyesMath.E18.continuous_comp_Uw
#print axioms ReyesMath.E18.weight_facts
#print axioms ReyesMath.E18.regularity
-- The L² representative of the derivative (`MathProofs/E18Representative.lean`)
#print axioms ReyesMath.E18.inner_lap_comm
#print axioms ReyesMath.E18.coeFn_Wt
#print axioms ReyesMath.E18.Wcoef_eq
#print axioms ReyesMath.E18.DE_eq_inner
#print axioms ReyesMath.E18.DE_eq_volume
#print axioms ReyesMath.E18.real_gradient_eq
#print axioms ReyesMath.E18.G_real_gradient_iff
#print axioms ReyesMath.E18.dpart_ae_eq_of_hasPartial
#print axioms ReyesMath.E18.lap_ae_eq_of_hasPartial
-- Exact Lyapunov dissipation (`MathProofs/E18Lyapunov.lean`)
#print axioms ReyesMath.E18.energy_rate_general
#print axioms ReyesMath.E18.energy_rate
#print axioms ReyesMath.E18.e18_lyapunov
#print axioms ReyesMath.E18.e18_finite_dissipation
#print axioms ReyesMath.E18.e18_global_dissipation
#print axioms ReyesMath.E18.J4
#print axioms ReyesMath.E18.iota_two
#print axioms ReyesMath.E18.e18_lyapunov_H4
