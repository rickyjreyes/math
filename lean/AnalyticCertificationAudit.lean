import MathProofs.E62Certification
import MathProofs.E58Certification
import MathProofs.E58GreenFunction
import MathProofs.E17Certification
import MathProofs.E26QuotientDomain
import MathProofs.E57Certification
import MathProofs.BandPassFlow

/-!
Reproducible dependency audit of the seven analytic manuscript certifications
(E62, E58, M2/E17, E26, M3/E57, E61, E16) and the F11 companions (E13/E14, E59).
Run `lake env lean AnalyticCertificationAudit.lean` after building the imported modules
(the focused workflow `.github/workflows/lean-analytic-cores.yml` does this on every pull
request). Every declaration below must depend only on `propext`, `Classical.choice` and
`Quot.sound`. This file adds no declarations to the maintained library.
-/

-- E62 (#34)
#print axioms ReyesMath.E62Cert.theorem_e62
#print axioms ReyesMath.E62Cert.projector
#print axioms ReyesMath.E62Cert.projector_physical
#print axioms ReyesMath.E62Cert.sharpness
#print axioms ReyesMath.E62Cert.continuous_spectrum
#print axioms ReyesMath.E62Cert.zero_width_shell
#print axioms ReyesMath.E62Cert.zero_field
#print axioms ReyesMath.E62Cert.no_monotonicity
#print axioms ReyesMath.TorusL2.e62
#print axioms ReyesMath.SpectralConc.e62_continuous
#print axioms ReyesMath.E62LebesgueFraction.fraction_bounds
#print axioms ReyesMath.E62LebesgueFraction.fraction_zero_iff
#print axioms ReyesMath.E62LebesgueFraction.fraction_one_iff

-- E58 (#38)
#print axioms ReyesMath.E58Cert.theorem_e58
#print axioms ReyesMath.E58Cert.resolvent
#print axioms ReyesMath.E58Cert.near_shell
#print axioms ReyesMath.E58Cert.not_attained
#print axioms ReyesMath.E58Cert.attained_of_a_zero
#print axioms ReyesMath.E58Cert.coercivity
#print axioms ReyesMath.E58Cert.band_selectivity
#print axioms ReyesMath.E58Cert.scope
#print axioms ReyesMath.E58Cert.periodic_box
#print axioms ReyesMath.E58Green.fourier_g
#print axioms ReyesMath.E58Green.inversion
#print axioms ReyesMath.E58Green.distrib
#print axioms ReyesMath.E58Green.ode
#print axioms ReyesMath.E58Green.sign_change
#print axioms ReyesMath.E58Green.not_pointwise_bound

-- M2/E17 (#36)
#print axioms ReyesMath.E17Cert.main_theorem
#print axioms ReyesMath.E17Cert.global_bound
#print axioms ReyesMath.E17Cert.exact_difference
#print axioms ReyesMath.E17Cert.error_formula
#print axioms ReyesMath.E17Cert.uniform_bound
#print axioms ReyesMath.E17Cert.compact_bound
#print axioms ReyesMath.E17Cert.tendstoUniformlyOn_compact
#print axioms ReyesMath.E17Cert.l2_limit
#print axioms ReyesMath.E17Cert.fixed_eps_control
#print axioms ReyesMath.E17Cert.whole_space
#print axioms ReyesMath.E17Cert.node_obstruction
#print axioms ReyesMath.E17Cert.phase_invariance
#print axioms ReyesMath.E17Cert.local_gauge
#print axioms ReyesMath.E17Cert.historical
#print axioms ReyesMath.E17GlobalBound.arbitrary_alpha_bound

-- E26 (#35)
#print axioms ReyesMath.E26.e26
#print axioms ReyesMath.E26.e26_Rd
#print axioms ReyesMath.E26.cor_modulus
#print axioms ReyesMath.E26.cor_nonneg
#print axioms ReyesMath.E26.not_ae_norm_ge_of_memLp
#print axioms ReyesMath.E26.counterexample
#print axioms ReyesMath.E26.corrected_bound
#print axioms ReyesMath.E26.delta_not_replaceable
#print axioms ReyesMath.E26Certification.main_theorem
#print axioms ReyesMath.E26Domain.quotient_domain
#print axioms ReyesMath.E26Domain.sharp_constant

-- M3/E57 (#43)
#print axioms ReyesMath.E57Cert.part_i
#print axioms ReyesMath.E57Cert.main_theorem
#print axioms ReyesMath.E57Cert.semigroup
#print axioms ReyesMath.E57Cert.smoothing
#print axioms ReyesMath.E57Cert.strong_ode
#print axioms ReyesMath.E57Cert.energy_identities
#print axioms ReyesMath.E57Cert.gradient
#print axioms ReyesMath.E57Cert.shell_corollary
#print axioms ReyesMath.E57Cert.no_shell_state
#print axioms ReyesMath.E57Cert.plane_wave_not_memLp
#print axioms ReyesMath.E57Cert.periodic
#print axioms ReyesMath.E57Cert.linear_threshold
#print axioms ReyesMath.E57Cert.sign_reversal
#print axioms ReyesMath.E57Cert.e57_eq_Sr

-- E61 (#39)
#print axioms ReyesMath.E61Cert.theorem_e61
#print axioms ReyesMath.E61Cert.stable
#print axioms ReyesMath.E61Cert.critical
#print axioms ReyesMath.E61Cert.unstable
#print axioms ReyesMath.E61Cert.unstable_band
#print axioms ReyesMath.E61Cert.near_onset
#print axioms ReyesMath.E61Cert.periodic_box
#print axioms ReyesMath.E61Cert.rcL_tendsto
#print axioms ReyesMath.E61Cert.translation
#print axioms ReyesMath.E61Cert.exactNorm_eq_Sr
#print axioms ReyesMath.SH.spectrum_Lr
#print axioms ReyesMath.SH.generator
#print axioms ReyesMath.SH.generator_domain
#print axioms ReyesMath.SH.Aop_isSelfAdjoint
#print axioms ReyesMath.SH.mild_iff
#print axioms ReyesMath.SH.opNorm_Sr

-- E16 (#32)
#print axioms ReyesMath.SpectralConc.exact_modal_law
#print axioms ReyesMath.SpectralConc.gap_lemma
#print axioms ReyesMath.SpectralConc.concentration
#print axioms ReyesMath.SpectralConc.decay_of_mu_zero
#print axioms ReyesMath.SpectralConc.argmax_convergence
#print axioms ReyesMath.SpectralConc.argmax_rate
#print axioms ReyesMath.SpectralConc.radial_law
#print axioms ReyesMath.SpectralConc.radial_corollary
#print axioms ReyesMath.SpectralConc.counterexample
#print axioms ReyesMath.E16Torus.coef_flow
#print axioms ReyesMath.E16Torus.power_law
#print axioms ReyesMath.E16Torus.coef_ode
#print axioms ReyesMath.E16Torus.dominant_concentration
#print axioms ReyesMath.E16Torus.shell_missed

-- F11 companions (E13/E14, E59)
#print axioms ReyesMath.BandPass.e13
#print axioms ReyesMath.BandPass.real_gradient
#print axioms ReyesMath.BandPass.half_flow
#print axioms ReyesMath.BandPass.centred_first_variation
#print axioms ReyesMath.TorusL2.e59
