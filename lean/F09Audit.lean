import MathProofs.GC26GlobalIdentifiability

/-!
Reproducible audit of the exported F09 theorem signatures and dependencies.
Run `lake env lean F09Audit.lean` after building MathProofs.V18Identifiability.
This file adds no declarations to the maintained library.
-/

#check ReyesMath.V18MiddleJacobian.middle_det_ne_zero
#check ReyesMath.V18Forward.hasFDerivAt_observed_near_frozen
#check ReyesMath.V18Forward.selectedMinor_frozen_eq
#check ReyesMath.V18Forward.jacobian_rank
#check ReyesMath.V18Forward.jacobian_nullity
#check ReyesMath.conditional_local_level_set
#check ReyesMath.V18Forward.observed_locally_nonidentifiable
#check ReyesMath.V18Forward.f09_completion
#print ReyesMath.V18Forward.HasTwentyDimensionalLocalFiber

#print axioms ReyesMath.V18MiddleJacobian.middle_det_bounds
#print axioms ReyesMath.V18MiddleJacobian.middle_det_ne_zero
#print axioms ReyesMath.V18Forward.hasFDerivAt_observed_near_frozen
#print axioms ReyesMath.V18Forward.selectedMinor_frozen_eq
#print axioms ReyesMath.V18Forward.jacobian_rank
#print axioms ReyesMath.V18Forward.jacobian_nullity
#print axioms ReyesMath.conditional_local_level_set
#print axioms ReyesMath.V18Forward.observed_local_level_set
#print axioms ReyesMath.V18Forward.observed_locally_nonidentifiable
#print axioms ReyesMath.V18Forward.f09_completion

/- GC26 candidate roots -/
#print axioms ReyesMath.V18Forward.observed_update_quarkAmp
#print axioms ReyesMath.V18Forward.observed_update_quarkPower
#print axioms ReyesMath.V18Forward.observed_shiftHiggs
#print axioms ReyesMath.V18Forward.observed_invisibleFamily
#print axioms ReyesMath.V18Forward.invisibleFamily_injective
#print axioms ReyesMath.V18Forward.observed_all_points_nonisolated
#print axioms ReyesMath.V18Forward.observed_relative_nonisolated
#print axioms ReyesMath.V18Forward.observed_not_injective
#print axioms ReyesMath.V18Forward.floor_eq_iff
#print axioms ReyesMath.V18Forward.nested_floor_eq_iff
#print axioms ReyesMath.V18Forward.generic_rank_counterexample
#print axioms ReyesMath.V18Forward.augmented_rank_obstruction
#print axioms ReyesMath.V18Forward.injective_of_strict_pairing

#print axioms ReyesMath.V18Forward.historical_lightRaw
#print axioms ReyesMath.V18Forward.logistic_floor_logit_eq
#print axioms ReyesMath.V18Forward.historical_two_active_unique
#print axioms ReyesMath.V18Forward.historical_zero_alpha

#print axioms ReyesMath.V18Forward.historical_active_prefix
#print axioms ReyesMath.V18Forward.historical_one_active_interval
#print axioms ReyesMath.V18Forward.historical_exceptional_endpoint
