import MathProofs.V18Identifiability

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
