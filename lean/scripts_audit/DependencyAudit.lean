import MathProofs.D4FrozenWholeSpace
import MathProofs.GC16ZeroShell
import MathProofs.GC06NearZeroShell
import MathProofs.GC08Cartesian
import MathProofs.GC08Gauge
import MathProofs.GC08Field
import MathProofs.GC08PlaneLocus
import MathProofs.GC08ClosedPlane
import MathProofs.GC08Spatial
import MathProofs.GC08Hadamard
import MathProofs.GC03Energy

/-!
Dependency audit for the whole-space confinement chain (Task 2).

Collects every constant transitively used by the audited roots, keeps the ones in the
`ReyesMath` namespace, and prints them grouped by defining module, together with their kind
(theorem / definition / other). It also prints the axioms each root depends on.

Run: `lake env lean scripts_audit/DependencyAudit.lean`
-/

open Lean Meta Elab Command

partial def collectDeps (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet do
        if !seen.contains m then stack := stack.push m
  return seen

def kindOf (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "AXIOM"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"
  | .quotInfo _ => "quot"

elab "#audit_deps " root:ident : command => do
  let env ← getEnv
  let rootName := root.getId
  let deps := collectDeps env rootName
  let mut byModule : Std.HashMap Name (Array (String × Name)) := {}
  let mut axioms : Array Name := #[]
  for n in deps.toList do
    let some ci := env.find? n | continue
    if let .axiomInfo _ := ci then axioms := axioms.push n
    if (`ReyesMath).isPrefixOf n && !n.isInternal then
      let modName := match env.getModuleIdxFor? n with
        | some idx => env.header.moduleNames[idx.toNat]!
        | none => `current
      byModule := byModule.insert modName ((byModule.getD modName #[]).push (kindOf ci, n))
  logInfo m!"ROOT {rootName}: {deps.size} constants transitively; axioms: {axioms.toList}"
  let mods := byModule.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (modName, decls) in mods do
    let thms := (decls.filter (·.1 == "theorem")).size
    let defs := (decls.filter (·.1 == "def")).size
    logInfo m!"MODULE {modName}: {decls.size} project declarations ({thms} theorems, {defs} defs)"

#audit_deps ReyesMath.OrbitalStability.main
#audit_deps ReyesMath.D4Frozen.d4_frozen_main
#audit_deps ReyesMath.D4Frozen.d4_strict_binding
#audit_deps ReyesMath.GC16ZeroShell.strict_binding_all_mass
#audit_deps ReyesMath.GC16ZeroShell.compactness_all_mass
#audit_deps ReyesMath.GC16ZeroShell.exists_minimizer_all_mass
#audit_deps ReyesMath.GC16ZeroShell.orbital_stability_all_mass
#audit_deps ReyesMath.GC06ShellBinding.mB_lt_mR
#audit_deps ReyesMath.GC06ShellBinding.gap_refined
#audit_deps ReyesMath.GC06ShellBinding.strict_binding_refined
#audit_deps ReyesMath.GC06ShellBinding.compactness_refined
#audit_deps ReyesMath.GC06ShellBinding.exists_minimizer_refined
#audit_deps ReyesMath.GC06NearZeroShell.exists_stretch
#audit_deps ReyesMath.GC06NearZeroShell.seed_upper
#audit_deps ReyesMath.GC06NearZeroShell.kinetic_gap
#audit_deps ReyesMath.GC06NearZeroShell.strict_binding_near_zero
#audit_deps ReyesMath.GC06NearZeroShell.compactness_near_zero
#audit_deps ReyesMath.GC06NearZeroShell.exists_minimizer_near_zero
#audit_deps ReyesMath.GC08.curvature_at_zero
#audit_deps ReyesMath.GC08.closure_plane
#audit_deps ReyesMath.GC08.closure_family_distinct
#audit_deps ReyesMath.GC08.polar_scalar_unique
#audit_deps ReyesMath.GC08.curvature_rotate
#audit_deps ReyesMath.GC08.curvature_gauge
#audit_deps ReyesMath.GC08.exists_real_gauge
#audit_deps ReyesMath.GC08.unique_all_jets
#audit_deps ReyesMath.GC08.lineCurrent_deriv
#audit_deps ReyesMath.GC08.fieldCurvature_eq_cartesian
#audit_deps ReyesMath.GC08.fieldCurvature_at_zero
#audit_deps ReyesMath.GC08.field_closure_family_distinct
#audit_deps ReyesMath.GC08.unique_symmetric_jets
#audit_deps ReyesMath.GC08.plane_iff_equations
#audit_deps ReyesMath.GC08.nodal_factorization
#audit_deps ReyesMath.GC08.closed_plane_iff_equations
#audit_deps ReyesMath.GC08.vanishes_on_closed_plane
#audit_deps ReyesMath.GC08.curvature_spatial
#audit_deps ReyesMath.GC08.closure_spatial
#audit_deps ReyesMath.GC08.closure_rotate
#audit_deps ReyesMath.GC08.parameter_integral_smooth
#audit_deps ReyesMath.GC08.smooth_graph_factorization
#audit_deps ReyesMath.GC08.equivariant_graph_factorization
#audit_deps ReyesMath.GC08.segment_difference

#audit_deps ReyesMath.GC03Energy.power_absorption
#audit_deps ReyesMath.GC03Energy.integrated_absorption
#audit_deps ReyesMath.GC03Energy.energy_coercivity
#audit_deps ReyesMath.GC03Energy.cubic_quintic_d2_p2
#audit_deps ReyesMath.GC03Energy.supercritical_scaling_iff
#audit_deps ReyesMath.GC03Energy.singular_exponent_window_iff
#audit_deps ReyesMath.GC03Energy.trajectory_kinetic_bound
#audit_deps ReyesMath.GC03Energy.energy_drop_count
#audit_deps ReyesMath.GC03Energy.finite_energy_drop_count
#audit_deps ReyesMath.GC03Energy.gradient_forcing_threshold
#audit_deps ReyesMath.GC03Energy.lower_cutoff_exponent_lt_critical
#audit_deps ReyesMath.GC03Energy.relative_mass_cancellation
