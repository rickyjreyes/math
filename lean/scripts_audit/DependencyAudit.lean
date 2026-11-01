import MathProofs.D4FrozenWholeSpace

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
