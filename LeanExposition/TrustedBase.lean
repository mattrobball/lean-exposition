import Lean
import Informal

open Lean Informal

namespace LeanExposition

structure TrustedBaseConfig where
  modulePrefix : Name
  excludeModulePrefixes : Array Name := #[]
deriving Repr

structure TrustedBaseResult where
  typeDeps : NameSet := {}
  valueDeps : NameSet := {}

private partial def hasPrefix (n prefixName : Name) : Bool :=
  n == prefixName || match n with
    | .str p _ => hasPrefix p prefixName
    | .num p _ => hasPrefix p prefixName
    | .anonymous => false

private def isInReportedModule (env : Environment) (cfg : TrustedBaseConfig) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some modIdx =>
      let modName := env.header.moduleNames[modIdx.toNat]!
      hasPrefix modName cfg.modulePrefix
      && !cfg.excludeModulePrefixes.any (hasPrefix modName ·)
  | none => false

/-- Filter a raw dependency set to project-local, user-facing declarations.
    Uses lean-informal's `classifyNonUser` and `resolveToUser` for resolution,
    then restricts to declarations in reported modules. -/
private def filterAndResolveDeps (env : Environment) (cfg : TrustedBaseConfig)
    (rawDeps : NameSet) : NameSet := Id.run do
  let mut resolved : NameSet := {}
  for dep in rawDeps.toArray do
    let r := resolveToUser env dep
    if isInReportedModule env cfg r && (classifyNonUser env r).isNone then
      resolved := resolved.insert r
  resolved

/-- Compute the trusted base for a single target declaration.
    Uses lean-informal's `collectDeps` for transitive dependency collection
    (proof-irrelevant: theorem values are skipped, only types followed),
    then resolves and filters to user-facing project-local declarations. -/
def extractTrustedBase (env : Environment) (cfg : TrustedBaseConfig) (target : Name)
    : TrustedBaseResult := Id.run do
  let some info := env.find? target | return {}
  -- Collect type-only deps (proof-irrelevant, the default)
  let typeDepsRaw := collectDeps env target info (proofIrrelevant := true)
  let typeDeps := filterAndResolveDeps env cfg typeDepsRaw
  -- Collect all deps including values
  let allDepsRaw := collectDeps env target info (proofIrrelevant := false)
  let allDeps := filterAndResolveDeps env cfg allDepsRaw
  let valueDeps := allDeps.diff typeDeps
  { typeDeps, valueDeps }

/-- Compute the union of trusted base names for multiple target declarations. -/
def extractTrustedBaseNames (env : Environment) (cfg : TrustedBaseConfig)
    (targets : Array Name) : Std.HashSet Name := Id.run do
  let mut names : Std.HashSet Name := {}
  for target in targets do
    let result := extractTrustedBase env cfg target
    for name in result.typeDeps.toArray do
      names := names.insert name
  names

end LeanExposition
