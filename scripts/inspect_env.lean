import Lean
import Lake.CLI.Main
import Lake.Load.Workspace

open Lake Lean

private def withCurrentDir {α : Type} (dir : System.FilePath) (act : IO α) : IO α := do
  let cwd ← IO.Process.getCurrentDir
  IO.Process.setCurrentDir dir
  try
    act
  finally
    IO.Process.setCurrentDir cwd

private def loadWorkspaceAt (projectDir : System.FilePath) : IO Lake.Workspace := do
  let projectDir := projectDir.normalize
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let cfg ← Lake.MonadError.runEIO <| Lake.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let ws? ← withCurrentDir projectDir <| Lake.loadWorkspace cfg |>.toBaseIO
  match ws? with
  | some ws => pure ws
  | none => throw <| IO.userError s!"failed to load Lake workspace at {projectDir}"

private def importRoots (ws : Lake.Workspace) (excludeLibs : Array Name := #[]) : Array Import := Id.run do
  let mut imports := #[]
  for lib in ws.root.leanLibs do
    if excludeLibs.contains lib.name then
      continue
    for root in lib.config.roots do
      imports := imports.push { module := root }
  imports

private unsafe def loadEnv (projectDir : System.FilePath) (ws : Lake.Workspace) (imports : Array Import) : IO Environment := do
  enableInitializersExecution
  Lean.searchPathRef.set ws.augmentedLeanPath
  withCurrentDir projectDir <| Lean.importModules imports {}

private partial def hasPrefixName (n prefixName : Name) : Bool :=
  n == prefixName || match n with
    | .str p _ => hasPrefixName p prefixName
    | .num p _ => hasPrefixName p prefixName
    | .anonymous => false

unsafe def main (args : List String) : IO UInt32 := do
  let projectDir := args[0]?.map System.FilePath.mk |>.getD "."
  let rootPrefix := args[1]?.map String.toName |>.getD `BridgelandStability
  let excludeLibs := args.drop 2 |>.toArray.map String.toName
  let ws ← loadWorkspaceAt projectDir
  IO.println s!"lean libs: {String.intercalate ", " (ws.root.leanLibs.toList.map (·.name.toString))}"
  let imports := importRoots ws excludeLibs
  IO.println s!"imports ({imports.size}):"
  for imp in imports do
    IO.println s!"  - {imp.module}"
  let env ← loadEnv projectDir ws imports
  IO.println s!"constants: {env.constants.toList.length}"
  let mut moduleHits : Std.HashMap Name Nat := {}
  let mut nameHits := 0
  for (name, _) in env.constants.toList do
    if hasPrefixName name rootPrefix then
      nameHits := nameHits + 1
    if let some modIdx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[modIdx.toNat]!
      if hasPrefixName modName rootPrefix then
        moduleHits := moduleHits.insert modName (moduleHits.getD modName 0 + 1)
  IO.println s!"name-prefix hits ({rootPrefix}): {nameHits}"
  let hits := moduleHits.toArray.qsort (fun a b => a.1.lt b.1)
  IO.println s!"module-prefix hits ({rootPrefix}): {hits.size} modules"
  for (modName, count) in hits[:20] do
    IO.println s!"  - {modName}: {count}"
  return 0
