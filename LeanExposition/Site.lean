import Lean
import Lean.DeclarationRange
import Lean.Elab.Import
import Lean.Meta.Instances
import Lake.CLI.Main
import Lake.Load.Workspace
import Informal
import LeanExposition.TrustedBase

open Lake
open Lean
open Lean.Meta

namespace LeanExposition

structure Cli where
  projectDir : System.FilePath := "."
  rootPrefix : Option Name := none
  repoUrl : Option String := none
  siteTitle : Option String := none
  outputDir : Option String := none
  comparatorConfig : Option System.FilePath := none
  tfbExe : String := "extractDeps"
  shadowOutputDir : Option System.FilePath := none
  shadowOnly : Bool := false
  excludeLibs : Array Name := #[]
deriving Repr

inductive DeclKind where
  | theorem
  | definition
  | opaque
  | structure
  | typeclass
  | inductive
  | axiom
  | instance
deriving Repr, BEq, Inhabited, ToJson, FromJson

def DeclKind.label : DeclKind → String
  | .theorem => "Theorem"
  | .definition => "Definition"
  | .opaque => "Opaque"
  | .structure => "Structure"
  | .typeclass => "Type Class"
  | .inductive => "Inductive"
  | .axiom => "Axiom"
  | .instance => "Instance"

structure SourceInfo where
  relPath : String
  absPath : System.FilePath
  line : Nat
  endLine : Nat
deriving Repr, ToJson, FromJson


structure ComparatorConfigInfo where
  challengeModule : String
  solutionModule : String
  theoremNames : Array Name
  permittedAxioms : Array String
  enableNanoda : Bool
deriving Repr, ToJson, FromJson

structure GraphNode where
  id : String
  label : String
  kind : String
  status : String
  groupKey : String
  moduleName : String
  href : String
deriving Repr, ToJson, FromJson

structure GraphEdge where
  source : String
  target : String
deriving Repr, ToJson, FromJson

structure GraphData where
  nodes : Array GraphNode
  edges : Array GraphEdge
deriving Repr, ToJson, FromJson

structure ShadowEntry where
  name : Name
  moduleName : Name
  anchor : String
  kind : DeclKind
  source : SourceInfo
  displaySignature : String
  deps : Array Name := #[]
  tags : Array String := #[]
deriving Repr, ToJson, FromJson

structure ShadowManifest where
  comparator? : Option ComparatorConfigInfo := none
  entries : Array ShadowEntry := #[]
deriving Repr, ToJson, FromJson

structure TrustedBaseInfo where
  names : Std.HashSet Name := {}
  comparator? : Option ComparatorConfigInfo := none
deriving Repr

private def usage : String :=
  String.intercalate "\n" [
    "Usage: lake exe exposition [options]",
    "",
    "Options:",
    "  --project DIR        Path to the target Lean project (default: current directory)",
    "  --root PREFIX        Root module prefix to expose (default: first root library)",
    "  --repo-url URL       GitHub repo URL used for issue/source links",
    "  --title TITLE        Site title override",
    "  --output DIR         Output directory passed to Verso",
    "  --comparator-config  Comparator config file relative to the target project",
    "  --tfb-exe NAME       Deprecated; trusted-base extraction is built in",
    "  --write-shadow DIR   Write and build a Verso-ready shadow project",
    "  --shadow-only        Exit after the shadow project is built",
    "  --exclude-lib NAME   Exclude a root library when importing the target project",
  ]

private def parseArgs : List String → Except String Cli
  | [] => .ok {}
  | "--project" :: dir :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with projectDir := dir }
  | "--root" :: root :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with rootPrefix := some root.toName }
  | "--repo-url" :: url :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with repoUrl := some url }
  | "--title" :: title :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with siteTitle := some title }
  | "--output" :: out :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with outputDir := some out }
  | "--comparator-config" :: path :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with comparatorConfig := some path }
  | "--tfb-exe" :: exe :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with tfbExe := exe }
  | "--write-shadow" :: dir :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with shadowOutputDir := some dir }
  | "--shadow-only" :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with shadowOnly := true }
  | "--exclude-lib" :: lib :: rest => do
      let cfg ← parseArgs rest
      pure { cfg with excludeLibs := cfg.excludeLibs.push lib.toName }
  | flag :: _ =>
      .error s!"Unknown or incomplete option: {flag}\n\n{usage}"

private def hasPrefixName (n prefixName : Name) : Bool :=
  n == prefixName || match n with
    | .str p _ => hasPrefixName p prefixName
    | .num p _ => hasPrefixName p prefixName
    | .anonymous => false

private def slugify (s : String) : String :=
  let pushChar (acc : String) (ch : Char) : String :=
    if ch.isAlphanum then
      acc.push (if ch.isUpper then ch.toLower else ch)
    else if acc.isEmpty || acc.back == '-' then
      acc
    else
      acc.push '-'
  let slug := s.foldl pushChar ""
  if slug.isEmpty then "item" else slug


private def nameComponents : Name → List String
  | .anonymous => []
  | .num p n => nameComponents p ++ [toString n]
  | .str p s => nameComponents p ++ [s]

private def moduleTailComponents (rootPrefix moduleName : Name) : List String :=
  let root := nameComponents rootPrefix
  let full := nameComponents moduleName
  full.drop root.length

private def groupKeyOfModule (rootPrefix moduleName : Name) : String :=
  match moduleTailComponents rootPrefix moduleName with
  | first :: _ => first
  | [] => rootPrefix.toString

private def modulePathOf (rootPrefix moduleName : Name) : String :=
  let tail := moduleTailComponents rootPrefix moduleName
  match tail with
  | [] => moduleName.toString
  | _ => String.intercalate "." tail

private def readFileIfExists (path : System.FilePath) : IO (Option String) := do
  if ← path.pathExists then
    return some (← IO.FS.readFile path)
  return none

private def loadComparatorConfig? (projectDir : System.FilePath)
    (configPath? : Option System.FilePath := none) : IO (Option ComparatorConfigInfo) := do
  let cfgPath := projectDir / configPath?.getD "comparator.json"
  let text? ← readFileIfExists cfgPath
  match text? with
  | none => return none
  | some contents =>
      match Json.parse contents with
      | .error _ => pure none
      | .ok json =>
          let challenge? :=
            match json.getObjValAs? String "challenge_module" with
            | .ok value => some value
            | .error _ => none
          let solution? :=
            match json.getObjValAs? String "solution_module" with
            | .ok value => some value
            | .error _ => none
          let theoremNames? :=
            match json.getObjValAs? (Array String) "theorem_names" with
            | .ok value => some <| value.map String.toName
            | .error _ => none
          let permittedAxioms? :=
            match json.getObjValAs? (Array String) "permitted_axioms" with
            | .ok value => some value
            | .error _ => none
          let enableNanoda? :=
            match json.getObjValAs? Bool "enable_nanoda" with
            | .ok value => some value
            | .error _ => none
          match challenge?, solution?, theoremNames?, permittedAxioms?, enableNanoda? with
          | some challengeModule, some solutionModule, some theoremNames, some permittedAxioms, some enableNanoda =>
              pure <| some {
                challengeModule
                solutionModule
                theoremNames
                permittedAxioms
                enableNanoda
              }
          | _, _, _, _, _ => pure none

private def splitTopLevelAssignment? (s : String) : Option (String × String) :=
  let rec go (chars : List Char) (round curly square angled : Nat) (acc : List Char) : Option (String × String) :=
    match chars with
    | [] => none
    | ':' :: '=' :: rest =>
        if round == 0 && curly == 0 && square == 0 && angled == 0 then
          some (
            (String.trimAscii (String.ofList acc.reverse)).toString,
            (String.trimAscii (String.ofList rest)).toString
          )
        else
          go rest round curly square angled ('=' :: ':' :: acc)
    | '(' :: rest => go rest (round + 1) curly square angled ('(' :: acc)
    | ')' :: rest => go rest (round - 1) curly square angled (')' :: acc)
    | '{' :: rest => go rest round (curly + 1) square angled ('{' :: acc)
    | '}' :: rest => go rest round (curly - 1) square angled ('}' :: acc)
    | '[' :: rest => go rest round curly (square + 1) angled ('[' :: acc)
    | ']' :: rest => go rest round curly (square - 1) angled (']' :: acc)
    | '⦃' :: rest => go rest round curly square (angled + 1) ('⦃' :: acc)
    | '⦄' :: rest => go rest round curly square (angled - 1) ('⦄' :: acc)
    | ch :: rest => go rest round curly square angled (ch :: acc)
  go s.toList 0 0 0 0 []

private def computeTrustedBaseNames (env : Environment) (rootPrefix : Name)
    (comparator : ComparatorConfigInfo) : Std.HashSet Name :=
  extractTrustedBaseNames env {
    modulePrefix := rootPrefix
    excludeModulePrefixes := #[comparator.challengeModule.toName]
  } comparator.theoremNames

private def loadTrustedBaseInfo (cfg : Cli) (rootPrefix : Name) (env : Environment) : IO TrustedBaseInfo := do
  let comparator? ← loadComparatorConfig? cfg.projectDir cfg.comparatorConfig
  match comparator? with
  | none => pure {}
  | some comparator =>
      let names := computeTrustedBaseNames env rootPrefix comparator
      pure {
        names
        comparator? := some comparator
      }

private def ppExprString (env : Environment) (e : Expr) : IO String := do
  let ctx : PPContext := { env := env, opts := {} }
  return toString (← ctx.runMetaM (Meta.ppExpr e))

private def readSourceSnippet (src : SourceInfo) : IO String := do
  let text ← IO.FS.readFile src.absPath
  let lines := (text.splitOn "\n").toArray
  let startIdx := src.line - 1
  let endIdx := min src.endLine lines.size
  let selected := (List.range (endIdx - startIdx)).map fun i => lines[startIdx + i]!
  pure <| String.intercalate "\n" selected

private def declKeyword : DeclKind → String
  | .theorem => "theorem"
  | .definition => "def"
  | .opaque => "opaque"
  | .structure => "structure"
  | .typeclass => "class"
  | .inductive => "inductive"
  | .axiom => "axiom"
  | .instance => "instance"

private def displaySignatureFallback (kind : DeclKind) (name : Name) (expandedSignature : String) : String :=
  s!"{declKeyword kind} {name.getString!} : {expandedSignature}"

private def stringContains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def stripInlineAttributePrefix (line : String) : String :=
  let trimmed := (String.trimAscii line).toString
  if !trimmed.startsWith "@[" then
    trimmed
  else
    match trimmed.splitOn "]" with
    | _attr :: rest@(_ :: _) =>
        (String.trimAscii (String.intercalate "]" rest)).toString
    | _ => ""

private partial def dropLeadingDecorations (lines : List String) : List String :=
  let lines := lines.dropWhile (fun line => line.trimAscii.isEmpty)
  match lines with
  | [] => []
  | line :: rest =>
      let trimmed := (String.trimAscii line).toString
      if trimmed.startsWith "/-" then
        let rec dropCommentBlock : List String → List String
          | [] => []
          | commentLine :: remaining =>
              if stringContains commentLine "-/" then
                remaining
              else
                dropCommentBlock remaining
        dropLeadingDecorations (dropCommentBlock (line :: rest))
      else if trimmed.startsWith "@[" then
        let remainder := stripInlineAttributePrefix line
        if remainder.isEmpty then
          dropLeadingDecorations rest
        else
          remainder :: rest
      else
        line :: rest

private def cleanDeclSnippet (snippet : String) : String :=
  (String.trimAscii (String.intercalate "\n" (dropLeadingDecorations (snippet.splitOn "\n")))).toString

private def headBeforeAssignment (snippet : String) : String :=
  match splitTopLevelAssignment? snippet with
  | some (first, _) => first
  | none => (String.trimAscii snippet).toString

private def dropSuffixString? (s suffix : String) : Option String :=
  if s.endsWith suffix then
    some <| String.ofList ((s.toList.reverse.drop suffix.length).reverse)
  else
    none

private def headBeforeWhere? (snippet : String) : Option String :=
  let rec go (remaining : List String) (acc : List String) :=
    match remaining with
    | [] => none
    | line :: rest =>
        let trimmed := (String.trimAscii line).toString
        if trimmed == "where" then
          some <| (String.trimAscii (String.intercalate "\n" acc.reverse)).toString
        else
          let prefix? := dropSuffixString? trimmed " where"
          match prefix? with
          | some pfx =>
              let acc := if pfx.isEmpty then acc else pfx :: acc
              some <| (String.trimAscii (String.intercalate "\n" acc.reverse)).toString
          | none =>
              go rest (line :: acc)
  go (snippet.splitOn "\n") []

private def headBeforeProof (snippet : String) : String :=
  let assignmentHead := headBeforeAssignment snippet
  match headBeforeWhere? snippet with
  | some whereHead =>
      if assignmentHead.contains "where" then
        whereHead
      else
        assignmentHead
  | none => assignmentHead

private def displaySignatureFromSource (kind : DeclKind) (src? : Option SourceInfo) : IO (Option String) := do
  let some src := src? | return none
  let snippet := cleanDeclSnippet (← readSourceSnippet src)
  if snippet.isEmpty then
    return none
  let rendered :=
    match kind with
    | .definition | .structure | .typeclass | .inductive => snippet
    | _ => headBeforeProof snippet
  if rendered.isEmpty then
    return none
  return some rendered

private def moduleNameOf (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

private def declKindOf (env : Environment) (info : ConstantInfo) (name : Name) : DeclKind :=
  if Lean.Meta.isInstanceCore env name then
    .instance
  else if isClass env name then
    .typeclass
  else match info with
    | .thmInfo _ => .theorem
    | .opaqueInfo _ => .opaque
    | .axiomInfo _ => .axiom
    | .inductInfo _ =>
        if (getStructureInfo? env name).isSome then
          .structure
        else
          .inductive
    | .defnInfo _ => .definition
    | _ => .definition

private def shouldExpose (env : Environment) (rootPrefix : Name) (name : Name) (_info : ConstantInfo) : Bool :=
  if let some moduleName := moduleNameOf env name then
    if !hasPrefixName moduleName rootPrefix then
      false
    else
      (Informal.classifyNonUser env name).isNone
  else
    false

private def sourcePathForModule (pkg : Lake.Package) (moduleName : Name) : Option System.FilePath :=
  (pkg.findModule? moduleName).map (·.leanFile)

private def moduleSourcePath (projectDir : System.FilePath) (moduleName : Name) : System.FilePath :=
  projectDir / s!"{moduleName.toString.replace "." "/"}.lean"

private def parseImportedModule? (line : String) : Option Name :=
  let trimmed := (String.trimAscii line).toString
  let prefixes := ["public import ", "import "]
  prefixes.findSome? fun pfx =>
    if trimmed.startsWith pfx then
      let rest := (String.trimAscii (trimmed.drop pfx.length |>.toString)).toString
      if rest.isEmpty then none else some rest.toName
    else
      none

private partial def visitModuleImports (projectDir : System.FilePath) (rootPrefix : Name)
    (moduleName : Name) (visited : Std.HashSet Name) (order : Std.HashMap Name Nat)
    (nextRank : Nat) : IO (Std.HashSet Name × Std.HashMap Name Nat × Nat) := do
  if visited.contains moduleName then
    return (visited, order, nextRank)
  let visited := visited.insert moduleName
  let text? ← readFileIfExists (moduleSourcePath projectDir moduleName)
  match text? with
  | none => return (visited, order, nextRank)
  | some contents =>
      let imports : List Name := (contents.splitOn "\n").filterMap parseImportedModule?
      let imports := imports.filter fun imported => imported != moduleName && hasPrefixName imported rootPrefix
      let mut visited := visited
      let mut order := order
      let mut nextRank := nextRank
      for imported in imports do
        if !order.contains imported then
          order := order.insert imported nextRank
          nextRank := nextRank + 1
        let (visited', order', nextRank') ← visitModuleImports projectDir rootPrefix imported visited order nextRank
        visited := visited'
        order := order'
        nextRank := nextRank'
      return (visited, order, nextRank)

private def moduleOrderMap (projectDir : System.FilePath) (rootPrefix : Name) : IO (Std.HashMap Name Nat) := do
  let rootFile := moduleSourcePath projectDir rootPrefix
  if !(← rootFile.pathExists) then
    return {}
  let initial : Std.HashMap Name Nat := {}
  let (_, order, _) ← visitModuleImports projectDir rootPrefix rootPrefix {} (initial.insert rootPrefix 0) 1
  return order

private def insertExprDeps (self : Name) (acc : Std.HashSet Name) (e : Expr) : Std.HashSet Name :=
  e.getUsedConstants.foldl
    (fun acc dep => if dep != self then acc.insert dep else acc)
    acc

private def directShadowDeps (env : Environment) (name : Name) (info : ConstantInfo) : Array Name := Id.run do
  let mut deps : Std.HashSet Name := {}
  match info with
  | .defnInfo v =>
      deps := insertExprDeps name deps v.type
      deps := insertExprDeps name deps v.value
  | .thmInfo v =>
      deps := insertExprDeps name deps v.type
  | .opaqueInfo v =>
      deps := insertExprDeps name deps v.type
      deps := insertExprDeps name deps v.value
  | .inductInfo v =>
      deps := insertExprDeps name deps v.type
      for ctor in v.ctors do
        if ctor != name then
          deps := deps.insert ctor
        if let some ctorInfo := env.find? ctor then
          deps := insertExprDeps name deps ctorInfo.type
  | .ctorInfo v =>
      deps := insertExprDeps name deps v.type
  | .recInfo v =>
      deps := insertExprDeps name deps v.type
  | .axiomInfo v =>
      deps := insertExprDeps name deps v.type
  | .quotInfo _ => ()
  deps.toArray.qsort Name.lt

private def relevantShadowDepMap (entries : Array ShadowEntry) : Std.HashMap Name (Array Name) :=
  let relevant : Std.HashSet Name :=
    entries.foldl (fun acc entry => acc.insert entry.name) {}
  entries.foldl
    (fun acc entry =>
      acc.insert entry.name (entry.deps.filter fun dep => dep != entry.name && relevant.contains dep))
    {}

private def shadowEntryLt (moduleOrder : Std.HashMap Name Nat) (a b : ShadowEntry) : Bool :=
  let ra := moduleOrder.getD a.moduleName 1000000000
  let rb := moduleOrder.getD b.moduleName 1000000000
  if ra == rb then
    if a.moduleName == b.moduleName then
      if a.source.line == b.source.line then
        a.name.lt b.name
      else
        a.source.line < b.source.line
    else
      a.moduleName.lt b.moduleName
  else
    ra < rb

private def shadowTopologicalLayers (moduleOrder : Std.HashMap Name Nat)
    (entries : Array ShadowEntry) : Array (Array ShadowEntry) := Id.run do
  let depMap := relevantShadowDepMap entries
  let dependentMap : Std.HashMap Name (Array Name) :=
    depMap.toArray.foldl
      (fun acc pair =>
        let name := pair.1
        let deps := pair.2
        deps.foldl
          (fun acc dep => acc.insert dep ((acc.getD dep #[]).push name))
          acc)
      {}
  let entryMap : Std.HashMap Name ShadowEntry :=
    entries.foldl (fun acc entry => acc.insert entry.name entry) {}
  let mut indegree : Std.HashMap Name Nat := {}
  for entry in entries do
    indegree := indegree.insert entry.name (depMap.getD entry.name #[]).size
  let mut frontier :=
    (entries.filter fun entry => indegree.getD entry.name 0 == 0).qsort (shadowEntryLt moduleOrder)
  let mut emitted : Std.HashSet Name := {}
  let mut layers : Array (Array ShadowEntry) := #[]
  while !frontier.isEmpty do
    layers := layers.push frontier
    let mut next : Array ShadowEntry := #[]
    for entry in frontier do
      if !emitted.contains entry.name then
        emitted := emitted.insert entry.name
        for dependent in dependentMap.getD entry.name #[] do
          let newDegree := (indegree.getD dependent 0).pred
          indegree := indegree.insert dependent newDegree
          if newDegree == 0 then
            if let some dependentEntry := entryMap.get? dependent then
              next := next.push dependentEntry
    frontier := next.qsort (shadowEntryLt moduleOrder)
  let leftovers :=
    (entries.filter fun entry => !emitted.contains entry.name).qsort (shadowEntryLt moduleOrder)
  if !leftovers.isEmpty then
    layers := layers.push leftovers
  layers

private def flattenShadowLayers (layers : Array (Array ShadowEntry)) : Array ShadowEntry :=
  layers.foldl (fun acc layer => acc ++ layer) #[]

private def shadowLayerMapFromOrderedEntries (entries : Array ShadowEntry) : Std.HashMap Name Nat := Id.run do
  let depMap := relevantShadowDepMap entries
  let mut layers : Std.HashMap Name Nat := {}
  for entry in entries do
    let entryLayer :=
      (depMap.getD entry.name #[]).foldl
        (fun acc dep => max acc (layers.getD dep 1 + 1))
        1
    layers := layers.insert entry.name entryLayer
  layers

private def issueUrlOf (repoUrl? : Option String) (decl : Name) (moduleName : Name) (source? : Option SourceInfo) (hasSorry : Bool) : Option String :=
  repoUrl?.map fun repoUrl =>
    let title := s!"Review: {decl.getString!}"
    let sourceLine :=
      match source? with
      | some src => s!"**Source:** {src.relPath}:{src.line}"
      | none => "**Source:** unavailable"
    let body := String.intercalate "%0A" [
      s!"**Declaration:** `{decl}`",
      s!"**Module:** `{moduleName}`",
      sourceLine,
      s!"**Status:** {if hasSorry then "sorry" else "proved"}",
      "",
      "---",
      "",
      "**Describe the issue:**",
      ""
    ]
    s!"{repoUrl}/issues/new?title={title}&body={body}&labels=exposition-review"

private def sourceUrlOf (repoUrl? : Option String) (source? : Option SourceInfo) : Option String :=
  match repoUrl?, source? with
  | some repoUrl, some src => some s!"{repoUrl}/blob/main/{src.relPath}#L{src.line}"
  | _, _ => none

private def runCoreIO {α : Type} (env : Environment) (x : CoreM α) : IO α := do
  x.toIO'
    { fileName := "<exposition>", fileMap := default, options := {}, currNamespace := .anonymous, openDecls := [] }
    { env := env, ngen := { namePrefix := `_exposition } }

private def findRanges? (env : Environment) (name : Name) : IO (Option DeclarationRanges) := do
  try
    runCoreIO env (findDeclarationRanges? name)
  catch _ =>
    pure none

private def relativeSourcePath (projectDir absPath : System.FilePath) : IO String := do
  let projectDir ← IO.FS.realPath projectDir
  let absPath ← IO.FS.realPath absPath
  let project := projectDir.normalize.toString
  let path := absPath.normalize.toString
  match path.dropPrefix? (project ++ "/") with
  | some rel => pure rel.toString
  | none =>
      match path.dropPrefix? project with
      | some rel => pure <| (rel.toString.dropWhile (· == '/')).toString
      | none => pure path

private def toSourceInfo? (projectDir : System.FilePath) (pkg : Lake.Package) (moduleName : Name) (ranges? : Option DeclarationRanges) : IO (Option SourceInfo) := do
  let some ranges := ranges? | return none
  let some absPath := sourcePathForModule pkg moduleName | return none
  let absPath ← IO.FS.realPath absPath
  let relPath ← relativeSourcePath projectDir absPath
  return some {
    relPath := relPath
    absPath := absPath
    line := ranges.range.pos.line
    endLine := ranges.range.endPos.line
  }

private def shadowManifestPath (shadowDir : System.FilePath) : System.FilePath :=
  shadowDir / "exposition-shadow.json"

private def comparatorManualModule : String :=
  "ComparatorManual"

private def comparatorManualSupportModule : String :=
  "ComparatorManualSupport"

private def comparatorManualMainModule : String :=
  "ComparatorManualMain"

private def comparatorManualExe : String :=
  "comparatorManual"

private def shadowSiteDir (shadowDir : System.FilePath) : System.FilePath :=
  shadowDir / "_out" / "html-multi"

private def shadowSiteIndexPath (shadowDir : System.FilePath) : System.FilePath :=
  shadowSiteDir shadowDir / "index.html"

private def versoShadowGit : String :=
  "https://github.com/leanprover/verso"

private def versoShadowRev : String :=
  "v4.29.0-rc8"

private def versoRevOfToolchain (toolchain : String) : String :=
  match toolchain.trimAscii.toString.splitOn ":" with
  | _ :: version :: _ =>
      let version := version.trimAscii.toString
      if version.isEmpty then versoShadowRev else version
  | _ => versoShadowRev

private def insertShadowTag (acc : Std.HashMap Name (Array String)) (name : Name) (tag : String)
    : Std.HashMap Name (Array String) :=
  let tags := acc.getD name #[]
  if tags.contains tag then
    acc
  else
    acc.insert name (tags.push tag)

private def selectedShadowTags (tfbInfo : TrustedBaseInfo) : Std.HashMap Name (Array String) :=
  let acc :=
    tfbInfo.names.toArray.foldl
      (fun acc name => insertShadowTag acc name "tfb")
      {}
  match tfbInfo.comparator? with
  | none => acc
  | some comparator =>
      comparator.theoremNames.foldl
        (fun acc name => insertShadowTag acc name "solution")
        acc

private def loadShadowEntries (projectDir : System.FilePath) (rootPrefix : Name)
    (pkg : Lake.Package) (env : Environment)
    (selected : Std.HashMap Name (Array String)) : IO (Array ShadowEntry) := do
  let order := (← moduleOrderMap projectDir rootPrefix)
  let mut entries := #[]
  for (name, tags) in selected.toArray.qsort (fun a b => a.1.lt b.1) do
    let some info := env.find? name | continue
    let some moduleName := moduleNameOf env name | continue
    if !shouldExpose env rootPrefix name info then
      continue
    let ranges? ← findRanges? env name
    let source? ← toSourceInfo? projectDir pkg moduleName ranges?
    let some source := source? | continue
    let kind := declKindOf env info name
    let expandedSignature ← ppExprString env info.type
    let displaySignature :=
      (← displaySignatureFromSource kind (some source)).getD <|
        displaySignatureFallback kind name expandedSignature
    let deps := directShadowDeps env name info
    entries := entries.push {
      name
      moduleName
      anchor := name.toString
      kind
      source
      displaySignature
      deps
      tags
    }
  let stableEntries := entries.qsort (shadowEntryLt order)
  let solutionEntries := stableEntries.filter fun entry => entry.tags.contains "solution"
  let solutionNames : Std.HashSet Name :=
    solutionEntries.foldl (fun acc entry => acc.insert entry.name) {}
  let tfbEntries :=
    stableEntries.filter fun entry => entry.tags.contains "tfb" && !solutionNames.contains entry.name
  let otherEntries :=
    stableEntries.filter fun entry =>
      !entry.tags.contains "solution" && !entry.tags.contains "tfb"
  pure <|
    solutionEntries
      ++ flattenShadowLayers (shadowTopologicalLayers order tfbEntries)
      ++ otherEntries

private def anchorStartLine (anchor : String) : String :=
  s!"-- ANCHOR: {anchor}"

private def anchorEndLine (anchor : String) : String :=
  s!"-- ANCHOR_END: {anchor}"

private def snippetFromSourceLines (lines : Array String) (startLine endLine : Nat) : String :=
  if startLine == 0 then
    ""
  else
    let stop := min endLine lines.size
    if startLine > stop then
      ""
    else
      let startIdx := startLine - 1
      let selected := (List.range (stop - startIdx)).map fun i => lines[startIdx + i]!
      String.intercalate "\n" selected

private def renderShadowSnippet (entry : ShadowEntry) (snippet : String)
    : Array String := Id.run do
  let rendered := snippet.trimAsciiEnd.toString
  let mut out : Array String := #[anchorStartLine entry.anchor]
  for line in rendered.splitOn "\n" do
    out := out.push line
  out.push (anchorEndLine entry.anchor)

private def renderShadowFile (sourceText : String)
    (entries : Array ShadowEntry) : String := Id.run do
  let lines := (sourceText.splitOn "\n").toArray
  let sortedEntries :=
    entries.qsort fun a b =>
      if a.source.line == b.source.line then
        if a.source.endLine == b.source.endLine then
          a.name.lt b.name
        else
          a.source.endLine < b.source.endLine
      else
        a.source.line < b.source.line
  let mut out : Array String := #[]
  let mut cursor := 1
  for entry in sortedEntries do
    while cursor < entry.source.line && cursor <= lines.size do
      out := out.push lines[cursor - 1]!
      cursor := cursor + 1
    let snippet := snippetFromSourceLines lines entry.source.line entry.source.endLine
    out := out ++ renderShadowSnippet entry snippet
    cursor := entry.source.endLine + 1
  while cursor <= lines.size do
    out := out.push lines[cursor - 1]!
    cursor := cursor + 1
  String.intercalate "\n" out.toList

private unsafe def generatedShadowFiles (entries : Array ShadowEntry) : IO (Std.HashMap String String) := do
  let mut grouped : Std.HashMap String (Array ShadowEntry) := {}
  for entry in entries do
    grouped := grouped.insert entry.source.relPath ((grouped.getD entry.source.relPath #[]).push entry)
  let mut generated : Std.HashMap String String := {}
  for (relPath, fileEntries) in grouped.toArray do
    let some first := fileEntries[0]? | continue
    let sourceText ← IO.FS.readFile first.source.absPath
    generated := generated.insert relPath (renderShadowFile sourceText fileEntries)
  pure generated

private def copyFileToShadow (src dst : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile dst (← IO.FS.readBinFile src)

/-- Remove all top-level entries in `shadowDir` except `.lake` and `.git`. -/
private def clearShadowDirPreservingLake (shadowDir : System.FilePath) : IO Unit := do
  for entry in (← shadowDir.readDir) do
    if entry.fileName ∈ [".lake", ".git"] then
      continue
    let ftype ← entry.path.metadata
    match ftype.type with
    | .dir => IO.FS.removeDirAll entry.path
    | _    => IO.FS.removeFile entry.path

/-- Compute the transitive import closure within the project for a set of starting modules. -/
private partial def moduleImportClosure (projectDir : System.FilePath) (rootPrefix : Name)
    (startModules : Array Name) : IO (Std.HashSet Name) := do
  let rec go (stack : List Name) (visited : Std.HashSet Name) : IO (Std.HashSet Name) := do
    match stack with
    | [] => return visited
    | mod :: rest =>
      if visited.contains mod then
        go rest visited
      else
        let visited := visited.insert mod
        let text? ← readFileIfExists (moduleSourcePath projectDir mod)
        match text? with
        | none => go rest visited
        | some contents =>
          let imports := (contents.splitOn "\n").filterMap parseImportedModule?
          let newImports := imports.filter fun imported =>
            imported != mod && hasPrefixName imported rootPrefix && !visited.contains imported
          go (newImports ++ rest) visited
  go startModules.toList {}

/-- Copy only the modules in `modules` into the shadow directory, using annotated
    content from `generatedFiles` when available. -/
private def copySelectiveModules (projectDir shadowDir : System.FilePath)
    (modules : Std.HashSet Name)
    (generatedFiles : Std.HashMap String String) : IO Unit := do
  for mod in modules.toArray do
    let relPath := mod.toString.replace "." "/" ++ ".lean"
    let srcPath := projectDir / relPath
    let dstPath := shadowDir / relPath
    if let some parent := dstPath.parent then
      IO.FS.createDirAll parent
    if let some generated := generatedFiles[relPath]? then
      IO.FS.writeFile dstPath generated
    else if ← srcPath.pathExists then
      copyFileToShadow srcPath dstPath

/-- Copy essential config files (lakefile, toolchain, manifest) from project to shadow. -/
private def copyShadowConfigFiles (projectDir shadowDir : System.FilePath) : IO Unit := do
  for name in ["lakefile.toml", "lakefile.lean", "lean-toolchain", "lake-manifest.json"] do
    let src := projectDir / name
    if ← src.pathExists then
      copyFileToShadow src (shadowDir / name)

private def writeShadowManifest (shadowDir : System.FilePath) (tfbInfo : TrustedBaseInfo)
    (entries : Array ShadowEntry) : IO Unit := do
  let manifest : ShadowManifest := {
    comparator? := tfbInfo.comparator?
    entries
  }
  IO.FS.writeFile (shadowManifestPath shadowDir) (Json.pretty (ToJson.toJson manifest))

private def hasShadowTag (entry : ShadowEntry) (tag : String) : Bool :=
  entry.tags.contains tag

private def markdownHeading (level : Nat) (title : String) : String :=
  s!"{String.ofList (List.replicate level '#')} {title}"

private def shadowTagForEntry (entry : ShadowEntry) : String :=
  s!"shadow-entry-{slugify entry.moduleName.toString}-{slugify entry.name.toString}-{entry.source.line}-{entry.source.endLine}"

private def appendTaggedHeading (lines : Array String) (level : Nat) (title tag : String) : Array String :=
  lines
    |>.push (markdownHeading level title)
    |>.push "%%%"
    |>.push s!"tag := \"{tag}\""
    |>.push "%%%"
    |>.push ""

private def codeFenceFor (snippet : String) : String :=
  let rec scan (chars : List Char) (run best : Nat) : Nat :=
    match chars with
    | [] => max run best
    | '`' :: rest => scan rest (run + 1) best
    | _ :: rest => scan rest 0 (max run best)
  String.ofList <| List.replicate (max 3 (scan snippet.toList 0 0 + 1)) '`'

private def renderShadowCodeBlock (entry : ShadowEntry) (snippet : String) : Array String :=
  let fence := codeFenceFor snippet
  let defSite := if hasShadowTag entry "tfb" then " -defSite" else ""
  let proofKind := entry.kind == .theorem || entry.kind == .opaque || entry.kind == .instance
  let blockType := if proofKind then "collapsibleModule" else "module"
  let config := s!"{fence}{blockType} (module := {entry.moduleName}) (anchor := {entry.anchor}){defSite}"
  #[
    config,
    snippet,
    fence,
    ""
  ]

private def appendShadowEntryBlock (lines : Array String) (level : Nat) (entry : ShadowEntry)
    (repoUrl? : Option String := none) : IO (Array String) := do
  let snippet := (← readSourceSnippet entry.source).trimAsciiEnd.toString
  let sourceLink := match sourceUrlOf repoUrl? (some entry.source) with
    | some url => s!" | [Source]({url})"
    | none => ""
  let issueLink := match issueUrlOf repoUrl? entry.name entry.moduleName (some entry.source) false with
    | some url => s!" | [Open Issue]({url})"
    | none => ""
  pure <|
    (appendTaggedHeading lines level s!"`{entry.name}`" (shadowTagForEntry entry))
      ++ #[
        s!"`{entry.kind.label}` | `{entry.moduleName}`{sourceLink}{issueLink}",
        ""
      ]
      ++ #[
        "```declAnchorEmbed",
        entry.name.toString,
        "```",
        ""
      ]
      ++ renderShadowCodeBlock entry snippet

private def moduleSlug (rootPrefix : Name) (moduleName : Name) : String :=
  slugify (moduleName.toString.dropPrefix s!"{rootPrefix}.").toString

private def buildShadowGraphData (rootPrefix : Name) (entries : Array ShadowEntry) : GraphData := Id.run do
  let entryNames : Std.HashSet Name := entries.foldl (fun s e => s.insert e.name) {}
  let nodes := entries.map fun entry => {
    id := entry.name.toString
    label := entry.name.getString!
    kind := entry.kind.label
    status := "clean"
    groupKey := entry.moduleName.toString
    moduleName := entry.moduleName.toString
    -- Link to the split module page. The module slug matches what split_pages.py generates.
    href := s!"{moduleSlug rootPrefix entry.moduleName}/"
  }
  let mut edges : Array GraphEdge := #[]
  for entry in entries do
    for dep in entry.deps do
      if entryNames.contains dep then
        edges := edges.push { source := entry.name.toString, target := dep.toString }
  return { nodes, edges }

private def renderComparatorManual (_env : Environment) (tfbInfo : TrustedBaseInfo)
    (entries : Array ShadowEntry) (rootPrefix : Name) (repoUrl? : Option String := none) : IO String := do
  let some comparator := tfbInfo.comparator?
    | return String.intercalate "\n" [
        "import VersoManual",
        "import BridgelandStability",
        s!"import {comparatorManualSupportModule}",
        "",
        "open Verso.Genre Manual",
        "open Verso.Code.External",
        s!"open {comparatorManualSupportModule}",
        "",
        "set_option maxHeartbeats 2000000",
        "set_option verso.exampleProject \".\"",
        "",
        s!"#doc (Manual) \"{comparatorManualModule}\" =>",
        "This generated manual requires a comparator configuration."
      ]
  let solutionEntries :=
    entries.filter fun entry => hasShadowTag entry "solution"
  let tfbEntries :=
    entries.filter fun entry => hasShadowTag entry "tfb"
  let solutionNames : Std.HashSet Name :=
    solutionEntries.foldl (fun acc entry => acc.insert entry.name) {}
  let tfbOnlyEntries :=
    tfbEntries.filter fun entry => !solutionNames.contains entry.name
  -- Collect per-module declaration counts for the overview
  let mut moduleCounts : Std.HashMap Name Nat := {}
  for entry in tfbOnlyEntries do
    moduleCounts := moduleCounts.insert entry.moduleName ((moduleCounts.getD entry.moduleName 0) + 1)
  let mut lines : Array String := #[
    "import VersoManual",
    s!"import {comparator.solutionModule}",
    s!"import {comparatorManualSupportModule}",
    "",
    "open Verso.Genre Manual",
    "open Verso.Code.External",
    s!"open {comparatorManualSupportModule}",
    "",
    "set_option pp.rawOnError true",
    "set_option maxHeartbeats 2000000",
    "set_option verso.exampleProject \".\"",
    "",
    let rootName := rootPrefix.toString
    s!"#doc (Manual) \"{rootName} Comparator Manual\" =>",
    "%%%",
    "htmlSplit := .never",
    "%%%",
    "",
    "# Overview",
    "",
    "![comparator](badge/comparator.svg)",
    ""
  ]
  if let some url := repoUrl? then
    lines := lines.push s!"Repository: [{url}]({url})"
    lines := lines.push ""
  lines := lines ++ #[
    "This manual presents the comparator view of the formalization.",
    s!"It was generated mechanically from the trusted formalization base walk rooted at the comparator target theorem in `{comparator.solutionModule}`.",
    s!"The formalization covers *{entries.size}* declarations across *{moduleCounts.size}* modules.",
    ""
  ]
  -- Solution theorem (## stays on overview page)
  if !solutionEntries.isEmpty then
    for entry in solutionEntries do
      lines ← appendShadowEntryBlock lines 2 entry repoUrl?
  -- Dependency graph (## stays on overview page)
  let graphData := buildShadowGraphData rootPrefix entries
  let graphJson := Json.compress (ToJson.toJson graphData)
  lines := lines.push "## Dependency graph"
  lines := lines.push ""
  lines := lines.push "Click a node to navigate to its declaration."
  lines := lines.push ""
  let graphFence := codeFenceFor graphJson
  lines := lines.push s!"{graphFence}graphEmbed"
  lines := lines.push graphJson
  lines := lines.push graphFence
  lines := lines.push ""
  -- Module pages: each # creates a separate page (TFB entries only, solution is on overview)
  -- Order modules by minimum dependency layer
  let layerMap := shadowLayerMapFromOrderedEntries tfbOnlyEntries
  let mut byModule : Std.HashMap Name (Array ShadowEntry) := {}
  let mut moduleMinLayer : Std.HashMap Name Nat := {}
  for entry in tfbOnlyEntries do
    byModule := byModule.insert entry.moduleName ((byModule.getD entry.moduleName #[]).push entry)
    let layer := layerMap.getD entry.name 999
    let prev := moduleMinLayer.getD entry.moduleName 999
    if layer < prev then
      moduleMinLayer := moduleMinLayer.insert entry.moduleName layer
  let sortedModules := byModule.toArray.qsort fun a b =>
    let la := moduleMinLayer.getD a.1 999
    let lb := moduleMinLayer.getD b.1 999
    if la == lb then a.1.lt b.1 else la < lb
  for (modName, modEntries) in sortedModules do
    let kinds := modEntries.map (·.kind.label) |>.toList.eraseDups
    let kindSummary := String.intercalate ", " kinds
    -- Plain text heading (no backticks) so TOC font matches Overview
    let shortName := (modName.toString.dropPrefix s!"{rootPrefix}.").toString
    lines := lines.push s!"# {shortName}"
    lines := lines.push ""
    lines := lines.push s!"Module `{modName}` — *{modEntries.size}* declarations ({kindSummary})"
    lines := lines.push ""
    for entry in modEntries do
      lines ← appendShadowEntryBlock lines 2 entry repoUrl?
  pure <| String.intercalate "\n" lines.toList

private def renderComparatorManualMain : String :=
  String.intercalate "\n" [
    "import VersoManual",
    s!"import {comparatorManualModule}",
    "",
    "open Verso.Genre Manual",
    "",
    s!"def main := manualMain (%doc {comparatorManualModule})"
  ]

private def renderComparatorManualSupport : String :=
  String.intercalate "\n" [
    "import VersoManual",
    "import SubVerso.Compat",
    "import SubVerso.Highlighting",
    "import Verso.Code.External",
    "",
    "open Lean",
    "open Verso Doc Elab ArgParse Genre.Manual",
    "open Verso.Code.External",
    "open ExternalCode",
    "open SubVerso.Highlighting",
    "",
    s!"namespace {comparatorManualSupportModule}",
    "",
    "/-- True when the keyword name identifies a declaration-value construct",
    "    (`where` or `|` at the declaration level). -/",
    "private def isDeclValueKeyword (name : Name) : Bool :=",
    "  match name with",
    "  | .str _ \"whereStructInst\" => true",
    "  | .str _ \"declValEqns\"     => true",
    "  | _ => false",
    "",
    "/-- Walk the Highlighted tree and find the character offset where the",
    "    declaration body begins. Matches:",
    "    1. Keyword tokens named `whereStructInst` or `declValEqns`",
    "    2. Unknown tokens with content `:=` at bracket depth 0",
    "    Returns the character count of the signature prefix. -/",
    "private def findDeclBodyOffset (hl : Highlighted) : Option Nat :=",
    "  -- depth tracks bracket nesting: only `:=` at depth 0 is the declaration body",
    "  let rec go (hl : Highlighted) (offset depth : Nat) : Option Nat × Nat × Nat :=",
    "    match hl with",
    "    | .token tok =>",
    "        let len := tok.content.length",
    "        -- Check for keyword-identified declaration values (where, |)",
    "        let foundKeyword := match tok.kind with",
    "          | .keyword (some name) _ _ => isDeclValueKeyword name",
    "          | _ => false",
    "        if foundKeyword then (some offset, offset + len, depth)",
    "        else",
    "          -- Check for `:=` at bracket depth 0 (unknown kind in SubVerso)",
    "          let foundAssign := depth == 0 && tok.content == \":=\"",
    "          if foundAssign then (some offset, offset + len, depth)",
    "          else",
    "            -- Track bracket depth",
    "            let depth := match tok.content with",
    "              | \"(\" | \"{\" | \"[\" | \"⦃\" | \"⟨\" => depth + 1",
    "              | \")\" | \"}\" | \"]\" | \"⦄\" | \"⟩\" => depth - 1",
    "              | _ => depth",
    "            (none, offset + len, depth)",
    "    | .text s => (none, offset + s.length, depth)",
    "    | .unparsed s => (none, offset + s.length, depth)",
    "    | .point _ _ => (none, offset, depth)",
    "    | .span _ inner => go inner offset depth",
    "    | .tactics _ _ _ inner => go inner offset depth",
    "    | .seq hs =>",
    "        let rec loop (items : List Highlighted) (offset depth : Nat) : Option Nat × Nat × Nat :=",
    "          match items with",
    "          | [] => (none, offset, depth)",
    "          | h :: t =>",
    "              let (result, offset', depth') := go h offset depth",
    "              match result with",
    "              | some _ => (result, offset', depth')",
    "              | none   => loop t offset' depth'",
    "        loop hs.toList offset depth",
    "  (go hl 0 0).1",
    "",
    "private def takeExact (remaining : Nat) (hl : Highlighted) : Highlighted × Nat :=",
    "  match hl with",
    "  | .point kind info =>",
    "      (.point kind info, remaining)",
    "  | .text s =>",
    "      if remaining >= s.length then",
    "        (.text s, remaining - s.length)",
    "      else",
    "        (.text (SubVerso.Compat.String.take s remaining), 0)",
    "  | .token tok =>",
    "      if remaining >= tok.content.length then",
    "        (.token tok, remaining - tok.content.length)",
    "      else",
    "        (.text (SubVerso.Compat.String.take tok.content remaining), 0)",
    "  | .unparsed s =>",
    "      if remaining >= s.length then",
    "        (.unparsed s, remaining - s.length)",
    "      else",
    "        (.text (SubVerso.Compat.String.take s remaining), 0)",
    "  | .span info inner =>",
    "      let (inner', remaining') := takeExact remaining inner",
    "      (if inner'.isEmpty then .empty else .span info inner', remaining')",
    "  | .tactics info startPos endPos inner =>",
    "      let (inner', remaining') := takeExact remaining inner",
    "      (if inner'.isEmpty then .empty else .tactics info startPos endPos inner', remaining')",
    "  | .seq hs =>",
    "      let rec loop (remaining : Nat) (todo : List Highlighted) (acc : Highlighted) : Highlighted × Nat :=",
    "        match todo with",
    "        | [] => (acc, remaining)",
    "        | h :: t =>",
    "            let (h', remaining') := takeExact remaining h",
    "            let acc := acc ++ h'",
    "            if remaining' == 0 then",
    "              (acc, 0)",
    "            else",
    "              loop remaining' t acc",
    "      loop remaining hs.toList .empty",
    "",
    "-- Custom block that renders its child inside a collapsed <details> element.",
    "def Block.collapsibleProof : Genre.Manual.Block where",
    "  name := `ComparatorManualSupport.Block.collapsibleProof",
    "",
    "open Verso.Output Html in",
    "@[block_extension Block.collapsibleProof]",
    "def collapsibleProof.descr : BlockDescr where",
    "  traverse _ _ _ := pure none",
    "  toTeX := none",
    "  extraCss := [",
    "    -- Warm academic theme from the exposition site",
    "    \":root { --site-ink: #193428; --site-muted: #5a655f; --site-warm: #fbf7ef; --site-card: #fffdf8; --site-accent: #a14d2a; --site-border: #d8cdbd; --verso-structure-color: #154734; --verso-toc-background-color: #f4efe5; --verso-selected-color: #f0dcc8; --verso-text-font-family: 'Iowan Old Style', 'Palatino Linotype', 'Book Antiqua', serif; --verso-structure-font-family: 'Avenir Next Condensed', 'Gill Sans', sans-serif; --verso-code-font-family: 'Iosevka Term', 'JetBrains Mono', monospace; }\",",
    "    \"body { color: var(--site-ink); }\",",
    "    -- Code block styling",
    "    \".hl.lean.block { background: #faf4e8; border: 1px solid #eadfcf; border-radius: 10px; padding: 0.85rem 1rem; box-shadow: inset 0 1px 0 rgba(255,255,255,0.7); }\",",
    "    -- Collapsible proof styling",
    "    \"details.collapsible-proof > summary { cursor: pointer; color: var(--site-muted, #666); font-style: italic; margin: 0.3em 0; user-select: none; font-family: var(--verso-structure-font-family, sans-serif); font-size: 0.88rem; }\",",
    "    \"details.collapsible-proof > summary:hover { color: var(--site-accent, #a14d2a); }\",",
    "    -- Section heading accents",
    "    \"main section > h2, main section > h3, main section > h4 { border-left: 4px solid var(--verso-structure-color, #154734); padding-left: 0.6rem; }\",",
    "    \".decl-anchor { height: 0; margin: 0; padding: 0; }\"]",
    "  toHtml := some fun _goI goB _id _data blocks => do",
    "    let inner ← blocks.mapM (goB ·)",
    "    pure {{ <details class=\"collapsible-proof\"><summary>\"Show proof\"</summary>{{inner}}</details> }}",
    "",
    "-- Invisible anchor block that registers a constant in the docstring domain",
    "-- for cross-reference linking. Renders only an empty anchor div.",
    "def Block.declAnchor (declName : String) : Genre.Manual.Block where",
    "  name := `ComparatorManualSupport.Block.declAnchor",
    "  data := Lean.toJson declName",
    "",
    "open Verso.Output Html in",
    "@[block_extension Block.declAnchor]",
    "def declAnchor.descr : BlockDescr where",
    "  traverse id info _ := do",
    "    let some declName := info.getStr? |>.toOption | pure none",
    "    let path ← (·.path) <$> read",
    "    let _ ← Verso.Genre.Manual.externalTag id path declName",
    "    modify fun st => st.saveDomainObject Verso.Genre.Manual.docstringDomain declName id",
    "    pure none",
    "  toTeX := none",
    "  toHtml := some fun _goI _goB id _info _blocks => open Verso.Output Html Verso.Doc.Html in do",
    "    let xref ← HtmlT.state",
    "    let idAttr := xref.htmlId id",
    "    pure {{ <div class=\"decl-anchor\" {{idAttr}}></div> }}",
    "",
    "private abbrev ManualDocBlock := Verso.Doc.Block Verso.Genre.Manual",
    "",
    "def wrapDeclAnchor (declName : String) : ManualDocBlock :=",
    "  .other (Block.declAnchor declName) #[]",
    "",
    "private def stringTail (s : String) (n : Nat) : String :=",
    "  String.ofList (s.toList.drop n)",
    "",
    "private def dropExact (n : Nat) (hl : Highlighted) : Highlighted :=",
    "  let rec go (remaining : Nat) (hl : Highlighted) : Highlighted × Nat :=",
    "    match hl with",
    "    | .point _ _ => (.empty, remaining)",
    "    | .text s =>",
    "        if remaining >= s.length then (.empty, remaining - s.length)",
    "        else (.text (stringTail s remaining), 0)",
    "    | .token tok =>",
    "        if remaining >= tok.content.length then (.empty, remaining - tok.content.length)",
    "        else (.token { tok with content := stringTail tok.content remaining }, 0)",
    "    | .unparsed s =>",
    "        if remaining >= s.length then (.empty, remaining - s.length)",
    "        else (.unparsed (stringTail s remaining), 0)",
    "    | .span info inner =>",
    "        let (inner', remaining') := go remaining inner",
    "        (if inner'.isEmpty then .empty else .span info inner', remaining')",
    "    | .tactics info startPos endPos inner =>",
    "        let (inner', remaining') := go remaining inner",
    "        (if inner'.isEmpty then .empty else .tactics info startPos endPos inner', remaining')",
    "    | .seq hs =>",
    "        let rec loop (remaining : Nat) (todo : List Highlighted) : Highlighted × Nat :=",
    "          match todo with",
    "          | [] => (.empty, remaining)",
    "          | h :: t =>",
    "              if remaining == 0 then (.seq (h :: t).toArray, 0)",
    "              else",
    "                let (tail, remaining') := go remaining h",
    "                if remaining' == 0 then",
    "                  -- h spans the boundary; include its tail + rest",
    "                  if tail.isEmpty then (.seq t.toArray, 0)",
    "                  else (.seq (tail :: t).toArray, 0)",
    "                else",
    "                  loop remaining' t",
    "        loop remaining hs.toList",
    "  (go n hl).1",
    "",
    "-- Dependency graph block: renders a D3 force-directed graph from embedded JSON data.",
    "def Block.dependencyGraph (graphJson : String) : Genre.Manual.Block where",
    "  name := `ComparatorManualSupport.Block.dependencyGraph",
    "  data := Lean.Json.str graphJson",
    "",
    "open Verso.Output Html in",
    "@[block_extension Block.dependencyGraph]",
    "def dependencyGraph.descr : BlockDescr where",
    "  traverse _ _ _ := pure none",
    "  toTeX := none",
    "  extraJs := [\"document.addEventListener('DOMContentLoaded',function(){var el=document.getElementById('graph-data');if(!el)return;var data=JSON.parse(el.textContent);var root=document.getElementById('graph-root');if(!root)return;var w=root.clientWidth,h=600;var svg=document.createElementNS('http://www.w3.org/2000/svg','svg');svg.setAttribute('width','100%');svg.setAttribute('height',h);svg.setAttribute('viewBox','0 0 '+w+' '+h);root.appendChild(svg);var nodeMap={};data.nodes.forEach(function(n){nodeMap[n.id]=n;});var groups=Array.from(new Set(data.nodes.map(function(n){return n.groupKey})));var colors=['#3d6b59','#b96d2d','#7a4e7a','#2f5f87','#8a3b3b','#5f6f2e','#9a5b8f','#6b5041'];function groupColor(g){return colors[groups.indexOf(g)%colors.length]}var sim=d3.forceSimulation(data.nodes).force('link',d3.forceLink(data.edges).id(function(d){return d.id}).distance(80).strength(0.2)).force('charge',d3.forceManyBody().strength(-210)).force('center',d3.forceCenter(w/2,h/2)).force('collide',d3.forceCollide(22));var g=document.createElementNS('http://www.w3.org/2000/svg','g');svg.appendChild(g);var linkG=document.createElementNS('http://www.w3.org/2000/svg','g');g.appendChild(linkG);var nodeG=document.createElementNS('http://www.w3.org/2000/svg','g');g.appendChild(nodeG);data.edges.forEach(function(e){var line=document.createElementNS('http://www.w3.org/2000/svg','line');line.setAttribute('stroke','#b8b0a4');line.setAttribute('stroke-opacity','0.6');line.setAttribute('stroke-width','1.2');line._data=e;linkG.appendChild(line)});data.nodes.forEach(function(n){var ng=document.createElementNS('http://www.w3.org/2000/svg','g');ng.setAttribute('cursor','pointer');var c=document.createElementNS('http://www.w3.org/2000/svg','circle');c.setAttribute('r','10');c.setAttribute('fill',groupColor(n.groupKey));c.setAttribute('stroke','#1f6b4b');c.setAttribute('stroke-width','2');ng.appendChild(c);var t=document.createElementNS('http://www.w3.org/2000/svg','text');t.setAttribute('dx','14');t.setAttribute('dy','4');t.setAttribute('font-size','11');t.setAttribute('fill','#333');t.textContent=n.label;ng.appendChild(t);ng._data=n;ng.addEventListener('click',function(){if(n.href)window.location.href=n.href});nodeG.appendChild(ng)});sim.on('tick',function(){linkG.childNodes.forEach(function(l){l.setAttribute('x1',l._data.source.x);l.setAttribute('y1',l._data.source.y);l.setAttribute('x2',l._data.target.x);l.setAttribute('y2',l._data.target.y)});nodeG.childNodes.forEach(function(ng){var d=ng._data;ng.setAttribute('transform','translate('+d.x+','+d.y+')')})});var zoom=d3.zoom().scaleExtent([0.25,4]).on('zoom',function(e){g.setAttribute('transform',e.transform)});d3.select(svg).call(zoom)})\"]",
    "  extraCss := [\"#graph-root { background: var(--site-card, #fffdf8); border: 1px solid var(--site-border, #d8cdbd); border-radius: 14px; min-height: 620px; padding: 1rem; margin: 1rem 0; } #graph-root svg { display: block; }\"]",
    "  toHtml := some fun _goI _goB _id info _blocks => open Output.Html in do",
    "    let graphJson := info.getStr? |>.toOption |>.getD \"{}\"",
    "    pure {{ <div id=\"graph-root\"><script id=\"graph-data\" type=\"application/json\">{{graphJson}}</script><script src=\"https://d3js.org/d3.v7.min.js\"></script></div> }}",
    "",
    "def wrapCollapsible (body : ManualDocBlock) : ManualDocBlock :=",
    "  .other Block.collapsibleProof #[body]",
    "",
    "def wrapDependencyGraph (graphJson : String) : ManualDocBlock :=",
    "  .other (Block.dependencyGraph graphJson) #[]",
    "",
    "/-- Embed an interactive dependency graph. The code block body is the JSON data. -/",
    "@[code_block_expander graphEmbed]",
    "public meta def graphEmbed : CodeBlockExpander",
    "  | _args, code => do",
    "    let json := code.getString",
    "    pure #[← ``(wrapDependencyGraph $(quote json))]",
    "",
    "/-- Register a declaration name as a cross-reference anchor. Renders nothing. -/",
    "@[code_block_expander declAnchorEmbed]",
    "public meta def declAnchorEmbed : CodeBlockExpander",
    "  | _args, code => do",
    "    let declName := code.getString.trim",
    "    pure #[← ``(wrapDeclAnchor $(quote declName))]",
    "",
    "/-- Render an anchored external Lean block with the proof body inside",
    "    a collapsed `<details>` element. The signature is always visible. -/",
    "@[code_block_expander collapsibleModule]",
    "public meta def collapsibleModule : CodeBlockExpander",
    "  | args, _code => withTraceNode `Elab.Verso (fun _ => pure m!\"collapsibleModule\") <| do",
    "    let cfg@{ module := moduleName, project, anchor?, showProofStates := _, defSite := _ } ← parseThe CodeContext args",
    "    withAnchored project moduleName anchor? fun hl => do",
    "      match findDeclBodyOffset hl with",
    "      | some offset =>",
    "          let headHl := (takeExact offset hl).1",
    "          let bodyHl := dropExact offset hl",
    "          let headBlock ← ``(leanBlock $(quote headHl) $(quote cfg.toCodeConfig))",
    "          let bodyBlock ← ``(leanBlock $(quote bodyHl) $(quote cfg.toCodeConfig))",
    "          pure #[headBlock, ← ``(wrapCollapsible $bodyBlock)]",
    "      | none =>",
    "          pure #[← ``(leanBlock $(quote hl) $(quote cfg.toCodeConfig))]",
    "",
    s!"end {comparatorManualSupportModule}"
  ]

private def writeComparatorManualFiles (env : Environment) (shadowDir : System.FilePath) (tfbInfo : TrustedBaseInfo)
    (entries : Array ShadowEntry) (rootPrefix : Name) (repoUrl? : Option String := none) : IO Unit := do
  IO.FS.writeFile (shadowDir / s!"{comparatorManualSupportModule}.lean") renderComparatorManualSupport
  IO.FS.writeFile (shadowDir / s!"{comparatorManualModule}.lean") (← renderComparatorManual env tfbInfo entries rootPrefix repoUrl?)
  IO.FS.writeFile (shadowDir / s!"{comparatorManualMainModule}.lean") renderComparatorManualMain

private def insertBeforeMarkerOrAppend (contents marker block : String) : String :=
  if contents.contains marker then
    let parts := contents.splitOn marker
    match parts with
    | first :: second :: rest =>
        first ++ block ++ marker ++ String.intercalate marker (second :: rest)
    | _ => contents ++ block
  else
    contents ++ block

private def ensureVersoInShadowProject (shadowDir : System.FilePath) : IO Unit := do
  let lakeToml := shadowDir / "lakefile.toml"
  let lakeLean := shadowDir / "lakefile.lean"
  let toolchainFile := shadowDir / "lean-toolchain"
  let versoRev ←
    if ← toolchainFile.pathExists then
      pure <| versoRevOfToolchain (← IO.FS.readFile toolchainFile)
    else
      pure versoShadowRev
  if ← lakeToml.pathExists then
    let mut contents ← IO.FS.readFile lakeToml
    if !contents.contains "name = \"verso\"" then
      let versoBlock := String.intercalate "\n" [
        "",
        "[[require]]",
        "name = \"verso\"",
        s!"git = \"{versoShadowGit}\"",
        s!"rev = \"{versoRev}\"",
        ""
      ]
      contents := insertBeforeMarkerOrAppend contents "[[require]]\nname = \"mathlib\"" versoBlock
    if !contents.contains s!"name = \"{comparatorManualModule}\"" then
      contents := contents ++ String.intercalate "\n" [
        "",
        "[[lean_lib]]",
        s!"name = \"{comparatorManualModule}\"",
        "srcDir = \".\"",
        ""
      ]
    if !contents.contains s!"name = \"{comparatorManualSupportModule}\"" then
      contents := contents ++ String.intercalate "\n" [
        "",
        "[[lean_lib]]",
        s!"name = \"{comparatorManualSupportModule}\"",
        "srcDir = \".\"",
        ""
      ]
    if !contents.contains s!"name = \"{comparatorManualExe}\"" then
      contents := contents ++ String.intercalate "\n" [
        "",
        "[[lean_exe]]",
        s!"name = \"{comparatorManualExe}\"",
        s!"root = \"{comparatorManualMainModule}\"",
        "supportInterpreter = true",
        ""
      ]
    IO.FS.writeFile lakeToml contents
  else if ← lakeLean.pathExists then
    let mut contents ← IO.FS.readFile lakeLean
    if !contents.contains "require verso from git" then
      let versoBlock := String.intercalate "\n" [
        "",
        s!"require verso from git \"{versoShadowGit}\" @ \"{versoRev}\"",
        ""
      ]
      contents := insertBeforeMarkerOrAppend contents "require mathlib" versoBlock
    if !contents.contains s!"lean_lib {comparatorManualModule}" then
      contents := contents ++ String.intercalate "\n" [
        "",
        s!"lean_lib {comparatorManualModule} where",
        "  srcDir := \".\"",
        ""
      ]
    if !contents.contains s!"lean_lib {comparatorManualSupportModule}" then
      contents := contents ++ String.intercalate "\n" [
        "",
        s!"lean_lib {comparatorManualSupportModule} where",
        "  srcDir := \".\"",
        ""
      ]
    if !contents.contains s!"lean_exe {comparatorManualExe}" then
      contents := contents ++ String.intercalate "\n" [
        "",
        s!"lean_exe {comparatorManualExe} where",
        s!"  root := `{comparatorManualMainModule}",
        "  supportInterpreter := true",
        ""
      ]
    IO.FS.writeFile lakeLean contents

private def renderProcessCommand (cmd : String) (args : Array String) : String :=
  String.intercalate " " <| cmd :: args.toList

private def printProcessOutput (out : IO.Process.Output) : IO Unit := do
  if !out.stdout.isEmpty then
    IO.print out.stdout
  if !out.stderr.isEmpty then
    IO.eprint out.stderr

private def runShadowCommand (shadowDir : System.FilePath) (cmd : String) (args : Array String) : IO Unit := do
  let display := renderProcessCommand cmd args
  IO.println s!"[shadow] {display}"
  let out ← IO.Process.output {
    cmd := cmd
    args := args
    cwd := some shadowDir
  }
  printProcessOutput out
  if out.exitCode != 0 then
    throw <| IO.userError s!"shadow command failed ({display})"

private def missingCacheExecutable (out : IO.Process.Output) : Bool :=
  let text := out.stdout ++ out.stderr
  text.contains "unknown executable cache"
    || text.contains "unknown executable 'cache'"
    || text.contains "unknown executable `cache`"

private def pullShadowCache (shadowDir : System.FilePath) : IO Unit := do
  let display := "lake exe cache get"
  IO.println s!"[shadow] {display}"
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["exe", "cache", "get"]
    cwd := some shadowDir
  }
  printProcessOutput out
  if out.exitCode == 0 then
    return
  if missingCacheExecutable out then
    IO.println "[shadow] skipping cache pull; no `cache` executable is defined in the shadow workspace."
    return
  throw <| IO.userError s!"shadow command failed ({display})"

private def updateShadowDependencies (shadowDir : System.FilePath) : IO Unit := do
  let manifest := shadowDir / "lake-manifest.json"
  if ← manifest.pathExists then
    runShadowCommand shadowDir "lake" #["update", "verso"]
  else
    runShadowCommand shadowDir "lake" #["update"]

private def splitShadowPages (shadowDir : System.FilePath) : IO Unit := do
  let htmlDir := shadowSiteDir shadowDir
  let scriptPath := (← IO.currentDir) / shadowDir / "_split_pages.py"
  -- Find the split script from the exposition project root
  let exePath ← IO.appPath
  let projectRoot := exePath.parent.getD "." |>.parent.getD "." |>.parent.getD "." |>.parent.getD "."
  let srcScript := projectRoot / "scripts" / "split_pages.py"
  if ← srcScript.pathExists then
    IO.FS.writeBinFile scriptPath (← IO.FS.readBinFile srcScript)
  else
    throw <| IO.userError s!"split_pages.py not found at {srcScript}; cannot split pages"
  IO.println s!"[shadow] splitting pages: {htmlDir}"
  let out ← IO.Process.output {
    cmd := "python3"
    args := #[scriptPath.toString, htmlDir.toString]
  }
  printProcessOutput out
  if out.exitCode != 0 then
    IO.eprintln "[shadow] warning: page splitting failed, keeping single-page output"

private def buildShadowSite (shadowDir : System.FilePath) : IO Unit := do
  updateShadowDependencies shadowDir
  pullShadowCache shadowDir
  runShadowCommand shadowDir "lake" #["build", comparatorManualExe]
  runShadowCommand shadowDir "lake" #["exe", comparatorManualExe]
  splitShadowPages shadowDir


private unsafe def writeComparatorShadow (projectDir shadowDir : System.FilePath)
    (rootPrefix : Name) (env : Environment) (tfbInfo : TrustedBaseInfo)
    (entries : Array ShadowEntry) (repoUrl? : Option String := none) : IO Unit := do
  if ← shadowDir.pathExists then
    clearShadowDirPreservingLake shadowDir
  else
    IO.FS.createDirAll shadowDir
  let entryModules := entries.foldl (fun acc e => acc.insert e.moduleName) ({} : Std.HashSet Name)
  let closure ← moduleImportClosure projectDir rootPrefix entryModules.toArray
  IO.println s!"[shadow] module closure: {closure.size} modules"
  let generatedFiles ← generatedShadowFiles entries
  copySelectiveModules projectDir shadowDir closure generatedFiles
  copyShadowConfigFiles projectDir shadowDir
  ensureVersoInShadowProject shadowDir
  writeShadowManifest shadowDir tfbInfo entries
  writeComparatorManualFiles env shadowDir tfbInfo entries rootPrefix repoUrl?
  buildShadowSite shadowDir

private def detectRepoUrl (projectDir : System.FilePath) : IO (Option String) := do
  let result ← IO.Process.output {
    cmd := "git"
    args := #["remote", "get-url", "origin"]
    cwd := some projectDir
  }
  if result.exitCode != 0 then return none
  let url := result.stdout.trimAscii.toString
  if url.isEmpty then return none
  -- Convert SSH URLs (git@github.com:owner/repo.git) to HTTPS
  if url.startsWith "git@" then
    let url := (url.dropPrefix "git@").toString
    let url := url.replace ":" "/"
    let url := if url.endsWith ".git" then (url.dropEnd 4).toString else url
    return some s!"https://{url}"
  -- Strip trailing .git from HTTPS URLs
  let url := if url.endsWith ".git" then (url.dropEnd 4).toString else url
  return some url

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
  let cfg ← Lake.MonadError.runEIO <| Lake.mkLoadConfig {
    elanInstall?
    leanInstall?
    lakeInstall?
    rootDir := projectDir
  }
  let ws? ← Lake.loadWorkspace cfg |>.toBaseIO
  match ws? with
  | some ws => pure ws
  | none => throw <| IO.userError s!"failed to load Lake workspace at {projectDir}"

private def importRoots (ws : Lake.Workspace) (excludeLibs : Array Name) : Array Import := Id.run do
  let mut imports := #[]
  for lib in ws.root.leanLibs do
    if excludeLibs.contains lib.name then
      continue
    for root in lib.config.roots do
      imports := imports.push { module := root }
  imports

private def firstRootPrefix (ws : Lake.Workspace) (excludeLibs : Array Name) : Option Name := do
  let lib ← ws.root.leanLibs.find? fun lib => !excludeLibs.contains lib.name
  lib.config.roots[0]?

private unsafe def loadEnv (projectDir : System.FilePath) (ws : Lake.Workspace) (imports : Array Import) : IO Environment := do
  enableInitializersExecution
  Lean.searchPathRef.set ws.augmentedLeanPath
  withCurrentDir projectDir <| Lean.importModules imports {}

unsafe def mainImpl (args : List String) : IO UInt32 := do
  let cfg ←
    match parseArgs args with
    | .ok cfg => pure cfg
    | .error err =>
        IO.eprintln err
        return 1
  let cfg ← do
    if cfg.repoUrl.isSome then pure cfg
    else
      let detected ← detectRepoUrl cfg.projectDir
      pure { cfg with repoUrl := detected }
  let ws ← loadWorkspaceAt cfg.projectDir
  let some rootPrefix := cfg.rootPrefix <|> firstRootPrefix ws cfg.excludeLibs
    | IO.eprintln "Could not determine a root module prefix. Pass --root PREFIX."
      return 1
  let imports := importRoots ws cfg.excludeLibs
  let env ← loadEnv cfg.projectDir ws imports
  let tfbInfo ← loadTrustedBaseInfo cfg rootPrefix env
  if let some shadowDir := cfg.shadowOutputDir then
    match tfbInfo.comparator? with
    | none =>
        IO.eprintln "--write-shadow requires a comparator config."
        return 1
    | some _ =>
        let entries ← loadShadowEntries cfg.projectDir rootPrefix ws.root env (selectedShadowTags tfbInfo)
        writeComparatorShadow cfg.projectDir shadowDir rootPrefix env tfbInfo entries cfg.repoUrl
        IO.println s!"Wrote {entries.size} anchored declarations to {shadowDir}"
        IO.println s!"Manifest: {shadowManifestPath shadowDir}"
        IO.println s!"Shadow site: {shadowSiteIndexPath shadowDir}"
  else if cfg.shadowOnly then
    IO.eprintln "--shadow-only requires --write-shadow DIR."
    return 1
  if cfg.shadowOnly then
    return 0
  IO.eprintln "Non-shadow rendering path is not available. Pass --write-shadow DIR --shadow-only."
  return 1

end LeanExposition
