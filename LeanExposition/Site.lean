import Lean
import Lean.DeclarationRange
import Lean.Elab.Import
import Lean.Meta.Instances
import Lean.Util.Sorry
import Lake.CLI.Main
import Lake.Load.Workspace
import MD4Lean
import LeanExposition.TrustedBase
import SubVerso.Compat
import VersoManual
import VersoManual.Markdown

open Lake
open Lean
open Lean.Meta
open Verso.Doc
open Verso.Genre
open Manual

namespace LeanExposition

open Verso.Output Html

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

structure LinkInfo where
  label : String
  href? : Option String := none
deriving Repr, ToJson, FromJson

structure DeclCardData where
  anchorId : String
  shortName : String
  kindLabel : String
  fullName : String
  tags : Array String := #[]
deriving Repr, ToJson, FromJson, Inhabited

structure DetailsData where
  summary : String
deriving Repr, ToJson, FromJson, Inhabited

structure LinkListDetailsData where
  summary : String
  links : Array LinkInfo
deriving Repr, ToJson, FromJson, Inhabited

structure CodeDetailsData where
  summary : String
  code : String
  wrap : Bool := false
deriving Repr, ToJson, FromJson, Inhabited

structure StatementPanelData where
  label : String
  code : String
  source? : Option LinkInfo := none
  wrap : Bool := true
deriving Repr, ToJson, FromJson, Inhabited

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

structure DeclInfo where
  name : Name
  moduleName : Name
  modulePath : String
  groupKey : String
  kind : DeclKind
  displaySignature : String
  expandedSignature : String
  docBlocks : Array (Block Manual)
  proofText? : Option String
  source? : Option SourceInfo
  hasSorry : Bool
  dependsOnSorry : Bool := false
  inTfb : Bool := false
  deps : Array Name
  usedBy : Array Name := #[]
deriving Repr

structure ModuleInfo where
  name : Name
  path : String
  groupKey : String
  decls : Array DeclInfo
deriving Repr

structure GroupInfo where
  key : String
  modules : Array ModuleInfo
deriving Repr

structure MarkdownSection where
  title : String
  body : String
deriving Repr

structure ComparatorConfigInfo where
  challengeModule : String
  solutionModule : String
  theoremNames : Array Name
  permittedAxioms : Array String
  enableNanoda : Bool
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

structure TargetStatementInfo where
  theoremName : Name
  relPath : String
  line? : Option Nat := none
  statement? : Option String := none
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

private def isAuxComponent (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_"

private partial def isInternalName : Name → Bool
  | .anonymous => false
  | .num p _ => isInternalName p
  | .str p s =>
      isAuxComponent s
      || s ∈ ["brecOn", "below", "casesOn", "noConfusion", "noConfusionType",
              "recOn", "rec", "ind", "mk", "sizeOf_spec", "inject", "injEq",
              "ctorIdx", "ext_iff"]
      || isInternalName p

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

private def humanizeWord (s : String) : String :=
  if s.isEmpty then
    s
  else
    let rec go (chars : List Char) (prevLower : Bool) (acc : String) :=
      match chars with
      | [] => acc
      | ch :: rest =>
          let insertSpace := prevLower && ch.isUpper
          let acc := if insertSpace then acc.push ' ' else acc
          go rest ch.isLower (acc.push ch)
    go s.toList false ""

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

private def anchorIdOf (name : Name) : String :=
  String.intercalate "___" (name.toString.splitOn ".")

private def mkInlineText (s : String) : Inline Manual :=
  .text s

private def mkCodeLink (link : LinkInfo) : Inline Manual :=
  match link.href? with
  | some href => .link #[.code link.label] href
  | none => .code link.label

private def joinInlines (xs : List (Array (Inline Manual))) (sep : Array (Inline Manual)) : Array (Inline Manual) :=
  match xs with
  | [] => #[]
  | x :: rest => rest.foldl (fun acc item => acc ++ sep ++ item) x

private def depParagraph (label : String) (links : Array LinkInfo) : Option (Block Manual) :=
  if links.isEmpty then
    none
  else
    let entries := links.toList.map fun link => #[mkCodeLink link]
    some <| .para <|
      #[.bold #[.text s!"{label}: "]] ++
      joinInlines entries #[.text " · "]

private def depListBlock (links : Array LinkInfo) : Option (Block Manual) :=
  if links.isEmpty then
    none
  else
    let items := links.map fun link => Verso.Doc.ListItem.mk #[.para #[mkCodeLink link]]
    some <| .ul items

private def codeListParagraph (label : String) (items : Array String) : Option (Block Manual) :=
  if items.isEmpty then
    none
  else
    let entries := items.toList.map fun item => #[.code item]
    some <| .para <|
      #[.bold #[.text s!"{label}: "]] ++
      joinInlines entries #[.text " · "]

private def mkLinkParagraph (sourceUrl? issueUrl? : Option String) : Option (Block Manual) :=
  let items :=
    ([sourceUrl?.map fun url => .link #[.text "Source"] url,
      issueUrl?.map fun url => .link #[.text "Open Issue"] url].filterMap id)
  if items.isEmpty then
    none
  else
    let entries := items.map fun item => #[item]
    some <| .para <|
      #[.bold #[.text "Actions: "]] ++ joinInlines entries #[.text " · "]

private def markdownToBlocks (doc : String) : Array (Block Manual) :=
  match MD4Lean.parse doc (MD4Lean.MD_DIALECT_GITHUB ||| MD4Lean.MD_FLAG_LATEXMATHSPANS ||| MD4Lean.MD_FLAG_NOHTML) with
  | none => #[.para #[.text doc]]
  | some parsed =>
      parsed.blocks.foldl
        (fun acc block =>
          match Verso.Genre.Manual.Markdown.blockFromMarkdown' block (handleHeaders := Verso.Genre.Manual.Markdown.strongEmphHeaders') with
          | .ok out => acc.push out
          | .error _ => acc.push (.para #[.text doc]))
        #[]

private def trimBlankLines (lines : List String) : List String :=
  let dropFront := lines.dropWhile (fun s => s.trimAscii.isEmpty)
  dropFront.reverse.dropWhile (fun s => s.trimAscii.isEmpty) |>.reverse

private def parseMarkdownSections (text : String) : Array MarkdownSection := Id.run do
  let lines := text.splitOn "\n"
  let mut introLines : List String := []
  let mut currentTitle? : Option String := none
  let mut currentBody : List String := []
  let mut sections : Array MarkdownSection := #[]
  for line in lines do
    if line.startsWith "## " then
      match currentTitle? with
      | some title =>
          let body := String.intercalate "\n" (trimBlankLines currentBody.reverse)
          if !body.trimAscii.isEmpty then
            sections := sections.push { title, body }
      | none =>
          let intro := String.intercalate "\n" (trimBlankLines introLines.reverse)
          if !intro.trimAscii.isEmpty then
            sections := sections.push { title := "Overview", body := intro }
      currentTitle? := some (line.drop 3).trimAscii.toString
      currentBody := []
    else if line.startsWith "# " then
      continue
    else
      match currentTitle? with
      | some _ => currentBody := line :: currentBody
      | none => introLines := line :: introLines
  match currentTitle? with
  | some title =>
      let body := String.intercalate "\n" (trimBlankLines currentBody.reverse)
      if !body.trimAscii.isEmpty then
        sections := sections.push { title, body }
  | none =>
      let intro := String.intercalate "\n" (trimBlankLines introLines.reverse)
      if !intro.trimAscii.isEmpty then
        sections := sections.push { title := "Overview", body := intro }
  sections

private def readFileIfExists (path : System.FilePath) : IO (Option String) := do
  if ← path.pathExists then
    return some (← IO.FS.readFile path)
  return none

private def extractDepsName? (line : String) : Option Name :=
  let trimmed := (String.trimAscii line).toString
  if trimmed.startsWith "- `" then
    let rest := (trimmed.drop 3).toString
    match rest.splitOn "`" with
    | name :: _ => if name.isEmpty then none else some name.toName
    | [] => none
  else
    none

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

private def moduleRelPathOfString (moduleName : String) : String :=
  s!"{moduleName.replace "." "/"}.lean"

private def findDeclarationLine? (lines : Array String) (shortName : String) : Option Nat :=
  ((List.range lines.size).findSome? fun idx =>
    let trimmed := (String.trimAscii lines[idx]!).toString
    if trimmed.startsWith "theorem " && trimmed.contains shortName then
      some (idx + 1)
    else
      none)

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

private def loadTargetStatementInfo (projectDir : System.FilePath) (challengeModule : String)
    (theoremName : Name) : IO TargetStatementInfo := do
  let relPath := moduleRelPathOfString challengeModule
  let filePath := projectDir / relPath
  let some contents ← readFileIfExists filePath
    | pure { theoremName, relPath }
  let lines := (contents.splitOn "\n").toArray
  let line? := findDeclarationLine? lines theoremName.getString!
  let statement? :=
    line?.bind fun line =>
      let snippet := String.intercalate "\n" <| (lines.toList.drop (line - 1))
      let head :=
        match splitTopLevelAssignment? snippet with
        | some (first, _) => first
        | none => (String.trimAscii snippet).toString
      if head.isEmpty then none else some head
  pure {
    theoremName
    relPath
    line?
    statement?
  }

private def targetSourceUrlOf (repoUrl? : Option String) (relPath : String) (line? : Option Nat) : Option String :=
  match repoUrl? with
  | none => none
  | some repoUrl =>
      some <| match line? with
        | some line => s!"{repoUrl}/blob/main/{relPath}#L{line}"
        | none => s!"{repoUrl}/blob/main/{relPath}"

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

private def stripDeclPrefix (kind : DeclKind) (shortName : String) (signature : String) : String :=
  let pfx := s!"{declKeyword kind} {shortName}"
  match signature.dropPrefix? pfx with
  | some rest => (String.trimAscii rest.toString).toString
  | none => signature

private def splitTopLevelColon? (s : String) : Option (String × String) :=
  let rec go (chars : List Char) (round curly square angled : Nat) (acc : List Char) : Option (String × String) :=
    match chars with
    | [] => none
    | ':' :: rest =>
        if round == 0 && curly == 0 && square == 0 && angled == 0 then
          some (
            (String.trimAscii (String.ofList acc.reverse)).toString,
            (String.trimAscii (String.ofList rest)).toString
          )
        else
          go rest round curly square angled (':' :: acc)
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

private def signatureSections? (kind : DeclKind) (shortName : String) (signature : String) : Option (String × String) :=
  match kind with
  | .theorem | .definition | .opaque | .axiom | .instance =>
      let remainder := stripDeclPrefix kind shortName signature
      splitTopLevelColon? remainder
  | _ => none

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

private def shouldExpose (env : Environment) (rootPrefix : Name) (name : Name) (info : ConstantInfo) : Bool :=
  if let some moduleName := moduleNameOf env name then
    if !hasPrefixName moduleName rootPrefix then
      false
    else if env.isProjectionFn name then
      false
    else if isInternalName name || name.isInternal || name.isImplementationDetail then
      false
    else if isAuxRecursor env name || isNoConfusion env name then
      false
    else match info with
      | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
      | _ => true
  else if env.isProjectionFn name then
    false
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

private def proofTextFromSource (kind : DeclKind) (src? : Option SourceInfo) : IO (Option String) := do
  match kind, src? with
  | .theorem, some src
  | .opaque, some src
  | .instance, some src =>
      let snippet := (String.trimAscii (← readSourceSnippet src)).toString
      match splitTopLevelAssignment? snippet with
      | some (_, rest) => pure <| some rest
      | none => pure <| some snippet
  | _, _ => pure none

private def hasSorryIn (info : ConstantInfo) : Bool :=
  info.type.hasSorry || info.value?.any Expr.hasSorry

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

private def moduleIndexMap (decls : Array DeclInfo) : Std.HashMap Name (Array DeclInfo) :=
  decls.foldl
    (fun acc decl => acc.insert decl.moduleName ((acc.getD decl.moduleName #[]).push decl))
    {}

private def groupIndexMap (mods : Array ModuleInfo) : Std.HashMap String (Array ModuleInfo) :=
  mods.foldl
    (fun acc modInfo => acc.insert modInfo.groupKey ((acc.getD modInfo.groupKey #[]).push modInfo))
    {}

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

private def repoFileUrlOf (repoUrl? : Option String) (relPath : String) : Option String :=
  repoUrl?.map fun repoUrl => s!"{repoUrl}/blob/main/{relPath}"

private def groupHrefOf (groupKey : String) : String :=
  s!"chapter-{slugify groupKey}/"

private def moduleHrefOf (modulePath : String) : String :=
  s!"module-{slugify modulePath}/"

private def trustedBaseGroupHrefOf (groupKey : String) : String :=
  s!"tfb-chapter-{slugify groupKey}/"

private def trustedBaseModuleHrefOf (modulePath : String) : String :=
  s!"tfb-module-{slugify modulePath}/"

private def pathForPart (groupKey modulePath : String) (declName : Name) : String :=
  s!"{groupHrefOf groupKey}{moduleHrefOf modulePath}#{anchorIdOf declName}"

private def pathForTrustedBasePart (groupKey modulePath : String) (declName : Name) : String :=
  s!"{trustedBaseGroupHrefOf groupKey}{trustedBaseModuleHrefOf modulePath}#{anchorIdOf declName}"

private def declHrefMap (decls : Array DeclInfo) : Std.HashMap Name String :=
  decls.foldl
    (fun acc decl => acc.insert decl.name (pathForPart decl.groupKey decl.modulePath decl.name))
    {}

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

/-- Create ShadowEntries for theorems declared in the challenge module.
    These reference the spec source (with `sorry`) rather than the solution module. -/
private def loadChallengeEntries (projectDir : System.FilePath)
    (comparator : ComparatorConfigInfo) : IO (Array ShadowEntry) := do
  let challengeModule := comparator.challengeModule.toName
  let relPath := moduleRelPathOfString comparator.challengeModule
  let filePath := projectDir / relPath
  let some contents ← readFileIfExists filePath
    | return #[]
  let lines := (contents.splitOn "\n").toArray
  let absPath ← IO.FS.realPath filePath
  let mut entries := #[]
  for theoremName in comparator.theoremNames do
    let shortName := theoremName.getString!
    let some startLine := findDeclarationLine? lines shortName | continue
    -- find end of the declaration (next blank line or end of file)
    let mut endLine := startLine
    for idx in List.range (lines.size - startLine) do
      let ln := startLine + idx
      let trimmed := (String.trimAscii lines[ln]!).toString
      endLine := ln + 1
      if trimmed.isEmpty && ln > startLine then
        break
    let source : SourceInfo := {
      relPath
      absPath := absPath.toString
      line := startLine
      endLine
    }
    entries := entries.push {
      name := theoremName
      moduleName := challengeModule
      anchor := theoremName.toString
      kind := .theorem
      source
      displaySignature := s!"theorem {shortName} ..."
      deps := #[]
      tags := #["challenge"]
    }
  return entries

private def anchorStartLine (anchor : String) : String :=
  s!"-- ANCHOR: {anchor}"

private def anchorEndLine (anchor : String) : String :=
  s!"-- ANCHOR_END: {anchor}"

private def shouldDropProofInShadow (entry : ShadowEntry) : Bool :=
  (entry.tags.contains "tfb" || entry.tags.contains "challenge")
    && (entry.kind == .theorem || entry.kind == .opaque || entry.kind == .instance)

private def shadowDeclValueSyntax? (commandStx : Syntax) : Option Syntax :=
  if commandStx.getKind != ``Lean.Parser.Command.declaration then
    none
  else
    let inner := commandStx[1]
    match inner.getKind with
    | ``Lean.Parser.Command.theorem =>
        inner[3]?
    | ``Lean.Parser.Command.instance =>
        inner[5]?
    | ``Lean.Parser.Command.opaque =>
        let optVal := inner[3]
        optVal[0]?
    | _ => none

private def shadowSignatureFromSyntax? (env : Environment) (fullName : Name) (snippet : String) : Option String :=
  match Parser.runParserCategory env `command snippet "<shadow-proofless>" with
  | .error _ => none
  | .ok commandStx =>
      if commandStx.getKind != ``Lean.Parser.Command.declaration then
        none
      else
        let inner := commandStx[1]
        if inner.getKind == ``Lean.Parser.Command.theorem then
          inner[2]? |>.bind fun declSigStx =>
            declSigStx.getRange? |>.map fun declSigRange =>
              s!"theorem {fullName} {SubVerso.Compat.String.Pos.extract snippet declSigRange.start declSigRange.stop}"
        else if inner.getKind == ``Lean.Parser.Command.instance then
          inner[4]? |>.bind fun declSigStx =>
            declSigStx.getRange? |>.map fun declSigRange =>
              s!"theorem {fullName} {SubVerso.Compat.String.Pos.extract snippet declSigRange.start declSigRange.stop}"
        else
          none

private def dropLeadingWhitespace (s : String) : String :=
  (s.dropWhile Char.isWhitespace).toString

private def takeLeadingWord (s : String) : String × String :=
  let trimmed := dropLeadingWhitespace s
  let word := trimmed.takeWhile fun ch => !ch.isWhitespace
  let word := word.toString
  let rest := trimmed.drop word.length
  (word, rest.toString)

private def isDeclNameChar (ch : Char) : Bool :=
  ch.isAlphanum || ch == '_' || ch == '\'' || ch == '.'

private def dropLeadingDeclName (s : String) : String :=
  let trimmed := dropLeadingWhitespace s
  let name := trimmed.takeWhile isDeclNameChar
  trimmed.drop name.toString.length |>.toString

private def joinCanonicalTheoremSignature (fullName : Name) (rest : String) : String :=
  if rest.isEmpty then
    s!"theorem {fullName}"
  else if rest.front?.map Char.isWhitespace |>.getD false then
    s!"theorem {fullName}{rest}"
  else
    s!"theorem {fullName} {rest}"

private def canonicalShadowTheoremSignature (entry : ShadowEntry) (signature : String) : String :=
  let (kw, rest0) := takeLeadingWord signature
  let rest :=
    match kw with
    | "theorem" | "lemma" | "def" | "opaque" =>
        dropLeadingDeclName rest0
    | "instance" =>
        let trimmed := dropLeadingWhitespace rest0
        match trimmed.front? with
        | some '(' | some '{' | some '[' | some '⦃' | some ':' => trimmed
        | _ => dropLeadingDeclName trimmed
    | _ => rest0
  joinCanonicalTheoremSignature entry.name rest

private def shadowRootImport (moduleName : String) : String :=
  match moduleName.splitOn "." with
  | root :: _ => root
  | [] => moduleName

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

private def sameNormalizedPath (a b : System.FilePath) : Bool :=
  a.normalize.toString == b.normalize.toString

private partial def populateShadowTree (projectDir shadowDir srcDir dstDir : System.FilePath)
    (generatedFiles : Std.HashMap String String) : IO Unit := do
  IO.FS.createDirAll dstDir
  for entry in (← srcDir.readDir) do
    let srcPath := entry.path
    if sameNormalizedPath srcPath shadowDir || entry.fileName ∈ [".git", ".lake", "build"] then
      continue
    let symlinkMeta ← srcPath.symlinkMetadata
    let fileMeta ← srcPath.metadata
    let dstPath := dstDir / entry.fileName
    match fileMeta.type with
    | .dir =>
        populateShadowTree projectDir shadowDir srcPath dstPath generatedFiles
    | .file =>
        let relPath ← relativeSourcePath projectDir srcPath
        if let some generated := generatedFiles[relPath]? then
          IO.FS.writeFile dstPath generated
        else if symlinkMeta.type == IO.FS.FileType.symlink then
          IO.FS.writeBinFile dstPath (← IO.FS.readBinFile srcPath)
        else
          copyFileToShadow srcPath dstPath
    | _ => pure ()

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

private def shadowTagForModule (moduleName : Name) : String :=
  s!"shadow-module-{slugify moduleName.toString}"

private def shadowTagForEntry (entry : ShadowEntry) : String :=
  s!"shadow-entry-{slugify entry.moduleName.toString}-{slugify entry.name.toString}-{entry.source.line}-{entry.source.endLine}"

private def shadowTagForLayer (layer : Nat) : String :=
  s!"shadow-layer-{layer}"

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
  let blockType :=
    if hasShadowTag entry "tfb" && proofKind then "collapsibleModule" else "module"
  let config := s!"{fence}{blockType} (module := {entry.moduleName}) (anchor := {entry.anchor}){defSite}"
  #[
    config,
    snippet,
    fence,
    ""
  ]

private def appendShadowEntryBlock (_env : Environment) (lines : Array String) (level : Nat) (entry : ShadowEntry)
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
      ++ renderShadowCodeBlock entry snippet

private def renderComparatorManual (env : Environment) (tfbInfo : TrustedBaseInfo)
    (entries : Array ShadowEntry) (repoUrl? : Option String := none) : IO String := do
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
    s!"#doc (Manual) \"{comparator.solutionModule} Comparator Manual\" =>",
    "%%%",
    "htmlSplit := .never",
    "%%%",
    "",
    "This manual was generated mechanically from the comparator configuration and the trusted formalization base walk.",
    "",
    s!"The comparator target theorem is rendered from `{comparator.solutionModule}`.",
    ""
  ]
  if solutionEntries.isEmpty then
    lines := appendTaggedHeading lines 1 "Solution theorem" "shadow-solution-theorem"
    lines := lines.push "No solution theorem declarations were resolved from the comparator configuration."
    lines := lines.push ""
  else
    lines := appendTaggedHeading lines 1 "Solution theorem" "shadow-solution-theorem"
    for entry in solutionEntries do
      lines ← appendShadowEntryBlock env lines 2 entry repoUrl?
  lines := appendTaggedHeading lines 1 "Trusted formalization base" "shadow-trusted-formalization-base"
  lines := lines.push "These declarations were selected by the trusted-base walk rooted at the comparator theorem statements."
  lines := lines.push ""
  if tfbEntries.isEmpty then
    lines := lines.push "No trusted-base declarations were resolved."
    lines := lines.push ""
  else
    let solutionNames : Std.HashSet Name :=
      solutionEntries.foldl (fun acc entry => acc.insert entry.name) {}
    let tfbOnlyEntries :=
      tfbEntries.filter fun entry => !solutionNames.contains entry.name
    let layerMap := shadowLayerMapFromOrderedEntries tfbOnlyEntries
    let mut currentLayer? : Option Nat := none
    for entry in tfbOnlyEntries do
      let layer := layerMap.getD entry.name 1
      if currentLayer? != some layer then
        currentLayer? := some layer
        lines := appendTaggedHeading lines 2 s!"Dependency layer {layer}" (shadowTagForLayer layer)
      lines ← appendShadowEntryBlock env lines 3 entry repoUrl?
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
    "    \"main section > h2, main section > h3, main section > h4 { border-left: 4px solid var(--verso-structure-color, #154734); padding-left: 0.6rem; }\"]",
    "  toHtml := some fun _goI goB _id _data blocks => do",
    "    let inner ← blocks.mapM (goB ·)",
    "    pure {{ <details class=\"collapsible-proof\"><summary>\"Show proof\"</summary>{{inner}}</details> }}",
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
    "private abbrev ManualDocBlock := Verso.Doc.Block Verso.Genre.Manual",
    "",
    "def wrapCollapsible (body : ManualDocBlock) : ManualDocBlock :=",
    "  .other Block.collapsibleProof #[body]",
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
    (entries : Array ShadowEntry) (repoUrl? : Option String := none) : IO Unit := do
  IO.FS.writeFile (shadowDir / s!"{comparatorManualSupportModule}.lean") renderComparatorManualSupport
  IO.FS.writeFile (shadowDir / s!"{comparatorManualModule}.lean") (← renderComparatorManual env tfbInfo entries repoUrl?)
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

private def buildShadowSite (shadowDir : System.FilePath) : IO Unit := do
  updateShadowDependencies shadowDir
  pullShadowCache shadowDir
  runShadowCommand shadowDir "lake" #["build", comparatorManualExe]
  runShadowCommand shadowDir "lake" #["exe", comparatorManualExe]


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
  writeComparatorManualFiles env shadowDir tfbInfo entries repoUrl?
  buildShadowSite shadowDir

private def collectDecls (projectDir : System.FilePath) (rootPrefix : Name)
    (pkg : Lake.Package) (env : Environment) : IO (Array DeclInfo) := do
  let mut decls := #[]
  for (name, info) in env.constants.toList do
    let some moduleName := moduleNameOf env name | continue
    if !shouldExpose env rootPrefix name info then
      continue
    let ranges? ← findRanges? env name
    let source? ← toSourceInfo? projectDir pkg moduleName ranges?
    let kind := declKindOf env info name
    let expandedSignature ← ppExprString env info.type
    let displaySignature :=
      (← displaySignatureFromSource kind source?).getD <|
        displaySignatureFallback kind name expandedSignature
    let proofText? ← proofTextFromSource kind source?
    let doc? ← findDocString? env name
    let docBlocks :=
      match doc? with
      | some doc => markdownToBlocks doc
      | none => #[]
    let deps :=
      info.type.getUsedConstants.foldl (fun acc dep => if dep != name then acc.push dep else acc) #[]
    let decl : DeclInfo := {
      name := name
      moduleName := moduleName
      modulePath := modulePathOf rootPrefix moduleName
      groupKey := groupKeyOfModule rootPrefix moduleName
      kind := kind
      displaySignature := displaySignature
      expandedSignature := expandedSignature
      docBlocks := docBlocks
      proofText? := proofText?
      source? := source?
      hasSorry := hasSorryIn info
      deps := deps
    }
    decls := decls.push decl
  pure decls

private def debugEmptyDeclCollection (env : Environment) (rootPrefix : Name)
    (imports : Array Import) : IO Unit := do
  let mut moduleHits : Std.HashMap Name Nat := {}
  let mut reportableModuleHits : Std.HashMap Name Nat := {}
  let mut sample : Array String := #[]
  for (name, info) in env.constants.toList do
    let some moduleName := moduleNameOf env name | continue
    if hasPrefixName moduleName rootPrefix then
      moduleHits := moduleHits.insert moduleName ((moduleHits.getD moduleName 0) + 1)
      if shouldExpose env rootPrefix name info then
        reportableModuleHits := reportableModuleHits.insert moduleName ((reportableModuleHits.getD moduleName 0) + 1)
        if sample.size < 12 then
          sample := sample.push s!"{name} [{moduleName}]"
  let moduleTotal := moduleHits.toArray.foldl (fun n entry => n + entry.2) 0
  let reportableTotal := reportableModuleHits.toArray.foldl (fun n entry => n + entry.2) 0
  IO.eprintln s!"Debug: imports = {String.intercalate ", " (imports.toList.map fun imp => toString imp.module)}"
  IO.eprintln s!"Debug: constants = {env.constants.toList.length}"
  IO.eprintln s!"Debug: module-prefix hits for {rootPrefix} = {moduleTotal} across {moduleHits.size} modules"
  IO.eprintln s!"Debug: reportable hits for {rootPrefix} = {reportableTotal} across {reportableModuleHits.size} modules"
  let topModules :=
    moduleHits.toArray.qsort (fun a b =>
      if a.2 == b.2 then a.1.lt b.1 else a.2 > b.2)
  for (moduleName, count) in topModules[:10] do
    let visible := reportableModuleHits.getD moduleName 0
    IO.eprintln s!"  {moduleName}: {count} total, {visible} reportable"
  if !sample.isEmpty then
    IO.eprintln "Debug: sample reportable declarations:"
    for entry in sample do
      IO.eprintln s!"  - {entry}"

private def attachReverseDeps (decls : Array DeclInfo) : Array DeclInfo :=
  let exposed : Std.HashSet Name := decls.foldl (fun s decl => s.insert decl.name) {}
  let rev : Std.HashMap Name (Array Name) := decls.foldl
    (fun acc decl =>
      decl.deps.foldl
        (fun inner dep =>
          if exposed.contains dep then
            inner.insert dep ((inner.getD dep #[]).push decl.name)
          else
            inner)
        acc)
    {}
  decls.map fun decl => { decl with usedBy := (rev.getD decl.name #[]).qsort Name.lt }

private def attachDependsOnSorry (decls : Array DeclInfo) : Array DeclInfo :=
  Id.run do
    let exposed : Std.HashSet Name := decls.foldl (fun s decl => s.insert decl.name) {}
    let mut marked : Std.HashSet Name :=
      decls.foldl (fun s decl => if decl.hasSorry then s.insert decl.name else s) {}
    let mut changed := true
    while changed do
      changed := false
      for decl in decls do
        if !marked.contains decl.name then
          let depends := decl.deps.any fun dep => exposed.contains dep && marked.contains dep
          if depends then
            marked := marked.insert decl.name
            changed := true
    return decls.map fun decl => { decl with dependsOnSorry := marked.contains decl.name }

private def attachTrustedBaseFlags (tfb : Std.HashSet Name) (decls : Array DeclInfo) : Array DeclInfo :=
  decls.map fun decl => { decl with inTfb := tfb.contains decl.name }

private def moduleRank (order : Std.HashMap Name Nat) (moduleName : Name) : Nat :=
  order.getD moduleName 1000000000

private def sortModules (order : Std.HashMap Name Nat) (mods : Array ModuleInfo) : Array ModuleInfo :=
  mods.qsort fun a b =>
    let ra := moduleRank order a.name
    let rb := moduleRank order b.name
    if ra == rb then a.path < b.path else ra < rb

private def sortDeclsInModules (mods : Array ModuleInfo) : Array ModuleInfo :=
  mods.map fun modInfo =>
    let decls :=
      modInfo.decls.qsort fun a b =>
        match a.source?, b.source? with
        | some sa, some sb => if sa.line == sb.line then a.name.lt b.name else sa.line < sb.line
        | some _, none => true
        | none, some _ => false
        | none, none => a.name.lt b.name
    { modInfo with decls := decls }

private def buildModules (rootPrefix : Name) (order : Std.HashMap Name Nat) (decls : Array DeclInfo) : Array ModuleInfo :=
  let mods := moduleIndexMap decls |>.toArray.map fun (name, ds) => {
    name := name
    path := modulePathOf rootPrefix name
    groupKey := groupKeyOfModule rootPrefix name
    decls := ds
  }
  sortDeclsInModules <| sortModules order mods

private def buildGroups (order : Std.HashMap Name Nat) (mods : Array ModuleInfo) : Array GroupInfo :=
  let groupRank (group : GroupInfo) : Nat :=
    group.modules.foldl (fun best modInfo => min best (moduleRank order modInfo.name)) 1000000000
  groupIndexMap mods |>.toArray
    |>.map (fun (key, modules) => { key, modules := sortModules order modules })
    |>.qsort (fun a b =>
      let ra := groupRank a
      let rb := groupRank b
      if ra == rb then a.key < b.key else ra < rb)

private def mkSourceParagraph (label : String) (url? : Option String) : Array (Block Manual) :=
  match url? with
  | some url => #[.para #[.bold #[.text "Source: "], .link #[.text label] url]]
  | none => #[]

private def mkMarkdownPart (title : String) (fileSlug : String) (body : String)
    (sourceUrl? : Option String := none) (shortTitle? : Option String := none)
    (sourceLabel? : Option String := none)
    (subParts : Array (Part Manual) := #[]) : Part Manual :=
  {
    title := #[.text title]
    titleString := title
    metadata := some {
      file := some fileSlug
      shortTitle := shortTitle?
      tag := some (.provided fileSlug)
      number := false
    }
    content := mkSourceParagraph (sourceLabel?.getD title) sourceUrl? ++ markdownToBlocks body
    subParts := subParts
  }

private def loadProjectContextParts (projectDir : System.FilePath) (repoUrl? : Option String)
    : IO (Array (Block Manual) × Array (Part Manual)) := do
  let readmePath := projectDir / "README.md"
  let mut rootBlocks : Array (Block Manual) := #[]
  let mut parts : Array (Part Manual) := #[]

  if let some readme ← readFileIfExists readmePath then
    let sections := parseMarkdownSections readme
    let sections :=
      sections.takeWhile fun sec => sec.title != "Selected References"
    if let some overview := sections[0]? then
      rootBlocks := rootBlocks ++ #[.para #[.text "Project overview."]] ++ markdownToBlocks overview.body
      let contextSubParts :=
        sections.toList.drop 1 |>.toArray.map fun sec =>
          mkMarkdownPart sec.title s!"context-{slugify sec.title}" sec.body
      let contextPage := {
        title := #[.text "Overview"]
        titleString := "Overview"
        metadata := some {
          file := some "context"
          shortTitle := some "Overview"
          tag := some (.provided "project-context")
          number := false
        }
        content := mkSourceParagraph "README.md" (repoFileUrlOf repoUrl? "README.md") ++ markdownToBlocks overview.body
        subParts := contextSubParts
      }
      parts := parts.push contextPage

  return (rootBlocks, parts)

def customCss : String := "
:root {
  --verso-structure-color: #154734;
  --verso-toc-background-color: #f4efe5;
  --verso-selected-color: #f0dcc8;
  --verso-text-font-family: 'Iowan Old Style', 'Palatino Linotype', 'Book Antiqua', serif;
  --verso-structure-font-family: 'Avenir Next Condensed', 'Gill Sans', sans-serif;
  --verso-code-font-family: 'Iosevka Term', 'JetBrains Mono', monospace;
  --site-ink: #193428;
  --site-muted: #5a655f;
  --site-warm: #fbf7ef;
  --site-card: #fffdf8;
  --site-accent: #a14d2a;
  --site-border: #d8cdbd;
  --site-content-min-width: 52rem;
  --site-collapsed-sidebar-width: 9rem;
}

body {
  background:
    radial-gradient(circle at top left, rgba(198, 148, 92, 0.12), transparent 28%),
    linear-gradient(180deg, #fcfaf5 0%, #f5efe6 100%);
  color: var(--site-ink);
}

.decl-section {
  scroll-margin-top: 5rem;
}

.decl-heading {
  align-items: center;
  display: flex;
  gap: 0.5rem;
  margin: 1.8rem 0 0.5rem;
}

.decl-heading code {
  font-size: 1.05rem;
}

.decl-permalink {
  color: var(--site-muted);
  font-size: 0.95rem;
  text-decoration: none;
}

.decl-permalink:hover {
  color: var(--site-accent);
}

.decl-card {
  background: var(--site-card);
  border: 1px solid var(--site-border);
  border-left: 6px solid var(--verso-structure-color);
  border-radius: 14px;
  margin: 1.2rem 0 1.8rem;
  padding: 1rem 1.2rem 1.1rem;
  box-shadow: 0 10px 28px rgba(52, 36, 18, 0.06);
}

.decl-card-header {
  align-items: flex-start;
  display: flex;
  gap: 0.8rem;
  justify-content: space-between;
  margin-bottom: 0.8rem;
}

.decl-card-title {
  min-width: 0;
}

.decl-card-label {
  color: var(--site-muted);
  font-family: var(--verso-structure-font-family);
  font-size: 0.92rem;
  font-weight: 700;
  letter-spacing: 0.08em;
  text-transform: uppercase;
}

.decl-card-name {
  display: block;
  font-family: var(--verso-code-font-family);
  font-size: 0.95rem;
  margin-top: 0.1rem;
}

.decl-card-tags {
  display: flex;
  flex-wrap: wrap;
  gap: 0.45rem;
  justify-content: flex-end;
  margin-top: 0;
}

.decl-card-tag {
  border: 1px solid var(--site-border);
  border-radius: 999px;
  font-family: var(--verso-structure-font-family);
  font-size: 0.82rem;
  padding: 0.2rem 0.55rem;
}

.decl-card-tag.sorry {
  background: #fff2ec;
  border-color: #e8b294;
  color: #8b3517;
}

.decl-card-tag.tfb {
  background: #eef3ff;
  border-color: #b8c8ef;
  color: #294b88;
}

.decl-card-tagbar {
  align-items: flex-start;
  display: flex;
  flex: 0 0 auto;
}

.decl-card-action {
  background: var(--site-ink);
  border-radius: 999px;
  color: white !important;
  font-family: var(--verso-structure-font-family);
  font-size: 0.82rem;
  padding: 0.35rem 0.75rem;
  text-decoration: none !important;
}

.decl-card details {
  border-top: 1px solid rgba(216, 205, 189, 0.8);
  margin-top: 0.9rem;
  padding-top: 0.75rem;
}

.decl-card summary {
  color: var(--site-accent);
  cursor: pointer;
  font-family: var(--verso-structure-font-family);
  font-weight: 700;
}

.decl-card details ul {
  margin: 0.65rem 0 0;
  padding-left: 1.25rem;
}

.decl-card details li + li {
  margin-top: 0.25rem;
}

.decl-card pre,
.decl-card code.hl.lean.block {
  background: #faf4e8 !important;
  border: 1px solid #eadfcf;
  border-radius: 10px;
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.7);
}

.decl-card pre {
  overflow-x: auto;
  padding: 0.85rem 1rem;
  white-space: pre-wrap;
  word-break: break-word;
  overflow-wrap: anywhere;
}

.site-details-panel {
  border-top: 1px solid rgba(216, 205, 189, 0.8);
  margin-top: 0.9rem;
  padding-top: 0.75rem;
}

.site-details-panel summary {
  color: var(--site-accent);
  cursor: pointer;
  font-family: var(--verso-structure-font-family);
  font-weight: 700;
}

.site-details-panel ul {
  margin: 0.65rem 0 0;
  padding-left: 1.25rem;
}

.site-details-panel li + li {
  margin-top: 0.25rem;
}

.site-statement-panel {
  background: var(--site-card);
  border: 1px solid var(--site-border);
  border-left: 6px solid var(--verso-structure-color);
  border-radius: 14px;
  box-shadow: 0 10px 28px rgba(52, 36, 18, 0.06);
  margin: 1rem 0 1.35rem;
  padding: 1rem 1.2rem 1.1rem;
}

.site-statement-label,
.site-statement-source {
  margin: 0 0 0.75rem;
}

.site-statement-source {
  margin-top: 0.85rem;
}

.site-code-block {
  background: #faf4e8;
  border: 1px solid #eadfcf;
  border-radius: 10px;
  box-shadow: inset 0 1px 0 rgba(255, 255, 255, 0.7);
  overflow-x: auto;
  padding: 0.85rem 1rem;
}

.site-code-block.wrap {
  white-space: pre-wrap;
  word-break: break-word;
  overflow-wrap: anywhere;
}

.header-logo-wrapper,
.with-toc #toc,
.with-toc > main {
  transition:
    flex-basis var(--verso-toc-transition-time) ease,
    width var(--verso-toc-transition-time) ease,
    padding-left var(--verso-toc-transition-time) ease,
    transform var(--verso-toc-transition-time) ease;
}

.site-toc-toggle {
  display: none;
}

.site-utility-nav {
  align-items: flex-start;
  border-bottom: 1px solid rgba(216, 205, 189, 0.9);
  display: flex;
  flex-direction: column;
  gap: 0.4rem;
  margin: 0.2rem 0 0.8rem;
  padding: 0 1rem 0.85rem;
}

.site-utility-link {
  color: var(--site-ink);
  font-family: var(--verso-structure-font-family);
  font-size: 0.82rem;
  font-weight: 700;
  letter-spacing: 0.03em;
  text-decoration: none;
}

.site-utility-link:hover {
  color: var(--site-accent);
}

@media screen and (min-width: 701px) {
  .site-toc-toggle {
    background: var(--site-card);
    border: 1px solid var(--site-border);
    border-radius: 999px;
    color: var(--site-ink);
    cursor: pointer;
    display: inline-flex;
    font-family: var(--verso-structure-font-family);
    font-size: 0.85rem;
    margin: 0 1rem 0.85rem;
    padding: 0.45rem 0.8rem;
    width: fit-content;
  }

  body.site-toc-collapsed .with-toc #toc {
    width: var(--site-collapsed-sidebar-width);
  }

  body.site-toc-collapsed .with-toc > main {
    padding-left: var(--site-collapsed-sidebar-width);
  }

  body.site-toc-collapsed .header-logo-wrapper {
    flex-basis: var(--site-collapsed-sidebar-width);
    padding-left: 0;
    width: var(--site-collapsed-sidebar-width);
  }

  body.site-toc-collapsed #toc .split-tocs,
  body.site-toc-collapsed #toc .last {
    display: none;
  }
}

@media screen and (min-width: 900px) {
  .content-wrapper {
    box-sizing: border-box;
    margin: 0;
    max-width: none;
    width: 100%;
  }

  .content-wrapper > section,
  main section {
    box-sizing: border-box;
    max-width: none;
    min-width: min(var(--site-content-min-width), calc(100vw - var(--verso-toc-width) - 4rem));
    width: 100%;
  }
}

#graph-root {
  background: var(--site-card);
  border: 1px solid var(--site-border);
  border-radius: 14px;
  min-height: 720px;
  padding: 1rem;
}

.graph-toolbar {
  align-items: center;
  display: flex;
  flex-wrap: wrap;
  gap: 0.8rem;
  margin-bottom: 0.8rem;
}

.graph-toolbar input,
.graph-toolbar select,
.graph-toolbar button {
  border: 1px solid var(--site-border);
  border-radius: 999px;
  padding: 0.55rem 0.9rem;
}

.graph-toolbar input,
.graph-toolbar select {
  font-family: var(--verso-text-font-family);
}

.graph-toolbar input {
  flex: 1 1 20rem;
}

.graph-toolbar button {
  background: var(--site-card);
  color: var(--site-ink);
  cursor: pointer;
  font-family: var(--verso-structure-font-family);
}

.graph-legend {
  color: var(--site-muted);
  font-size: 0.92rem;
  margin: 0.2rem 0 0.9rem;
}

.graph-layout {
  display: grid;
  gap: 1rem;
  grid-template-columns: minmax(0, 1fr) 18rem;
}

.graph-panel {
  background: rgba(255, 253, 248, 0.92);
  border: 1px solid var(--site-border);
  border-radius: 14px;
  padding: 0.9rem 1rem;
}

.graph-panel h2 {
  margin-top: 0;
}

.graph-hint {
  color: var(--site-muted);
  font-size: 0.92rem;
  margin-bottom: 0.8rem;
}

#graph-svg {
  cursor: grab;
}

.graph-panel code {
  font-size: 0.9rem;
}

.graph-group-label {
  fill: var(--site-muted);
  font-family: var(--verso-structure-font-family);
  font-size: 12px;
  font-weight: 700;
  letter-spacing: 0.04em;
  text-transform: uppercase;
}

.graph-group-frame {
  fill: rgba(255, 253, 248, 0.74);
  stroke: rgba(216, 205, 189, 0.85);
  stroke-width: 1.2;
}

.graph-node-hit {
  cursor: pointer;
  fill: transparent;
}

.graph-neighbor-list {
  margin: 0.7rem 0 0;
  padding-left: 1.1rem;
}

.graph-neighbor-list li {
  margin-bottom: 0.35rem;
}

@media (max-width: 900px) {
  .graph-layout {
    grid-template-columns: 1fr;
  }
}
"

def graphJs : String := r###"
document.addEventListener('DOMContentLoaded', () => {
  const root = document.getElementById('graph-root');
  const dataNode = document.getElementById('graph-data');
  if (!root || !dataNode || !window.d3) return;

  const graph = JSON.parse(dataNode.textContent);
  const groups = [...new Set(graph.nodes.map(node => node.groupKey))].sort();
  const groupOptions = groups.map(group => `<option value="${group}">${group}</option>`).join('');
  root.innerHTML = `
    <div class="graph-toolbar">
      <input id="graph-filter" type="search" placeholder="Filter declarations by name or module" />
      <select id="graph-group">
        <option value="">All chapters</option>
        ${groupOptions}
      </select>
      <button id="graph-fit" type="button">Fit view</button>
      <button id="graph-clear" type="button">Clear focus</button>
    </div>
    <p class="graph-hint">Use search or the chapter filter to narrow the graph, click a node to inspect local dependencies, and double-click a node to open its page.</p>
    <p class="graph-legend">Node fill colors mark chapters. Green outlines are kernel-checked; rust outlines contain sorry. Edges appear only for focused or narrow views.</p>
    <div class="graph-layout">
      <svg id="graph-svg" width="100%"></svg>
      <aside id="graph-panel" class="graph-panel">
        <h2>Graph</h2>
        <p>Use search or click a node to inspect its local neighborhood.</p>
      </aside>
    </div>
  `;

  const svg = d3.select('#graph-svg');
  const panel = document.getElementById('graph-panel');
  const filterInput = document.getElementById('graph-filter');
  const groupSelect = document.getElementById('graph-group');
  const fitButton = document.getElementById('graph-fit');
  const clearButton = document.getElementById('graph-clear');

  const palette = ['#3d6b59', '#b96d2d', '#7a4e7a', '#2f5f87', '#8a3b3b', '#5f6f2e', '#9a5b8f', '#6b5041'];
  const color = d3.scaleOrdinal(groups, groups.map((_, index) => palette[index % palette.length]));

  const nodes = graph.nodes
    .map((node, index) => ({
      ...node,
      index,
      searchText: `${node.id} ${node.moduleName}`.toLowerCase()
    }))
    .sort((a, b) => {
      if (a.groupKey !== b.groupKey) return a.groupKey.localeCompare(b.groupKey);
      if (a.moduleName !== b.moduleName) return a.moduleName.localeCompare(b.moduleName);
      return a.label.localeCompare(b.label);
    });
  const edges = graph.edges.map((edge, index) => ({ ...edge, edgeId: `edge-${index}` }));

  const nodeById = new Map(nodes.map(node => [node.id, node]));
  const outgoing = new Map(nodes.map(node => [node.id, []]));
  const incoming = new Map(nodes.map(node => [node.id, []]));
  const degree = new Map(nodes.map(node => [node.id, 0]));
  for (const edge of edges) {
    degree.set(edge.source, (degree.get(edge.source) || 0) + 1);
    degree.set(edge.target, (degree.get(edge.target) || 0) + 1);
    outgoing.get(edge.source)?.push(edge.target);
    incoming.get(edge.target)?.push(edge.source);
  }

  const baseWidth = Math.max(960, root.clientWidth - 32);
  const groupGap = 18;
  const outerPadding = 18;
  const groupCount = Math.max(1, groups.length);
  const columns = Math.max(1, Math.min(4, Math.ceil(Math.sqrt(groupCount))));
  const boxWidth = Math.max(250, Math.floor((baseWidth - outerPadding * 2 - groupGap * (columns - 1)) / columns));

  const groupNodes = new Map(groups.map(group => [group, nodes.filter(node => node.groupKey === group)]));
  const layouts = [];
  const rowHeights = [];

  groups.forEach((group, index) => {
    const members = groupNodes.get(group) || [];
    const row = Math.floor(index / columns);
    const col = index % columns;
    const nodesPerRow = Math.max(6, Math.min(18, Math.ceil(Math.sqrt(Math.max(1, members.length) * 1.4))));
    const rows = Math.max(1, Math.ceil(members.length / nodesPerRow));
    const boxHeight = 68 + rows * 22;
    rowHeights[row] = Math.max(rowHeights[row] || 0, boxHeight);
    layouts.push({ group, members, row, col, nodesPerRow, rows, boxHeight });
  });

  const rowOffsets = [];
  let cursorY = outerPadding;
  for (let row = 0; row < rowHeights.length; row += 1) {
    rowOffsets[row] = cursorY;
    cursorY += rowHeights[row] + groupGap;
  }
  const width = columns * boxWidth + (columns - 1) * groupGap + outerPadding * 2;
  const height = Math.max(720, cursorY - groupGap + outerPadding);

  for (const layout of layouts) {
    const x = outerPadding + layout.col * (boxWidth + groupGap);
    const y = rowOffsets[layout.row];
    layout.x = x;
    layout.y = y;
    const innerLeft = x + 18;
    const innerTop = y + 42;
    const innerWidth = boxWidth - 36;
    const stepX = layout.nodesPerRow <= 1 ? 0 : innerWidth / Math.max(1, layout.nodesPerRow - 1);
    layout.members.forEach((node, memberIndex) => {
      const col = memberIndex % layout.nodesPerRow;
      const row = Math.floor(memberIndex / layout.nodesPerRow);
      node.x = innerLeft + col * stepX;
      node.y = innerTop + row * 22;
    });
  }

  svg.attr('height', height).attr('viewBox', [0, 0, width, height]);
  const canvas = svg.append('g').attr('class', 'graph-canvas');

  const zoom = d3.zoom()
    .scaleExtent([0.35, 5])
    .on('zoom', event => {
      canvas.attr('transform', event.transform);
    });
  svg.call(zoom);

  const frameLayer = canvas.append('g').attr('class', 'graph-groups');
  frameLayer.selectAll('g')
    .data(layouts)
    .join('g')
    .each(function(layout) {
      const group = d3.select(this);
      group.append('rect')
        .attr('class', 'graph-group-frame')
        .attr('rx', 16)
        .attr('ry', 16)
        .attr('x', layout.x)
        .attr('y', layout.y)
        .attr('width', boxWidth)
        .attr('height', layout.boxHeight);
      group.append('text')
        .attr('class', 'graph-group-label')
        .attr('x', layout.x + 18)
        .attr('y', layout.y + 24)
        .text(`${layout.group} (${layout.members.length})`);
    });

  const linkLayer = canvas.append('g')
    .attr('class', 'graph-links')
    .attr('stroke', '#b8b0a4')
    .attr('stroke-linecap', 'round');

  const node = canvas.append('g')
    .attr('class', 'graph-nodes')
    .selectAll('g')
    .data(nodes)
    .join('g')
    .attr('class', 'graph-node')
    .attr('transform', d => `translate(${d.x},${d.y})`);

  const radius = d => 5 + Math.min(6, Math.floor((degree.get(d.id) || 0) / 12));
  const circles = node.append('circle')
    .attr('r', radius)
    .attr('fill', d => color(d.groupKey))
    .attr('stroke', d => d.status === 'sorry' ? '#a14d2a' : '#1f6b4b')
    .attr('stroke-width', 1.8);

  node.append('circle')
    .attr('class', 'graph-node-hit')
    .attr('r', d => Math.max(radius(d) + 4, 10));

  node.append('title')
    .text(d => `${d.kind}: ${d.id}\n${d.moduleName}`);

  const labels = node.append('text')
    .attr('class', 'graph-label')
    .text(d => d.label)
    .attr('x', d => radius(d) + 6)
    .attr('y', 4)
    .attr('font-size', 10)
    .attr('fill', '#193428')
    .style('display', 'none');

  const formatNeighborList = (title, ids) => {
    if (!ids || ids.length === 0) {
      return `<p><strong>${title}:</strong> none in the exposed graph.</p>`;
    }
    const items = ids.slice(0, 10).map(id => {
      const node = nodeById.get(id);
      return `<li><a href="${node.href}"><code>${node.label}</code></a></li>`;
    }).join('');
    const extra = ids.length > 10 ? `<p>Showing 10 of ${ids.length}.</p>` : '';
    return `<p><strong>${title}:</strong></p><ul class="graph-neighbor-list">${items}</ul>${extra}`;
  };

  const setDefaultPanel = (visibleCount, edgeCount) => {
    panel.innerHTML = `
      <h2>Graph</h2>
      <p>${visibleCount} declarations are visible in the current filter.</p>
      <p>${edgeCount === 0 ? 'Edges are hidden until the view is focused or narrowed.' : `${edgeCount} edges are currently drawn.`}</p>
      <p>Select a node to inspect its module and immediate dependencies.</p>
    `;
  };

  const zoomToBounds = visibleNodes => {
    const positioned = visibleNodes.filter(node =>
      Number.isFinite(node.x) && Number.isFinite(node.y));
    if (positioned.length === 0) return;
    const minX = d3.min(positioned, node => node.x);
    const maxX = d3.max(positioned, node => node.x);
    const minY = d3.min(positioned, node => node.y);
    const maxY = d3.max(positioned, node => node.y);
    const boxW = Math.max(160, maxX - minX + 120);
    const boxH = Math.max(160, maxY - minY + 120);
    const scale = Math.max(0.45, Math.min(2.6, 0.92 / Math.max(boxW / width, boxH / height)));
    const tx = width / 2 - scale * ((minX + maxX) / 2);
    const ty = height / 2 - scale * ((minY + maxY) / 2);
    svg.transition().duration(220).call(zoom.transform, d3.zoomIdentity.translate(tx, ty).scale(scale));
  };

  let activeQuery = '';
  let activeGroup = '';
  let selectedId = null;
  let scheduled = false;
  let pendingFit = false;

  const filteredNodes = () => nodes.filter(node => {
    const matchesGroup = activeGroup === '' || node.groupKey === activeGroup;
    const matchesQuery = activeQuery === '' || node.searchText.includes(activeQuery);
    return matchesGroup && matchesQuery;
  });

  const neighborhoodIds = () => {
    if (!selectedId) return null;
    const ids = new Set([selectedId]);
    for (const dep of outgoing.get(selectedId) || []) ids.add(dep);
    for (const user of incoming.get(selectedId) || []) ids.add(user);
    return ids;
  };

  const edgeSubset = (visibleIds, neighborhood) => {
    if (selectedId && neighborhood) {
      return edges.filter(edge =>
        visibleIds.has(edge.source) &&
        visibleIds.has(edge.target) &&
        neighborhood.has(edge.source) &&
        neighborhood.has(edge.target));
    }
    if (visibleIds.size <= 90 || (activeQuery !== '' && visibleIds.size <= 160)) {
      return edges.filter(edge => visibleIds.has(edge.source) && visibleIds.has(edge.target));
    }
    return [];
  };

  const updatePanel = (visibleIds, drawnEdges) => {
    if (!selectedId) {
      setDefaultPanel(visibleIds.size, drawnEdges.length);
      return;
    }
    const selected = nodeById.get(selectedId);
    const deps = (outgoing.get(selectedId) || []).filter(id => visibleIds.has(id));
    const usedBy = (incoming.get(selectedId) || []).filter(id => visibleIds.has(id));
    panel.innerHTML = `
      <h2>${selected.label}</h2>
      <p><strong>Kind:</strong> ${selected.kind}</p>
      <p><strong>Status:</strong> ${selected.status}</p>
      <p><strong>Chapter:</strong> <code>${selected.groupKey}</code></p>
      <p><strong>Module:</strong> <code>${selected.moduleName}</code></p>
      <p><a class="decl-card-action" href="${selected.href}">Open declaration</a></p>
      ${formatNeighborList('Uses', deps)}
      ${formatNeighborList('Used by', usedBy)}
    `;
  };

  const renderEdges = drawnEdges => {
    linkLayer.selectAll('line')
      .data(drawnEdges, edge => edge.edgeId)
      .join(
        enter => enter.append('line'),
        update => update,
        exit => exit.remove()
      )
      .attr('x1', edge => nodeById.get(edge.source).x)
      .attr('y1', edge => nodeById.get(edge.source).y)
      .attr('x2', edge => nodeById.get(edge.target).x)
      .attr('y2', edge => nodeById.get(edge.target).y)
      .attr('stroke-width', edge => selectedId && (edge.source === selectedId || edge.target === selectedId) ? 2.3 : 1.1)
      .attr('stroke', edge => selectedId && (edge.source === selectedId || edge.target === selectedId) ? '#a14d2a' : '#b8b0a4')
      .attr('stroke-opacity', edge => selectedId ? 0.92 : 0.42);
  };

  const runUpdate = () => {
    scheduled = false;
    const visibleNodes = filteredNodes();
    const visibleIds = new Set(visibleNodes.map(node => node.id));
    if (selectedId && !visibleIds.has(selectedId)) selectedId = null;
    const neighborhood = neighborhoodIds();
    const labelsVisible = selectedId || (activeQuery !== '' && visibleIds.size <= 150);

    node
      .style('display', d => visibleIds.has(d.id) ? null : 'none')
      .style('opacity', d => {
        if (!visibleIds.has(d.id)) return 0;
        if (!neighborhood) return 0.92;
        return neighborhood.has(d.id) ? 1 : 0.16;
      });

    labels
      .style('display', d => {
        if (!visibleIds.has(d.id)) return 'none';
        if (!labelsVisible) return 'none';
        if (neighborhood) return neighborhood.has(d.id) ? null : 'none';
        return null;
      });

    circles
      .attr('stroke-width', d => d.id === selectedId ? 3.4 : 1.8)
      .attr('r', d => d.id === selectedId ? radius(d) + 2 : radius(d));

    const drawnEdges = edgeSubset(visibleIds, neighborhood);
    renderEdges(drawnEdges);
    updatePanel(visibleIds, drawnEdges);

    if (pendingFit) {
      pendingFit = false;
      const focusNodes = neighborhood
        ? nodes.filter(node => neighborhood.has(node.id) && visibleIds.has(node.id))
        : visibleNodes;
      zoomToBounds(focusNodes.length > 0 ? focusNodes : visibleNodes);
    }
  };

  const scheduleUpdate = (fit = false) => {
    pendingFit = pendingFit || fit;
    if (scheduled) return;
    scheduled = true;
    window.requestAnimationFrame(runUpdate);
  };

  node.on('click', (event, d) => {
    event.preventDefault();
    selectedId = d.id === selectedId ? null : d.id;
    scheduleUpdate(true);
  });

  node.on('dblclick', (event, d) => {
    event.preventDefault();
    window.location.href = d.href;
  });

  filterInput.addEventListener('input', event => {
    activeQuery = event.target.value.trim().toLowerCase();
    scheduleUpdate(false);
  });

  groupSelect.addEventListener('change', event => {
    activeGroup = event.target.value;
    scheduleUpdate(true);
  });

  fitButton.addEventListener('click', () => {
    scheduleUpdate(true);
  });

  clearButton.addEventListener('click', () => {
    selectedId = null;
    scheduleUpdate(true);
  });

  svg.on('dblclick', event => {
    if (event.target === svg.node()) {
      selectedId = null;
      scheduleUpdate(true);
    }
  });

  setDefaultPanel(nodes.length, 0);
  scheduleUpdate(true);
});
"###

private def tocJs : String := "
document.addEventListener('DOMContentLoaded', () => {
  const toc = document.getElementById('toc');
  if (!toc) return;
  const key = 'lean-exposition:toc-collapsed';
  const utilityLinks = [
    { slug: 'context', label: 'Overview', href: 'context/' },
    { slug: 'trusted-base', label: 'TFB', href: 'trusted-base/' },
    { slug: 'graph', label: 'Graph', href: 'graph/' }
  ];
  const button = document.createElement('button');
  button.type = 'button';
  button.className = 'site-toc-toggle';

  const isDesktop = () => window.matchMedia('(min-width: 701px)').matches;

  const normalizeHref = href => {
    if (!href) return '';
    try {
      const url = new URL(href, document.baseURI);
      let path = url.pathname;
      if (path.endsWith('index.html')) path = path.slice(0, -'index.html'.length);
      return path.endsWith('/') ? path : `${path}/`;
    } catch (_err) {
      return href;
    }
  };

  const matchesUtility = (href, slug) => {
    const normalized = normalizeHref(href);
    return normalized === `/${slug}/` || normalized.endsWith(`/${slug}/`);
  };

  const buildUtilityNav = () => {
    toc.querySelector('.site-utility-nav')?.remove();
    const nav = document.createElement('nav');
    nav.className = 'site-utility-nav';
    nav.setAttribute('aria-label', 'Reader guides');
    for (const link of utilityLinks) {
      const item = document.createElement('a');
      item.className = 'site-utility-link';
      item.href = link.href;
      item.textContent = link.label;
      nav.appendChild(item);
    }
    const container = toc.querySelector('.first') || toc;
    const beforeNode = container.querySelector('.split-tocs');
    if (beforeNode) {
      container.insertBefore(nav, beforeNode);
    } else {
      container.appendChild(nav);
    }
  };

  const pruneUtilityEntries = () => {
    toc.querySelectorAll('.split-toc:not(.book)').forEach(block => {
      block.remove();
    });
    toc.querySelectorAll('.split-toc').forEach(block => {
      const titleLink = block.querySelector('.title a');
      const href = titleLink?.getAttribute('href') || '';
      if (utilityLinks.some(link => matchesUtility(href, link.slug))) {
        block.remove();
      }
    });
    toc.querySelectorAll('tr').forEach(row => {
      const href = row.querySelector('a')?.getAttribute('href') || '';
      if (utilityLinks.some(link => matchesUtility(href, link.slug))) {
        row.remove();
      }
    });
  };

  const applyState = collapsed => {
    document.body.classList.toggle('site-toc-collapsed', collapsed);
    button.textContent = collapsed ? 'Show Contents' : 'Hide Contents';
    button.setAttribute('aria-expanded', collapsed ? 'false' : 'true');
  };

  let collapsed = false;
  try {
    collapsed = window.localStorage.getItem(key) === 'true';
  } catch (_err) {
    collapsed = false;
  }
  buildUtilityNav();
  pruneUtilityEntries();
  applyState(collapsed);

  button.addEventListener('click', () => {
    collapsed = !document.body.classList.contains('site-toc-collapsed');
    try {
      window.localStorage.setItem(key, String(collapsed));
    } catch (_err) {
    }
    applyState(collapsed);
  });

  const container = toc.querySelector('.first') || toc;
  const beforeNode = container.querySelector('.split-tocs');
  if (beforeNode) {
    container.insertBefore(button, beforeNode);
  } else {
    container.appendChild(button);
  }
});
"

block_extension Block.declCard (_payload : DeclCardData) where
  data := ToJson.toJson _payload
  traverse _ _ _ _ := pure none
  toTeX := some fun _goI goB _id _data contents => contents.mapM goB
  toHtml := some fun _goI goB _id data contents => do
    let .ok (payload : DeclCardData) := FromJson.fromJson? data
      | HtmlT.logError s!"Could not decode declaration card data from {data.compress}"
        pure .empty
    let tags :=
      payload.tags.map fun tag =>
        let className :=
          if tag == "TFB" then "decl-card-tag tfb" else "decl-card-tag sorry"
        {{<span class={{className}}>{{tag}}</span>}}
    let tagsHtml :=
      if payload.tags.isEmpty then
        .empty
      else
        {{<div class="decl-card-tags">{{tags}}</div>}}
    pure {{
      <section class="decl-section">
        <h2 id={{payload.anchorId}} class="decl-heading">
          <code>{{payload.shortName}}</code>
          <a class="decl-permalink" href={{s!"#{payload.anchorId}"}} title="Permalink">"🔗"</a>
        </h2>
        <div class="decl-card">
          <div class="decl-card-header">
            <div class="decl-card-title">
              <span class="decl-card-label">{{payload.kindLabel}}</span>
              <code class="decl-card-name">{{payload.fullName}}</code>
            </div>
            <div class="decl-card-tagbar">{{tagsHtml}}</div>
          </div>
          <div class="decl-card-body">
            {{← contents.mapM goB}}
          </div>
        </div>
      </section>
    }}

block_extension Block.details (_payload : DetailsData) where
  data := ToJson.toJson _payload
  traverse _ _ _ _ := pure none
  toTeX := some fun _goI goB _id _data contents => contents.mapM goB
  toHtml := some fun _goI goB _id data contents => do
    let .ok (payload : DetailsData) := FromJson.fromJson? data
      | HtmlT.logError s!"Could not decode details block data from {data.compress}"
        pure .empty
    pure {{
      <details>
        <summary>{{payload.summary}}</summary>
        {{← contents.mapM goB}}
      </details>
    }}

private def htmlCodeLink (link : LinkInfo) : Html :=
  match link.href? with
  | some href => {{<a href={{href}}><code>{{link.label}}</code></a>}}
  | none => {{<code>{{link.label}}</code>}}

private def codeBlockClasses (wrap : Bool) : String :=
  if wrap then "site-code-block wrap" else "site-code-block"

block_extension Block.linkListDetails (_payload : LinkListDetailsData) where
  data := ToJson.toJson _payload
  traverse _ _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ data _ => do
    let .ok (payload : LinkListDetailsData) := FromJson.fromJson? data
      | HtmlT.logError s!"Could not decode link list details data from {data.compress}"
        pure .empty
    let items := payload.links.map fun link => {{<li>{{htmlCodeLink link}}</li>}}
    pure {{
      <details class="site-details-panel">
        <summary>{{payload.summary}}</summary>
        <ul>{{items}}</ul>
      </details>
    }}

block_extension Block.codeDetails (_payload : CodeDetailsData) where
  data := ToJson.toJson _payload
  traverse _ _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ data _ => do
    let .ok (payload : CodeDetailsData) := FromJson.fromJson? data
      | HtmlT.logError s!"Could not decode code details data from {data.compress}"
        pure .empty
    pure {{
      <details class="site-details-panel">
        <summary>{{payload.summary}}</summary>
        <pre class={{codeBlockClasses payload.wrap}}>{{Html.text true payload.code}}</pre>
      </details>
    }}

block_extension Block.statementPanel (_payload : StatementPanelData) where
  data := ToJson.toJson _payload
  traverse _ _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ data _ => do
    let .ok (payload : StatementPanelData) := FromJson.fromJson? data
      | HtmlT.logError s!"Could not decode statement panel data from {data.compress}"
        pure .empty
    let sourceHtml :=
      match payload.source? with
      | some source => {{<p class="site-statement-source"><strong>"Source: "</strong>{{htmlCodeLink source}}</p>}}
      | none => .empty
    pure {{
      <section class="site-statement-panel">
        <p class="site-statement-label"><strong>{{payload.label}}</strong></p>
        <pre class={{codeBlockClasses payload.wrap}}>{{Html.text true payload.code}}</pre>
        {{sourceHtml}}
      </section>
    }}

block_extension Block.graph (_payload : GraphData) where
  data := ToJson.toJson _payload
  traverse _ _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml := some fun _ _ _ data _ => do
    let .ok (payload : GraphData) := FromJson.fromJson? data
      | HtmlT.logError s!"Could not decode graph data from {data.compress}"
        pure .empty
    pure {{
      <div id="graph-root"></div>
      {{Html.tag "script" #[("id", "graph-data"), ("type", "application/json")] (.text false (ToJson.toJson payload).compress)}}
    }}

private def loadTrustedBaseTargetBlocks (projectDir : System.FilePath) (repoUrl? : Option String)
    (tfbInfo : TrustedBaseInfo) : IO (Array (Block Manual)) := do
  match tfbInfo.comparator? with
  | none => pure #[]
  | some comparator =>
      let mut blocks : Array (Block Manual) := #[]
      for theoremName in comparator.theoremNames do
        let info ← loadTargetStatementInfo projectDir comparator.challengeModule theoremName
        let sourceLabel :=
          match info.line? with
          | some line => s!"{info.relPath}:{line}"
          | none => info.relPath
        let sourceInfo : LinkInfo := {
          label := sourceLabel
          href? := targetSourceUrlOf repoUrl? info.relPath info.line?
        }
        let statement := info.statement?.getD theoremName.toString
        blocks := blocks.push <| .other (Block.statementPanel {
          label := "Checked statement"
          code := statement
          source? := some sourceInfo
          wrap := true
        }) #[]
      pure blocks

private def renderConfig : RenderConfig :=
  {
    emitTeX := false
    emitHtmlSingle := .no
    emitHtmlMulti := .immediately
    htmlDepth := 2
    rootTocDepth := some 1
    sectionTocDepth := some 1
    extraCss := [customCss]
    extraJs := [graphJs, tocJs]
    extraHead := #[
      Html.tag "script" #[("src", "https://d3js.org/d3.v7.min.js")] .empty
    ]
  }

private def countSorries (decls : Array DeclInfo) : Nat :=
  decls.foldl (fun n decl => n + if decl.hasSorry then 1 else 0) 0

private def countDecls (groups : Array GroupInfo) : Nat :=
  groups.foldl (fun n group =>
    n + group.modules.foldl (fun inner modInfo => inner + modInfo.decls.size) 0) 0

private def mkDashboardBlocks (groups : Array GroupInfo) : Array (Block Manual) :=
  groups.foldl (fun acc group =>
    let groupTotal := group.modules.foldl (fun n modInfo => n + modInfo.decls.size) 0
    let groupSorry := group.modules.foldl (fun n modInfo => n + countSorries modInfo.decls) 0
    let intro : Block Manual :=
      .para #[
        .bold #[.link #[.text <| humanizeWord group.key] (groupHrefOf group.key)],
        .text s!"  ({groupTotal} declarations, {groupSorry} with sorry)"
      ]
    let items := group.modules.map fun modInfo =>
      Verso.Doc.ListItem.mk #[
        .para #[
          .link #[.code modInfo.path] s!"{groupHrefOf group.key}{moduleHrefOf modInfo.path}",
          .text s!"  ({modInfo.decls.size} declarations, {countSorries modInfo.decls} with sorry)"
        ]
      ]
    acc ++ #[intro, .ul items]
  ) #[]

private def mkReaderGuideBlocks (hasContext hasTfb : Bool) : Array (Block Manual) :=
  let contextItems :=
    if hasContext then
      #[Verso.Doc.ListItem.mk #[
        .para #[
          .bold #[.link #[.text "Overview"] "context/"],
          .text " explains the repository scope and mathematical target."
        ]
      ]]
    else
      #[]
  let tfbItems :=
    if hasTfb then
      #[Verso.Doc.ListItem.mk #[
        .para #[
          .bold #[.link #[.text "Trusted Formalization Base"] "trusted-base/"],
          .text " shows the declarations a reader must trust for the comparator-facing theorem."
        ]
      ]]
    else
      #[]
  let graphItems := #[Verso.Doc.ListItem.mk #[
    .para #[
      .bold #[.link #[.text "Dependency Graph"] "graph/"],
      .text " provides the interactive dependency view."
    ]
  ]]
  let items := contextItems ++ tfbItems ++ graphItems
  if items.isEmpty then
    #[]
  else
    #[
      .para #[.bold #[.text "Reader guides"]],
      .ul items
    ]

private def mkTrustedBaseIndexBlocks (groups : Array GroupInfo) : Array (Block Manual) :=
  if groups.isEmpty then
    #[]
  else
    #[.para #[.bold #[.text "Browse the trusted base by chapter."]]]
    ++ groups.foldl (fun acc group =>
      let groupTotal := group.modules.foldl (fun n modInfo => n + modInfo.decls.size) 0
      let moduleItems := group.modules.map fun modInfo =>
        let declLinks := modInfo.decls.map fun decl =>
          { label := decl.name.getString!
            href? := some <| pathForTrustedBasePart group.key modInfo.path decl.name }
        let linkBlock? :=
          if declLinks.isEmpty then
            none
          else
            let entries := declLinks.toList.map fun link => #[mkCodeLink link]
            some <| .para <| joinInlines entries #[.text " · "]
        let blocks : Array (Block Manual) := #[
          .para #[
            .bold #[.link #[.code modInfo.path] s!"{trustedBaseGroupHrefOf group.key}{trustedBaseModuleHrefOf modInfo.path}"],
            .text s!" ({modInfo.decls.size} declarations)"
          ]
        ]
        let blocks :=
          match linkBlock? with
          | some linkBlock => blocks.push linkBlock
          | none => blocks
        Verso.Doc.ListItem.mk blocks
      acc.push <| .other (Block.details {
        summary := s!"{humanizeWord group.key} ({groupTotal} declarations)"
      }) #[
        .para #[
          .text "Chapter page: ",
          .link #[.text <| humanizeWord group.key] (trustedBaseGroupHrefOf group.key)
        ],
        .ul moduleItems
      ]
    ) #[]

private def mkDeclBlock (decl : DeclInfo) (repoUrl? : Option String)
    (declHrefs : Std.HashMap Name String) : Block Manual :=
  Id.run do
    let issueUrl := issueUrlOf repoUrl? decl.name decl.moduleName decl.source? decl.hasSorry
    let sourceUrl := sourceUrlOf repoUrl? decl.source?
    let depLinks := decl.deps.filterMap fun dep =>
      declHrefs.get? dep |>.map fun href => { label := dep.getString!, href? := some href }
    let usedByLinks := decl.usedBy.filterMap fun dep =>
      declHrefs.get? dep |>.map fun href => { label := dep.getString!, href? := some href }
    let mut blocks : Array (Block Manual) := #[]
    blocks := blocks ++ decl.docBlocks
    let hasDoc := !decl.docBlocks.isEmpty
    if !hasDoc then
      blocks := blocks.push (.para #[.emph #[.text "No docstring."]])
    blocks := blocks.push (.para #[.bold #[.text "Statement"]])
    blocks := blocks.push (.code decl.displaySignature)
    if !depLinks.isEmpty then
      let block : Block Manual := .other (Block.linkListDetails {
        summary := s!"Uses ({depLinks.size})"
        links := depLinks
      }) #[]
      blocks := blocks.push block
    if !usedByLinks.isEmpty then
      let block : Block Manual := .other (Block.linkListDetails {
        summary := s!"Used by ({usedByLinks.size})"
        links := usedByLinks
      }) #[]
      blocks := blocks.push block
    if let some block := mkLinkParagraph sourceUrl issueUrl then
      blocks := blocks.push block
    if let some proof := decl.proofText? then
      blocks := blocks.push <| .other (Block.codeDetails {
        summary := "Proof"
        code := proof
        wrap := true
      }) #[]
    let cardData : DeclCardData := {
      anchorId := anchorIdOf decl.name
      shortName := decl.name.getString!
      kindLabel := decl.kind.label
      fullName := decl.name.toString
      tags := #[
        if decl.dependsOnSorry then some "depends transitively on sorry" else none,
        if decl.inTfb then some "TFB" else none
      ].filterMap id
    }
    .other (Block.declCard cardData) blocks

private def mkModulePart (moduleInfo : ModuleInfo) (repoUrl? : Option String)
    (declHrefs : Std.HashMap Name String) : Part Manual :=
  {
    title := #[.text moduleInfo.path]
    titleString := moduleInfo.path
    metadata := some {
      file := some s!"module-{slugify moduleInfo.path}"
      tag := some (.provided moduleInfo.name.toString)
      shortTitle := some moduleInfo.path
    }
    content := #[
      .para #[
        .text "Module ",
        .code moduleInfo.name.toString,
        .text s!" contains {moduleInfo.decls.size} exposed declarations."
      ]
    ] ++ moduleInfo.decls.map (fun decl => mkDeclBlock decl repoUrl? declHrefs)
    subParts := #[]
  }

private def mkTrustedBaseModulePart (moduleInfo : ModuleInfo) (repoUrl? : Option String)
    (declHrefs : Std.HashMap Name String) : Part Manual :=
  {
    title := #[.text moduleInfo.path]
    titleString := moduleInfo.path
    metadata := some {
      file := some s!"tfb-module-{slugify moduleInfo.path}"
      tag := some (.provided s!"tfb-{moduleInfo.name}")
      shortTitle := some moduleInfo.path
    }
    content := #[
      .para #[
        .text "Module ",
        .code moduleInfo.name.toString,
        .text s!" contributes {moduleInfo.decls.size} declarations to the trusted formalization base."
      ]
    ] ++ moduleInfo.decls.map (fun decl => mkDeclBlock decl repoUrl? declHrefs)
    subParts := #[]
  }

private def mkGroupPart (group : GroupInfo) (repoUrl? : Option String)
    (declHrefs : Std.HashMap Name String) : Part Manual :=
  let title := humanizeWord group.key
  {
    title := #[.text title]
    titleString := title
    metadata := some {
      file := some s!"chapter-{slugify group.key}"
      shortTitle := some title
      tag := some (.provided group.key)
    }
    content := #[
      .para #[.text s!"Modules in the {title} slice are grouped from the first path component after the project root."]
    ]
    subParts := group.modules.map fun moduleInfo => mkModulePart moduleInfo repoUrl? declHrefs
  }

private def mkTrustedBaseGroupPart (group : GroupInfo) (repoUrl? : Option String)
    (declHrefs : Std.HashMap Name String) : Part Manual :=
  let title := humanizeWord group.key
  {
    title := #[.text title]
    titleString := title
    metadata := some {
      file := some s!"tfb-chapter-{slugify group.key}"
      shortTitle := some title
      tag := some (.provided s!"tfb-{group.key}")
    }
    content := #[
      .para #[.text s!"Modules in the {title} slice that contribute declarations to the trusted formalization base."]
    ]
    subParts := group.modules.map fun moduleInfo => mkTrustedBaseModulePart moduleInfo repoUrl? declHrefs
  }

private def mkTrustedBasePart (groups : Array GroupInfo) (repoUrl? : Option String)
    (declHrefs : Std.HashMap Name String) (targetBlocks : Array (Block Manual)) : Part Manual :=
  let declCount := countDecls groups
  let moduleCount := groups.foldl (fun n group => n + group.modules.size) 0
  let intro :=
    if declCount == 0 then
      #[.para #[.text "No exposed declarations were collected into the trusted formalization base from the comparator targets."]]
    else
      #[.para #[.text s!"This view collects the {declCount} exposed declarations across {moduleCount} modules that are reachable from the comparator target theorem statements."]]
  {
    title := #[.text "Trusted Formalization Base"]
    titleString := "Trusted Formalization Base"
    metadata := some {
      file := some "trusted-base"
      shortTitle := some "TFB"
      tag := some (.provided "trusted-base")
      number := false
    }
    content := #[
        .para #[.text "These are the exposed declarations a reader must trust in order to accept the comparator-facing theorem."]
      ]
      ++ targetBlocks
      ++ intro
      ++ mkTrustedBaseIndexBlocks groups
      ++ mkDashboardBlocks groups
    subParts := groups.map fun group => mkTrustedBaseGroupPart group repoUrl? declHrefs
  }

private def mkGraphPart (decls : Array DeclInfo) (declHrefs : Std.HashMap Name String) : Part Manual :=
  let nodes := decls.map fun decl => {
    id := decl.name.toString
    label := decl.name.getString!
    kind := decl.kind.label
    status := if decl.hasSorry then "sorry" else "proved"
    groupKey := decl.groupKey
    moduleName := decl.modulePath
    href := declHrefs.getD decl.name (pathForPart decl.groupKey decl.modulePath decl.name)
  }
  let edges := decls.foldl (fun acc decl =>
    acc ++ decl.deps.filterMap (fun dep =>
      if declHrefs.contains dep then
        some { source := decl.name.toString, target := dep.toString }
      else
        none)) #[]
  let graphData : GraphData := { nodes, edges }
  {
    title := #[.text "Dependency Graph"]
    titleString := "Dependency Graph"
    metadata := some {
      file := some "graph"
      shortTitle := some "Graph"
      tag := some (.provided "graph")
    }
    content := #[
      .para #[.text "Interactive dependency view for exposed declarations."],
      .other (Block.graph graphData) #[]
    ]
    subParts := #[]
  }

private def mkRootPart (cfg : Cli) (rootPrefix : Name) (groups : Array GroupInfo)
    (decls : Array DeclInfo) (declHrefs : Std.HashMap Name String)
    (introBlocks : Array (Block Manual)) (readerGuideBlocks : Array (Block Manual))
    (extraParts : Array (Part Manual)) : Part Manual :=
  let title := cfg.siteTitle.getD s!"{rootPrefix} exposition"
  {
    title := #[.text title]
    titleString := title
    metadata := some {
      file := some "index"
      shortTitle := some title
      number := false
    }
    content := #[.para #[.text "Auto-generated exposition for ", .code rootPrefix.toString, .text "."]]
      ++ introBlocks
      ++ readerGuideBlocks
      ++ mkDashboardBlocks groups
    subParts := (groups.map fun group => mkGroupPart group cfg.repoUrl declHrefs)
      ++ extraParts
      ++ #[mkGraphPart decls declHrefs]
  }

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
  let decls ← collectDecls cfg.projectDir rootPrefix ws.root env
  if decls.isEmpty then
    let namedCount :=
      env.constants.toList.foldl (fun n entry =>
        let name := entry.1
        n + if hasPrefixName name rootPrefix then 1 else 0) 0
    IO.eprintln s!"No declarations exposed under module filtering. Declarations with matching name prefix: {namedCount}"
    debugEmptyDeclCollection env rootPrefix imports
  else
    IO.println s!"Collected {decls.size} declarations under {rootPrefix}"
  let decls := decls |> attachReverseDeps |> attachDependsOnSorry |> attachTrustedBaseFlags tfbInfo.names
  let order ← moduleOrderMap cfg.projectDir rootPrefix
  let modules := buildModules rootPrefix order decls
  let groups := buildGroups order modules
  let declHrefs := declHrefMap decls
  let (introBlocks, extraParts) ← loadProjectContextParts cfg.projectDir cfg.repoUrl
  let tfbGroups := buildGroups order <| buildModules rootPrefix order <| decls.filter (·.inTfb)
  let targetBlocks ← loadTrustedBaseTargetBlocks cfg.projectDir cfg.repoUrl tfbInfo
  let hasContext := extraParts.any fun part => part.metadata.bind PartMetadata.file == some "context"
  let extraParts :=
    if tfbInfo.comparator?.isSome then
      extraParts.push <| mkTrustedBasePart tfbGroups cfg.repoUrl declHrefs targetBlocks
    else
      extraParts
  let readerGuideBlocks := mkReaderGuideBlocks hasContext tfbInfo.comparator?.isSome
  let root := mkRootPart cfg rootPrefix groups decls declHrefs introBlocks readerGuideBlocks extraParts
  let versoArgs :=
    match cfg.outputDir with
    | some out => ["--output", out]
    | none => []
  manualMain root (options := versoArgs) (config := renderConfig)

end LeanExposition
