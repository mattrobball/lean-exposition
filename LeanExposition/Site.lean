import Lean
import Lean.DeclarationRange
import Lean.Meta.Instances
import Lean.Util.Sorry
import Lake.CLI.Main
import Lake.Load.Workspace
import MD4Lean
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
deriving Repr

structure TrustedBaseInfo where
  names : Std.HashSet Name := {}
  comparator? : Option ComparatorConfigInfo := none
  comparatorInstalled : Bool := false
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

private def loadComparatorConfig? (projectDir : System.FilePath) : IO (Option ComparatorConfigInfo) := do
  let cfgPath := projectDir / "comparator.json"
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

private def isComparatorInstalled : IO Bool := do
  let out ← IO.Process.output {
    cmd := "which"
    args := #["comparator"]
  }
  pure <| out.exitCode == 0

private def moduleRelPathOfString (moduleName : String) : String :=
  s!"{moduleName.replace "." "/"}.lean"

private def findDeclarationLine? (lines : Array String) (shortName : String) : Option Nat :=
  ((List.range lines.size).findSome? fun idx =>
    let trimmed := (String.trimAscii lines[idx]!).toString
    if trimmed.startsWith "theorem " && trimmed.contains shortName then
      some (idx + 1)
    else
      none)

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
        match snippet.splitOn ":=" with
        | first :: _ => (String.trimAscii first).toString
        | [] => (String.trimAscii snippet).toString
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

private def loadTrustedBaseTargetBlocks (projectDir : System.FilePath) (repoUrl? : Option String)
    (tfbInfo : TrustedBaseInfo) : IO (Array (Block Manual)) := do
  match tfbInfo.comparator? with
  | none => pure #[]
  | some comparator =>
      let mut blocks : Array (Block Manual) := #[]
      for theoremName in comparator.theoremNames do
        let info ← loadTargetStatementInfo projectDir comparator.challengeModule theoremName
        blocks := blocks.push (.para #[.bold #[.text "Checked statement"]])
        match info.statement? with
        | some statement => blocks := blocks.push (.code statement)
        | none => blocks := blocks.push (.para #[.code theoremName.toString])
        let sourceLabel :=
          match info.line? with
          | some line => s!"{info.relPath}:{line}"
          | none => info.relPath
        let sourceInline :=
          match targetSourceUrlOf repoUrl? info.relPath info.line? with
          | some url => .link #[.text sourceLabel] url
          | none => .code sourceLabel
        blocks := blocks.push (.para #[.bold #[.text "Source: "], sourceInline])
      pure blocks

private def computeTrustedBaseNames (projectDir : System.FilePath) (rootPrefix : Name)
    (targets : Array Name) : IO (Std.HashSet Name) := do
  if targets.isEmpty then
    return {}
  let mut names : Std.HashSet Name := {}
  for target in targets do
    let out ← IO.Process.output {
      cmd := "lake"
      args := #["exe", "extractDeps", target.toString, rootPrefix.toString]
      cwd := some projectDir
    }
    if out.exitCode != 0 then
      return {}
    for line in out.stdout.splitOn "\n" do
      if let some dep := extractDepsName? line then
        names := names.insert dep
  pure names

private def loadTrustedBaseInfo (projectDir : System.FilePath) (rootPrefix : Name) : IO TrustedBaseInfo := do
  let comparator? ← loadComparatorConfig? projectDir
  let comparatorInstalled ← isComparatorInstalled
  match comparator? with
  | none => pure { comparatorInstalled := comparatorInstalled }
  | some comparator =>
      let names ← computeTrustedBaseNames projectDir rootPrefix comparator.theoremNames
      pure {
        names
        comparator? := some comparator
        comparatorInstalled := comparatorInstalled
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
  match snippet.splitOn ":=" with
  | first :: _ => (String.trimAscii first).toString
  | [] => (String.trimAscii snippet).toString

private def headBeforeWhere (snippet : String) : String :=
  let rec go (remaining : List String) (acc : List String) :=
    match remaining with
    | [] => String.intercalate "\n" acc.reverse
    | line :: rest =>
        let acc := line :: acc
        let trimmed := (String.trimAscii line).toString
        if trimmed == "where" || trimmed.endsWith " where" || trimmed.endsWith "where" then
          String.intercalate "\n" acc.reverse
        else
          go rest acc
  (String.trimAscii (go (snippet.splitOn "\n") [])).toString

private def displaySignatureFromSource (kind : DeclKind) (src? : Option SourceInfo) : IO (Option String) := do
  let some src := src? | return none
  let snippet := cleanDeclSnippet (← readSourceSnippet src)
  if snippet.isEmpty then
    return none
  let rendered :=
    match kind with
    | .definition | .structure | .typeclass | .inductive => snippet
    | _ => headBeforeAssignment snippet
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
      match snippet.splitOn ":=" with
      | _prefix :: rest@(_ :: _) =>
          pure <| some <| (String.trimAscii (String.intercalate ":=" rest)).toString
      | _ =>
          pure <| some snippet
  | _, _ => pure none

private def hasSorryIn (info : ConstantInfo) : Bool :=
  info.type.hasSorry || info.value?.any Expr.hasSorry

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

def graphJs : String := "
document.addEventListener('DOMContentLoaded', () => {
  const root = document.getElementById('graph-root');
  const dataNode = document.getElementById('graph-data');
  if (!root || !dataNode || !window.d3) return;

  const graph = JSON.parse(dataNode.textContent);
  const groups = [...new Set(graph.nodes.map(node => node.groupKey))].sort();
  const groupOptions = groups.map(group => `<option value=\"${group}\">${group}</option>`).join('');
  root.innerHTML = `
    <div class=\"graph-toolbar\">
      <input id=\"graph-filter\" type=\"search\" placeholder=\"Filter declarations by name or module\" />
      <select id=\"graph-group\">
        <option value=\"\">All chapters</option>
        ${groupOptions}
      </select>
      <button id=\"graph-fit\" type=\"button\">Fit view</button>
      <button id=\"graph-clear\" type=\"button\">Clear focus</button>
    </div>
    <p class=\"graph-hint\">Scroll to zoom, drag the background to pan, click a node to focus its neighborhood, and double-click a node to open its page.</p>
    <p class=\"graph-legend\">Node fill colors mark chapters. Green outlines are kernel-checked; rust outlines contain sorry.</p>
    <div class=\"graph-layout\">
      <svg id=\"graph-svg\" width=\"100%\" height=\"720\"></svg>
      <aside id=\"graph-panel\" class=\"graph-panel\">
        <h2>Graph</h2>
        <p>Use search or click a node to focus its local neighborhood.</p>
      </aside>
    </div>
  `;

  const svg = d3.select('#graph-svg');
  const panel = document.getElementById('graph-panel');
  const filterInput = document.getElementById('graph-filter');
  const groupSelect = document.getElementById('graph-group');
  const fitButton = document.getElementById('graph-fit');
  const clearButton = document.getElementById('graph-clear');
  const width = Math.max(960, root.clientWidth - 32);
  const height = 720;
  svg.attr('viewBox', [0, 0, width, height]);
  const canvas = svg.append('g').attr('class', 'graph-canvas');

  let nodes = graph.nodes.map(n => ({...n}));
  let edges = graph.edges.map(e => ({...e}));
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

  const palette = ['#3d6b59', '#b96d2d', '#7a4e7a', '#2f5f87', '#8a3b3b', '#5f6f2e', '#9a5b8f', '#6b5041'];
  const color = d3.scaleOrdinal(groups, groups.map((_, index) => palette[index % palette.length]));
  const cols = Math.max(1, Math.ceil(Math.sqrt(groups.length)));
  const rows = Math.max(1, Math.ceil(groups.length / cols));
  const groupCenters = new Map(groups.map((group, index) => {
    const col = index % cols;
    const row = Math.floor(index / cols);
    return [group, {
      x: width * ((col + 0.5) / cols),
      y: height * ((row + 0.5) / rows)
    }];
  }));

  const simulation = d3.forceSimulation(nodes)
    .force('link', d3.forceLink(edges).id(d => d.id).distance(80).strength(0.2))
    .force('charge', d3.forceManyBody().strength(-210))
    .force('center', d3.forceCenter(width / 2, height / 2))
    .force('x', d3.forceX(d => groupCenters.get(d.groupKey)?.x || width / 2).strength(0.08))
    .force('y', d3.forceY(d => groupCenters.get(d.groupKey)?.y || height / 2).strength(0.08))
    .force('collision', d3.forceCollide(22));

  const zoom = d3.zoom()
    .scaleExtent([0.25, 4])
    .on('zoom', event => {
      canvas.attr('transform', event.transform);
    });
  svg.call(zoom);

  const link = canvas.append('g')
    .attr('stroke', '#b8b0a4')
    .attr('stroke-opacity', 0.6)
    .selectAll('line')
    .data(edges)
    .join('line')
    .attr('stroke-width', 1.2);

  const node = canvas.append('g')
    .selectAll('g')
    .data(nodes)
    .join('g')
    .attr('class', 'graph-node')
    .style('cursor', 'pointer');

  const radius = d => 8 + Math.min(6, Math.floor((degree.get(d.id) || 0) / 3));
  const circles = node.append('circle')
    .attr('r', radius)
    .attr('fill', d => color(d.groupKey))
    .attr('stroke', d => d.status === 'sorry' ? '#a14d2a' : '#1f6b4b')
    .attr('stroke-width', 2.2);

  node.append('title')
    .text(d => `${d.kind}: ${d.id}\\n${d.moduleName}`);

  const labels = node.append('text')
    .attr('class', 'graph-label')
    .text(d => d.label)
    .attr('x', 14)
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
      return `<li><a href=\"${node.href}\"><code>${node.label}</code></a></li>`;
    }).join('');
    const extra = ids.length > 10 ? `<p>Showing 10 of ${ids.length}.</p>` : '';
    return `<p><strong>${title}:</strong></p><ul class=\"graph-neighbor-list\">${items}</ul>${extra}`;
  };

  const setDefaultPanel = visibleCount => {
    panel.innerHTML = `
      <h2>Graph</h2>
      <p>${visibleCount} declarations are visible in the current filter.</p>
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
    const boxWidth = Math.max(120, maxX - minX + 80);
    const boxHeight = Math.max(120, maxY - minY + 80);
    const scale = Math.max(0.3, Math.min(2.4, 0.9 / Math.max(boxWidth / width, boxHeight / height)));
    const tx = width / 2 - scale * ((minX + maxX) / 2);
    const ty = height / 2 - scale * ((minY + maxY) / 2);
    svg.transition().duration(250).call(zoom.transform, d3.zoomIdentity.translate(tx, ty).scale(scale));
  };

  let activeQuery = '';
  let activeGroup = '';
  let selectedId = null;

  const filteredIds = () => new Set(
    nodes
      .filter(node => {
        const matchesGroup = activeGroup === '' || node.groupKey === activeGroup;
        const haystack = `${node.id} ${node.moduleName}`.toLowerCase();
        const matchesQuery = activeQuery === '' || haystack.includes(activeQuery);
        return matchesGroup && matchesQuery;
      })
      .map(node => node.id)
  );

  const neighborhoodIds = () => {
    if (!selectedId) return null;
    const ids = new Set([selectedId]);
    for (const dep of outgoing.get(selectedId) || []) ids.add(dep);
    for (const user of incoming.get(selectedId) || []) ids.add(user);
    return ids;
  };

  const updatePanel = visible => {
    if (!selectedId) {
      setDefaultPanel(visible.size);
      return;
    }
    const selected = nodeById.get(selectedId);
    const deps = outgoing.get(selectedId) || [];
    const usedBy = incoming.get(selectedId) || [];
    panel.innerHTML = `
      <h2>${selected.label}</h2>
      <p><strong>Kind:</strong> ${selected.kind}</p>
      <p><strong>Status:</strong> ${selected.status}</p>
      <p><strong>Chapter:</strong> <code>${selected.groupKey}</code></p>
      <p><strong>Module:</strong> <code>${selected.moduleName}</code></p>
      <p><a class=\"decl-card-action\" href=\"${selected.href}\">Open declaration</a></p>
      ${formatNeighborList('Uses', deps)}
      ${formatNeighborList('Used by', usedBy)}
    `;
  };

  const updateVisibility = () => {
    const visible = filteredIds();
    if (selectedId && !visible.has(selectedId)) selectedId = null;
    const neighborhood = neighborhoodIds();

    node
      .style('display', d => visible.has(d.id) ? null : 'none')
      .style('opacity', d => {
        if (!visible.has(d.id)) return 0;
        if (!neighborhood) return 1;
        return neighborhood.has(d.id) ? 1 : 0.15;
      });

    labels
      .style('display', d => {
        if (!visible.has(d.id)) return 'none';
        if (neighborhood) return neighborhood.has(d.id) ? null : 'none';
        return activeQuery === '' ? 'none' : null;
      });

    circles
      .attr('stroke-width', d => d.id === selectedId ? 4 : 2.2)
      .attr('r', d => d.id === selectedId ? radius(d) + 2 : radius(d));

    link
      .style('display', d => {
        const source = typeof d.source === 'object' ? d.source.id : d.source;
        const target = typeof d.target === 'object' ? d.target.id : d.target;
        return visible.has(source) && visible.has(target) ? null : 'none';
      })
      .style('opacity', d => {
        const source = typeof d.source === 'object' ? d.source.id : d.source;
        const target = typeof d.target === 'object' ? d.target.id : d.target;
        if (!visible.has(source) || !visible.has(target)) return 0;
        if (!neighborhood) return 0.45;
        return neighborhood.has(source) && neighborhood.has(target) ? 0.9 : 0.05;
      })
      .attr('stroke', d => {
        const source = typeof d.source === 'object' ? d.source.id : d.source;
        const target = typeof d.target === 'object' ? d.target.id : d.target;
        return selectedId && (source === selectedId || target === selectedId) ? '#a14d2a' : '#b8b0a4';
      });

    updatePanel(visible);
    return visible;
  };

  const drag = d3.drag()
    .on('start', (event, d) => {
      if (!event.active) simulation.alphaTarget(0.2).restart();
      d.fx = d.x;
      d.fy = d.y;
    })
    .on('drag', (event, d) => {
      d.fx = event.x;
      d.fy = event.y;
    })
    .on('end', (event, d) => {
      if (!event.active) simulation.alphaTarget(0);
      d.fx = null;
      d.fy = null;
    });

  node.call(drag);

  node.on('click', (event, d) => {
    event.preventDefault();
    selectedId = d.id == selectedId ? null : d.id;
    updateVisibility();
    if (selectedId) {
      const neighborhood = neighborhoodIds() || new Set();
      zoomToBounds(nodes.filter(node => neighborhood.has(node.id)));
    }
  });

  node.on('dblclick', (event, d) => {
    event.preventDefault();
    window.location.href = d.href;
  });

  simulation.on('tick', () => {
    link
      .attr('x1', d => d.source.x)
      .attr('y1', d => d.source.y)
      .attr('x2', d => d.target.x)
      .attr('y2', d => d.target.y);

    node.attr('transform', d => `translate(${d.x},${d.y})`);
  });

  filterInput.addEventListener('input', event => {
    activeQuery = event.target.value.trim().toLowerCase();
    updateVisibility();
  });

  groupSelect.addEventListener('change', event => {
    activeGroup = event.target.value;
    updateVisibility();
  });

  fitButton.addEventListener('click', () => {
    const visible = updateVisibility();
    const neighborhood = neighborhoodIds();
    zoomToBounds(nodes.filter(node => visible.has(node.id) && (!neighborhood || neighborhood.has(node.id))));
  });

  clearButton.addEventListener('click', () => {
    selectedId = null;
    const visible = updateVisibility();
    zoomToBounds(nodes.filter(node => visible.has(node.id)));
  });

  svg.on('dblclick', event => {
    if (event.target === svg.node()) {
      selectedId = null;
      const visible = updateVisibility();
      zoomToBounds(nodes.filter(node => visible.has(node.id)));
    }
  });

  setDefaultPanel(nodes.length);
  setTimeout(() => {
    const visible = updateVisibility();
    zoomToBounds(nodes.filter(node => visible.has(node.id)));
  }, 800);
});
"

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
    if let some block := depListBlock depLinks then
      blocks := blocks.push <| .other (Block.details { summary := s!"Uses ({depLinks.size})" }) #[block]
    if let some block := depListBlock usedByLinks then
      blocks := blocks.push <| .other (Block.details { summary := s!"Used by ({usedByLinks.size})" }) #[block]
    if let some block := mkLinkParagraph sourceUrl issueUrl then
      blocks := blocks.push block
    if let some proof := decl.proofText? then
      blocks := blocks.push <| .other (Block.details { summary := "Proof" }) #[.code proof]
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
  let cfg ← Lake.MonadError.runEIO <| Lake.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let ws? ← withCurrentDir projectDir <| Lake.loadWorkspace cfg |>.toBaseIO
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
  let decls ← collectDecls cfg.projectDir rootPrefix ws.root env
  if decls.isEmpty then
    let namedCount :=
      env.constants.toList.foldl (fun n entry =>
        let name := entry.1
        n + if hasPrefixName name rootPrefix then 1 else 0) 0
    IO.eprintln s!"No declarations exposed under module filtering. Declarations with matching name prefix: {namedCount}"
  else
    IO.println s!"Collected {decls.size} declarations under {rootPrefix}"
  let tfbInfo ← loadTrustedBaseInfo cfg.projectDir rootPrefix
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
