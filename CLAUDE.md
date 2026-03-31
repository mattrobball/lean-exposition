# CLAUDE.md

## Quality control

Before committing ANY changes to `LeanExposition/Site.lean` or `scripts/split_pages.py`, you MUST run `/qa-comparator-manual` and verify all checks pass. Do NOT commit if any check fails.

## Principles

- Never use string-based parsing for Lean syntax. Use SubVerso's Highlighted token semantics or Verso's block extensions.
- Reuse tools that already solve the problem — the Highlighted tree, InfoTrees, `@[block_extension]`, `extraCss`, Verso's domain system.
- Test changes by loading the actual rendered pages, not just grepping HTML.

## Project structure

- `LeanExposition/Site.lean` — the exposition tool, including shadow generation and comparator manual rendering
- `LeanExposition/TrustedBase.lean` — trusted formalization base extraction
- `scripts/split_pages.py` — post-processing: splits Verso's single-page HTML into multi-page output
- Generated files in the shadow project:
  - `ComparatorManualSupport.lean` — block extensions (`collapsibleModule`, `declAnchor`, `graphEmbed`), proof body splitting via Highlighted tree
  - `ComparatorManual.lean` — the manual content (generated markdown with SubVerso code blocks)
  - `ComparatorManualMain.lean` — entry point

## Key design decisions

- Shadow copies only modules in the dependency cone (selective copy, not full tree)
- `.lake` preserved across regenerations for incremental builds
- Proof body splitting uses SubVerso `Token.Kind.keyword` names and bracket-depth-tracked `:=`
- Cross-reference linking uses invisible `Block.declAnchor` that registers in Verso's `docstringDomain` via `saveDomainObject` + `externalTag`
- Multi-page output via post-processing split (Verso's native multi-page doesn't render SubVerso external code blocks)
- Sub-pages use `<base href="../">` — ALL fragment links must use explicit `slug/#id` format
