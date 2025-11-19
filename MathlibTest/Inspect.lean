import Mathlib.Util.Inspect
import Lean.Elab.App
import Lean.Linter.MissingDocs

open Lean

open InspectGeneric in
/--
info: Syntax.node Parser.Command.section, SourceInfo.synthetic false
|-Syntax.node Parser.Command.sectionHeader, SourceInfo.synthetic false
  |-Syntax.node null, SourceInfo.synthetic false
  |-Syntax.node null, SourceInfo.synthetic false
  |-Syntax.node null, SourceInfo.synthetic false
  |-Syntax.node null, SourceInfo.synthetic false
    |-Syntax.atom SourceInfo.synthetic false-- 'meta'
|-Syntax.atom SourceInfo.synthetic false-- 'section'
|-Syntax.node null, SourceInfo.synthetic false
  |-Syntax.ident SourceInfo.synthetic false-- (Hello,Hello) -- []
---
info: Syntax.node Parser.Command.section, SourceInfo.synthetic false
|-Syntax.node Parser.Command.sectionHeader, SourceInfo.synthetic false
| |-Syntax.node null, SourceInfo.synthetic false
| |-Syntax.node null, SourceInfo.synthetic false
| |-Syntax.node null, SourceInfo.synthetic false
| |-Syntax.node null, SourceInfo.synthetic false
| | |-Syntax.atom SourceInfo.synthetic false-- 'meta'
|-Syntax.atom SourceInfo.synthetic false-- 'section'
|-Syntax.node null, SourceInfo.synthetic false
| |-Syntax.ident SourceInfo.synthetic false-- (Hello,Hello) -- []
-/
#guard_msgs in
#eval do
  let stx ← `(meta section Hello)
  logInfo <| treeR InspectSyntax.printNode Syntax.getArgs stx
  logInfo <| treeR InspectSyntax.printNode Syntax.getArgs stx (indent := "| ")


/--
info: inspect expr: '∀ {a : Nat}, a ≠ 0 → (a + a ≠ 0 + 0) ≠ False'

{'a'} -- forallE
|-'Nat' '[]' -- const
|-('h') -- forallE
|   |-'Ne' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'0' -- bvar
|   |   |-'OfNat.ofNat' -- app
|   |   |   |-'Nat' '[]' -- const
|   |   |   |-'0' -- lit
|   |   |   |-'instOfNatNat' -- app
|   |   |   |   |-'0' -- lit
|   |-'Ne' -- app
|   |   |-'0' -- sort
|   |   |-'Ne' -- app
|   |   |   |-'Nat' '[]' -- const
|   |   |   |-'HAdd.hAdd' -- app
|   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |-'instHAdd' -- app
|   |   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |   |-'instAddNat' '[]' -- const
|   |   |   |   |-'1' -- bvar
|   |   |   |   |-'1' -- bvar
|   |   |   |-'HAdd.hAdd' -- app
|   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |-'instHAdd' -- app
|   |   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |   |-'instAddNat' '[]' -- const
|   |   |   |   |-'OfNat.ofNat' -- app
|   |   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |   |-'0' -- lit
|   |   |   |   |   |-'instOfNatNat' -- app
|   |   |   |   |   |   |-'0' -- lit
|   |   |   |   |-'OfNat.ofNat' -- app
|   |   |   |   |   |-'Nat' '[]' -- const
|   |   |   |   |   |-'0' -- lit
|   |   |   |   |   |-'instOfNatNat' -- app
|   |   |   |   |   |   |-'0' -- lit
|   |   |-'False' '[]' -- const
---
info: inspect expr: 'a + a ≠ 0 + 0'

'Ne' -- app
|-'Nat' '[]' -- const
|-'HAdd.hAdd' -- app
|   |-'Nat' '[]' -- const
|   |-'Nat' '[]' -- const
|   |-'Nat' '[]' -- const
|   |-'instHAdd' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'instAddNat' '[]' -- const
|   |-'_uniq.3117' -- fvar
|   |-'_uniq.3117' -- fvar
|-'HAdd.hAdd' -- app
|   |-'Nat' '[]' -- const
|   |-'Nat' '[]' -- const
|   |-'Nat' '[]' -- const
|   |-'instHAdd' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'instAddNat' '[]' -- const
|   |-'OfNat.ofNat' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'0' -- lit
|   |   |-'instOfNatNat' -- app
|   |   |   |-'0' -- lit
|   |-'OfNat.ofNat' -- app
|   |   |-'Nat' '[]' -- const
|   |   |-'0' -- lit
|   |   |-'instOfNatNat' -- app
|   |   |   |-'0' -- lit
---
info: inspect expr: 'False'

'False' '[]' -- const
---
info: inspect expr: 'a ≠ 0'

'Ne' -- app
|-'Nat' '[]' -- const
|-'_uniq.3117' -- fvar
|-'OfNat.ofNat' -- app
|   |-'Nat' '[]' -- const
|   |-'0' -- lit
|   |-'instOfNatNat' -- app
|   |   |-'0' -- lit
---
info: inspect expr: 'a ≠ 0'

'_uniq.3124' -- mvar
-/
#guard_msgs in
set_option linter.unusedTactic false in
example {a : Nat} (h : a ≠ 0) : (a + a ≠ 0 + 0) ≠ False := by
  revert a
  inspect
  intro a h
  have := h
  inspect_lhs
  inspect_rhs
  inspect h
  inspect this
  simpa

/--
info: inspect syntax:
---
/-- I am a doc-string -/
@[simp, grind =]
private nonrec theorem X (a : Nat) (b : Int) : a + b = b + a := by inspect_syntax apply Int.add_comm
---

Syntax.node Parser.Command.declaration, SourceInfo.none
|-Syntax.node Parser.Command.declModifiers, SourceInfo.none
| |-Syntax.node null, SourceInfo.none
| | |-Syntax.node Parser.Command.docComment, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- '/--'
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎⟩-- 'I am a doc-string -/'
| |-Syntax.node null, SourceInfo.none
| | |-Syntax.node Parser.Term.attributes, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- '@['
| | | |-Syntax.node null, SourceInfo.none
| | | | |-Syntax.node Parser.Term.attrInstance, SourceInfo.none
| | | | | |-Syntax.node Parser.Term.attrKind, SourceInfo.none
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.node Parser.Attr.simp, SourceInfo.none
| | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- 'simp'
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ','
| | | | |-Syntax.node Parser.Term.attrInstance, SourceInfo.none
| | | | | |-Syntax.node Parser.Term.attrKind, SourceInfo.none
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.node Parser.Attr.grind, SourceInfo.none
| | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'grind'
| | | | | | |-Syntax.node null, SourceInfo.none
| | | | | | | |-Syntax.node Parser.Attr.grindMod, SourceInfo.none
| | | | | | | | |-Syntax.node Parser.Attr.grindEq, SourceInfo.none
| | | | | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- '='
| | | | | | | | | |-Syntax.node null, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎⟩-- ']'
| |-Syntax.node null, SourceInfo.none
| | |-Syntax.node Parser.Command.private, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'private'
| |-Syntax.node null, SourceInfo.none
| |-Syntax.node null, SourceInfo.none
| |-Syntax.node null, SourceInfo.none
| |-Syntax.node null, SourceInfo.none
| | |-Syntax.node Parser.Command.nonrec, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'nonrec'
|-Syntax.node Parser.Command.theorem, SourceInfo.none
| |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'theorem'
| |-Syntax.node Parser.Command.declId, SourceInfo.none
| | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (X,X) -- []
| | |-Syntax.node null, SourceInfo.none
| |-Syntax.node Parser.Command.declSig, SourceInfo.none
| | |-Syntax.node null, SourceInfo.none
| | | |-Syntax.node Parser.Term.explicitBinder, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- '('
| | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (a,a) -- []
| | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':'
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨⟩-- (Nat,Nat) -- []
| | | | |-Syntax.node null, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ')'
| | | |-Syntax.node Parser.Term.explicitBinder, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⟩-- '('
| | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (b,b) -- []
| | | | |-Syntax.node null, SourceInfo.none
| | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':'
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨⟩-- (Int,Int) -- []
| | | | |-Syntax.node null, SourceInfo.none
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ')'
| | |-Syntax.node Parser.Term.typeSpec, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':'
| | | |-Syntax.node «term_=_», SourceInfo.none
| | | | |-Syntax.node «term_+_», SourceInfo.none
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (a,a) -- []
| | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- '+'
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (b,b) -- []
| | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- '='
| | | | |-Syntax.node «term_+_», SourceInfo.none
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (b,b) -- []
| | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- '+'
| | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨ ⟩-- (a,a) -- []
| |-Syntax.node Parser.Command.declValSimple, SourceInfo.none
| | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- ':='
| | |-Syntax.node Parser.Term.byTactic, SourceInfo.none
| | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨⏎  ⟩-- 'by'
| | | |-Syntax.node Parser.Tactic.tacticSeq, SourceInfo.none
| | | | |-Syntax.node Parser.Tactic.tacticSeq1Indented, SourceInfo.none
| | | | | |-Syntax.node null, SourceInfo.none
| | | | | | |-Syntax.node InspectSyntax.inspectTacticCmd, SourceInfo.none
| | | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'inspect_syntax'
| | | | | | | |-Syntax.node Parser.Tactic.tacticSeq, SourceInfo.none
| | | | | | | | |-Syntax.node Parser.Tactic.tacticSeq1Indented, SourceInfo.none
| | | | | | | | | |-Syntax.node null, SourceInfo.none
| | | | | | | | | | |-Syntax.node Parser.Tactic.apply, SourceInfo.none
| | | | | | | | | | | |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'apply'
| | | | | | | | | | | |-Syntax.ident SourceInfo.original: ⟨⟩⟨⏎⏎⟩-- (Int.add_comm,Int.add_comm) -- []
| | |-Syntax.node Parser.Termination.suffix, SourceInfo.none
| | | |-Syntax.node null, SourceInfo.none
| | | |-Syntax.node null, SourceInfo.none
| | |-Syntax.node null, SourceInfo.none
---
info: inspect syntax:
---
apply Int.add_comm
---

Syntax.node Parser.Tactic.tacticSeq, SourceInfo.none
|-Syntax.node Parser.Tactic.tacticSeq1Indented, SourceInfo.none
|   |-Syntax.node null, SourceInfo.none
|   |   |-Syntax.node Parser.Tactic.apply, SourceInfo.none
|   |   |   |-Syntax.atom SourceInfo.original: ⟨⟩⟨ ⟩-- 'apply'
|   |   |   |-Syntax.ident SourceInfo.original: ⟨⟩⟨⏎⏎⟩-- (Int.add_comm,Int.add_comm) -- []
-/
#guard_msgs in
inspect_syntax compact
/-- I am a doc-string -/
@[simp, grind =]
private nonrec theorem X (a : Nat) (b : Int) : a + b = b + a := by
  inspect_syntax apply Int.add_comm

open Elab PartialContextInfo
/--
info: inspectIT:
---
set_option linter.missingDocs true
---
commandCtx
|-Info.ofCommandInfo: Lean.Elab.Command.elabSetOption, 'set_option…gDocs true'
|   |-Info.ofCompletionInfo.CompletionInfo.option 'set_option…issingDocs'
|   |-Info.ofOptionInfo: linter.missingDocs, Linter.linter.missingDocs
-/
#guard_msgs in
inspectIT
set_option linter.missingDocs true

/--
info: inspectIT:
---
@[simp]
example : True := .intro
---
commandCtx
|-Info.ofCommandInfo: Lean.Elab.Command.elabDeclaration, '@[simp]⏎ex… := .intro'
| |-commandCtx
| | |-autoImplicitCtx: []
| | | |-commandCtx
| | | | |-parentDeclCtx _example
| | | | | |-autoImplicitCtx: []
| | | | | | |-Info.ofTermInfo: Term.elabIdent, 'True', True
| | | | | | | |-Info.ofCompletionInfo.CompletionInfo.id True 'True' Sort ?u.3511
| | | | | | | |-Info.ofTermInfo: [anonymous], 'True', True
| |-commandCtx
| | |-autoImplicitCtx: []
| | | |-commandCtx
| | | | |-parentDeclCtx _example
| | | | | |-Info.ofCustomInfo: '.intro'
| | | | | | |-Info.ofTermInfo: Term.elabDotIdent, '.intro', True.intro
| | | | | | | |-Info.ofCompletionInfo.CompletionInfo.dotId 'intro' True
| | | | | | | |-Info.ofTermInfo: [anonymous], '.intro', True.intro
| |-commandCtx
| | |-autoImplicitCtx: []
| | | |-commandCtx
| | | | |-parentDeclCtx _example
| | | | | |-Info.ofCommandInfo: Meta.simpExtension, 'simp'
| | | | | | |-Info.ofCommandInfo: Meta.simpExtension, 'simp'
| |-commandCtx
| | |-autoImplicitCtx: []
| | | |-commandCtx
| | | | |-commandCtx
| | | | | |-Info.ofTermInfo: [anonymous], 'example', _example
| |-commandCtx
| | |-autoImplicitCtx: []
| | | |-commandCtx
| | | | |-Info.ofTermInfo: [anonymous], '', _fvar.3512
-/
#guard_msgs in
inspectIT compact
@[simp]
example : True := .intro
