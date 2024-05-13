import Lean
import Mathlib.Tactic.Lemma
import Mathlib.adomaniLeanUtils.inspect_syntax

open Lean Elab Command

inspect
/-- docs -/
@[simp]
theorem hi_ : True := .intro

/-- `thmNoDoc cmd` checks whether the `cmd` is a `theorem` with no doc-string.
If that is the case, then it returns two syntax nodes: the one for `theorem` and the one
for the name of the theorem.
Otherwise, it returns none.
-/
def thmNoDoc : Syntax → Option (Syntax × Syntax)
  | .node _ ``Lean.Parser.Command.declaration #[
    -- the inner `#[]` detects the absence of a doc-string
    .node _ ``Lean.Parser.Command.declModifiers #[.node _ `null #[], _, _, _, _, _],
    .node _ ``Lean.Parser.Command.theorem #[
      thm@(.atom _ "theorem"),
      .node _ ``Lean.Parser.Command.declId #[id, _],
      _,
      _]
  ] => some (thm, id)
  | _ => none

elab "tt " cmd:command : command => do
  match thmNoDoc cmd with
    | none => return
    | some (thm, id) =>
      logInfoAt thm m!"'theorem' requires a doc-string. \
                       Either add one to '{id}' or use 'lemma' instead."
--  logInfo m!"{thmNoDoc cmd}"

tt
/- docs -/
@[simp]
theorem hi__ : True := sorry --.intro

tt
/- docs -/
@[simp]
example : True := .intro

tt
instance : Add Unit := sorry

tt
/- docs -/
@[simp]
lemma hi__ : True := .intro


--node Lean.Parser.Command.declaration, none
--|-node Lean.Parser.Command.declModifiers, none
--|   |-node null, none
--|   |   |-node Lean.Parser.Command.docComment, none
--|   |   |   |-atom original: ⟨⟩⟨ ⟩-- '/--'
--|   |   |   |-atom original: ⟨⟩⟨\n⟩-- 'docs -/'
--|   |-node null, none
--|   |   |-node Lean.Parser.Term.attributes, none
--|   |   |   |-atom original: ⟨⟩⟨⟩-- '@['
--|   |   |   |-node null, none
--|   |   |   |   |-node Lean.Parser.Term.attrInstance, none
--|   |   |   |   |   |-node Lean.Parser.Term.attrKind, none
--|   |   |   |   |   |   |-node null, none
--|   |   |   |   |   |-node Lean.Parser.Attr.simp, none
--|   |   |   |   |   |   |-atom original: ⟨⟩⟨⟩-- 'simp'
--|   |   |   |   |   |   |-node null, none
--|   |   |   |   |   |   |-node null, none
--|   |   |   |-atom original: ⟨⟩⟨\n⟩-- ']'
--|   |-node null, none
--|   |-node null, none
--|   |-node null, none
--|   |-node null, none
--|-node Lean.Parser.Command.theorem, none
--|   |-atom original: ⟨⟩⟨ ⟩-- 'theorem'
--|   |-node Lean.Parser.Command.declId, none
--|   |   |-ident original: ⟨⟩⟨ ⟩-- (hi_,hi_)
--|   |   |-node null, none
--|   |-node Lean.Parser.Command.declSig, none
--|   |   |-node null, none
--|   |   |-node Lean.Parser.Term.typeSpec, none
--|   |   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
--|   |   |   |-ident original: ⟨⟩⟨ ⟩-- (True,True)
