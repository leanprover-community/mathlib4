/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Order.Notation
/-!
#  `to_top` a command to convert from `Bot` to `Top`

If `thm` is a theorem about `WithBot`, then `to_top thm` tries to add to the
environment the analogous result about `WithTop`.
-/

open Lean Elab Command

namespace Mathlib.MA

--/-- the core of the string translation.  These replacements are applied to individual "segments"
--after grouping words and splitting further at uppercase letter. -/
--abbrev segmentReplacements : HashMap String String := HashMap.empty
--  |>.insert "⊥"      "⊤"
--  |>.insert "max"    "min"
--  |>.insert "Sup"    "Inf"
--  |>.insert "sup"    "inf"
--  |>.insert "Bot"    "Top"
--  |>.insert "bot"    "top"
--  |>.insert "unbot"  "untop"
--  |>.insert "union"  "inter"
--  |>.insert "inter"  "union"

abbrev botTop : HashMap String String := HashMap.empty
  |>.insert "⊥"      "⊤"
  |>.insert "Mul"    "Add"
  |>.insert "Bot"    "Top"
  |>.insert "bot"    "top"
  |>.insert "unbot"  "untop"
  |>.insert "union"  "inter"

/-- splits a string into maximal substrings consisting of either `[uppercase]*[lowercase]*` or
`[non-alpha]*`. -/
def splitUpper (s : String) : List String :=
  s.toList.groupBy (fun a b => a.isUpper || (a.isLower && b.isLower)) |>.map (⟨·⟩)

/-- some binary operations need to be reversed in the change `Bot` to `Top`, others stay unchanged.
`binopReplacements` performs some of these changes. -/
partial
def binopReplacements {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] (stx : Syntax) :
    m Syntax :=
  stx.replaceM fun s => do
    match s with
      | `(term| antisymm $ha $hb) => return some (← `($(mkIdent `antisymm) $hb $ha))
      | `(term| le_trans $ha $hb) => return some (← `($(mkIdent `le_trans) $hb $ha))
      | `(term| lt_trans $ha $hb) => return some (← `($(mkIdent `lt_trans) $hb $ha))
      | `(term| $ha ⊔ $hb) =>
        let ha' := ⟨← binopReplacements ha⟩
        let hb' := ⟨← binopReplacements hb⟩
        return some (← `(term| $ha' ⊓ $hb'))
      | `(term| $ha ∪ $hb) =>
        let ha' := ⟨← binopReplacements ha⟩
        let hb' := ⟨← binopReplacements hb⟩
        return some (← `(term| $ha' ∩ $hb'))
      | `(term| $ha ∩ $hb) =>
        let ha' := ⟨← binopReplacements ha⟩
        let hb' := ⟨← binopReplacements hb⟩
        return some (← `(term| $ha' ∪ $hb'))
      | `(term| $ha ≤ $hb) =>
        let ha' := ⟨← binopReplacements ha⟩
        let hb' := ⟨← binopReplacements hb⟩
        return some (← `(term| $ha' ≤ $hb'))
      | `(Lean.Parser.Term.typeAscription| (g : G → R)) => dbg_trace "found"; return some (← `(term| (g : Multiplicative G → R)))
      | _ => return none

/-- some names have consecutive parts that should be transposed.
`lelt` is one of the two parts. -/
abbrev lelt : HashSet String := { "le", "lt" }

/-- some names have consecutive parts that should be transposed.
`leftRight` is one of the two parts. -/
abbrev leftRight : HashSet String :=
  { "left", "right", "sup", "inf", "inter", "union", "none", "bot", "top", "trailingDegree" }

/-- `swapWords` uses `lelt` and `leftRight` to perform the swap in names.
E.g. it replaces `["none", "le"]` with `["le", "none"]`. -/
def swapWords : List String → List String
  | "Monoid"::"Algebra"::rest => "AddMonoidAlgebra"::swapWords rest
  | "monoid"::"_"::"algebra"::rest => "add_monoid_algebra"::swapWords rest
  | "le"::"_"::"of"::"_"::"eq"::rest => "ge"::"_"::"of"::"_"::"eq"::swapWords rest
  | "untop"::"'"::"_"::"le"::rest => "le"::"_"::"untop"::"'"::swapWords rest
  | le::"_"::left::ls =>
    if ((lelt.contains le) && (leftRight.contains left)) ||
       ((lelt.contains left) && (leftRight.contains le))
    then left::"_"::le::(swapWords ls)
    else le::"_"::swapWords (left :: ls)
  | le::left => le::swapWords left
  | [] => []

/-- replaces "words" in a string using `convs`.  It breaks the string into "words"
grouping together maximal consecutive substrings consisting of
either `[uppercase]*[lowercase]*` or a single `non-alpha`. -/
def stringReplacements (convs : HashMap String String) (str : String) : String :=
  let strs := (splitUpper str).map fun s => (convs.find? s).getD s
  String.join <| swapWords strs

variable (convs : HashMap String String) in
/-- converts a name involving `WithBot` to a name involving `WithTop`. -/
def nameToTop : Name → Name
  | .str a b => .str (nameToTop a) (stringReplacements convs b)
  | _ => default

variable (convs : HashMap String String) in
/-- converts `WithBot _` to `ℕ∞` and `⊥` to `⊤`.
Useful when converting a `degree` with values in `WithBot ℕ` to a `trailingDegree` with values
in `ℕ∞`. -/
def MaxToMin (stx : Syntax) : CommandElabM Syntax := do
  let stx ← stx.replaceM fun s => do
    match s.getId with
      | .anonymous => return none
      | v => return some (mkIdent (nameToTop convs v))

  stx.replaceM fun s => do
    match s with
      | .node _ ``Lean.Parser.Term.app #[.ident _ _ na _, .node _ _ #[b]] =>
        match na with
          | .str a "antisymm" => return some (← `($(mkIdent `antisymm) $(mkIdent a) $(⟨b⟩)))
          | .str a "trans_le" => return some (← `($(mkIdent `lt_of_le_of_lt) $(⟨b⟩) $(mkIdent a)))
          | `g => return some <| mkNode ``Lean.Parser.Term.app #[
                                  mkIdent na,
                                  mkNode `null #[mkNode ``Lean.Parser.Term.app #[
                                  mkIdent `Multiplicative.ofAdd,
                                  mkNode `null #[mkIdent b.getId]]]]
          | _ => return none
      | .node _ `«term⊥» #[.atom _ "⊥"] => return some (← `((⊤ : $(mkIdent `WithTop) _)))
      | .atom _ s =>
        if s.contains '⊥' then return some (mkAtom (s.replace "⊥" "⊤")) else return none
      | .node _ `«term_≤_» #[a, _, b] => return some (← `($(⟨b⟩) ≤ $(⟨a⟩)))
--      | .node _ `«term_<_» #[a, _, b] => return some (← `($(⟨b⟩) < $(⟨a⟩)))
      | .node _ ``Lean.Parser.Command.docComment #[init, .atom _ docs] =>
        let newDocs := stringReplacements convs docs
        let newDocs :=
          if newDocs == docs
          then "[recycled by `to_top`] " ++ docs
          else "[autogenerated by `to_top`] " ++ newDocs
        let nd := mkNode ``Lean.Parser.Command.docComment #[init, mkAtom newDocs]
        return some nd
      | .node _ ``Lean.Parser.Term.explicitBinder
        #[_, -- `(`
          .node _ _ #[.ident _ _ `g _],
          .node _ _ #[
            _, -- `:`
            .node _ ``Lean.Parser.Term.arrow
            #[.ident _ _ `G _,
              .atom _ _,
              .ident _ _ `R _]],
          _, _] => -- `)`
            return some <| mkNode ``Lean.Parser.Term.explicitBinder #[
                mkAtom "(",
                mkNode `null #[mkIdent `g],
                mkNode `null #[
                  mkAtom ":",
                  mkNode ``Lean.Parser.Term.arrow #[
                    mkNode ``Lean.Parser.Term.app #[
                      mkIdent `Multiplicative,
                      mkNode `null #[mkIdent `G]],
                    mkAtom "→", mkIdent "R"]],
                mkNode `null #[],
                mkAtom ")"]
      | _ => return none
--|-mkNode ``Lean.Parser.Term.app #[mkIdent `Multiplicative, mkNode ``null #[mkIdent `G]]
--|   |-node null, none
--|   |   |-ident original: ⟨⟩⟨\n\n⟩-- (G,G)
--|-node Lean.Parser.Term.app, none
--|   |-ident original: ⟨⟩⟨ ⟩-- (Multiplicative,Multiplicative)
--|   |-node null, none
--|   |   |-ident original: ⟨⟩⟨\n\n⟩-- (G,G)


--|-node Lean.Parser.Term.explicitBinder, none
--|   |-atom original: ⟨⟩⟨⟩-- '('
--|   |-node null, none
--|   |   |-ident original: ⟨⟩⟨ ⟩-- (f,f)
--|   |-node null, none
--|   |   |-atom original: ⟨⟩⟨ ⟩-- ':'
--|   |   |-node Lean.Parser.Term.arrow, none
--|   |   |   |-ident original: ⟨⟩⟨ ⟩-- (G,G)
--|   |   |   |-atom original: ⟨⟩⟨ ⟩-- '→'
--|   |   |   |-ident original: ⟨⟩⟨⟩-- (R,R)
--|   |-node null, none
--|   |-atom original: ⟨⟩⟨ ⟩-- ')'



def translation (convs : HashMap String String) (stx : Syntax) : CommandElabM Syntax := do
  binopReplacements <| ← MaxToMin convs stx
/--
If `thm` is a theorem about `WithBot`, then `to_top thm` tries to add to the
environment the analogous result about `WithTop`.

Writing `to_top?` also prints the extra declaration added by `to_top`.
-/
elab (name := to_amaCmd) "to_ama " tk:"?"? cmd:command : command => do
  let newCmd ← binopReplacements <| ← MaxToMin botTop cmd
  if tk.isSome then logInfo m!"-- adding\n{newCmd}"
  elabCommand cmd
  let currNS ← getCurrNamespace
  withScope (fun s => { s with currNamespace := nameToTop botTop currNS }) <| elabCommand newCmd

@[inherit_doc to_amaCmd]
macro "to_ama? " cmd:command : command => return (← `(to_ama ? $cmd))

--variable {X Y G H R}
--set_option linter.unusedVariables false in
--to_ama?
--example (f : X → Y) (h : H) (g : H → Prop) : g h := sorry
