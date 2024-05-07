/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Algebra.Group.Defs
/-!
#  `to_ama` a command to convert from `MonoidAlgebra` to `AddMonoidAlgebra`

If `thm` is a theorem about `MonoidAlgebra`, then `to_ama thm` tries to add to the
environment the analogous result about `AddMonoidAlgebra`.
-/

open Lean Elab Command

namespace Mathlib.MA

/-- `toAddWords` performs a subset of what `to_additive` would do. -/
abbrev toAddWords : HashMap String String := HashMap.empty
  |>.insert "Mul"       "Add"
  |>.insert "Semigroup" "AddSemigroup"
  |>.insert "CommMonoid" "AddCommMonoid"
  |>.insert "Monoid" "AddMonoid"
  |>.insert "CommSemigroup" "AddCommSemigroup"
  |>.insert "MulOneClass" "AddZeroClass"
  |>.insert "MonoidHomClass" "AddMonoidHomClass"
  |>.insert "singleOneRingHom" "singleZeroRingHom"
  |>.insert "singleOneAlgHom" "singleZeroAlgHom"
  |>.insert "MonoidAlgebra" "AddMonoidAlgebra"
  |>.insert "monoid" "add_monoid"

/-- splits a string into maximal substrings consisting of either `[alpha]*` or `[non-alpha]*`. -/
def splitAlpha (s : String) : List String :=
  s.toList.groupBy (fun a b => (a.isAlpha && b.isAlpha)) |>.map (⟨·⟩)

/-- replaces "words" in a string using `convs`.  It breaks the string into "words"
grouping together maximal consecutive substrings consisting of
either `[alpha]*` or a single `non-alpha`. -/
def stringReplacements (convs : HashMap String String) (str : String) : String :=
  String.join <| (splitAlpha str).map fun s => (convs.find? s).getD s

def extraTranslations (s : String) : String :=
  let repls := [("single_one", "single_zero"), ("exists_mul", "exists_add")]
  Id.run do
  let mut str := s
  for (orig, new) in repls do
    str := str.replace orig new
  return str

variable (convs : HashMap String String) in
/-- converts a name involving `MonoidAlgebra` to a name involving `AddMonoidAlgebra`. -/
def nameToAdd : Name → Name
  | .str a b => .str (nameToAdd a) (extraTranslations <| stringReplacements convs b)
  | _ => default

variable {m} [Monad m] [MonadRef m] [MonadQuotation m]
  --[MonadLog m] [AddMessageContext m] [MonadOptions m]
  (convs : HashMap String String) (toMultArrow : Name) (toMult : Name) (toPlus : Array Syntax) in
/-- converts `WithBot _` to `ℕ∞` and `⊥` to `⊤`.
Useful when converting a `degree` with values in `WithBot ℕ` to a `trailingDegree` with values
in `ℕ∞`. -/
def MaxToMin (stx : Syntax) : m Syntax := do
  let stx ← stx.replaceM fun s => do
    match s.getId with
      | .anonymous => return none
      | v => return some (mkIdent (nameToAdd convs v))

  stx.replaceM fun s => do
    match s with
      | .node _ `«term_*_» #[a, _, b] =>
        if toPlus.contains a then
          return some <| ← `($(⟨a⟩) + $(⟨b⟩))
        else return none
      | .node _ ``Lean.Parser.Term.app #[.ident _ _ ama _, .node _ _ #[first, second]] =>
        match ama with
          | `AddMonoidAlgebra => if second.getId == toMult then return s else return none
          | `ofMagma          => if second.getId == toMult then return s else return none
          | `of               => if second.getId == toMult then return s else return none
          | `single => match first with
            | `(1)           => return some <| ← `($(mkIdent `single) 0 $(⟨second⟩))
            | `((1 : $type)) => return some <| ← `($(mkIdent `single) (0 : $(⟨type⟩)) $(⟨second⟩))
            | _ => return none
          | `Commute =>
            if toPlus.contains first then
              return some <| ← `($(mkIdent `AddCommute) $(⟨first⟩) $(⟨second⟩))
            else return none

          | _ => return none

      | .node _ ``Lean.Parser.Term.app #[.ident _ _ azc _, .node _ _ #[x]] =>
        match azc with
          | `One =>
            if toPlus.contains x then return some <| ← `($(mkIdent `Zero) $(⟨x⟩))
            else return none

          | `Finsupp.singleAddHom => return some <| ← `($(mkIdent `Finsupp.singleAddHom) 0)
          | `single =>
            if x == (← `(1)) then return some <| ← `($(mkIdent `single) 0) else return none
          | _ =>
            if azc == toMultArrow then
                    return some <| ← `($(mkIdent azc) ($(mkIdent `Multiplicative.ofAdd) $(⟨x⟩)))
            else
            if x.getId == toMult && azc ∈ [`Add, `AddZeroClass] then return s else return none

      | .node _ ``Lean.Parser.Term.app #[.ident _ _ cls _, .node _ _ #[F, a, b]] =>
        if cls ∉ [`OneHomClass, `MulHomClass] then return none else
        if toPlus.contains a then
          let repl := if cls == `OneHomClass then `ZeroHomClass else `AddHomClass
          let zhc := mkNode ``Lean.Parser.Term.app #[mkIdent repl, mkNullNode #[F, a, b]]
          return some zhc
        else return none

      | .node _ `«term_^_» #[a, _, b] =>
        if toPlus.contains a then return some <| ← `($(⟨b⟩) • $(⟨a⟩))
        else return none

      | .ident _ _ `Commute.one_left _ => return some <| mkIdent `AddCommute.zero_left

      | .ident _ _ x _ => if x != toMult then return none else
                return some <| ← `($(mkIdent `Multiplicative) $(mkIdent x))
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
            let MultGtoR ← `($(mkIdent `Multiplicative) $(mkIdent `G) → $(mkIdent `R))
            return some <| Term.mkExplicitBinder (mkIdent `g) MultGtoR
      | _ => return none

/--
If `thm` is a theorem about `MonoidAlgebra`, then `to_ama thm` tries to add to the
environment the analogous result about `AddMonoidAlgebra`.

Writing `to_ama?` also prints the extra declaration added by `to_ama`.
-/
def toAmaCmd (verbose? : Bool) (id1 id2 : TSyntax `ident) (id3 : Array Syntax) (cmd : Syntax) :
    CommandElabM Unit := do
  let id1 := id1.getId
  let id2 := id2.getId
  let newCmd ← MaxToMin toAddWords id1 id2 id3 cmd
  if verbose? then logInfo m!"-- adding\n{newCmd}"
  elabCommand cmd
  if (← get).messages.hasErrors then return
  let currNS ← getCurrNamespace
  withScope (fun s => { s with currNamespace := nameToAdd toAddWords currNS }) <| elabCommand newCmd

@[inherit_doc toAmaCmd]
elab "to_ama " tk:("?")? "[" id:(ident)? "]" cmd:command : command =>
  let rid := mkIdent `hi
  toAmaCmd tk.isSome (id.getD default) rid #[] cmd

@[inherit_doc toAmaCmd]
elab "to_ama " tk:("?")? id:ident cmd:command : command =>
  toAmaCmd tk.isSome default id #[] cmd

@[inherit_doc toAmaCmd]
elab "to_ama " tk:("?")? i1:(ident)? "plus" id:term,* cmd:command : command => do
  toAmaCmd tk.isSome default (i1.getD default) (id.getElems.map (·.raw)) cmd

@[inherit_doc toAmaCmd]
elab "to_ama " tk:("?")? cmd:command : command =>
  toAmaCmd tk.isSome default default #[] cmd
