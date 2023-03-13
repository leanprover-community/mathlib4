/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Lean.Meta.Simp

/-!
# The `reasoc` attribute

Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ⟶ Y` in some category
will create a new lemmas named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified used the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

There is also a term elaborator `reassoc_of% t` for use within proofs.
-/

open Lean Meta Elab Tactic

namespace CategoryTheory

variable {C : Type _} [Category C]

/-- A variant of `eq_whisker` with a more convenient argument order for use in tactics.  -/
theorem eq_whisker' {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) :
    f ≫ h = g ≫ h := by rw [w]

/-- Simplify an expression using only the axioms of a category. -/
def categorySimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Category.comp_id, ``Category.id_comp, ``Category.assoc] e

/--
Given an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly after a `∀` binder),
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
-/
def reassocExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType categorySimp (← mkAppM ``eq_whisker' #[e])) e

/-- Syntax for the `reassoc` attribute -/
syntax (name := reassoc) "reassoc" ("(" &"attr" ":=" Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `reassoc
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| reassoc $[(attr := $stx?,*)]?) => MetaM.run' do
    let tgt := match src with
      | Name.str n s => Name.mkStr n $ s ++ "_assoc"
      | x => x
    if (kind != AttributeKind.global) then
      throwError "`reassoc` can only be used as a global attribute"
    addDeclarationRanges tgt {
      range := ← getDeclarationRange (← getRef)
      selectionRange := ← getDeclarationRange ref }
    let info ← getConstInfo src
    -- We use `info.type` to give an expected type hint for `info.value!`
    -- before passing to `reassoc`,
    -- so that `reassoc` simplifies the declared type,
    -- rather than reading the proof and inferring a type from that.
    let newValue ← reassocExpr (← mkExpectedTypeHint info.value! info.type)
    let newType ← inferType newValue
    match info with
    | ConstantInfo.thmInfo info =>
      addAndCompile <| .thmDecl { info with type := newType, name := tgt, value := newValue }
    | ConstantInfo.defnInfo info =>
      -- It looks a bit weird that we use `.thmDecl` here too,
      -- but apparently structure fields are created using `def`
      -- even with they are propositional. If `reassoc` worked, it was a `Prop` anyway.
      addAndCompile <| .thmDecl { info with type := newType, name := tgt, value := newValue }
    | _ => throwError "Constant {src} is not a theorem or definition."
    if isProtected (← getEnv) src then
      setEnv $ addProtected (← getEnv) tgt
    let stx := match stx? with | some stx => stx | none => #[]
    _ ← Term.TermElabM.run' <| ToAdditive.applyAttributes ref stx `reassoc src tgt
  | _ => throwUnsupportedSyntax }

open Term in
/--
`reassoc_of% t`, where `t` is
an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly after a `∀` binder),
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
-/
elab "reassoc_of% " t:term : term => do
  reassocExpr (← elabTerm t none)

end CategoryTheory
