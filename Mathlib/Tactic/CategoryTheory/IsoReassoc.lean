/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Iso

/-!
# The `iso_reassoc` attribute

We extend `reassoc` for equality of isomorphisms.
Adding `@[iso_reassoc]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ≅ Y` in some category will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`
but with the conclusions simplified using basic propertions in isomorphisms in a category
(`Iso.trans_refl`, `Iso.refl_trans`, `Iso.trans_assoc`, `Iso.trans_symm`).

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

We provide an `iso_reassoc_of%` elaborator.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- A variant of `eq_whisker` with a more convenient argument order for use in tactics. -/
theorem iso_eq_whisker {X Y : C} {f g : X ≅ Y} (w : f = g) {Z : C} (h : Y ≅ Z) :
    f ≪≫ h = g ≪≫ h := by rw [w]

/-- Simplify an expression using only the axioms of a groupoid. -/
def categoryIsoSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Iso.trans_symm, ``Iso.trans_refl, ``Iso.refl_trans, ``Iso.trans_assoc,
    ``Iso.symm_self_id, ``Iso.self_symm_id, ``Iso.symm_self_id_assoc, ``Iso.self_symm_id_assoc,
    ``Functor.mapIso_trans, ``Functor.mapIso_symm, ``Functor.mapIso_refl, ``Functor.id_obj] e
    (config := { decide := false })

/--
Given an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly after a `∀` binder),
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
-/
def isoReassocExpr (e : Expr) : MetaM Expr := do
  mapForallTelescope (fun e => do simpType categoryIsoSimp (← mkAppM ``iso_eq_whisker #[e])) e

/--
Adding `@[iso_reassoc]` to a lemma named `F` of shape `∀ .., f = g`, where `f g : X ≅ Y` are
isomorphisms in some category, will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).
So, for example, if the conclusion of `F` is `a ≪≫ b = g` then
the conclusion of `F_assoc` will be `a ≪≫ (b ≪≫ h) = g ≪≫ h` (note that `≪≫` reassociates
to the right so the brackets will not appear in the statement).

This attribute is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

Note that if you want both the lemma and the reassociated lemma to be
`simp` lemmas, you should tag the lemma `@[reassoc (attr := simp)]`.
The variant `@[simp, reassoc]` on a lemma `F` will tag `F` with `@[simp]`,
but not `F_assoc` (this is sometimes useful).
-/
syntax (name := iso_reassoc)
  "iso_reassoc" (" (" &"attr" " := " Parser.Term.attrInstance,* ")")? : attr

initialize registerBuiltinAttribute {
  name := `iso_reassoc
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| iso_reassoc $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`iso_reassoc` can only be used as a global attribute"
    addRelatedDecl src "_assoc" ref stx? fun type value levels => do
      let e ← mkExpectedTypeHint value type
      let t ← forallTelescope type (fun _ e' => do
        match e'.eq? with
        | some (t, _, _) =>
          match t.app4? ``Iso with
          | some _ => isoReassocExpr e
          | _ => reassocExpr e
        | _ =>
          throwError "`iso_reassoc` can only be used on lemmas about equality of (iso)morphisms.")
      pure (t, levels)
  | _ => throwUnsupportedSyntax }

open Term in
/--
`iso_reassoc_of% t`, where `t` is
an equation `f = g` between isomorphisms `X ≅ Y` in a category (possibly after a `∀` binder),
produces the equation `∀ {Z} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`,
but with compositions fully right associated, identities removed, and compositions with an
inverse cancelled.
-/
elab "iso_reassoc_of% " t:term : term => do
  let e ← elabTerm t none
  forallTelescope e (fun _ e' => do
    match e'.eq? with
    | some (t, _, _) =>
      match t.app4? ``Iso with
      | some _ => isoReassocExpr e
      | _ =>  reassocExpr e
    | _ => throwError "`iso_reassoc` can only be used on lemmas whose conclusions are equalities.")

end CategoryTheory
