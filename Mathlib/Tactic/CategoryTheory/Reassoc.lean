/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Lean.Meta.Simp
import Mathlib.Tactic.Simps.Basic
import Mathlib.Util.AddRelatedDecl

/-!
# The `reassoc` attribute

Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ⟶ Y` in some category
will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

There is also a term elaborator `reassoc_of% t` for use within proofs.

The `Mathlib.Tactic.CategoryTheory.IsoReassoc` extends `@[reassoc]` and `reassoc_of%`
to support creating isomorphism reassociation lemmas.
-/

open Lean Meta Elab Tactic
open Mathlib.Tactic

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- A variant of `eq_whisker` with a more convenient argument order for use in tactics. -/
theorem eq_whisker' {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) :
    f ≫ h = g ≫ h := by rw [w]

/-- Simplify an expression using only the axioms of a category. -/
def categorySimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Category.comp_id, ``Category.id_comp, ``Category.assoc,
    ``Functor.id_obj, ``Functor.id_map, ``Functor.comp_obj, ``Functor.comp_map] e
    (config := { decide := false })

/--
Given an equation `f = g` between morphisms `X ⟶ Y` in a category,
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
-/
def reassocExprHom (e : Expr) : MetaM Expr := do
  simpType categorySimp (← mkAppM ``eq_whisker' #[e])

/--
Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`, where `f g : X ⟶ Y` are
morphisms in some category, will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h`
but with the conclusions simplified using the axioms for a category
(`Category.comp_id`, `Category.id_comp`, and `Category.assoc`).
So, for example, if the conclusion of `F` is `a ≫ b = g` then
the conclusion of `F_assoc` will be `a ≫ (b ≫ h) = g ≫ h` (note that `≫` reassociates
to the right so the brackets will not appear in the statement).

This attribute is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.

Note that if you want both the lemma and the reassociated lemma to be
`simp` lemmas, you should tag the lemma `@[reassoc (attr := simp)]`.
The variant `@[simp, reassoc]` on a lemma `F` will tag `F` with `@[simp]`,
but not `F_assoc` (this is sometimes useful).

This attribute also works for lemmas of shape `∀ .., f = g` where `f g : X ≅ Y` are
isomorphisms, provided that `Tactic.CategoryTheory.IsoReassoc` has been imported.
-/
syntax (name := reassoc) "reassoc" (" (" &"attr" " := " Parser.Term.attrInstance,* ")")? : attr

/--
IO ref for reassociation handlers `reassoc` attribute, so that it can be extended
with additional handlers. Handlers take a proof of the equation.

The default handler is `reassocExprHom` for morphism reassociation.
This will be extended in `Tactic.CategoryTheory.IsoReassoc` for isomorphism reassociation.
-/
private initialize reassocImplRef : IO.Ref (Array (Expr → MetaM Expr)) ← IO.mkRef #[]

/--
Registers a handler for `reassocExpr`. The handler takes a proof of an equation
and returns a proof of the reassociation lemma.
Handlers are considered in order of registration.
They are applied directly to the equation in the body of the forall.
-/
def registerReassocExpr (f : Expr → MetaM Expr) : IO Unit := do
  reassocImplRef.modify (·.push f)

initialize registerReassocExpr reassocExprHom

/--
Reassociates the morphisms in `type?` using the registered handlers,
using `reassocExprHom` as the default.
If `type?` is not given, it is assumed to be the type of `pf`.
-/
def reassocExpr (pf : Expr) (type? : Option Expr) : MetaM Expr := do
  let pf ← if let some type := type? then mkExpectedTypeHint pf type else pure pf
  mapForallTelescope (forallTerm := pf) fun pf => do
    let handlers ← reassocImplRef.get
    handlers.firstM (fun h => h pf) <|> do
      throwError "`reassoc` can only be used on terms about equality of (iso)morphisms"

initialize registerBuiltinAttribute {
  name := `reassoc
  descr := ""
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| reassoc $[(attr := $stx?,*)]?) => MetaM.run' do
    if (kind != AttributeKind.global) then
      throwError "`reassoc` can only be used as a global attribute"
    addRelatedDecl src "_assoc" ref stx? fun type value levels => do
      pure (← reassocExpr value type, levels)
  | _ => throwUnsupportedSyntax }

/--
`reassoc_of% t`, where `t` is
an equation `f = g` between morphisms `X ⟶ Y` in a category (possibly after a `∀` binder),
produce the equation `∀ {Z} (h : Y ⟶ Z), f ≫ h = g ≫ h`,
but with compositions fully right associated and identities removed.
This also works for equations between isomorphisms, provided that
`Tactic.CategoryTheory.IsoReassoc` has been imported.
-/
elab "reassoc_of% " t:term : term => do
  let e ← Term.elabTerm t none
  reassocExpr e none

end CategoryTheory
