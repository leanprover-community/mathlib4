/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Lean.Meta.Simp

/-!
To avoid an initialization order issue, we move the `IO.Ref` declaration and other declarations
that it depends on into an earlier file.
-/

open Lean Meta

namespace CategoryTheory

#adaptation_note /- nightly-2025-08-25
This used to be defined in Reassoc.lean before `registerReassocExpr`.
-/

/-- A variant of `eq_whisker` with a more convenient argument order for use in tactics. -/
theorem eq_whisker' {C : Type*} [Category C]
    {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) :
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
Also returns the category `C` and any instance metavariables that need to be solved for.
-/
def reassocExprHom (e : Expr) : MetaM (Expr × Array MVarId) := do
  let lem₀ ← mkConstWithFreshMVarLevels ``eq_whisker'
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 7
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[6]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType categorySimp (mkAppN lem₀ args), #[inst.mvarId!])

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

#adaptation_note /- nightly-2025-08-25
This used to be private.
-/

/--
IO ref for reassociation handlers `reassoc` attribute, so that it can be extended
with additional handlers. Handlers take a proof of the equation.

The default handler is `reassocExprHom` for morphism reassociation.
This will be extended in `Tactic.CategoryTheory.IsoReassoc` for isomorphism reassociation.
-/
initialize reassocImplRef : IO.Ref (Array (Expr → MetaM (Expr × Array MVarId))) ←
  IO.mkRef #[reassocExprHom]

end CategoryTheory
