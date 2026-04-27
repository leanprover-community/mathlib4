/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# The `mk_concrete_category` command

`mk_concrete_category C FC id comp` generates the standard initial boilerplate for a concrete
category whose morphisms are modeled by a bundled function type `FC`.

It creates a wrapper morphism structure `Hom`, a `Category` instance, a `ConcreteCategory`
instance, the public constructor `ofHom`, the projection abbreviation `Hom.hom`, and the basic
`dsimp`/round-trip lemmas.
-/

open Lean Elab Command
open CategoryTheory

namespace Mathlib.Tactic.CategoryTheory

/--
`mk_concrete_category C FC id comp` generates the standard boilerplate for a concrete category on
`C` whose underlying bundled hom type is `FC : C → C → Type*`, with identities given by `id` and
composition given by `comp`.

The command is intended to be used in the namespace of `C`. It creates declarations named `Hom`,
`Hom.hom`, `ofHom`, `hom_id`, `hom_comp`, `hom_ofHom`, and `ofHom_hom`.
-/
syntax (name := mkConcreteCategory) "mk_concrete_category " term:max ppSpace term:max ppSpace
  term:max ppSpace term:max : command

/-- Elaborator for `mk_concrete_category`. -/
@[command_elab mkConcreteCategory]
public meta def elabMkConcreteCategory : CommandElab := fun stx => do
  let `(mk_concrete_category $cat $FC $idTerm $compTerm) := stx
    | throwUnsupportedSyntax

  elabCommand <| ← set_option hygiene false in `(command|
    set_option backward.privateInPublic true in
    /-- The type of morphisms in this concrete category. -/
    @[ext]
    structure Hom (X Y : $cat) where
      private mk ::
      /-- The underlying bundled morphism. -/
      hom' : ($FC:term) X Y)

  elabCommand <| ← set_option hygiene false in `(command|
    set_option backward.privateInPublic true in
    set_option backward.privateInPublic.warn false in
    instance : CategoryTheory.Category $cat where
      Hom X Y := Hom X Y
      id X := ⟨($idTerm:term) X⟩
      comp f g := ⟨($compTerm:term) f.hom' g.hom'⟩)

  elabCommand <| ← set_option hygiene false in `(command|
    set_option backward.privateInPublic true in
    set_option backward.privateInPublic.warn false in
    instance : CategoryTheory.ConcreteCategory $cat $FC where
      hom := Hom.hom'
      ofHom := Hom.mk
      id_apply := by intros; rfl
      comp_apply := by intros; rfl)

  elabCommand <| ← set_option hygiene false in `(command|
    /-- Turn a categorical morphism back into its underlying bundled morphism. -/
    abbrev Hom.hom {X Y : $cat} (f : Hom X Y) :=
      CategoryTheory.ConcreteCategory.hom (C := $cat) f)

  elabCommand <| ← set_option hygiene false in `(command|
    /-- Typecheck a bundled morphism as a morphism in this concrete category. -/
    abbrev ofHom {X Y : $cat} (f : CategoryTheory.ToHom X Y) : X ⟶ Y :=
      CategoryTheory.ConcreteCategory.ofHom (C := $cat) f)

  elabCommand <| ← set_option hygiene false in `(command|
    /-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
    def Hom.Simps.hom (X Y : $cat) (f : Hom X Y) :=
      f.hom)

  elabCommand <| ← set_option hygiene false in `(command|
    initialize_simps_projections Hom (hom' → hom))

  elabCommand <| ← set_option hygiene false in `(command|
    @[simp]
    lemma hom_id {X : $cat} : (𝟙 X : X ⟶ X).hom = (($idTerm) X) :=
      rfl)

  elabCommand <| ← set_option hygiene false in `(command|
    @[simp]
    lemma hom_comp {X Y Z : $cat} (f : X ⟶ Y) (g : Y ⟶ Z) :
        (f ≫ g).hom = (($compTerm) f.hom g.hom) :=
      rfl)

  elabCommand <| ← set_option hygiene false in `(command|
    @[simp]
    lemma hom_ofHom {X Y : $cat} (f : CategoryTheory.ToHom X Y) : (ofHom f).hom = f :=
      rfl)

  elabCommand <| ← set_option hygiene false in `(command|
    @[simp]
    lemma ofHom_hom {X Y : $cat} (f : X ⟶ Y) : ofHom f.hom = f :=
      rfl)

end Mathlib.Tactic.CategoryTheory
