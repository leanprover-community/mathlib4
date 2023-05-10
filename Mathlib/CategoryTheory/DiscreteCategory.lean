/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn

! This file was ported from Lean 3 source module category_theory.discrete_category
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Data.ULift
import Mathlib.Tactic.CasesM

/-!
# Discrete categories

We define `Discrete α` as a structure containing a term `a : α` for any type `α`,
and use this type alias to provide a `SmallCategory` instance
whose only morphisms are the identities.

There is an annoying technical difficulty that it has turned out to be inconvenient
to allow categories with morphisms living in `Prop`,
so instead of defining `X ⟶ Y` in `Discrete α` as `X = Y`,
one might define it as `PLift (X = Y)`.
In fact, to allow `Discrete α` to be a `SmallCategory`
(i.e. with morphisms in the same universe as the objects),
we actually define the hom type `X ⟶ Y` as `ULift (PLift (X = Y))`.

`Discrete.functor` promotes a function `f : I → C` (for any category `C`) to a functor
`Discrete.functor f : Discrete I ⥤ C`.

Similarly, `Discrete.natTrans` and `Discrete.natIso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We show equivalences of types are the same as (categorical) equivalences of the corresponding
discrete categories.
-/

namespace CategoryTheory

-- morphism levels before object levels. See note [CategoryTheory universes].
universe v₁ v₂ v₃ u₁ u₁' u₂ u₃

-- This is intentionally a structure rather than a type synonym
-- to enforce using `DiscreteEquiv` (or `Discrete.mk` and `Discrete.as`) to move between
-- `Discrete α` and `α`. Otherwise there is too much API leakage.
/-- A wrapper for promoting any type to a category,
with the only morphisms being equalities.
-/
@[ext]
structure Discrete (α : Type u₁) where
  /-- A wrapper for promoting any type to a category,
  with the only morphisms being equalities.
  -/
  as : α
#align category_theory.discrete CategoryTheory.Discrete

@[simp]
theorem Discrete.mk_as {α : Type u₁} (X : Discrete α) : Discrete.mk X.as = X := by
  ext
  rfl
#align category_theory.discrete.mk_as CategoryTheory.Discrete.mk_as

/-- `Discrete α` is equivalent to the original type `α`.-/
@[simps]
def discreteEquiv {α : Type u₁} : Discrete α ≃ α where
  toFun := Discrete.as
  invFun := Discrete.mk
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align category_theory.discrete_equiv CategoryTheory.discreteEquiv

instance {α : Type u₁} [DecidableEq α] : DecidableEq (Discrete α) :=
  discreteEquiv.decidableEq

/-- The "Discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ULift (PLift (X = Y))`.

See <https://stacks.math.columbia.edu/tag/001A>
-/
instance discreteCategory (α : Type u₁) : SmallCategory (Discrete α) where
  Hom X Y := ULift (PLift (X.as = Y.as))
  id X := ULift.up (PLift.up rfl)
  comp {X Y Z} g f := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨⟨⟨⟩⟩⟩
    exact g
#align category_theory.discrete_category CategoryTheory.discreteCategory

namespace Discrete

variable {α : Type u₁}

instance [Inhabited α] : Inhabited (Discrete α) :=
  ⟨⟨default⟩⟩

instance [Subsingleton α] : Subsingleton (Discrete α) :=
  ⟨by
    intros
    ext
    apply Subsingleton.elim⟩

instance (X Y : Discrete α) : Subsingleton (X ⟶ Y) :=
  show Subsingleton (ULift (PLift _)) from inferInstance

/-
Porting note: It seems that `aesop` currently has no way to add lemmas locally.

attribute [local tidy] tactic.discrete_cases
`[cases_matching* [discrete _, (_ : discrete _) ⟶ (_ : discrete _), PLift _]]
-/

/- Porting note: rewrote `discrete_cases` tactic -/
/-- A simple tactic to run `cases` on any `discrete α` hypotheses. -/
macro "discrete_cases": tactic =>
  `(tactic|casesm* Discrete _, (_ : Discrete _) ⟶ (_ : Discrete _), PLift _)

instance [Unique α] : Unique (Discrete α) :=
  Unique.mk' (Discrete α)

/-- Extract the equation from a morphism in a discrete category. -/
theorem eq_of_hom {X Y : Discrete α} (i : X ⟶ Y) : X.as = Y.as :=
  i.down.down
#align category_theory.discrete.eq_of_hom CategoryTheory.Discrete.eq_of_hom

/-- Promote an equation between the wrapped terms in `X Y : Discrete α` to a morphism `X ⟶ Y`
in the discrete category. -/
protected abbrev eqToHom {X Y : Discrete α} (h : X.as = Y.as) : X ⟶ Y :=
  eqToHom
    (by
      ext
      exact h)
#align category_theory.discrete.eq_to_hom CategoryTheory.Discrete.eqToHom

/-- Promote an equation between the wrapped terms in `X Y : Discrete α` to an isomorphism `X ≅ Y`
in the discrete category. -/
protected abbrev eqToIso {X Y : Discrete α} (h : X.as = Y.as) : X ≅ Y :=
  eqToIso
    (by
      ext
      exact h)
#align category_theory.discrete.eq_to_iso CategoryTheory.Discrete.eqToIso

/-- A variant of `eqToHom` that lifts terms to the discrete category. -/
abbrev eqToHom' {a b : α} (h : a = b) : Discrete.mk a ⟶ Discrete.mk b :=
  Discrete.eqToHom h
#align category_theory.discrete.eq_to_hom' CategoryTheory.Discrete.eqToHom'

/-- A variant of `eqToIso` that lifts terms to the discrete category. -/
abbrev eqToIso' {a b : α} (h : a = b) : Discrete.mk a ≅ Discrete.mk b :=
  Discrete.eqToIso h
#align category_theory.discrete.eq_to_iso' CategoryTheory.Discrete.eqToIso'

@[simp]
theorem id_def (X : Discrete α) : ULift.up (PLift.up (Eq.refl X.as)) = 𝟙 X :=
  rfl
#align category_theory.discrete.id_def CategoryTheory.Discrete.id_def

variable {C : Type u₂} [Category.{v₂} C]

instance {I : Type u₁} {i j : Discrete I} (f : i ⟶ j) : IsIso f :=
  ⟨⟨Discrete.eqToHom (eq_of_hom f).symm, by aesop_cat⟩⟩

/-- Any function `I → C` gives a functor `Discrete I ⥤ C`.-/
def functor {I : Type u₁} (F : I → C) : Discrete I ⥤ C where
  obj := F ∘ Discrete.as
  map {X Y} f := by
    dsimp
    rcases f with ⟨⟨h⟩⟩
    exact eqToHom (congrArg _ h)
  map_id := by aesop_cat
  map_comp := fun {X Y Z} f g => by
    discrete_cases
    aesop_cat
#align category_theory.discrete.functor CategoryTheory.Discrete.functor

@[simp]
theorem functor_obj {I : Type u₁} (F : I → C) (i : I) :
    (Discrete.functor F).obj (Discrete.mk i) = F i :=
  rfl
#align category_theory.discrete.functor_obj CategoryTheory.Discrete.functor_obj

theorem functor_map {I : Type u₁} (F : I → C) {i : Discrete I} (f : i ⟶ i) :
    (Discrete.functor F).map f = 𝟙 (F i.as) := by aesop_cat
#align category_theory.discrete.functor_map CategoryTheory.Discrete.functor_map

/-- The discrete functor induced by a composition of maps can be written as a
composition of two discrete functors.
-/
@[simps!]
def functorComp {I : Type u₁} {J : Type u₁'} (f : J → C) (g : I → J) :
    Discrete.functor (f ∘ g) ≅ Discrete.functor (Discrete.mk ∘ g) ⋙ Discrete.functor f :=
  NatIso.ofComponents (fun X => Iso.refl _) (by aesop_cat)
#align category_theory.discrete.functor_comp CategoryTheory.Discrete.functorComp

/-- For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
@[simps]
def natTrans {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ⟶ G.obj i) : F ⟶ G
    where
  app := f
  naturality := fun {X Y} ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp
#align category_theory.discrete.nat_trans CategoryTheory.Discrete.natTrans

/-- For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
@[simps!]
def natIso {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i) : F ≅ G :=
  NatIso.ofComponents f fun ⟨⟨g⟩⟩ => by
    discrete_cases
    rcases g
    change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
    simp
#align category_theory.discrete.nat_iso CategoryTheory.Discrete.natIso

@[simp]
theorem natIso_app {I : Type u₁} {F G : Discrete I ⥤ C} (f : ∀ i : Discrete I, F.obj i ≅ G.obj i)
    (i : Discrete I) : (Discrete.natIso f).app i = f i := by aesop_cat
#align category_theory.discrete.nat_iso_app CategoryTheory.Discrete.natIso_app

/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `discrete.functor (F.obj)`. -/
@[simp]
def natIsoFunctor {I : Type u₁} {F : Discrete I ⥤ C} : F ≅ Discrete.functor (F.obj ∘ Discrete.mk) :=
  natIso fun _ => Iso.refl _
#align category_theory.discrete.nat_iso_functor CategoryTheory.Discrete.natIsoFunctor

/-- Composing `discrete.functor F` with another functor `G` amounts to composing `F` with `G.obj` -/
@[simp]
def compNatIsoDiscrete {I : Type u₁} {D : Type u₃} [Category.{v₃} D] (F : I → C) (G : C ⥤ D) :
    Discrete.functor F ⋙ G ≅ Discrete.functor (G.obj ∘ F) :=
  natIso fun _ => Iso.refl _
#align category_theory.discrete.comp_nat_iso_discrete CategoryTheory.Discrete.compNatIsoDiscrete

/-- We can promote a type-level `Equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
def equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : Discrete I ≌ Discrete J where
  functor := Discrete.functor (Discrete.mk ∘ (e : I → J))
  inverse := Discrete.functor (Discrete.mk ∘ (e.symm : J → I))
  unitIso :=
    Discrete.natIso fun i =>
      eqToIso
        (by
          discrete_cases
          simp)
  counitIso :=
    Discrete.natIso fun j =>
      eqToIso
        (by
          discrete_cases
          simp)
#align category_theory.discrete.equivalence CategoryTheory.Discrete.equivalence

/-- We can convert an equivalence of `discrete` categories to a type-level `Equiv`. -/
@[simps]
def equivOfEquivalence {α : Type u₁} {β : Type u₂} (h : Discrete α ≌ Discrete β) : α ≃ β where
  toFun := Discrete.as ∘ h.functor.obj ∘ Discrete.mk
  invFun := Discrete.as ∘ h.inverse.obj ∘ Discrete.mk
  left_inv a := by simpa using eq_of_hom (h.unitIso.app (Discrete.mk a)).2
  right_inv a := by simpa using eq_of_hom (h.counitIso.app (Discrete.mk a)).1
#align category_theory.discrete.equiv_of_equivalence CategoryTheory.Discrete.equivOfEquivalence

end Discrete

namespace Discrete

variable {J : Type v₁}

open Opposite

/-- A discrete category is equivalent to its opposite category. -/
@[simps! functor_obj_as inverse_obj]
protected def opposite (α : Type u₁) : (Discrete α)ᵒᵖ ≌ Discrete α :=
  let F : Discrete α ⥤ (Discrete α)ᵒᵖ := Discrete.functor fun x => op (Discrete.mk x)
  Equivalence.mk F.leftOp F
  (NatIso.ofComponents (fun ⟨X⟩ => Iso.refl _) <| fun {X Y} => by
      induction X using Opposite.rec
      induction Y using Opposite.rec
      discrete_cases
      intro f
      rcases f
      aesop_cat)
  (Discrete.natIso <| fun ⟨X⟩ => Iso.refl _)

/-
  Porting note:
  The following is what was generated by mathport:

  refine'
    Equivalence.mk (F.leftOp) F _
      (Discrete.natIso fun X =>
        by
          discrete_cases
          rfl)
  refine'
    NatIso.ofComponents
      (fun X =>
        by
        discrete_cases
        induction X using Opposite.rec
        discrete_cases
        exact Iso.refl _)
-/

#align category_theory.discrete.opposite CategoryTheory.Discrete.opposite

variable {C : Type u₂} [Category.{v₂} C]

@[simp]
theorem functor_map_id (F : Discrete J ⥤ C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j) :=
  by
  have h : f = 𝟙 j := by
    rcases f with ⟨⟨f⟩⟩
    rfl
  rw [h]
  simp
#align category_theory.discrete.functor_map_id CategoryTheory.Discrete.functor_map_id

end Discrete

end CategoryTheory
