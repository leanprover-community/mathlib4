/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.SetTheory.Cardinal.Cofinality

/-! # Presentable objects

If `κ` is a regular cardinal, we introduce the notion of `κ`-filtered
category, which generalizes the notion of filtered category.
Indeed, we obtain the equivalence
`IsCardinalFiltered J ℵ₀ ↔ IsFiltered J`.

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-filtered category.

An object `X` of a category is `κ`-presentable (`IsPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w w' v' v u' u

namespace CategoryTheory

open Limits Opposite

section

/-- A category `J` is `κ`-filtered (for a regular cardinal `κ`) is
any functor `F : A ⥤ J` from a `κ`-small category (`Cardinal.mk (Arrow A) < κ`)
admits a cocone. -/
class IsCardinalFiltered (J : Type w) [SmallCategory J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  nonempty_cocone {A : Type w} [SmallCategory A] (F : A ⥤ J)
    (hA : Cardinal.mk (Arrow A) < κ) : Nonempty (Cocone F)

namespace IsCardinalFiltered

variable {J : Type w} [SmallCategory J] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

/-- A choice of cocone for a functor `F : A ⥤ J` such that `Cardinal.mk (Arrow A) < κ`
when `J` is a `κ`-filtered category. -/
noncomputable def cocone {A : Type w} [SmallCategory A]
    (F : A ⥤ J) (hA : Cardinal.mk (Arrow A) < κ) :
    Cocone F :=
  (nonempty_cocone (κ := κ) _ hA).some

/-- When `S : Set J` is of cardinality `< κ` and `J` is `κ`-filtered, this is
a choice of object in `J` which is the target of a map from any object in `S`. -/
noncomputable def max (S : Set J) (hS : Cardinal.mk S < κ) : J := by
  have : Cardinal.mk (Arrow (Discrete S)) < κ := by simpa using hS
  exact (cocone (Discrete.functor Subtype.val) this).pt

/-- When `S : Set J` is of cardinality `< κ` and `J` is `κ`-filtered,
this is a choice of map `s.1 ⟶ max S hS` for any `s : S`. -/
noncomputable def toMax (S : Set J) (hS : Cardinal.mk S < κ) (s : S) :
    s.1 ⟶ max S hS := by
  have : Cardinal.mk (Arrow (Discrete S)) < κ := by simpa using hS
  exact (cocone (Discrete.functor Subtype.val) this).ι.app ⟨s⟩

variable (J)

lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' ≤ κ) :
    IsCardinalFiltered J κ' where
  nonempty_cocone F hA := ⟨cocone F (lt_of_lt_of_le hA h)⟩

end IsCardinalFiltered

open IsCardinalFiltered in
lemma isFiltered_of_isCardinalDirected (J : Type w) [SmallCategory J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]:
    IsFiltered J := by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : Cardinal.mk (Arrow A) < κ := by
    refine lt_of_lt_of_le ?_ hκ.out.aleph0_le
    rw [Cardinal.mk_lt_aleph0_iff]
    infer_instance
  exact ⟨cocone F hA⟩

instance : Fact Cardinal.aleph0.IsRegular where
  out := Cardinal.isRegular_aleph0

lemma isCardinalFiltered_aleph0_iff (J : Type w) [SmallCategory J] :
    IsCardinalFiltered J Cardinal.aleph0 ↔ IsFiltered J := by
  constructor
  · intro
    exact isFiltered_of_isCardinalDirected J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [Cardinal.mk_lt_aleph0_iff] at hA
    have := ((Arrow.finite_iff A).1 hA).some
    exact ⟨IsFiltered.cocone F⟩

lemma isCardinalFiltered_preorder (J : Type w) [Preorder J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : ∀ (S : Set J) (_ : Cardinal.mk S < κ), ∃ (j : J), ∀ (s : S), s.1 ≤ j) :
    IsCardinalFiltered J κ where
  nonempty_cocone {A _ F hA} := by
    let S := Set.range F.obj
    have hS : Cardinal.mk S < κ := by
      let f : A → S := fun a ↦ ⟨F.obj a, ⟨a, rfl⟩⟩
      have hf : Function.Surjective f := by
        rintro ⟨_, ⟨a, rfl⟩⟩
        exact ⟨a, rfl⟩
      exact lt_of_le_of_lt (Cardinal.mk_le_of_surjective hf)
        (lt_of_le_of_lt (cardinal_le_cardinal_arrow A) hA)
    obtain ⟨j, hj⟩ := h S hS
    refine ⟨Cocone.mk j
      { app a := homOfLE (hj ⟨F.obj a, ⟨a, rfl⟩⟩)
        naturality _ _ _ := rfl }⟩

end

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

variable (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A functor is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-filtered category. -/
class IsAccessible : Prop where
  preservesColimitOfShape {J : Type w} [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F

lemma preservesColimitsOfShape_of_isAccessible [F.IsAccessible κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F :=
  IsAccessible.preservesColimitOfShape κ

variable {κ} in
lemma isAccessible_of_le
    [F.IsAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    F.IsAccessible κ' where
  preservesColimitOfShape {J _ _} := by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isAccessible κ J

end Functor

variable (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- An object `X` in a category is `κ`-presentable (for `κ` a regular cardinal)
when the functor `Hom(X, _)` preserves colimits indexed by
`κ`-filtered categories. -/
abbrev IsPresentable : Prop := (coyoneda.obj (op X)).IsAccessible κ

lemma preservesColimitsOfShape_of_isPresentable [IsPresentable X κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isAccessible κ J

variable {κ} in
lemma isPresentable_of_le [IsPresentable X κ]
    {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    IsPresentable X κ' :=
  (coyoneda.obj (op X)).isAccessible_of_le h

end CategoryTheory
