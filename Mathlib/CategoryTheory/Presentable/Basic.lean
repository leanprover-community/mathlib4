/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.HasCardinalLT

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

universe w w' v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite

section

/-- A category `J` is `κ`-filtered (for a regular cardinal `κ`) is
any functor `F : A ⥤ J` from a `κ`-small category (`Cardinal.mk (Arrow A) < κ`)
admits a cocone. -/
class IsCardinalFiltered (J : Type u') [Category.{v'} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  nonempty_cocone {A : Type w} [SmallCategory A] (F : A ⥤ J)
    (hA : HasCardinalLT (Arrow A) κ) : Nonempty (Cocone F)

namespace IsCardinalFiltered

variable {J : Type u'} [Category.{v'} J] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

/-- A choice of cocone for a functor `F : A ⥤ J` such that `Cardinal.mk (Arrow A) < κ`
when `J` is a `κ`-filtered category. -/
noncomputable def cocone {A : Type v''} [Category.{u''} A]
    (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ) :
    Cocone F := by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocones.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inverse ⋙ F) (by simpa)).some

--/-- When `S : Set J` is of cardinality `< κ` and `J` is `κ`-filtered, this is
--a choice of object in `J` which is the target of a map from any object in `S`. -/
noncomputable def max {K : Type v''} (S : K → J) (hS : HasCardinalLT K κ) : J := by
  have : HasCardinalLT (Arrow (Discrete K)) κ := by simpa using hS
  exact (cocone (Discrete.functor S) this).pt

/-- When `S : Set J` is of cardinality `< κ` and `J` is `κ`-filtered,
this is a choice of map `s.1 ⟶ max S hS` for any `s : S`. -/
noncomputable def toMax {K : Type v''} (S : K → J) (hS : HasCardinalLT K κ) (k : K) :
    S k ⟶ max S hS := by
  have : HasCardinalLT (Arrow (Discrete K)) κ := by simpa using hS
  exact (cocone (Discrete.functor S) this).ι.app ⟨k⟩

variable (J)

lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' ≤ κ) :
    IsCardinalFiltered J κ' where
  nonempty_cocone F hA := ⟨cocone F (hA.of_le h)⟩

end IsCardinalFiltered

open IsCardinalFiltered in
lemma isFiltered_of_isCardinalDirected (J : Type u') [Category.{v'} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]:
    IsFiltered J := by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : HasCardinalLT (Arrow A) κ := by
    refine HasCardinalLT.of_le ?_ hκ.out.aleph0_le
    simp only [hasCardinalLT_aleph0]
    infer_instance
  exact ⟨cocone F hA⟩

instance : Fact Cardinal.aleph0.IsRegular where
  out := Cardinal.isRegular_aleph0

lemma isCardinalFiltered_aleph0_iff (J : Type u') [Category.{v'} J] :
    IsCardinalFiltered J Cardinal.aleph0 ↔ IsFiltered J := by
  constructor
  · intro
    exact isFiltered_of_isCardinalDirected J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [hasCardinalLT_aleph0] at hA
    have := ((Arrow.finite_iff A).1 hA).some
    exact ⟨IsFiltered.cocone F⟩

lemma isCardinalFiltered_preorder (J : Type w) [Preorder J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (h : ∀ ⦃K : Type w⦄ (s : K → J) (_ : Cardinal.mk K < κ),
      ∃ (j : J), ∀ (k : K), s k ≤ j) :
    IsCardinalFiltered J κ where
  nonempty_cocone {A _ F hA} := by
    obtain ⟨j, hj⟩ := h F.obj (by simpa only [hasCardinalLT_iff_cardinal_mk_lt] using
        hasCardinalLT_of_hasCardinalLT_arrow hA)
    exact ⟨Cocone.mk j
      { app a := homOfLE (hj a)
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
