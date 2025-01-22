/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Shapes.WideEqualizers
import Mathlib.CategoryTheory.Comma.CardinalArrow
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # κ-filtered category

If `κ` is a regular cardinal, we introduce the notion of `κ`-filtered
category `J`: it means that any functor `A ⥤ J` from a small category such
that `Arrow A` is of cardinality `< κ` admits a cocone.
This generalizes the notion of filtered category.
Indeed, we obtain the equivalence `IsCardinalFiltered J ℵ₀ ↔ IsFiltered J`.
The API is mostly parallel to that of filtered categories.

A preordered type `J` is a `κ`-filtered category (i.e. `κ`-directed set)
if any subset of `J` of cardinality `< κ` has an upper bound.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

/-- A category `J` is `κ`-filtered (for a regular cardinal `κ`) if
any functor `F : A ⥤ J` from a category `A` such that `HasCardinalLT (Arrow A) κ`
admits a cocone. -/
class IsCardinalFiltered (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  nonempty_cocone {A : Type w} [SmallCategory A] (F : A ⥤ J)
    (hA : HasCardinalLT (Arrow A) κ) : Nonempty (Cocone F)

lemma hasCardinalLT_arrow_walkingParallelFamily {T : Type u}
    {κ : Cardinal.{w}} (hT : HasCardinalLT T κ) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (Arrow (WalkingParallelFamily T)) κ := by
  simpa only [hasCardinalLT_iff_of_equiv (WalkingParallelFamily.arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ] using hT

namespace IsCardinalFiltered

variable {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

/-- A choice of cocone for a functor `F : A ⥤ J` such that `HasCardinatLT (Arrow A) κ`
when `J` is a `κ`-filtered category, and `Arrow A` has cardinality `< κ`. -/
noncomputable def cocone {A : Type v'} [Category.{u'} A]
    (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ) :
    Cocone F := by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocones.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inverse ⋙ F) (by simpa)).some

variable (J) in
lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' ≤ κ) :
    IsCardinalFiltered J κ' where
  nonempty_cocone F hA := ⟨cocone F (hA.of_le h)⟩

section max

variable {K : Type u'} (S : K → J) (hS : HasCardinalLT K κ)

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a  choice of objects in `J` which is the target of a map from any of
the objects `S k`. -/
noncomputable def max : J :=
  (cocone (Discrete.functor S) (by simpa using hS)).pt

/-- If `S : K → J` is a family of objects of cardinality `< κ` in a `κ`-filtered category,
this is a choice of map `S k ⟶ max S hS` for any `k : K`. -/
noncomputable def toMax (k : K) :
    S k ⟶ max S hS :=
  (cocone (Discrete.functor S) (by simpa using hS)).ι.app ⟨k⟩

end max

section coeq

variable {K : Type v'} {j j' : J} (f : K → (j ⟶ j')) (hK : HasCardinalLT K κ)

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, this is an object of `J` where these morphisms
shall be equalized. -/
noncomputable def coeq : J :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).pt

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, and `k : K`, this is a choice of morphism `j' ⟶ coeq f hK`. -/
noncomputable def coeqHom : j' ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .one

/-- Given a family of maps `f : K → (j ⟶ j')` in a `κ`-filtered category `J`,
with `HasCardinalLT K κ`, this is a morphism `j ⟶ coeq f hK` which is equal
to all compositions `f k ≫ coeqHom f hK` for `k : K`. -/
noncomputable def toCoeq : j ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .zero

@[reassoc]
lemma coeq_condition (k : K) : f k ≫ coeqHom f hK = toCoeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).w
    (.line k)

end coeq

end IsCardinalFiltered

open IsCardinalFiltered in
lemma isFiltered_of_isCardinalDirected (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ] :
    IsFiltered J := by
  rw [IsFiltered.iff_cocone_nonempty.{w}]
  intro A _ _ F
  have hA : HasCardinalLT (Arrow A) κ := by
    refine HasCardinalLT.of_le ?_ hκ.out.aleph0_le
    simp only [hasCardinalLT_aleph0_iff]
    infer_instance
  exact ⟨cocone F hA⟩

attribute [local instance] Cardinal.fact_isRegular_aleph0

lemma isCardinalFiltered_aleph0_iff (J : Type u) [Category.{v} J] :
    IsCardinalFiltered J Cardinal.aleph0.{w} ↔ IsFiltered J := by
  constructor
  · intro
    exact isFiltered_of_isCardinalDirected J Cardinal.aleph0
  · intro
    constructor
    intro A _ F hA
    rw [hasCardinalLT_aleph0_iff] at hA
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

end CategoryTheory
