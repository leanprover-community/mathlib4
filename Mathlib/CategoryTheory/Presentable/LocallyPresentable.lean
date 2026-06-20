/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Presentable.CardinalFilteredPresentation

/-!
# Locally presentable and accessible categories

In this file, we define the notion of locally presentable and accessible
categories. We first define these notions for a category `C` relative to a
fixed regular cardinal `κ` (typeclasses `IsCardinalLocallyPresentable C κ`
and `IsCardinalAccessibleCategory C κ`). The existence of such a regular
cardinal `κ` is asserted in the typeclasses `IsLocallyPresentable` and
`IsAccessibleCategory`. We show that in a locally presentable or
accessible category, any object is presentable.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

public section

universe w v u

namespace CategoryTheory

open Limits Opposite

section

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- Given a regular cardinal `κ`, a category `C` is `κ`-locally presentable
if it is cocomplete and admits a (small) family `G : ι → C` of `κ`-presentable
objects such that any object identifies as a `κ`-filtered colimit of these objects. -/
class IsCardinalLocallyPresentable : Prop
  extends HasCardinalFilteredGenerator C κ, HasColimitsOfSize.{w, w} C where

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := inferInstance

/-- Given a regular cardinal `κ`, a category `C` is `κ`-accessible
if it has `κ`-filtered colimits and admits a (small) family `G : ι → C` of `κ`-presentable
objects such that any object identifies as a `κ`-filtered colimit of these objects. -/
class IsCardinalAccessibleCategory : Prop
  extends HasCardinalFilteredGenerator C κ, HasCardinalFilteredColimits.{w} C κ where

instance [IsCardinalLocallyPresentable C κ] : IsCardinalAccessibleCategory C κ where

example (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalAccessibleCategory C κ] :
    ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable C κ) := inferInstance

section Finite

open Cardinal
attribute [local instance] fact_isRegular_aleph0

/-- A category is locally finitely presentable if it is locally `ℵ₀`-presentable. -/
abbrev IsLocallyFinitelyPresentable :=
  IsCardinalLocallyPresentable.{w} C ℵ₀

/-- A category is finitely accessible if it is `ℵ₀`-accessible. -/
abbrev IsFinitelyAccessibleCategory :=
  IsCardinalAccessibleCategory.{w} C ℵ₀

end Finite

end

section

/-- A category `C` is locally presentable if it is `κ`-locally presentable
for some regular cardinal `κ`. -/
@[pp_with_univ]
class IsLocallyPresentable (C : Type u) [hC : Category.{v} C] : Prop where
  exists_cardinal (C) [hC] : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalLocallyPresentable C κ

/-- A category `C` is accessible if it is `κ`-accessible
for some regular cardinal `κ`. -/
@[pp_with_univ]
class IsAccessibleCategory (C : Type u) [hC : Category.{v} C] : Prop where
  exists_cardinal (C) [hC] : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    IsCardinalAccessibleCategory C κ

variable (C : Type u) [hC : Category.{v} C]

instance [IsLocallyPresentable.{w} C] : IsAccessibleCategory.{w} C where
  exists_cardinal := by
    obtain ⟨κ, hκ, h'⟩ := IsLocallyPresentable.exists_cardinal C
    exact ⟨κ, hκ, inferInstance⟩

instance [IsAccessibleCategory.{w} C] (X : C) : IsPresentable.{w} X := by
  obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal C
  obtain ⟨_, _, h⟩ := HasCardinalFilteredGenerator.exists_generator C κ
  apply h.presentable

example [IsLocallyPresentable.{w} C] (X : C) : IsPresentable.{w} X := inferInstance

end

lemma ObjectProperty.le_isCardinalPresentable
    {C : Type u} [Category.{v} C] [IsAccessibleCategory.{w} C]
    (P : ObjectProperty C) [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (κ' : Cardinal.{w}) (_ : Fact κ'.IsRegular),
      P ≤ isCardinalPresentable C κ' := by
  obtain ⟨Q, hQ, h₁, h₂⟩ := EssentiallySmall.exists_small_le.{w} P
  choose κ hκ' hκ using fun (X : Subtype Q) ↦
    Functor.IsAccessible.exists_cardinal (coyoneda.obj (op X.val))
  obtain ⟨κ', h₃, h₄⟩ := HasCardinalLT.exists_regular_cardinal_forall
    (fun i ↦ (κ i).ord.ToType)
  have : Fact κ'.IsRegular := ⟨h₃⟩
  refine ⟨κ', inferInstance, h₂.trans ((isoClosure_le_iff _ _).2 ?_)⟩
  intro X hX
  have := h₄ ⟨X, hX⟩
  simp only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_toType,
    Cardinal.card_ord] at this
  exact isCardinalPresentable_monotone C this.le _ (hκ ⟨X, hX⟩)

end CategoryTheory
