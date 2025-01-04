/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Presentable objects

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsCardinalAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-filtered category
(that is essentially small relative to the universe `w` such that `κ : Cardinal.{w}`.).
We also introduce another typeclass `Functor.IsAccessible` saying that there exists
a regular cardinal `κ` such that `Functor.IsCardinalAccessible`.

An object `X` of a category is `κ`-presentable (`IsCardinalPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.
Similar as for accessible functors, we define a type class `IsAccessible`.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w w' v'' v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Limits Opposite

namespace Limits

namespace Types

variable {J : Type u₁} [Category.{v₁} J]

namespace uliftFunctor

variable {F : J ⥤ Type w'} (c : Cocone F)

variable (F) in
def quotEquiv : Quot F ≃ Quot (F ⋙ uliftFunctor.{w}) where
  toFun := Quot.lift (fun ⟨j, x⟩ ↦ Quot.ι _ j (ULift.up x)) (by
    rintro ⟨j₁, x₁⟩ ⟨j₂, x₂⟩ ⟨f, h⟩
    dsimp at f h
    exact Quot.sound ⟨f, by simp [h]⟩)
  invFun := Quot.lift (fun ⟨j, x⟩ ↦ Quot.ι _ j (ULift.down x)) (by
    rintro ⟨j₁, ⟨x₁⟩⟩ ⟨j₂, ⟨x₂⟩⟩ ⟨f, h⟩
    dsimp at f h ⊢
    refine Quot.sound ⟨f, by simpa using h⟩)
  left_inv := by rintro ⟨_, _⟩; rfl
  right_inv := by rintro ⟨_, _⟩; rfl

lemma quotEquiv_comm :
    Quot.desc (uliftFunctor.{w}.mapCocone c) ∘ quotEquiv F =
    ULift.up ∘ Quot.desc c := by
  ext ⟨j, x⟩
  simp [quotEquiv]
  rfl

lemma isColimit_cocone_iff :
    Nonempty (IsColimit c) ↔ Nonempty (IsColimit (uliftFunctor.{w}.mapCocone c)) := by
  simp only [isColimit_iff_bijective_desc]
  rw [← Function.Bijective.of_comp_iff _ ((quotEquiv F).bijective), quotEquiv_comm.{w} c,
    ← Function.Bijective.of_comp_iff' Equiv.ulift.symm.bijective]
  rfl

noncomputable def isColimitEquiv :
    IsColimit c ≃ IsColimit (uliftFunctor.{w}.mapCocone c) where
  toFun hc := ((isColimit_cocone_iff c).1 ⟨hc⟩).some
  invFun hc := ((isColimit_cocone_iff c).2 ⟨hc⟩).some
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

instance : PreservesColimit F (uliftFunctor.{w, w'}) where
  preserves {c} hc := ⟨isColimitEquiv c hc⟩

instance : ReflectsColimit F (uliftFunctor.{w, w'}) where
  reflects {c} hc := ⟨(isColimitEquiv c).symm hc⟩

instance : PreservesColimitsOfShape J (uliftFunctor.{w, w'}) where

instance : ReflectsColimitsOfShape J (uliftFunctor.{w, w'}) where

end uliftFunctor

instance : PreservesColimitsOfSize.{v₁, u₁} (uliftFunctor.{w, w'}) where
instance : ReflectsColimitsOfSize.{v₁, u₁} (uliftFunctor.{w, w'}) where

end Types

end Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

section

variable (F G : C ⥤ D) (e : F ≅ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A functor is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-filtered category. -/
class IsCardinalAccessible : Prop where
  preservesColimitOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F

lemma preservesColimitsOfShape_of_isCardinalAccessible [F.IsCardinalAccessible κ]
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F :=
  IsCardinalAccessible.preservesColimitOfShape κ _

lemma preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall
    [F.IsCardinalAccessible κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by
  have := IsCardinalFiltered.of_equivalence κ (equivSmallModel.{w} J)
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ (SmallModel.{w} J)
  exact preservesColimitsOfShape_of_equiv (equivSmallModel.{w} J).symm F

variable {κ} in
lemma isCardinalAccessible_of_le
    [F.IsCardinalAccessible κ] {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    F.IsCardinalAccessible κ' where
  preservesColimitOfShape {J _ _} := by
    have := IsCardinalFiltered.of_le J h
    exact F.preservesColimitsOfShape_of_isCardinalAccessible κ J

include e in
variable {F G} in
lemma isCardinalAccessible_of_iso [F.IsCardinalAccessible κ] : G.IsCardinalAccessible κ where
  preservesColimitOfShape J _ hκ  := by
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    exact preservesColimitsOfShape_of_natIso e

end

section

variable (F : C ⥤ D)

/-- A functor is accessible relative to a universe `w` if
it is `κ`-accessible for some regular `κ : Cardinal.{w}`. -/
class IsAccessible  : Prop where
  exists_cardinal : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalAccessible F κ

lemma isAccessible_of_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessible F κ] : IsAccessible.{w} F where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

end

end Functor

section

variable (X : C) (Y : C) (e : X ≅ Y) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- An object `X` in a category is `κ`-presentable (for `κ` a regular cardinal)
when the functor `Hom(X, _)` preserves colimits indexed by
`κ`-filtered categories. -/
abbrev IsCardinalPresentable : Prop := (coyoneda.obj (op X)).IsCardinalAccessible κ

lemma preservesColimitsOfShape_of_isCardinalPresentable [IsCardinalPresentable X κ]
    (J : Type w) [SmallCategory.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible κ J

lemma preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
    [IsCardinalPresentable X κ]
    (J : Type u₃) [Category.{v₃} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ J

variable {κ} in
lemma isCardinalPresentable_of_le [IsCardinalPresentable X κ]
    {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    IsCardinalPresentable X κ' :=
  (coyoneda.obj (op X)).isCardinalAccessible_of_le h

include e in
variable {X Y} in
lemma isCardinalPresentable_of_iso [IsCardinalPresentable X κ] : IsCardinalPresentable Y κ :=
  Functor.isCardinalAccessible_of_iso (coyoneda.mapIso e.symm.op) κ

lemma isCardinalPresentable_of_equivalence
    {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] (e : C ≌ C') :
    IsCardinalPresentable (e.functor.obj X) κ := by
  refine ⟨fun J _ _ ↦ ⟨fun {Y} ↦ ?_⟩⟩
  have := preservesColimitsOfShape_of_isCardinalPresentable X κ J
  suffices PreservesColimit Y (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) from
    ⟨fun {c} hc ↦ ⟨isColimitOfReflects uliftFunctor.{v₁}
        (isColimitOfPreserves (coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁}) hc)⟩⟩
  have iso : coyoneda.obj (op (e.functor.obj X)) ⋙ uliftFunctor.{v₁} ≅
    e.inverse ⋙ coyoneda.obj (op X) ⋙ uliftFunctor.{v₃} :=
    NatIso.ofComponents (fun Z ↦
      (Equiv.ulift.trans ((e.toAdjunction.homEquiv X Z).trans Equiv.ulift.symm)).toIso) (by
        intro _ _ f
        ext ⟨g⟩
        apply Equiv.ulift.injective
        simp [Adjunction.homEquiv_unit])
  exact preservesColimit_of_natIso Y iso.symm

instance isCardinalPresentable_of_isEquivalence
    {C' : Type u₃} [Category.{v₃} C'] [IsCardinalPresentable X κ] (F : C ⥤ C')
    [F.IsEquivalence] :
    IsCardinalPresentable (F.obj X) κ :=
  isCardinalPresentable_of_equivalence X κ F.asEquivalence

@[simp]
lemma isCardinalPresentable_iff_of_isEquivalence
    {C' : Type u₃} [Category.{v₃} C'] (F : C ⥤ C')
    [F.IsEquivalence] :
    IsCardinalPresentable (F.obj X) κ ↔ IsCardinalPresentable X κ := by
  constructor
  · intro
    exact isCardinalPresentable_of_iso
      (show F.inv.obj (F.obj X) ≅ X from F.asEquivalence.unitIso.symm.app X : ) κ
  · intro
    infer_instance

lemma isCardinalPresentable_shrinkHoms_iff [LocallySmall.{w} C] :
    IsCardinalPresentable ((ShrinkHoms.functor.{w} C).obj X) κ ↔ IsCardinalPresentable X κ :=
  isCardinalPresentable_iff_of_isEquivalence X κ _

end

section

variable (X : C)

/-- An object of a category is presentable relative to a universe `w`
if it is `κ`-presentable for some regular `κ : Cardinal.{w}`. -/
abbrev IsPresentable (X : C) : Prop :=
  Functor.IsAccessible.{w} (coyoneda.obj (op X))

lemma isPresentable_of_isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] : IsPresentable.{w} X where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

end

section

variable (C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

class HasCardinalFilteredColimits : Prop where
  hasColimitsOfShape (J : Type w) [Category.{w} J] [IsCardinalFiltered J κ] :
    HasColimitsOfShape J C := by intros; infer_instance

attribute [instance] HasCardinalFilteredColimits.hasColimitsOfShape

instance [HasColimitsOfSize.{w, w} C] : HasCardinalFilteredColimits.{w} C κ where

end

end CategoryTheory
