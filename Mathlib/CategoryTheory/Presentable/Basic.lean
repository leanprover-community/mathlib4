/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

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

@[expose] public section

universe t w w' v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Functor

section

variable (F G : C ⥤ D) (e : F ≅ G) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A functor `F : C ⥤ D` is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-filtered category.
In the mathematical literature, some assumptions are often made on the
categories `C` or `D` (e.g. the existence of `κ`-filtered colimits,
see `HasCardinalFilteredColimits` below), but here we do not
make such assumptions. -/
class IsCardinalAccessible : Prop where
  preservesColimitOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    PreservesColimitsOfShape J F := by intros; infer_instance

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
lemma isCardinalAccessible_of_natIso [F.IsCardinalAccessible κ] : G.IsCardinalAccessible κ where
  preservesColimitOfShape J _ hκ := by
    have := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    exact preservesColimitsOfShape_of_natIso e

instance : IsCardinalAccessible (𝟭 C) κ where

instance {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] :
    (F ⋙ G).IsCardinalAccessible κ := by
  have := F.preservesColimitsOfShape_of_isCardinalAccessible κ
  have := G.preservesColimitsOfShape_of_isCardinalAccessible κ
  exact { }

instance [PreservesColimitsOfSize.{w, w} F] : F.IsCardinalAccessible κ where

end

section

variable (F : C ⥤ D)

/-- A functor is accessible relative to a universe `w` if
it is `κ`-accessible for some regular `κ : Cardinal.{w}`. -/
@[pp_with_univ]
class IsAccessible : Prop where
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

variable (C) in
/-- The property of objects that are `κ`-presentable. -/
def isCardinalPresentable : ObjectProperty C := fun X ↦ IsCardinalPresentable X κ

instance (X : (isCardinalPresentable C κ).FullSubcategory) :
    IsCardinalPresentable X.obj κ :=
  X.property

instance (X : (isCardinalPresentable C κ).FullSubcategory) :
    IsCardinalPresentable ((isCardinalPresentable C κ).ι.obj X) κ := by
  dsimp
  infer_instance

lemma isCardinalPresentable_iff_isCardinalAccessible_coyoneda_obj :
    IsCardinalPresentable X κ ↔ (coyoneda.obj (op X)).IsCardinalAccessible κ := Iff.rfl

lemma isCardinalPresentable_iff (X : C) :
    isCardinalPresentable C κ X ↔ IsCardinalPresentable X κ := Iff.rfl

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

variable (C) {κ} in
lemma isCardinalPresentable_monotone {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ ≤ κ') :
    isCardinalPresentable C κ ≤ isCardinalPresentable C κ' := by
  intro X hX
  rw [isCardinalPresentable_iff] at hX ⊢
  exact isCardinalPresentable_of_le _ h

include e in
variable {X Y} in
lemma isCardinalPresentable_of_iso [IsCardinalPresentable X κ] : IsCardinalPresentable Y κ :=
  Functor.isCardinalAccessible_of_natIso (coyoneda.mapIso e.symm.op) κ

instance : (isCardinalPresentable C κ).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    rw [isCardinalPresentable_iff] at hX ⊢
    exact isCardinalPresentable_of_iso e _

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
      (show F.inv.obj (F.obj X) ≅ X from F.asEquivalence.unitIso.symm.app X :) κ
  · intro
    infer_instance

variable {X} in
lemma IsCardinalPresentable.exists_hom_of_isColimit [IsCardinalPresentable X κ]
    {J : Type u₂} [Category.{v₂} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) (f : X ⟶ c.pt) :
    ∃ (j : J) (f' : X ⟶ F.obj j), f' ≫ c.ι.app j = f := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  exact Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (op X)) hc) f

variable {X} in
lemma IsCardinalPresentable.exists_eq_of_isColimit [IsCardinalPresentable X κ]
    {J : Type u₂} [Category.{v₂} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {i₁ i₂ : J} (f₁ : X ⟶ F.obj i₁)
    (f₂ : X ⟶ F.obj i₂) (hf : f₁ ≫ c.ι.app i₁ = f₂ ≫ c.ι.app i₂) :
    ∃ (j : J) (u : i₁ ⟶ j) (v : i₂ ⟶ j), f₁ ≫ F.map u = f₂ ≫ F.map v := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact (Types.FilteredColimit.isColimit_eq_iff _
    (isColimitOfPreserves (coyoneda.obj (op X)) hc)).1 hf

variable {X} in
lemma IsCardinalPresentable.exists_eq_of_isColimit' [IsCardinalPresentable X κ]
    {J : Type u₂} [Category.{v₂} J] [EssentiallySmall.{w} J] [IsCardinalFiltered J κ]
    {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) {i : J} (f₁ f₂ : X ⟶ F.obj i)
    (hf : f₁ ≫ c.ι.app i = f₂ ≫ c.ι.app i) :
    ∃ (j : J) (u : i ⟶ j), f₁ ≫ F.map u = f₂ ≫ F.map u := by
  have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
  have := isFiltered_of_isCardinalFiltered J κ
  exact (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (coyoneda.obj (op X)) hc) f₁ f₂).1 hf

lemma isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj :
    IsCardinalPresentable X κ ↔ (uliftCoyoneda.{t}.obj (op X)).IsCardinalAccessible κ := by
  change _ ↔ (coyoneda.obj (op X) ⋙ uliftFunctor.{t}).IsCardinalAccessible κ
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨fun J _ _ ↦ ?_⟩⟩
  have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
    (coyoneda.obj (op X) ⋙ uliftFunctor.{t}) κ J
  exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{t, v₁}

instance [IsCardinalPresentable X κ] :
    (uliftCoyoneda.{t}.obj (op X)).IsCardinalAccessible κ :=
  (isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{t} X κ).1 inferInstance

end

section

variable (X : C)

/-- An object of a category is presentable relative to a universe `w`
if it is `κ`-presentable for some regular `κ : Cardinal.{w}`. -/
@[pp_with_univ]
abbrev IsPresentable (X : C) : Prop :=
  Functor.IsAccessible.{w} (coyoneda.obj (op X))

lemma isPresentable_of_isCardinalPresentable (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalPresentable X κ] : IsPresentable.{w} X where
  exists_cardinal := ⟨κ, inferInstance, inferInstance⟩

end

section

variable (C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A category has `κ`-filtered colimits if it has colimits of shape `J`
for any `κ`-filtered category `J`. -/
class HasCardinalFilteredColimits : Prop where
  hasColimitsOfShape (J : Type w) [SmallCategory J] [IsCardinalFiltered J κ] :
    HasColimitsOfShape J C := by intros; infer_instance

attribute [instance] HasCardinalFilteredColimits.hasColimitsOfShape

instance [HasColimitsOfSize.{w, w} C] : HasCardinalFilteredColimits.{w} C κ where

end

end CategoryTheory
