/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.limits.shapes.wide_pullbacks
! leanprover-community/mathlib commit f187f1074fa1857c94589cc653c786cadc4c35ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Thin

/-!
# Wide pullbacks

We define the category `wide_pullback_shape`, (resp. `wide_pushout_shape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wide_cospan` (`wide_span`) constructs a functor from this category, hitting
the given morphisms.

We use `wide_pullback_shape` to define ordinary pullbacks (pushouts) by using `J := walking_pair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `has_wide_pullbacks` and `has_finite_wide_pullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/


universe w w' v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

variable (J : Type w)

/-- A wide pullback shape for any type `J` can be written simply as `option J`. -/
def WidePullbackShape :=
  Option J deriving Inhabited
#align category_theory.limits.wide_pullback_shape CategoryTheory.Limits.WidePullbackShape

/-- A wide pushout shape for any type `J` can be written simply as `option J`. -/
def WidePushoutShape :=
  Option J deriving Inhabited
#align category_theory.limits.wide_pushout_shape CategoryTheory.Limits.WidePushoutShape

namespace WidePullbackShape

variable {J}

/-- The type of arrows for the shape indexing a wide pullback. -/
inductive Hom : WidePullbackShape J → WidePullbackShape J → Type w
  | id : ∀ X, hom X X
  | term : ∀ j : J, hom (some j) none
  deriving DecidableEq
#align category_theory.limits.wide_pullback_shape.hom CategoryTheory.Limits.WidePullbackShape.Hom

attribute [nolint unused_arguments] hom.decidable_eq

instance struct : CategoryStruct (WidePullbackShape J)
    where
  Hom := Hom
  id j := Hom.id j
  comp j₁ j₂ j₃ f g := by
    cases f
    exact g
    cases g
    apply hom.term _
#align category_theory.limits.wide_pullback_shape.struct CategoryTheory.Limits.WidePullbackShape.struct

instance Hom.inhabited : Inhabited (Hom none none) :=
  ⟨Hom.id (none : WidePullbackShape J)⟩
#align category_theory.limits.wide_pullback_shape.hom.inhabited CategoryTheory.Limits.WidePullbackShape.Hom.inhabited

attribute [local tidy] tactic.case_bash

instance subsingleton_hom : Quiver.IsThin (WidePullbackShape J) := fun _ _ => ⟨by tidy⟩
#align category_theory.limits.wide_pullback_shape.subsingleton_hom CategoryTheory.Limits.WidePullbackShape.subsingleton_hom

instance category : SmallCategory (WidePullbackShape J) :=
  thin_category
#align category_theory.limits.wide_pullback_shape.category CategoryTheory.Limits.WidePullbackShape.category

@[simp]
theorem hom_id (X : WidePullbackShape J) : Hom.id X = 𝟙 X :=
  rfl
#align category_theory.limits.wide_pullback_shape.hom_id CategoryTheory.Limits.WidePullbackShape.hom_id

variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[simps]
def wideCospan (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : WidePullbackShape J ⥤ C
    where
  obj j := Option.casesOn j B objs
  map X Y f := by
    cases' f with _ j
    · apply 𝟙 _
    · exact arrows j
  map_comp' _ _ _ f g := by
    cases f
    · simpa
    cases g
    simp
#align category_theory.limits.wide_pullback_shape.wide_cospan CategoryTheory.Limits.WidePullbackShape.wideCospan

/-- Every diagram is naturally isomorphic (actually, equal) to a `wide_cospan` -/
def diagramIsoWideCospan (F : WidePullbackShape J ⥤ C) :
    F ≅ wideCospan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.term j) :=
  (NatIso.ofComponents fun j => eqToIso <| by tidy) <| by tidy
#align category_theory.limits.wide_pullback_shape.diagram_iso_wide_cospan CategoryTheory.Limits.WidePullbackShape.diagramIsoWideCospan

/-- Construct a cone over a wide cospan. -/
@[simps]
def mkCone {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : ∀ j, X ⟶ F.obj (some j))
    (w : ∀ j, π j ≫ F.map (Hom.term j) = f) : Cone F :=
  { x
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j
        naturality' := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> unfold_aux <;> dsimp <;> simp [w] } }
#align category_theory.limits.wide_pullback_shape.mk_cone CategoryTheory.Limits.WidePullbackShape.mkCone

/-- Wide pullback diagrams of equivalent index types are equivlent. -/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') : WidePullbackShape J ≌ WidePullbackShape J'
    where
  Functor := wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso :=
    NatIso.ofComponents (fun j => by cases j <;> simp) fun j k f => by
      simp only [eq_iff_true_of_subsingleton]
  counitIso :=
    NatIso.ofComponents (fun j => by cases j <;> simp) fun j k f => by
      simp only [eq_iff_true_of_subsingleton]
#align category_theory.limits.wide_pullback_shape.equivalence_of_equiv CategoryTheory.Limits.WidePullbackShape.equivalenceOfEquiv

/-- Lifting universe and morphism levels preserves wide pullback diagrams. -/
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePullbackShape J)) ≌ WidePullbackShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePullbackShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))
#align category_theory.limits.wide_pullback_shape.ulift_equivalence CategoryTheory.Limits.WidePullbackShape.uliftEquivalence

end WidePullbackShape

namespace WidePushoutShape

variable {J}

/-- The type of arrows for the shape indexing a wide psuhout. -/
inductive Hom : WidePushoutShape J → WidePushoutShape J → Type w
  | id : ∀ X, hom X X
  | init : ∀ j : J, hom none (some j)
  deriving DecidableEq
#align category_theory.limits.wide_pushout_shape.hom CategoryTheory.Limits.WidePushoutShape.Hom

attribute [nolint unused_arguments] hom.decidable_eq

instance struct : CategoryStruct (WidePushoutShape J)
    where
  Hom := Hom
  id j := Hom.id j
  comp j₁ j₂ j₃ f g := by
    cases f
    exact g
    cases g
    apply hom.init _
#align category_theory.limits.wide_pushout_shape.struct CategoryTheory.Limits.WidePushoutShape.struct

instance Hom.inhabited : Inhabited (Hom none none) :=
  ⟨Hom.id (none : WidePushoutShape J)⟩
#align category_theory.limits.wide_pushout_shape.hom.inhabited CategoryTheory.Limits.WidePushoutShape.Hom.inhabited

attribute [local tidy] tactic.case_bash

instance subsingleton_hom : Quiver.IsThin (WidePushoutShape J) := fun _ _ => ⟨by tidy⟩
#align category_theory.limits.wide_pushout_shape.subsingleton_hom CategoryTheory.Limits.WidePushoutShape.subsingleton_hom

instance category : SmallCategory (WidePushoutShape J) :=
  thin_category
#align category_theory.limits.wide_pushout_shape.category CategoryTheory.Limits.WidePushoutShape.category

@[simp]
theorem hom_id (X : WidePushoutShape J) : Hom.id X = 𝟙 X :=
  rfl
#align category_theory.limits.wide_pushout_shape.hom_id CategoryTheory.Limits.WidePushoutShape.hom_id

variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/
@[simps]
def wideSpan (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : WidePushoutShape J ⥤ C
    where
  obj j := Option.casesOn j B objs
  map X Y f := by
    cases' f with _ j
    · apply 𝟙 _
    · exact arrows j
  map_comp' := by rintro (_ | _) (_ | _) (_ | _) (_ | _) (_ | _) <;> first |simpa|simp
#align category_theory.limits.wide_pushout_shape.wide_span CategoryTheory.Limits.WidePushoutShape.wideSpan

/-- Every diagram is naturally isomorphic (actually, equal) to a `wide_span` -/
def diagramIsoWideSpan (F : WidePushoutShape J ⥤ C) :
    F ≅ wideSpan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.init j) :=
  (NatIso.ofComponents fun j => eqToIso <| by tidy) <| by tidy
#align category_theory.limits.wide_pushout_shape.diagram_iso_wide_span CategoryTheory.Limits.WidePushoutShape.diagramIsoWideSpan

/-- Construct a cocone over a wide span. -/
@[simps]
def mkCocone {F : WidePushoutShape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : ∀ j, F.obj (some j) ⟶ X)
    (w : ∀ j, F.map (Hom.init j) ≫ ι j = f) : Cocone F :=
  { x
    ι :=
      { app := fun j =>
          match j with
          | none => f
          | some j => ι j
        naturality' := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> unfold_aux <;> dsimp <;> simp [w] } }
#align category_theory.limits.wide_pushout_shape.mk_cocone CategoryTheory.Limits.WidePushoutShape.mkCocone

end WidePushoutShape

variable (C : Type u) [Category.{v} C]

/-- `has_wide_pullbacks` represents a choice of wide pullback for every collection of morphisms -/
abbrev HasWidePullbacks : Prop :=
  ∀ J : Type w, HasLimitsOfShape (WidePullbackShape J) C
#align category_theory.limits.has_wide_pullbacks CategoryTheory.Limits.HasWidePullbacks

/-- `has_wide_pushouts` represents a choice of wide pushout for every collection of morphisms -/
abbrev HasWidePushouts : Prop :=
  ∀ J : Type w, HasColimitsOfShape (WidePushoutShape J) C
#align category_theory.limits.has_wide_pushouts CategoryTheory.Limits.HasWidePushouts

variable {C J}

/-- `has_wide_pullback B objs arrows` means that `wide_cospan B objs arrows` has a limit. -/
abbrev HasWidePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : Prop :=
  HasLimit (WidePullbackShape.wideCospan B objs arrows)
#align category_theory.limits.has_wide_pullback CategoryTheory.Limits.HasWidePullback

/-- `has_wide_pushout B objs arrows` means that `wide_span B objs arrows` has a colimit. -/
abbrev HasWidePushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : Prop :=
  HasColimit (WidePushoutShape.wideSpan B objs arrows)
#align category_theory.limits.has_wide_pushout CategoryTheory.Limits.HasWidePushout

/-- A choice of wide pullback. -/
noncomputable abbrev widePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    [HasWidePullback B objs arrows] : C :=
  limit (WidePullbackShape.wideCospan B objs arrows)
#align category_theory.limits.wide_pullback CategoryTheory.Limits.widePullback

/-- A choice of wide pushout. -/
noncomputable abbrev widePushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j)
    [HasWidePushout B objs arrows] : C :=
  colimit (WidePushoutShape.wideSpan B objs arrows)
#align category_theory.limits.wide_pushout CategoryTheory.Limits.widePushout

variable (C)

namespace WidePullback

variable {C} {B : C} {objs : J → C} (arrows : ∀ j : J, objs j ⟶ B)

variable [HasWidePullback B objs arrows]

/-- The `j`-th projection from the pullback. -/
noncomputable abbrev π (j : J) : widePullback _ _ arrows ⟶ objs j :=
  limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)
#align category_theory.limits.wide_pullback.π CategoryTheory.Limits.widePullback.π

/-- The unique map to the base from the pullback. -/
noncomputable abbrev base : widePullback _ _ arrows ⟶ B :=
  limit.π (WidePullbackShape.wideCospan _ _ _) Option.none
#align category_theory.limits.wide_pullback.base CategoryTheory.Limits.widePullback.base

@[simp, reassoc.1]
theorem π_arrow (j : J) : π arrows j ≫ arrows _ = base arrows := by
  apply limit.w (wide_pullback_shape.wide_cospan _ _ _) (wide_pullback_shape.hom.term j)
#align category_theory.limits.wide_pullback.π_arrow CategoryTheory.Limits.widePullback.π_arrow

variable {arrows}

/-- Lift a collection of morphisms to a morphism to the pullback. -/
noncomputable abbrev lift {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j)
    (w : ∀ j, fs j ≫ arrows j = f) : X ⟶ widePullback _ _ arrows :=
  limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)
#align category_theory.limits.wide_pullback.lift CategoryTheory.Limits.widePullback.lift

variable (arrows)

variable {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j) (w : ∀ j, fs j ≫ arrows j = f)

@[simp, reassoc.1]
theorem lift_π (j : J) : lift f fs w ≫ π arrows j = fs _ :=
  by
  simp
  rfl
#align category_theory.limits.wide_pullback.lift_π CategoryTheory.Limits.widePullback.lift_π

@[simp, reassoc.1]
theorem lift_base : lift f fs w ≫ base arrows = f :=
  by
  simp
  rfl
#align category_theory.limits.wide_pullback.lift_base CategoryTheory.Limits.widePullback.lift_base

theorem eq_lift_of_comp_eq (g : X ⟶ widePullback _ _ arrows) :
    (∀ j : J, g ≫ π arrows j = fs j) → g ≫ base arrows = f → g = lift f fs w :=
  by
  intro h1 h2
  apply
    (limit.is_limit (wide_pullback_shape.wide_cospan B objs arrows)).uniq
      (wide_pullback_shape.mk_cone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1
#align category_theory.limits.wide_pullback.eq_lift_of_comp_eq CategoryTheory.Limits.widePullback.eq_lift_of_comp_eq

theorem hom_eq_lift (g : X ⟶ widePullback _ _ arrows) :
    g = lift (g ≫ base arrows) (fun j => g ≫ π arrows j) (by tidy) :=
  by
  apply eq_lift_of_comp_eq
  tidy
#align category_theory.limits.wide_pullback.hom_eq_lift CategoryTheory.Limits.widePullback.hom_eq_lift

@[ext]
theorem hom_ext (g1 g2 : X ⟶ widePullback _ _ arrows) :
    (∀ j : J, g1 ≫ π arrows j = g2 ≫ π arrows j) → g1 ≫ base arrows = g2 ≫ base arrows → g1 = g2 :=
  by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1
#align category_theory.limits.wide_pullback.hom_ext CategoryTheory.Limits.widePullback.hom_ext

end WidePullback

namespace WidePushout

variable {C} {B : C} {objs : J → C} (arrows : ∀ j : J, B ⟶ objs j)

variable [HasWidePushout B objs arrows]

/-- The `j`-th inclusion to the pushout. -/
noncomputable abbrev ι (j : J) : objs j ⟶ widePushout _ _ arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) (Option.some j)
#align category_theory.limits.wide_pushout.ι CategoryTheory.Limits.widePushout.ι

/-- The unique map from the head to the pushout. -/
noncomputable abbrev head : B ⟶ widePushout B objs arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) Option.none
#align category_theory.limits.wide_pushout.head CategoryTheory.Limits.widePushout.head

@[simp, reassoc.1]
theorem arrow_ι (j : J) : arrows j ≫ ι arrows j = head arrows := by
  apply colimit.w (wide_pushout_shape.wide_span _ _ _) (wide_pushout_shape.hom.init j)
#align category_theory.limits.wide_pushout.arrow_ι CategoryTheory.Limits.widePushout.arrow_ι

variable {arrows}

/-- Descend a collection of morphisms to a morphism from the pushout. -/
noncomputable abbrev desc {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X)
    (w : ∀ j, arrows j ≫ fs j = f) : widePushout _ _ arrows ⟶ X :=
  colimit.desc (WidePushoutShape.wideSpan B objs arrows) (WidePushoutShape.mkCocone f fs <| w)
#align category_theory.limits.wide_pushout.desc CategoryTheory.Limits.widePushout.desc

variable (arrows)

variable {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X) (w : ∀ j, arrows j ≫ fs j = f)

@[simp, reassoc.1]
theorem ι_desc (j : J) : ι arrows j ≫ desc f fs w = fs _ :=
  by
  simp
  rfl
#align category_theory.limits.wide_pushout.ι_desc CategoryTheory.Limits.widePushout.ι_desc

@[simp, reassoc.1]
theorem head_desc : head arrows ≫ desc f fs w = f :=
  by
  simp
  rfl
#align category_theory.limits.wide_pushout.head_desc CategoryTheory.Limits.widePushout.head_desc

theorem eq_desc_of_comp_eq (g : widePushout _ _ arrows ⟶ X) :
    (∀ j : J, ι arrows j ≫ g = fs j) → head arrows ≫ g = f → g = desc f fs w :=
  by
  intro h1 h2
  apply
    (colimit.is_colimit (wide_pushout_shape.wide_span B objs arrows)).uniq
      (wide_pushout_shape.mk_cocone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1
#align category_theory.limits.wide_pushout.eq_desc_of_comp_eq CategoryTheory.Limits.widePushout.eq_desc_of_comp_eq

theorem hom_eq_desc (g : widePushout _ _ arrows ⟶ X) :
    g =
      desc (head arrows ≫ g) (fun j => ι arrows j ≫ g) fun j =>
        by
        rw [← category.assoc]
        simp :=
  by
  apply eq_desc_of_comp_eq
  tidy
#align category_theory.limits.wide_pushout.hom_eq_desc CategoryTheory.Limits.widePushout.hom_eq_desc

@[ext]
theorem hom_ext (g1 g2 : widePushout _ _ arrows ⟶ X) :
    (∀ j : J, ι arrows j ≫ g1 = ι arrows j ≫ g2) → head arrows ≫ g1 = head arrows ≫ g2 → g1 = g2 :=
  by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1
#align category_theory.limits.wide_pushout.hom_ext CategoryTheory.Limits.widePushout.hom_ext

end WidePushout

variable (J)

/-- The action on morphisms of the obvious functor
  `wide_pullback_shape_op : wide_pullback_shape J ⥤ (wide_pushout_shape J)ᵒᵖ`-/
def widePullbackShapeOpMap :
    ∀ X Y : WidePullbackShape J,
      (X ⟶ Y) → ((op X : (WidePushoutShape J)ᵒᵖ) ⟶ (op Y : (WidePushoutShape J)ᵒᵖ))
  | _, _, wide_pullback_shape.hom.id X => Quiver.Hom.op (WidePushoutShape.Hom.id _)
  | _, _, wide_pullback_shape.hom.term j => Quiver.Hom.op (WidePushoutShape.Hom.init _)
#align category_theory.limits.wide_pullback_shape_op_map CategoryTheory.Limits.widePullbackShapeOpMap

/-- The obvious functor `wide_pullback_shape J ⥤ (wide_pushout_shape J)ᵒᵖ` -/
@[simps]
def widePullbackShapeOp : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ
    where
  obj X := op X
  map := widePullbackShapeOpMap J
#align category_theory.limits.wide_pullback_shape_op CategoryTheory.Limits.widePullbackShapeOp

/-- The action on morphisms of the obvious functor
`wide_pushout_shape_op : `wide_pushout_shape J ⥤ (wide_pullback_shape J)ᵒᵖ` -/
def widePushoutShapeOpMap :
    ∀ X Y : WidePushoutShape J,
      (X ⟶ Y) → ((op X : (WidePullbackShape J)ᵒᵖ) ⟶ (op Y : (WidePullbackShape J)ᵒᵖ))
  | _, _, wide_pushout_shape.hom.id X => Quiver.Hom.op (WidePullbackShape.Hom.id _)
  | _, _, wide_pushout_shape.hom.init j => Quiver.Hom.op (WidePullbackShape.Hom.term _)
#align category_theory.limits.wide_pushout_shape_op_map CategoryTheory.Limits.widePushoutShapeOpMap

/-- The obvious functor `wide_pushout_shape J ⥤ (wide_pullback_shape J)ᵒᵖ` -/
@[simps]
def widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ
    where
  obj X := op X
  map := widePushoutShapeOpMap J
#align category_theory.limits.wide_pushout_shape_op CategoryTheory.Limits.widePushoutShapeOp

/-- The obvious functor `(wide_pullback_shape J)ᵒᵖ ⥤ wide_pushout_shape J`-/
@[simps]
def widePullbackShapeUnop : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J :=
  (widePullbackShapeOp J).leftOp
#align category_theory.limits.wide_pullback_shape_unop CategoryTheory.Limits.widePullbackShapeUnop

/-- The obvious functor `(wide_pushout_shape J)ᵒᵖ ⥤ wide_pullback_shape J` -/
@[simps]
def widePushoutShapeUnop : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J :=
  (widePushoutShapeOp J).leftOp
#align category_theory.limits.wide_pushout_shape_unop CategoryTheory.Limits.widePushoutShapeUnop

/-- The inverse of the unit isomorphism of the equivalence
`wide_pushout_shape_op_equiv : (wide_pushout_shape J)ᵒᵖ ≌ wide_pullback_shape J` -/
def widePushoutShapeOpUnop : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => Iso.refl _) fun X Y f => by decide
#align category_theory.limits.wide_pushout_shape_op_unop CategoryTheory.Limits.widePushoutShapeOpUnop

/-- The counit isomorphism of the equivalence
`wide_pullback_shape_op_equiv : (wide_pullback_shape J)ᵒᵖ ≌ wide_pushout_shape J` -/
def widePushoutShapeUnopOp : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => Iso.refl _) fun X Y f => by decide
#align category_theory.limits.wide_pushout_shape_unop_op CategoryTheory.Limits.widePushoutShapeUnopOp

/-- The inverse of the unit isomorphism of the equivalence
`wide_pullback_shape_op_equiv : (wide_pullback_shape J)ᵒᵖ ≌ wide_pushout_shape J` -/
def widePullbackShapeOpUnop : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => Iso.refl _) fun X Y f => by decide
#align category_theory.limits.wide_pullback_shape_op_unop CategoryTheory.Limits.widePullbackShapeOpUnop

/-- The counit isomorphism of the equivalence
`wide_pushout_shape_op_equiv : (wide_pushout_shape J)ᵒᵖ ≌ wide_pullback_shape J` -/
def widePullbackShapeUnopOp : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => Iso.refl _) fun X Y f => by decide
#align category_theory.limits.wide_pullback_shape_unop_op CategoryTheory.Limits.widePullbackShapeUnopOp

/-- The duality equivalence `(wide_pushout_shape J)ᵒᵖ ≌ wide_pullback_shape J` -/
@[simps]
def widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J
    where
  Functor := widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J
#align category_theory.limits.wide_pushout_shape_op_equiv CategoryTheory.Limits.widePushoutShapeOpEquiv

/-- The duality equivalence `(wide_pullback_shape J)ᵒᵖ ≌ wide_pushout_shape J` -/
@[simps]
def widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J
    where
  Functor := widePullbackShapeUnop J
  inverse := widePushoutShapeOp J
  unitIso := (widePullbackShapeOpUnop J).symm
  counitIso := widePushoutShapeUnopOp J
#align category_theory.limits.wide_pullback_shape_op_equiv CategoryTheory.Limits.widePullbackShapeOpEquiv

/-- If a category has wide pullbacks on a higher universe level it also has wide pullbacks
on a lower universe level. -/
theorem hasWidePullbacks_shrink [HasWidePullbacks.{max w w'} C] : HasWidePullbacks.{w} C := fun J =>
  hasLimitsOfShapeOfEquivalence (WidePullbackShape.equivalenceOfEquiv _ Equiv.ulift.{w'})
#align category_theory.limits.has_wide_pullbacks_shrink CategoryTheory.Limits.hasWidePullbacks_shrink

end CategoryTheory.Limits

