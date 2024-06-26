/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Thin

#align_import category_theory.limits.shapes.wide_pullbacks from "leanprover-community/mathlib"@"f187f1074fa1857c94589cc653c786cadc4c35ff"

/-!
# Wide pullbacks

We define the category `WidePullbackShape`, (resp. `WidePushoutShape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wideCospan` (`wideSpan`) constructs a functor from this category, hitting
the given morphisms.

We use `WidePullbackShape` to define ordinary pullbacks (pushouts) by using `J := WalkingPair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `HasWidePullbacks` and `HasFiniteWidePullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/

universe w w' v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

variable (J : Type w)

/-- A wide pullback shape for any type `J` can be written simply as `Option J`. -/
def WidePullbackShape := Option J
#align category_theory.limits.wide_pullback_shape CategoryTheory.Limits.WidePullbackShape

-- Porting note: strangely this could be synthesized
instance : Inhabited (WidePullbackShape J) where
  default := none

/-- A wide pushout shape for any type `J` can be written simply as `Option J`. -/
def WidePushoutShape := Option J
#align category_theory.limits.wide_pushout_shape CategoryTheory.Limits.WidePushoutShape

instance : Inhabited (WidePushoutShape J) where
  default := none

namespace WidePullbackShape

variable {J}

/-- The type of arrows for the shape indexing a wide pullback. -/
inductive Hom : WidePullbackShape J → WidePullbackShape J → Type w
  | id : ∀ X, Hom X X
  | term : ∀ j : J, Hom (some j) none
  deriving DecidableEq
#align category_theory.limits.wide_pullback_shape.hom CategoryTheory.Limits.WidePullbackShape.Hom

-- This is relying on an automatically generated instance name, generated in a `deriving` handler.
-- See https://github.com/leanprover/lean4/issues/2343
attribute [nolint unusedArguments] instDecidableEqHom

instance struct : CategoryStruct (WidePullbackShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.term _
#align category_theory.limits.wide_pullback_shape.struct CategoryTheory.Limits.WidePullbackShape.struct

instance Hom.inhabited : Inhabited (Hom (none : WidePullbackShape J) none) :=
  ⟨Hom.id (none : WidePullbackShape J)⟩
#align category_theory.limits.wide_pullback_shape.hom.inhabited CategoryTheory.Limits.WidePullbackShape.Hom.inhabited

open Lean Elab Tactic
/- Pointing note: experimenting with manual scoping of aesop tactics. Attempted to define
aesop rule directing on `WidePushoutOut` and it didn't take for some reason -/
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
def evalCasesBash : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePullbackShape _,
      (_: WidePullbackShape _) ⟶ (_ : WidePullbackShape _) ))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash

instance subsingleton_hom : Quiver.IsThin (WidePullbackShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePullbackShape _, (_: WidePullbackShape _) ⟶ (_ : WidePullbackShape _)
  · rfl
  · rfl
  · rfl
#align category_theory.limits.wide_pullback_shape.subsingleton_hom CategoryTheory.Limits.WidePullbackShape.subsingleton_hom

instance category : SmallCategory (WidePullbackShape J) :=
  thin_category
#align category_theory.limits.wide_pullback_shape.category CategoryTheory.Limits.WidePullbackShape.category

@[simp]
theorem hom_id (X : WidePullbackShape J) : Hom.id X = 𝟙 X :=
  rfl
#align category_theory.limits.wide_pullback_shape.hom_id CategoryTheory.Limits.WidePullbackShape.hom_id

/- Porting note: we get a warning that we should change LHS to `sizeOf (𝟙 X)` but Lean cannot
find the category instance on `WidePullbackShape J` in that case. Once supplied in the proof,
the proposed proof of `simp [only WidePullbackShape.hom_id]` does not work -/
attribute [nolint simpNF] Hom.id.sizeOf_spec

variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[simps]
def wideCospan (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : WidePullbackShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    cases' f with _ j
    · apply 𝟙 _
    · exact arrows j
#align category_theory.limits.wide_pullback_shape.wide_cospan CategoryTheory.Limits.WidePullbackShape.wideCospan

/-- Every diagram is naturally isomorphic (actually, equal) to a `wideCospan` -/
def diagramIsoWideCospan (F : WidePullbackShape J ⥤ C) :
    F ≅ wideCospan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.term j) :=
  NatIso.ofComponents fun j => eqToIso <| by aesop_cat
#align category_theory.limits.wide_pullback_shape.diagram_iso_wide_cospan CategoryTheory.Limits.WidePullbackShape.diagramIsoWideCospan

/-- Construct a cone over a wide cospan. -/
@[simps]
def mkCone {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : ∀ j, X ⟶ F.obj (some j))
    (w : ∀ j, π j ≫ F.map (Hom.term j) = f) : Cone F :=
  { pt := X
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> dsimp <;> simp [w] } }
#align category_theory.limits.wide_pullback_shape.mk_cone CategoryTheory.Limits.WidePullbackShape.mkCone

/-- Wide pullback diagrams of equivalent index types are equivalent. -/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') :
    WidePullbackShape J ≌ WidePullbackShape J' where
  functor := wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso :=
    NatIso.ofComponents (fun j => by aesop_cat) fun f =>
      by simp only [eq_iff_true_of_subsingleton]
  counitIso :=
    NatIso.ofComponents (fun j => by aesop_cat)
      fun f => by simp only [eq_iff_true_of_subsingleton]
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

/-- The type of arrows for the shape indexing a wide pushout. -/
inductive Hom : WidePushoutShape J → WidePushoutShape J → Type w
  | id : ∀ X, Hom X X
  | init : ∀ j : J, Hom none (some j)
  deriving DecidableEq
#align category_theory.limits.wide_pushout_shape.hom CategoryTheory.Limits.WidePushoutShape.Hom

-- This is relying on an automatically generated instance name, generated in a `deriving` handler.
-- See https://github.com/leanprover/lean4/issues/2343
attribute [nolint unusedArguments] instDecidableEqHom

instance struct : CategoryStruct (WidePushoutShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.init _
#align category_theory.limits.wide_pushout_shape.struct CategoryTheory.Limits.WidePushoutShape.struct

instance Hom.inhabited : Inhabited (Hom (none : WidePushoutShape J) none) :=
  ⟨Hom.id (none : WidePushoutShape J)⟩
#align category_theory.limits.wide_pushout_shape.hom.inhabited CategoryTheory.Limits.WidePushoutShape.Hom.inhabited

open Lean Elab Tactic
-- Pointing note: experimenting with manual scoping of aesop tactics; only this worked
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
def evalCasesBash' : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePushoutShape _,
      (_: WidePushoutShape _) ⟶ (_ : WidePushoutShape _) ))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash'

instance subsingleton_hom : Quiver.IsThin (WidePushoutShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePushoutShape _, (_: WidePushoutShape _) ⟶ (_ : WidePushoutShape _)
  repeat rfl
#align category_theory.limits.wide_pushout_shape.subsingleton_hom CategoryTheory.Limits.WidePushoutShape.subsingleton_hom

instance category : SmallCategory (WidePushoutShape J) :=
  thin_category
#align category_theory.limits.wide_pushout_shape.category CategoryTheory.Limits.WidePushoutShape.category

@[simp]
theorem hom_id (X : WidePushoutShape J) : Hom.id X = 𝟙 X :=
  rfl
#align category_theory.limits.wide_pushout_shape.hom_id CategoryTheory.Limits.WidePushoutShape.hom_id

/- Porting note: we get a warning that we should change LHS to `sizeOf (𝟙 X)` but Lean cannot
find the category instance on `WidePushoutShape J` in that case. Once supplied in the proof,
the proposed proof of `simp [only WidePushoutShape.hom_id]` does not work -/
attribute [nolint simpNF] Hom.id.sizeOf_spec
variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/
@[simps]
def wideSpan (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : WidePushoutShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    cases' f with _ j
    · apply 𝟙 _
    · exact arrows j
  map_comp := fun f g => by
    cases f
    · simp only [Eq.ndrec, hom_id, eq_rec_constant, Category.id_comp]; congr
    · cases g
      simp only [Eq.ndrec, hom_id, eq_rec_constant, Category.comp_id]; congr
#align category_theory.limits.wide_pushout_shape.wide_span CategoryTheory.Limits.WidePushoutShape.wideSpan

/-- Every diagram is naturally isomorphic (actually, equal) to a `wideSpan` -/
def diagramIsoWideSpan (F : WidePushoutShape J ⥤ C) :
    F ≅ wideSpan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.init j) :=
  NatIso.ofComponents fun j => eqToIso <| by cases j; repeat rfl
#align category_theory.limits.wide_pushout_shape.diagram_iso_wide_span CategoryTheory.Limits.WidePushoutShape.diagramIsoWideSpan

/-- Construct a cocone over a wide span. -/
@[simps]
def mkCocone {F : WidePushoutShape J ⥤ C} {X : C} (f : F.obj none ⟶ X) (ι : ∀ j, F.obj (some j) ⟶ X)
    (w : ∀ j, F.map (Hom.init j) ≫ ι j = f) : Cocone F :=
  { pt := X
    ι :=
      { app := fun j =>
          match j with
          | none => f
          | some j => ι j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> dsimp <;> simp [w] } }
#align category_theory.limits.wide_pushout_shape.mk_cocone CategoryTheory.Limits.WidePushoutShape.mkCocone

/-- Wide pushout diagrams of equivalent index types are equivalent. -/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') : WidePushoutShape J ≌ WidePushoutShape J' where
  functor := wideSpan none (fun j => some (h j)) fun j => Hom.init (h j)
  inverse := wideSpan none (fun j => some (h.invFun j)) fun j => Hom.init (h.invFun j)
  unitIso :=
    NatIso.ofComponents (fun j => by aesop_cat) fun f => by
      simp only [eq_iff_true_of_subsingleton]
  counitIso :=
    NatIso.ofComponents (fun j => by aesop_cat) fun f => by
      simp only [eq_iff_true_of_subsingleton]

/-- Lifting universe and morphism levels preserves wide pushout diagrams. -/
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePushoutShape J)) ≌ WidePushoutShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePushoutShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

end WidePushoutShape

variable (C : Type u) [Category.{v} C]

/-- `HasWidePullbacks` represents a choice of wide pullback for every collection of morphisms -/
abbrev HasWidePullbacks : Prop :=
  ∀ J : Type w, HasLimitsOfShape (WidePullbackShape J) C
#align category_theory.limits.has_wide_pullbacks CategoryTheory.Limits.HasWidePullbacks

/-- `HasWidePushouts` represents a choice of wide pushout for every collection of morphisms -/
abbrev HasWidePushouts : Prop :=
  ∀ J : Type w, HasColimitsOfShape (WidePushoutShape J) C
#align category_theory.limits.has_wide_pushouts CategoryTheory.Limits.HasWidePushouts

variable {C J}

/-- `HasWidePullback B objs arrows` means that `wideCospan B objs arrows` has a limit. -/
abbrev HasWidePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : Prop :=
  HasLimit (WidePullbackShape.wideCospan B objs arrows)
#align category_theory.limits.has_wide_pullback CategoryTheory.Limits.HasWidePullback

/-- `HasWidePushout B objs arrows` means that `wideSpan B objs arrows` has a colimit. -/
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

namespace WidePullback

variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, objs j ⟶ B)
variable [HasWidePullback B objs arrows]

/-- The `j`-th projection from the pullback. -/
noncomputable abbrev π (j : J) : widePullback _ _ arrows ⟶ objs j :=
  limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)
#align category_theory.limits.wide_pullback.π CategoryTheory.Limits.WidePullback.π


/-- The unique map to the base from the pullback. -/
noncomputable abbrev base : widePullback _ _ arrows ⟶ B :=
  limit.π (WidePullbackShape.wideCospan _ _ _) Option.none
#align category_theory.limits.wide_pullback.base CategoryTheory.Limits.WidePullback.base

@[reassoc (attr := simp)]
theorem π_arrow (j : J) : π arrows j ≫ arrows _ = base arrows := by
  apply limit.w (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.Hom.term j)
#align category_theory.limits.wide_pullback.π_arrow CategoryTheory.Limits.WidePullback.π_arrow

variable {arrows}

/-- Lift a collection of morphisms to a morphism to the pullback. -/
noncomputable abbrev lift {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j)
    (w : ∀ j, fs j ≫ arrows j = f) : X ⟶ widePullback _ _ arrows :=
  limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)
#align category_theory.limits.wide_pullback.lift CategoryTheory.Limits.WidePullback.lift

variable (arrows)
variable {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j) (w : ∀ j, fs j ≫ arrows j = f)

-- Porting note (#10618): simp can prove this so removed simp attribute
@[reassoc]
theorem lift_π (j : J) : lift f fs w ≫ π arrows j = fs _ := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_pt, WidePullbackShape.mkCone_π_app]
#align category_theory.limits.wide_pullback.lift_π CategoryTheory.Limits.WidePullback.lift_π

-- Porting note (#10618): simp can prove this so removed simp attribute
@[reassoc]
theorem lift_base : lift f fs w ≫ base arrows = f := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_pt, WidePullbackShape.mkCone_π_app]
#align category_theory.limits.wide_pullback.lift_base CategoryTheory.Limits.WidePullback.lift_base

theorem eq_lift_of_comp_eq (g : X ⟶ widePullback _ _ arrows) :
    (∀ j : J, g ≫ π arrows j = fs j) → g ≫ base arrows = f → g = lift f fs w := by
  intro h1 h2
  apply
    (limit.isLimit (WidePullbackShape.wideCospan B objs arrows)).uniq
      (WidePullbackShape.mkCone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1
#align category_theory.limits.wide_pullback.eq_lift_of_comp_eq CategoryTheory.Limits.WidePullback.eq_lift_of_comp_eq

theorem hom_eq_lift (g : X ⟶ widePullback _ _ arrows) :
    g = lift (g ≫ base arrows) (fun j => g ≫ π arrows j) (by aesop_cat) := by
  apply eq_lift_of_comp_eq
  · aesop_cat
  · rfl  -- Porting note: quite a few missing refl's in aesop_cat now
#align category_theory.limits.wide_pullback.hom_eq_lift CategoryTheory.Limits.WidePullback.hom_eq_lift

@[ext 1100]
theorem hom_ext (g1 g2 : X ⟶ widePullback _ _ arrows) : (∀ j : J,
    g1 ≫ π arrows j = g2 ≫ π arrows j) → g1 ≫ base arrows = g2 ≫ base arrows → g1 = g2 := by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1
#align category_theory.limits.wide_pullback.hom_ext CategoryTheory.Limits.WidePullback.hom_ext

end WidePullback

namespace WidePushout

variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, B ⟶ objs j)
variable [HasWidePushout B objs arrows]

/-- The `j`-th inclusion to the pushout. -/
noncomputable abbrev ι (j : J) : objs j ⟶ widePushout _ _ arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) (Option.some j)
#align category_theory.limits.wide_pushout.ι CategoryTheory.Limits.WidePushout.ι

/-- The unique map from the head to the pushout. -/
noncomputable abbrev head : B ⟶ widePushout B objs arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) Option.none
#align category_theory.limits.wide_pushout.head CategoryTheory.Limits.WidePushout.head

@[reassoc (attr := simp)]
theorem arrow_ι (j : J) : arrows j ≫ ι arrows j = head arrows := by
  apply colimit.w (WidePushoutShape.wideSpan _ _ _) (WidePushoutShape.Hom.init j)
#align category_theory.limits.wide_pushout.arrow_ι CategoryTheory.Limits.WidePushout.arrow_ι

-- Porting note: this can simplify itself
attribute [nolint simpNF] WidePushout.arrow_ι WidePushout.arrow_ι_assoc

variable {arrows}

/-- Descend a collection of morphisms to a morphism from the pushout. -/
noncomputable abbrev desc {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X)
    (w : ∀ j, arrows j ≫ fs j = f) : widePushout _ _ arrows ⟶ X :=
  colimit.desc (WidePushoutShape.wideSpan B objs arrows) (WidePushoutShape.mkCocone f fs <| w)
#align category_theory.limits.wide_pushout.desc CategoryTheory.Limits.WidePushout.desc

variable (arrows)
variable {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X) (w : ∀ j, arrows j ≫ fs j = f)

-- Porting note (#10618): simp can prove this so removed simp attribute
@[reassoc]
theorem ι_desc (j : J) : ι arrows j ≫ desc f fs w = fs _ := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_pt, WidePushoutShape.mkCocone_ι_app]
#align category_theory.limits.wide_pushout.ι_desc CategoryTheory.Limits.WidePushout.ι_desc

-- Porting note (#10618): simp can prove this so removed simp attribute
@[reassoc]
theorem head_desc : head arrows ≫ desc f fs w = f := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_pt, WidePushoutShape.mkCocone_ι_app]
#align category_theory.limits.wide_pushout.head_desc CategoryTheory.Limits.WidePushout.head_desc

theorem eq_desc_of_comp_eq (g : widePushout _ _ arrows ⟶ X) :
    (∀ j : J, ι arrows j ≫ g = fs j) → head arrows ≫ g = f → g = desc f fs w := by
  intro h1 h2
  apply
    (colimit.isColimit (WidePushoutShape.wideSpan B objs arrows)).uniq
      (WidePushoutShape.mkCocone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1
#align category_theory.limits.wide_pushout.eq_desc_of_comp_eq CategoryTheory.Limits.WidePushout.eq_desc_of_comp_eq

theorem hom_eq_desc (g : widePushout _ _ arrows ⟶ X) :
    g =
      desc (head arrows ≫ g) (fun j => ι arrows j ≫ g) fun j => by
        rw [← Category.assoc]
        simp := by
  apply eq_desc_of_comp_eq
  · aesop_cat
  · rfl -- Porting note: another missing rfl
#align category_theory.limits.wide_pushout.hom_eq_desc CategoryTheory.Limits.WidePushout.hom_eq_desc

@[ext 1100]
theorem hom_ext (g1 g2 : widePushout _ _ arrows ⟶ X) : (∀ j : J,
    ι arrows j ≫ g1 = ι arrows j ≫ g2) → head arrows ≫ g1 = head arrows ≫ g2 → g1 = g2 := by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1
#align category_theory.limits.wide_pushout.hom_ext CategoryTheory.Limits.WidePushout.hom_ext

end WidePushout

variable (J)

/-- The action on morphisms of the obvious functor
  `WidePullbackShape_op : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ`-/
def widePullbackShapeOpMap :
    ∀ X Y : WidePullbackShape J,
      (X ⟶ Y) → ((op X : (WidePushoutShape J)ᵒᵖ) ⟶ (op Y : (WidePushoutShape J)ᵒᵖ))
  | _, _, WidePullbackShape.Hom.id X => Quiver.Hom.op (WidePushoutShape.Hom.id _)
  | _, _, WidePullbackShape.Hom.term _ => Quiver.Hom.op (WidePushoutShape.Hom.init _)
#align category_theory.limits.wide_pullback_shape_op_map CategoryTheory.Limits.widePullbackShapeOpMap

/-- The obvious functor `WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ` -/
@[simps]
def widePullbackShapeOp : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where
  obj X := op X
  map {X₁} {X₂} := widePullbackShapeOpMap J X₁ X₂
#align category_theory.limits.wide_pullback_shape_op CategoryTheory.Limits.widePullbackShapeOp

/-- The action on morphisms of the obvious functor
`widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/
def widePushoutShapeOpMap :
    ∀ X Y : WidePushoutShape J,
      (X ⟶ Y) → ((op X : (WidePullbackShape J)ᵒᵖ) ⟶ (op Y : (WidePullbackShape J)ᵒᵖ))
  | _, _, WidePushoutShape.Hom.id X => Quiver.Hom.op (WidePullbackShape.Hom.id _)
  | _, _, WidePushoutShape.Hom.init _ => Quiver.Hom.op (WidePullbackShape.Hom.term _)
#align category_theory.limits.wide_pushout_shape_op_map CategoryTheory.Limits.widePushoutShapeOpMap

/-- The obvious functor `WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/
@[simps]
def widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ where
  obj X := op X
  map := fun {X} {Y} => widePushoutShapeOpMap J X Y
#align category_theory.limits.wide_pushout_shape_op CategoryTheory.Limits.widePushoutShapeOp

/-- The obvious functor `(WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J`-/
@[simps!]
def widePullbackShapeUnop : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J :=
  (widePullbackShapeOp J).leftOp
#align category_theory.limits.wide_pullback_shape_unop CategoryTheory.Limits.widePullbackShapeUnop

/-- The obvious functor `(WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J` -/
@[simps!]
def widePushoutShapeUnop : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J :=
  (widePushoutShapeOp J).leftOp
#align category_theory.limits.wide_pushout_shape_unop CategoryTheory.Limits.widePushoutShapeUnop

/-- The inverse of the unit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
def widePushoutShapeOpUnop : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.limits.wide_pushout_shape_op_unop CategoryTheory.Limits.widePushoutShapeOpUnop

/-- The counit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
def widePushoutShapeUnopOp : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.limits.wide_pushout_shape_unop_op CategoryTheory.Limits.widePushoutShapeUnopOp

/-- The inverse of the unit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
def widePullbackShapeOpUnop : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.limits.wide_pullback_shape_op_unop CategoryTheory.Limits.widePullbackShapeOpUnop

/-- The counit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
def widePullbackShapeUnopOp : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => Iso.refl _
#align category_theory.limits.wide_pullback_shape_unop_op CategoryTheory.Limits.widePullbackShapeUnopOp

/-- The duality equivalence `(WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
@[simps]
def widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J where
  functor := widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J
#align category_theory.limits.wide_pushout_shape_op_equiv CategoryTheory.Limits.widePushoutShapeOpEquiv

/-- The duality equivalence `(WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
@[simps]
def widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J where
  functor := widePullbackShapeUnop J
  inverse := widePushoutShapeOp J
  unitIso := (widePullbackShapeOpUnop J).symm
  counitIso := widePushoutShapeUnopOp J
#align category_theory.limits.wide_pullback_shape_op_equiv CategoryTheory.Limits.widePullbackShapeOpEquiv

/-- If a category has wide pushouts on a higher universe level it also has wide pushouts
on a lower universe level. -/
theorem hasWidePushouts_shrink [HasWidePushouts.{max w w'} C] : HasWidePushouts.{w} C := fun _ =>
  hasColimitsOfShape_of_equivalence (WidePushoutShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

/-- If a category has wide pullbacks on a higher universe level it also has wide pullbacks
on a lower universe level. -/
theorem hasWidePullbacks_shrink [HasWidePullbacks.{max w w'} C] : HasWidePullbacks.{w} C := fun _ =>
  hasLimitsOfShape_of_equivalence (WidePullbackShape.equivalenceOfEquiv _ Equiv.ulift.{w'})
#align category_theory.limits.has_wide_pullbacks_shrink CategoryTheory.Limits.hasWidePullbacks_shrink

end CategoryTheory.Limits
