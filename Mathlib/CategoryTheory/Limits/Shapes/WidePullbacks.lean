/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jakob von Raumer
-/
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Thin

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

instance : Inhabited (WidePullbackShape J) where
  default := none

/-- A wide pushout shape for any type `J` can be written simply as `Option J`. -/
def WidePushoutShape := Option J

instance : Inhabited (WidePushoutShape J) where
  default := none

namespace WidePullbackShape

variable {J}

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of arrows for the shape indexing a wide pullback. -/
inductive Hom : WidePullbackShape J → WidePullbackShape J → Type w
  | id : ∀ X, Hom X X
  | term : ∀ j : J, Hom (some j) none
  deriving DecidableEq

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

instance Hom.inhabited : Inhabited (Hom (none : WidePullbackShape J) none) :=
  ⟨Hom.id (none : WidePullbackShape J)⟩

open Lean Elab Tactic
/- Pointing note: experimenting with manual scoping of aesop tactics. Attempted to define
aesop rule directing on `WidePushoutOut` and it didn't take for some reason -/
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
def evalCasesBash : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePullbackShape _,
      (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _) ))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash

instance subsingleton_hom : Quiver.IsThin (WidePullbackShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePullbackShape _, (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)
  · rfl
  · rfl
  · rfl

instance category : SmallCategory (WidePullbackShape J) :=
  thin_category

@[simp]
theorem hom_id (X : WidePullbackShape J) : Hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[simps]
def wideCospan (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : WidePullbackShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j

/-- Every diagram is naturally isomorphic (actually, equal) to a `wideCospan` -/
def diagramIsoWideCospan (F : WidePullbackShape J ⥤ C) :
    F ≅ wideCospan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.term j) :=
  NatIso.ofComponents fun j => eqToIso <| by cat_disch

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
          cases j <;> cases j' <;> cases f <;> simp [w] } }

/-- Wide pullback diagrams of equivalent index types are equivalent. -/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') :
    WidePullbackShape J ≌ WidePullbackShape J' where
  functor := wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))

attribute [local instance] uliftCategory in
/-- Lifting universe and morphism levels preserves wide pullback diagrams. -/
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePullbackShape J)) ≌ WidePullbackShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePullbackShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

end WidePullbackShape

namespace WidePushoutShape

variable {J}

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of arrows for the shape indexing a wide pushout. -/
inductive Hom : WidePushoutShape J → WidePushoutShape J → Type w
  | id : ∀ X, Hom X X
  | init : ∀ j : J, Hom none (some j)
  deriving DecidableEq

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

instance Hom.inhabited : Inhabited (Hom (none : WidePushoutShape J) none) :=
  ⟨Hom.id (none : WidePushoutShape J)⟩

open Lean Elab Tactic
-- Pointing note: experimenting with manual scoping of aesop tactics; only this worked
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
def evalCasesBash' : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePushoutShape _,
      (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _) ))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash'

instance subsingleton_hom : Quiver.IsThin (WidePushoutShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePushoutShape _, (_ : WidePushoutShape _) ⟶ (_ : WidePushoutShape _)
  repeat rfl

instance category : SmallCategory (WidePushoutShape J) :=
  thin_category

@[simp]
theorem hom_id (X : WidePushoutShape J) : Hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/
@[simps]
def wideSpan (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : WidePushoutShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map f := by
    obtain - | j := f
    · apply 𝟙 _
    · exact arrows j
  map_comp := fun f g => by
    cases f
    · simp only [hom_id, Category.id_comp]; congr
    · cases g
      simp only [hom_id, Category.comp_id]; congr

/-- Every diagram is naturally isomorphic (actually, equal) to a `wideSpan` -/
def diagramIsoWideSpan (F : WidePushoutShape J ⥤ C) :
    F ≅ wideSpan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.init j) :=
  NatIso.ofComponents fun j => eqToIso <| by cases j; repeat rfl

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
          cases j <;> cases j' <;> cases f <;> simp [w] } }

/-- Wide pushout diagrams of equivalent index types are equivalent. -/
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') : WidePushoutShape J ≌ WidePushoutShape J' where
  functor := wideSpan none (fun j => some (h j)) fun j => Hom.init (h j)
  inverse := wideSpan none (fun j => some (h.invFun j)) fun j => Hom.init (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))

attribute [local instance] uliftCategory in
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

/-- `HasWidePushouts` represents a choice of wide pushout for every collection of morphisms -/
abbrev HasWidePushouts : Prop :=
  ∀ J : Type w, HasColimitsOfShape (WidePushoutShape J) C

variable {C J}

/-- `HasWidePullback B objs arrows` means that `wideCospan B objs arrows` has a limit. -/
abbrev HasWidePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : Prop :=
  HasLimit (WidePullbackShape.wideCospan B objs arrows)

/-- `HasWidePushout B objs arrows` means that `wideSpan B objs arrows` has a colimit. -/
abbrev HasWidePushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j) : Prop :=
  HasColimit (WidePushoutShape.wideSpan B objs arrows)

/-- A choice of wide pullback. -/
noncomputable abbrev widePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    [HasWidePullback B objs arrows] : C :=
  limit (WidePullbackShape.wideCospan B objs arrows)

/-- A choice of wide pushout. -/
noncomputable abbrev widePushout (B : C) (objs : J → C) (arrows : ∀ j : J, B ⟶ objs j)
    [HasWidePushout B objs arrows] : C :=
  colimit (WidePushoutShape.wideSpan B objs arrows)

namespace WidePullback

variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, objs j ⟶ B)
variable [HasWidePullback B objs arrows]

/-- The `j`-th projection from the pullback. -/
noncomputable abbrev π (j : J) : widePullback _ _ arrows ⟶ objs j :=
  limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)


/-- The unique map to the base from the pullback. -/
noncomputable abbrev base : widePullback _ _ arrows ⟶ B :=
  limit.π (WidePullbackShape.wideCospan _ _ _) Option.none

@[reassoc (attr := simp)]
theorem π_arrow (j : J) : π arrows j ≫ arrows _ = base arrows := by
  apply limit.w (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.Hom.term j)

variable {arrows} in
/-- Lift a collection of morphisms to a morphism to the pullback. -/
noncomputable abbrev lift {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j)
    (w : ∀ j, fs j ≫ arrows j = f) : X ⟶ widePullback _ _ arrows :=
  limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)

variable {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j) (w : ∀ j, fs j ≫ arrows j = f)

@[reassoc]
theorem lift_π (j : J) : lift f fs w ≫ π arrows j = fs _ := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_pt, WidePullbackShape.mkCone_π_app]

@[reassoc]
theorem lift_base : lift f fs w ≫ base arrows = f := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_pt, WidePullbackShape.mkCone_π_app]

theorem eq_lift_of_comp_eq (g : X ⟶ widePullback _ _ arrows) :
    (∀ j : J, g ≫ π arrows j = fs j) → g ≫ base arrows = f → g = lift f fs w := by
  intro h1 h2
  apply
    (limit.isLimit (WidePullbackShape.wideCospan B objs arrows)).uniq
      (WidePullbackShape.mkCone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

theorem hom_eq_lift (g : X ⟶ widePullback _ _ arrows) :
    g = lift (g ≫ base arrows) (fun j => g ≫ π arrows j) (by simp) := by
  aesop

@[ext 1100]
theorem hom_ext (g1 g2 : X ⟶ widePullback _ _ arrows) : (∀ j : J,
    g1 ≫ π arrows j = g2 ≫ π arrows j) → g1 ≫ base arrows = g2 ≫ base arrows → g1 = g2 := by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

end WidePullback

namespace WidePushout

variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, B ⟶ objs j)
variable [HasWidePushout B objs arrows]

/-- The `j`-th inclusion to the pushout. -/
noncomputable abbrev ι (j : J) : objs j ⟶ widePushout _ _ arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) (Option.some j)

/-- The unique map from the head to the pushout. -/
noncomputable abbrev head : B ⟶ widePushout B objs arrows :=
  colimit.ι (WidePushoutShape.wideSpan _ _ _) Option.none

@[reassoc, simp]
theorem arrow_ι (j : J) : arrows j ≫ ι arrows j = head arrows := by
  apply colimit.w (WidePushoutShape.wideSpan _ _ _) (WidePushoutShape.Hom.init j)

variable {arrows} in
/-- Descend a collection of morphisms to a morphism from the pushout. -/
noncomputable abbrev desc {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X)
    (w : ∀ j, arrows j ≫ fs j = f) : widePushout _ _ arrows ⟶ X :=
  colimit.desc (WidePushoutShape.wideSpan B objs arrows) (WidePushoutShape.mkCocone f fs <| w)

variable {X : C} (f : B ⟶ X) (fs : ∀ j : J, objs j ⟶ X) (w : ∀ j, arrows j ≫ fs j = f)

@[reassoc]
theorem ι_desc (j : J) : ι arrows j ≫ desc f fs w = fs _ := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_pt, WidePushoutShape.mkCocone_ι_app]

@[reassoc]
theorem head_desc : head arrows ≫ desc f fs w = f := by
  simp only [colimit.ι_desc, WidePushoutShape.mkCocone_pt, WidePushoutShape.mkCocone_ι_app]

theorem eq_desc_of_comp_eq (g : widePushout _ _ arrows ⟶ X) :
    (∀ j : J, ι arrows j ≫ g = fs j) → head arrows ≫ g = f → g = desc f fs w := by
  intro h1 h2
  apply
    (colimit.isColimit (WidePushoutShape.wideSpan B objs arrows)).uniq
      (WidePushoutShape.mkCocone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

theorem hom_eq_desc (g : widePushout _ _ arrows ⟶ X) :
    g =
      desc (head arrows ≫ g) (fun j => ι arrows j ≫ g) fun j => by
        rw [← Category.assoc]
        simp := by
  cat_disch

@[ext 1100]
theorem hom_ext (g1 g2 : widePushout _ _ arrows ⟶ X) : (∀ j : J,
    ι arrows j ≫ g1 = ι arrows j ≫ g2) → head arrows ≫ g1 = head arrows ≫ g2 → g1 = g2 := by
  intro h1 h2
  apply colimit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

end WidePushout

variable (J)

/-- The action on morphisms of the obvious functor
  `WidePullbackShape_op : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ` -/
def widePullbackShapeOpMap :
    ∀ X Y : WidePullbackShape J,
      (X ⟶ Y) → ((op X : (WidePushoutShape J)ᵒᵖ) ⟶ (op Y : (WidePushoutShape J)ᵒᵖ))
  | _, _, WidePullbackShape.Hom.id X => Quiver.Hom.op (WidePushoutShape.Hom.id _)
  | _, _, WidePullbackShape.Hom.term _ => Quiver.Hom.op (WidePushoutShape.Hom.init _)

/-- The obvious functor `WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ` -/
@[simps]
def widePullbackShapeOp : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where
  obj X := op X
  map {X₁} {X₂} := widePullbackShapeOpMap J X₁ X₂

/-- The action on morphisms of the obvious functor
`widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/
def widePushoutShapeOpMap :
    ∀ X Y : WidePushoutShape J,
      (X ⟶ Y) → ((op X : (WidePullbackShape J)ᵒᵖ) ⟶ (op Y : (WidePullbackShape J)ᵒᵖ))
  | _, _, WidePushoutShape.Hom.id X => Quiver.Hom.op (WidePullbackShape.Hom.id _)
  | _, _, WidePushoutShape.Hom.init _ => Quiver.Hom.op (WidePullbackShape.Hom.term _)

/-- The obvious functor `WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/
@[simps]
def widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ where
  obj X := op X
  map := fun {X} {Y} => widePushoutShapeOpMap J X Y

/-- The obvious functor `(WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J` -/
@[simps!]
def widePullbackShapeUnop : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J :=
  (widePullbackShapeOp J).leftOp

/-- The obvious functor `(WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J` -/
@[simps!]
def widePushoutShapeUnop : (WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J :=
  (widePushoutShapeOp J).leftOp

/-- The inverse of the unit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
def widePushoutShapeOpUnop : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The counit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
def widePushoutShapeUnopOp : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The inverse of the unit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
def widePullbackShapeOpUnop : widePullbackShapeUnop J ⋙ widePushoutShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The counit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
def widePullbackShapeUnopOp : widePullbackShapeOp J ⋙ widePushoutShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The duality equivalence `(WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
@[simps]
def widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J where
  functor := widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J

/-- The duality equivalence `(WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
@[simps]
def widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J where
  functor := widePullbackShapeUnop J
  inverse := widePushoutShapeOp J
  unitIso := (widePullbackShapeOpUnop J).symm
  counitIso := widePushoutShapeUnopOp J

/-- If a category has wide pushouts on a higher universe level it also has wide pushouts
on a lower universe level. -/
theorem hasWidePushouts_shrink [HasWidePushouts.{max w w'} C] : HasWidePushouts.{w} C := fun _ =>
  hasColimitsOfShape_of_equivalence (WidePushoutShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

/-- If a category has wide pullbacks on a higher universe level it also has wide pullbacks
on a lower universe level. -/
theorem hasWidePullbacks_shrink [HasWidePullbacks.{max w w'} C] : HasWidePullbacks.{w} C := fun _ =>
  hasLimitsOfShape_of_equivalence (WidePullbackShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

end CategoryTheory.Limits
