/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Opposites
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Connected limits in the over category

We show that the projection `CostructuredArrow K B ⥤ C` creates and preserves
connected limits, without assuming that `C` has any limits.
In particular, `CostructuredArrow K B` has any connected limit which `C` has.

From this we deduce the corresponding results for the over category.
-/

@[expose] public section

universe v' u' v u

-- morphism levels before object levels. See note [category theory universes].
noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {J : Type u'} [Category.{v'} J]
variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D] {K : C ⥤ D}
variable {X : C}

namespace CategoryTheory.CostructuredArrow

namespace CreatesConnected

/-- (Implementation) Given a diagram in `CostructuredArrow K B`, produce a natural transformation
from the diagram legs to the specific object.
-/
@[simps]
def natTransInCostructuredArrow {B : D} (F : J ⥤ CostructuredArrow K B) :
    F ⋙ CostructuredArrow.proj K B ⋙ K ⟶ (CategoryTheory.Functor.const J).obj B where
  app j := (F.obj j).hom

/-- (Implementation) Given a cone in the base category, raise it to a cone in
`CostructuredArrow K B`. Note this is where the connected assumption is used.
-/
@[simps]
def raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    (c : Cone (F ⋙ CostructuredArrow.proj K B)) :
    Cone F where
  pt := CostructuredArrow.mk
    (K.map (c.π.app (Classical.arbitrary J)) ≫ (F.obj (Classical.arbitrary J)).hom)
  π.app j := CostructuredArrow.homMk (c.π.app j) <| by
    let z : (Functor.const J).obj (K.obj c.pt) ⟶ _ :=
      (CategoryTheory.Functor.constComp J c.pt K).inv ≫ Functor.whiskerRight c.π K ≫
        natTransInCostructuredArrow F
    convert (nat_trans_from_is_connected z j (Classical.arbitrary J)) <;> simp [z]
  π.naturality X Y f := by
    apply CommaMorphism.ext
    · simpa using (c.w f).symm
    · simp

theorem mapCone_raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    (c : Cone (F ⋙ CostructuredArrow.proj K B)) :
    (CostructuredArrow.proj K B).mapCone (raiseCone c) = c := by cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) Show that the raised cone is a limit. -/
def isLimitRaiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    {c : Cone (F ⋙ CostructuredArrow.proj K B)}
    (t : IsLimit c) : IsLimit (raiseCone c) where
  lift s :=
    CostructuredArrow.homMk (t.lift ((CostructuredArrow.proj K B).mapCone s)) <| by
      simp [← Functor.map_comp_assoc]
  uniq s m K := by
    ext1
    apply t.hom_ext
    intro j
    simp [← K j]

end CreatesConnected

/-- The projection from `CostructuredArrow K B` to `C` creates any connected limit. -/
instance [IsConnected J] {B : D} : CreatesLimitsOfShape J (CostructuredArrow.proj K B) where
  CreatesLimit :=
    createsLimitOfReflectsIso fun c t =>
      { liftedCone := CreatesConnected.raiseCone c
        validLift := eqToIso (CreatesConnected.mapCone_raiseCone c)
        makesLimit := CreatesConnected.isLimitRaiseCone t }

set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor from `CostructuredArrow K B` preserves any connected limit. -/
instance [IsConnected J] {B : D} : PreservesLimitsOfShape J (CostructuredArrow.proj K B) where
  preservesLimit.preserves hc := ⟨{
    lift s := (CostructuredArrow.proj K B).map (hc.lift (CreatesConnected.raiseCone s))
    fac _ _ := by
      rw [Functor.mapCone_π_app, ← Functor.map_comp, hc.fac,
        CreatesConnected.raiseCone_π_app, CostructuredArrow.proj_map,
        CostructuredArrow.homMk_left _ _]
    uniq s m fac :=
      congrArg (CostructuredArrow.proj K B).map (hc.uniq (CreatesConnected.raiseCone s)
        (CostructuredArrow.homMk m (by simp [← fac])) fun j =>
          (CostructuredArrow.proj K B).map_injective (fac j))
  }⟩

/-- The over category has any connected limit which the original category has. -/
instance hasLimitsOfShape_of_isConnected {B : D} [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CostructuredArrow K B) where
  has_limit F := hasLimit_of_created F (CostructuredArrow.proj K B)

end CostructuredArrow

namespace StructuredArrow

/-- The projection from `StructuredArrow K B` to `C` creates any connected colimit. -/
instance [IsConnected J] {B : D} : CreatesColimitsOfShape J (StructuredArrow.proj B K) :=
  letI : CreatesLimitsOfShape Jᵒᵖ (proj B K).op :=
    inferInstanceAs <| CreatesLimitsOfShape Jᵒᵖ <|
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  createsColimitsOfShapeOfOp _ _

/-- The forgetful functor from `StructuredArrow K B` preserves any connected colimit. -/
instance [IsConnected J] {B : D} : PreservesColimitsOfShape J (StructuredArrow.proj B K) := by
  have : PreservesLimitsOfShape Jᵒᵖ (proj B K).op :=
    inferInstanceAs <| PreservesLimitsOfShape Jᵒᵖ <|
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  apply preservesColimitsOfShape_of_op

instance {B : D} [IsConnected J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (StructuredArrow B K) where
  has_colimit F := hasColimit_of_created F (StructuredArrow.proj B K)

end StructuredArrow

namespace Over

/-- The forgetful functor from the over category creates any connected limit. -/
instance createsLimitsOfShapeForgetOfIsConnected [IsConnected J] {B : C} :
    CreatesLimitsOfShape J (forget B) :=
  inferInstanceAs <| CreatesLimitsOfShape J (CostructuredArrow.proj _ _)

/-- The forgetful functor from the over category preserves any connected limit. -/
instance preservesLimitsOfShape_forget_of_isConnected [IsConnected J] {B : C} :
    PreservesLimitsOfShape J (forget B) :=
  inferInstanceAs <| PreservesLimitsOfShape J (CostructuredArrow.proj _ _)

/-- The over category has any connected limit which the original category has. -/
instance hasLimitsOfShape_of_isConnected {B : C} [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (Over B) where
  has_limit F := hasLimit_of_created F (forget B)

/-- The functor taking a cone over `F` to a cone over `Over.post F : Over i ⥤ Over (F.obj i)`.
This takes limit cones to limit cones when `J` is cofiltered. See `isLimitConePost` -/
@[simps]
def conePost (F : J ⥤ C) (i : J) : Cone F ⥤ Cone (Over.post (X := i) F) where
  obj c := { pt := Over.mk (c.π.app i), π := { app X := Over.homMk (c.π.app X.left) } }
  map f := { hom := Over.homMk f.hom }

/-- `conePost` is compatible with the forgetful functors on over categories. -/
@[simps!]
def conePostIso (F : J ⥤ C) (i : J) :
    conePost F i ⋙ Cone.functoriality _ (Over.forget (F.obj i)) ≅
      Cone.whiskering (Over.forget _) := .refl _

attribute [local instance] IsCofiltered.isConnected in
/-- The functor taking a cone over `F` to a cone over `Over.post F : Over i ⥤ Over (F.obj i)`
preserves limit cones -/
noncomputable
def isLimitConePost [IsCofilteredOrEmpty J] {F : J ⥤ C} {c : Cone F} (i : J) (hc : IsLimit c) :
    IsLimit ((conePost F i).obj c) :=
  isLimitOfReflects (Over.forget _)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

end Over

namespace Under

/-- The forgetful functor from the under category creates any connected limit. -/
instance createsColimitsOfShapeForgetOfIsConnected [IsConnected J] {B : C} :
    CreatesColimitsOfShape J (forget B) :=
  inferInstanceAs <| CreatesColimitsOfShape J (StructuredArrow.proj _ _)

/-- The forgetful functor from the under category preserves any connected limit. -/
instance preservesColimitsOfShape_forget_of_isConnected [IsConnected J] {B : C} :
    PreservesColimitsOfShape J (forget B) :=
  inferInstanceAs <| PreservesColimitsOfShape J (StructuredArrow.proj _ _)

/-- The under category has any connected limit which the original category has. -/
instance hasColimitsOfShape_of_isConnected {B : C} [IsConnected J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (Under B) where
  has_colimit F := hasColimit_of_created F (forget B)

end CategoryTheory.Under
