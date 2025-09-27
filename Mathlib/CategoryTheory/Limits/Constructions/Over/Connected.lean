/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Connected limits in the over category

Shows that the forgetful functor `Over B ⥤ C` creates and preserves connected limits,
the latter without assuming that `C` has any limits.
In particular, `Over B` has any connected limit which `C` has.
-/


universe v' u' v u

-- morphism levels before object levels. See note [CategoryTheory universes].
noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {J : Type u'} [Category.{v'} J]
variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace CategoryTheory.Over

namespace CreatesConnected

/-- (Impl) Given a diagram in the over category, produce a natural transformation from the
diagram legs to the specific object.
-/
def natTransInOver {B : C} (F : J ⥤ Over B) :
    F ⋙ forget B ⟶ (CategoryTheory.Functor.const J).obj B where
  app j := (F.obj j).hom

/-- (Impl) Given a cone in the base category, raise it to a cone in the over category. Note this is
where the connected assumption is used.
-/
@[simps]
def raiseCone [IsConnected J] {B : C} {F : J ⥤ Over B} (c : Cone (F ⋙ forget B)) :
    Cone F where
  pt := Over.mk (c.π.app (Classical.arbitrary J) ≫ (F.obj (Classical.arbitrary J)).hom)
  π :=
    { app := fun j =>
        Over.homMk (c.π.app j) (nat_trans_from_is_connected (c.π ≫ natTransInOver F) j _)
      naturality := by
        intro X Y f
        apply CommaMorphism.ext
        · simpa using (c.w f).symm
        · simp }

theorem raised_cone_lowers_to_original [IsConnected J] {B : C} {F : J ⥤ Over B}
    (c : Cone (F ⋙ forget B)) :
    (forget B).mapCone (raiseCone c) = c := by cat_disch

/-- (Impl) Show that the raised cone is a limit. -/
def raisedConeIsLimit [IsConnected J] {B : C} {F : J ⥤ Over B} {c : Cone (F ⋙ forget B)}
    (t : IsLimit c) : IsLimit (raiseCone c) where
  lift s :=
    Over.homMk (t.lift ((forget B).mapCone s))
  uniq s m K := by
    ext1
    apply t.hom_ext
    intro j
    simp [← K j]

end CreatesConnected

/-- The forgetful functor from the over category creates any connected limit. -/
instance forgetCreatesConnectedLimits [IsConnected J] {B : C} :
    CreatesLimitsOfShape J (forget B) where
  CreatesLimit :=
    createsLimitOfReflectsIso fun c t =>
      { liftedCone := CreatesConnected.raiseCone c
        validLift := eqToIso (CreatesConnected.raised_cone_lowers_to_original c)
        makesLimit := CreatesConnected.raisedConeIsLimit t }

/-- The forgetful functor from the over category preserves any connected limit. -/
instance forgetPreservesConnectedLimits [IsConnected J] {B : C} :
    PreservesLimitsOfShape J (forget B) where
  preservesLimit := {
    preserves hc := ⟨{
      lift s := (forget B).map (hc.lift (CreatesConnected.raiseCone s))
      fac _ _ := by
        rw [Functor.mapCone_π_app, ← Functor.map_comp, hc.fac,
          CreatesConnected.raiseCone_π_app, forget_map, homMk_left _ _]
      uniq s m fac :=
        congrArg (forget B).map (hc.uniq (CreatesConnected.raiseCone s)
          (Over.homMk m (by simp [← fac])) fun j => (forget B).map_injective (fac j))
    }⟩
  }

/-- The over category has any connected limit which the original category has. -/
instance has_connected_limits {B : C} [IsConnected J] [HasLimitsOfShape J C] :
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
    conePost F i ⋙ Cones.functoriality _ (Over.forget (F.obj i)) ≅
      Cones.whiskering (Over.forget _) := .refl _

attribute [local instance] IsCofiltered.isConnected in
/-- The functor taking a cone over `F` to a cone over `Over.post F : Over i ⥤ Over (F.obj i)`
preserves limit cones -/
noncomputable
def isLimitConePost [IsCofilteredOrEmpty J] {F : J ⥤ C} {c : Cone F} (i : J) (hc : IsLimit c) :
    IsLimit ((conePost F i).obj c) :=
  isLimitOfReflects (Over.forget _)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

end CategoryTheory.Over
