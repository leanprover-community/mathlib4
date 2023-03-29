/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.over
! leanprover-community/mathlib commit 3e0dd193514c9380edc69f1da92e80c02713c41d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Adjunction.Opposites
import Mathbin.CategoryTheory.Limits.Preserves.Basic
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Creates
import Mathbin.CategoryTheory.Limits.Comma

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : over X ⥤ C` creates colimits, and hence `over X` has
any colimits that `C` has (as well as the dual that `forget X : under X ⟶ C` creates limits).

Note that the folder `category_theory.limits.shapes.constructions.over` further shows that
`forget X : over X ⥤ C` creates connected limits (so `over X` has connected limits), and that
`over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.

TODO: If `C` has binary products, then `forget X : over X ⥤ C` has a right adjoint.
-/


noncomputable section

universe v u

-- morphism levels before object levels. See note [category_theory universes].
open CategoryTheory CategoryTheory.Limits

variable {J : Type v} [SmallCategory J]

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

instance hasColimit_of_hasColimit_comp_forget (F : J ⥤ Over X) [i : HasColimit (F ⋙ forget X)] :
    HasColimit F :=
  @CostructuredArrow.hasColimit _ _ _ _ i _
#align category_theory.over.has_colimit_of_has_colimit_comp_forget CategoryTheory.Over.hasColimit_of_hasColimit_comp_forget

instance [HasColimitsOfShape J C] : HasColimitsOfShape J (Over X) where

instance [HasColimits C] : HasColimits (Over X) :=
  ⟨inferInstance⟩

instance createsColimits : CreatesColimits (forget X) :=
  CostructuredArrow.createsColimits
#align category_theory.over.creates_colimits CategoryTheory.Over.createsColimits

-- We can automatically infer that the forgetful functor preserves and reflects colimits.
example [HasColimits C] : PreservesColimits (forget X) :=
  inferInstance

example : ReflectsColimits (forget X) :=
  inferInstance

theorem epi_left_of_epi [HasPushouts C] {f g : Over X} (h : f ⟶ g) [Epi h] : Epi h.left :=
  CostructuredArrow.epi_left_of_epi _
#align category_theory.over.epi_left_of_epi CategoryTheory.Over.epi_left_of_epi

theorem epi_iff_epi_left [HasPushouts C] {f g : Over X} (h : f ⟶ g) : Epi h ↔ Epi h.left :=
  CostructuredArrow.epi_iff_epi_left _
#align category_theory.over.epi_iff_epi_left CategoryTheory.Over.epi_iff_epi_left

section

variable [HasPullbacks C]

open Tactic

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `over Y ⥤ over X`,
by pulling back a morphism along `f`. -/
@[simps]
def pullback {X Y : C} (f : X ⟶ Y) : Over Y ⥤ Over X
    where
  obj g := Over.mk (pullback.snd : pullback g.Hom f ⟶ X)
  map g h k :=
    Over.homMk (pullback.lift (pullback.fst ≫ k.left) pullback.snd (by simp [pullback.condition]))
      (by tidy)
#align category_theory.over.pullback CategoryTheory.Over.pullback

/-- `over.map f` is left adjoint to `over.pullback f`. -/
def mapPullbackAdj {A B : C} (f : A ⟶ B) : Over.map f ⊣ pullback f :=
  Adjunction.mkOfHomEquiv
    {
      homEquiv := fun g h =>
        { toFun := fun X =>
            Over.homMk (pullback.lift X.left g.Hom (Over.w X)) (pullback.lift_snd _ _ _)
          invFun := fun Y => by
            refine' over.hom_mk _ _
            refine' Y.left ≫ pullback.fst
            dsimp
            rw [← over.w Y, category.assoc, pullback.condition, category.assoc]; rfl
          left_inv := fun X => by
            ext
            dsimp
            simp
          right_inv := fun Y => by
            ext; dsimp
            simp only [pullback.lift_fst]
            dsimp
            rw [pullback.lift_snd, ← over.w Y]
            rfl } }
#align category_theory.over.map_pullback_adj CategoryTheory.Over.mapPullbackAdj

/-- pullback (𝟙 A) : over A ⥤ over A is the identity functor. -/
def pullbackId {A : C} : pullback (𝟙 A) ≅ 𝟭 _ :=
  Adjunction.rightAdjointUniq (mapPullbackAdj _) (Adjunction.id.ofNatIsoLeft Over.mapId.symm)
#align category_theory.over.pullback_id CategoryTheory.Over.pullbackId

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  Adjunction.rightAdjointUniq (mapPullbackAdj _)
    (((mapPullbackAdj _).comp (mapPullbackAdj _)).ofNatIsoLeft (Over.mapComp _ _).symm)
#align category_theory.over.pullback_comp CategoryTheory.Over.pullbackComp

instance pullbackIsRightAdjoint {A B : C} (f : A ⟶ B) : IsRightAdjoint (pullback f) :=
  ⟨_, mapPullbackAdj f⟩
#align category_theory.over.pullback_is_right_adjoint CategoryTheory.Over.pullbackIsRightAdjoint

end

end CategoryTheory.Over

namespace CategoryTheory.Under

instance hasLimit_of_hasLimit_comp_forget (F : J ⥤ Under X) [i : HasLimit (F ⋙ forget X)] :
    HasLimit F :=
  @StructuredArrow.hasLimit _ _ _ _ i _
#align category_theory.under.has_limit_of_has_limit_comp_forget CategoryTheory.Under.hasLimit_of_hasLimit_comp_forget

instance [HasLimitsOfShape J C] : HasLimitsOfShape J (Under X) where

instance [HasLimits C] : HasLimits (Under X) :=
  ⟨inferInstance⟩

theorem mono_right_of_mono [HasPullbacks C] {f g : Under X} (h : f ⟶ g) [Mono h] : Mono h.right :=
  StructuredArrow.mono_right_of_mono _
#align category_theory.under.mono_right_of_mono CategoryTheory.Under.mono_right_of_mono

theorem mono_iff_mono_right [HasPullbacks C] {f g : Under X} (h : f ⟶ g) : Mono h ↔ Mono h.right :=
  StructuredArrow.mono_iff_mono_right _
#align category_theory.under.mono_iff_mono_right CategoryTheory.Under.mono_iff_mono_right

instance createsLimits : CreatesLimits (forget X) :=
  StructuredArrow.createsLimits
#align category_theory.under.creates_limits CategoryTheory.Under.createsLimits

-- We can automatically infer that the forgetful functor preserves and reflects limits.
example [HasLimits C] : PreservesLimits (forget X) :=
  inferInstance

example : ReflectsLimits (forget X) :=
  inferInstance

section

variable [HasPushouts C]

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `under X ⥤ under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) : Under X ⥤ Under Y
    where
  obj g := Under.mk (pushout.inr : Y ⟶ pushout g.Hom f)
  map g h k :=
    Under.homMk (pushout.desc (k.right ≫ pushout.inl) pushout.inr (by simp [← pushout.condition]))
      (by tidy)
#align category_theory.under.pushout CategoryTheory.Under.pushout

end

end CategoryTheory.Under

