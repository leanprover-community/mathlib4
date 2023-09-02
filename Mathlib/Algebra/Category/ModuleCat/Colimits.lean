/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.Algebra.Category.GroupCat.Colimits

#align_import algebra.category.Module.colimits from "leanprover-community/mathlib"@"5a684ce82399d820475609907c6ef8dba5b1b97c"

/-!
# The category of R-modules has all colimits.

From the existence of colimits in `AddCommGroupCat`, we deduce the existence of colimits
in `ModuleCat R`. This way, we get for free that the functor
`forget₂ (ModuleCat R) AddCommGroupCat` commutes with colimits.

Note that finite colimits can already be obtained from the instance `Abelian (Module R)`.

TODO:
In fact, in `ModuleCat R` there is a much nicer model of colimits as quotients
of finitely supported functions, and we really should implement this as well.
-/

universe w'' w' w u v

open CategoryTheory Category Limits

variable {R : Type w} [Ring R]

namespace ModuleCat

variable (M N : ModuleCat.{v} R)

-- this should be moved to `Basic.lean`
def smul : R →+* End ((forget₂ (ModuleCat R) AddCommGroupCat).obj M) where
  toFun r :=
    { toFun := fun (m : M) => r • m
      map_zero' := by dsimp; rw [smul_zero]
      map_add' := fun x y => by dsimp; rw [smul_add] }
  map_one' := AddMonoidHom.ext (fun x => by dsimp; rw [one_smul])
  map_zero' := AddMonoidHom.ext (fun x => by dsimp; rw [zero_smul])
  map_mul' r s := AddMonoidHom.ext (fun (x : M) => (smul_smul r s x).symm)
  map_add' r s := AddMonoidHom.ext (fun (x : M) => add_smul r s x)

lemma smul_naturality {M N : ModuleCat.{v} R} (f : M ⟶ N) (r : R) :
    (forget₂ (ModuleCat R) AddCommGroupCat).map f ≫ N.smul r =
      M.smul r ≫ (forget₂ (ModuleCat R) AddCommGroupCat).map f := by
  ext x
  exact (f.map_smul r x).symm

@[nolint unusedArguments]
def mkOfSMul' {A : AddCommGroupCat} (_ : R →+* End A) := A

section

variable {A : AddCommGroupCat} (φ : R →+* End A)

instance : AddCommGroup (mkOfSMul' φ) := by
  dsimp only [mkOfSMul']
  infer_instance

instance : SMul R (mkOfSMul' φ) := ⟨fun r (x : A) => (show A ⟶ A from φ r) x⟩

@[simp]
lemma mkOfSMul'_smul (r : R) (x : mkOfSMul' φ) :
    r • x = (show A ⟶ A from φ r) x := rfl

instance : Module R (mkOfSMul' φ) where
  smul_zero _ := map_zero _
  smul_add _ _ _ := map_add _ _ _
  one_smul := by simp
  mul_smul := by simp
  add_smul _ _ _ := by simp; rfl
  zero_smul := by simp

abbrev mkOfSMul := ModuleCat.of R (mkOfSMul' φ)

@[simp]
lemma mkOfSMul_smul (r : R) : (mkOfSMul φ).smul r = φ r := rfl

end

section

variable {M N} (φ : (forget₂ (ModuleCat R) AddCommGroupCat).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGroupCat).obj N)
    (hφ : ∀ (r : R), φ ≫ N.smul r = M.smul r ≫ φ)

@[simps]
def homMk : M ⟶ N where
  toFun := φ
  map_add' _ _ := map_add _ _ _
  map_smul' r x := (congr_hom (hφ r) x).symm

lemma forget₂_map_homMk :
    (forget₂ (ModuleCat R) AddCommGroupCat).map (homMk φ hφ) = φ := rfl

end

end ModuleCat

namespace ModuleCat

-- refactor the colimits in `AddCommGroupCat` so as to generalize universes
variable {J : Type u} [Category.{v} J] (F : J ⥤ ModuleCat.{w'} R)

namespace HasColimit

variable [HasColimit (F ⋙ forget₂ _ AddCommGroupCat)]

@[simps]
noncomputable def coconePointSMul :
    R →+* End (colimit (F ⋙ forget₂ _ AddCommGroupCat)) where
  toFun r := colimMap
    { app := fun j => (F.obj j).smul r
      naturality := fun X Y f => smul_naturality _ _ }
  map_zero' := colimit.hom_ext (by simp)
  map_one' := colimit.hom_ext (by simp)
  map_add' r s := colimit.hom_ext (fun j => by
    simp only [Functor.comp_obj, forget₂_obj, map_add, ι_colimMap]
    rw [Preadditive.add_comp, Preadditive.comp_add]
    simp only [ι_colimMap, Functor.comp_obj, forget₂_obj])
  map_mul' r s := colimit.hom_ext (fun j => by simp)

@[simps]
noncomputable def colimitCocone : Cocone F where
  pt := mkOfSMul (coconePointSMul F)
  ι :=
    { app := fun j => homMk (colimit.ι (F ⋙ forget₂ _ AddCommGroupCat)  j) (fun r => by
        dsimp
        rw [mkOfSMul_smul]
        simp)
      naturality := fun i j f => by
        apply (forget₂ _ AddCommGroupCat).map_injective
        simp only [Functor.map_comp, forget₂_map_homMk]
        dsimp
        erw [colimit.w (F ⋙ forget₂ _ AddCommGroupCat), comp_id] }

noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) where
  desc s := homMk (colimit.desc _ ((forget₂ _ AddCommGroupCat).mapCocone s)) (fun r => by
    apply colimit.hom_ext
    intro j
    dsimp
    rw [colimit.ι_desc_assoc]
    rw [mkOfSMul_smul]
    dsimp
    simp only [ι_colimMap_assoc, Functor.comp_obj, forget₂_obj, colimit.ι_desc,
      Functor.mapCocone_pt, Functor.mapCocone_ι_app, forget₂_map]
    exact smul_naturality (s.ι.app j) r)
  fac s j := by
    apply (forget₂ _ AddCommGroupCat).map_injective
    exact colimit.ι_desc ((forget₂ _ AddCommGroupCat).mapCocone s) j
  uniq s m hm := by
    apply (forget₂ _ AddCommGroupCat).map_injective
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc ((forget₂ _ AddCommGroupCat).mapCocone s) j]
    dsimp
    rw [← hm]
    rfl

instance : HasColimit F := ⟨_, isColimitColimitCocone F⟩

noncomputable instance : PreservesColimit F (forget₂ _ AddCommGroupCat) :=
  preservesColimitOfPreservesColimitCocone (isColimitColimitCocone F) (colimit.isColimit _)

end HasColimit

variable (J R)

instance hasColimitsOfShape [HasColimitsOfShape J AddCommGroupCat.{w'}] :
    HasColimitsOfShape J (ModuleCat.{w'} R) where

instance hasColimitsOfSize [HasColimitsOfSize.{v, u} AddCommGroupCat.{w'}] :
    HasColimitsOfSize.{v, u} (ModuleCat.{w'} R) where

noncomputable instance forget₂PreservesColimitsOfShape
    [HasColimitsOfShape J AddCommGroupCat.{w'}] :
    PreservesColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGroupCat) where

noncomputable instance forget₂PreservesColimitsOfSize
    [HasColimitsOfSize.{u, v} AddCommGroupCat.{w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{w'} R) AddCommGroupCat) where

--instance [HasColimitsOfShape J (AddCommGroupCatMax.{w', w''})] :
--  HasColimitsOfShape J (ModuleCatMax.{w', w''} R) where
--
--instance [HasColimitsOfSize.{v, u} (AddCommGroupCatMax.{w', w''})] :
--  HasColimitsOfSize.{v, u} (ModuleCatMax.{w', w''} R) where

noncomputable instance
    [HasColimitsOfSize.{u, v} AddCommGroupCatMax.{w, w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCatMax.{w, w'} R) AddCommGroupCat) where

instance : HasFiniteColimits (ModuleCat.{w'} R) := inferInstance

-- Sanity checks, just to make sure typeclass search can find the instances we want.
example (R : Type u) [Ring R] : HasColimits (ModuleCatMax.{v, u} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCatMax.{u, v} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{u} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasCoequalizers (ModuleCat.{u} R) := by
  infer_instance

-- for some reason, this instance is not found automatically later on
instance : HasCoequalizers (ModuleCat.{v} R) where

noncomputable example (R : Type u) [Ring R] :
  PreservesColimits (forget₂ (ModuleCat.{u} R) AddCommGroupCat) := inferInstance

end ModuleCat
