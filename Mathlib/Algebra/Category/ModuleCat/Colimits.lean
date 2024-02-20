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

universe w' w u v

open CategoryTheory Category Limits

variable {R : Type w} [Ring R]

namespace ModuleCat

variable {J : Type u} [Category.{v} J] (F : J ⥤ ModuleCat.{w'} R)

namespace HasColimit

variable [HasColimit (F ⋙ forget₂ _ AddCommGroupCat)]

/-- The induced scalar multiplication on
`colimit (F ⋙ forget₂ _ AddCommGroupCat)`. -/
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

/-- The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGroupCat)`. -/
@[simps]
noncomputable def colimitCocone : Cocone F where
  pt := mkOfSMul (coconePointSMul F)
  ι :=
    { app := fun j => homMk (colimit.ι (F ⋙ forget₂ _ AddCommGroupCat)  j) (fun r => by
        dsimp
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [mkOfSMul_smul]
        simp)
      naturality := fun i j f => by
        apply (forget₂ _ AddCommGroupCat).map_injective
        simp only [Functor.map_comp, forget₂_map_homMk]
        dsimp
        erw [colimit.w (F ⋙ forget₂ _ AddCommGroupCat), comp_id] }

/-- The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGroupCat)` is a colimit cocone. -/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) where
  desc s := homMk (colimit.desc _ ((forget₂ _ AddCommGroupCat).mapCocone s)) (fun r => by
    apply colimit.hom_ext
    intro j
    dsimp
    rw [colimit.ι_desc_assoc]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [mkOfSMul_smul]
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
