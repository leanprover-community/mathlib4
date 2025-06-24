/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# The category of R-modules has all colimits.

From the existence of colimits in `AddCommGrp`, we deduce the existence of colimits
in `ModuleCat R`. This way, we get for free that the functor
`forget₂ (ModuleCat R) AddCommGrp` commutes with colimits.

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

variable [HasColimit (F ⋙ forget₂ _ AddCommGrp)]

/-- The induced scalar multiplication on
`colimit (F ⋙ forget₂ _ AddCommGrp)`. -/
@[simps]
noncomputable def coconePointSMul :
    R →+* End (colimit (F ⋙ forget₂ _ AddCommGrp)) where
  toFun r := colimMap
    { app := fun j => (F.obj j).smul r
      naturality := fun _ _ _ => smul_naturality _ _ }
  map_zero' := colimit.hom_ext (by simp)
  map_one' := colimit.hom_ext (by simp)
  map_add' r s := colimit.hom_ext (fun j => by
    simp only [Functor.comp_obj, forget₂_obj, map_add, ι_colimMap]
    rw [Preadditive.add_comp, Preadditive.comp_add]
    simp only [ι_colimMap, Functor.comp_obj, forget₂_obj])
  map_mul' r s := colimit.hom_ext (fun j => by simp)

/-- The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGrp)`. -/
@[simps]
noncomputable def colimitCocone : Cocone F where
  pt := mkOfSMul (coconePointSMul F)
  ι :=
    { app := fun j => homMk (colimit.ι (F ⋙ forget₂ _ AddCommGrp)  j) (fun r => by
        dsimp
        -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
        erw [mkOfSMul_smul]
        simp)
      naturality := fun i j f => by
        apply (forget₂ _ AddCommGrp).map_injective
        simp only [Functor.map_comp, forget₂_map_homMk]
        dsimp
        erw [colimit.w (F ⋙ forget₂ _ AddCommGrp), comp_id] }

/-- The cocone for `F` constructed from the colimit of
`(F ⋙ forget₂ (ModuleCat R) AddCommGrp)` is a colimit cocone. -/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) where
  desc s := homMk (colimit.desc _ ((forget₂ _ AddCommGrp).mapCocone s)) (fun r => by
    apply colimit.hom_ext
    intro j
    dsimp
    rw [colimit.ι_desc_assoc]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [mkOfSMul_smul]
    dsimp
    simp only [ι_colimMap_assoc, Functor.comp_obj, forget₂_obj, colimit.ι_desc,
      Functor.mapCocone_pt, Functor.mapCocone_ι_app, forget₂_map]
    exact smul_naturality (s.ι.app j) r)
  fac s j := by
    apply (forget₂ _ AddCommGrp).map_injective
    exact colimit.ι_desc ((forget₂ _ AddCommGrp).mapCocone s) j
  uniq s m hm := by
    apply (forget₂ _ AddCommGrp).map_injective
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc ((forget₂ _ AddCommGrp).mapCocone s) j]
    dsimp
    rw [← hm]
    rfl

instance : HasColimit F := ⟨_, isColimitColimitCocone F⟩

noncomputable instance : PreservesColimit F (forget₂ _ AddCommGrp) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

noncomputable instance reflectsColimit :
    ReflectsColimit F (forget₂ (ModuleCat.{w'} R) AddCommGrp) :=
  reflectsColimit_of_reflectsIsomorphisms _ _

end HasColimit

variable (J R)

instance hasColimitsOfShape [HasColimitsOfShape J AddCommGrp.{w'}] :
    HasColimitsOfShape J (ModuleCat.{w'} R) where

noncomputable instance reflectsColimitsOfShape [HasColimitsOfShape J AddCommGrp.{w'}] :
    ReflectsColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGrp) where

instance hasColimitsOfSize [HasColimitsOfSize.{v, u} AddCommGrp.{w'}] :
    HasColimitsOfSize.{v, u} (ModuleCat.{w'} R) where

noncomputable instance forget₂PreservesColimitsOfShape
    [HasColimitsOfShape J AddCommGrp.{w'}] :
    PreservesColimitsOfShape J (forget₂ (ModuleCat.{w'} R) AddCommGrp) where

noncomputable instance forget₂PreservesColimitsOfSize
    [HasColimitsOfSize.{u, v} AddCommGrp.{w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{w'} R) AddCommGrp) where

noncomputable instance
    [HasColimitsOfSize.{u, v} AddCommGrpMax.{w, w'}] :
    PreservesColimitsOfSize.{u, v} (forget₂ (ModuleCat.{max w w'} R) AddCommGrp) where

instance : HasFiniteColimits (ModuleCat.{w'} R) := inferInstance

-- Sanity checks, just to make sure typeclass search can find the instances we want.
example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max v u} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{max u v} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasColimits (ModuleCat.{u} R) :=
  inferInstance

example (R : Type u) [Ring R] : HasCoequalizers (ModuleCat.{u} R) := by
  infer_instance

-- for some reason, this instance is not found automatically later on
instance : HasCoequalizers (ModuleCat.{v} R) where

noncomputable example (R : Type u) [Ring R] :
  PreservesColimits (forget₂ (ModuleCat.{u} R) AddCommGrp) := inferInstance

end ModuleCat
