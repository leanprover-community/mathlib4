/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The category of left R-modules is abelian.

Additionally, two linear maps are exact in the categorical sense iff `range f = ker g`.
-/


open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe w v u

namespace ModuleCat

variable {R : Type u} [Ring R] {M N : ModuleCat.{v} R} (f : M ⟶ N)

/-- In the category of modules, every monomorphism is normal. -/
def normalMono (hf : Mono f) : NormalMono f where
  Z := of R (N ⧸ LinearMap.range f.hom)
  g := ofHom (LinearMap.range f.hom).mkQ
  w := hom_ext <| LinearMap.range_mkQ_comp _
  isLimit :=
    /- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
        might help you understand what's going on here:
        ```
        calc
        M   ≃ₗ[R] f.ker.quotient  : (Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm
        ... ≃ₗ[R] f.range         : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] r.range.mkQ.ker : LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm
        ```
      -/
        IsKernel.isoKernel _ _ (kernelIsLimit _)
          (LinearEquiv.toModuleIso
            ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
              (LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm))) <| by ext; rfl

/-- In the category of modules, every epimorphism is normal. -/
def normalEpi (hf : Epi f) : NormalEpi f where
  W := of R (LinearMap.ker f.hom)
  g := ofHom (LinearMap.ker f.hom).subtype
  w := hom_ext <| LinearMap.comp_ker_subtype _
  isColimit :=
    /- The following invalid Lean code might help you understand what's going on here:
        ```
        calc f.ker.subtype.range.quotient
            ≃ₗ[R] f.ker.quotient : Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _)
        ... ≃ₗ[R] f.range        : LinearMap.quotKerEquivRange f
        ... ≃ₗ[R] N              : LinearEquiv.ofTop _ (range_eq_top_of_epi _)
        ```
      -/
        IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
          (LinearEquiv.toModuleIso
            (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
                LinearMap.quotKerEquivRange f.hom ≪≫ₗ
              LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

/-- The category of R-modules is abelian. -/
instance abelian : Abelian (ModuleCat.{v} R) where
  has_cokernels := hasCokernels_moduleCat
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

section ReflectsLimits

/-- Add this instance to help Lean with universe levels. -/
instance : HasLimitsOfSize.{v,v} (ModuleCat.{max v w} R) :=
  ModuleCat.hasLimitsOfSize.{v, v, max v w}

/- We need to put this in this weird spot because we need to know that the category of modules
    is balanced. -/
instance forget_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget (ModuleCat.{max v w} R)) :=
  reflectsLimits_of_reflectsIsomorphisms

instance forget₂_reflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget₂ (ModuleCat.{max v w} R) AddCommGrpCat.{max v w}) :=
  reflectsLimits_of_reflectsIsomorphisms

instance forget_reflectsLimits : ReflectsLimits (forget (ModuleCat.{v} R)) :=
  ModuleCat.forget_reflectsLimitsOfSize.{v, v}

instance forget₂_reflectsLimits : ReflectsLimits (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}) :=
  ModuleCat.forget₂_reflectsLimitsOfSize.{v, v}

end ReflectsLimits

end ModuleCat
