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
  Z := of R (N ⧸ LinearMap.range f)
  g := f.range.mkQ
  w := LinearMap.range_mkQ_comp _
  isLimit :=
    /- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
        might help you understand what's going on here:
        ```
        calc
        M   ≃ₗ[R] f.ker.quotient  : (submodule.quot_equiv_of_eq_bot _ (ker_eq_bot_of_mono _)).symm
        ... ≃ₗ[R] f.range         : linear_map.quot_ker_equiv_range f
        ... ≃ₗ[R] r.range.mkq.ker : linear_equiv.of_eq _ _ (submodule.ker_mkq _).symm
        ```
      -/
        IsKernel.isoKernel _ _ (kernelIsLimit _)
          (LinearEquiv.toModuleIso'
            ((Submodule.quotEquivOfEqBot _ (ker_eq_bot_of_mono _)).symm ≪≫ₗ
              (LinearMap.quotKerEquivRange f ≪≫ₗ
              LinearEquiv.ofEq _ _ (Submodule.ker_mkQ _).symm))) <| by ext; rfl

/-- In the category of modules, every epimorphism is normal. -/
def normalEpi (hf : Epi f) : NormalEpi f where
  W := of R (LinearMap.ker f)
  g := (LinearMap.ker f).subtype
  w := LinearMap.comp_ker_subtype _
  isColimit :=
    /- The following invalid Lean code might help you understand what's going on here:
        ```
        calc f.ker.subtype.range.quotient
            ≃ₗ[R] f.ker.quotient : submodule.quot_equiv_of_eq _ _ (submodule.range_subtype _)
        ... ≃ₗ[R] f.range        : linear_map.quot_ker_equiv_range f
        ... ≃ₗ[R] N              : linear_equiv.of_top _ (range_eq_top_of_epi _)
        ```
      -/
        IsCokernel.cokernelIso _ _ (cokernelIsColimit _)
          (LinearEquiv.toModuleIso'
            (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _) ≪≫ₗ
                LinearMap.quotKerEquivRange f ≪≫ₗ
              LinearEquiv.ofTop _ (range_eq_top_of_epi _))) <| by ext; rfl

/-- The category of R-modules is abelian. -/
instance abelian : Abelian (ModuleCat.{v} R) where
  has_cokernels := hasCokernels_moduleCat
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi

section ReflectsLimits

-- Porting note: added to make the following definitions work
instance : HasLimitsOfSize.{v,v} (ModuleCatMax.{v, w} R) :=
  ModuleCat.hasLimitsOfSize.{v, v, max v w}

/- We need to put this in this weird spot because we need to know that the category of modules
    is balanced. -/
instance forgetReflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget (ModuleCatMax.{v, w} R)) :=
  reflectsLimitsOfReflectsIsomorphisms

instance forget₂ReflectsLimitsOfSize :
    ReflectsLimitsOfSize.{v, v} (forget₂ (ModuleCatMax.{v, w} R) AddCommGrp.{max v w}) :=
  reflectsLimitsOfReflectsIsomorphisms

instance forgetReflectsLimits : ReflectsLimits (forget (ModuleCat.{v} R)) :=
  ModuleCat.forgetReflectsLimitsOfSize.{v, v}

instance forget₂ReflectsLimits : ReflectsLimits (forget₂ (ModuleCat.{v} R) AddCommGrp.{v}) :=
  ModuleCat.forget₂ReflectsLimitsOfSize.{v, v}

end ReflectsLimits

end ModuleCat
