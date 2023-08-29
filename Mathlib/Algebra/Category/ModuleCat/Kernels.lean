/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

#align_import algebra.category.Module.kernels from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/

set_option linter.uppercaseLean3 false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

section

variable {M N : ModuleCat.{v} R} (f : M ⟶ N)

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  -- Porting note: previously proven by tidy
  KernelFork.ofι (asHom f.ker.subtype) <| by ext x; cases x; assumption
                                             -- ⊢ ↑(↟(Submodule.subtype (LinearMap.ker f)) ≫ f) x = ↑0 x
                                                    -- ⊢ ↑(↟(Submodule.subtype (LinearMap.ker f)) ≫ f) { val := val✝, property := pro …
                                                             -- 🎉 no goals
#align Module.kernel_cone ModuleCat.kernelCone

/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s =>
    -- Porting note: broken dot notation on LinearMap.ker
      LinearMap.codRestrict (LinearMap.ker f) (Fork.ι s) fun c =>
        LinearMap.mem_ker.2 <| by
          rw [← @Function.comp_apply _ _ _ f (Fork.ι s) c, ← coe_comp, Fork.condition,
            HasZeroMorphisms.comp_zero (Fork.ι s) N]
          rfl)
          -- 🎉 no goals
    (fun s => LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
    LinearMap.ext fun x => Subtype.ext_iff_val.2 (by simp [← h]; rfl)
                                                     -- ⊢ ↑m x = ↑(LinearMap.codRestrict (LinearMap.ker f) (m ≫ Fork.ι (kernelCone f)) …
                                                                 -- 🎉 no goals
#align Module.kernel_is_limit ModuleCat.kernelIsLimit

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (asHom f.range.mkQ) <| LinearMap.range_mkQ_comp _
#align Module.cokernel_cocone ModuleCat.cokernelCocone

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s =>
      f.range.liftQ (Cofork.π s) <| LinearMap.range_le_ker_iff.2 <| CokernelCofork.condition s)
    (fun s => f.range.liftQ_mkQ (Cofork.π s) _) fun s m h => by
    -- Porting note: broken dot notation
    haveI : Epi (asHom (LinearMap.range f).mkQ) :=
      (epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)
    -- Porting note: broken dot notation
    apply (cancel_epi (asHom (LinearMap.range f).mkQ)).1
    -- ⊢ ↟(Submodule.mkQ (LinearMap.range f)) ≫ m = ↟(Submodule.mkQ (LinearMap.range  …
    convert h
    -- 🎉 no goals
    -- Porting note : no longer necessary
    -- exact Submodule.liftQ_mkQ _ _ _
#align Module.cokernel_is_colimit ModuleCat.cokernelIsColimit

end

/-- The category of R-modules has kernels, given by the inclusion of the kernel submodule. -/
theorem hasKernels_moduleCat : HasKernels (ModuleCat R) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩
#align Module.has_kernels_Module ModuleCat.hasKernels_moduleCat

/-- The category of R-modules has cokernels, given by the projection onto the quotient. -/
theorem hasCokernels_moduleCat : HasCokernels (ModuleCat R) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩
#align Module.has_cokernels_Module ModuleCat.hasCokernels_moduleCat

open ModuleCat

attribute [local instance] hasKernels_moduleCat

attribute [local instance] hasCokernels_moduleCat

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

/-- The categorical kernel of a morphism in `ModuleCat`
agrees with the usual module-theoretical kernel.
-/
noncomputable def kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    -- Porting note: broken dot notation
    kernel f ≅ ModuleCat.of R (LinearMap.ker f) :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩
#align Module.kernel_iso_ker ModuleCat.kernelIsoKer

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
    -- Porting note: broken dot notation
theorem kernelIsoKer_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f =
    (LinearMap.ker f).subtype :=
  limit.isoLimitCone_inv_π _ _
#align Module.kernel_iso_ker_inv_kernel_ι ModuleCat.kernelIsoKer_inv_kernel_ι

@[simp, elementwise]
theorem kernelIsoKer_hom_ker_subtype :
    -- Porting note: broken dot notation
    (kernelIsoKer f).hom ≫ (LinearMap.ker f).subtype = kernel.ι f :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero
#align Module.kernel_iso_ker_hom_ker_subtype ModuleCat.kernelIsoKer_hom_ker_subtype

/-- The categorical cokernel of a morphism in `ModuleCat`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernelIsoRangeQuotient {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    -- Porting note: broken dot notation
    cokernel f ≅ ModuleCat.of R (H ⧸ LinearMap.range f) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩
#align Module.cokernel_iso_range_quotient ModuleCat.cokernelIsoRangeQuotient

-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[simp, elementwise]
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = f.range.mkQ := by
  -- Porting note: needs help with F but got rid of rfl after
  convert colimit.isoColimitCocone_ι_hom (F := parallelPair f 0) _ _
  -- 🎉 no goals
#align Module.cokernel_π_cokernel_iso_range_quotient_hom ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom

@[simp, elementwise]
theorem range_mkQ_cokernelIsoRangeQuotient_inv :
    ↿f.range.mkQ ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f :=
  colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one
#align Module.range_mkq_cokernel_iso_range_quotient_inv ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv

theorem cokernel_π_ext {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m) :
    cokernel.π f x = cokernel.π f y := by
  subst w
  -- ⊢ ↑(cokernel.π f) (y + ↑f m) = ↑(cokernel.π f) y
  simpa only [map_add, add_right_eq_self] using cokernel.condition_apply f m
  -- 🎉 no goals
#align Module.cokernel_π_ext ModuleCat.cokernel_π_ext

end ModuleCat
