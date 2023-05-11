/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Module.kernels
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/


open CategoryTheory

open CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

section

variable {M N : ModuleCat.{v} R} (f : M ⟶ N)

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  KernelFork.ofι (asHom f.ker.Subtype) <| by tidy
#align Module.kernel_cone ModuleCat.kernelCone

/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s =>
      LinearMap.codRestrict f.ker (Fork.ι s) fun c =>
        LinearMap.mem_ker.2 <|
          by
          rw [← @Function.comp_apply _ _ _ f (fork.ι s) c, ← coe_comp, fork.condition,
            has_zero_morphisms.comp_zero (fork.ι s) N]
          rfl)
    (fun s => LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
    LinearMap.ext fun x => Subtype.ext_iff_val.2 (by simpa [← h] )
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
    (fun s => f.range.liftQ_mkQ (Cofork.π s) _) fun s m h =>
    by
    haveI : epi (as_hom f.range.mkq) := (epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)
    apply (cancel_epi (as_hom f.range.mkq)).1
    convert h
    exact Submodule.liftQ_mkQ _ _ _
#align Module.cokernel_is_colimit ModuleCat.cokernelIsColimit

end

/-- The category of R-modules has kernels, given by the inclusion of the kernel submodule. -/
theorem hasKernels_moduleCat : HasKernels (ModuleCat R) :=
  ⟨fun X Y f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩
#align Module.has_kernels_Module ModuleCat.hasKernels_moduleCat

/-- The category or R-modules has cokernels, given by the projection onto the quotient. -/
theorem hasCokernels_moduleCat : HasCokernels (ModuleCat R) :=
  ⟨fun X Y f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩
#align Module.has_cokernels_Module ModuleCat.hasCokernels_moduleCat

open ModuleCat

attribute [local instance] has_kernels_Module

attribute [local instance] has_cokernels_Module

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

/-- The categorical kernel of a morphism in `Module`
agrees with the usual module-theoretical kernel.
-/
noncomputable def kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    kernel f ≅ ModuleCat.of R f.ker :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩
#align Module.kernel_iso_ker ModuleCat.kernelIsoKer

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
theorem kernelIsoKer_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f = f.ker.Subtype :=
  limit.isoLimitCone_inv_π _ _
#align Module.kernel_iso_ker_inv_kernel_ι ModuleCat.kernelIsoKer_inv_kernel_ι

@[simp, elementwise]
theorem kernelIsoKer_hom_ker_subtype : (kernelIsoKer f).hom ≫ f.ker.Subtype = kernel.ι f :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero
#align Module.kernel_iso_ker_hom_ker_subtype ModuleCat.kernelIsoKer_hom_ker_subtype

/-- The categorical cokernel of a morphism in `Module`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernelIsoRangeQuotient {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    cokernel f ≅ ModuleCat.of R (H ⧸ f.range) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩
#align Module.cokernel_iso_range_quotient ModuleCat.cokernelIsoRangeQuotient

-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[simp, elementwise]
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = f.range.mkQ := by
  convert colimit.iso_colimit_cocone_ι_hom _ _ <;> rfl
#align Module.cokernel_π_cokernel_iso_range_quotient_hom ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom

@[simp, elementwise]
theorem range_mkQ_cokernelIsoRangeQuotient_inv :
    ↿f.range.mkQ ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f := by
  convert colimit.iso_colimit_cocone_ι_inv ⟨_, cokernel_is_colimit f⟩ _ <;> rfl
#align Module.range_mkq_cokernel_iso_range_quotient_inv ModuleCat.range_mkQ_cokernelIsoRangeQuotient_inv

theorem cokernel_π_ext {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m) :
    cokernel.π f x = cokernel.π f y := by
  subst w
  simp
#align Module.cokernel_π_ext ModuleCat.cokernel_π_ext

end ModuleCat

