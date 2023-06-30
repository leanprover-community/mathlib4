import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

open CategoryTheory Limits WalkingParallelPair

universe u

namespace AddCommGroupCat

variable {M N : AddCommGroupCat.{u}} (f : M ⟶ N)

instance : HasZeroMorphisms AddCommGroupCat := HasZeroMorphisms.mk

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  KernelFork.ofι (Z := of f.ker) (f.ker.subtype : of f.ker ⟶ M) <| ext fun x =>
    Subtype.casesOn x fun _ hx => hx

instance : AddSubmonoidClass (AddSubgroup M) ((parallelPair f 0).obj WalkingParallelPair.zero) where
  add_mem := fun s {_ _} => AddSubgroup.add_mem s
  zero_mem := AddSubgroup.zero_mem

/-- The kernel of a group homomorphism is a kernel in the categorical sense. -/
def kernelIsLimit : IsLimit <| kernelCone f :=
  Fork.IsLimit.mk _
    (fun s => AddMonoidHom.codRestrict (Fork.ι s) _ <| fun c => (AddMonoidHom.mem_ker _).2 <| by
      rw [← @Function.comp_apply _ _ _ f _ _, ← coe_comp, Fork.condition]; rfl)
    (fun _ => rfl)
    (fun _ _ h => ext $ fun x => Subtype.ext_iff_val.2 $ FunLike.congr_fun h x)

/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (Z := of $ N ⧸ f.range) (QuotientAddGroup.mk' f.range) <| ext fun x =>
    (QuotientAddGroup.eq_zero_iff _).mpr ⟨x, rfl⟩

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernelIsColimit : IsColimit <| cokernelCocone f :=
  Cofork.IsColimit.mk _
    (fun s : Cofork f 0 => QuotientAddGroup.lift _ s.π $ by
      rintro _ ⟨x, rfl⟩
      have := FunLike.congr_fun s.condition
      simpa only [comp_apply, zero_apply, map_zero] using this)
    (fun s => by
      ext
      simp only [comp_apply]
      rfl)
    (fun s m h => by
      let g : N ⟶ (of $ N ⧸ f.range) := QuotientAddGroup.mk' f.range
      haveI : epi g := (epi_iff_range_eq_top _).mpr _
      swap
      · ext ⟨x⟩
        simp only [AddMonoidHom.mem_range, QuotientAddGroup.mk'_apply,
          add_subgroup.mem_top, iff_true]
        exact ⟨x, rfl⟩
      apply (cancel_epi g).1
      convert h
      ext
      rfl)

/-
-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
-- TODO: the next two already exist: add `elementwise` to those lemmas in mathlib
@[simp, elementwise] lemma kernel_iso_ker_inv_kernel_ι :
  (kernel_iso_ker f).inv ≫ kernel.ι f = f.ker.subtype :=
kernel_iso_ker_inv_comp_ι _
@[simp, elementwise] lemma kernel_iso_ker_hom_ker_subtype :
  (kernel_iso_ker f).hom ≫ f.ker.subtype = kernel.ι f :=
kernel_iso_ker_hom_comp_subtype _
/--
The categorical cokernel of a morphism in `Module`
agrees with the usual module-theoretical quotient.
-/
noncomputable def cokernel_iso_range_quotient : cokernel f ≅ of (N ⧸ f.range) :=
colimit.iso_colimit_cocone ⟨_, cokernel_is_colimit f⟩
-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[simp, elementwise] lemma cokernel_π_cokernel_iso_range_quotient_hom :
  cokernel.π f ≫ (cokernel_iso_range_quotient f).hom = quotient_add_group.mk' f.range :=
by { convert colimit.iso_colimit_cocone_ι_hom _ _; refl, }
@[simp, elementwise] lemma range_mkq_cokernel_iso_range_quotient_inv :
  (by exact quotient_add_group.mk' f.range : _) ≫ (cokernel_iso_range_quotient f).inv = cokernel.π f :=
by { convert colimit.iso_colimit_cocone_ι_inv ⟨_, cokernel_is_colimit f⟩ _; refl, }
-/

end AddCommGroupCat
