
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Category.GroupCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.WalkingParallelPair

universe u

namespace AddCommGroupCat

variable {M N : AddCommGroupCat.{u}} (f : M ⟶ N)

instance : HasZeroMorphisms AddCommGroupCat := by refine HasZeroMorphisms.mk


#check @KernelFork.ofι AddCommGroupCat _ _ M N f

/-- The kernel cone induced by the concrete kernel. -/
def kernelCone : KernelFork f :=
  @KernelFork.ofι AddCommGroupCat _ _ M N f (of f.ker) (f.ker.subtype : of f.ker ⟶ M)
   <| by
   ext x
   simp
   rcases x with ⟨x, hx⟩
   exact hx
   --assumption


instance : AddSubmonoidClass (AddSubgroup M) ((parallelPair f 0).obj WalkingParallelPair.zero) :=
by sorry

/-- The kernel of a linear map is a kernel in the categorical sense. -/
def kernel_is_limit : IsLimit (kernelCone f) :=
Fork.IsLimit.mk _
    (fun s : Fork f 0 =>
      AddMonoidHom.codRestrict  (Fork.ι s) (f.ker) <| fun c =>
        (AddMonoidHom.mem_ker _).2 <| by
          rw [← @Function.comp_apply _ _ _ f (Fork.ι s) c, ← coe_comp, Fork.condition]
          --rw [HasZeroMorphisms.comp_zero (Fork.ι s) N]
          rfl)
  (fun s : Fork f 0 => AddMonoidHom.codRestrict (Fork.ι s) f.ker <|
    fun c => (AddMonoidHom.mem_ker _).2 <|
    by
      rw [←@Function.comp_apply _ _ _ f s.ι c, ←coe_comp, Fork.condition]
      --rw [HasZeroMorphisms.comp_zero (Fork.ι s) N]
      rfl )
  (fun s => by
    ext
    simp only [comp_apply, AddMonoidHom.codRestrict_apply]
    rfl )
  (fun s m h => AddMonoidHom.ext $ fun x => Subtype.ext_iff_val.2 $
    have h₁ : (m ≫ (kernel_cone f).π.app zero).to_fun = (s.π.app zero).to_fun := by
      congr
      exact h
    by convert @congr_fun _ _ _ _ h₁ x )

/-
/-- The cokernel cocone induced by the projection onto the quotient. -/
def cokernel_cocone : cokernel_cofork f :=
@cokernel_cofork.of_π AddCommGroup _ _ M N f (of $ N ⧸ f.range) (quotient_add_group.mk' f.range) $
by { ext1, simp only [comp_apply, quotient_add_group.mk'_apply, zero_apply,
  quotient_add_group.eq_zero_iff, add_monoid_hom.mem_range, exists_apply_eq_apply], }

/-- The projection onto the quotient is a cokernel in the categorical sense. -/
def cokernel_is_colimit : is_colimit (cokernel_cocone f) :=
cofork.is_colimit.mk _
  (λ s : cofork f 0, quotient_add_group.lift _ s.π $
  by { rintro _ ⟨x, rfl⟩, have := add_monoid_hom.congr_fun s.condition x,
    simpa only [comp_apply, zero_apply, map_zero] using this, })
  (λ s, by { ext, simp only [comp_apply], refl })
  (λ s m h,
  begin
    let g : N ⟶ (of $ N ⧸ f.range) := (quotient_add_group.mk' f.range),
    haveI : epi g := (epi_iff_range_eq_top _).mpr _,
    swap, { ext ⟨x⟩, simp only [add_monoid_hom.mem_range, quotient_add_group.mk'_apply,
      add_subgroup.mem_top, iff_true], exact ⟨x, rfl⟩ },
    apply (cancel_epi g).1,
    convert h,
    ext, refl,
  end)

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
