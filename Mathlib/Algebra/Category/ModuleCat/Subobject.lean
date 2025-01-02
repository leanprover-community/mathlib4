/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Subobjects in the category of `R`-modules

We construct an explicit order isomorphism between the categorical subobjects of an `R`-module `M`
and its submodules. This immediately implies that the category of `R`-modules is well-powered.

-/


open CategoryTheory

open CategoryTheory.Subobject

open CategoryTheory.Limits

open ModuleCat

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)

/-- The categorical subobjects of a module `M` are in one-to-one correspondence with its
    submodules. -/
noncomputable def subobjectModule : Subobject M ≃o Submodule R M :=
  OrderIso.symm
    { invFun := fun S => LinearMap.range S.arrow.hom
      toFun := fun N => Subobject.mk (ofHom N.subtype)
      right_inv := fun S => Eq.symm (by
        fapply eq_mk_of_comm
        · apply LinearEquiv.toModuleIso
          apply LinearEquiv.ofBijective (LinearMap.codRestrict
            (LinearMap.range S.arrow.hom) S.arrow.hom _)
          constructor
          · simp [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict]
            rw [ker_eq_bot_of_mono]
          · rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
              Submodule.comap_subtype_self]
            exact LinearMap.mem_range_self _
        · ext x
          rfl)
      left_inv := fun N => by
        convert congr_arg LinearMap.range (ModuleCat.hom_ext_iff.mp
            (underlyingIso_arrow (ofHom N.subtype))) using 1
        · have :
            -- Porting note: added the `.toLinearEquiv.toLinearMap`
            (underlyingIso (ofHom N.subtype)).inv =
              ofHom (underlyingIso (ofHom N.subtype)).symm.toLinearEquiv.toLinearMap := by
              ext x
              rfl
          rw [this, hom_comp, LinearEquiv.range_comp]
        · exact (Submodule.range_subtype _).symm
      map_rel_iff' := fun {S T} => by
        refine ⟨fun h => ?_, fun h => mk_le_mk_of_comm (↟(Submodule.inclusion h)) rfl⟩
        convert LinearMap.range_comp_le_range (ofMkLEMk _ _ h).hom (ofHom T.subtype).hom
        · rw [← hom_comp, ofMkLEMk_comp]
          exact (Submodule.range_subtype _).symm
        · exact (Submodule.range_subtype _).symm }

instance wellPowered_moduleCat : WellPowered.{v} (ModuleCat.{v} R) :=
  ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩

attribute [local instance] hasKernels_moduleCat

/-- Bundle an element `m : M` such that `f m = 0` as a term of `kernelSubobject f`. -/
noncomputable def toKernelSubobject {M N : ModuleCat.{v} R} {f : M ⟶ N} :
    LinearMap.ker f.hom →ₗ[R] kernelSubobject f :=
  (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv.hom

@[simp]
theorem toKernelSubobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f.hom) :
    (kernelSubobject f).arrow (toKernelSubobject x) = x.1 := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/pull/10959): the whole proof was just `simp [toKernelSubobject]`.
  suffices ((arrow ((kernelSubobject f))) ∘ (kernelSubobjectIso f ≪≫ kernelIsoKer f).inv) x = x by
    convert this
  rw [Iso.trans_inv, ← LinearMap.coe_comp, ← hom_comp, Category.assoc]
  simp only [Category.assoc, kernelSubobject_arrow', kernelIsoKer_inv_kernel_ι]
  aesop_cat

/-- An extensionality lemma showing that two elements of a cokernel by an image
are equal if they differ by an element of the image.

The application is for homology:
two elements in homology are equal if they differ by a boundary.
-/
-- Porting note (https://github.com/leanprover-community/mathlib4/pull/11215): TODO compiler complains that this is marked with `@[ext]`.
-- Should this be changed?
-- @[ext] this is no longer an ext lemma under the current interpretation see eg
-- the conversation beginning at
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/
-- Goal.20state.20not.20updating.2C.20bugs.2C.20etc.2E/near/338456803
theorem cokernel_π_imageSubobject_ext {L M N : ModuleCat.{v} R} (f : L ⟶ M) [HasImage f]
    (g : (imageSubobject f : ModuleCat.{v} R) ⟶ N) [HasCokernel g] {x y : N} (l : L)
    (w : x = y + g (factorThruImageSubobject f l)) : cokernel.π g x = cokernel.π g y := by
  subst w
  -- Porting note (https://github.com/leanprover-community/mathlib4/pull/10959): The proof from here used to just be `simp`.
  simp only [map_add, add_right_eq_self]
  -- TODO: add a `@[simp]` lemma along the lines of:
  -- ```
  -- lemma ModuleCat.Hom.cokernel_condition : (cokernel.π g).hom (g.hom x) = 0
  -- ```
  -- ideally generated for all concrete categories (using a metaprogram like `@[elementwise]`?).
  -- See also: https://github.com/leanprover-community/mathlib4/pull/19511#discussion_r1867083077
  change ((factorThruImageSubobject f) ≫ g ≫ (cokernel.π g)).hom l = 0
  simp

end ModuleCat
