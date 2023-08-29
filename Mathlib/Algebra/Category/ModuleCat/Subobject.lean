/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Subobject.WellPowered
import Mathlib.CategoryTheory.Subobject.Limits

#align_import algebra.category.Module.subobject from "leanprover-community/mathlib"@"6d584f1709bedbed9175bd9350df46599bdd7213"

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
set_option linter.uppercaseLean3 false -- `Module`

variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)

/-- The categorical subobjects of a module `M` are in one-to-one correspondence with its
    submodules.-/
noncomputable def subobjectModule : Subobject M ≃o Submodule R M :=
  OrderIso.symm
    { invFun := fun S => LinearMap.range S.arrow
      toFun := fun N => Subobject.mk (↾N.subtype)
      right_inv := fun S => Eq.symm (by
        fapply eq_mk_of_comm
        -- ⊢ underlying.obj S ≅ of R { x // x ∈ (fun S => LinearMap.range (arrow S)) S }
        · apply LinearEquiv.toModuleIso'Left
          -- ⊢ ↑(underlying.obj S) ≃ₗ[R] { x // x ∈ (fun S => LinearMap.range (arrow S)) S }
          apply LinearEquiv.ofBijective (LinearMap.codRestrict (LinearMap.range S.arrow) S.arrow _)
          -- ⊢ Function.Bijective ↑(LinearMap.codRestrict (LinearMap.range (arrow S)) (arro …
          constructor
          · simp [← LinearMap.ker_eq_bot, LinearMap.ker_codRestrict]
            -- ⊢ LinearMap.ker (arrow S) = ⊥
            rw [ker_eq_bot_of_mono]
            -- 🎉 no goals
          · rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, Submodule.comap_subtype_self]
            -- ⊢ ∀ (c : ↑(underlying.obj S)), ↑(arrow S) c ∈ LinearMap.range (arrow S)
            exact LinearMap.mem_range_self _
            -- 🎉 no goals
        · apply LinearMap.ext
          -- ⊢ ∀ (x : ↑(underlying.obj S)), ↑((LinearEquiv.toModuleIso'Left (LinearEquiv.of …
          intro x
          -- ⊢ ↑((LinearEquiv.toModuleIso'Left (LinearEquiv.ofBijective (LinearMap.codRestr …
          rfl)
          -- 🎉 no goals
      left_inv := fun N => by
        -- Porting note: The type of `↾N.subtype` was ambiguous. Not entirely sure, I made the right
        -- choice here
          -- 🎉 no goals
        convert congr_arg LinearMap.range
          -- 🎉 no goals
            (underlyingIso_arrow (↾N.subtype : of R { x // x ∈ N } ⟶ M)) using 1
        · have :
            -- Porting note: added the `.toLinearEquiv.toLinearMap`
            (underlyingIso (↾N.subtype : of R _ ⟶ M)).inv =
              (underlyingIso (↾N.subtype : of R _ ⟶ M)).symm.toLinearEquiv.toLinearMap := by
              apply LinearMap.ext
              intro x
              rfl
          rw [this, comp_def, LinearEquiv.range_comp]
        · exact (Submodule.range_subtype _).symm
      map_rel_iff' := fun {S T} => by
        refine' ⟨fun h => _, fun h => mk_le_mk_of_comm (↟(Submodule.ofLe h)) rfl⟩
        -- ⊢ S ≤ T
        convert LinearMap.range_comp_le_range (ofMkLEMk _ _ h) (↾T.subtype)
        -- ⊢ S = LinearMap.range (LinearMap.comp (↾(Submodule.subtype T)) (ofMkLEMk (↾(Su …
        · simpa only [← comp_def, ofMkLEMk_comp] using (Submodule.range_subtype _).symm
          -- 🎉 no goals
        · exact (Submodule.range_subtype _).symm }
          -- 🎉 no goals
#align Module.subobject_Module ModuleCat.subobjectModule

instance wellPowered_moduleCat : WellPowered (ModuleCat.{v} R) :=
  ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩
#align Module.well_powered_Module ModuleCat.wellPowered_moduleCat

attribute [local instance] hasKernels_moduleCat

/-- Bundle an element `m : M` such that `f m = 0` as a term of `kernelSubobject f`. -/
noncomputable def toKernelSubobject {M N : ModuleCat.{v} R} {f : M ⟶ N} :
    LinearMap.ker f →ₗ[R] kernelSubobject f :=
  (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv
#align Module.to_kernel_subobject ModuleCat.toKernelSubobject

@[simp]
theorem toKernelSubobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f) :
    (kernelSubobject f).arrow (toKernelSubobject x) = x.1 := by
  -- Porting note: The whole proof was just `simp [toKernelSubobject]`.
  suffices ((arrow ((kernelSubobject f))) ∘ (kernelSubobjectIso f ≪≫ kernelIsoKer f).inv) x = x by
    convert this
  rw [Iso.trans_inv, ← coe_comp, Category.assoc]
  -- ⊢ ↑((kernelIsoKer f).inv ≫ (kernelSubobjectIso f).inv ≫ arrow (kernelSubobject …
  simp only [Category.assoc, kernelSubobject_arrow', kernelIsoKer_inv_kernel_ι]
  -- ⊢ ↑(Submodule.subtype (LinearMap.ker f)) x = ↑x
  aesop_cat
  -- 🎉 no goals
#align Module.to_kernel_subobject_arrow ModuleCat.toKernelSubobject_arrow

/-- An extensionality lemma showing that two elements of a cokernel by an image
are equal if they differ by an element of the image.

The application is for homology:
two elements in homology are equal if they differ by a boundary.
-/
-- Porting note: TODO compiler complains that this is marked with `@[ext]`. Should this be changed?
-- @[ext] this is no longer an ext lemma under the current interpretation see eg
-- the conversation beginning at
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/
-- Goal.20state.20not.20updating.2C.20bugs.2C.20etc.2E/near/338456803
theorem cokernel_π_imageSubobject_ext {L M N : ModuleCat.{v} R} (f : L ⟶ M) [HasImage f]
    (g : (imageSubobject f : ModuleCat.{v} R) ⟶ N) [HasCokernel g] {x y : N} (l : L)
    (w : x = y + g (factorThruImageSubobject f l)) : cokernel.π g x = cokernel.π g y := by
  subst w
  -- ⊢ ↑(cokernel.π g) (y + ↑g (↑(factorThruImageSubobject f) l)) = ↑(cokernel.π g) y
  -- Porting note: The proof from here used to just be `simp`.
  simp only [map_add, add_right_eq_self]
  -- ⊢ ↑(cokernel.π g) (↑g (↑(factorThruImageSubobject f) l)) = 0
  change ((cokernel.π g) ∘ (g) ∘ (factorThruImageSubobject f)) l = 0
  -- ⊢ (↑(cokernel.π g) ∘ ↑g ∘ ↑(factorThruImageSubobject f)) l = 0
  rw [← coe_comp, ← coe_comp, Category.assoc]
  -- ⊢ ↑(factorThruImageSubobject f ≫ g ≫ cokernel.π g) l = 0
  simp only [cokernel.condition, comp_zero]
  -- ⊢ ↑0 l = 0
  rfl
  -- 🎉 no goals
#align Module.cokernel_π_image_subobject_ext ModuleCat.cokernel_π_imageSubobject_ext

end ModuleCat
