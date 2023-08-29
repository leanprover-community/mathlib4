/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Homology.ImageToKernel

#align_import algebra.homology.exact from "leanprover-community/mathlib"@"3feb151caefe53df080ca6ca67a0c6685cfd1b82"

/-!
# Exact sequences

In a category with zero morphisms, images, and equalizers we say that `f : A ⟶ B` and `g : B ⟶ C`
are exact if `f ≫ g = 0` and the natural map `image f ⟶ kernel g` is an epimorphism.

In any preadditive category this is equivalent to the homology at `B` vanishing.

However in general it is weaker than other reasonable definitions of exactness,
particularly that
1. the inclusion map `image.ι f` is a kernel of `g` or
2. `image f ⟶ kernel g` is an isomorphism or
3. `imageSubobject f = kernelSubobject f`.
However when the category is abelian, these all become equivalent;
these results are found in `CategoryTheory/Abelian/Exact.lean`.

# Main results
* Suppose that cokernels exist and that `f` and `g` are exact.
  If `s` is any kernel fork over `g` and `t` is any cokernel cofork over `f`,
  then `Fork.ι s ≫ Cofork.π t = 0`.
* Precomposing the first morphism with an epimorphism retains exactness.
  Postcomposing the second morphism with a monomorphism retains exactness.
* If `f` and `g` are exact and `i` is an isomorphism,
  then `f ≫ i.hom` and `i.inv ≫ g` are also exact.

# Future work
* Short exact sequences, split exact sequences, the splitting lemma (maybe only for abelian
  categories?)
* Two adjacent maps in a chain complex are exact iff the homology vanishes

-/


universe v v₂ u u₂

open CategoryTheory CategoryTheory.Limits

variable {V : Type u} [Category.{v} V]

variable [HasImages V]

namespace CategoryTheory

-- One nice feature of this definition is that we have
-- `Epi f → Exact g h → Exact (f ≫ g) h` and `Exact f g → Mono h → Exact f (g ≫ h)`,
-- which do not necessarily hold in a non-abelian category with the usual definition of `Exact`.
/-- Two morphisms `f : A ⟶ B`, `g : B ⟶ C` are called exact if `w : f ≫ g = 0` and the natural map
`imageToKernel f g w : imageSubobject f ⟶ kernelSubobject g` is an epimorphism.

In any preadditive category, this is equivalent to `w : f ≫ g = 0` and `homology f g w ≅ 0`.

In an abelian category, this is equivalent to `imageToKernel f g w` being an isomorphism,
and hence equivalent to the usual definition,
`imageSubobject f = kernelSubobject g`.
-/
structure Exact [HasZeroMorphisms V] [HasKernels V] {A B C : V} (f : A ⟶ B) (g : B ⟶ C) : Prop where
  w : f ≫ g = 0
  epi : Epi (imageToKernel f g w)
#align category_theory.exact CategoryTheory.Exact

-- porting note: it seems it no longer works in Lean4, so that some `haveI` have been added below
-- This works as an instance even though `Exact` itself is not a class, as long as the goal is
-- literally of the form `Epi (imageToKernel f g h.w)` (where `h : Exact f g`). If the proof of
-- `f ≫ g = 0` looks different, we are out of luck and have to add the instance by hand.
attribute [instance] Exact.epi

attribute [reassoc] Exact.w

section

variable [HasZeroObject V] [Preadditive V] [HasKernels V] [HasCokernels V]

open ZeroObject

/-- In any preadditive category,
composable morphisms `f g` are exact iff they compose to zero and the homology vanishes.
-/
theorem Preadditive.exact_iff_homology_zero {A B C : V} (f : A ⟶ B) (g : B ⟶ C) :
    Exact f g ↔ ∃ w : f ≫ g = 0, Nonempty (homology f g w ≅ 0) :=
  ⟨fun h => ⟨h.w, ⟨by
    haveI := h.epi
    -- ⊢ homology f g (_ : f ≫ g = 0) ≅ 0
    exact cokernel.ofEpi _⟩⟩,
    -- 🎉 no goals
   fun h => by
    obtain ⟨w, ⟨i⟩⟩ := h
    -- ⊢ Exact f g
    exact ⟨w, Preadditive.epi_of_cokernel_zero ((cancel_mono i.hom).mp (by ext))⟩⟩
    -- 🎉 no goals
#align category_theory.preadditive.exact_iff_homology_zero CategoryTheory.Preadditive.exact_iff_homology_zero

theorem Preadditive.exact_of_iso_of_exact {A₁ B₁ C₁ A₂ B₂ C₂ : V} (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)
    (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (α : Arrow.mk f₁ ≅ Arrow.mk f₂) (β : Arrow.mk g₁ ≅ Arrow.mk g₂)
    (p : α.hom.right = β.hom.left) (h : Exact f₁ g₁) : Exact f₂ g₂ := by
  rw [Preadditive.exact_iff_homology_zero] at h ⊢
  -- ⊢ ∃ w, Nonempty (homology f₂ g₂ w ≅ 0)
  rcases h with ⟨w₁, ⟨i⟩⟩
  -- ⊢ ∃ w, Nonempty (homology f₂ g₂ w ≅ 0)
  suffices w₂ : f₂ ≫ g₂ = 0; exact ⟨w₂, ⟨(homology.mapIso w₁ w₂ α β p).symm.trans i⟩⟩
  -- ⊢ ∃ w, Nonempty (homology f₂ g₂ w ≅ 0)
                             -- ⊢ f₂ ≫ g₂ = 0
  rw [← cancel_epi α.hom.left, ← cancel_mono β.inv.right, comp_zero, zero_comp, ← w₁]
  -- ⊢ (α.hom.left ≫ f₂ ≫ g₂) ≫ β.inv.right = f₁ ≫ g₁
  have eq₁ := β.inv.w
  -- ⊢ (α.hom.left ≫ f₂ ≫ g₂) ≫ β.inv.right = f₁ ≫ g₁
  have eq₂ := α.hom.w
  -- ⊢ (α.hom.left ≫ f₂ ≫ g₂) ≫ β.inv.right = f₁ ≫ g₁
  dsimp at eq₁ eq₂
  -- ⊢ (α.hom.left ≫ f₂ ≫ g₂) ≫ β.inv.right = f₁ ≫ g₁
  simp only [Category.assoc, Category.assoc, ← eq₁, reassoc_of% eq₂, p,
    ← reassoc_of% (Arrow.comp_left β.hom β.inv), β.hom_inv_id, Arrow.id_left, Category.id_comp]
#align category_theory.preadditive.exact_of_iso_of_exact CategoryTheory.Preadditive.exact_of_iso_of_exact

/-- A reformulation of `Preadditive.exact_of_iso_of_exact` that does not involve the arrow
category. -/
theorem Preadditive.exact_of_iso_of_exact' {A₁ B₁ C₁ A₂ B₂ C₂ : V} (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)
    (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (α : A₁ ≅ A₂) (β : B₁ ≅ B₂) (γ : C₁ ≅ C₂)
    (hsq₁ : α.hom ≫ f₂ = f₁ ≫ β.hom) (hsq₂ : β.hom ≫ g₂ = g₁ ≫ γ.hom) (h : Exact f₁ g₁) :
    Exact f₂ g₂ :=
  Preadditive.exact_of_iso_of_exact f₁ g₁ f₂ g₂ (Arrow.isoMk α β hsq₁) (Arrow.isoMk β γ hsq₂) rfl h
#align category_theory.preadditive.exact_of_iso_of_exact' CategoryTheory.Preadditive.exact_of_iso_of_exact'

theorem Preadditive.exact_iff_exact_of_iso {A₁ B₁ C₁ A₂ B₂ C₂ : V} (f₁ : A₁ ⟶ B₁) (g₁ : B₁ ⟶ C₁)
    (f₂ : A₂ ⟶ B₂) (g₂ : B₂ ⟶ C₂) (α : Arrow.mk f₁ ≅ Arrow.mk f₂) (β : Arrow.mk g₁ ≅ Arrow.mk g₂)
    (p : α.hom.right = β.hom.left) : Exact f₁ g₁ ↔ Exact f₂ g₂ :=
  ⟨Preadditive.exact_of_iso_of_exact _ _ _ _ _ _ p,
    Preadditive.exact_of_iso_of_exact _ _ _ _ α.symm β.symm
      (by
        rw [← cancel_mono α.hom.right]
        -- ⊢ α.symm.hom.right ≫ α.hom.right = β.symm.hom.left ≫ α.hom.right
        simp only [Iso.symm_hom, ← Arrow.comp_right, α.inv_hom_id]
        -- ⊢ (𝟙 (Arrow.mk f₂)).right = β.inv.left ≫ α.hom.right
        simp only [p, ← Arrow.comp_left, Arrow.id_right, Arrow.id_left, Iso.inv_hom_id]
        -- ⊢ 𝟙 (Arrow.mk f₂).right = 𝟙 (Arrow.mk g₂).left
        rfl)⟩
        -- 🎉 no goals
#align category_theory.preadditive.exact_iff_exact_of_iso CategoryTheory.Preadditive.exact_iff_exact_of_iso

end

section

variable [HasZeroMorphisms V] [HasKernels V]

theorem comp_eq_zero_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
    (p : imageSubobject f = kernelSubobject g) : f ≫ g = 0 := by
  suffices Subobject.arrow (imageSubobject f) ≫ g = 0 by
    rw [← imageSubobject_arrow_comp f, Category.assoc, this, comp_zero]
  rw [p, kernelSubobject_arrow_comp]
  -- 🎉 no goals
#align category_theory.comp_eq_zero_of_image_eq_kernel CategoryTheory.comp_eq_zero_of_image_eq_kernel

theorem imageToKernel_isIso_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
    (p : imageSubobject f = kernelSubobject g) :
    IsIso (imageToKernel f g (comp_eq_zero_of_image_eq_kernel f g p)) := by
  refine' ⟨⟨Subobject.ofLE _ _ p.ge, _⟩⟩
  -- ⊢ imageToKernel f g (_ : f ≫ g = 0) ≫ Subobject.ofLE (kernelSubobject g) (imag …
  dsimp [imageToKernel]
  -- ⊢ Subobject.ofLE (imageSubobject f) (kernelSubobject g) (_ : imageSubobject f  …
  simp only [Subobject.ofLE_comp_ofLE, Subobject.ofLE_refl]
  -- 🎉 no goals
#align category_theory.image_to_kernel_is_iso_of_image_eq_kernel CategoryTheory.imageToKernel_isIso_of_image_eq_kernel

-- We'll prove the converse later, when `V` is abelian.
theorem exact_of_image_eq_kernel {A B C : V} (f : A ⟶ B) (g : B ⟶ C)
    (p : imageSubobject f = kernelSubobject g) : Exact f g :=
  { w := comp_eq_zero_of_image_eq_kernel f g p
    epi := by
      haveI := imageToKernel_isIso_of_image_eq_kernel f g p
      -- ⊢ Epi (imageToKernel f g (_ : f ≫ g = 0))
      infer_instance }
      -- 🎉 no goals
#align category_theory.exact_of_image_eq_kernel CategoryTheory.exact_of_image_eq_kernel

end

variable {A B C D : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}

attribute [local instance] epi_comp

section

variable [HasZeroMorphisms V] [HasEqualizers V]

theorem exact_comp_hom_inv_comp (i : B ≅ D) (h : Exact f g) : Exact (f ≫ i.hom) (i.inv ≫ g) := by
  refine' ⟨by simp [h.w], _⟩
  -- ⊢ Epi (imageToKernel (f ≫ i.hom) (i.inv ≫ g) (_ : (f ≫ i.hom) ≫ i.inv ≫ g = 0))
  rw [imageToKernel_comp_hom_inv_comp]
  -- ⊢ Epi ((imageSubobjectCompIso f i.hom).hom ≫ imageToKernel f g (_ : f ≫ g = 0) …
  haveI := h.epi
  -- ⊢ Epi ((imageSubobjectCompIso f i.hom).hom ≫ imageToKernel f g (_ : f ≫ g = 0) …
  infer_instance
  -- 🎉 no goals
#align category_theory.exact_comp_hom_inv_comp CategoryTheory.exact_comp_hom_inv_comp

theorem exact_comp_inv_hom_comp (i : D ≅ B) (h : Exact f g) : Exact (f ≫ i.inv) (i.hom ≫ g) :=
  exact_comp_hom_inv_comp i.symm h
#align category_theory.exact_comp_inv_hom_comp CategoryTheory.exact_comp_inv_hom_comp

theorem exact_comp_hom_inv_comp_iff (i : B ≅ D) : Exact (f ≫ i.hom) (i.inv ≫ g) ↔ Exact f g :=
  ⟨fun h => by simpa using exact_comp_inv_hom_comp i h, exact_comp_hom_inv_comp i⟩
               -- 🎉 no goals
#align category_theory.exact_comp_hom_inv_comp_iff CategoryTheory.exact_comp_hom_inv_comp_iff

theorem exact_epi_comp (hgh : Exact g h) [Epi f] : Exact (f ≫ g) h := by
  refine' ⟨by simp [hgh.w], _⟩
  -- ⊢ Epi (imageToKernel (f ≫ g) h (_ : (f ≫ g) ≫ h = 0))
  rw [imageToKernel_comp_left]
  -- ⊢ Epi (Subobject.ofLE (imageSubobject (f ≫ g)) (imageSubobject g) (_ : imageSu …
  haveI := hgh.epi
  -- ⊢ Epi (Subobject.ofLE (imageSubobject (f ≫ g)) (imageSubobject g) (_ : imageSu …
  infer_instance
  -- 🎉 no goals
#align category_theory.exact_epi_comp CategoryTheory.exact_epi_comp

@[simp]
theorem exact_iso_comp [IsIso f] : Exact (f ≫ g) h ↔ Exact g h :=
  ⟨fun w => by
    rw [← IsIso.inv_hom_id_assoc f g]
    -- ⊢ Exact (inv f ≫ f ≫ g) h
    exact exact_epi_comp w, fun w => exact_epi_comp w⟩
    -- 🎉 no goals
#align category_theory.exact_iso_comp CategoryTheory.exact_iso_comp

theorem exact_comp_mono (hfg : Exact f g) [Mono h] : Exact f (g ≫ h) := by
  refine' ⟨by simp [hfg.w_assoc], _⟩
  -- ⊢ Epi (imageToKernel f (g ≫ h) (_ : f ≫ g ≫ h = 0))
  rw [imageToKernel_comp_right f g h hfg.w]
  -- ⊢ Epi (imageToKernel f g (_ : f ≫ g = 0) ≫ Subobject.ofLE (kernelSubobject g)  …
  haveI := hfg.epi
  -- ⊢ Epi (imageToKernel f g (_ : f ≫ g = 0) ≫ Subobject.ofLE (kernelSubobject g)  …
  infer_instance
  -- 🎉 no goals
#align category_theory.exact_comp_mono CategoryTheory.exact_comp_mono

/-- The dual of this lemma is only true when `V` is abelian, see `Abelian.exact_epi_comp_iff`. -/
theorem exact_comp_mono_iff [Mono h] : Exact f (g ≫ h) ↔ Exact f g := by
  refine'
    ⟨fun hfg => ⟨zero_of_comp_mono h (by rw [Category.assoc, hfg.1]), _⟩, fun h =>
      exact_comp_mono h⟩
  rw [← (Iso.eq_comp_inv _).1 (imageToKernel_comp_mono _ _ h hfg.1)]
  -- ⊢ Epi (imageToKernel f (g ≫ h) (_ : f ≫ g ≫ h = 0) ≫ (Subobject.isoOfEq (kerne …
  haveI := hfg.2; infer_instance
  -- ⊢ Epi (imageToKernel f (g ≫ h) (_ : f ≫ g ≫ h = 0) ≫ (Subobject.isoOfEq (kerne …
                  -- 🎉 no goals
#align category_theory.exact_comp_mono_iff CategoryTheory.exact_comp_mono_iff

@[simp]
theorem exact_comp_iso [IsIso h] : Exact f (g ≫ h) ↔ Exact f g :=
  exact_comp_mono_iff
#align category_theory.exact_comp_iso CategoryTheory.exact_comp_iso

theorem exact_kernelSubobject_arrow : Exact (kernelSubobject f).arrow f := by
  refine' ⟨by simp, _⟩
  -- ⊢ Epi (imageToKernel (Subobject.arrow (kernelSubobject f)) f (_ : Subobject.ar …
  refine' @IsIso.epi_of_iso _ _ _ _ _ ?_
  -- ⊢ IsIso (imageToKernel (Subobject.arrow (kernelSubobject f)) f (_ : Subobject. …
  exact ⟨⟨factorThruImageSubobject _, by aesop_cat, by aesop_cat⟩⟩
  -- 🎉 no goals
#align category_theory.exact_kernel_subobject_arrow CategoryTheory.exact_kernelSubobject_arrow

theorem exact_kernel_ι : Exact (kernel.ι f) f := by
  rw [← kernelSubobject_arrow', exact_iso_comp]
  -- ⊢ Exact (Subobject.arrow (kernelSubobject f)) f
  exact exact_kernelSubobject_arrow
  -- 🎉 no goals
#align category_theory.exact_kernel_ι CategoryTheory.exact_kernel_ι

instance Exact.epi_factorThruKernelSubobject (h : Exact f g) :
  Epi (factorThruKernelSubobject g f h.w) := by
  rw [← factorThruImageSubobject_comp_imageToKernel]
  -- ⊢ Epi (factorThruImageSubobject f ≫ imageToKernel f g (_ : f ≫ g = 0))
  haveI := h.epi
  -- ⊢ Epi (factorThruImageSubobject f ≫ imageToKernel f g (_ : f ≫ g = 0))
  apply epi_comp
  -- 🎉 no goals

-- porting note: this can no longer be an instance in Lean4
lemma Exact.epi_kernel_lift (h : Exact f g) : Epi (kernel.lift g f h.w) := by
  rw [← factorThruKernelSubobject_comp_kernelSubobjectIso]
  -- ⊢ Epi (factorThruKernelSubobject g f (_ : f ≫ g = 0) ≫ (kernelSubobjectIso g). …
  haveI := h.epi_factorThruKernelSubobject
  -- ⊢ Epi (factorThruKernelSubobject g f (_ : f ≫ g = 0) ≫ (kernelSubobjectIso g). …
  apply epi_comp
  -- 🎉 no goals

variable (A)

theorem kernelSubobject_arrow_eq_zero_of_exact_zero_left (h : Exact (0 : A ⟶ B) g) :
    (kernelSubobject g).arrow = 0 := by
  haveI := h.epi
  -- ⊢ Subobject.arrow (kernelSubobject g) = 0
  rw [← cancel_epi (imageToKernel (0 : A ⟶ B) g h.w), ←
    cancel_epi (factorThruImageSubobject (0 : A ⟶ B))]
  simp
  -- 🎉 no goals
#align category_theory.kernel_subobject_arrow_eq_zero_of_exact_zero_left CategoryTheory.kernelSubobject_arrow_eq_zero_of_exact_zero_left

theorem kernel_ι_eq_zero_of_exact_zero_left (h : Exact (0 : A ⟶ B) g) : kernel.ι g = 0 := by
  rw [← kernelSubobject_arrow']
  -- ⊢ (kernelSubobjectIso g).inv ≫ Subobject.arrow (kernelSubobject g) = 0
  simp [kernelSubobject_arrow_eq_zero_of_exact_zero_left A h]
  -- 🎉 no goals
#align category_theory.kernel_ι_eq_zero_of_exact_zero_left CategoryTheory.kernel_ι_eq_zero_of_exact_zero_left

theorem exact_zero_left_of_mono [HasZeroObject V] [Mono g] : Exact (0 : A ⟶ B) g :=
  ⟨by simp, imageToKernel_epi_of_zero_of_mono _⟩
      -- 🎉 no goals
#align category_theory.exact_zero_left_of_mono CategoryTheory.exact_zero_left_of_mono

end

section HasCokernels

variable [HasZeroMorphisms V] [HasEqualizers V] [HasCokernels V] (f g)

@[reassoc (attr := simp)]
theorem kernel_comp_cokernel (h : Exact f g) : kernel.ι g ≫ cokernel.π f = 0 := by
  suffices Subobject.arrow (kernelSubobject g) ≫ cokernel.π f = 0 by
    rw [← kernelSubobject_arrow', Category.assoc, this, comp_zero]
  haveI := h.epi
  -- ⊢ Subobject.arrow (kernelSubobject g) ≫ cokernel.π f = 0
  apply zero_of_epi_comp (imageToKernel f g h.w) _
  -- ⊢ imageToKernel f g (_ : f ≫ g = 0) ≫ Subobject.arrow (kernelSubobject g) ≫ co …
  rw [imageToKernel_arrow_assoc, ← imageSubobject_arrow, Category.assoc, ← Iso.eq_inv_comp]
  -- ⊢ image.ι f ≫ cokernel.π f = (imageSubobjectIso f).inv ≫ 0
  aesop_cat
  -- 🎉 no goals
#align category_theory.kernel_comp_cokernel CategoryTheory.kernel_comp_cokernel

theorem comp_eq_zero_of_exact (h : Exact f g) {X Y : V} {ι : X ⟶ B} (hι : ι ≫ g = 0) {π : B ⟶ Y}
    (hπ : f ≫ π = 0) : ι ≫ π = 0 := by
  rw [← kernel.lift_ι _ _ hι, ← cokernel.π_desc _ _ hπ, Category.assoc,
    kernel_comp_cokernel_assoc _ _ h, zero_comp, comp_zero]
#align category_theory.comp_eq_zero_of_exact CategoryTheory.comp_eq_zero_of_exact

@[reassoc (attr := simp)]
theorem fork_ι_comp_cofork_π (h : Exact f g) (s : KernelFork g) (t : CokernelCofork f) :
    Fork.ι s ≫ Cofork.π t = 0 :=
  comp_eq_zero_of_exact f g h (KernelFork.condition s) (CokernelCofork.condition t)
#align category_theory.fork_ι_comp_cofork_π CategoryTheory.fork_ι_comp_cofork_π

end HasCokernels

section

variable [HasZeroObject V]

open ZeroObject

section

variable [HasZeroMorphisms V] [HasKernels V]

theorem exact_of_zero {A C : V} (f : A ⟶ 0) (g : 0 ⟶ C) : Exact f g := by
  obtain rfl : f = 0 := by ext
  -- ⊢ Exact 0 g
  obtain rfl : g = 0 := by ext
  -- ⊢ Exact 0 0
  fconstructor
  -- ⊢ 0 ≫ 0 = 0
  · simp
    -- 🎉 no goals
  · exact imageToKernel_epi_of_zero_of_mono 0
    -- 🎉 no goals
#align category_theory.exact_of_zero CategoryTheory.exact_of_zero

theorem exact_zero_mono {B C : V} (f : B ⟶ C) [Mono f] : Exact (0 : 0 ⟶ B) f :=
  ⟨_, inferInstance⟩
#align category_theory.exact_zero_mono CategoryTheory.exact_zero_mono

theorem exact_epi_zero {A B : V} (f : A ⟶ B) [Epi f] : Exact f (0 : B ⟶ 0) :=
  ⟨_, inferInstance⟩
#align category_theory.exact_epi_zero CategoryTheory.exact_epi_zero

end

section

variable [Preadditive V]

theorem mono_iff_exact_zero_left [HasKernels V] {B C : V} (f : B ⟶ C) :
    Mono f ↔ Exact (0 : 0 ⟶ B) f :=
  ⟨fun h => exact_zero_mono _, fun h =>
    Preadditive.mono_of_kernel_iso_zero
      ((kernelSubobjectIso f).symm ≪≫ isoZeroOfEpiZero (by simpa using h.epi))⟩
                                                           -- 🎉 no goals
#align category_theory.mono_iff_exact_zero_left CategoryTheory.mono_iff_exact_zero_left

theorem epi_iff_exact_zero_right [HasEqualizers V] {A B : V} (f : A ⟶ B) :
    Epi f ↔ Exact f (0 : B ⟶ 0) :=
  ⟨fun h => exact_epi_zero _, fun h => by
    have e₁ := h.epi
    -- ⊢ Epi f
    rw [imageToKernel_zero_right] at e₁
    -- ⊢ Epi f
    have e₂ : Epi (((imageSubobject f).arrow ≫ inv (kernelSubobject 0).arrow) ≫
          (kernelSubobject 0).arrow) := @epi_comp _ _ _ _ _ _ e₁ _ _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id] at e₂
    -- ⊢ Epi f
    rw [← imageSubobject_arrow] at e₂
    -- ⊢ Epi f
    haveI : Epi (image.ι f) := epi_of_epi (imageSubobjectIso f).hom (image.ι f)
    -- ⊢ Epi f
    apply epi_of_epi_image⟩
    -- 🎉 no goals
#align category_theory.epi_iff_exact_zero_right CategoryTheory.epi_iff_exact_zero_right

end

end

namespace Functor

variable [HasZeroMorphisms V] [HasKernels V] {W : Type u₂} [Category.{v₂} W]

variable [HasImages W] [HasZeroMorphisms W] [HasKernels W]

/-- A functor reflects exact sequences if any composable pair of morphisms that is mapped to an
    exact pair is itself exact. -/
class ReflectsExactSequences (F : V ⥤ W) : Prop where
  reflects : ∀ {A B C : V} (f : A ⟶ B) (g : B ⟶ C), Exact (F.map f) (F.map g) → Exact f g
#align category_theory.functor.reflects_exact_sequences CategoryTheory.Functor.ReflectsExactSequences

theorem exact_of_exact_map (F : V ⥤ W) [ReflectsExactSequences F] {A B C : V} {f : A ⟶ B}
    {g : B ⟶ C} (hfg : Exact (F.map f) (F.map g)) : Exact f g :=
  ReflectsExactSequences.reflects f g hfg
#align category_theory.functor.exact_of_exact_map CategoryTheory.Functor.exact_of_exact_map

end Functor

end CategoryTheory
