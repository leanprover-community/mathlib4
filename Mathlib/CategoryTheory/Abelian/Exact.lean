/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Adam Topaz, Johan Commelin, Jakob von Raumer
-/
module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Tactic.TFAE

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* A short complex `S` is exact iff `imageSubobject S.f = kernelSubobject S.g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `Exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π f = 0` iff `Exact f 0`.
* A faithful functor between abelian categories that preserves zero morphisms reflects exact
  sequences.
* `X ⟶ Y ⟶ Z ⟶ 0` is exact if and only if the second map is a cokernel of the first, and
  `0 ⟶ X ⟶ Y ⟶ Z` is exact if and only if the first map is a kernel of the second.
* A functor `F` such that for all `S`, we have `S.Exact → (S.map F).Exact` preserves both
  finite limits and colimits.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

namespace CategoryTheory

namespace ShortComplex

variable (S : ShortComplex C)

attribute [local instance] hasEqualizers_of_hasKernels

theorem exact_iff_epi_imageToKernel' : S.Exact ↔ Epi (imageToKernel' S.f S.g S.zero) := by
  rw [S.exact_iff_epi_kernel_lift]
  have : factorThruImage S.f ≫ imageToKernel' S.f S.g S.zero = kernel.lift S.g S.f S.zero := by
    simp only [← cancel_mono (kernel.ι _), kernel.lift_ι, imageToKernel',
      Category.assoc, image.fac]
  constructor
  · intro
    exact epi_of_epi_fac this
  · intro
    rw [← this]
    apply epi_comp

theorem exact_iff_epi_imageToKernel : S.Exact ↔ Epi (imageToKernel S.f S.g S.zero) := by
  rw [S.exact_iff_epi_imageToKernel']
  apply (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
  exact Arrow.isoMk (imageSubobjectIso S.f).symm (kernelSubobjectIso S.g).symm

lemma exact_iff_isIso_imageToKernel' : S.Exact ↔ IsIso (imageToKernel' S.f S.g S.zero) := by
  simp only [S.exact_iff_epi_imageToKernel', isIso_iff_mono_and_epi, iff_and_self]
  intro
  apply Limits.kernel.lift_mono

theorem exact_iff_isIso_imageToKernel : S.Exact ↔ IsIso (imageToKernel S.f S.g S.zero) := by
  rw [S.exact_iff_epi_imageToKernel]
  constructor
  · intro
    apply isIso_of_mono_of_epi
  · intro
    infer_instance

lemma Exact.isIso_imageToKernel (hS : S.Exact) : IsIso (imageToKernel S.f S.g S.zero) :=
  S.exact_iff_isIso_imageToKernel.1 hS

lemma Exact.isIso_imageToKernel' (hS : S.Exact) : IsIso (imageToKernel' S.f S.g S.zero) :=
  S.exact_iff_isIso_imageToKernel'.1 hS

/-- In an abelian category, a short complex `S` is exact
iff `imageSubobject S.f = kernelSubobject S.g`.
-/
theorem exact_iff_image_eq_kernel : S.Exact ↔ imageSubobject S.f = kernelSubobject S.g := by
  rw [exact_iff_isIso_imageToKernel]
  constructor
  · intro
    exact Subobject.eq_of_comm (asIso (imageToKernel _ _ S.zero)) (by simp)
  · intro h
    exact ⟨Subobject.ofLE _ _ h.ge, by ext; simp, by ext; simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem exact_iff_of_forks {cg : KernelFork S.g} (hg : IsLimit cg) {cf : CokernelCofork S.f}
    (hf : IsColimit cf) : S.Exact ↔ cg.ι ≫ cf.π = 0 := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero]
  let e₁ := IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hg
  let e₂ := IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hf
  have : cg.ι ≫ cf.π = e₁.inv ≫ kernel.ι S.g ≫ cokernel.π S.f ≫ e₂.hom := by
    have eq₁ := IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) hg (.zero)
    have eq₂ := IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel S.f) hf (.one)
    dsimp at eq₁ eq₂
    rw [← eq₁, ← eq₂, Category.assoc]
  rw [this, IsIso.comp_left_eq_zero e₁.inv, ← Category.assoc,
    IsIso.comp_right_eq_zero _ e₂.hom]

variable {S}

/-- If `(f, g)` is exact, then `Abelian.image.ι S.f` is a kernel of `S.g`. -/
def Exact.isLimitImage (h : S.Exact) :
    IsLimit (KernelFork.ofι (Abelian.image.ι S.f)
      (Abelian.image_ι_comp_eq_zero S.zero) : KernelFork S.g) := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  exact KernelFork.IsLimit.ofι _ _
    (fun u hu ↦ kernel.lift (cokernel.π S.f) u
      (by rw [← kernel.lift_ι S.g u hu, Category.assoc, h, comp_zero])) (by simp)
    (fun _ _ _ hm => by rw [← cancel_mono (Abelian.image.ι S.f), hm, kernel.lift_ι])

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
def Exact.isLimitImage' (h : S.Exact) :
    IsLimit (KernelFork.ofι (Limits.image.ι S.f)
      (image_ι_comp_eq_zero S.zero) : KernelFork S.g) :=
  IsKernel.isoKernel _ _ h.isLimitImage (Abelian.imageIsoImage S.f).symm <| IsImage.lift_fac _ _

/-- If `(f, g)` is exact, then `Abelian.coimage.π g` is a cokernel of `f`. -/
def Exact.isColimitCoimage (h : S.Exact) :
    IsColimit
      (CokernelCofork.ofπ (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero) :
        CokernelCofork S.f) := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun u hu => cokernel.desc (kernel.ι S.g) u
      (by rw [← cokernel.π_desc S.f u hu, ← Category.assoc, h, zero_comp]))
    (by simp) ?_
  intro _ _ _ _ hm
  ext
  rw [hm, cokernel.π_desc]

set_option backward.isDefEq.respectTransparency false in
/-- If `(f, g)` is exact, then `factorThruImage g` is a cokernel of `f`. -/
def Exact.isColimitImage (h : S.Exact) :
    IsColimit (CokernelCofork.ofπ (Limits.factorThruImage S.g)
        (comp_factorThruImage_eq_zero S.zero)) :=
  IsCokernel.cokernelIso _ _ h.isColimitCoimage (Abelian.coimageIsoImage' S.g) <|
    (cancel_mono (Limits.image.ι S.g)).1 <| by simp

theorem exact_kernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (kernel.ι f) f (by simp)).Exact :=
  exact_of_f_is_kernel _ (kernelIsKernel f)

theorem exact_cokernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk f (cokernel.π f) (by simp)).Exact :=
  exact_of_g_is_cokernel _ (cokernelIsCokernel f)

variable (S)

theorem exact_iff_exact_image_ι :
    S.Exact ↔ (ShortComplex.mk (Abelian.image.ι S.f) S.g
      (Abelian.image_ι_comp_eq_zero S.zero)).Exact :=
  ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := Abelian.factorThruImage S.f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }

theorem exact_iff_exact_coimage_π :
    S.Exact ↔ (ShortComplex.mk S.f (Abelian.coimage.π S.g)
      (Abelian.comp_coimage_π_eq_zero S.zero)).Exact := by
  symm
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.factorThruCoimage S.g }

end ShortComplex

section

open List in
theorem Abelian.tfae_mono {X Y : C} (f : X ⟶ Y) (Z : C) :
    TFAE [Mono f, kernel.ι f = 0, (ShortComplex.mk (0 : Z ⟶ X) f zero_comp).Exact] := by
  tfae_have 2 → 1 := mono_of_kernel_ι_eq_zero _
  tfae_have 1 → 2
  | _ => by rw [← cancel_mono f, kernel.condition, zero_comp]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_mono _ (by simp)
  tfae_finish

open List in
theorem Abelian.tfae_epi {X Y : C} (f : X ⟶ Y) (Z : C) :
    TFAE [Epi f, cokernel.π f = 0, (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).Exact] := by
  tfae_have 2 → 1 := epi_of_cokernel_π_eq_zero _
  tfae_have 1 → 2
  | _ => by rw [← cancel_epi f, cokernel.condition, comp_zero]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_epi _ (by simp)
  tfae_finish

end

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F]

set_option backward.isDefEq.respectTransparency false in
lemma reflects_exact_of_faithful [F.Faithful] (S : ShortComplex C) (hS : (S.map F).Exact) :
    S.Exact := by
  rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero] at hS ⊢
  dsimp at hS
  apply F.zero_of_map_zero
  obtain ⟨k, hk⟩ :=
    kernel.lift' (F.map S.g) (F.map (kernel.ι S.g))
      (by simp only [← F.map_comp, kernel.condition, CategoryTheory.Functor.map_zero])
  obtain ⟨l, hl⟩ :=
    cokernel.desc' (F.map S.f) (F.map (cokernel.π S.f))
      (by simp only [← F.map_comp, cokernel.condition, CategoryTheory.Functor.map_zero])
  rw [F.map_comp, ← hl, ← hk, Category.assoc, reassoc_of% hS, zero_comp, comp_zero]

end

end Functor

namespace Functor

open Limits Abelian

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [Abelian A] [Abelian B]
variable (L : A ⥤ B)

section

variable [L.PreservesZeroMorphisms]
variable (hL : ∀ (S : ShortComplex A), S.Exact → (S.map L).Exact)
include hL

open ZeroObject

/-- A functor which preserves exactness preserves monomorphisms. -/
theorem preservesMonomorphisms_of_map_exact : L.PreservesMonomorphisms where
  preserves f hf := by
    apply ((Abelian.tfae_mono (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_mono f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- A functor which preserves exactness preserves epimorphisms. -/
theorem preservesEpimorphisms_of_map_exact : L.PreservesEpimorphisms where
  preserves f hf := by
    apply ((Abelian.tfae_epi (L.map f) (L.obj 0)).out 2 0).mp
    refine ShortComplex.exact_of_iso ?_ (hL _ (((tfae_epi f 0).out 0 2).mp hf))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- A functor which preserves the exactness of short complexes preserves homology. -/
lemma preservesHomology_of_map_exact : L.PreservesHomology where
  preservesCokernels X Y f := by
    have := preservesEpimorphisms_of_map_exact _ hL
    apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    apply (CokernelCofork.isColimitMapCoconeEquiv _ L).2
    have : Epi ((ShortComplex.mk _ _ (cokernel.condition f)).map L).g := by
      dsimp
      infer_instance
    exact (hL (ShortComplex.mk _ _ (cokernel.condition f))
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))).gIsCokernel
  preservesKernels X Y f := by
    have := preservesMonomorphisms_of_map_exact _ hL
    apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
    apply (KernelFork.isLimitMapConeEquiv _ L).2
    have : Mono ((ShortComplex.mk _ _ (kernel.condition f)).map L).f := by
      dsimp
      infer_instance
    exact (hL (ShortComplex.mk _ _ (kernel.condition f))
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f))).fIsKernel

end

section

set_option backward.isDefEq.respectTransparency false in
/-- A functor preserving zero morphisms, monos, and cokernels preserves homology. -/
lemma preservesHomology_of_preservesMonos_and_cokernels [PreservesZeroMorphisms L]
    [PreservesMonomorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) L] :
    PreservesHomology L := by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : (ShortComplex.mk _ _ (Abelian.comp_coimage_π_eq_zero S.zero)).map L ⟶ S.map L :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := L.map (Abelian.factorThruCoimage S.g)
      comm₂₃ := by
        dsimp
        rw [Category.id_comp, ← L.map_comp, cokernel.π_desc] }
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1
  apply ShortComplex.exact_of_g_is_cokernel
  exact CokernelCofork.mapIsColimit _ ((S.exact_iff_exact_coimage_π).1 hS).gIsCokernel L

set_option backward.isDefEq.respectTransparency false in
/-- A functor preserving zero morphisms, epis, and kernels preserves homology. -/
lemma preservesHomology_of_preservesEpis_and_kernels [PreservesZeroMorphisms L]
    [PreservesEpimorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) L] :
    PreservesHomology L := by
  apply preservesHomology_of_map_exact
  intro S hS
  let φ : S.map L ⟶ (ShortComplex.mk _ _ (Abelian.image_ι_comp_eq_zero S.zero)).map L :=
    { τ₁ := L.map (Abelian.factorThruImage S.f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp
        rw [Category.comp_id, ← L.map_comp, kernel.lift_ι] }
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.mapIsLimit _ ((S.exact_iff_exact_image_ι).1 hS).fIsKernel L

end

end Functor

end CategoryTheory
