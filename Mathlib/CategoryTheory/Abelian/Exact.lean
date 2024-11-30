/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Adam Topaz, Johan Commelin, Jakob von Raumer
-/
import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Adjunction.Limits
<<<<<<< HEAD
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
=======
>>>>>>> origin/ext-change-of-universes
import Mathlib.Tactic.TFAE

/-!
# Exact sequences in abelian categories

In an abelian category, we get several interesting results related to exactness which are not
true in more general settings.

## Main results
* A short complex `S` is exact iff `imageSubobject S.f = kernelSubobject S.g`.
* If `(f, g)` is exact, then `image.ι f` has the universal property of the kernel of `g`.
* `f` is a monomorphism iff `kernel.ι f = 0` iff `Exact 0 f`, and `f` is an epimorphism iff
  `cokernel.π = 0` iff `Exact f 0`.
* A faithful functor between abelian categories that preserves zero morphisms reflects exact
  sequences.
* `X ⟶ Y ⟶ Z ⟶ 0` is exact if and only if the second map is a cokernel of the first, and
  `0 ⟶ X ⟶ Y ⟶ Z` is exact if and only if the first map is a kernel of the second.
* A functor `F` such that for all `S`, we have `S.Exact → (S.map F).Exact` preserves both
finite limits and colimits.

-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/- redundant with the new homology API

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

theorem exact_iff_isIso_imageToKernel : S.Exact ↔ IsIso (imageToKernel S.f S.g S.zero) := by
  rw [S.exact_iff_epi_imageToKernel]
  constructor
  · intro
    apply isIso_of_mono_of_epi
  · intro
    infer_instance

/-- In an abelian category, a short complex `S` is exact
iff `imageSubobject S.f = kernelSubobject S.g`.
-/
<<<<<<< HEAD
theorem exact_iff_image_eq_kernel : Exact' f g ↔ imageSubobject f = kernelSubobject g := by
=======
theorem exact_iff_image_eq_kernel : S.Exact ↔ imageSubobject S.f = kernelSubobject S.g := by
  rw [exact_iff_isIso_imageToKernel]
>>>>>>> origin/ext-change-of-universes
  constructor
  · intro
    exact Subobject.eq_of_comm (asIso (imageToKernel _ _ S.zero)) (by simp)
  · intro h
    exact ⟨Subobject.ofLE _ _ h.ge, by ext; simp, by ext; simp⟩

<<<<<<< HEAD
theorem exact_iff : Exact' f g ↔ f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0 := by
  constructor
  · exact fun h ↦ ⟨h.1, kernel_comp_cokernel f g h⟩
  · refine fun h ↦ ⟨h.1, ?_⟩
    suffices hl : IsLimit
        (KernelFork.ofι (imageSubobject f).arrow (imageSubobject_arrow_comp_eq_zero h.1)) by
      have : imageToKernel f g h.1 = (hl.conePointUniqueUpToIso (limit.isLimit _)).hom ≫
          (kernelSubobjectIso _).inv := by ext; simp
      rw [this]
      infer_instance
    refine KernelFork.IsLimit.ofι _ _ (fun u hu ↦ ?_) ?_ (fun _ _ _ h ↦ ?_)
    · refine kernel.lift (cokernel.π f) u ?_ ≫ (imageIsoImage f).hom ≫ (imageSubobjectIso _).inv
      rw [← kernel.lift_ι g u hu, Category.assoc, h.2, comp_zero]
    · aesop_cat
    · rw [← cancel_mono (imageSubobject f).arrow, h]
      simp
#align category_theory.abelian.exact_iff CategoryTheory.Abelian.exact_iff

theorem exact_iff' {cg : KernelFork g} (hg : IsLimit cg) {cf : CokernelCofork f}
    (hf : IsColimit cf) : Exact' f g ↔ f ≫ g = 0 ∧ cg.ι ≫ cf.π = 0 := by
  constructor
  · intro h
    exact ⟨h.1, fork_ι_comp_cofork_π f g h cg cf⟩
  · rw [exact_iff]
    refine fun h => ⟨h.1, ?_⟩
    apply zero_of_epi_comp (IsLimit.conePointUniqueUpToIso hg (limit.isLimit _)).hom
    apply zero_of_comp_mono (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hf).hom
    simp [h.2]
#align category_theory.abelian.exact_iff' CategoryTheory.Abelian.exact_iff'

open List in
theorem exact_tfae :
    TFAE [Exact' f g, f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0,
      imageSubobject f = kernelSubobject g] := by
  tfae_have 1 ↔ 2; · apply exact_iff
  tfae_have 1 ↔ 3; · apply exact_iff_image_eq_kernel
  tfae_finish
#align category_theory.abelian.exact_tfae CategoryTheory.Abelian.exact_tfae

nonrec theorem IsEquivalence.exact_iff {D : Type u₁} [Category.{v₁} D] [Abelian D] (F : C ⥤ D)
    [F.IsEquivalence] : Exact (F.map f) (F.map g) ↔ Exact f g := by
  simp only [exact_iff, ← F.map_eq_zero_iff, F.map_comp, Category.assoc, ←
    kernelComparison_comp_ι g F, ← π_comp_cokernelComparison f F]
  rw [IsIso.comp_left_eq_zero (kernelComparison g F), ← Category.assoc,
    IsIso.comp_right_eq_zero _ (cokernelComparison f F)]
#align category_theory.abelian.is_equivalence.exact_iff CategoryTheory.Abelian.IsEquivalence.exact_iff

/-- The dual result is true even in non-abelian categories, see
    `CategoryTheory.exact_comp_mono_iff`. -/
theorem exact_epi_comp_iff {W : C} (h : W ⟶ X) [Epi h] : Exact' (h ≫ f) g ↔ Exact' f g := by
  refine' ⟨fun hfg => _, fun h => exact_epi_comp h⟩
  let hc := isCokernelOfComp _ _ (colimit.isColimit (parallelPair (h ≫ f) 0))
    (by rw [← cancel_epi h, ← Category.assoc, CokernelCofork.condition, comp_zero]) rfl
  refine' (exact_iff' _ _ (limit.isLimit _) hc).2 ⟨_, ((exact_iff _ _).1 hfg).2⟩
  exact zero_of_epi_comp h (by rw [← hfg.1, Category.assoc])
#align category_theory.abelian.exact_epi_comp_iff CategoryTheory.Abelian.exact_epi_comp_iff

/-- If `(f, g)` is exact, then `Abelian.image.ι f` is a kernel of `g`. -/
def isLimitImage (h : Exact' f g) :
    IsLimit (KernelFork.ofι (Abelian.image.ι f) (image_ι_comp_eq_zero h.1) : KernelFork g) := by
  rw [exact_iff] at h
=======
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
>>>>>>> origin/ext-change-of-universes
  exact KernelFork.IsLimit.ofι _ _
    (fun u hu ↦ kernel.lift (cokernel.π S.f) u
      (by rw [← kernel.lift_ι S.g u hu, Category.assoc, h, comp_zero])) (by aesop_cat)
    (fun _ _ _ hm => by rw [← cancel_mono (Abelian.image.ι S.f), hm, kernel.lift_ι])

/-- If `(f, g)` is exact, then `image.ι f` is a kernel of `g`. -/
<<<<<<< HEAD
def isLimitImage' (h : Exact' f g) :
    IsLimit (KernelFork.ofι (Limits.image.ι f) (Limits.image_ι_comp_eq_zero h.1)) :=
  IsKernel.isoKernel _ _ (isLimitImage f g h) (imageIsoImage f).symm <| IsImage.lift_fac _ _
#align category_theory.abelian.is_limit_image' CategoryTheory.Abelian.isLimitImage'

/-- If `(f, g)` is exact, then `Abelian.coimage.π g` is a cokernel of `f`. -/
def isColimitCoimage (h : Exact' f g) :
=======
def Exact.isLimitImage' (h : S.Exact) :
    IsLimit (KernelFork.ofι (Limits.image.ι S.f)
      (image_ι_comp_eq_zero S.zero) : KernelFork S.g) :=
  IsKernel.isoKernel _ _ h.isLimitImage (Abelian.imageIsoImage S.f).symm <| IsImage.lift_fac _ _

/-- If `(f, g)` is exact, then `Abelian.coimage.π g` is a cokernel of `f`. -/
def Exact.isColimitCoimage (h : S.Exact) :
>>>>>>> origin/ext-change-of-universes
    IsColimit
      (CokernelCofork.ofπ (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero) :
        CokernelCofork S.f) := by
  rw [exact_iff_kernel_ι_comp_cokernel_π_zero] at h
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun u hu => cokernel.desc (kernel.ι S.g) u
      (by rw [← cokernel.π_desc S.f u hu, ← Category.assoc, h, zero_comp]))
    (by aesop_cat) ?_
  intros _ _ _ _ hm
  ext
  rw [hm, cokernel.π_desc]

/-- If `(f, g)` is exact, then `factorThruImage g` is a cokernel of `f`. -/
<<<<<<< HEAD
def isColimitImage (h : Exact' f g) :
    IsColimit (CokernelCofork.ofπ (Limits.factorThruImage g) (comp_factorThruImage_eq_zero h.1)) :=
  IsCokernel.cokernelIso _ _ (isColimitCoimage f g h) (coimageIsoImage' g) <|
    (cancel_mono (Limits.image.ι g)).1 <| by simp
#align category_theory.abelian.is_colimit_image CategoryTheory.Abelian.isColimitImage

theorem exact_cokernel : Exact' f (cokernel.π f) := by
  rw [exact_iff]
  aesop_cat
#align category_theory.abelian.exact_cokernel CategoryTheory.Abelian.exact_cokernel
=======
def Exact.isColimitImage (h : S.Exact) :
    IsColimit (CokernelCofork.ofπ (Limits.factorThruImage S.g)
        (comp_factorThruImage_eq_zero S.zero)) :=
  IsCokernel.cokernelIso _ _ h.isColimitCoimage (Abelian.coimageIsoImage' S.g) <|
    (cancel_mono (Limits.image.ι S.g)).1 <| by simp

theorem exact_kernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (kernel.ι f) f (by simp)).Exact :=
  exact_of_f_is_kernel _ (kernelIsKernel f)
>>>>>>> origin/ext-change-of-universes

theorem exact_cokernel {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk f (cokernel.π f) (by simp)).Exact :=
  exact_of_g_is_cokernel _ (cokernelIsCokernel f)

<<<<<<< HEAD
-- Porting note: this can no longer be an instance in Lean4
/-- If `ex : Exact f g` and `epi g`, then `cokernel.desc _ _ ex.w` is an isomorphism. -/
lemma isIso_cokernel_desc_of_exact_of_epi (ex : Exact' f g) [Epi g] :
    IsIso (cokernel.desc f g ex.w) :=
  have := mono_cokernel_desc_of_exact _ _ ex
  isIso_of_mono_of_epi (Limits.cokernel.desc f g ex.w)

-- Porting note: removed the simp attribute because the lemma may never apply automatically
@[reassoc (attr := nolint unusedHavesSuffices)]
theorem cokernel.desc.inv [Epi g] (ex : Exact' f g) :
    have := isIso_cokernel_desc_of_exact_of_epi _ _ ex
    g ≫ inv (cokernel.desc _ _ ex.w) = cokernel.π _ := by
  have := isIso_cokernel_desc_of_exact_of_epi _ _ ex
  simp
#align category_theory.abelian.cokernel.desc.inv CategoryTheory.Abelian.cokernel.desc.inv
=======
variable (S)

theorem exact_iff_exact_image_ι :
    S.Exact ↔ (ShortComplex.mk (Abelian.image.ι S.f) S.g
      (Abelian.image_ι_comp_eq_zero S.zero)).Exact :=
  ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := Abelian.factorThruImage S.f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
>>>>>>> origin/ext-change-of-universes

theorem exact_iff_exact_coimage_π :
    S.Exact ↔ (ShortComplex.mk S.f (Abelian.coimage.π S.g)
      (Abelian.comp_coimage_π_eq_zero S.zero)).Exact := by
  symm
  exact ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.factorThruCoimage S.g }

<<<<<<< HEAD
-- Porting note: removed the simp attribute because the lemma may never apply automatically
@[reassoc (attr := nolint unusedHavesSuffices)]
theorem kernel.lift.inv [Mono f] (ex : Exact' f g) :
    have := isIso_kernel_lift_of_exact_of_mono _ _ ex
    inv (kernel.lift _ _ ex.w) ≫ f = kernel.ι g := by
  have := isIso_kernel_lift_of_exact_of_mono _ _ ex
  simp
#align category_theory.abelian.kernel.lift.inv CategoryTheory.Abelian.kernel.lift.inv

/-- If `X ⟶ Y ⟶ Z ⟶ 0` is exact, then the second map is a cokernel of the first. -/
def isColimitOfExactOfEpi [Epi g] (h : Exact' f g) : IsColimit (CokernelCofork.ofπ _ h.w) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) <|
    Cocones.ext
      ⟨cokernel.desc _ _ h.w, epiDesc g (cokernel.π f) ((exact_iff _ _).1 h).2,
        (cancel_epi (cokernel.π f)).1 (by aesop_cat), (cancel_epi g).1 (by aesop_cat)⟩
          (by rintro (_|_) <;> simp [h.w])
#align category_theory.abelian.is_colimit_of_exact_of_epi CategoryTheory.Abelian.isColimitOfExactOfEpi

/-- If `0 ⟶ X ⟶ Y ⟶ Z` is exact, then the first map is a kernel of the second. -/
def isLimitOfExactOfMono [Mono f] (h : Exact' f g) : IsLimit (KernelFork.ofι _ h.w) :=
  IsLimit.ofIsoLimit (limit.isLimit _) <|
    Cones.ext
      ⟨monoLift f (kernel.ι g) ((exact_iff _ _).1 h).2, kernel.lift _ _ h.w,
        (cancel_mono (kernel.ι g)).1 (by aesop_cat), (cancel_mono f).1 (by aesop_cat)⟩
      fun j => by cases j <;> simp
#align category_theory.abelian.is_limit_of_exact_of_mono CategoryTheory.Abelian.isLimitOfExactOfMono

theorem exact_of_is_cokernel (w : f ≫ g = 0)
    (h : IsColimit (CokernelCofork.ofπ _ w)) : Exact' f g := by
  refine' (exact_iff _ _).2 ⟨w, _⟩
  have := h.fac (CokernelCofork.ofπ _ (cokernel.condition f)) WalkingParallelPair.one
  simp only [Cofork.ofπ_ι_app] at this
  rw [← this, ← Category.assoc, kernel.condition, zero_comp]
#align category_theory.abelian.exact_of_is_cokernel CategoryTheory.Abelian.exact_of_is_cokernel

theorem exact_of_is_kernel (w : f ≫ g = 0) (h : IsLimit (KernelFork.ofι _ w)) : Exact' f g := by
  refine' (exact_iff _ _).2 ⟨w, _⟩
  have := h.fac (KernelFork.ofι _ (kernel.condition g)) WalkingParallelPair.zero
  simp only [Fork.ofι_π_app] at this
  rw [← this, Category.assoc, cokernel.condition, comp_zero]
#align category_theory.abelian.exact_of_is_kernel CategoryTheory.Abelian.exact_of_is_kernel

theorem exact_iff_exact_image_ι : Exact' f g ↔ Exact' (Abelian.image.ι f) g := by
  conv_lhs => rw [← Abelian.image.fac f]
  rw [exact_epi_comp_iff]
#align category_theory.abelian.exact_iff_exact_image_ι CategoryTheory.Abelian.exact_iff_exact_image_ι

theorem exact_iff_exact_coimage_π : Exact' f g ↔ Exact' f (coimage.π g) := by
  conv_lhs => rw [← Abelian.coimage.fac g]
  rw [exact_comp_mono_iff]
#align category_theory.abelian.exact_iff_exact_coimage_π CategoryTheory.Abelian.exact_iff_exact_coimage_π
=======
end ShortComplex
>>>>>>> origin/ext-change-of-universes

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
<<<<<<< HEAD
theorem tfae_mono : TFAE [Mono f, kernel.ι f = 0, Exact' (0 : Z ⟶ X) f] := by
  tfae_have 3 → 2
  · exact kernel_ι_eq_zero_of_exact_zero_left Z
  tfae_have 1 → 3
  · intros
    exact exact_zero_left_of_mono Z
  tfae_have 2 → 1
  · exact mono_of_kernel_ι_eq_zero _
  tfae_finish
#align category_theory.abelian.tfae_mono CategoryTheory.Abelian.tfae_mono

-- Note we've already proved `mono_iff_exact_zero_left : mono f ↔ Exact (0 : Z ⟶ X) f`
-- in any preadditive category with kernels and images.
theorem mono_iff_kernel_ι_eq_zero : Mono f ↔ kernel.ι f = 0 :=
  (tfae_mono X f).out 0 1
#align category_theory.abelian.mono_iff_kernel_ι_eq_zero CategoryTheory.Abelian.mono_iff_kernel_ι_eq_zero

open List in
theorem tfae_epi : TFAE [Epi f, cokernel.π f = 0, Exact' f (0 : Y ⟶ Z)] := by
  tfae_have 3 → 2
  · rw [exact_iff]
    rintro ⟨-, h⟩
    exact zero_of_epi_comp _ h
  tfae_have 1 → 3
  · rw [exact_iff]
    intro
    exact ⟨by simp, by simp [cokernel.π_of_epi]⟩
  tfae_have 2 → 1
  · exact epi_of_cokernel_π_eq_zero _
  tfae_finish
#align category_theory.abelian.tfae_epi CategoryTheory.Abelian.tfae_epi

-- Note we've already proved `epi_iff_exact_zero_right : epi f ↔ exact f (0 : Y ⟶ Z)`
-- in any preadditive category with equalizers and images.
theorem epi_iff_cokernel_π_eq_zero : Epi f ↔ cokernel.π f = 0 :=
  (tfae_epi X f).out 0 1
#align category_theory.abelian.epi_iff_cokernel_π_eq_zero CategoryTheory.Abelian.epi_iff_cokernel_π_eq_zero

end

section Opposite

theorem Exact.op (h : Exact' f g) : Exact' g.op f.op := by
  rw [exact_iff]
  refine' ⟨by simp [← op_comp, h.w], Quiver.Hom.unop_inj _⟩
  simp only [unop_comp, cokernel.π_op, eqToHom_refl, kernel.ι_op, Category.id_comp,
    Category.assoc, kernel_comp_cokernel_assoc _ _ h, zero_comp, comp_zero, unop_zero]
#align category_theory.abelian.exact.op CategoryTheory.Abelian.Exact.op

theorem Exact.op_iff : Exact' g.op f.op ↔ Exact' f g :=
  ⟨fun e => by
    rw [← IsEquivalence.exact_iff _ _ (opOpEquivalence C).inverse]
    exact Exact.op _ _ e, Exact.op _ _⟩
#align category_theory.abelian.exact.op_iff CategoryTheory.Abelian.Exact.op_iff

theorem Exact.unop {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (f : Y ⟶ Z) (h : Exact' g f) : Exact' f.unop g.unop := by
  rw [← f.op_unop, ← g.op_unop] at h
  rwa [← Exact.op_iff]
#align category_theory.abelian.exact.unop CategoryTheory.Abelian.Exact.unop

theorem Exact.unop_iff {X Y Z : Cᵒᵖ} (g : X ⟶ Y) (f : Y ⟶ Z) : Exact' f.unop g.unop ↔ Exact' g f :=
  ⟨fun e => by rwa [← f.op_unop, ← g.op_unop, ← Exact.op_iff] at e, fun e => by
    rw [← Exact.op_iff]
    exact e⟩
#align category_theory.abelian.exact.unop_iff CategoryTheory.Abelian.Exact.unop_iff

end Opposite

end Abelian-/

namespace CategoryTheory

/-

this is now in `CategoryTheory.Functor.ReflectsExactSequences`

=======
theorem Abelian.tfae_epi {X Y : C} (f : X ⟶ Y) (Z : C ) :
    TFAE [Epi f, cokernel.π f = 0, (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).Exact] := by
  tfae_have 2 → 1 := epi_of_cokernel_π_eq_zero _
  tfae_have 1 → 2
  | _ => by rw [← cancel_epi f, cokernel.condition, comp_zero]
  tfae_have 3 ↔ 1 := ShortComplex.exact_iff_epi _ (by simp)
  tfae_finish

end

>>>>>>> origin/ext-change-of-universes
namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F]

<<<<<<< HEAD
instance (priority := 100) reflectsExactSequences'OfPreservesZeroMorphismsOfFaithful [Faithful F] :
    ReflectsExactSequences F where
  reflects {X Y Z} f g hfg := by
    rw [Abelian.exact_iff, ← F.map_comp, F.map_eq_zero_iff] at hfg
    refine' (Abelian.exact_iff _ _).2 ⟨hfg.1, F.zero_of_map_zero _ _⟩
    obtain ⟨k, hk⟩ :=
      kernel.lift' (F.map g) (F.map (kernel.ι g))
        (by simp only [← F.map_comp, kernel.condition, CategoryTheory.Functor.map_zero])
    obtain ⟨l, hl⟩ :=
      cokernel.desc' (F.map f) (F.map (cokernel.π f))
        (by simp only [← F.map_comp, cokernel.condition, CategoryTheory.Functor.map_zero])
    rw [F.map_comp, ← hk, ← hl, Category.assoc, reassoc_of% hfg.2, zero_comp, comp_zero]
#align category_theory.functor.reflects_exact_sequences_of_preserves_zero_morphisms_of_faithful CategoryTheory.Functor.reflectsExactSequences'OfPreservesZeroMorphismsOfFaithful
=======
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
>>>>>>> origin/ext-change-of-universes

end

end Functor-/

namespace Functor

@[deprecated (since := "2024-07-09")] alias CategoryTheory.Functor.map_exact :=
  ShortComplex.Exact.map

open Limits Abelian

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [Abelian A] [Abelian B]
variable (L : A ⥤ B)

section

<<<<<<< HEAD
variable [PreservesFiniteLimits L] [PreservesFiniteColimits L]


/- redundant with the new homologhy API, because this works
instance : L.PreservesHomology := inferInstance

/-- A functor preserving finite limits and finite colimits preserves exactness. The converse
result is also true, see `Functor.preservesFiniteLimitsOfMapExact` and
`Functor.preservesFiniteColimitsOfMapExact`. -/
theorem map_exact {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (e1 : Exact' f g) :
    Exact' (L.map f) (L.map g) := by
  let hcoker := isColimitOfHasCokernelOfPreservesColimit L f
  let hker := isLimitOfHasKernelOfPreservesLimit L g
  refine' (exact_iff' _ _ hker hcoker).2 ⟨by simp [← L.map_comp, e1.1], _⟩
  simp only [Fork.ι_ofι, Cofork.π_ofπ, ← L.map_comp, kernel_comp_cokernel _ _ e1, L.map_zero]
#align category_theory.functor.map_exact CategoryTheory.Functor.map_exact-/

end

section

--variable (h : ∀ ⦃X Y Z : A⦄ {f : X ⟶ Y} {g : Y ⟶ Z}, Exact' f g → Exact' (L.map f) (L.map g))

variable [L.PreservesZeroMorphisms]
variable (h : ∀ (S : ShortComplex A), S.Exact → (S.map L).Exact)

open ZeroObject

/-
/-- A functor which preserves exactness preserves zero morphisms. -/
theorem preservesZeroMorphisms_of_map_exact : L.PreservesZeroMorphisms := by
  replace h := (h (exact_of_zero (𝟙 0) (𝟙 0))).w
  rw [L.map_id, Category.comp_id] at h
  exact preservesZeroMorphisms_of_map_zero_object (idZeroEquivIsoZero _ h)
#align category_theory.functor.preserves_zero_morphisms_of_map_exact CategoryTheory.Functor.preservesZeroMorphisms_of_map_exact-/

/-- A functor which preserves exactness preserves monomorphisms. -/
theorem preservesMonomorphisms_of_map_exact : L.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    let S := ShortComplex.mk (0 : 0 ⟶ X) f zero_comp
    erw [← S.exact_iff_mono rfl] at hf
    erw [← (S.map L).exact_iff_mono (by simp)]
    exact h _ hf
#align category_theory.functor.preserves_monomorphisms_of_map_exact CategoryTheory.Functor.preservesMonomorphisms_of_map_exact

/-- A functor which preserves exactness preserves epimorphisms. -/
theorem preservesEpimorphisms_of_map_exact : L.PreservesEpimorphisms where
  preserves {X Y} f hf := by
    let S := ShortComplex.mk f (0 : Y ⟶ 0) comp_zero
    erw [← S.exact_iff_epi rfl] at hf
    erw [← (S.map L).exact_iff_epi (by simp)]
    exact h _ hf
#align category_theory.functor.preserves_epimorphisms_of_map_exact CategoryTheory.Functor.preservesEpimorphisms_of_map_exact

/-- A functor which preserves exactness preserves kernels. -/
def preservesKernelsOfMapExact (X Y : A) (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) L where
  preserves {c : KernelFork f} ic := by
    apply (c.isLimitMapConeEquiv L).invFun
    letI := mono_of_isLimit_fork ic
    letI := preservesMonomorphisms_of_map_exact L h
    let S := ShortComplex.mk c.ι f c.condition
    have : Mono (S.map L).f := by
      dsimp; infer_instance
    exact (h S (ShortComplex.exact_of_f_is_kernel _
      (IsLimit.ofIsoLimit ic (Fork.ext (Iso.refl _) (by simp))))).fIsKernel
#align category_theory.functor.preserves_kernels_of_map_exact CategoryTheory.Functor.preservesKernelsOfMapExact

/-- A functor which preserves exactness preserves zero cokernels. -/
def preservesCokernelsOfMapExact (X Y : A) (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) L where
  preserves {c : CokernelCofork f} ic := by
    apply (c.isColimitMapCoconeEquiv L).invFun
    letI := epi_of_isColimit_cofork ic
    letI := preservesEpimorphisms_of_map_exact L h
    let S := ShortComplex.mk f c.π c.condition
    have : Epi (S.map L).g := by
      dsimp; infer_instance
    exact (h S (ShortComplex.exact_of_g_is_cokernel _
      (IsColimit.ofIsoColimit ic (Cofork.ext (Iso.refl _) (by simp))))).gIsCokernel
#align category_theory.functor.preserves_cokernels_of_map_exact CategoryTheory.Functor.preservesCokernelsOfMapExact

/-- A functor which preserves exactness is left exact, i.e. preserves finite limits.
This is part of the inverse implication to `Functor.map_exact`. -/
def preservesFiniteLimitsOfMapExact : PreservesFiniteLimits L := by
  letI := preservesKernelsOfMapExact L h
  apply preservesFiniteLimitsOfPreservesKernels
#align category_theory.functor.preserves_finite_limits_of_map_exact CategoryTheory.Functor.preservesFiniteLimitsOfMapExact

/-- A functor which preserves exactness is right exact, i.e. preserves finite colimits.
This is part of the inverse implication to `Functor.map_exact`. -/
def preservesFiniteColimitsOfMapExact : PreservesFiniteColimits L := by
  letI := preservesCokernelsOfMapExact L h
  apply preservesFiniteColimitsOfPreservesCokernels
#align category_theory.functor.preserves_finite_colimits_of_map_exact CategoryTheory.Functor.preservesFiniteColimitsOfMapExact
=======
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

@[deprecated (since := "2024-07-09")] alias preservesKernelsOfMapExact :=
  PreservesHomology.preservesKernels
@[deprecated (since := "2024-07-09")] alias preservesCokernelsOfMapExact :=
  PreservesHomology.preservesCokernels
>>>>>>> origin/ext-change-of-universes

end

section

/-- A functor preserving zero morphisms, monos, and cokernels preserves homology. -/
lemma preservesHomology_of_preservesMonos_and_cokernels [PreservesZeroMorphisms L]
    [PreservesMonomorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) L] :
<<<<<<< HEAD
    PreservesFiniteLimits L := by
  apply preservesFiniteLimitsOfMapExact
  intro S hS
  let T := ShortComplex.mk S.f (coimage.π S.g) (by
    simp only [← cancel_mono (Abelian.factorThruCoimage S.g),
      coequalizer_as_cokernel, Category.assoc, cokernel.π_desc, ShortComplex.zero, zero_comp])
  let φ : T ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := Abelian.factorThruCoimage S.g }
  have : Epi (L.mapShortComplex.map φ).τ₁ := by dsimp; infer_instance
  have : IsIso (L.mapShortComplex.map φ).τ₂ := by dsimp; infer_instance
  have : Mono (L.mapShortComplex.map φ).τ₃ := by dsimp; infer_instance
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ] at hS
  erw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono (L.mapShortComplex.map φ)]
  exact ShortComplex.Exact.map_of_epi_of_preservesCokernel hS L
    (by dsimp; infer_instance) inferInstance
#align category_theory.functor.preserves_finite_limits_of_preserves_monos_and_cokernels CategoryTheory.Functor.preservesFiniteLimitsOfPreservesMonosAndCokernels
=======
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
>>>>>>> origin/ext-change-of-universes

/-- A functor preserving zero morphisms, epis, and kernels preserves homology. -/
lemma preservesHomology_of_preservesEpis_and_kernels [PreservesZeroMorphisms L]
    [PreservesEpimorphisms L] [∀ {X Y} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) L] :
<<<<<<< HEAD
    PreservesFiniteColimits L := by
  apply preservesFiniteColimitsOfMapExact
  intro S hS
  let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (by
    simp only [← cancel_epi (Abelian.factorThruImage S.f),
      equalizer_as_kernel, kernel.lift_ι_assoc, ShortComplex.zero, comp_zero])
  let φ : S ⟶ T :=
    { τ₁ := Abelian.factorThruImage S.f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have : Epi (L.mapShortComplex.map φ).τ₁ := by dsimp; infer_instance
  have : IsIso (L.mapShortComplex.map φ).τ₂ := by dsimp; infer_instance
  have : Mono (L.mapShortComplex.map φ).τ₃ := by dsimp; infer_instance
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ] at hS
  erw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono (L.mapShortComplex.map φ)]
  exact ShortComplex.Exact.map_of_mono_of_preservesKernel hS L
    (by dsimp; infer_instance) inferInstance
#align category_theory.functor.preserves_finite_colimits_of_preserves_epis_and_kernels CategoryTheory.Functor.preservesFiniteColimitsOfPreservesEpisAndKernels
=======
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
>>>>>>> origin/ext-change-of-universes

end

end Functor

end CategoryTheory
