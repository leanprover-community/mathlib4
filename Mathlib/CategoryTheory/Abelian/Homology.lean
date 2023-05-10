/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Amelia Livingston

! This file was ported from Lean 3 source module category_theory.abelian.homology
! leanprover-community/mathlib commit 956af7c76589f444f2e1313911bad16366ea476d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Additive
import Mathbin.CategoryTheory.Abelian.Pseudoelements
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Images

/-!

The object `homology f g w`, where `w : f ≫ g = 0`, can be identified with either a
cokernel or a kernel. The isomorphism with a cokernel is `homology_iso_cokernel_lift`, which
was obtained elsewhere. In the case of an abelian category, this file shows the isomorphism
with a kernel as well.

We use these isomorphisms to obtain the analogous api for `homology`:
- `homology.ι` is the map from `homology f g w` into the cokernel of `f`.
- `homology.π'` is the map from `kernel g` to `homology f g w`.
- `homology.desc'` constructs a morphism from `homology f g w`, when it is viewed as a cokernel.
- `homology.lift` constructs a morphism to `homology f g w`, when it is viewed as a kernel.
- Various small lemmas are proved as well, mimicking the API for (co)kernels.
With these definitions and lemmas, the isomorphisms between homology and a (co)kernel need not
be used directly.
-/


open CategoryTheory.Limits

open CategoryTheory

noncomputable section

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

variable {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)

namespace CategoryTheory.Abelian

/-- The cokernel of `kernel.lift g f w`. This is isomorphic to `homology f g w`.
  See `homology_iso_cokernel_lift`. -/
abbrev homologyC : A :=
  cokernel (kernel.lift g f w)
#align category_theory.abelian.homology_c CategoryTheory.Abelian.homologyC

/-- The kernel of `cokernel.desc f g w`. This is isomorphic to `homology f g w`.
  See `homology_iso_kernel_desc`. -/
abbrev homologyK : A :=
  kernel (cokernel.desc f g w)
#align category_theory.abelian.homology_k CategoryTheory.Abelian.homologyK

/-- The canonical map from `homology_c` to `homology_k`.
  This is an isomorphism, and it is used in obtaining the API for `homology f g w`
  in the bottom of this file. -/
abbrev homologyCToK : homologyC f g w ⟶ homologyK f g w :=
  cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ cokernel.π _) (by simp))
    (by
      apply limits.equalizer.hom_ext
      simp)
#align category_theory.abelian.homology_c_to_k CategoryTheory.Abelian.homologyCToK

attribute [local instance] pseudoelement.hom_to_fun pseudoelement.has_zero

instance : Mono (homologyCToK f g w) :=
  by
  apply pseudoelement.mono_of_zero_of_map_zero
  intro a ha
  obtain ⟨a, rfl⟩ := pseudoelement.pseudo_surjective_of_epi (cokernel.π (kernel.lift g f w)) a
  apply_fun kernel.ι (cokernel.desc f g w)  at ha
  simp only [← pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι,
    pseudoelement.apply_zero] at ha
  simp only [pseudoelement.comp_apply] at ha
  obtain ⟨b, hb⟩ : ∃ b, f b = _ := (pseudoelement.pseudo_exact_of_exact (exact_cokernel f)).2 _ ha
  rsuffices ⟨c, rfl⟩ : ∃ c, kernel.lift g f w c = a
  · simp [← pseudoelement.comp_apply]
  use b
  apply_fun kernel.ι g
  swap; · apply pseudoelement.pseudo_injective_of_mono
  simpa [← pseudoelement.comp_apply]

instance : Epi (homologyCToK f g w) :=
  by
  apply pseudoelement.epi_of_pseudo_surjective
  intro a
  let b := kernel.ι (cokernel.desc f g w) a
  obtain ⟨c, hc⟩ : ∃ c, cokernel.π f c = b
  apply pseudoelement.pseudo_surjective_of_epi (cokernel.π f)
  have : g c = 0 := by
    dsimp [b] at hc
    rw [show g = cokernel.π f ≫ cokernel.desc f g w by simp, pseudoelement.comp_apply, hc]
    simp [← pseudoelement.comp_apply]
  obtain ⟨d, hd⟩ : ∃ d, kernel.ι g d = c := by
    apply (pseudoelement.pseudo_exact_of_exact exact_kernel_ι).2 _ this
  use cokernel.π (kernel.lift g f w) d
  apply_fun kernel.ι (cokernel.desc f g w)
  swap
  · apply pseudoelement.pseudo_injective_of_mono
  simp only [← pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι]
  simp only [pseudoelement.comp_apply, hd, hc]

instance (w : f ≫ g = 0) : IsIso (homologyCToK f g w) :=
  isIso_of_mono_of_epi _

end CategoryTheory.Abelian

/-- The homology associated to `f` and `g` is isomorphic to a kernel. -/
def homologyIsoKernelDesc : homology f g w ≅ kernel (cokernel.desc f g w) :=
  homologyIsoCokernelLift _ _ _ ≪≫ asIso (CategoryTheory.Abelian.homologyCToK _ _ _)
#align homology_iso_kernel_desc homologyIsoKernelDesc

namespace homology

-- `homology.π` is taken
/-- The canonical map from the kernel of `g` to the homology of `f` and `g`. -/
def π' : kernel g ⟶ homology f g w :=
  cokernel.π _ ≫ (homologyIsoCokernelLift _ _ _).inv
#align homology.π' homology.π'

/-- The canonical map from the homology of `f` and `g` to the cokernel of `f`. -/
def ι : homology f g w ⟶ cokernel f :=
  (homologyIsoKernelDesc _ _ _).Hom ≫ kernel.ι _
#align homology.ι homology.ι

/-- Obtain a morphism from the homology, given a morphism from the kernel. -/
def desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) : homology f g w ⟶ W :=
  (homologyIsoCokernelLift _ _ _).Hom ≫ cokernel.desc _ e he
#align homology.desc' homology.desc'

/-- Obtain a moprhism to the homology, given a morphism to the kernel. -/
def lift {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) : W ⟶ homology f g w :=
  kernel.lift _ e he ≫ (homologyIsoKernelDesc _ _ _).inv
#align homology.lift homology.lift

@[simp, reassoc.1]
theorem π'_desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) :
    π' f g w ≫ desc' f g w e he = e := by
  dsimp [π', desc']
  simp
#align homology.π'_desc' homology.π'_desc'

@[simp, reassoc.1]
theorem lift_ι {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) :
    lift f g w e he ≫ ι _ _ _ = e := by
  dsimp [ι, lift]
  simp
#align homology.lift_ι homology.lift_ι

@[simp, reassoc.1]
theorem condition_π' : kernel.lift g f w ≫ π' f g w = 0 :=
  by
  dsimp [π']
  simp
#align homology.condition_π' homology.condition_π'

@[simp, reassoc.1]
theorem condition_ι : ι f g w ≫ cokernel.desc f g w = 0 :=
  by
  dsimp [ι]
  simp
#align homology.condition_ι homology.condition_ι

@[ext]
theorem hom_from_ext {W : A} (a b : homology f g w ⟶ W) (h : π' f g w ≫ a = π' f g w ≫ b) : a = b :=
  by
  dsimp [π'] at h
  apply_fun fun e => (homologyIsoCokernelLift f g w).inv ≫ e
  swap
  · intro i j hh
    apply_fun fun e => (homologyIsoCokernelLift f g w).Hom ≫ e  at hh
    simpa using hh
  simp only [category.assoc] at h
  exact coequalizer.hom_ext h
#align homology.hom_from_ext homology.hom_from_ext

@[ext]
theorem hom_to_ext {W : A} (a b : W ⟶ homology f g w) (h : a ≫ ι f g w = b ≫ ι f g w) : a = b :=
  by
  dsimp [ι] at h
  apply_fun fun e => e ≫ (homologyIsoKernelDesc f g w).Hom
  swap
  · intro i j hh
    apply_fun fun e => e ≫ (homologyIsoKernelDesc f g w).inv  at hh
    simpa using hh
  simp only [← category.assoc] at h
  exact equalizer.hom_ext h
#align homology.hom_to_ext homology.hom_to_ext

@[simp, reassoc.1]
theorem π'_ι : π' f g w ≫ ι f g w = kernel.ι _ ≫ cokernel.π _ :=
  by
  dsimp [π', ι, homologyIsoKernelDesc]
  simp
#align homology.π'_ι homology.π'_ι

@[simp, reassoc.1]
theorem π'_eq_π : (kernelSubobjectIso _).Hom ≫ π' f g w = π _ _ _ :=
  by
  dsimp [π', homologyIsoCokernelLift]
  simp only [← category.assoc]
  rw [iso.comp_inv_eq]
  dsimp [π, homologyIsoCokernelImageToKernel']
  simp
#align homology.π'_eq_π homology.π'_eq_π

section

variable {X' Y' Z' : A} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0)

@[simp, reassoc.1]
theorem π'_map (α β h) :
    π' _ _ _ ≫ map w w' α β h = kernel.map _ _ α.right β.right (by simp [h, β.w.symm]) ≫ π' _ _ _ :=
  by
  apply_fun fun e => (kernel_subobject_iso _).Hom ≫ e
  swap
  · intro i j hh
    apply_fun fun e => (kernel_subobject_iso _).inv ≫ e  at hh
    simpa using hh
  dsimp [map]
  simp only [π'_eq_π_assoc]
  dsimp [π]
  simp only [cokernel.π_desc]
  rw [← iso.inv_comp_eq, ← category.assoc]
  have :
    (limits.kernel_subobject_iso g).inv ≫ limits.kernel_subobject_map β =
      kernel.map _ _ β.left β.right β.w.symm ≫ (kernel_subobject_iso _).inv :=
    by
    rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv]
    ext
    dsimp
    simp
  rw [this]
  simp only [category.assoc]
  dsimp [π', homologyIsoCokernelLift]
  simp only [cokernel_iso_of_eq_inv_comp_desc, cokernel.π_desc_assoc]
  congr 1
  · congr
    exact h.symm
  · rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv]
    dsimp [homologyIsoCokernelImageToKernel']
    simp
#align homology.π'_map homology.π'_map

theorem map_eq_desc'_lift_left (α β h) :
    map w w' α β h =
      homology.desc' _ _ _ (homology.lift _ _ _ (kernel.ι _ ≫ β.left ≫ cokernel.π _) (by simp))
        (by
          ext
          simp only [← h, category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc]
          erw [← reassoc_of α.w]
          simp) :=
  by
  apply homology.hom_from_ext
  simp only [π'_map, π'_desc']
  dsimp [π', lift]
  rw [iso.eq_comp_inv]
  dsimp [homologyIsoKernelDesc]
  ext
  simp [h]
#align homology.map_eq_desc'_lift_left homology.map_eq_desc'_lift_left

theorem map_eq_lift_desc'_left (α β h) :
    map w w' α β h =
      homology.lift _ _ _
        (homology.desc' _ _ _ (kernel.ι _ ≫ β.left ≫ cokernel.π _)
          (by
            simp only [kernel.lift_ι_assoc, ← h]
            erw [← reassoc_of α.w]
            simp))
        (by
          ext
          simp) :=
  by
  rw [map_eq_desc'_lift_left]
  ext
  simp
#align homology.map_eq_lift_desc'_left homology.map_eq_lift_desc'_left

theorem map_eq_desc'_lift_right (α β h) :
    map w w' α β h =
      homology.desc' _ _ _ (homology.lift _ _ _ (kernel.ι _ ≫ α.right ≫ cokernel.π _) (by simp [h]))
        (by
          ext
          simp only [category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc]
          erw [← reassoc_of α.w]
          simp) :=
  by
  rw [map_eq_desc'_lift_left]
  ext
  simp [h]
#align homology.map_eq_desc'_lift_right homology.map_eq_desc'_lift_right

theorem map_eq_lift_desc'_right (α β h) :
    map w w' α β h =
      homology.lift _ _ _
        (homology.desc' _ _ _ (kernel.ι _ ≫ α.right ≫ cokernel.π _)
          (by
            simp only [kernel.lift_ι_assoc]
            erw [← reassoc_of α.w]
            simp))
        (by
          ext
          simp [h]) :=
  by
  rw [map_eq_desc'_lift_right]
  ext
  simp
#align homology.map_eq_lift_desc'_right homology.map_eq_lift_desc'_right

@[simp, reassoc.1]
theorem map_ι (α β h) :
    map w w' α β h ≫ ι f' g' w' =
      ι f g w ≫ cokernel.map f f' α.left β.left (by simp [h, β.w.symm]) :=
  by
  rw [map_eq_lift_desc'_left, lift_ι]
  ext
  simp only [← category.assoc]
  rw [π'_ι, π'_desc', category.assoc, category.assoc, cokernel.π_desc]
#align homology.map_ι homology.map_ι

end

end homology

namespace CategoryTheory.Functor

variable {ι : Type _} {c : ComplexShape ι} {B : Type _} [Category B] [Abelian B] (F : A ⥤ B)
  [Functor.Additive F] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- When `F` is an exact additive functor, `F(Hᵢ(X)) ≅ Hᵢ(F(X))` for `X` a complex. -/
noncomputable def homologyIso (C : HomologicalComplex A c) (j : ι) :
    F.obj (C.homology j) ≅ ((F.mapHomologicalComplex _).obj C).homology j :=
  (PreservesCokernel.iso _ _).trans
    (cokernel.mapIso _ _
      ((F.mapIso (imageSubobjectIso _)).trans
        ((PreservesImage.iso _ _).symm.trans (imageSubobjectIso _).symm))
      ((F.mapIso (kernelSubobjectIso _)).trans
        ((PreservesKernel.iso _ _).trans (kernelSubobjectIso _).symm))
      (by
        dsimp
        ext
        simp only [category.assoc, imageToKernel_arrow]
        erw [kernel_subobject_arrow', kernel_comparison_comp_ι, image_subobject_arrow']
        simp [← F.map_comp]))
#align category_theory.functor.homology_iso CategoryTheory.Functor.homologyIso

/-- If `F` is an exact additive functor, then `F` commutes with `Hᵢ` (up to natural isomorphism). -/
noncomputable def homologyFunctorIso (i : ι) :
    homologyFunctor A c i ⋙ F ≅ F.mapHomologicalComplex c ⋙ homologyFunctor B c i :=
  NatIso.ofComponents (fun X => homologyIso F X i)
    (by
      intro X Y f
      dsimp
      rw [← iso.inv_comp_eq, ← category.assoc, ← iso.eq_comp_inv]
      refine' coequalizer.hom_ext _
      dsimp [homology_iso]
      simp only [homology.map, ← category.assoc, cokernel.π_desc]
      simp only [category.assoc, cokernel_comparison_map_desc, cokernel.π_desc,
        π_comp_cokernel_comparison, ← F.map_comp]
      erw [← kernel_subobject_iso_comp_kernel_map_assoc]
      simp only [HomologicalComplex.Hom.sqFrom_right, HomologicalComplex.Hom.sqFrom_left,
        F.map_homological_complex_map_f, F.map_comp]
      dsimp only [HomologicalComplex.dFrom, HomologicalComplex.Hom.next]
      dsimp
      rw [kernel_map_comp_preserves_kernel_iso_inv_assoc, ← F.map_comp_assoc, ←
        kernel_map_comp_kernel_subobject_iso_inv]
      any_goals simp)
#align category_theory.functor.homology_functor_iso CategoryTheory.Functor.homologyFunctorIso

end CategoryTheory.Functor

