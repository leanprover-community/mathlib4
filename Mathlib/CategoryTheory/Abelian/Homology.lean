/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Amelia Livingston
-/
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Abelian.Pseudoelements
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images

#align_import category_theory.abelian.homology from "leanprover-community/mathlib"@"956af7c76589f444f2e1313911bad16366ea476d"

/-!

The object `homology' f g w`, where `w : f ≫ g = 0`, can be identified with either a
cokernel or a kernel. The isomorphism with a cokernel is `homology'IsoCokernelLift`, which
was obtained elsewhere. In the case of an abelian category, this file shows the isomorphism
with a kernel as well.

We use these isomorphisms to obtain the analogous api for `homology'`:
- `homology'.ι` is the map from `homology' f g w` into the cokernel of `f`.
- `homology'.π'` is the map from `kernel g` to `homology' f g w`.
- `homology'.desc'` constructs a morphism from `homology' f g w`, when it is viewed as a cokernel.
- `homology'.lift` constructs a morphism to `homology' f g w`, when it is viewed as a kernel.
- Various small lemmas are proved as well, mimicking the API for (co)kernels.
With these definitions and lemmas, the isomorphisms between homology and a (co)kernel need not
be used directly.

Note: As part of the homology refactor, it is planned to remove the definitions in this file,
because it can be replaced by the content of `Algebra.Homology.ShortComplex.Homology`.

-/


open CategoryTheory.Limits

open CategoryTheory

noncomputable section

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)

namespace CategoryTheory.Abelian

/-- The cokernel of `kernel.lift g f w`. This is isomorphic to `homology f g w`.
  See `homologyIsoCokernelLift`. -/
abbrev homologyC : A :=
  cokernel (kernel.lift g f w)
#align category_theory.abelian.homology_c CategoryTheory.Abelian.homologyC

/-- The kernel of `cokernel.desc f g w`. This is isomorphic to `homology f g w`.
  See `homologyIsoKernelDesc`. -/
abbrev homologyK : A :=
  kernel (cokernel.desc f g w)
#align category_theory.abelian.homology_k CategoryTheory.Abelian.homologyK

/-- The canonical map from `homologyC` to `homologyK`.
  This is an isomorphism, and it is used in obtaining the API for `homology f g w`
  in the bottom of this file. -/
abbrev homologyCToK : homologyC f g w ⟶ homologyK f g w :=
  cokernel.desc _ (kernel.lift _ (kernel.ι _ ≫ cokernel.π _) (by simp)) (by ext; simp)
#align category_theory.abelian.homology_c_to_k CategoryTheory.Abelian.homologyCToK

attribute [local instance] Pseudoelement.homToFun Pseudoelement.hasZero

instance : Mono (homologyCToK f g w) := by
  apply Pseudoelement.mono_of_zero_of_map_zero
  intro a ha
  obtain ⟨a, rfl⟩ := Pseudoelement.pseudo_surjective_of_epi (cokernel.π (kernel.lift g f w)) a
  apply_fun kernel.ι (cokernel.desc f g w) at ha
  simp only [← Pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι,
    Pseudoelement.apply_zero] at ha
  simp only [Pseudoelement.comp_apply] at ha
  obtain ⟨b, hb⟩ : ∃ b, f b = _ := (Pseudoelement.pseudo_exact_of_exact (exact_cokernel f)).2 _ ha
  rsuffices ⟨c, rfl⟩ : ∃ c, kernel.lift g f w c = a
  · simp [← Pseudoelement.comp_apply]
  use b
  apply_fun kernel.ι g
  swap; · apply Pseudoelement.pseudo_injective_of_mono
  simpa [← Pseudoelement.comp_apply]

instance : Epi (homologyCToK f g w) := by
  apply Pseudoelement.epi_of_pseudo_surjective
  intro a
  let b := kernel.ι (cokernel.desc f g w) a
  obtain ⟨c, hc⟩ : ∃ c, cokernel.π f c = b := by
    apply Pseudoelement.pseudo_surjective_of_epi (cokernel.π f)
  have : g c = 0 := by
    rw [show g = cokernel.π f ≫ cokernel.desc f g w by simp, Pseudoelement.comp_apply, hc]
    simp [b, ← Pseudoelement.comp_apply]
  obtain ⟨d, hd⟩ : ∃ d, kernel.ι g d = c := by
    apply (Pseudoelement.pseudo_exact_of_exact exact_kernel_ι).2 _ this
  use cokernel.π (kernel.lift g f w) d
  apply_fun kernel.ι (cokernel.desc f g w)
  swap
  · apply Pseudoelement.pseudo_injective_of_mono
  simp only [← Pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι]
  simp only [Pseudoelement.comp_apply, hd, hc]

instance (w : f ≫ g = 0) : IsIso (homologyCToK f g w) :=
  isIso_of_mono_of_epi _

end CategoryTheory.Abelian

/-- The homology associated to `f` and `g` is isomorphic to a kernel. -/
def homology'IsoKernelDesc : homology' f g w ≅ kernel (cokernel.desc f g w) :=
  homology'IsoCokernelLift _ _ _ ≪≫ asIso (CategoryTheory.Abelian.homologyCToK _ _ _)
#align homology_iso_kernel_desc homology'IsoKernelDesc

namespace homology'

-- `homology'.π` is taken
/-- The canonical map from the kernel of `g` to the homology of `f` and `g`. -/
def π' : kernel g ⟶ homology' f g w :=
  cokernel.π _ ≫ (homology'IsoCokernelLift _ _ _).inv
#align homology.π' homology'.π'

/-- The canonical map from the homology of `f` and `g` to the cokernel of `f`. -/
def ι : homology' f g w ⟶ cokernel f :=
  (homology'IsoKernelDesc _ _ _).hom ≫ kernel.ι _
#align homology.ι homology'.ι

/-- Obtain a morphism from the homology, given a morphism from the kernel. -/
def desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) : homology' f g w ⟶ W :=
  (homology'IsoCokernelLift _ _ _).hom ≫ cokernel.desc _ e he
#align homology.desc' homology'.desc'

/-- Obtain a morphism to the homology, given a morphism to the kernel. -/
def lift {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) : W ⟶ homology' f g w :=
  kernel.lift _ e he ≫ (homology'IsoKernelDesc _ _ _).inv
#align homology.lift homology'.lift

@[reassoc (attr := simp)]
theorem π'_desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) :
    π' f g w ≫ desc' f g w e he = e := by
  dsimp [π', desc']
  simp
#align homology.π'_desc' homology'.π'_desc'

@[reassoc (attr := simp)]
theorem lift_ι {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) :
    lift f g w e he ≫ ι _ _ _ = e := by
  dsimp [ι, lift]
  simp
#align homology.lift_ι homology'.lift_ι

@[reassoc (attr := simp)]
theorem condition_π' : kernel.lift g f w ≫ π' f g w = 0 := by
  dsimp [π']
  simp
#align homology.condition_π' homology'.condition_π'

@[reassoc (attr := simp)]
theorem condition_ι : ι f g w ≫ cokernel.desc f g w = 0 := by
  dsimp [ι]
  simp
#align homology.condition_ι homology'.condition_ι

@[ext]
theorem hom_from_ext {W : A} (a b : homology' f g w ⟶ W)
    (h : π' f g w ≫ a = π' f g w ≫ b) : a = b := by
  dsimp [π'] at h
  apply_fun fun e => (homology'IsoCokernelLift f g w).inv ≫ e
  swap
  · intro i j hh
    apply_fun fun e => (homology'IsoCokernelLift f g w).hom ≫ e at hh
    simpa using hh
  simp only [Category.assoc] at h
  exact coequalizer.hom_ext h
#align homology.hom_from_ext homology'.hom_from_ext

@[ext]
theorem hom_to_ext {W : A} (a b : W ⟶ homology' f g w) (h : a ≫ ι f g w = b ≫ ι f g w) : a = b := by
  dsimp [ι] at h
  apply_fun fun e => e ≫ (homology'IsoKernelDesc f g w).hom
  swap
  · intro i j hh
    apply_fun fun e => e ≫ (homology'IsoKernelDesc f g w).inv at hh
    simpa using hh
  simp only [← Category.assoc] at h
  exact equalizer.hom_ext h
#align homology.hom_to_ext homology'.hom_to_ext

@[reassoc (attr := simp)]
theorem π'_ι : π' f g w ≫ ι f g w = kernel.ι _ ≫ cokernel.π _ := by
  dsimp [π', ι, homology'IsoKernelDesc]
  simp
#align homology.π'_ι homology'.π'_ι

@[reassoc (attr := simp)]
theorem π'_eq_π : (kernelSubobjectIso _).hom ≫ π' f g w = π _ _ _ := by
  dsimp [π', homology'IsoCokernelLift]
  simp only [← Category.assoc]
  rw [Iso.comp_inv_eq]
  dsimp [π, homology'IsoCokernelImageToKernel']
  simp
#align homology.π'_eq_π homology'.π'_eq_π

section

variable {X' Y' Z' : A} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0)

@[reassoc (attr := simp)]
theorem π'_map (α β h) : π' _ _ _ ≫ map w w' α β h =
    kernel.map _ _ α.right β.right (by simp [h, β.w.symm]) ≫ π' _ _ _ := by
  apply_fun fun e => (kernelSubobjectIso _).hom ≫ e
  swap
  · intro i j hh
    apply_fun fun e => (kernelSubobjectIso _).inv ≫ e at hh
    simpa using hh
  dsimp [map]
  simp only [π'_eq_π_assoc]
  dsimp [π]
  simp only [cokernel.π_desc]
  rw [← Iso.inv_comp_eq, ← Category.assoc]
  have :
    (kernelSubobjectIso g).inv ≫ kernelSubobjectMap β =
      kernel.map _ _ β.left β.right β.w.symm ≫ (kernelSubobjectIso _).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    ext
    dsimp
    simp
  rw [this]
  simp only [Category.assoc]
  dsimp [π', homology'IsoCokernelLift]
  simp only [cokernelIsoOfEq_inv_comp_desc, cokernel.π_desc_assoc]
  congr 1
  · congr
    exact h.symm
  · rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    dsimp [homology'IsoCokernelImageToKernel']
    simp
#align homology.π'_map homology'.π'_map

-- Porting note: need to fill in f,g,f',g' in the next few results or time out
theorem map_eq_desc'_lift_left (α β h) :
    map w w' α β h =
      homology'.desc' f g _ (homology'.lift f' g' _ (kernel.ι _ ≫ β.left ≫ cokernel.π _)
      (by simp)) (by
          ext
          simp only [← h, Category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc]
          erw [← reassoc_of% α.w]
          simp) := by
  apply homology'.hom_from_ext
  simp only [π'_map, π'_desc']
  dsimp [π', lift]
  rw [Iso.eq_comp_inv]
  dsimp [homology'IsoKernelDesc]
  ext
  simp [h]
#align homology.map_eq_desc'_lift_left homology'.map_eq_desc'_lift_left

theorem map_eq_lift_desc'_left (α β h) :
    map w w' α β h =
      homology'.lift f' g' _
        (homology'.desc' f g _ (kernel.ι _ ≫ β.left ≫ cokernel.π _)
          (by
            simp only [kernel.lift_ι_assoc, ← h]
            erw [← reassoc_of% α.w]
            simp))
        (by
          -- Porting note: used to be ext
          apply homology'.hom_from_ext
          simp) := by
  rw [map_eq_desc'_lift_left]
  -- Porting note: once was known as ext
  apply homology'.hom_to_ext
  apply homology'.hom_from_ext
  simp
#align homology.map_eq_lift_desc'_left homology'.map_eq_lift_desc'_left

theorem map_eq_desc'_lift_right (α β h) :
    map w w' α β h =
      homology'.desc' f g _ (homology'.lift f' g' _ (kernel.ι _ ≫ α.right ≫ cokernel.π _)
        (by simp [h]))
        (by
          ext
          simp only [Category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc]
          erw [← reassoc_of% α.w]
          simp) := by
  rw [map_eq_desc'_lift_left]
  ext
  simp [h]
#align homology.map_eq_desc'_lift_right homology'.map_eq_desc'_lift_right

theorem map_eq_lift_desc'_right (α β h) :
    map w w' α β h =
      homology'.lift f' g' _
        (homology'.desc' f g _ (kernel.ι _ ≫ α.right ≫ cokernel.π _)
          (by
            simp only [kernel.lift_ι_assoc]
            erw [← reassoc_of% α.w]
            simp))
        (by
          -- Porting note: once was known as ext
          apply homology'.hom_from_ext
          simp [h]) := by
  rw [map_eq_desc'_lift_right]
  -- Porting note: once was known as ext
  apply homology'.hom_to_ext
  apply homology'.hom_from_ext
  simp
#align homology.map_eq_lift_desc'_right homology'.map_eq_lift_desc'_right

@[reassoc (attr := simp)]
theorem map_ι (α β h) :
    map w w' α β h ≫ ι f' g' w' =
      ι f g w ≫ cokernel.map f f' α.left β.left (by simp [h, β.w.symm]) := by
  rw [map_eq_lift_desc'_left, lift_ι]
  -- Porting note: once was known as ext
  apply homology'.hom_from_ext
  simp only [← Category.assoc]
  rw [π'_ι, π'_desc', Category.assoc, Category.assoc, cokernel.π_desc]
#align homology.map_ι homology'.map_ι

end

end homology'

namespace CategoryTheory.Functor

variable {ι : Type*} {c : ComplexShape ι} {B : Type*} [Category B] [Abelian B] (F : A ⥤ B)
  [Functor.Additive F] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- When `F` is an exact additive functor, `F(Hᵢ(X)) ≅ Hᵢ(F(X))` for `X` a complex. -/
noncomputable def homology'Iso (C : HomologicalComplex A c) (j : ι) :
    F.obj (C.homology' j) ≅ ((F.mapHomologicalComplex c).obj C).homology' j :=
  (PreservesCokernel.iso F _).trans
    (cokernel.mapIso _ _
      ((F.mapIso (imageSubobjectIso _)).trans
        ((PreservesImage.iso F _).symm.trans (imageSubobjectIso _).symm))
      ((F.mapIso (kernelSubobjectIso _)).trans
        ((PreservesKernel.iso F _).trans (kernelSubobjectIso _).symm))
      (by
        dsimp
        ext
        simp only [Category.assoc, imageToKernel_arrow]
        erw [kernelSubobject_arrow', imageSubobject_arrow']
        simp [← F.map_comp]))
#align category_theory.functor.homology_iso CategoryTheory.Functor.homology'Iso

/-- If `F` is an exact additive functor, then `F` commutes with `Hᵢ` (up to natural isomorphism). -/
noncomputable def homology'FunctorIso (i : ι) :
    homology'Functor A c i ⋙ F ≅ F.mapHomologicalComplex c ⋙ homology'Functor B c i :=
  NatIso.ofComponents (fun X => homology'Iso F X i) (by
      intro X Y f
      dsimp
      rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
      refine coequalizer.hom_ext ?_
      dsimp [homology'Iso]
      simp only [PreservesCokernel.iso_inv]
      dsimp [homology'.map]
      simp only [← Category.assoc, cokernel.π_desc]
      simp only [Category.assoc, cokernelComparison_map_desc, cokernel.π_desc]
      simp only [π_comp_cokernelComparison, ← F.map_comp]
      erw [← kernelSubobjectIso_comp_kernel_map_assoc]
      simp only [HomologicalComplex.Hom.sqFrom_right, HomologicalComplex.Hom.sqFrom_left,
        F.mapHomologicalComplex_map_f, F.map_comp]
      dsimp [HomologicalComplex.dFrom, HomologicalComplex.Hom.next]
      rw [kernel_map_comp_preserves_kernel_iso_inv_assoc]
      · conv_lhs => erw [← F.map_comp_assoc]
        rw [← kernel_map_comp_kernelSubobjectIso_inv]
        · simp
      · simp)
#align category_theory.functor.homology_functor_iso CategoryTheory.Functor.homology'FunctorIso

end CategoryTheory.Functor
