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

The object `homology f g w`, where `w : f ≫ g = 0`, can be identified with either a
cokernel or a kernel. The isomorphism with a cokernel is `homologyIsoCokernelLift`, which
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
                                                                 -- 🎉 no goals
                                                                            -- ⊢ (kernel.lift g f w ≫ kernel.lift (cokernel.desc f g w) (kernel.ι g ≫ cokerne …
                                                                                 -- 🎉 no goals
#align category_theory.abelian.homology_c_to_k CategoryTheory.Abelian.homologyCToK

attribute [local instance] Pseudoelement.homToFun Pseudoelement.hasZero

instance : Mono (homologyCToK f g w) := by
  apply Pseudoelement.mono_of_zero_of_map_zero
  -- ⊢ ∀ (a : Pseudoelement (homologyC f g w)), Pseudoelement.pseudoApply (homology …
  intro a ha
  -- ⊢ a = 0
  obtain ⟨a, rfl⟩ := Pseudoelement.pseudo_surjective_of_epi (cokernel.π (kernel.lift g f w)) a
  -- ⊢ Pseudoelement.pseudoApply (cokernel.π (kernel.lift g f w)) a = 0
  apply_fun kernel.ι (cokernel.desc f g w) at ha
  -- ⊢ Pseudoelement.pseudoApply (cokernel.π (kernel.lift g f w)) a = 0
  simp only [← Pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι,
    Pseudoelement.apply_zero] at ha
  simp only [Pseudoelement.comp_apply] at ha
  -- ⊢ Pseudoelement.pseudoApply (cokernel.π (kernel.lift g f w)) a = 0
  obtain ⟨b, hb⟩ : ∃ b, f b = _ := (Pseudoelement.pseudo_exact_of_exact (exact_cokernel f)).2 _ ha
  -- ⊢ Pseudoelement.pseudoApply (cokernel.π (kernel.lift g f w)) a = 0
  rsuffices ⟨c, rfl⟩ : ∃ c, kernel.lift g f w c = a
  -- ⊢ Pseudoelement.pseudoApply (cokernel.π (kernel.lift g f w)) (Pseudoelement.ps …
  · simp [← Pseudoelement.comp_apply]
    -- 🎉 no goals
  use b
  -- ⊢ Pseudoelement.pseudoApply (kernel.lift g f w) b = a
  apply_fun kernel.ι g
  -- ⊢ Pseudoelement.pseudoApply (kernel.ι g) (Pseudoelement.pseudoApply (kernel.li …
  swap; · apply Pseudoelement.pseudo_injective_of_mono
  -- ⊢ Function.Injective (Pseudoelement.pseudoApply (kernel.ι g))
          -- 🎉 no goals
  simpa [← Pseudoelement.comp_apply]
  -- 🎉 no goals

instance : Epi (homologyCToK f g w) := by
  apply Pseudoelement.epi_of_pseudo_surjective
  -- ⊢ Function.Surjective (Pseudoelement.pseudoApply (homologyCToK f g w))
  intro a
  -- ⊢ ∃ a_1, Pseudoelement.pseudoApply (homologyCToK f g w) a_1 = a
  let b := kernel.ι (cokernel.desc f g w) a
  -- ⊢ ∃ a_1, Pseudoelement.pseudoApply (homologyCToK f g w) a_1 = a
  obtain ⟨c, hc⟩ : ∃ c, cokernel.π f c = b
  -- ⊢ ∃ c, Pseudoelement.pseudoApply (cokernel.π f) c = b
  apply Pseudoelement.pseudo_surjective_of_epi (cokernel.π f)
  -- ⊢ ∃ a_1, Pseudoelement.pseudoApply (homologyCToK f g w) a_1 = a
  have : g c = 0 := by
    rw [show g = cokernel.π f ≫ cokernel.desc f g w by simp, Pseudoelement.comp_apply, hc]
    simp [← Pseudoelement.comp_apply]
  obtain ⟨d, hd⟩ : ∃ d, kernel.ι g d = c := by
    apply (Pseudoelement.pseudo_exact_of_exact exact_kernel_ι).2 _ this
  use cokernel.π (kernel.lift g f w) d
  -- ⊢ Pseudoelement.pseudoApply (homologyCToK f g w) (Pseudoelement.pseudoApply (c …
  apply_fun kernel.ι (cokernel.desc f g w)
  -- ⊢ Pseudoelement.pseudoApply (kernel.ι (cokernel.desc f g w)) (Pseudoelement.ps …
  swap
  -- ⊢ Function.Injective (Pseudoelement.pseudoApply (kernel.ι (cokernel.desc f g w …
  · apply Pseudoelement.pseudo_injective_of_mono
    -- 🎉 no goals
  simp only [← Pseudoelement.comp_apply, cokernel.π_desc, kernel.lift_ι]
  -- ⊢ Pseudoelement.pseudoApply (kernel.ι g ≫ cokernel.π f) d = Pseudoelement.pseu …
  simp only [Pseudoelement.comp_apply, hd, hc]
  -- 🎉 no goals

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
  (homologyIsoKernelDesc _ _ _).hom ≫ kernel.ι _
#align homology.ι homology.ι

/-- Obtain a morphism from the homology, given a morphism from the kernel. -/
def desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) : homology f g w ⟶ W :=
  (homologyIsoCokernelLift _ _ _).hom ≫ cokernel.desc _ e he
#align homology.desc' homology.desc'

/-- Obtain a moprhism to the homology, given a morphism to the kernel. -/
def lift {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) : W ⟶ homology f g w :=
  kernel.lift _ e he ≫ (homologyIsoKernelDesc _ _ _).inv
#align homology.lift homology.lift

@[reassoc (attr := simp)]
theorem π'_desc' {W : A} (e : kernel g ⟶ W) (he : kernel.lift g f w ≫ e = 0) :
    π' f g w ≫ desc' f g w e he = e := by
  dsimp [π', desc']
  -- ⊢ (cokernel.π (kernel.lift g f w) ≫ (homologyIsoCokernelLift f g w).inv) ≫ (ho …
  simp
  -- 🎉 no goals
#align homology.π'_desc' homology.π'_desc'

@[reassoc (attr := simp)]
theorem lift_ι {W : A} (e : W ⟶ cokernel f) (he : e ≫ cokernel.desc f g w = 0) :
    lift f g w e he ≫ ι _ _ _ = e := by
  dsimp [ι, lift]
  -- ⊢ (kernel.lift (cokernel.desc f g w) e he ≫ (homologyIsoKernelDesc f g w).inv) …
  simp
  -- 🎉 no goals
#align homology.lift_ι homology.lift_ι

@[reassoc (attr := simp)]
theorem condition_π' : kernel.lift g f w ≫ π' f g w = 0 := by
  dsimp [π']
  -- ⊢ kernel.lift g f w ≫ cokernel.π (kernel.lift g f w) ≫ (homologyIsoCokernelLif …
  simp
  -- 🎉 no goals
#align homology.condition_π' homology.condition_π'

@[reassoc (attr := simp)]
theorem condition_ι : ι f g w ≫ cokernel.desc f g w = 0 := by
  dsimp [ι]
  -- ⊢ ((homologyIsoKernelDesc f g w).hom ≫ kernel.ι (cokernel.desc f g w)) ≫ coker …
  simp
  -- 🎉 no goals
#align homology.condition_ι homology.condition_ι

@[ext]
theorem hom_from_ext {W : A} (a b : homology f g w ⟶ W)
    (h : π' f g w ≫ a = π' f g w ≫ b) : a = b := by
  dsimp [π'] at h
  -- ⊢ a = b
  apply_fun fun e => (homologyIsoCokernelLift f g w).inv ≫ e
  -- ⊢ (fun e => (homologyIsoCokernelLift f g w).inv ≫ e) a = (fun e => (homologyIs …
  swap
  -- ⊢ Function.Injective fun e => (homologyIsoCokernelLift f g w).inv ≫ e
  · intro i j hh
    -- ⊢ i = j
    apply_fun fun e => (homologyIsoCokernelLift f g w).hom ≫ e at hh
    -- ⊢ i = j
    simpa using hh
    -- 🎉 no goals
  simp only [Category.assoc] at h
  -- ⊢ (fun e => (homologyIsoCokernelLift f g w).inv ≫ e) a = (fun e => (homologyIs …
  exact coequalizer.hom_ext h
  -- 🎉 no goals
#align homology.hom_from_ext homology.hom_from_ext

@[ext]
theorem hom_to_ext {W : A} (a b : W ⟶ homology f g w) (h : a ≫ ι f g w = b ≫ ι f g w) : a = b := by
  dsimp [ι] at h
  -- ⊢ a = b
  apply_fun fun e => e ≫ (homologyIsoKernelDesc f g w).hom
  -- ⊢ (fun e => e ≫ (homologyIsoKernelDesc f g w).hom) a = (fun e => e ≫ (homology …
  swap
  -- ⊢ Function.Injective fun e => e ≫ (homologyIsoKernelDesc f g w).hom
  · intro i j hh
    -- ⊢ i = j
    apply_fun fun e => e ≫ (homologyIsoKernelDesc f g w).inv at hh
    -- ⊢ i = j
    simpa using hh
    -- 🎉 no goals
  simp only [← Category.assoc] at h
  -- ⊢ (fun e => e ≫ (homologyIsoKernelDesc f g w).hom) a = (fun e => e ≫ (homology …
  exact equalizer.hom_ext h
  -- 🎉 no goals
#align homology.hom_to_ext homology.hom_to_ext

@[reassoc (attr := simp)]
theorem π'_ι : π' f g w ≫ ι f g w = kernel.ι _ ≫ cokernel.π _ := by
  dsimp [π', ι, homologyIsoKernelDesc]
  -- ⊢ (cokernel.π (kernel.lift g f w) ≫ (homologyIsoCokernelLift f g w).inv) ≫ ((h …
  simp
  -- 🎉 no goals
#align homology.π'_ι homology.π'_ι

@[reassoc (attr := simp)]
theorem π'_eq_π : (kernelSubobjectIso _).hom ≫ π' f g w = π _ _ _ := by
  dsimp [π', homologyIsoCokernelLift]
  -- ⊢ (kernelSubobjectIso g).hom ≫ cokernel.π (kernel.lift g f w) ≫ ((cokernelIsoO …
  simp only [← Category.assoc]
  -- ⊢ ((((kernelSubobjectIso g).hom ≫ cokernel.π (kernel.lift g f w)) ≫ (cokernelI …
  rw [Iso.comp_inv_eq]
  -- ⊢ (((kernelSubobjectIso g).hom ≫ cokernel.π (kernel.lift g f w)) ≫ (cokernelIs …
  dsimp [π, homologyIsoCokernelImageToKernel']
  -- ⊢ (((kernelSubobjectIso g).hom ≫ cokernel.π (kernel.lift g f w)) ≫ (cokernelIs …
  simp
  -- 🎉 no goals
#align homology.π'_eq_π homology.π'_eq_π

section

variable {X' Y' Z' : A} (f' : X' ⟶ Y') (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0)

@[reassoc (attr := simp)]
theorem π'_map (α β h) : π' _ _ _ ≫ map w w' α β h =
    kernel.map _ _ α.right β.right (by simp [h, β.w.symm]) ≫ π' _ _ _ := by
                                       -- 🎉 no goals
  apply_fun fun e => (kernelSubobjectIso _).hom ≫ e
  -- ⊢ (fun e => (kernelSubobjectIso g).hom ≫ e) (π' f g w ≫ map w w' α β h) = (fun …
  swap
  -- ⊢ Function.Injective fun e => (kernelSubobjectIso g).hom ≫ e
  · intro i j hh
    -- ⊢ i = j
    apply_fun fun e => (kernelSubobjectIso _).inv ≫ e at hh
    -- ⊢ i = j
    simpa using hh
    -- 🎉 no goals
  dsimp [map]
  -- ⊢ (kernelSubobjectIso g).hom ≫ π' f g w ≫ cokernel.desc (imageToKernel f g w)  …
  simp only [π'_eq_π_assoc]
  -- ⊢ π f g w ≫ cokernel.desc (imageToKernel f g w) (kernelSubobjectMap β ≫ cokern …
  dsimp [π]
  -- ⊢ cokernel.π (imageToKernel f g w) ≫ cokernel.desc (imageToKernel f g w) (kern …
  simp only [cokernel.π_desc]
  -- ⊢ kernelSubobjectMap β ≫ cokernel.π (imageToKernel f' g' w') = (kernelSubobjec …
  rw [← Iso.inv_comp_eq, ← Category.assoc]
  -- ⊢ ((kernelSubobjectIso g).inv ≫ kernelSubobjectMap β) ≫ cokernel.π (imageToKer …
  have :
    (kernelSubobjectIso g).inv ≫ kernelSubobjectMap β =
      kernel.map _ _ β.left β.right β.w.symm ≫ (kernelSubobjectIso _).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    ext
    dsimp
    simp
  rw [this]
  -- ⊢ (kernel.map (Arrow.mk g).hom (Arrow.mk g').hom β.left β.right (_ : (Arrow.mk …
  simp only [Category.assoc]
  -- ⊢ kernel.map (Arrow.mk g).hom (Arrow.mk g').hom β.left β.right (_ : (Arrow.mk  …
  dsimp [π', homologyIsoCokernelLift]
  -- ⊢ kernel.map g g' β.left β.right (_ : g ≫ β.right = β.left ≫ g') ≫ (kernelSubo …
  simp only [cokernelIsoOfEq_inv_comp_desc, cokernel.π_desc_assoc]
  -- ⊢ kernel.map g g' β.left β.right (_ : g ≫ β.right = β.left ≫ g') ≫ (kernelSubo …
  congr 1
  -- ⊢ kernel.map g g' β.left β.right (_ : g ≫ β.right = β.left ≫ g') = kernel.map  …
  · congr
    -- ⊢ β.left = α.right
    exact h.symm
    -- 🎉 no goals
  · rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    -- ⊢ cokernel.π (imageToKernel f' g' w') ≫ (homologyIsoCokernelImageToKernel' f'  …
    dsimp [homologyIsoCokernelImageToKernel']
    -- ⊢ cokernel.π (imageToKernel f' g' w') ≫ cokernel.map (imageToKernel f' g' w')  …
    simp
    -- 🎉 no goals
#align homology.π'_map homology.π'_map

-- Porting note: need to fill in f,g,f',g' in the next few results or time out
theorem map_eq_desc'_lift_left (α β h) :
    map w w' α β h =
      homology.desc' f g _ (homology.lift f' g' _ (kernel.ι _ ≫ β.left ≫ cokernel.π _)
      (by simp)) (by
          -- 🎉 no goals
          ext
          -- ⊢ (kernel.lift g f w ≫ lift f' g' w' (kernel.ι g ≫ β.left ≫ cokernel.π f') (_  …
          simp only [← h, Category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc]
          -- ⊢ f ≫ α.right ≫ cokernel.π f' = 0
          erw [← reassoc_of% α.w]
          -- ⊢ α.left ≫ (Arrow.mk f').hom ≫ cokernel.π f' = 0
          simp) := by
          -- 🎉 no goals
  apply homology.hom_from_ext
  -- ⊢ π' f g w ≫ map w w' α β h = π' f g w ≫ desc' f g w (lift f' g' w' (kernel.ι  …
  simp only [π'_map, π'_desc']
  -- ⊢ kernel.map g g' α.right β.right (_ : g ≫ β.right = α.right ≫ g') ≫ π' f' g'  …
  dsimp [π', lift]
  -- ⊢ kernel.map g g' α.right β.right (_ : g ≫ β.right = α.right ≫ g') ≫ cokernel. …
  rw [Iso.eq_comp_inv]
  -- ⊢ (kernel.map g g' α.right β.right (_ : g ≫ β.right = α.right ≫ g') ≫ cokernel …
  dsimp [homologyIsoKernelDesc]
  -- ⊢ (kernel.map g g' α.right β.right (_ : g ≫ β.right = α.right ≫ g') ≫ cokernel …
  ext
  -- ⊢ ((kernel.map g g' α.right β.right (_ : g ≫ β.right = α.right ≫ g') ≫ cokerne …
  simp [h]
  -- 🎉 no goals
#align homology.map_eq_desc'_lift_left homology.map_eq_desc'_lift_left

theorem map_eq_lift_desc'_left (α β h) :
    map w w' α β h =
      homology.lift f' g' _
        (homology.desc' f g _ (kernel.ι _ ≫ β.left ≫ cokernel.π _)
          (by
            simp only [kernel.lift_ι_assoc, ← h]
            -- ⊢ f ≫ α.right ≫ cokernel.π f' = 0
            erw [← reassoc_of% α.w]
            -- ⊢ α.left ≫ (Arrow.mk f').hom ≫ cokernel.π f' = 0
            simp))
            -- 🎉 no goals
        (by
          -- Porting note: used to be ext
          apply homology.hom_from_ext
          -- ⊢ π' f g w ≫ desc' f g w (kernel.ι g ≫ β.left ≫ cokernel.π f') (_ : kernel.lif …
          simp) := by
          -- 🎉 no goals
  rw [map_eq_desc'_lift_left]
  -- ⊢ desc' f g w (lift f' g' w' (kernel.ι g ≫ β.left ≫ cokernel.π f') (_ : (kerne …
  -- Porting note: once was known as ext
  apply homology.hom_to_ext
  -- ⊢ desc' f g w (lift f' g' w' (kernel.ι g ≫ β.left ≫ cokernel.π f') (_ : (kerne …
  apply homology.hom_from_ext
  -- ⊢ π' f g w ≫ desc' f g w (lift f' g' w' (kernel.ι g ≫ β.left ≫ cokernel.π f')  …
  simp
  -- 🎉 no goals
#align homology.map_eq_lift_desc'_left homology.map_eq_lift_desc'_left

theorem map_eq_desc'_lift_right (α β h) :
    map w w' α β h =
      homology.desc' f g _ (homology.lift f' g' _ (kernel.ι _ ≫ α.right ≫ cokernel.π _)
        (by simp [h]))
            -- 🎉 no goals
        (by
          ext
          -- ⊢ (kernel.lift g f w ≫ lift f' g' w' (kernel.ι g ≫ α.right ≫ cokernel.π f') (_ …
          simp only [Category.assoc, zero_comp, lift_ι, kernel.lift_ι_assoc]
          -- ⊢ f ≫ α.right ≫ cokernel.π f' = 0
          erw [← reassoc_of% α.w]
          -- ⊢ α.left ≫ (Arrow.mk f').hom ≫ cokernel.π f' = 0
          simp) := by
          -- 🎉 no goals
  rw [map_eq_desc'_lift_left]
  -- ⊢ desc' f g w (lift f' g' w' (kernel.ι g ≫ β.left ≫ cokernel.π f') (_ : (kerne …
  ext
  -- ⊢ (π' f g w ≫ desc' f g w (lift f' g' w' (kernel.ι g ≫ β.left ≫ cokernel.π f') …
  simp [h]
  -- 🎉 no goals
#align homology.map_eq_desc'_lift_right homology.map_eq_desc'_lift_right

theorem map_eq_lift_desc'_right (α β h) :
    map w w' α β h =
      homology.lift f' g' _
        (homology.desc' f g _ (kernel.ι _ ≫ α.right ≫ cokernel.π _)
          (by
            simp only [kernel.lift_ι_assoc]
            -- ⊢ f ≫ α.right ≫ cokernel.π f' = 0
            erw [← reassoc_of% α.w]
            -- ⊢ α.left ≫ (Arrow.mk f').hom ≫ cokernel.π f' = 0
            simp))
            -- 🎉 no goals
        (by
          -- Porting note: once was known as ext
          apply homology.hom_from_ext
          -- ⊢ π' f g w ≫ desc' f g w (kernel.ι g ≫ α.right ≫ cokernel.π f') (_ : kernel.li …
          simp [h]) := by
          -- 🎉 no goals
  rw [map_eq_desc'_lift_right]
  -- ⊢ desc' f g w (lift f' g' w' (kernel.ι g ≫ α.right ≫ cokernel.π f') (_ : (kern …
  -- Porting note: once was known as ext
  apply homology.hom_to_ext
  -- ⊢ desc' f g w (lift f' g' w' (kernel.ι g ≫ α.right ≫ cokernel.π f') (_ : (kern …
  apply homology.hom_from_ext
  -- ⊢ π' f g w ≫ desc' f g w (lift f' g' w' (kernel.ι g ≫ α.right ≫ cokernel.π f') …
  simp
  -- 🎉 no goals
#align homology.map_eq_lift_desc'_right homology.map_eq_lift_desc'_right

@[reassoc (attr := simp)]
theorem map_ι (α β h) :
    map w w' α β h ≫ ι f' g' w' =
      ι f g w ≫ cokernel.map f f' α.left β.left (by simp [h, β.w.symm]) := by
                                                    -- 🎉 no goals
  rw [map_eq_lift_desc'_left, lift_ι]
  -- ⊢ desc' f g w (kernel.ι g ≫ β.left ≫ cokernel.π f') (_ : kernel.lift g f w ≫ k …
  -- Porting note: once was known as ext
  apply homology.hom_from_ext
  -- ⊢ π' f g w ≫ desc' f g w (kernel.ι g ≫ β.left ≫ cokernel.π f') (_ : kernel.lif …
  simp only [← Category.assoc]
  -- ⊢ π' f g w ≫ desc' f g w ((kernel.ι g ≫ β.left) ≫ cokernel.π f') (_ : kernel.l …
  rw [π'_ι, π'_desc', Category.assoc, Category.assoc, cokernel.π_desc]
  -- 🎉 no goals
#align homology.map_ι homology.map_ι

end

end homology

namespace CategoryTheory.Functor

variable {ι : Type*} {c : ComplexShape ι} {B : Type*} [Category B] [Abelian B] (F : A ⥤ B)
  [Functor.Additive F] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- When `F` is an exact additive functor, `F(Hᵢ(X)) ≅ Hᵢ(F(X))` for `X` a complex. -/
noncomputable def homologyIso (C : HomologicalComplex A c) (j : ι) :
    F.obj (C.homology j) ≅ ((F.mapHomologicalComplex c).obj C).homology j :=
  (PreservesCokernel.iso F _).trans
    (cokernel.mapIso _ _
      ((F.mapIso (imageSubobjectIso _)).trans
        ((PreservesImage.iso F _).symm.trans (imageSubobjectIso _).symm))
      ((F.mapIso (kernelSubobjectIso _)).trans
        ((PreservesKernel.iso F _).trans (kernelSubobjectIso _).symm))
      (by
        dsimp
        -- ⊢ F.map (imageToKernel (HomologicalComplex.dTo C j) (HomologicalComplex.dFrom  …
        ext
        -- ⊢ (F.map (imageToKernel (HomologicalComplex.dTo C j) (HomologicalComplex.dFrom …
        simp only [Category.assoc, imageToKernel_arrow]
        -- ⊢ F.map (imageToKernel (HomologicalComplex.dTo C j) (HomologicalComplex.dFrom  …
        erw [kernelSubobject_arrow', imageSubobject_arrow']
        -- ⊢ F.map (imageToKernel (HomologicalComplex.dTo C j) (HomologicalComplex.dFrom  …
        simp [← F.map_comp]))
        -- 🎉 no goals
#align category_theory.functor.homology_iso CategoryTheory.Functor.homologyIso

/-- If `F` is an exact additive functor, then `F` commutes with `Hᵢ` (up to natural isomorphism). -/
noncomputable def homologyFunctorIso (i : ι) :
    homologyFunctor A c i ⋙ F ≅ F.mapHomologicalComplex c ⋙ homologyFunctor B c i :=
  NatIso.ofComponents (fun X => homologyIso F X i) (by
      intro X Y f
      -- ⊢ (homologyFunctor A c i ⋙ F).map f ≫ ((fun X => homologyIso F X i) Y).hom = ( …
      dsimp
      -- ⊢ F.map (homology.map (_ : HomologicalComplex.dTo X i ≫ HomologicalComplex.dFr …
      rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
      -- ⊢ (homologyIso F X i).inv ≫ F.map (homology.map (_ : HomologicalComplex.dTo X  …
      refine' coequalizer.hom_ext _
      -- ⊢ coequalizer.π (imageToKernel (HomologicalComplex.dTo ((mapHomologicalComplex …
      dsimp [homologyIso]
      -- ⊢ cokernel.π (imageToKernel (F.map (HomologicalComplex.d X (ComplexShape.prev  …
      simp only [PreservesCokernel.iso_inv]
      -- ⊢ cokernel.π (imageToKernel (F.map (HomologicalComplex.d X (ComplexShape.prev  …
      dsimp [homology.map]
      -- ⊢ cokernel.π (imageToKernel (F.map (HomologicalComplex.d X (ComplexShape.prev  …
      simp only [← Category.assoc, cokernel.π_desc]
      -- ⊢ (((((kernelSubobjectIso (F.map (HomologicalComplex.dFrom X i))).hom ≫ (Prese …
      simp only [Category.assoc, cokernelComparison_map_desc, cokernel.π_desc]
      -- ⊢ (kernelSubobjectIso (F.map (HomologicalComplex.dFrom X i))).hom ≫ (Preserves …
      simp only [π_comp_cokernelComparison, ← F.map_comp]
      -- ⊢ (kernelSubobjectIso (F.map (HomologicalComplex.dFrom X i))).hom ≫ (Preserves …
      erw [← kernelSubobjectIso_comp_kernel_map_assoc]
      -- ⊢ (kernelSubobjectIso (F.map (HomologicalComplex.dFrom X i))).hom ≫ (Preserves …
      simp only [HomologicalComplex.Hom.sqFrom_right, HomologicalComplex.Hom.sqFrom_left,
        F.mapHomologicalComplex_map_f, F.map_comp]
      dsimp [HomologicalComplex.dFrom, HomologicalComplex.Hom.next]
      -- ⊢ (kernelSubobjectIso (F.map (HomologicalComplex.d X i (ComplexShape.next c i) …
      rw [kernel_map_comp_preserves_kernel_iso_inv_assoc]
      -- ⊢ (kernelSubobjectIso (F.map (HomologicalComplex.d X i (ComplexShape.next c i) …
      conv_lhs => erw [← F.map_comp_assoc]
      -- ⊢ (kernelSubobjectIso (F.map (HomologicalComplex.d X i (ComplexShape.next c i) …
      rotate_right; simp
      -- ⊢ HomologicalComplex.d X i (ComplexShape.next c i) ≫ HomologicalComplex.Hom.f  …
                    -- ⊢ (kernelSubobjectIso (F.map (HomologicalComplex.d X i (ComplexShape.next c i) …
      rw [← kernel_map_comp_kernelSubobjectIso_inv]
      -- ⊢ (kernelSubobjectIso (F.map (HomologicalComplex.d X i (ComplexShape.next c i) …
      any_goals simp)
      -- 🎉 no goals
#align category_theory.functor.homology_functor_iso CategoryTheory.Functor.homologyFunctorIso

end CategoryTheory.Functor
