/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

#align_import category_theory.limits.preserves.shapes.kernels from "leanprover-community/mathlib"@"956af7c76589f444f2e1313911bad16366ea476d"

/-!
# Preserving (co)kernels

Constructions to relate the notions of preserving (co)kernels and reflecting (co)kernels
to concrete (co)forks.

In particular, we show that `kernel_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,0`, as well as the dual result.
-/


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

namespace CategoryTheory.Limits

namespace KernelFork

variable {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

@[reassoc (attr := simp)]
lemma map_condition : G.map c.ι ≫ G.map f = 0 := by
  rw [← G.map_comp, c.condition, G.map_zero]

/-- A kernel fork for `f` is mapped to a kernel fork for `G.map f` if `G` is a functor
which preserves zero morphisms. -/
def map : KernelFork (G.map f) :=
  KernelFork.ofι (G.map c.ι) (c.map_condition G)

@[simp]
lemma map_ι : (c.map G).ι = G.map c.ι := rfl

/-- The underlying cone of a kernel fork is mapped to a limit cone if and only if
the mapped kernel fork is limit. -/
def isLimitMapConeEquiv :
    IsLimit (G.mapCone c) ≃ IsLimit (c.map G) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cones.ext (Iso.refl _) (by rintro (_|_) <;> aesop_cat)

/-- A limit kernel fork is mapped to a limit kernel fork by a functor `G` when this functor
preserves the corresponding limit. -/
def mapIsLimit (hc : IsLimit c) (G : C ⥤ D)
    [Functor.PreservesZeroMorphisms G] [PreservesLimit (parallelPair f 0) G] :
    IsLimit (c.map G) :=
  c.isLimitMapConeEquiv G (isLimitOfPreserves G hc)

end KernelFork

section Kernels

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  {X Y Z : C} {f : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = 0)

/-- The map of a kernel fork is a limit iff
the kernel fork consisting of the mapped morphisms is a limit.
This essentially lets us commute `KernelFork.ofι` with `Functor.mapCone`.

This is a variant of `isLimitMapConeForkEquiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isLimitMapConeForkEquiv' :
    IsLimit (G.mapCone (KernelFork.ofι h w)) ≃
      IsLimit
        (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Fork (G.map f) 0) :=
  KernelFork.isLimitMapConeEquiv _ _
#align category_theory.limits.is_limit_map_cone_fork_equiv' CategoryTheory.Limits.isLimitMapConeForkEquiv'

/-- The property of preserving kernels expressed in terms of kernel forks.

This is a variant of `isLimitForkMapOfIsLimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isLimitForkMapOfIsLimit' [PreservesLimit (parallelPair f 0) G]
    (l : IsLimit (KernelFork.ofι h w)) :
    IsLimit
      (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitMapConeForkEquiv' G w (PreservesLimit.preserves l)
#align category_theory.limits.is_limit_fork_map_of_is_limit' CategoryTheory.Limits.isLimitForkMapOfIsLimit'

variable (f)
variable [HasKernel f]

/-- If `G` preserves kernels and `C` has them, then the fork constructed of the mapped morphisms of
a kernel fork is a limit.
-/
def isLimitOfHasKernelOfPreservesLimit [PreservesLimit (parallelPair f 0) G] :
    IsLimit
      (Fork.ofι (G.map (kernel.ι f))
          (by simp only [← G.map_comp, kernel.condition, comp_zero, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)
#align category_theory.limits.is_limit_of_has_kernel_of_preserves_limit CategoryTheory.Limits.isLimitOfHasKernelOfPreservesLimit

instance [PreservesLimit (parallelPair f 0) G] : HasKernel (G.map f) where
  exists_limit := ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩

variable [HasKernel (G.map f)]

/-- If the kernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
kernel of `f`.
-/
def PreservesKernel.ofIsoComparison [i : IsIso (kernelComparison f G)] :
    PreservesLimit (parallelPair f 0) G := by
  apply preservesLimitOfPreservesLimitCone (kernelIsKernel f)
  apply (isLimitMapConeForkEquiv' G (kernel.condition f)).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (kernelIsKernel (G.map f)) i
#align category_theory.limits.preserves_kernel.of_iso_comparison CategoryTheory.Limits.PreservesKernel.ofIsoComparison

variable [PreservesLimit (parallelPair f 0) G]

/-- If `G` preserves the kernel of `f`, then the kernel comparison map for `G` at `f` is
an isomorphism.
-/
def PreservesKernel.iso : G.obj (kernel f) ≅ kernel (G.map f) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (limit.isLimit _)
#align category_theory.limits.preserves_kernel.iso CategoryTheory.Limits.PreservesKernel.iso

@[simp]
theorem PreservesKernel.iso_hom : (PreservesKernel.iso G f).hom = kernelComparison f G := by
  rw [← cancel_mono (kernel.ι _)]
  simp [PreservesKernel.iso]
#align category_theory.limits.preserves_kernel.iso_hom CategoryTheory.Limits.PreservesKernel.iso_hom

instance : IsIso (kernelComparison f G) := by
  rw [← PreservesKernel.iso_hom]
  infer_instance

@[reassoc]
theorem kernel_map_comp_preserves_kernel_iso_inv {X' Y' : C} (g : X' ⟶ Y') [HasKernel g]
    [HasKernel (G.map g)] [PreservesLimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        (PreservesKernel.iso G _).inv =
      (PreservesKernel.iso G _).inv ≫ G.map (kernel.map f g p q hpq) := by
  rw [Iso.comp_inv_eq, Category.assoc, PreservesKernel.iso_hom, Iso.eq_inv_comp,
    PreservesKernel.iso_hom, kernelComparison_comp_kernel_map]
#align category_theory.limits.kernel_map_comp_preserves_kernel_iso_inv CategoryTheory.Limits.kernel_map_comp_preserves_kernel_iso_inv

end Kernels

namespace CokernelCofork

variable {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

@[reassoc (attr := simp)]
lemma map_condition : G.map f ≫ G.map c.π = 0 := by
  rw [← G.map_comp, c.condition, G.map_zero]

/-- A cokernel cofork for `f` is mapped to a cokernel cofork for `G.map f` if `G` is a functor
which preserves zero morphisms. -/
def map : CokernelCofork (G.map f) :=
  CokernelCofork.ofπ (G.map c.π) (c.map_condition G)

@[simp]
lemma map_π : (c.map G).π = G.map c.π := rfl

/-- The underlying cocone of a cokernel cofork is mapped to a colimit cocone if and only if
the mapped cokernel cofork is colimit. -/
def isColimitMapCoconeEquiv :
    IsColimit (G.mapCocone c) ≃ IsColimit (c.map G) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cocones.ext (Iso.refl _) (by rintro (_|_) <;> aesop_cat)

/-- A colimit cokernel cofork is mapped to a colimit cokernel cofork by a functor `G`
when this functor preserves the corresponding colimit. -/
def mapIsColimit  (hc : IsColimit c) (G : C ⥤ D)
    [Functor.PreservesZeroMorphisms G] [PreservesColimit (parallelPair f 0) G] :
    IsColimit (c.map G) :=
  c.isColimitMapCoconeEquiv G (isColimitOfPreserves G hc)

end CokernelCofork

section Cokernels

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  {X Y Z : C} {f : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = 0)

/-- The map of a cokernel cofork is a colimit iff
the cokernel cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `CokernelCofork.ofπ` with `Functor.mapCocone`.

This is a variant of `isColimitMapCoconeCoforkEquiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isColimitMapCoconeCoforkEquiv' :
    IsColimit (G.mapCocone (CokernelCofork.ofπ h w)) ≃
      IsColimit
        (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Cofork (G.map f) 0) :=
  CokernelCofork.isColimitMapCoconeEquiv _ _
#align category_theory.limits.is_colimit_map_cocone_cofork_equiv' CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv'

/-- The property of preserving cokernels expressed in terms of cokernel coforks.

This is a variant of `isColimitCoforkMapOfIsColimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
def isColimitCoforkMapOfIsColimit' [PreservesColimit (parallelPair f 0) G]
    (l : IsColimit (CokernelCofork.ofπ h w)) :
    IsColimit
      (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitMapCoconeCoforkEquiv' G w (PreservesColimit.preserves l)
#align category_theory.limits.is_colimit_cofork_map_of_is_colimit' CategoryTheory.Limits.isColimitCoforkMapOfIsColimit'

variable (f)
variable [HasCokernel f]

/--
If `G` preserves cokernels and `C` has them, then the cofork constructed of the mapped morphisms of
a cokernel cofork is a colimit.
-/
def isColimitOfHasCokernelOfPreservesColimit [PreservesColimit (parallelPair f 0) G] :
    IsColimit
      (Cofork.ofπ (G.map (cokernel.π f))
          (by simp only [← G.map_comp, cokernel.condition, zero_comp, Functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitCoforkMapOfIsColimit' G (cokernel.condition f) (cokernelIsCokernel f)
#align category_theory.limits.is_colimit_of_has_cokernel_of_preserves_colimit CategoryTheory.Limits.isColimitOfHasCokernelOfPreservesColimit

instance [PreservesColimit (parallelPair f 0) G] : HasCokernel (G.map f) where
  exists_colimit := ⟨⟨_, isColimitOfHasCokernelOfPreservesColimit G f⟩⟩

variable [HasCokernel (G.map f)]

/-- If the cokernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
cokernel of `f`.
-/
def PreservesCokernel.ofIsoComparison [i : IsIso (cokernelComparison f G)] :
    PreservesColimit (parallelPair f 0) G := by
  apply preservesColimitOfPreservesColimitCocone (cokernelIsCokernel f)
  apply (isColimitMapCoconeCoforkEquiv' G (cokernel.condition f)).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (cokernelIsCokernel (G.map f)) i
#align category_theory.limits.preserves_cokernel.of_iso_comparison CategoryTheory.Limits.PreservesCokernel.ofIsoComparison

variable [PreservesColimit (parallelPair f 0) G]

/-- If `G` preserves the cokernel of `f`, then the cokernel comparison map for `G` at `f` is
an isomorphism.
-/
def PreservesCokernel.iso : G.obj (cokernel f) ≅ cokernel (G.map f) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _)
#align category_theory.limits.preserves_cokernel.iso CategoryTheory.Limits.PreservesCokernel.iso

@[simp]
theorem PreservesCokernel.iso_inv : (PreservesCokernel.iso G f).inv = cokernelComparison f G := by
  rw [← cancel_epi (cokernel.π _)]
  simp [PreservesCokernel.iso]
#align category_theory.limits.preserves_cokernel.iso_inv CategoryTheory.Limits.PreservesCokernel.iso_inv

instance : IsIso (cokernelComparison f G) := by
  rw [← PreservesCokernel.iso_inv]
  infer_instance

@[reassoc]
theorem preserves_cokernel_iso_comp_cokernel_map {X' Y' : C} (g : X' ⟶ Y') [HasCokernel g]
    [HasCokernel (G.map g)] [PreservesColimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    (PreservesCokernel.iso G _).hom ≫
        cokernel.map (G.map f) (G.map g) (G.map p) (G.map q)
          (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (cokernel.map f g p q hpq) ≫ (PreservesCokernel.iso G _).hom := by
  rw [← Iso.comp_inv_eq, Category.assoc, ← Iso.eq_inv_comp, PreservesCokernel.iso_inv,
    cokernel_map_comp_cokernelComparison, PreservesCokernel.iso_inv]
#align category_theory.limits.preserves_cokernel_iso_comp_cokernel_map CategoryTheory.Limits.preserves_cokernel_iso_comp_cokernel_map

end Cokernels

variable (X Y : C) (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

noncomputable instance preservesKernelZero :
    PreservesLimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := by
    have := KernelFork.IsLimit.isIso_ι c hc rfl
    refine (KernelFork.isLimitMapConeEquiv c G).symm ?_
    refine IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (G.map_zero _ _)) ?_
    exact (Fork.ext (G.mapIso (asIso (Fork.ι c))).symm (by simp))

noncomputable instance preservesCokernelZero :
    PreservesColimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := by
    have := CokernelCofork.IsColimit.isIso_π c hc rfl
    refine (CokernelCofork.isColimitMapCoconeEquiv c G).symm ?_
    refine IsColimit.ofIsoColimit (CokernelCofork.IsColimit.ofId _ (G.map_zero _ _)) ?_
    exact (Cofork.ext (G.mapIso (asIso (Cofork.π c))) (by simp))

variable {X Y}

/-- The kernel of a zero map is preserved by any functor which preserves zero morphisms. -/
noncomputable def preservesKernelZero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesLimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance

/-- The cokernel of a zero map is preserved by any functor which preserves zero morphisms. -/
noncomputable def preservesCokernelZero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesColimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance

end CategoryTheory.Limits
