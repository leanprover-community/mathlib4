/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Preserving (co)kernels

Constructions to relate the notions of preserving (co)kernels and reflecting (co)kernels
to concrete (co)forks.

In particular, we show that `kernel_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,0`, as well as the dual result.
-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

namespace CategoryTheory.Limits

namespace KernelFork

variable {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

@[to_dual (attr := reassoc (attr := simp))]
lemma map_condition : G.map c.ι ≫ G.map f = 0 := by
  rw [← G.map_comp, c.condition, G.map_zero]

/-- A kernel fork for `f` is mapped to a kernel fork for `G.map f` if `G` is a functor
which preserves zero morphisms. -/
@[to_dual (attr := implicit_reducible)
/-- A cokernel cofork for `f` is mapped to a cokernel cofork for `G.map f` if `G` is a functor
which preserves zero morphisms. -/]
def map : KernelFork (G.map f) :=
  KernelFork.ofι (G.map c.ι) (c.map_condition G)

@[to_dual (attr := simp) map_π]
lemma map_ι : (c.map G).ι = G.map c.ι := rfl

/-- The underlying cone of a kernel fork is mapped to a limit cone if and only if
the mapped kernel fork is limit. -/
@[to_dual
/-- The underlying cocone of a cokernel cofork is mapped to a colimit cocone if and only if
the mapped cokernel cofork is colimit. -/]
def isLimitMapConeEquiv :
    IsLimit (G.mapCone c) ≃ IsLimit (c.map G) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  · exact Cone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

/-- A limit kernel fork is mapped to a limit kernel fork by a functor `G` when this functor
preserves the corresponding limit. -/
@[to_dual
/-- A colimit cokernel cofork is mapped to a colimit cokernel cofork by a functor `G`
when this functor preserves the corresponding colimit. -/]
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
@[to_dual
/-- The map of a cokernel cofork is a colimit iff
the cokernel cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `CokernelCofork.ofπ` with `Functor.mapCocone`.

This is a variant of `isColimitMapCoconeCoforkEquiv` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/]
def isLimitMapConeForkEquiv' :
    IsLimit (G.mapCone (KernelFork.ofι h w)) ≃
      IsLimit
        (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Fork (G.map f) 0) :=
  KernelFork.isLimitMapConeEquiv _ _

/-- The property of preserving kernels expressed in terms of kernel forks.

This is a variant of `isLimitForkMapOfIsLimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/
@[to_dual
/-- The property of preserving cokernels expressed in terms of cokernel coforks.

This is a variant of `isColimitCoforkMapOfIsColimit` for equalizers,
which we can't use directly between `G.map 0 = 0` does not hold definitionally.
-/]
def isLimitForkMapOfIsLimit' [PreservesLimit (parallelPair f 0) G]
    (l : IsLimit (KernelFork.ofι h w)) :
    IsLimit
      (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitMapConeForkEquiv' G w (isLimitOfPreserves G l)

variable (f)
variable [HasKernel f]

/-- If `G` preserves kernels and `C` has them, then the fork constructed of the mapped morphisms of
a kernel fork is a limit.
-/
@[to_dual
/--
If `G` preserves cokernels and `C` has them, then the cofork constructed of the mapped morphisms of
a cokernel cofork is a colimit.
-/]
def isLimitOfHasKernelOfPreservesLimit [PreservesLimit (parallelPair f 0) G] :
    IsLimit
      (Fork.ofι (G.map (kernel.ι f))
          (by simp only [← G.map_comp, kernel.condition, comp_zero, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)

@[to_dual]
instance [PreservesLimit (parallelPair f 0) G] : HasKernel (G.map f) where
  exists_limit := ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩

variable [HasKernel (G.map f)]

insert_to_dual_translation
  CategoryTheory.Limits.PreservesKernel CategoryTheory.Limits.PreservesCokernel

/-- If the kernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
kernel of `f`.
-/
@[to_dual
/-- If the cokernel comparison map for `G` at `f` is an isomorphism, then `G` preserves the
cokernel of `f`.
-/]
lemma PreservesKernel.of_iso_comparison [i : IsIso (kernelComparison f G)] :
    PreservesLimit (parallelPair f 0) G := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  apply (isLimitMapConeForkEquiv' G (kernel.condition f)).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (kernelIsKernel (G.map f)) i

variable [PreservesLimit (parallelPair f 0) G]

/-- If `G` preserves the kernel of `f`, then the kernel comparison map for `G` at `f` is
an isomorphism.
-/
@[to_dual
/-- If `G` preserves the cokernel of `f`, then the cokernel comparison map for `G` at `f` is
an isomorphism.
-/]
def PreservesKernel.iso : G.obj (kernel f) ≅ kernel (G.map f) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (limit.isLimit _)

@[to_dual (attr := reassoc (attr := simp)) π_iso_hom]
theorem PreservesKernel.iso_inv_ι :
    (PreservesKernel.iso G f).inv ≫ G.map (kernel.ι f) = kernel.ι (G.map f) :=
  IsLimit.conePointUniqueUpToIso_inv_comp (isLimitOfHasKernelOfPreservesLimit G f)
    (limit.isLimit _) (WalkingParallelPair.zero)

@[to_dual (attr := simp) iso_inv]
theorem PreservesKernel.iso_hom : (PreservesKernel.iso G f).hom = kernelComparison f G := by
  rw [← cancel_mono (kernel.ι _)]
  simp [PreservesKernel.iso]

@[to_dual]
instance : IsIso (kernelComparison f G) := by
  rw [← PreservesKernel.iso_hom]
  infer_instance

@[to_dual (attr := reassoc) preservesCokernelIso_comp_cokernelMap]
theorem kernelMap_comp_preservesKernelIso_inv {X' Y' : C} (g : X' ⟶ Y') [HasKernel g]
    [PreservesLimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        (PreservesKernel.iso G _).inv =
      (PreservesKernel.iso G _).inv ≫ G.map (kernel.map f g p q hpq) := by
  rw [Iso.comp_inv_eq, Category.assoc, PreservesKernel.iso_hom, Iso.eq_inv_comp,
    PreservesKernel.iso_hom, kernelComparison_comp_kernel_map]

@[deprecated (since := "2026-11-17")]
alias kernel_map_comp_preserves_kernel_iso_inv := kernelMap_comp_preservesKernelIso_inv

@[deprecated (since := "2026-11-17")]
alias preserves_cokernel_iso_comp_cokernel_map := preservesCokernelIso_comp_cokernelMap

end Kernels

variable (X Y : C) (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

@[to_dual]
instance preservesKernel_zero :
    PreservesLimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := ⟨by
    have := KernelFork.IsLimit.isIso_ι c hc rfl
    refine (KernelFork.isLimitMapConeEquiv c G).symm ?_
    refine IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (G.map_zero _ _)) ?_
    exact (Fork.ext (G.mapIso (asIso (Fork.ι c))).symm (by simp))⟩

variable {X Y}

/-- The kernel of a zero map is preserved by any functor which preserves zero morphisms. -/
@[to_dual
/-- The cokernel of a zero map is preserved by any functor which preserves zero morphisms. -/]
lemma preservesKernel_zero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesLimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

variable {X Y : C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- Mapping a `zeroKernelFork` of `f : X ⟶ Y` along a functor `G` that preserves zero morphisms
is isomorphic to the `zeroKernelFork` of `G.map f`. -/
@[to_dual
/-- Mapping a `zeroCokernelCofork` of `f : X ⟶ Y` along a functor `G` that preserves zero morphisms
is isomorphic to the `zeroCokernelCofork` of `G.map f`. -/]
def mapZeroKernelFork :
    (kernel.zeroKernelFork f).map G ≅ (kernel.zeroKernelFork (G.map f)) :=
  Fork.ext G.mapZeroObject

end ZeroObject

end CategoryTheory.Limits
