/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Objects that are (co)kernels of morphisms

Given a morphism property `W` on a category, we introduce two object properties
`kernels W` and `cokernels W`, consisting of all (co)kernels of morphisms
satisfying `W`.

Given an object property `P`, we also introduce two predicates
`P.IsClosedUnderKernels` and `P.IsClosedUnderCokernels`, stating that all
(co)kernels of morphisms between objects in `P` remain in `P`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- The property of objects that are kernels of morphisms satisfying `W`. -/
inductive kernels : ObjectProperty C
  | of_isLimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : KernelFork f) (hk : IsLimit k)
    (hf : W f) : kernels k.pt

lemma nonempty_kernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasKernel f] :
    W.kernels.Nonempty :=
  ObjectProperty.nonempty_of_prop (kernels.of_isLimit f _ (kernelIsKernel f) hf)

set_option backward.defeqAttrib.useBackward true in
instance : W.kernels.IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isLimit f (KernelFork.ofι (i.inv ≫ k.ι) (by simp))
      (IsLimit.ofIsoLimit hk (Fork.ext i)) hf

/-- The property of objects that are cokernels of morphisms satisfying `W`. -/
inductive cokernels : ObjectProperty C
  | of_isColimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : CokernelCofork f) (hk : IsColimit k)
    (hf : W f) : cokernels k.pt

lemma nonempty_cokernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasCokernel f] :
    W.cokernels.Nonempty :=
  ObjectProperty.nonempty_of_prop (cokernels.of_isColimit f _ (cokernelIsCokernel f) hf)

instance : W.cokernels.IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isColimit f (CokernelCofork.ofπ (k.π ≫ i.hom) (by simp))
      (IsColimit.ofIsoColimit hk (Cofork.ext i)) hf

end MorphismProperty

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- A property of objects satisfies `P.IsClosedUnderKernels` if whenever `X` and `Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`. -/
@[mk_iff]
class IsClosedUnderKernels : Prop where
  kernels_le : (MorphismProperty.ofObjectProperty P P).kernels ≤ P

lemma prop_of_isLimit_kernelFork [P.IsClosedUnderKernels] {X Y : C} {f : X ⟶ Y} {k : KernelFork f}
    (hk : IsLimit k) (hX : P X) (hY : P Y) : P k.pt :=
  IsClosedUnderKernels.kernels_le _ (.of_isLimit _ k hk ⟨hX, hY⟩)

lemma prop_kernel [P.IsClosedUnderKernels] {X Y : C} (f : X ⟶ Y) [HasKernel f] (hX : P X)
    (hY : P Y) : P (kernel f) :=
  (P.prop_of_isLimit_kernelFork (kernelIsKernel f) hX hY :)

instance [P.IsClosedUnderSubobjects] : P.IsClosedUnderKernels where
  kernels_le := by
    intro _ ⟨_, k, hk, hf⟩
    letI := Fork.IsLimit.mono hk
    exact P.prop_of_mono k.ι hf.1

lemma hasLimit_parallelPair_comp_ι {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasKernel f.hom] :
    HasLimit (parallelPair f 0 ⋙ P.ι) :=
  hasLimit_of_iso (F := parallelPair f.hom 0) (Iso.symm (diagramIsoParallelPair _))

set_option backward.defeqAttrib.useBackward true in
/-- If an object property `P` is closed under kernels, then `P.ι` creates kernels.
In particular, this implies `P.ι` preserves kernels. -/
@[reducible]
noncomputable def createsKernels [P.IsClosedUnderKernels] {X Y : P.FullSubcategory}
    (f : X ⟶ Y) [HasKernel f.hom] : CreatesLimit (parallelPair f 0) P.ι := by
  fapply createsLimitFullSubcategoryInclusion'
  · exact (Cone.postcompose (Iso.symm (diagramIsoParallelPair _)).hom).obj
      (Fork.ofι (kernel.ι f.hom) (by simp))
  · exact (IsLimit.postcomposeInvEquiv _ _).symm (kernelIsKernel f.hom)
  · exact P.prop_kernel f.hom X.property Y.property

lemma preservesKernels_ι [HasKernels C] [P.IsClosedUnderKernels] ⦃X Y : P.FullSubcategory⦄
    (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) P.ι := by
  have := P.createsKernels f
  have := P.hasLimit_parallelPair_comp_ι f
  exact preservesLimit_of_createsLimit_and_hasLimit _ _

instance [P.IsClosedUnderKernels] [HasKernels C] : HasKernels P.FullSubcategory where
  has_limit f :=
    letI := P.createsKernels f
    letI := P.hasLimit_parallelPair_comp_ι f
    hasLimit_of_created _ P.ι

/-- A property of objects satisfies `P.IsClosedUnderCokernels` if whenever `X` and `Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`. -/
@[mk_iff]
class IsClosedUnderCokernels : Prop where
  cokernels_le : (MorphismProperty.ofObjectProperty P P).cokernels ≤ P

lemma prop_of_isColimit_cokernelCofork [P.IsClosedUnderCokernels] {X Y : C} {f : X ⟶ Y}
    {k : CokernelCofork f} (hk : IsColimit k) (hX : P X) (hY : P Y) : P k.pt :=
  IsClosedUnderCokernels.cokernels_le _ (.of_isColimit _ k hk ⟨hX, hY⟩)

lemma prop_cokernel [P.IsClosedUnderCokernels] {X Y : C} (f : X ⟶ Y) [HasCokernel f] (hX : P X)
    (hY : P Y) : P (cokernel f) :=
  (P.prop_of_isColimit_cokernelCofork (cokernelIsCokernel f) hX hY :)

instance [P.IsClosedUnderQuotients] : P.IsClosedUnderCokernels where
  cokernels_le := by
    intro _ ⟨_, k, hk, hf⟩
    letI := Cofork.IsColimit.epi hk
    exact P.prop_of_epi k.π hf.2

lemma hasColimit_parallelPair_comp_ι {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasCokernel f.hom] :
    HasColimit (parallelPair f 0 ⋙ P.ι) :=
  hasColimit_of_iso (F := parallelPair f.hom 0) (diagramIsoParallelPair _)

set_option backward.defeqAttrib.useBackward true in
/-- If an object property `P` is closed under cokernels, then `P.ι` creates cokernels.
In particular, this implies `P.ι` preserves cokernels. -/
@[reducible]
noncomputable def createsCokernels [P.IsClosedUnderCokernels] {X Y : P.FullSubcategory}
    (f : X ⟶ Y) [HasCokernel f.hom] : CreatesColimit (parallelPair f 0) P.ι := by
  fapply createsColimitFullSubcategoryInclusion'
  · exact (Cocone.precompose (diagramIsoParallelPair _).hom).obj
      (Cofork.ofπ (cokernel.π f.hom) (by simp))
  · exact (IsColimit.precomposeHomEquiv _ _).symm (cokernelIsCokernel f.hom)
  · exact P.prop_cokernel f.hom X.property Y.property

lemma preservesCokernels_ι [HasCokernels C] [P.IsClosedUnderCokernels] ⦃X Y : P.FullSubcategory⦄
    (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) P.ι := by
  have := P.createsCokernels f
  have := P.hasColimit_parallelPair_comp_ι f
  exact preservesColimit_of_createsColimit_and_hasColimit _ _

instance [P.IsClosedUnderCokernels] [HasCokernels C] : HasCokernels P.FullSubcategory where
  has_colimit f :=
    letI := P.createsCokernels f
    letI := P.hasColimit_parallelPair_comp_ι f
    hasColimit_of_created _ P.ι

end ObjectProperty

end CategoryTheory
