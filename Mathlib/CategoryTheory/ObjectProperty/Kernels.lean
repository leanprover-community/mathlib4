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

set_option backward.isDefEq.respectTransparency false in
instance : W.kernels.IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isLimit f (KernelFork.ofι (i.inv ≫ k.ι) (by simp))
      (IsLimit.ofIsoLimit hk (Fork.ext i)) hf

/-- The property of objects that are cokernels of morphisms satisfying `W`. -/
inductive cokernels : ObjectProperty C
  | of_isColimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : CokernelCofork f) (hk : IsColimit k)
    (hf : W f) : cokernels k.pt

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
instance [P.IsClosedUnderSubobjects] : P.IsClosedUnderKernels where
  kernels_le := by
    intro _ ⟨_, k, hk, hf⟩
    letI := Fork.IsLimit.mono hk
    exact P.prop_of_mono k.ι hf.1

noncomputable instance hasLimitParallelPairInclusion [P.IsClosedUnderKernels]
    {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasKernel f.hom] :
    HasLimit (parallelPair f 0 ⋙ P.ι) :=
  hasLimit_of_iso (F := parallelPair f.hom 0) (Iso.symm (diagramIsoParallelPair _))

noncomputable instance createsKernels [P.IsClosedUnderKernels] {X Y : P.FullSubcategory}
    (f : X ⟶ Y) [HasKernel f.hom] : CreatesLimit (parallelPair f 0) P.ι := by
  fapply createsLimitFullSubcategoryInclusion'
  · exact (Cone.postcompose (Iso.symm (diagramIsoParallelPair _)).hom).obj
      (Fork.ofι (kernel.ι f.hom) (by simp))
  · exact (IsLimit.postcomposeInvEquiv _ _).symm (kernelIsKernel f.hom)
  · exact P.prop_kernel f.hom X.property Y.property

instance [P.IsClosedUnderKernels] {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasKernel f.hom] :
    HasKernel f :=
  hasLimit_of_created _ P.ι

instance [P.IsClosedUnderKernels] [HasKernels C] : HasKernels P.FullSubcategory where

/-- A property of objects satisfies `P.IsClosedUnderCokernels` if whenever `X` and `Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`. -/
@[mk_iff]
class IsClosedUnderCokernels : Prop where
  cokernels_le : (MorphismProperty.ofObjectProperty P P).cokernels ≤ P

variable [P.IsClosedUnderCokernels]

lemma prop_of_isColimit_cokernelCofork {X Y : C} {f : X ⟶ Y} {k : CokernelCofork f}
    (hk : IsColimit k) (hX : P X) (hY : P Y) : P k.pt :=
  IsClosedUnderCokernels.cokernels_le _ (.of_isColimit _ k hk ⟨hX, hY⟩)

lemma prop_cokernel {X Y : C} (f : X ⟶ Y) [HasCokernel f] (hX : P X) (hY : P Y) :
    P (cokernel f) :=
  (P.prop_of_isColimit_cokernelCofork (cokernelIsCokernel f) hX hY :)

set_option backward.isDefEq.respectTransparency false in
instance [P.IsClosedUnderQuotients] : P.IsClosedUnderCokernels where
  cokernels_le := by
    intro _ ⟨_, k, hk, hf⟩
    letI := Cofork.IsColimit.epi hk
    exact P.prop_of_epi k.π hf.2

noncomputable instance hasColimitParallelPairInclusion [P.IsClosedUnderCokernels]
    {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasCokernel f.hom] :
    HasColimit (parallelPair f 0 ⋙ P.ι) :=
  hasColimit_of_iso (F := parallelPair f.hom 0) (diagramIsoParallelPair _)

noncomputable instance createsCokernels [P.IsClosedUnderCokernels] {X Y : P.FullSubcategory}
    (f : X ⟶ Y) [HasCokernel f.hom] : CreatesColimit (parallelPair f 0) P.ι := by
  fapply createsColimitFullSubcategoryInclusion'
  · exact (Cocone.precompose (diagramIsoParallelPair _).hom).obj
      (Cofork.ofπ (cokernel.π f.hom) (by simp))
  · exact (IsColimit.precomposeHomEquiv _ _).symm (cokernelIsCokernel f.hom)
  · exact P.prop_cokernel f.hom X.property Y.property

instance [P.IsClosedUnderCokernels] {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasCokernel f.hom] :
    HasCokernel f :=
  hasColimit_of_created _ P.ι

instance [P.IsClosedUnderCokernels] [HasCokernels C] : HasCokernels P.FullSubcategory where

end ObjectProperty

end CategoryTheory
