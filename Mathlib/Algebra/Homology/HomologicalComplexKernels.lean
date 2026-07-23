/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Kernels and cokernels in categories of homological complexes

-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι C : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c} (f : K ⟶ L)

set_option backward.defeqAttrib.useBackward true in
lemma hasKernel_of_hasKernel_f [∀ i, HasKernel (f.f i)] : HasKernel f :=
  have (i : ι) : HasLimit (parallelPair f 0 ⋙ eval C c i) :=
    hasLimit_of_iso (F := (parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  ⟨_, isLimitConeOfHasLimitEval _⟩

set_option backward.defeqAttrib.useBackward true in
lemma hasCokernel_of_hasCokernel_f [∀ i, HasCokernel (f.f i)] : HasCokernel f :=
  have (i : ι) : HasColimit (parallelPair f 0 ⋙ eval C c i) :=
    hasColimit_of_iso (F := (parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  ⟨_, isColimitCoconeOfHasColimitEval _⟩

set_option backward.defeqAttrib.useBackward true in
lemma eval_preservesKernel_of_hasKernel_f [∀ i, HasKernel (f.f i)] (i : ι) :
    PreservesLimit (parallelPair f 0) (eval C c i) :=
  have (i : ι) : HasLimit (parallelPair f 0 ⋙ eval C c i) :=
    hasLimit_of_iso (F := (parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  preservesLimit_of_preserves_limit_cone
    (isLimitConeOfHasLimitEval _) (limit.isLimit _)

set_option backward.defeqAttrib.useBackward true in
lemma eval_preservesCokernel_of_hasCokernel_f [∀ i, HasCokernel (f.f i)] (i : ι) :
    PreservesColimit (parallelPair f 0) (eval C c i) :=
  have (i : ι) : HasColimit (parallelPair f 0 ⋙ eval C c i) :=
    hasColimit_of_iso (F := (parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _))
  preservesColimit_of_preserves_colimit_cocone
    (isColimitCoconeOfHasColimitEval _) (colimit.isColimit _)

end HomologicalComplex
