/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Miscellany about preservations of (co)limits in monoidal categories

This file records some `PreservesColimits` instance on tensors products on monoidal categories. -/

namespace CategoryTheory.MonoidalCategory.Limits
open _root_.CategoryTheory.Limits

variable {C : Type*} [Category C] [MonoidalCategory C]
  {J : Type*} [Category J] (F : J ⥤ C)

section Colimits

/-- When `C` is braided and `tensorLeft c` preserves a colimit, then so does `tensorRight k`. -/
instance preservesColimit_of_braided_and_preservesColimit_tensor_left
    [BraidedCategory C] (c : C)
    [PreservesColimit F (tensorLeft c)] :
    PreservesColimit F (tensorRight c) :=
  preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

/-- When `C` is braided and `tensorRight c` preserves a colimit, then so does `tensorLeft k`.
We are not making this an instance to avoid an instance loop with
`preservesColimit_of_braided_and_preservesColimit_tensor_left`. -/
lemma preservesColimit_of_braided_and_preservesColimit_tensor_right
    [BraidedCategory C] (c : C)
    [PreservesColimit F (tensorRight c)] :
    PreservesColimit F (tensorLeft c) :=
  preservesColimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

lemma preservesCoLimit_curriedTensor [h : ∀ c : C, PreservesColimit F (tensorRight c)] :
    PreservesColimit F (curriedTensor C) :=
  preservesColimit_of_evaluation _ _
    (fun c ↦ inferInstanceAs (PreservesColimit F (tensorRight c)))

end Colimits

section Limits

/-- When `C` is braided and `tensorLeft c` preserves a limit, then so does `tensorRight k`. -/
instance preservesLimit_of_braided_and_preservesLimit_tensor_left
    [BraidedCategory C] (c : C)
    [PreservesLimit F (tensorLeft c)] :
    PreservesLimit F (tensorRight c) :=
  preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c)

/-- When `C` is braided and `tensorRight c` preserves a limit, then so does `tensorLeft k`.
We are not making this an instance to avoid an instance loop with
`preservesLimit_of_braided_and_preservesLimit_tensor_left`. -/
lemma preservesLimit_of_braided_and_preservesLimit_tensor_right
    [BraidedCategory C] (c : C)
    [PreservesLimit F (tensorRight c)] :
    PreservesLimit F (tensorLeft c) :=
  preservesLimit_of_natIso F (BraidedCategory.tensorLeftIsoTensorRight c).symm

lemma preservesLimit_curriedTensor [h : ∀ c : C, PreservesLimit F (tensorRight c)] :
    PreservesLimit F (curriedTensor C) :=
  preservesLimit_of_evaluation _ _ <| fun c ↦ inferInstanceAs (PreservesLimit F (tensorRight c))

end Limits

end CategoryTheory.MonoidalCategory.Limits
