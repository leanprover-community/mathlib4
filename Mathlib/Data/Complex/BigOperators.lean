/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic

#align_import data.complex.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Finite sums and products of complex numbers

-/

namespace Complex

variable {α : Type*} (s : Finset α)

@[simp, norm_cast]
theorem ofReal_prod (f : α → ℝ) : ((∏ i ∈ s, f i : ℝ) : ℂ) = ∏ i ∈ s, (f i : ℂ) :=
  map_prod ofReal _ _
#align complex.of_real_prod Complex.ofReal_prod

@[simp, norm_cast]
theorem ofReal_sum (f : α → ℝ) : ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ) :=
  map_sum ofReal _ _
#align complex.of_real_sum Complex.ofReal_sum

@[simp]
theorem re_sum (f : α → ℂ) : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re :=
  map_sum reAddGroupHom f s
#align complex.re_sum Complex.re_sum

@[simp]
theorem im_sum (f : α → ℂ) : (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im :=
  map_sum imAddGroupHom f s
#align complex.im_sum Complex.im_sum

end Complex
