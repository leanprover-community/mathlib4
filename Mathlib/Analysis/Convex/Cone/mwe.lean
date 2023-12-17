import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.BigOperators

open BigOperators

variable {𝕜 : Type*} {E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

example (t : Finset E) (g : t → 𝕜) :
  ∑ i : t, g i = ∑ i in t, Function.extend Subtype.val g 0 i := by
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl ?_
  rintro x -
  rw [Function.Injective.extend_apply]
  exact Subtype.val_injective
