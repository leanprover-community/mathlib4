/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song, Yury Kudryashov
-/
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.Order.Iterate
import Mathlib.Order.WellFounded
import Mathlib.Data.Fintype.Card

/-!
# Fixed points of function `f` with `f(x) ≥ x`

In this file we consider the fixed points of function `f : α → α` with `f(x) ≥ x`. If `α` is
a finite type, then the sequence `x, f(x), f(f(x)), ...` will eventually be a constant.

# Main definitions
* `fixedPointIndex`: The smallest `n` such that the sequence `x, f(x), f(f(x)), ...`
  becomes a constant after this index.
* `eventuallyValue`: The value that the sequence converges to after sufficient number
  of iterations of `f` on `x`.
-/
namespace Function

open Filter
variable {α : Type*} [PartialOrder α] [hα : WellFoundedGT α] {f : α → α}

/-- The function `g : ι → α` will eventually be constant if the `>` relation on `α`
  is well-founded. -/
lemma Monotone.eventuallyConst_atTop {ι : Type*}
    [SemilatticeSup ι] [Nonempty ι] {g : ι → α} (hg : Monotone g) :
    EventuallyConst g atTop := by
  rw [Filter.eventuallyConst_atTop]
  obtain ⟨x, hx⟩ : ∃ x, g x = _ := hα.wf.min_mem _ (Set.range_nonempty _)
  exact ⟨x, fun z hz =>
    (hg hz).eq_of_not_gt (hx ▸ hα.wf.not_lt_min _ _ (Set.mem_range_self _))⟩

/-- Iterations of an inflationary endomorphisms of a cowell-founded order eventually stabilise. -/
lemma eventuallyConst_iterate_of_wellFoundedGT (hf : id ≤ f) (x : α) :
    EventuallyConst (fun n => f^[n] x) atTop :=
  Monotone.eventuallyConst_atTop (fun _ _ h => monotone_iterate_of_id_le hf h x)

/-- An index at which the sequence `f` starts to become constant. -/
noncomputable def stabilizationIndex {f : ℕ → α} (hf : EventuallyConst f atTop) :=
  (eventuallyConst_atTop.mp hf).choose

/-- An index at which the iteration sequence of `f` on `x` starts to become constant. -/
noncomputable def selfIncreasingFixedPointIndex (hf : id ≤ f) (x : α) : ℕ :=
  stabilizationIndex (eventuallyConst_iterate_of_wellFoundedGT hf x)

lemma selfIncreasingFixedPointIndex_spec (hf : id ≤ f) (x : α) :
    ∀ m ≥ selfIncreasingFixedPointIndex hf x,
      f^[m] x = f^[selfIncreasingFixedPointIndex hf x] x :=
  (eventuallyConst_atTop.mp (eventuallyConst_iterate_of_wellFoundedGT hf x)).choose_spec

/-- The eventual value of iteration of `f` on `x`. -/
noncomputable def eventualValue (hf : id ≤ f) (x : α) :=
  f^[selfIncreasingFixedPointIndex hf x] x

/-- The eventual value is a fixed point of `f`. -/
lemma isFixedPt_eventualValue (hf : id ≤ f) (x : α) : IsFixedPt f (eventualValue hf x) := by
  unfold IsFixedPt
  simp only [eventualValue, ← iterate_succ_apply']
  apply selfIncreasingFixedPointIndex_spec
  simp

/-- The eventual value is larger or equal than `x` itself. -/
lemma self_le_eventualValue (hf : id ≤ f) (x : α) : x ≤ eventualValue hf x := by
  simp only [eventualValue]
  conv_lhs => rw [← iterate_zero_apply f x]
  apply f.monotone_iterate_of_id_le hf
  simp

end Function
