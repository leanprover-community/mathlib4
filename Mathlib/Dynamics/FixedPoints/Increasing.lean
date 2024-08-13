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
lemma eventually_constant_monotone {ι : Type*}
    [SemilatticeSup ι] [Nonempty ι] {g : ι → α} (hg : Monotone g) :
    EventuallyConst g atTop := by
  rw [eventuallyConst_atTop]
  obtain ⟨x, hx⟩ : ∃ x, g x = _ := hα.wf.min_mem _ (Set.range_nonempty _)
  exact ⟨x, fun z hz =>
    (hg hz).eq_of_not_gt (hx ▸ hα.wf.not_lt_min _ _ (Set.mem_range_self _))⟩

/-- The theorem states that the iteration will eventually become a constant. -/
lemma eventually_constant_iterate (hf : id ≤ f) (x : α) :
    EventuallyConst (fun n => f^[n] x) atTop :=
  eventually_constant_monotone (fun _ _ h => monotone_iterate_of_id_le hf h x)

/-- The index at which the iteration sequence of `f` on `x` starts to become constant. -/
noncomputable def fixedPointIndex (hf : id ≤ f) (x : α) : ℕ :=
  (eventuallyConst_atTop.mp (eventually_constant_iterate hf x)).choose

lemma fixedPointIndex_spec (hf : id ≤ f) (x : α) :
    ∀ m ≥ fixedPointIndex hf x, f^[m] x = f^[fixedPointIndex hf x] x :=
  (eventuallyConst_atTop.mp (eventually_constant_iterate hf x)).choose_spec

/-- The eventual value of iteration of `f` on `x`. -/
noncomputable def eventualValue (hf : id ≤ f) (x : α) := f^[fixedPointIndex hf x] x

/-- The eventual value is a fixed point of `f`. -/
lemma fixed_eventualValue (hf : id ≤ f) (x : α) : IsFixedPt f (eventualValue hf x) := by
  unfold IsFixedPt
  simp only [eventualValue, ← iterate_succ_apply']
  apply fixedPointIndex_spec
  simp

/-- The eventual value is larger or equal than `x` itself. -/
lemma self_le_eventualValue (hf : id ≤ f) (x : α) : x ≤ eventualValue hf x := by
  simp only [eventualValue]
  conv_lhs => rw [show x = f^[0] x from rfl]
  apply f.monotone_iterate_of_id_le hf
  simp

end Function
