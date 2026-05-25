import Mathlib.Combinatorics.Quiver.MaxFlowMinCutAlt.FFNonTerminate
open FFVert
open Finset

variable (X : ℝ) (hX : X > 2)

set_option linter.style.openClassical false
open Classical in
lemma mk_out_sub_mk_in (f : FFVert → FFVert → ℝ) (v : FFVert) :
  mk_out f {v} - mk_in f {v} = ∑ u : FFVert, (f v u - f u v) := by
  have H_out : mk_out f {v} + f v v = ∑ y : FFVert, f v y := by
    unfold mk_out
    simp only [sum_singleton]
    rw [add_comm, ← sum_add_sum_compl {v}]
    simp only [subset_univ, sum_sdiff_eq_sub, sum_singleton, add_sub_cancel]
    exact Fintype.sum_eq_add_sum_compl v (f v)
  have H_in : mk_in f {v} + f v v = ∑ x : FFVert, f x v := by
    unfold mk_in
    simp only [sum_singleton]
    rw [add_comm, ← sum_add_sum_compl {v}]
    simp only [subset_univ, sum_sdiff_eq_sub, sum_singleton, add_sub_cancel]
    exact Fintype.sum_eq_add_sum_compl v fun i ↦ f i v
  have e1 : mk_out f {v} = (∑ y, f v y) - f v v := eq_sub_of_add_eq H_out
  have e2 : mk_in f {v} = (∑ x, f x v) - f v v := eq_sub_of_add_eq H_in
  rw [e1, e2, sum_sub_distrib]
  ring
