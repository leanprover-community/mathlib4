/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.EReal.Inv

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Big operators on extended real numbers

This file contains elementary lemmas about finite sums in `EReal`.
-/

@[expose] public section

open scoped BigOperators

open Finset

namespace EReal

variable {ι : Type*} {s : Finset ι} {f : ι → EReal} {a : EReal}

lemma sum_mul_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi,
      right_distrib_of_nonneg (hf i (by simp)) (sum_nonneg <| by grind), ih (by grind)]

lemma mul_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := by
  grind [sum_mul_of_nonneg hf (a := a)]

lemma mul_sum_of_nonneg_of_ne_top (ha : 0 ≤ a) (ha' : a ≠ ⊤) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [sum_insert hi, sum_insert hi, left_distrib_of_nonneg_of_ne_top ha ha', ih]

lemma sum_mul_of_nonneg_of_ne_top (ha : 0 ≤ a) (ha' : a ≠ ⊤) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := by
  grind [mul_sum_of_nonneg_of_ne_top ha ha']

@[simp, norm_cast]
lemma coe_finsetSum (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) :=
  map_sum Real.toERealAddHom f s

end EReal
