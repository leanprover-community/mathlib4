/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ENNReal.Inv

/-!
# Properties of big operators extended non-negative real numbers

In this file we prove elementary properties of sums and products on `ℝ≥0∞`, as well as how these
interact with the order structure on `ℝ≥0∞`.
-/

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

section OperationsAndInfty

variable {α : Type*}

@[simp, norm_cast]
theorem coe_finset_sum {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a ∈ s, f a) = ∑ a ∈ s, (f a : ℝ≥0∞) :=
  map_sum ofNNRealHom f s

@[simp, norm_cast]
theorem coe_finset_prod {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℝ≥0∞) :=
  map_prod ofNNRealHom f s

@[simp]
theorem toNNReal_prod {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i ∈ s, f i).toNNReal = ∏ i ∈ s, (f i).toNNReal :=
  map_prod toNNRealHom _ _

@[simp]
theorem toReal_prod {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i ∈ s, f i).toReal = ∏ i ∈ s, (f i).toReal :=
  map_prod toRealHom _ _

theorem ofReal_prod_of_nonneg {α : Type*} {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_prod, coe_inj]
  exact Real.toNNReal_prod_of_nonneg hf

theorem iInf_sum {ι α : Type*} {f : ι → α → ℝ≥0∞} {s : Finset α} [Nonempty ι]
    (h : ∀ (t : Finset α) (i j : ι), ∃ k, ∀ a ∈ t, f k a ≤ f i a ∧ f k a ≤ f j a) :
    ⨅ i, ∑ a ∈ s, f i a = ∑ a ∈ s, ⨅ i, f i a := by
  induction s using Finset.cons_induction_on with
  | empty => simp only [Finset.sum_empty, ciInf_const]
  | cons a s ha ih =>
    simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)

end OperationsAndInfty

section Sum

open Finset

variable {α : Type*} {s : Finset α} {f : α → ℝ≥0∞}

/-- A product of finite numbers is still finite. -/
lemma prod_ne_top (h : ∀ a ∈ s, f a ≠ ∞) : ∏ a ∈ s, f a ≠ ∞ := WithTop.prod_ne_top h

/-- A product of finite numbers is still finite. -/
lemma prod_lt_top (h : ∀ a ∈ s, f a < ∞) : ∏ a ∈ s, f a < ∞ := WithTop.prod_lt_top h

/-- A sum is infinite iff one of the summands is infinite. -/
@[simp] lemma sum_eq_top : ∑ x ∈ s, f x = ∞ ↔ ∃ a ∈ s, f a = ∞ := WithTop.sum_eq_top

/-- A sum is finite iff all summands are finite. -/
lemma sum_ne_top : ∑ a ∈ s, f a ≠ ∞ ↔ ∀ a ∈ s, f a ≠ ∞ := WithTop.sum_ne_top

/-- A sum is finite iff all summands are finite. -/
@[simp] lemma sum_lt_top : ∑ a ∈ s, f a < ∞ ↔ ∀ a ∈ s, f a < ∞ := WithTop.sum_lt_top

theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∑ x ∈ s, f x ≠ ∞) {a : α}
    (ha : a ∈ s) : f a < ∞ :=
  sum_lt_top.1 h.lt_top a ha

/-- Seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity -/
theorem toNNReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toNNReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.toNNReal (f a) := by
  rw [← coe_inj, coe_toNNReal, coe_finset_sum, sum_congr rfl]
  · intro x hx
    exact (coe_toNNReal (hf x hx)).symm
  · exact sum_ne_top.2 hf

/-- seeing `ℝ≥0∞` as `Real` does not change their sum, unless one of the `ℝ≥0∞` is infinity -/
theorem toReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.toReal (f a) := by
  rw [ENNReal.toReal, toNNReal_sum hf, NNReal.coe_sum]
  rfl

theorem ofReal_sum_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_sum, coe_inj]
  exact Real.toNNReal_sum_of_nonneg hf

theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hlt : ∀ i ∈ s, f i < g i) : ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp [Hlt _ (Finset.mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [Finset.sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENNReal.add_lt_add Hlt.1 (ih Hlt.2)

theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hle : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i) : ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle
  apply ENNReal.sum_lt_sum_of_nonempty hs Hle

end Sum

section Inv

lemma prod_inv_distrib {ι : Type*} {f : ι → ℝ≥0∞} {s : Finset ι}
    (hf : (s : Set ι).Pairwise fun i j ↦ f i ≠ 0 ∨ f j ≠ ∞) :
    (∏ i ∈ s, f i)⁻¹ = ∏ i ∈ s, (f i)⁻¹ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => ?_
  simp only [Finset.prod_cons, ← ih (hf.mono <| by simp)]
  refine ENNReal.mul_inv (not_or_of_imp fun hi₀ ↦ prod_ne_top fun j hj ↦ ?_)
    (not_or_of_imp fun hi₀ ↦ Finset.prod_ne_zero_iff.2 fun j hj ↦ ?_)
  · exact imp_iff_not_or.2 (hf (by simp) (by simp [hj]) <| .symm <| ne_of_mem_of_not_mem hj hi) hi₀
  · exact imp_iff_not_or.2 (hf (by simp [hj]) (by simp) <| ne_of_mem_of_not_mem hj hi).symm hi₀

lemma finsetSum_iSup {α ι : Type*} {s : Finset α} {f : α → ι → ℝ≥0∞}
    (hf : ∀ i j, ∃ k, ∀ a, f a i ≤ f a k ∧ f a j ≤ f a k) :
    ∑ a ∈ s, ⨆ i, f a i = ⨆ i, ∑ a ∈ s, f a i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ihs =>
    simp_rw [Finset.sum_cons, ihs]
    refine iSup_add_iSup fun i j ↦ (hf i j).imp fun k hk ↦ ?_
    gcongr
    exacts [(hk a).1, (hk _).2]

lemma finsetSum_iSup_of_monotone {α ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {s : Finset α}
    {f : α → ι → ℝ≥0∞} (hf : ∀ a, Monotone (f a)) : (∑ a ∈ s, iSup (f a)) = ⨆ n, ∑ a ∈ s, f a n :=
  finsetSum_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ a ↦ ⟨hf a hi, hf a hj⟩

end Inv

end ENNReal
