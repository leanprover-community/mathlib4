/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Rat.Floor
import Mathlib.SetTheory.Cardinal.Basic

/-!
# IMO 2024 Q6

A function `f: ℚ → ℚ` is called *aquaesulian* if the following
property holds: for every `x, y ∈ ℚ`,
`f(x + f(y)) = f(x) + y` or `f(f(x) + y) = x + f(y)`.

Show that there exists an integer `c` such that for any aquaesulian function `f` there are at
most `c` different rational numbers of the form `f(r)+f(-r)` for some rational number `r`,
and find the smallest possible value of `c`.

We follow Solution 1 from the
[official solutions](https://www.imo2024.uk/s/IMO-2024-Paper-1-Solutions.pdf). A key observation
is that `f(-f(-x)) = x`. We then consider a pair of distinct nonzero values of `f(x)+f(-x)`,
and a series of manipulations together with the previous observation result in a contradiction,
so there are at most two values of `f(x)+f(-x)`. All this works over any `AddCommGroup`; over
`ℚ`, we then show that `⌊x⌋ - Int.fract x` achieves two different values of `f(x)+f(-x)`.
-/


namespace Imo2024Q6

open scoped Cardinal

namespace General

variable {G : Type*} [AddCommGroup G]

/-- The condition on functions in the problem (for a general `AddCommGroup` and in
symmetric form). -/
def Aquaesulian (f : G → G) : Prop := ∀ x y, f (f y + x) = f x + y ∨ f (f x + y) = f y + x

variable {f : G → G} (h : Aquaesulian f)
include h

lemma Aquaesulian.apply_apply_add (x : G) : f (f x + x) = f x + x := by
  rcases h x x with hx | hx <;> exact hx

lemma Aquaesulian.eq_of_apply_eq_inl {x₁ x₂ : G} (he : f x₁ = f x₂)
    (hc : f (f x₁ + x₂) = f x₂ + x₁) : x₁ = x₂ := by
  rw [he, h.apply_apply_add, add_right_inj] at hc
  exact hc.symm

lemma Aquaesulian.injective : Function.Injective f := by
  intro x₁ x₂ he
  rcases h x₁ x₂ with hc | hc
  · exact (h.eq_of_apply_eq_inl he.symm hc).symm
  · exact h.eq_of_apply_eq_inl he hc

@[simp]
lemma Aquaesulian.apply_zero : f 0 = 0 := by
  refine h.injective ?_
  convert h.apply_apply_add 0 using 1 <;> simp

@[simp]
lemma Aquaesulian.apply_neg_apply_add (x : G) : f (-(f x)) + x = 0 := by
  rcases h x (-(f x)) with hc | hc
  · rw [add_neg_cancel, ← h.apply_zero] at hc
    exact h.injective hc
  · rw [add_neg_cancel, h.apply_zero] at hc
    exact hc.symm

@[simp]
lemma Aquaesulian.apply_neg_apply (x : G) : f (-(f x)) = -x := by
  rw [← add_eq_zero_iff_eq_neg]
  exact h.apply_neg_apply_add x

lemma Aquaesulian.apply_neg_apply_neg (x : G) : f (-(f (-x))) = x := by
  simp [h]

lemma Aquaesulian.apply_neg_of_apply_eq {x₁ x₂ : G} (hx : f x₁ = x₂) : f (-x₂) = -x₁ := by
  rw [← hx]
  exact h.apply_neg_apply _

lemma Aquaesulian.apply_neg_eq_neg_iff {x₁ x₂ : G} : f (-x₂) = -x₁ ↔ f x₁ = x₂ := by
  refine ⟨fun hn ↦ ?_, h.apply_neg_of_apply_eq⟩
  convert h.apply_neg_of_apply_eq hn <;> rw [neg_neg]

lemma Aquaesulian.pair_lemma {x u v : G} (huv : u ≠ v) (hx : f x = u ∨ f u = x)
    (hy : f x = v ∨ f v = x) : f x = v ∨ f x = u := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (huv (hx.symm.trans hy)).elim
  · exact .inr hx
  · exact .inl hy
  · exact ((h.injective.ne huv) (hx.trans hy.symm)).elim

lemma Aquaesulian.g_two {x y u v : G} (huv : u ≠ v) (hx : f x + f (-x) = u)
    (hy : f y + f (-y) = v) :
    f (x + y) = -(f (-x)) + -(f (-y)) + v ∨ f (x + y) = -(f (-x)) + -(f (-y)) + u := by
  refine h.pair_lemma ?_ ?_ ?_
  · simp [huv]
  · convert h x (-(f (-y))) using 2
    · rw [h.apply_neg_apply_neg, add_comm]
    · rw [← hx]
      abel
    · rw [← hx]
      abel_nf
    · rw [h.apply_neg_apply_neg, add_comm]
  · convert h y (-(f (-x))) using 2
    · rw [h.apply_neg_apply_neg]
    · rw [← hy]
      abel
    · rw [← hy]
      abel_nf
    · rw [h.apply_neg_apply_neg]

lemma Aquaesulian.u_eq_zero {x y u v : G} (huv : u ≠ v) (hx : f x + f (-x) = u)
    (hy : f y + f (-y) = v) (hxyv : f (x + y) = -(f (-x)) + -(f (-y)) + v) : u = 0 := by
  rw [← eq_sub_iff_add_eq, ← h.apply_neg_eq_neg_iff, neg_sub] at hx
  rw [add_comm, ← eq_sub_iff_add_eq] at hy
  have hc := h (x + y) (f (-x) - u)
  rw [hx, hxyv, neg_add_cancel_left, hy] at hc
  rcases hc with hc | hc
  · abel_nf at hc
    simpa using hc
  · nth_rw 2 [← h.apply_neg_apply_neg y] at hc
    rw [h.injective.eq_iff, hy] at hc
    abel_nf at hc
    simp [add_comm, huv] at hc

lemma Aquaesulian.u_eq_zero_or_v_eq_zero {x y u v : G} (huv : u ≠ v) (hx : f x + f (-x) = u)
    (hy : f y + f (-y) = v) : u = 0 ∨ v = 0 := by
  rcases h.g_two huv hx hy with hxy' | hxy'
  · exact .inl (h.u_eq_zero huv hx hy hxy')
  · rw [add_comm x y, add_comm (-(f (-x))) (-(f (-y)))] at hxy'
    exact .inr (h.u_eq_zero huv.symm hy hx hxy')

lemma Aquaesulian.card_le_two : #(Set.range (fun x ↦ f x + f (-x))) ≤ 2 := by
  classical
  by_cases hf : ∀ x, f x + f (-x) = 0
  · simp [hf]
  · rw [not_forall] at hf
    rcases hf with ⟨x, hx⟩
    suffices #(Set.range (fun x ↦ f x + f (-x))) ≤ (2 : ℕ) from mod_cast this
    rw [Cardinal.mk_le_iff_forall_finset_subset_card_le]
    intro s hs
    simp_rw [Set.subset_def, Set.mem_range] at hs
    refine (Finset.card_le_card_of_surjOn (fun x ↦ f x + f (-x)) ?_).trans
      (Finset.card_le_two (a := 0) (b := x))
    intro y hy
    rcases hs y hy with ⟨t, ht⟩
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_image, Set.mem_insert_iff,
               Set.mem_singleton_iff, exists_eq_or_imp, neg_zero, exists_eq_left, h.apply_zero,
               add_zero]
    by_cases h0 : y = 0
    · simp [h0]
    · refine .inr ?_
      by_contra hxy
      have huv := h.u_eq_zero_or_v_eq_zero hxy rfl ht
      simp [hx, h0] at huv

end General

/-- The condition on functions in the problem (for `ℚ` and in the original form). -/
def Aquaesulian (f : ℚ → ℚ) : Prop := ∀ x y, f (x + f y) = f x + y ∨ f (f x + y) = x + f y

lemma aquaesulian_iff_general {f : ℚ → ℚ} : Aquaesulian f ↔ General.Aquaesulian f := by
  rw [Aquaesulian, General.Aquaesulian]
  refine forall_congr' (fun x ↦ forall_congr' (fun y ↦ ?_))
  rw [add_comm x]

lemma Aquaesulian.card_le_two {f : ℚ → ℚ} (h : Aquaesulian f) :
    #(Set.range (fun x ↦ f x + f (-x))) ≤ 2 := by
  rw [aquaesulian_iff_general] at h
  exact h.card_le_two

/-- An example of a function achieving the maximum number of values of `f(r)+f(-r)`. -/
def fExample (x : ℚ) : ℚ := ⌊x⌋ - Int.fract x

lemma fExample_add (x y : ℚ) : fExample x + y = ⌊x⌋ + ⌊y⌋ + (Int.fract y - Int.fract x) := by
  rw [fExample]
  nth_rw 1 [← Int.floor_add_fract y]
  abel

lemma add_fExample (x y : ℚ) : x + fExample y = ⌊x⌋ + ⌊y⌋ + (Int.fract x - Int.fract y) := by
  rw [add_comm, fExample_add]
  abel

lemma fExample_intCast_add (x : ℤ) (y : ℚ) : fExample (x + y) = x + fExample y := by
  simp_rw [fExample, Int.floor_intCast_add, Int.fract_intCast_add, ← add_sub_assoc]
  exact_mod_cast rfl

lemma fExample_of_mem_Ico {x : ℚ} (h : x ∈ Set.Ico 0 1) : fExample x = -x := by
  rw [fExample, Int.fract_eq_self.2 h, Int.floor_eq_zero_iff.2 h]
  simp

lemma apply_fExample_add_apply_of_fract_le {x y : ℚ} (h : Int.fract y ≤ Int.fract x) :
    fExample (x + fExample y) = fExample x + y := by
  rw [← sub_nonneg] at h
  have h₁ : Int.fract x - Int.fract y < 1 :=
    (sub_le_self (Int.fract x) (Int.fract_nonneg y)).trans_lt (Int.fract_lt_one x)
  rw [fExample_add, add_fExample, add_assoc, fExample_intCast_add, fExample_intCast_add,
      fExample_of_mem_Ico ⟨h, h₁⟩]
  abel

lemma aquaesulian_fExample : Aquaesulian fExample := by
  intro x y
  rcases lt_or_ge (Int.fract x) (Int.fract y) with h | h
  · rw [add_comm (fExample x), add_comm x]
    exact .inr (apply_fExample_add_apply_of_fract_le h.le)
  · exact .inl (apply_fExample_add_apply_of_fract_le h)

lemma fract_fExample (x : ℚ) :
    Int.fract (fExample x) = if Int.fract x = 0 then 0 else 1 - Int.fract x := by
  by_cases h : Int.fract x = 0
  · simp [fExample, h]
  · simp [fExample, h, sub_eq_add_neg, Int.fract_neg]

lemma floor_fExample (x : ℚ) :
    ⌊fExample x⌋ = if Int.fract x = 0 then x else ⌊x⌋ - 1 := by
  by_cases h : Int.fract x = 0
  · simp only [h, if_true, fExample, sub_zero, Int.floor_intCast]
    rw [Int.fract, sub_eq_zero] at h
    exact h.symm
  · simp only [h, if_false, fExample, sub_eq_add_neg, Int.floor_intCast_add, Int.cast_add,
               add_right_inj]
    suffices ⌊-Int.fract x⌋ = -1 from mod_cast this
    rw [Int.floor_eq_iff]
    simp [(Int.fract_nonneg x).lt_of_ne' h, (Int.fract_lt_one x).le]

lemma card_range_fExample : #(Set.range (fun x ↦ fExample x + fExample (-x))) = 2 := by
  have h : Set.range (fun x ↦ fExample x + fExample (-x)) = {0, -2} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with ⟨y, rfl⟩
      rw [← Int.floor_add_fract (fExample y), ← Int.floor_add_fract (fExample (-y))]
      by_cases h : Int.fract y = 0
      · simp [fract_fExample, floor_fExample, h]
      · refine .inr ?_
        simp only [fract_fExample, floor_fExample, h, if_false, sub_add_sub_cancel,
                   Int.fract_neg_eq_zero]
        rw [Int.fract_neg h, Int.floor_neg, Int.cast_neg, Int.ceil_eq_add_one_sub_fract h,
            ← Int.self_sub_fract]
        abel_nf
        simp
    · rcases h with rfl | rfl
      · refine ⟨0, by simp [fExample]⟩
      · refine ⟨1 / 2, ?_⟩
        rw [(by norm_num : (-(1 / 2) : ℚ) = (-1 : ℤ) + (1 / 2 : ℚ)), fExample_intCast_add,
            fExample_of_mem_Ico ⟨by simp, by norm_num⟩]
        norm_num
  rw [h]
  simp

/-- The answer 2 is to be determined by the solver of the original problem. -/
theorem _root_.imo2024q6 : (∀ f, Aquaesulian f → #(Set.range (fun x ↦ f x + f (-x))) ≤ (2 : ℕ)) ∧
    ∀ c : ℕ, (∀ f, Aquaesulian f → #(Set.range (fun x ↦ f x + f (-x))) ≤ c) → 2 ≤ c := by
  refine ⟨fun _ ↦ Aquaesulian.card_le_two, fun c h ↦ ?_⟩
  replace h := h fExample aquaesulian_fExample
  rw [card_range_fExample] at h
  exact_mod_cast h

end Imo2024Q6
