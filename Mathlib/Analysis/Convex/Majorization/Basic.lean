/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.Convex.Majorization.Defs

/-!
# Basic facts about majorization

Given two vectors `x y : n → R` (with `n` finite), we say that

* `y` submajorizes `x` (`x ≼ₛ y`) if `∀ k, ∑ i ≤ k, x↓ i ≤ ∑ i ≤ k, y↓ i` where `x↓` denotes
the values of `x` sorted in decreasing order (this notation is not used here, only in the
docstring).
* `y` supermajorizes `x` (`x ≼ˢ y`) if `∀ k, ∑ i ≤ k, y↑ i ≤ ∑ i ≤ k, x↑ i`.
* `y` majorizes `x` (`x ≼ y`) if `x ≼ₛ y` and `∑ i, x i = ∑ i, y i`.

This file develops basic API for these notions, and shows that a matrix `A` is doubly stochastic
iff `A *ᵥ x ≼ x` for all `x`.

## Main statements

* `mem_doublyStochastic_iff_forall_mulVec_isMajorizedBy`: A matrix `A` is doubly stochastic iff
  `A *ᵥ x ≼ x` for all `x`.

## Implementation notes

There are several characterizations of this notion, and one that is more amenable to
formalization (since it avoids having to introduce equivs to sort values), is the one that
makes use of the fact that
`∑ i ≤ k, x↓ i = max_{s, #s = k} ∑ i ∈ s, x i`
and likewise for the increasing sum. This is what we take as the definition here.

## References

* Rajendra Bhatia, ``Matrix Analysis'', Chapter 2.
-/

@[expose] public section

section incdecsum
open Finset

variable {n m R : Type*} [Fintype n] [LinearOrder R] [Semiring R]
  [Fintype m]

open Fintype Function Finset

lemma incSum_of_le_card {k : ℕ} {x : n → R} (hk : k ≤ card n) :
    incSum k x =
      min' ((powersetCard k (univ : Finset n)).image fun s => ∑ i ∈ s, x i) (by simp [hk]) := by
  simp [incSum, hk]

lemma decSum_of_le_card {k : ℕ} {x : n → R} (hk : k ≤ card n) :
    decSum k x =
      max' ((powersetCard k (univ : Finset n)).image fun s => ∑ i ∈ s, x i) (by simp [hk]) := by
  simp [decSum, hk]

@[simp]
lemma card_incSumSet (k : ℕ) (x : n → R) (hk : k ≤ card n) : (incSumSet k x).card = k := by
  obtain ⟨hs₁, hs₂⟩ := Classical.choose_spec (exists_min'_image (powersetCard k (univ : Finset n))
        (fun s => ∑ i ∈ s, x i) (by grind))
  simp only [mem_powersetCard, subset_univ, true_and, incSumSet, hk, ↓reduceDIte] at ⊢ hs₁
  grind

grind_pattern card_incSumSet => incSumSet k x

lemma incSum_eq_sum_incSumSet {k : ℕ} {x : n → R} (hk : k ≤ card n) :
    incSum k x = ∑ i ∈ incSumSet k x, x i := by
  obtain ⟨hs₁, hs₂⟩ := Classical.choose_spec (exists_min'_image (powersetCard k (univ : Finset n))
        (fun s => ∑ i ∈ s, x i) (by grind))
  unfold incSum incSumSet
  simp only [hk, ↓reduceDIte]
  exact hs₂

grind_pattern incSum_eq_sum_incSumSet => incSumSet k x

lemma sum_incSumSet_le (k : ℕ) (x : n → R) (hk : k ≤ card n) (t : Finset n) (ht : t.card = k) :
    ∑ i ∈ incSumSet k x, x i ≤ ∑ i ∈ t, x i := by
  obtain ⟨hs₁, hs₂⟩ := Classical.choose_spec (exists_min'_image (powersetCard k (univ : Finset n))
        (fun s => ∑ i ∈ s, x i) (by grind))
  unfold incSumSet
  simp only [mem_powersetCard, subset_univ, true_and, hk, ↓reduceDIte] at hs₂ ⊢
  rw [← hs₂]
  exact Finset.min'_le _ _ (by grind)

lemma le_of_mem_incSumSet [DecidableEq n] [IsStrictOrderedRing R] (k : ℕ) (x : n → R)
    (hk : k ≤ card n) (i : n) (hi : i ∈ incSumSet k x) (j : n) (hj : j ∈ (incSumSet k x)ᶜ) :
    x i ≤ x j := by
  by_contra hcontra
  let s := incSumSet k x
  let t : Finset n := insert j (s.erase i)
  have hs : s = insert i (s.erase i) := by grind
  have tcard : t.card = k := by
    have : j ∉ s.erase i := by rw [mem_erase]; grind
    rw [card_insert_of_notMem this, card_erase_of_mem hi]
    grind
  have hsum : ∑ l ∈ t, x l < ∑ l ∈ s, x l := by
    rw [Finset.sum_insert (by grind), hs, Finset.sum_insert (by grind)]
    simp only [erase_insert_eq_erase, mem_erase, ne_eq, not_true_eq_false, false_and,
      not_false_eq_true, erase_eq_of_notMem, add_lt_add_iff_right]
    grind
  have := sum_incSumSet_le k x hk t tcard
  grind only

@[simp]
lemma card_decSumSet (k : ℕ) (x : n → R) (hk : k ≤ card n) : (decSumSet k x).card = k := by
  obtain ⟨hs₁, hs₂⟩ := Classical.choose_spec (exists_min'_image (powersetCard k (univ : Finset n))
        (fun s => ∑ i ∈ s, x i) (by grind))
  simp only [mem_powersetCard, subset_univ, true_and, decSumSet, hk, ↓reduceDIte] at ⊢ hs₁
  grind

grind_pattern card_decSumSet => decSumSet k x

lemma decSum_eq_sum_decSumSet {k : ℕ} {x : n → R} (hk : k ≤ card n) :
    decSum k x = ∑ i ∈ decSumSet k x, x i := by
  obtain ⟨hs₁, hs₂⟩ := Classical.choose_spec (exists_max'_image (powersetCard k (univ : Finset n))
        (fun s => ∑ i ∈ s, x i) (by grind))
  unfold decSum decSumSet
  simp only [hk, ↓reduceDIte]
  exact hs₂

grind_pattern decSum_eq_sum_decSumSet => decSumSet k x

lemma sum_decSumSet_le (k : ℕ) (x : n → R) (hk : k ≤ card n) (t : Finset n) (ht : t.card = k) :
    ∑ i ∈ t, x i ≤ ∑ i ∈ decSumSet k x, x i := by
  obtain ⟨hs₁, hs₂⟩ := Classical.choose_spec (exists_max'_image (powersetCard k (univ : Finset n))
        (fun s => ∑ i ∈ s, x i) (by grind))
  unfold decSumSet
  simp only [mem_powersetCard, subset_univ, true_and, hk, ↓reduceDIte] at hs₂ ⊢
  rw [← hs₂]
  exact Finset.le_max' _ _ (by grind)

lemma ge_of_mem_decSumSet [DecidableEq n] [IsStrictOrderedRing R] (k : ℕ) (x : n → R)
    (hk : k ≤ card n) (i : n) (hi : i ∈ decSumSet k x) (j : n) (hj : j ∈ (decSumSet k x)ᶜ) :
    x j ≤ x i := by
  by_contra hcontra
  let s := decSumSet k x
  let t : Finset n := insert j (s.erase i)
  have hs : s = insert i (s.erase i) := by grind
  have tcard : t.card = k := by
    have : j ∉ s.erase i := by rw [mem_erase]; grind
    rw [card_insert_of_notMem this, card_erase_of_mem hi]
    grind
  have hsum : ∑ l ∈ s, x l < ∑ l ∈ t, x l := by
    rw [Finset.sum_insert (by grind), hs, Finset.sum_insert (by grind)]
    simp only [erase_insert_eq_erase, mem_erase, ne_eq, not_true_eq_false, false_and,
      not_false_eq_true, erase_eq_of_notMem, add_lt_add_iff_right]
    grind
  have := sum_decSumSet_le k x hk t tcard
  grind only

lemma exists_eq_incSum (k : ℕ) (x : n → R) (hk : k ≤ card n) :
    ∃ s : Finset n, s.card = k
      ∧ incSum k x = ∑ i ∈ s, x i
      ∧ ∀ t : Finset n, t.card = k → ∑ i ∈ s, x i ≤ ∑ i ∈ t, x i := by
  exact ⟨incSumSet k x, card_incSumSet k x hk, incSum_eq_sum_incSumSet hk,
    fun t a ↦ sum_incSumSet_le k x hk t a⟩

lemma exists_eq_decSum (k : ℕ) (x : n → R) (hk : k ≤ card n) :
    ∃ s : Finset n, s.card = k ∧ decSum k x = ∑ i ∈ s, x i
      ∧ ∀ t : Finset n, t.card = k → ∑ i ∈ t, x i ≤ ∑ i ∈ s, x i := by
  exact ⟨decSumSet k x, card_decSumSet k x hk, decSum_eq_sum_decSumSet hk,
    fun t a ↦ sum_decSumSet_le k x hk t a⟩

open Finset in
lemma incSum_of_ge_card {k : ℕ} {x : n → R} (hk : card n ≤ k) : incSum k x = ∑ i, x i := by
  by_cases hk : k ≤ card n
  · replace hk : k = card n := by grind
    have h₁ := incSum_of_le_card (x := x) (n := n) (k := k) (by grind)
    have h₂ := powersetCard_self (univ : Finset n)
    simp_all only [le_refl, card_univ, image_singleton, min'_singleton]
  · grind [incSum]

open Finset in
lemma decSum_of_ge_card {k : ℕ} {x : n → R} (hk : card n ≤ k) : decSum k x = ∑ i, x i := by
  by_cases hk : k ≤ card n
  · replace hk : k = card n := by grind
    have h₁ := decSum_of_le_card (x := x) (n := n) (k := k) (by grind)
    have h₂ := powersetCard_self (univ : Finset n)
    simp_all only [le_refl, card_univ, image_singleton, max'_singleton]
  · grind [decSum]

@[simp, grind =]
lemma incSum_zero {x : n → R} : incSum 0 x = 0 := by
  rw [incSum_of_le_card (by grind)]
  simp

@[simp, grind =]
lemma decSum_zero {x : n → R} : decSum 0 x = 0 := by
  rw [decSum_of_le_card (by grind)]
  simp

lemma le_decSum_one {x : n → R} (i : n) : x i ≤ decSum 1 x := by
  by_cases hcard : 1 ≤ card n
  · obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_decSum 1 x (by grind)
    rw [hs₂]
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hs₁
    specialize hs₃ {i} (by simp)
    simpa using hs₃
  · have hempty : IsEmpty n := by grind [Fintype.card_eq_zero_iff]
    exact hempty.elim i

lemma incSum_one_le {x : n → R} (i : n) : incSum 1 x ≤ x i := by
  by_cases hcard : 1 ≤ card n
  · obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_incSum 1 x (by grind)
    rw [hs₂]
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hs₁
    specialize hs₃ {i} (by simp)
    simpa using hs₃
  · have hempty : IsEmpty n := by grind [Fintype.card_eq_zero_iff]
    exact hempty.elim i

lemma decSum_add_incSum [IsStrictOrderedRing R] (k : ℕ) (x : n → R) :
    decSum k x + incSum (card n - k) x = ∑ i, x i := by
  classical
  by_cases hk : k ≤ card n
  · obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_decSum k x hk
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_eq_incSum (card n - k) x (by grind)
    rw [hs₂, ht₂, ← Finset.sum_add_sum_compl s]
    have h₁ : ∑ i ∈ t, x i ≤ ∑ i ∈ sᶜ, x i := by
      exact ht₃ sᶜ (by grind)
    have h₂ : ∑ i ∈ sᶜ, x i ≤ ∑ i ∈ t, x i := by
      have hs' := Finset.sum_add_sum_compl s x
      have ht' := Finset.sum_add_sum_compl t x
      specialize hs₃ tᶜ (by grind)
      grind
    grind only
  · have h₁ : decSum k x = ∑ i, x i := by grind [decSum_of_ge_card]
    have h₂ : incSum (card n - k) x = 0 := by
      have : card n - k = 0 := by grind
      grind
    grind only

lemma incSum_add_decSum [IsStrictOrderedRing R] (k : ℕ) (x : n → R) :
    incSum k x + decSum (card n - k) x = ∑ i, x i := by
  by_cases hk : k ≤ card n
  · have := decSum_add_incSum (card n - k) x
    grind
  · have h₁ : incSum k x = ∑ i, x i := by grind [incSum_of_ge_card]
    have h₂ : decSum (card n - k) x = 0 := by
      have : card n - k = 0 := by grind
      grind
    grind only

lemma decSum_const (k : ℕ) (a : R) (hk : k ≤ card n) : decSum k (const n a) = k • a := by
  obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_decSum k (const n a) (by grind)
  simp [hs₂, hs₁]

lemma incSum_const (k : ℕ) (a : R) (hk : k ≤ card n) : incSum k (const n a) = k • a := by
  obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_incSum k (const n a) (by grind)
  simp [hs₂, hs₁]

lemma exists_eq_incSum_one (x : n → R) (hcard : 1 ≤ card n) :
    ∃ i : n, incSum 1 x = x i ∧ ∀ j, x i ≤ x j := by
  obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_incSum 1 x (by grind)
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hs₁
  refine ⟨i, by simp [hs₂, hi], ?_⟩
  intro j
  specialize hs₃ {j} (by simp)
  simpa [hi] using hs₃

lemma exists_eq_decSum_one (x : n → R) (hcard : 1 ≤ card n) :
    ∃ i : n, decSum 1 x = x i ∧ ∀ j, x j ≤ x i := by
  obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_decSum 1 x (by grind)
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hs₁
  refine ⟨i, by simp [hs₂, hi], ?_⟩
  intro j
  specialize hs₃ {j} (by simp)
  simpa [hi] using hs₃

@[simp]
lemma incSum_comp_equiv (k : ℕ) (x : n → R) (e : m ≃ n) : incSum k (x ∘ e) = incSum k x := by
  have hmn : card m = card n := card_congr e
  by_cases hcard : k ≤ card n
  · obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_incSum k x (by grind)
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_eq_incSum k (x ∘ e) (by grind)
    rw [hs₂, ht₂]
    specialize hs₃ (t.map e.toEmbedding) (by grind)
    specialize ht₃ (s.map e.symm.toEmbedding) (by grind)
    simp only [Finset.sum_map, Equiv.coe_toEmbedding, comp_apply, Equiv.apply_symm_apply] at hs₃ ht₃
    grind
  · rw [incSum_of_ge_card (k := k) (x := x) (by grind),
      incSum_of_ge_card (k := k) (x := x ∘ e) (by grind)]
    exact sum_equiv e (x ∘ ⇑e) x (congrFun rfl)

@[simp]
lemma decSum_comp_equiv (k : ℕ) (x : n → R) (e : m ≃ n) : decSum k (x ∘ e) = decSum k x := by
  have hmn : card m = card n := card_congr e
  by_cases hcard : k ≤ card n
  · obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_decSum k x (by grind)
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_eq_decSum k (x ∘ e) (by grind)
    rw [hs₂, ht₂]
    specialize hs₃ (t.map e.toEmbedding) (by grind)
    specialize ht₃ (s.map e.symm.toEmbedding) (by grind)
    simp only [Finset.sum_map, Equiv.coe_toEmbedding, comp_apply, Equiv.apply_symm_apply] at hs₃ ht₃
    grind
  · rw [decSum_of_ge_card (k := k) (x := x) (by grind),
      decSum_of_ge_card (k := k) (x := x ∘ e) (by grind)]
    exact sum_equiv e (x ∘ ⇑e) x (congrFun rfl)

end incdecsum

section majorization

variable {m n R : Type*} [Fintype m] [Fintype n] [LinearOrder R] [Semiring R]

open scoped Majorization Matrix
open Finset Fintype

lemma isSubmajorizedBy_iff_forall_pos (x : m → R) (y : n → R) :
    x ≼ₛ y ↔ ∀ k > 0, decSum k x ≤ decSum k y := by
  refine ⟨fun h k _ => h k, fun h => ?_⟩
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · exact h k (by grind)

lemma isSubmajorizedBy_iff_isSupermajorizedBy [IsStrictOrderedRing R] {x : m → R} {y : n → R}
    (h : ∑ i, x i = ∑ i, y i) (hcard : card m = card n) : x ≼ₛ y ↔ x ≼ˢ y := by
  constructor
  · intro h₁
    rw [isSupermajorizedBy_def]
    rw [isSubmajorizedBy_def] at h₁
    intro k
    have hx := incSum_add_decSum (k := k) (x := x)
    have hy := incSum_add_decSum (k := k) (x := y)
    by_cases hcard : decSum (card m - k) x ≤ decSum (card n - k) y <;> grind
  · intro h₁
    rw [isSubmajorizedBy_def]
    rw [isSupermajorizedBy_def] at h₁
    intro k
    have hx := decSum_add_incSum (k := k) (x := x)
    have hy := decSum_add_incSum (k := k) (x := y)
    grind

lemma IsMajorizedBy.isSupermajorizedBy [IsStrictOrderedRing R] {x : m → R} {y : n → R}
    (hxy : x ≼ y) (hcard : card m = card n) : x ≼ˢ y :=
  (isSubmajorizedBy_iff_isSupermajorizedBy (x := x) (y := y) hxy.2 hcard).mp hxy.1

@[simp, grind =]
lemma IsSubmajorizedBy.equiv_left {o : Type*} [Fintype o] {x : m → R} {y : n → R} (e : o ≃ m) :
    (x ∘ e) ≼ₛ y ↔ x ≼ₛ y :=
  ⟨fun h k => by simpa using h k, fun h k => by simpa using h k⟩

@[simp, grind =]
lemma IsSubmajorizedBy.equiv_right {o : Type*} [Fintype o] {x : m → R} {y : n → R} (e : o ≃ n) :
    x ≼ₛ (y ∘ e) ↔ x ≼ₛ y :=
  ⟨fun h k => by simpa using h k, fun h k => by simpa using h k⟩

@[simp, grind =]
lemma IsSupermajorizedBy.equiv_left {o : Type*} [Fintype o] {x : m → R} {y : n → R} (e : o ≃ m) :
    (x ∘ e) ≼ˢ y ↔ x ≼ˢ y :=
  ⟨fun h k => by simpa using h k, fun h k => by simpa using h k⟩

@[simp, grind =]
lemma IsSupermajorizedBy.equiv_right {o : Type*} [Fintype o] {x : m → R} {y : n → R} (e : o ≃ n) :
    x ≼ˢ (y ∘ e) ↔ x ≼ˢ y :=
  ⟨fun h k => by simpa using h k, fun h k => by simpa using h k⟩

@[simp, grind =]
lemma IsMajorizedBy.equiv_left {o : Type*} [Fintype o] {x : m → R} {y : n → R} (e : o ≃ m) :
    (x ∘ e) ≼ y ↔ x ≼ y := by
  refine ⟨fun h => ⟨by simpa using h.1, ?_⟩, fun h => ⟨by simpa using h.1, ?_⟩⟩
  · have := h.2
    simp only [Finset.sum_comp_equiv] at this
    simpa using this
  · have := h.2
    simp only [Finset.sum_comp_equiv]
    simp [this]

@[simp, grind =]
lemma IsMajorizedBy.equiv_right {o : Type*} [Fintype o] {x : m → R} {y : n → R} (e : o ≃ n) :
    x ≼ (y ∘ e) ↔ x ≼ y := by
  refine ⟨fun h => ⟨by simpa using h.1, ?_⟩, fun h => ⟨by simpa using h.1, ?_⟩⟩
  · have := h.2
    simp only [Finset.sum_comp_equiv] at this
    simpa using this
  · have := h.2
    simp only [Finset.sum_comp_equiv]
    simp [this]

open Function in
lemma le_const_of_isSubmajorizedBy_const {x : n → R} {a : R} (h : x ≼ₛ const n a) :
    ∀ i, x i ≤ a := by
  by_cases hcard : 1 ≤ card n
  · intro i
    rw [isSubmajorizedBy_def] at h
    specialize h 1
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_decSum 1 x (by grind)
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_eq_decSum 1 (const n a) (by grind)
    calc _ ≤ decSum 1 x := le_decSum_one _
      _ ≤ decSum 1 (Function.const n a) := h
      _ = a := by rw [decSum_const _ _ (by grind)]; simp
  · have hempty : IsEmpty n := by grind [Fintype.card_eq_zero_iff]
    exact hempty.elim

open Function in
lemma const_le_of_isSupermajorizedBy_const {x : n → R} {a : R} (h : x ≼ˢ const n a) :
    ∀ i, a ≤ x i := by
  by_cases hcard : 1 ≤ card n
  · intro i
    rw [isSupermajorizedBy_def] at h
    specialize h 1
    obtain ⟨s, hs₁, hs₂, hs₃⟩ := exists_eq_incSum 1 x (by grind)
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_eq_incSum 1 (const n a) (by grind)
    calc _ = incSum 1 (const n a) := by rw [incSum_const _ _ (by grind)]; simp
      _ ≤ incSum 1 x := h
      _ ≤ _ := incSum_one_le _
  · have hempty : IsEmpty n := by grind [Fintype.card_eq_zero_iff]
    exact hempty.elim

open Function in
lemma eq_const_of_isMajorizedBy_const [IsStrictOrderedRing R] {x : n → R} {a : R}
    (h : x ≼ const n a) : x = const n a := by
  have h₁ := le_const_of_isSubmajorizedBy_const h.1
  have h₂ := const_le_of_isSupermajorizedBy_const <| h.isSupermajorizedBy rfl
  grind

lemma IsSupermajorizedBy.forall_nonneg {x y : n → R} (hy : ∀ i, 0 ≤ y i) (hxy : x ≼ˢ y) :
    ∀ i, 0 ≤ x i := by
  by_cases hcard : 1 ≤ card n
  · intro i
    have h₁ : incSum 1 x ≤ x i := incSum_one_le _
    have h₂ : 0 ≤ incSum 1 y := by
      obtain ⟨j, hj⟩ := exists_eq_incSum_one y hcard
      grind only
    have h₃ : incSum 1 y ≤ incSum 1 x := hxy 1
    grind
  · have h₁ : card n = 0 := by grind
    have h₂ : IsEmpty n := card_eq_zero_iff.mp h₁
    exact h₂.elim

lemma mem_doublyStochastic_of_forall_mulVec_isMajorizedBy [DecidableEq n] [IsStrictOrderedRing R]
    {A : Matrix n n R} (ha : ∀ x, A *ᵥ x ≼ x) : A ∈ doublyStochastic R n := by
  rw [mem_doublyStochastic]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    specialize ha (Pi.single j 1)
    have := (ha.isSupermajorizedBy rfl).forall_nonneg (by grind [zero_le_one]) i
    simpa [Matrix.mulVec] using this
  · specialize ha 1
    have : (1 : n → R) = Function.const n 1 := by simp
    rw [this] at ha ⊢
    rw [eq_const_of_isMajorizedBy_const ha]
  · rw [Matrix.one_vecMul]
    ext i
    specialize ha (Pi.single i 1)
    replace ha := ha.2
    simpa using ha

lemma mulVec_isSubmajorizedBy_of_mem_doublyStochastic [DecidableEq n] [IsStrictOrderedRing R]
    [CanonicallyOrderedAdd R] {A : Matrix n n R} (hA : A ∈ doublyStochastic R n) {x : n → R} :
    A *ᵥ x ≼ₛ x := by
  rw [isSubmajorizedBy_iff_forall_pos]
  intro k hk
  by_cases hcard : k ≤ card n
  · let s := decSumSet k x
    let t := decSumSet k (A *ᵥ x)
    have hs₁ := card_decSumSet k x hcard
    have ht₁ := card_decSumSet k (A *ᵥ x) (by grind)
    rw [decSum_eq_sum_decSumSet (by grind), decSum_eq_sum_decSumSet (by grind)]
    simp only [Matrix.mulVec, dotProduct]
    let z i := ∑ j ∈ t, A j i
    have hz : ∑ i, z i = k := by
      rw [Finset.sum_comm]
      simp_rw [sum_row_of_mem_doublyStochastic hA]
      simp [t, ht₁]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change ∑ i, z i * x i ≤ ∑ i ∈ s, x i
    let M := (s.image x).min' <| by grind
    have hM : ∀ i ∈ s, M ≤ x i := by
      intro i hi
      apply Finset.min'_le
      grind only [= Finset.mem_image]
    have hM' : ∀ i ∈ sᶜ, x i ≤ M := by
      have h₁ := Finset.min'_mem (s.image x) (by grind)
      rw [Finset.mem_image] at h₁
      obtain ⟨im, him⟩ := h₁
      grind [ge_of_mem_decSumSet]
    have hz₂ : ∀ i, z i ≤ 1 := by
      intro i
      unfold z
      calc _ ≤ ∑ j, A j i := by gcongr; grind only [= Finset.subset_iff, ← Finset.mem_univ]
        _ = 1 := sum_col_of_mem_doublyStochastic hA i
    have h₁ : ∀ i ∈ s, z i * x i + M ≤ x i + z i * M := by
      intro i hi
      obtain ⟨c, hc₁, hc₂⟩ := le_iff_exists_nonneg_add.mp (hz₂ i)
      calc _ = z i * x i + (z i + c) * M := by grind only
        _ = z i * x i + z i * M + c * M := by grind only
        _ ≤ z i * x i + z i * M + c * x i := by have := hM i hi; gcongr
        _ = (z i + c) * x i + z i * M := by grind only
        _ = x i + z i * M := by grind only
    have hmain : (∑ i, z i * x i) + k • M ≤ (∑ i ∈ s, x i) + k • M := by
      calc _ = (∑ i ∈ s, z i * x i) + (∑ i ∈ sᶜ, z i * x i) + (∑ i ∈ s, M) := by
                simp [Finset.sum_add_sum_compl, hs₁, s]
        _ = ∑ i ∈ s, (z i * x i + M) + ∑ i ∈ sᶜ, z i * x i := by
                rw [Finset.sum_add_distrib]
                grind only
        _ ≤ ∑ i ∈ s, (x i + z i * M) + ∑ i ∈ sᶜ, z i * x i := by
                gcongr (∑ i ∈ s, ?_) + ?_ with i hi
                exact le_of_eq_of_le rfl (h₁ i hi)
        _ ≤ ∑ i ∈ s, (x i + z i * M) + ∑ i ∈ sᶜ, z i * M := by
                gcongr with i hi
                grind only
        _ = ∑ i ∈ s, x i + ∑ i ∈ sᶜ, z i * M + ∑ i ∈ s, z i * M := by
                simp only [Finset.sum_add_distrib]
                grind only
        _ = ∑ i ∈ s, x i + ∑ i, z i * M := by
                rw [add_assoc]
                simp only [Finset.sum_compl_add_sum]
        _ = ∑ i ∈ s, x i + k • M := by
                simp only [← Finset.sum_mul, hz]
                grind only
    grind => linarith
  · rw [decSum_of_ge_card (k := k) (x := x) (by grind)]
    rw [decSum_of_ge_card (k := k) (x := (A *ᵥ x)) (by grind)]
    apply le_of_eq
    exact sum_mulVec_of_mem_doublyStochastic hA

lemma mulVec_isMajorizedBy_of_mem_doublyStochastic [DecidableEq n] [IsStrictOrderedRing R]
    [CanonicallyOrderedAdd R] {A : Matrix n n R} (hA : A ∈ doublyStochastic R n) {x : n → R} :
    A *ᵥ x ≼ x :=
  ⟨mulVec_isSubmajorizedBy_of_mem_doublyStochastic hA, sum_mulVec_of_mem_doublyStochastic hA⟩

lemma mem_doublyStochastic_iff_forall_mulVec_isMajorizedBy [DecidableEq n] [IsStrictOrderedRing R]
    [CanonicallyOrderedAdd R] {A : Matrix n n R} : A ∈ doublyStochastic R n ↔ ∀ x, A *ᵥ x ≼ x :=
  ⟨fun hA _ => mulVec_isMajorizedBy_of_mem_doublyStochastic hA,
    fun ha => mem_doublyStochastic_of_forall_mulVec_isMajorizedBy ha⟩

end majorization
