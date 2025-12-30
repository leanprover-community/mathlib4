/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.Convex.Majorization.Defs

/-!
# Majorization

Given two vectors `x y : n → R` (with `n` finite), we say that

* `y` submajorizes `x` (`x ≼ₛ y`) if `∀ k, ∑ i ≤ k, x↓ i ≤ ∑ i ≤ k, y↓ i` where `x↓` denotes
the values of `x` sorted in decreasing order (this notation is not used here, only in the
docstring).
* `y` supermajorizes `x` (`x ≼ˢ y`) if `∀ k, ∑ i ≤ k, y↑ i ≤ ∑ i ≤ k, x↑ i`.
* `y` majorizes `x` (`x ≼ y`) if `x ≼ₛ y` and `∑ i, x i = ∑ i, y i`.

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

lemma incSum_eq_sum_incSumSet (k : ℕ) (x : n → R) (hk : k ≤ card n) :
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
    have : j ∉ s.erase i := by rw [mem_erase]; grind [Finset.mem_compl]
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

lemma decSum_eq_sum_decSumSet (k : ℕ) (x : n → R) (hk : k ≤ card n) :
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
    have : j ∉ s.erase i := by rw [mem_erase]; grind [Finset.mem_compl]
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
  rw [incSum_of_le_card hk]
  obtain ⟨s, hs₁, hs₂⟩ := exists_min'_image (powersetCard k (univ : Finset n))
      (fun s => ∑ i ∈ s, x i) (by grind)
  refine ⟨s, ?_, hs₂, ?_⟩
  · exact mem_powersetCard_univ.mp hs₁
  · intro t ht
    rw [← hs₂]
    exact Finset.min'_le _ _ (by grind)

lemma exists_eq_decSum (k : ℕ) (x : n → R) (hk : k ≤ card n) :
    ∃ s : Finset n, s.card = k ∧ decSum k x = ∑ i ∈ s, x i
      ∧ ∀ t : Finset n, t.card = k → ∑ i ∈ t, x i ≤ ∑ i ∈ s, x i := by
  rw [decSum_of_le_card hk]
  obtain ⟨s, hs₁, hs₂⟩ := exists_max'_image (powersetCard k (univ : Finset n))
      (fun s => ∑ i ∈ s, x i) (by grind)
  refine ⟨s, ?_, hs₂, ?_⟩
  · exact mem_powersetCard_univ.mp hs₁
  · intro t ht
    rw [← hs₂]
    exact Finset.le_max' _ _ (by grind)

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
      exact ht₃ sᶜ (by grind [Finset.card_compl])
    have h₂ : ∑ i ∈ sᶜ, x i ≤ ∑ i ∈ t, x i := by
      have hs' := Finset.sum_add_sum_compl s x
      have ht' := Finset.sum_add_sum_compl t x
      specialize hs₃ tᶜ (by grind [Finset.card_compl])
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

lemma decSum_of_antitone [IsOrderedRing R] {n : ℕ} (k : ℕ) (x : Fin n → R) (hx : Antitone x)
    (hk0 : 0 < k) (hkn : k < n) : decSum k x = ∑ i ≤ ⟨k - 1, by grind⟩, x i := by
  let s : Finset (Fin n) := Iic ⟨k - 1, by grind⟩
  rw [decSum_of_le_card (by grind [Fintype.card_fin])]
  rw [max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_image]
    refine ⟨s, ?_, rfl⟩
    rw [mem_powersetCard_univ]
    grind [Fin.card_Iic]
  · intro b hb
    rw [mem_image] at hb
    obtain ⟨a, ha₁, ha₂⟩ := hb
    rw [← ha₂]
    change ∑ i ∈ a, x i ≤ ∑ i ∈ s, x i
    by_cases has : a = s
    · simp [has]
    have ha : a = (a ∩ s) ∪ (a \ s) := by grind
    have hs : s = (a ∩ s) ∪ (s \ a) := by grind
    have hcard : (a \ s).card = (s \ a).card := by
      rw [card_sdiff_eq_card_sdiff_iff]; grind [Fin.card_Iic]
    rw [ha, sum_union (by grind [Finset.disjoint_iff_ne])]
    conv_rhs => rw [hs, sum_union (by grind [Finset.disjoint_iff_ne])]
    gcongr ?_ + ?_
    let K := ((a \ s).image x).max' <| by grind [Finset.image_nonempty]
    calc _ ≤ (a \ s).card • K := by
              apply Finset.sum_le_card_nsmul
              intro i hi
              apply le_max'
              grind
      _ = (s \ a).card • K := by rw [hcard]
      _ ≤ ∑ i ∈ (s \ a), x i := by
              apply card_nsmul_le_sum
              intro i hi
              apply max'_le
              intro y hy
              rw [mem_image] at hy
              obtain ⟨j, hj₁, hj₂⟩ := hy
              rw [← hj₂]
              have hij : i < j := by grind
              exact hx (by grind)

lemma decSum_one_of_antitone {n : ℕ} [NeZero n] (x : Fin n → R) (hx : Antitone x) :
    decSum 1 x = x 0 := by
  have hcard : 1 ≤ card (Fin n) := by simp [NeZero.one_le]
  rw [decSum_of_le_card hcard]
  rw [max'_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_image]
    exact ⟨{0}, by simp, by simp⟩
  · intro b hb
    rw [mem_image] at hb
    obtain ⟨s, hs₁, hs₂⟩ := hb
    simp only [mem_powersetCard, subset_univ, true_and, card_eq_one] at hs₁
    obtain ⟨i, hi⟩ := hs₁
    simp only [hi, sum_singleton] at hs₂
    rw [← hs₂]
    exact hx <| Fin.zero_le i

end incdecsum

section majorization

variable {m n R : Type*} [Fintype m] [Fintype n] [LinearOrder R] [Semiring R]

open scoped Majorization
open Finset

lemma isSubmajorizedBy_iff_forall_pos (x : m → R) (y : n → R) :
    x ≼ₛ y ↔ ∀ k > 0, decSum k x ≤ decSum k y := by
  refine ⟨fun h k _ => h k, fun h => ?_⟩
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · exact h k (by grind)

lemma isSubmajorizedBy_of_sum_le_sum_antitone [IsOrderedRing R] {n : ℕ} [NeZero n] (x y : Fin n → R)
    (hx : Antitone x) (hmaj : ∀ k, ∑ i ≤ k, x i ≤ ∑ i ≤ k, y i) : x ≼ₛ y := by
  rw [isSubmajorizedBy_iff_forall_pos]
  intro k hk
  by_cases hk' : n ≤ k
  · rw [decSum_of_ge_card (by simp [hk']), decSum_of_ge_card (by simp [hk'])]
    let nmax : Fin n := ⟨n - 1, by grind [neZero_iff]⟩
    specialize hmaj nmax
    have hIic : Iic nmax = univ := by grind
    simpa [hIic] using hmaj
  let km1 : Fin n := ⟨k - 1, by grind⟩
  rw [decSum_of_antitone k x hx hk (by grind)]
  apply (hmaj km1).trans
  rw [decSum_of_le_card (by grind [Fintype.card_fin])]
  apply le_max'
  rw [mem_image]
  exact ⟨Iic km1, by grind [Fin.card_Iic], rfl⟩

lemma IsMajorizedBy.isSubmajorizedBy [IsStrictOrderedRing R] {x : m → R} {y : n → R}
    (hxy : x ≼ y) : x ≼ₛ y := hxy.1


end majorization
