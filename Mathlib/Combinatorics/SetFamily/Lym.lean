/-
Copyright (c) 2022 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies

! This file was ported from Lean 3 source module combinatorics.set_family.lym
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.Order.Field.Basic
import Mathbin.Combinatorics.DoubleCounting
import Mathbin.Combinatorics.SetFamily.Shadow
import Mathbin.Data.Rat.Order

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `finset.card_div_choose_le_card_shadow_div_choose`: Local Lubell-Yamamoto-Meshalkin inequality.
  The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜` does.
* `finset.sum_card_slice_div_choose_le_one`: Lubell-Yamamoto-Meshalkin inequality. The sum of
  densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `is_antichain.sperner`: Sperner's theorem. The size of any antichain in `finset α` is at most the
  size of the maximal layer of `finset α`. It is a corollary of `sum_card_slice_div_choose_le_one`.

## TODO

Prove upward local LYM.

Provide equality cases. Local LYM gives that the equality case of LYM and Sperner is precisely when
`𝒜` is a middle layer.

`falling` could be useful more generally in grade orders.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/


open Finset Nat

open BigOperators FinsetFamily

variable {𝕜 α : Type _} [LinearOrderedField 𝕜]

namespace Finset

/-! ### Local LYM inequality -/


section LocalLym

variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {r : ℕ}

/-- The downward **local LYM inequality**, with cancelled denominators. `𝒜` takes up less of `α^(r)`
(the finsets of card `r`) than `∂𝒜` takes up of `α^(r - 1)`. -/
theorem card_mul_le_card_shadow_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    𝒜.card * r ≤ ((∂ ) 𝒜).card * (Fintype.card α - r + 1) :=
  by
  refine' card_mul_le_card_mul' (· ⊆ ·) (fun s hs => _) fun s hs => _
  · rw [← h𝒜 hs, ← card_image_of_inj_on s.erase_inj_on]
    refine' card_le_of_subset _
    simp_rw [image_subset_iff, mem_bipartite_below]
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
  refine' le_trans _ tsub_tsub_le_tsub_add
  rw [← h𝒜.shadow hs, ← card_compl, ← card_image_of_inj_on (insert_inj_on' _)]
  refine' card_le_of_subset fun t ht => _
  infer_instance
  rw [mem_bipartite_above] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe, h𝒜.empty_mem_iff, coe_eq_singleton]
    rintro rfl
    rwa [shadow_singleton_empty] at hs
  obtain ⟨a, ha, rfl⟩ :=
    exists_eq_insert_iff.2 ⟨ht.2, by rw [(sized_shadow_iff this).1 h𝒜.shadow ht.1, h𝒜.shadow hs]⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)
#align finset.card_mul_le_card_shadow_mul Finset.card_mul_le_card_shadow_mul

/-- The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` (the finsets of card `r`)
than `∂𝒜` takes up of `α^(r - 1)`. -/
theorem card_div_choose_le_card_shadow_div_choose (hr : r ≠ 0) (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    (𝒜.card : 𝕜) / (Fintype.card α).choose r ≤ ((∂ ) 𝒜).card / (Fintype.card α).choose (r - 1) :=
  by
  obtain hr' | hr' := lt_or_le (Fintype.card α) r
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  replace h𝒜 := card_mul_le_card_shadow_mul h𝒜
  rw [div_le_div_iff] <;> norm_cast
  · cases r
    · exact (hr rfl).elim
    rw [Nat.succ_eq_add_one] at *
    rw [tsub_add_eq_add_tsub hr', add_tsub_add_eq_tsub_right] at h𝒜
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    · simp [mul_assoc, Nat.choose_succ_right_eq]
      exact Or.inl (mul_comm _ _)
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
  · exact Nat.choose_pos hr'
  · exact Nat.choose_pos (r.pred_le.trans hr')
#align finset.card_div_choose_le_card_shadow_div_choose Finset.card_div_choose_le_card_shadow_div_choose

end LocalLym

/-! ### LYM inequality -/


section Lym

section Falling

variable [DecidableEq α] (k : ℕ) (𝒜 : Finset (Finset α))

/-- `falling k 𝒜` is all the finsets of cardinality `k` which are a subset of something in `𝒜`. -/
def falling : Finset (Finset α) :=
  𝒜.sup <| powersetLen k
#align finset.falling Finset.falling

variable {𝒜 k} {s : Finset α}

theorem mem_falling : s ∈ falling k 𝒜 ↔ (∃ t ∈ 𝒜, s ⊆ t) ∧ s.card = k := by
  simp_rw [falling, mem_sup, mem_powerset_len, exists_and_right]
#align finset.mem_falling Finset.mem_falling

variable (𝒜 k)

theorem sized_falling : (falling k 𝒜 : Set (Finset α)).Sized k := fun s hs => (mem_falling.1 hs).2
#align finset.sized_falling Finset.sized_falling

theorem slice_subset_falling : 𝒜 # k ⊆ falling k 𝒜 := fun s hs =>
  mem_falling.2 <| (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩
#align finset.slice_subset_falling Finset.slice_subset_falling

theorem falling_zero_subset : falling 0 𝒜 ⊆ {∅} :=
  subset_singleton_iff'.2 fun t ht => card_eq_zero.1 <| sized_falling _ _ ht
#align finset.falling_zero_subset Finset.falling_zero_subset

theorem slice_union_shadow_falling_succ : 𝒜 # k ∪ (∂ ) (falling (k + 1) 𝒜) = falling k 𝒜 :=
  by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, exists_prop, mem_falling]
  constructor
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    · exact ⟨⟨s, h.1, subset.refl _⟩, h.2⟩
    refine' ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, _⟩
    rw [card_erase_of_mem ha, hs]
    rfl
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    by_cases s ∈ 𝒜
    · exact Or.inl ⟨h, hs⟩
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_not_mem h).symm)
    refine' Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, _⟩, a, mem_insert_self _ _, erase_insert ha⟩
    rw [card_insert_of_not_mem ha, hs]
#align finset.slice_union_shadow_falling_succ Finset.slice_union_shadow_falling_succ

variable {𝒜 k}

/-- The shadow of `falling m 𝒜` is disjoint from the `n`-sized elements of `𝒜`, thanks to the
antichain property. -/
theorem IsAntichain.disjoint_slice_shadow_falling {m n : ℕ}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) : Disjoint (𝒜 # m) ((∂ ) (falling n 𝒜)) :=
  disjoint_right.2 fun s h₁ h₂ =>
    by
    simp_rw [mem_shadow_iff, exists_prop, mem_falling] at h₁
    obtain ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩ := h₁
    refine' h𝒜 (slice_subset h₂) ht _ ((erase_subset _ _).trans hst)
    rintro rfl
    exact not_mem_erase _ _ (hst ha)
#align is_antichain.disjoint_slice_shadow_falling IsAntichain.disjoint_slice_shadow_falling

/-- A bound on any top part of the sum in LYM in terms of the size of `falling k 𝒜`. -/
theorem le_card_falling_div_choose [Fintype α] (hk : k ≤ Fintype.card α)
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r in range (k + 1),
        ((𝒜 # (Fintype.card α - r)).card : 𝕜) / (Fintype.card α).choose (Fintype.card α - r)) ≤
      (falling (Fintype.card α - k) 𝒜).card / (Fintype.card α).choose (Fintype.card α - k) :=
  by
  induction' k with k ih
  · simp only [tsub_zero, cast_one, cast_le, sum_singleton, div_one, choose_self, range_one]
    exact card_le_of_subset (slice_subset_falling _ _)
  rw [succ_eq_add_one] at *
  rw [sum_range_succ, ← slice_union_shadow_falling_succ,
    card_disjoint_union h𝒜.disjoint_slice_shadow_falling, cast_add, _root_.add_div, add_comm]
  rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
  exact
    add_le_add_left
      ((ih <| le_of_succ_le hk).trans <|
        card_div_choose_le_card_shadow_div_choose (tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' <|
          sized_falling _ _)
      _
#align finset.le_card_falling_div_choose Finset.le_card_falling_div_choose

end Falling

variable {𝒜 : Finset (Finset α)} {s : Finset α} {k : ℕ}

/-- The **Lubell-Yamamoto-Meshalkin inequality**. If `𝒜` is an antichain, then the sum of the
proportion of elements it takes from each layer is less than `1`. -/
theorem sum_card_slice_div_choose_le_one [Fintype α]
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r in range (Fintype.card α + 1), ((𝒜 # r).card : 𝕜) / (Fintype.card α).choose r) ≤ 1 := by
  classical
    rw [← sum_flip]
    refine' (le_card_falling_div_choose le_rfl h𝒜).trans _
    rw [div_le_iff] <;> norm_cast
    ·
      simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        (sized_falling 0 𝒜).card_le
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one
#align finset.sum_card_slice_div_choose_le_one Finset.sum_card_slice_div_choose_le_one

end Lym

/-! ### Sperner's theorem -/


/-- **Sperner's theorem**. The size of an antichain in `finset α` is bounded by the size of the
maximal layer in `finset α`. This precisely means that `finset α` is a Sperner order. -/
theorem IsAntichain.sperner [Fintype α] {𝒜 : Finset (Finset α)}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  classical
    suffices
      (∑ r in Iic (Fintype.card α),
          ((𝒜 # r).card : ℚ) / (Fintype.card α).choose (Fintype.card α / 2)) ≤
        1
      by
      rwa [← sum_div, ← Nat.cast_sum, div_le_one, cast_le, sum_card_slice] at this
      norm_cast
      exact choose_pos (Nat.div_le_self _ _)
    rw [Iic_eq_Icc, ← Ico_succ_right, bot_eq_zero, Ico_zero_eq_range]
    refine' (sum_le_sum fun r hr => _).trans (sum_card_slice_div_choose_le_one h𝒜)
    rw [mem_range] at hr
    refine' div_le_div_of_le_left _ _ _ <;> norm_cast
    · exact Nat.zero_le _
    · exact choose_pos (lt_succ_iff.1 hr)
    · exact choose_le_middle _ _
#align is_antichain.sperner IsAntichain.sperner

end Finset

