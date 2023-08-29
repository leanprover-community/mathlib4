/-
Copyright (c) 2022 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Combinatorics.DoubleCounting
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Data.Rat.Order

#align_import combinatorics.set_family.lym from "leanprover-community/mathlib"@"861a26926586cd46ff80264d121cdb6fa0e35cc1"

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `Finset.card_div_choose_le_card_shadow_div_choose`: Local Lubell-Yamamoto-Meshalkin inequality.
  The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜` does.
* `Finset.sum_card_slice_div_choose_le_one`: Lubell-Yamamoto-Meshalkin inequality. The sum of
  densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `IsAntichain.sperner`: Sperner's theorem. The size of any antichain in `Finset α` is at most the
  size of the maximal layer of `Finset α`. It is a corollary of `sum_card_slice_div_choose_le_one`.

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

variable {𝕜 α : Type*} [LinearOrderedField 𝕜]

namespace Finset

/-! ### Local LYM inequality -/


section LocalLYM
variable [DecidableEq α] [Fintype α]
  {𝒜 : Finset (Finset α)} {r : ℕ}
/-- The downward **local LYM inequality**, with cancelled denominators. `𝒜` takes up less of `α^(r)`
(the finsets of card `r`) than `∂𝒜` takes up of `α^(r - 1)`. -/
theorem card_mul_le_card_shadow_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    𝒜.card * r ≤ (∂ 𝒜).card * (Fintype.card α - r + 1) := by
  let i : DecidableRel ((· ⊆ ·) : Finset α → Finset α → Prop) := fun _ _ => Classical.dec _
  -- ⊢ card 𝒜 * r ≤ card (∂ 𝒜) * (Fintype.card α - r + 1)
  refine' card_mul_le_card_mul' (· ⊆ ·) (fun s hs => _) (fun s hs => _)
  -- ⊢ r ≤ card (bipartiteBelow (fun x x_1 => x ⊆ x_1) (∂ 𝒜) s)
  · rw [← h𝒜 hs, ← card_image_of_injOn s.erase_injOn]
    -- ⊢ card (image (erase s) s) ≤ card (bipartiteBelow (fun x x_1 => x ⊆ x_1) (∂ 𝒜) …
    refine' card_le_of_subset _
    -- ⊢ image (erase s) s ⊆ bipartiteBelow (fun x x_1 => x ⊆ x_1) (∂ 𝒜) s
    simp_rw [image_subset_iff, mem_bipartiteBelow]
    -- ⊢ ∀ (x : α), x ∈ s → erase s x ∈ ∂ 𝒜 ∧ erase s x ⊆ s
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
    -- 🎉 no goals
  refine' le_trans _ tsub_tsub_le_tsub_add
  -- ⊢ card (bipartiteAbove (fun x x_1 => x ⊆ x_1) 𝒜 s) ≤ Fintype.card α - (r - 1)
  rw [← (Set.Sized.shadow h𝒜) hs, ← card_compl, ← card_image_of_injOn (insert_inj_on' _)]
  -- ⊢ card (bipartiteAbove (fun x x_1 => x ⊆ x_1) 𝒜 s) ≤ card (image (fun a => ins …
  refine' card_le_of_subset fun t ht => _
  -- ⊢ t ∈ image (fun a => insert a s) sᶜ
  -- porting note: commented out the following line
  -- infer_instance
  rw [mem_bipartiteAbove] at ht
  -- ⊢ t ∈ image (fun a => insert a s) sᶜ
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe, h𝒜.empty_mem_iff, coe_eq_singleton]
    rintro rfl
    rw [shadow_singleton_empty] at hs
    exact not_mem_empty s hs
  have h := exists_eq_insert_iff.2 ⟨ht.2, by
    rw [(sized_shadow_iff this).1 (Set.Sized.shadow h𝒜) ht.1, (Set.Sized.shadow h𝒜) hs]⟩
  rcases h with ⟨a, ha, rfl⟩
  -- ⊢ insert a s ∈ image (fun a => insert a s) sᶜ
  exact mem_image_of_mem _ (mem_compl.2 ha)
  -- 🎉 no goals
#align finset.card_mul_le_card_shadow_mul Finset.card_mul_le_card_shadow_mul

/-- The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` (the finsets of card `r`)
than `∂𝒜` takes up of `α^(r - 1)`. -/
theorem card_div_choose_le_card_shadow_div_choose (hr : r ≠ 0)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : (𝒜.card : 𝕜) / (Fintype.card α).choose r
    ≤ (∂ 𝒜).card / (Fintype.card α).choose (r - 1) := by
  obtain hr' | hr' := lt_or_le (Fintype.card α) r
  -- ⊢ ↑(card 𝒜) / ↑(Nat.choose (Fintype.card α) r) ≤ ↑(card (∂ 𝒜)) / ↑(Nat.choose  …
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    -- ⊢ 0 ≤ ↑(card (∂ 𝒜)) / ↑(Nat.choose (Fintype.card α) (r - 1))
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
    -- 🎉 no goals
  replace h𝒜 := card_mul_le_card_shadow_mul h𝒜
  -- ⊢ ↑(card 𝒜) / ↑(Nat.choose (Fintype.card α) r) ≤ ↑(card (∂ 𝒜)) / ↑(Nat.choose  …
  rw [div_le_div_iff] <;> norm_cast
                          -- ⊢ card 𝒜 * Nat.choose (Fintype.card α) (r - 1) ≤ card (∂ 𝒜) * Nat.choose (Fint …
                          -- ⊢ 0 < Nat.choose (Fintype.card α) r
                          -- ⊢ 0 < Nat.choose (Fintype.card α) (r - 1)
  · cases' r with r
    -- ⊢ card 𝒜 * Nat.choose (Fintype.card α) (zero - 1) ≤ card (∂ 𝒜) * Nat.choose (F …
    · exact (hr rfl).elim
      -- 🎉 no goals
    rw [Nat.succ_eq_add_one] at *
    -- ⊢ card 𝒜 * Nat.choose (Fintype.card α) (r + 1 - 1) ≤ card (∂ 𝒜) * Nat.choose ( …
    rw [tsub_add_eq_add_tsub hr', add_tsub_add_eq_tsub_right] at h𝒜
    -- ⊢ card 𝒜 * Nat.choose (Fintype.card α) (r + 1 - 1) ≤ card (∂ 𝒜) * Nat.choose ( …
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    -- ⊢ card 𝒜 * Nat.choose (Fintype.card α) (r + 1 - 1) * (r + 1) ≤ card (∂ 𝒜) * Na …
    convert Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    -- ⊢ card 𝒜 * Nat.choose (Fintype.card α) (r + 1 - 1) * (r + 1) = card 𝒜 * (r + 1 …
    · simp [mul_assoc, Nat.choose_succ_right_eq]
      -- ⊢ Nat.choose (Fintype.card α) r * (r + 1) = (r + 1) * Nat.choose (Fintype.card …
      exact Or.inl (mul_comm _ _)
      -- 🎉 no goals
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      -- ⊢ Nat.choose (Fintype.card α) r * (Fintype.card α - r) = (Fintype.card α - r)  …
      exact Or.inl (mul_comm _ _)
      -- 🎉 no goals
  · exact Nat.choose_pos hr'
    -- 🎉 no goals
  · exact Nat.choose_pos (r.pred_le.trans hr')
    -- 🎉 no goals
#align finset.card_div_choose_le_card_shadow_div_choose Finset.card_div_choose_le_card_shadow_div_choose

end LocalLYM

/-! ### LYM inequality -/


section LYM

section Falling

variable [DecidableEq α] (k : ℕ) (𝒜 : Finset (Finset α))

/-- `falling k 𝒜` is all the finsets of cardinality `k` which are a subset of something in `𝒜`. -/
def falling : Finset (Finset α) :=
  𝒜.sup <| powersetLen k
#align finset.falling Finset.falling

variable {𝒜 k} {s : Finset α}

theorem mem_falling : s ∈ falling k 𝒜 ↔ (∃ t ∈ 𝒜, s ⊆ t) ∧ s.card = k := by
  simp_rw [falling, mem_sup, mem_powersetLen]
  -- ⊢ (∃ v, v ∈ 𝒜 ∧ s ⊆ v ∧ card s = k) ↔ (∃ t, t ∈ 𝒜 ∧ s ⊆ t) ∧ card s = k
  aesop
  -- 🎉 no goals
#align finset.mem_falling Finset.mem_falling

variable (𝒜 k)

theorem sized_falling : (falling k 𝒜 : Set (Finset α)).Sized k := fun _ hs => (mem_falling.1 hs).2
#align finset.sized_falling Finset.sized_falling

theorem slice_subset_falling : 𝒜 # k ⊆ falling k 𝒜 := fun s hs =>
  mem_falling.2 <| (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩
#align finset.slice_subset_falling Finset.slice_subset_falling

theorem falling_zero_subset : falling 0 𝒜 ⊆ {∅} :=
  subset_singleton_iff'.2 fun _ ht => card_eq_zero.1 <| sized_falling _ _ ht
#align finset.falling_zero_subset Finset.falling_zero_subset

theorem slice_union_shadow_falling_succ : 𝒜 # k ∪ ∂ (falling (k + 1) 𝒜) = falling k 𝒜 := by
  ext s
  -- ⊢ s ∈ 𝒜 # k ∪ ∂ (falling (k + 1) 𝒜) ↔ s ∈ falling k 𝒜
  simp_rw [mem_union, mem_slice, mem_shadow_iff, mem_falling]
  -- ⊢ (s ∈ 𝒜 ∧ card s = k ∨ ∃ t, ((∃ t_1, t_1 ∈ 𝒜 ∧ t ⊆ t_1) ∧ card t = k + 1) ∧ ∃ …
  constructor
  -- ⊢ (s ∈ 𝒜 ∧ card s = k ∨ ∃ t, ((∃ t_1, t_1 ∈ 𝒜 ∧ t ⊆ t_1) ∧ card t = k + 1) ∧ ∃ …
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    -- ⊢ (∃ t, t ∈ 𝒜 ∧ s ⊆ t) ∧ card s = k
    · exact ⟨⟨s, h.1, Subset.refl _⟩, h.2⟩
      -- 🎉 no goals
    refine' ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, _⟩
    -- ⊢ card (erase s a) = k
    rw [card_erase_of_mem ha, hs]
    -- ⊢ k + 1 - 1 = k
    rfl
    -- 🎉 no goals
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    -- ⊢ s ∈ 𝒜 ∧ card s = k ∨ ∃ t, ((∃ t_1, t_1 ∈ 𝒜 ∧ t ⊆ t_1) ∧ card t = k + 1) ∧ ∃  …
    by_cases h : s ∈ 𝒜
    -- ⊢ s ∈ 𝒜 ∧ card s = k ∨ ∃ t, ((∃ t_1, t_1 ∈ 𝒜 ∧ t ⊆ t_1) ∧ card t = k + 1) ∧ ∃  …
    · exact Or.inl ⟨h, hs⟩
      -- 🎉 no goals
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_not_mem h).symm)
    -- ⊢ s ∈ 𝒜 ∧ card s = k ∨ ∃ t, ((∃ t_1, t_1 ∈ 𝒜 ∧ t ⊆ t_1) ∧ card t = k + 1) ∧ ∃  …
    refine' Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, _⟩, a, mem_insert_self _ _, erase_insert ha⟩
    -- ⊢ card (insert a s) = k + 1
    rw [card_insert_of_not_mem ha, hs]
    -- 🎉 no goals
#align finset.slice_union_shadow_falling_succ Finset.slice_union_shadow_falling_succ

variable {𝒜 k}

/-- The shadow of `falling m 𝒜` is disjoint from the `n`-sized elements of `𝒜`, thanks to the
antichain property. -/
theorem IsAntichain.disjoint_slice_shadow_falling {m n : ℕ}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) : Disjoint (𝒜 # m) (∂ (falling n 𝒜)) :=
  disjoint_right.2 fun s h₁ h₂ => by
    simp_rw [mem_shadow_iff, mem_falling] at h₁
    -- ⊢ False
    obtain ⟨s, ⟨⟨t, ht, hst⟩, _⟩, a, ha, rfl⟩ := h₁
    -- ⊢ False
    refine' h𝒜 (slice_subset h₂) ht _ ((erase_subset _ _).trans hst)
    -- ⊢ erase s a ≠ t
    rintro rfl
    -- ⊢ False
    exact not_mem_erase _ _ (hst ha)
    -- 🎉 no goals
#align finset.is_antichain.disjoint_slice_shadow_falling Finset.IsAntichain.disjoint_slice_shadow_falling

/-- A bound on any top part of the sum in LYM in terms of the size of `falling k 𝒜`. -/
theorem le_card_falling_div_choose [Fintype α] (hk : k ≤ Fintype.card α)
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r in range (k + 1),
        ((𝒜 # (Fintype.card α - r)).card : 𝕜) / (Fintype.card α).choose (Fintype.card α - r)) ≤
      (falling (Fintype.card α - k) 𝒜).card / (Fintype.card α).choose (Fintype.card α - k) := by
  induction' k with k ih
  -- ⊢ ∑ r in range (zero + 1), ↑(card (𝒜 # (Fintype.card α - r))) / ↑(Nat.choose ( …
  · simp only [tsub_zero, cast_one, cast_le, sum_singleton, div_one, choose_self, range_one,
      zero_eq, zero_add, range_one, ge_iff_le, sum_singleton, nonpos_iff_eq_zero, tsub_zero,
      choose_self, cast_one, div_one, cast_le]
    exact card_le_of_subset (slice_subset_falling _ _)
    -- 🎉 no goals
  rw [succ_eq_add_one] at *
  -- ⊢ ∑ r in range (k + 1 + 1), ↑(card (𝒜 # (Fintype.card α - r))) / ↑(Nat.choose  …
  rw [sum_range_succ, ← slice_union_shadow_falling_succ,
    card_disjoint_union (IsAntichain.disjoint_slice_shadow_falling h𝒜), cast_add, _root_.add_div,
    add_comm]
  rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
  -- ⊢ ↑(card (𝒜 # (Fintype.card α - k - 1))) / ↑(Nat.choose (Fintype.card α) (Fint …
  exact
    add_le_add_left
      ((ih <| le_of_succ_le hk).trans <|
        card_div_choose_le_card_shadow_div_choose (tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' <|
          sized_falling _ _) _
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
    · simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        Set.Sized.card_le (sized_falling 0 𝒜)
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one
#align finset.sum_card_slice_div_choose_le_one Finset.sum_card_slice_div_choose_le_one

end LYM

/-! ### Sperner's theorem -/


/-- **Sperner's theorem**. The size of an antichain in `Finset α` is bounded by the size of the
maximal layer in `Finset α`. This precisely means that `Finset α` is a Sperner order. -/
theorem IsAntichain.sperner [Fintype α] {𝒜 : Finset (Finset α)}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  classical
    suffices (∑ r in Iic (Fintype.card α),
        ((𝒜 # r).card : ℚ) / (Fintype.card α).choose (Fintype.card α / 2)) ≤ 1 by
      rw [← sum_div, ← Nat.cast_sum, div_le_one] at this
      simp only [cast_le] at this
      rwa [sum_card_slice] at this
      simp only [cast_pos]
      exact choose_pos (Nat.div_le_self _ _)
    rw [Iic_eq_Icc, ← Ico_succ_right, bot_eq_zero, Ico_zero_eq_range]
    refine' (sum_le_sum fun r hr => _).trans (sum_card_slice_div_choose_le_one h𝒜)
    rw [mem_range] at hr
    refine' div_le_div_of_le_left _ _ _ <;> norm_cast
    · exact Nat.zero_le _
    · exact choose_pos (lt_succ_iff.1 hr)
    · exact choose_le_middle _ _
#align finset.is_antichain.sperner Finset.IsAntichain.sperner

end Finset
