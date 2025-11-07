/-
Copyright (c) 2022 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Data.NNRat.Order
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `Finset.local_lubell_yamamoto_meshalkin_inequality_div`: Local Lubell-Yamamoto-Meshalkin
  inequality. The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜`
  does.
* `Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`: Lubell-Yamamoto-Meshalkin
  inequality. The sum of densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `IsAntichain.sperner`: Sperner's theorem. The size of any antichain in `Finset α` is at most the
  size of the maximal layer of `Finset α`. It is a corollary of
  `lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`.

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
open scoped FinsetFamily

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

namespace Finset

/-! ### Local LYM inequality -/

section LocalLYM
variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {r : ℕ}

/-- The downward **local LYM inequality**, with cancelled denominators. `𝒜` takes up less of `α^(r)`
(the finsets of card `r`) than `∂𝒜` takes up of `α^(r - 1)`. -/
theorem local_lubell_yamamoto_meshalkin_inequality_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    #𝒜 * r ≤ #(∂ 𝒜) * (Fintype.card α - r + 1) := by
  let i : DecidableRel ((· ⊆ ·) : Finset α → Finset α → Prop) := fun _ _ => Classical.dec _
  refine card_mul_le_card_mul' (· ⊆ ·) (fun s hs => ?_) (fun s hs => ?_)
  · rw [← h𝒜 hs, ← card_image_of_injOn s.erase_injOn]
    refine card_le_card ?_
    simp_rw [image_subset_iff, mem_bipartiteBelow]
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
  refine le_trans ?_ tsub_tsub_le_tsub_add
  rw [← (Set.Sized.shadow h𝒜) hs, ← card_compl, ← card_image_of_injOn (insert_inj_on' _)]
  refine card_le_card fun t ht => ?_
  rw [mem_bipartiteAbove] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe, h𝒜.empty_mem_iff, coe_eq_singleton]
    rintro rfl
    rw [shadow_singleton_empty] at hs
    exact notMem_empty s hs
  have h := exists_eq_insert_iff.2 ⟨ht.2, by
    rw [(sized_shadow_iff this).1 (Set.Sized.shadow h𝒜) ht.1, (Set.Sized.shadow h𝒜) hs]⟩
  rcases h with ⟨a, ha, rfl⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_mul]
alias card_mul_le_card_shadow_mul := local_lubell_yamamoto_meshalkin_inequality_mul

/-- The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` (the finsets of card `r`)
than `∂𝒜` takes up of `α^(r - 1)`. -/
theorem local_lubell_yamamoto_meshalkin_inequality_div (hr : r ≠ 0)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : (#𝒜 : 𝕜) / (Fintype.card α).choose r
    ≤ #(∂ 𝒜) / (Fintype.card α).choose (r - 1) := by
  obtain hr' | hr' := lt_or_ge (Fintype.card α) r
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  replace h𝒜 := local_lubell_yamamoto_meshalkin_inequality_mul h𝒜
  rw [div_le_div_iff₀] <;> norm_cast
  · rcases r with - | r
    · exact (hr rfl).elim
    rw [tsub_add_eq_add_tsub hr', add_tsub_add_eq_tsub_right] at h𝒜
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    · simpa [mul_assoc, Nat.choose_succ_right_eq] using Or.inl (mul_comm _ _)
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
  · exact Nat.choose_pos hr'
  · exact Nat.choose_pos (r.pred_le.trans hr')

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_div]
alias card_div_choose_le_card_shadow_div_choose := local_lubell_yamamoto_meshalkin_inequality_div

end LocalLYM

/-! ### LYM inequality -/

section LYM

section Falling

variable [DecidableEq α] (k : ℕ) (𝒜 : Finset (Finset α))

/-- `falling k 𝒜` is all the finsets of cardinality `k` which are a subset of something in `𝒜`. -/
def falling : Finset (Finset α) :=
  𝒜.sup <| powersetCard k

variable {𝒜 k} {s : Finset α}

theorem mem_falling : s ∈ falling k 𝒜 ↔ (∃ t ∈ 𝒜, s ⊆ t) ∧ #s = k := by
  simp_rw [falling, mem_sup, mem_powersetCard]
  aesop

variable (𝒜 k)

theorem sized_falling : (falling k 𝒜 : Set (Finset α)).Sized k := fun _ hs => (mem_falling.1 hs).2

theorem slice_subset_falling : 𝒜 # k ⊆ falling k 𝒜 := fun s hs =>
  mem_falling.2 <| (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩

theorem falling_zero_subset : falling 0 𝒜 ⊆ {∅} :=
  subset_singleton_iff'.2 fun _ ht => card_eq_zero.1 <| sized_falling _ _ ht

theorem slice_union_shadow_falling_succ : 𝒜 # k ∪ ∂ (falling (k + 1) 𝒜) = falling k 𝒜 := by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, mem_falling]
  constructor
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    · exact ⟨⟨s, h.1, Subset.refl _⟩, h.2⟩
    refine ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, ?_⟩
    rw [card_erase_of_mem ha, hs]
    rfl
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    by_cases h : s ∈ 𝒜
    · exact Or.inl ⟨h, hs⟩
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_notMem h).symm)
    refine Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, ?_⟩, a, mem_insert_self _ _, erase_insert ha⟩
    rw [card_insert_of_notMem ha, hs]

variable {𝒜 k}

/-- The shadow of `falling m 𝒜` is disjoint from the `n`-sized elements of `𝒜`, thanks to the
antichain property. -/
theorem IsAntichain.disjoint_slice_shadow_falling {m n : ℕ}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) : Disjoint (𝒜 # m) (∂ (falling n 𝒜)) :=
  disjoint_right.2 fun s h₁ h₂ => by
    simp_rw [mem_shadow_iff, mem_falling] at h₁
    obtain ⟨s, ⟨⟨t, ht, hst⟩, _⟩, a, ha, rfl⟩ := h₁
    refine h𝒜 (slice_subset h₂) ht ?_ ((erase_subset _ _).trans hst)
    rintro rfl
    exact notMem_erase _ _ (hst ha)

/-- A bound on any top part of the sum in LYM in terms of the size of `falling k 𝒜`. -/
theorem le_card_falling_div_choose [Fintype α] (hk : k ≤ Fintype.card α)
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r ∈ range (k + 1),
        (#(𝒜 # (Fintype.card α - r)) : 𝕜) / (Fintype.card α).choose (Fintype.card α - r)) ≤
      (falling (Fintype.card α - k) 𝒜).card / (Fintype.card α).choose (Fintype.card α - k) := by
  induction k with
  | zero =>
    simp only [tsub_zero, cast_one, cast_le, sum_singleton, div_one, choose_self, range_one,
      zero_add, range_one, sum_singleton, tsub_zero,
      choose_self, cast_one, div_one, cast_le]
    exact card_le_card (slice_subset_falling _ _)
  | succ k ih =>
    rw [sum_range_succ, ← slice_union_shadow_falling_succ,
      card_union_of_disjoint (IsAntichain.disjoint_slice_shadow_falling h𝒜),
      cast_add, _root_.add_div, add_comm]
    rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
    grw [ih <| le_of_succ_le hk, local_lubell_yamamoto_meshalkin_inequality_div
      (tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' <| sized_falling _ _]

end Falling

variable [Fintype α] {𝒜 : Finset (Finset α)}

/-- The **Lubell-Yamamoto-Meshalkin inequality**, also known as the **LYM inequality**.

If `𝒜` is an antichain, then the sum of the proportion of elements it takes from each layer is less
than `1`. -/
theorem lubell_yamamoto_meshalkin_inequality_sum_card_div_choose
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    ∑ r ∈ range (Fintype.card α + 1), (#(𝒜 # r) / (Fintype.card α).choose r : 𝕜) ≤ 1 := by
  classical
    rw [← sum_flip]
    refine (le_card_falling_div_choose le_rfl h𝒜).trans ?_
    rw [div_le_iff₀] <;> norm_cast
    · simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        Set.Sized.card_le (sized_falling 0 𝒜)
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one

@[inherit_doc lubell_yamamoto_meshalkin_inequality_sum_card_div_choose]
alias sum_card_slice_div_choose_le_one := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose

/-- The **Lubell-Yamamoto-Meshalkin inequality**, also known as the **LYM inequality**.

If `𝒜` is an antichain, then the sum of `(#α.choose #s)⁻¹` over `s ∈ 𝒜` is less than `1`. -/
theorem lubell_yamamoto_meshalkin_inequality_sum_inv_choose
    (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    ∑ s ∈ 𝒜, ((Fintype.card α).choose #s : 𝕜)⁻¹ ≤ 1 := by
  calc
    _ = ∑ r ∈ range (Fintype.card α + 1),
        ∑ s ∈ 𝒜 with #s = r, ((Fintype.card α).choose r : 𝕜)⁻¹ := by
      rw [sum_fiberwise_of_maps_to']; simp [Nat.lt_succ_iff, card_le_univ]
    _ = ∑ r ∈ range (Fintype.card α + 1), (#(𝒜 # r) / (Fintype.card α).choose r : 𝕜) := by
      simp [slice, div_eq_mul_inv]
    _ ≤ 1 := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose h𝒜

/-! ### Sperner's theorem -/

/-- **Sperner's theorem**. The size of an antichain in `Finset α` is bounded by the size of the
maximal layer in `Finset α`. This precisely means that `Finset α` is a Sperner order. -/
theorem _root_.IsAntichain.sperner (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    #𝒜 ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  have : 0 < ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0) :=
    Nat.cast_pos.2 <| choose_pos (Nat.div_le_self _ _)
  have h := calc
    ∑ s ∈ 𝒜, ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0)⁻¹
    _ ≤ ∑ s ∈ 𝒜, ((Fintype.card α).choose #s : ℚ≥0)⁻¹ := by
      gcongr with s hs
      · exact mod_cast choose_pos s.card_le_univ
      · exact choose_le_middle _ _
    _ ≤ 1 := lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜
  simpa [mul_inv_le_iff₀' this] using h

end LYM
end Finset
