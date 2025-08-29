/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Order
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Positivity.Basic

/-!
# Density of a finite set

This defines the density of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.dens s`: Density of `s : Finset α` in `α` as a nonnegative rational number.

## Implementation notes

There are many other ways to talk about the density of a finset and provide its API:
1. Use the uniform measure
2. Define finitely additive functions and generalise the `Finset.card` API to it. This could either
  be done with
  a. A structure `FinitelyAdditiveFun`
  b. A typeclass `IsFinitelyAdditiveFun`

Solution 1 would mean importing measure theory in simple files (not necessarily bad, but not
amazing), and every single API lemma would require the user to prove that all the sets they are
talking about are measurable in the trivial sigma-algebra (quite terrible user experience).

Solution 2 would mean that some API lemmas about density don't contain `dens` in their name because
they are general results about finitely additive functions. But not all lemmas would be like that
either since some really are `dens`-specific. Hence the user would need to think about whether the
lemma they are looking for is generally true for finitely additive measure or whether it is
`dens`-specific.

On top of this, solution 2.a would break dot notation on `Finset.dens` (possibly fixable by
introducing notation for `⇑Finset.dens`) and solution 2.b would run the risk of being bad
performance-wise.

These considerations more generally apply to `Finset.card` and `Finset.sum` and demonstrate that
overengineering basic definitions is likely to hinder user experience.
-/

-- TODO
-- assert_not_exists Ring

open Function Multiset Nat

variable {𝕜 α β : Type*} [Fintype α]

namespace Finset
variable {s t : Finset α} {a b : α}

/-- Density of a finset.

`dens s` is the number of elements of `s` divided by the size of the ambient type `α`. -/
def dens (s : Finset α) : ℚ≥0 := s.card / Fintype.card α

lemma dens_eq_card_div_card (s : Finset α) : dens s = s.card / Fintype.card α := rfl

@[simp] lemma dens_empty : dens (∅ : Finset α) = 0 := by simp [dens]

@[simp] lemma dens_singleton (a : α) : dens ({a} : Finset α) = (Fintype.card α : ℚ≥0)⁻¹ := by
  simp [dens]

@[simp] lemma dens_cons (h : a ∉ s) : (s.cons a h).dens = dens s + (Fintype.card α : ℚ≥0)⁻¹ := by
  simp [dens, add_div]

@[simp] lemma dens_disjUnion (s t : Finset α) (h) : dens (s.disjUnion t h) = dens s + dens t := by
  simp_rw [dens, card_disjUnion, Nat.cast_add, add_div]

@[simp] lemma dens_eq_zero : dens s = 0 ↔ s = ∅ := by
  simp +contextual [dens, Fintype.card_eq_zero_iff, eq_empty_of_isEmpty]

lemma dens_ne_zero : dens s ≠ 0 ↔ s.Nonempty := dens_eq_zero.not.trans nonempty_iff_ne_empty.symm

@[simp] lemma dens_pos : 0 < dens s ↔ s.Nonempty := pos_iff_ne_zero.trans dens_ne_zero

protected alias ⟨_, Nonempty.dens_pos⟩ := dens_pos
protected alias ⟨_, Nonempty.dens_ne_zero⟩ := dens_ne_zero

@[gcongr]
lemma dens_le_dens (h : s ⊆ t) : dens s ≤ dens t :=
  div_le_div_of_nonneg_right (mod_cast card_mono h) <| by positivity

@[gcongr]
lemma dens_lt_dens (h : s ⊂ t) : dens s < dens t :=
  div_lt_div_of_pos_right (by gcongr) <| mod_cast calc
    0 ≤ #s := Nat.zero_le _
    _ < #t := by gcongr
    _ ≤ Fintype.card α := card_le_univ t

@[mono] lemma dens_mono : Monotone (dens : Finset α → ℚ≥0) := fun _ _ ↦ dens_le_dens
@[mono] lemma dens_strictMono : StrictMono (dens : Finset α → ℚ≥0) := fun _ _ ↦ dens_lt_dens

lemma dens_map_le [Fintype β] (f : α ↪ β) : dens (s.map f) ≤ dens s := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  simp_rw [dens, card_map]
  gcongr
  · exact mod_cast Fintype.card_pos
  · exact Fintype.card_le_of_injective _ f.2

@[simp] lemma dens_map_equiv [Fintype β] (e : α ≃ β) : (s.map e.toEmbedding).dens = s.dens := by
  simp [dens, Fintype.card_congr e]

lemma dens_image [Fintype β] [DecidableEq β] {f : α → β} (hf : Bijective f) (s : Finset α) :
    (s.image f).dens = s.dens := by
  simpa [map_eq_image, -dens_map_equiv] using dens_map_equiv (.ofBijective f hf)

@[simp] lemma card_mul_dens (s : Finset α) : Fintype.card α * s.dens = s.card := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  rw [dens, mul_div_cancel₀]
  exact mod_cast Fintype.card_ne_zero

@[simp] lemma dens_mul_card (s : Finset α) : s.dens * Fintype.card α = s.card := by
  rw [mul_comm, card_mul_dens]

section Semifield
variable [Semifield 𝕜] [CharZero 𝕜]

@[simp] lemma natCast_card_mul_nnratCast_dens (s : Finset α) :
    (Fintype.card α * s.dens : 𝕜) = s.card := mod_cast s.card_mul_dens

@[simp] lemma nnratCast_dens_mul_natCast_card (s : Finset α) :
    (s.dens * Fintype.card α : 𝕜) = s.card := mod_cast s.dens_mul_card

@[norm_cast] lemma nnratCast_dens (s : Finset α) : (s.dens : 𝕜) = s.card / Fintype.card α := by
  simp [dens]

end Semifield

section Nonempty
variable [Nonempty α]

@[simp] lemma dens_univ : dens (univ : Finset α) = 1 := by simp [dens, card_univ]

@[simp] lemma dens_eq_one : dens s = 1 ↔ s = univ := by
  simp [dens, div_eq_one_iff_eq, card_eq_iff_eq_univ]

lemma dens_ne_one : dens s ≠ 1 ↔ s ≠ univ := dens_eq_one.not

end Nonempty

@[simp] lemma dens_le_one : s.dens ≤ 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ

section Lattice
variable [DecidableEq α]

lemma dens_union_add_dens_inter (s t : Finset α) :
    dens (s ∪ t) + dens (s ∩ t) = dens s + dens t := by
  simp_rw [dens, ← add_div, ← Nat.cast_add, card_union_add_card_inter]

lemma dens_inter_add_dens_union (s t : Finset α) :
    dens (s ∩ t) + dens (s ∪ t) = dens s + dens t := by rw [add_comm, dens_union_add_dens_inter]

@[simp] lemma dens_union_of_disjoint (h : Disjoint s t) : dens (s ∪ t) = dens s + dens t := by
  rw [← disjUnion_eq_union s t h, dens_disjUnion _ _ _]

lemma dens_sdiff_add_dens_eq_dens (h : s ⊆ t) : dens (t \ s) + dens s = dens t := by
  simp [dens, ← card_sdiff_add_card_eq_card h, add_div]

lemma dens_sdiff_add_dens (s t : Finset α) : dens (s \ t) + dens t = (s ∪ t).dens := by
  rw [← dens_union_of_disjoint sdiff_disjoint, sdiff_union_self_eq_union]

lemma dens_sdiff_comm (h : card s = card t) : dens (s \ t) = dens (t \ s) :=
  add_left_injective (dens t) <| by
    simp_rw [dens_sdiff_add_dens, union_comm s, ← dens_sdiff_add_dens, dens, h]

@[simp]
lemma dens_sdiff_add_dens_inter (s t : Finset α) : dens (s \ t) + dens (s ∩ t) = dens s := by
  rw [← dens_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]

@[simp]
lemma dens_inter_add_dens_sdiff (s t : Finset α) : dens (s ∩ t) + dens (s \ t) = dens s := by
  rw [add_comm, dens_sdiff_add_dens_inter]

lemma dens_filter_add_dens_filter_not_eq_dens {α : Type*} [Fintype α] {s : Finset α}
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    dens {a ∈ s | p a} + dens {a ∈ s | ¬ p a} = dens s := by
  classical
  rw [← dens_union_of_disjoint (disjoint_filter_filter_neg ..), filter_union_filter_neg_eq]

lemma dens_union_le (s t : Finset α) : dens (s ∪ t) ≤ dens s + dens t :=
  dens_union_add_dens_inter s t ▸ le_add_of_nonneg_right zero_le'

lemma dens_le_dens_sdiff_add_dens : dens s ≤ dens (s \ t) + dens t :=
  dens_sdiff_add_dens s _ ▸ dens_le_dens subset_union_left

lemma dens_sdiff (h : s ⊆ t) : dens (t \ s) = dens t - dens s :=
  eq_tsub_of_add_eq (dens_sdiff_add_dens_eq_dens h)

lemma le_dens_sdiff (s t : Finset α) : dens t - dens s ≤ dens (t \ s) :=
  tsub_le_iff_right.2 dens_le_dens_sdiff_add_dens

end Lattice
end Finset
