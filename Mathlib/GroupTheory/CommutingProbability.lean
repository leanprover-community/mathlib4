/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Qify

/-!
# Commuting Probability
This file introduces the commuting probability of finite groups.

## Main definitions
* `commProb`: The commuting probability of a finite type with a multiplication operation.

## TODO
* Neumann's theorem.
-/

assert_not_exists Ideal TwoSidedIdeal

noncomputable section

open Fintype

variable (M : Type*) [Mul M]

/-- The commuting probability of a finite type with a multiplication operation. -/
def commProb : ℚ :=
  Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2

theorem commProb_def :
    commProb M = Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2 :=
  rfl

theorem commProb_prod (M' : Type*) [Mul M'] : commProb (M × M') = commProb M * commProb M' := by
  simp_rw [commProb_def, div_mul_div_comm, Nat.card_prod, Nat.cast_mul, mul_pow, ← Nat.cast_mul,
    ← Nat.card_prod, Commute, SemiconjBy, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_pi {α : Type*} (i : α → Type*) [Fintype α] [∀ a, Mul (i a)] :
    commProb (∀ a, i a) = ∏ a, commProb (i a) := by
  simp_rw [commProb_def, Finset.prod_div_distrib, Finset.prod_pow, ← Nat.cast_prod,
    ← Nat.card_pi, Commute, SemiconjBy, funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_function {α β : Type*} [Fintype α] [Mul β] :
    commProb (α → β) = (commProb β) ^ Fintype.card α := by
  rw [commProb_pi, Finset.prod_const, Finset.card_univ]

@[simp]
theorem commProb_eq_zero_of_infinite [Infinite M] : commProb M = 0 :=
  div_eq_zero_iff.2 (Or.inl (Nat.cast_eq_zero.2 Nat.card_eq_zero_of_infinite))

variable [Finite M]

theorem commProb_pos [h : Nonempty M] : 0 < commProb M :=
  h.elim fun x ↦
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)

theorem commProb_le_one : commProb M ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (sq_nonneg (Nat.card M : ℚ))
  rw [← Nat.cast_pow, Nat.cast_le, sq, ← Nat.card_prod]
  apply Finite.card_subtype_le

variable {M}

theorem commProb_eq_one_iff [h : Nonempty M] :
    commProb M = 1 ↔ Std.Commutative ((· * ·) : M → M → M) := by
  classical
  haveI := Fintype.ofFinite M
  rw [commProb, ← Set.coe_setOf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [div_eq_one_iff_eq, ← Nat.cast_pow, Nat.cast_inj, sq, ← card_prod,
    set_fintype_card_eq_univ_iff, Set.eq_univ_iff_forall]
  · exact ⟨fun h ↦ ⟨fun x y ↦ h (x, y)⟩, fun h x ↦ h.comm x.1 x.2⟩
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr card_ne_zero)

variable (G : Type*) [Group G]

theorem commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G := by
  rw [commProb, card_comm_eq_card_conjClasses_mul_card, Nat.cast_mul, sq]
  by_cases h : (Nat.card G : ℚ) = 0
  · rw [h, zero_mul, div_zero, div_zero]
  · exact mul_div_mul_right _ _ h

variable {G}
variable [Finite G] (H : Subgroup G)

theorem Subgroup.commProb_subgroup_le : commProb H ≤ commProb G * (H.index : ℚ) ^ 2 := by
  /- After rewriting with `commProb_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def, commProb_def, div_le_iff₀, mul_assoc, ← mul_pow, ← Nat.cast_mul,
    mul_comm H.index, H.card_mul_index, div_mul_cancel₀, Nat.cast_le]
  · refine Nat.card_le_card_of_injective (fun p ↦ ⟨⟨p.1.1, p.1.2⟩, Subtype.ext_iff.mp p.2⟩) ?_
    exact fun p q h ↦ by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr Finite.card_pos.ne')
  · exact pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2

theorem Subgroup.commProb_quotient_le [H.Normal] : commProb (G ⧸ H) ≤ commProb G * Nat.card H := by
  /- After rewriting with `commProb_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def', commProb_def', div_le_iff₀, mul_assoc, ← Nat.cast_mul, ← Subgroup.index,
    H.card_mul_index, div_mul_cancel₀, Nat.cast_le]
  · apply Nat.card_le_card_of_surjective
    show Function.Surjective (ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.mk''_surjective
  · exact Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  · exact Nat.cast_pos.mpr Finite.card_pos

variable (G)

theorem inv_card_commutator_le_commProb : (↑(Nat.card (commutator G)))⁻¹ ≤ commProb G :=
  (inv_le_iff_one_le_mul₀ (Nat.cast_pos.mpr Finite.card_pos)).mpr
    (le_trans (ge_of_eq (commProb_eq_one_iff.mpr ⟨(Abelianization.commGroup G).mul_comm⟩))
      (commutator G).commProb_quotient_le)

-- Construction of group with commuting probability 1/n
namespace DihedralGroup

lemma commProb_odd {n : ℕ} (hn : Odd n) :
    commProb (DihedralGroup n) = (n + 3) / (4 * n) := by
  rw [commProb_def', DihedralGroup.card_conjClasses_odd hn, nat_card]
  qify [show 2 ∣ n + 3 by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.odd_iff.mp hn]]
  rw [div_div, ← mul_assoc]
  congr
  norm_num

private lemma div_two_lt {n : ℕ} (h0 : n ≠ 0) : n / 2 < n :=
  Nat.div_lt_self (Nat.pos_of_ne_zero h0) (lt_add_one 1)

private lemma div_four_lt : {n : ℕ} → (h0 : n ≠ 0) → (h1 : n ≠ 1) → n / 4 + 1 < n
  | 0 | 1 | 2 | 3 => by decide
  | n + 4 => by cutsat

/-- A list of Dihedral groups whose product will have commuting probability `1 / n`. -/
def reciprocalFactors (n : ℕ) : List ℕ :=
  if _ : n = 0 then [0]
  else if _ : n = 1 then []
  else if Even n then
    3 :: reciprocalFactors (n / 2)
  else
    n % 4 * n :: reciprocalFactors (n / 4 + 1)

@[simp] lemma reciprocalFactors_zero : reciprocalFactors 0 = [0] := by
  unfold reciprocalFactors; rfl

@[simp] lemma reciprocalFactors_one : reciprocalFactors 1 = [] := by
  unfold reciprocalFactors; rfl

lemma reciprocalFactors_even {n : ℕ} (h0 : n ≠ 0) (h2 : Even n) :
    reciprocalFactors n = 3 :: reciprocalFactors (n / 2) := by
  have h1 : n ≠ 1 := by
    rintro rfl
    norm_num at h2
  rw [reciprocalFactors, dif_neg h0, dif_neg h1, if_pos h2]

lemma reciprocalFactors_odd {n : ℕ} (h1 : n ≠ 1) (h2 : Odd n) :
    reciprocalFactors n = n % 4 * n :: reciprocalFactors (n / 4 + 1) := by
  have h0 : n ≠ 0 := by
    rintro rfl
    norm_num [← Nat.not_even_iff_odd] at h2
  rw [reciprocalFactors, dif_neg h0, dif_neg h1, if_neg (Nat.not_even_iff_odd.2 h2)]

/-- A finite product of Dihedral groups. -/
abbrev Product (l : List ℕ) : Type :=
  ∀ i : Fin l.length, DihedralGroup l[i]

lemma commProb_nil : commProb (Product []) = 1 := by
  simp [Product, commProb_pi]

lemma commProb_cons (n : ℕ) (l : List ℕ) :
    commProb (Product (n :: l)) = commProb (DihedralGroup n) * commProb (Product l) := by
  simp only [commProb_pi, Fin.prod_univ_succ, Fin.getElem_fin, Fin.val_succ, Fin.val_zero,
    List.getElem_cons_zero, List.length_cons, List.getElem_cons_succ]

/-- Construction of a group with commuting probability `1 / n`. -/
theorem commProb_reciprocal (n : ℕ) :
    commProb (Product (reciprocalFactors n)) = 1 / n := by
  by_cases h0 : n = 0
  · rw [h0, reciprocalFactors_zero, commProb_cons, commProb_nil, mul_one, Nat.cast_zero, div_zero]
    apply commProb_eq_zero_of_infinite
  by_cases h1 : n = 1
  · rw [h1, reciprocalFactors_one, commProb_nil, Nat.cast_one, div_one]
  rcases Nat.even_or_odd n with h2 | h2
  · have := div_two_lt h0
    rw [reciprocalFactors_even h0 h2, commProb_cons, commProb_reciprocal (n / 2),
        commProb_odd (by decide)]
    simp [field, h2.two_dvd]
    norm_num
  · have := div_four_lt h0 h1
    rw [reciprocalFactors_odd h1 h2, commProb_cons, commProb_reciprocal (n / 4 + 1)]
    have key : n % 4 = 1 ∨ n % 4 = 3 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp h2)
    have hn : Odd (n % 4) := by rcases key with h | h <;> rw [h] <;> decide
    rw [commProb_odd (hn.mul h2), div_mul_div_comm, mul_one, div_eq_div_iff, one_mul] <;> norm_cast
    · have h0 : (n % 4) ^ 2 + 3 = n % 4 * 4 := by rcases key with h | h <;> rw [h] <;> norm_num
      have h1 := (Nat.div_add_mod n 4).symm
      zify at h0 h1 ⊢
      linear_combination (h0 + h1 * (n % 4)) * n
    · positivity [hn.pos.ne']

end DihedralGroup
