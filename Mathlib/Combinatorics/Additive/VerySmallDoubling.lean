/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Bhavik Mehta
-/
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Qify

/-!
# Sets with very small doubling

For a finset `A` in a group, its *doubling* is `#(A * A) / #A`. This file characterises sets with
* no doubling as the sets which are either empty or translates of a subgroup.
  For the converse, use the existing facts from the pointwise API: `∅ ^ 2 = ∅` (`Finset.empty_pow`),
  `(a • H) ^ 2 = a ^ 2 • H ^ 2 = a ^ 2 • H` (`smul_pow`, `coe_set_pow`).
* doubling strictly less than `3 / 2` as the sets that are contained in a coset of a subgroup of
  size strictly less than `3 / 2 * #A`.
* doubling strictly less than `φ` as the set `A` such that `A * A⁻¹` is covered by at most some
  constant (depending only on the doubling) number of cosets of a finite subgroup of `G`.

## TODO

* Do we need versions stated using the doubling constant (`Finset.mulConst`)?
* Add characterisation of sets with doubling ≤ 2 - ε. See
  https://terrytao.wordpress.com/2011/03/12/hamidounes-freiman-kneser-theorem-for-nonabelian-groups.

## References

* [*An elementary non-commutative Freiman theorem*, Terence Tao](https://terrytao.wordpress.com/2009/11/10/an-elementary-non-commutative-freiman-theorem)
* [*Introduction to approximate groups*, Matthew Tointon][tointon2020]
-/

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {K : ℝ} {A B : Finset G} {a b c d x y : G}

/-! ### Doubling exactly `1` -/

@[to_additive]
private lemma smul_stabilizer_of_no_doubling_aux (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    a •> (stabilizer G A : Set G) = A ∧ (stabilizer G A : Set G) <• a = A := by
  have smul_A {a} (ha : a ∈ A) : a •> A = A * A :=
    eq_of_subset_of_card_le (smul_finset_subset_mul ha) (by simpa)
  have A_smul {a} (ha : a ∈ A) : A <• a = A * A :=
    eq_of_subset_of_card_le (op_smul_finset_subset_mul ha) (by simpa)
  have smul_A_eq_A_smul {a} (ha : a ∈ A) : a •> A = A <• a := by rw [smul_A ha, A_smul ha]
  have mul_mem_A_comm {x a} (ha : a ∈ A) : x * a ∈ A ↔ a * x ∈ A := by
    rw [← smul_mem_smul_finset_iff a, smul_A_eq_A_smul ha, ← op_smul_eq_mul, smul_comm,
      smul_mem_smul_finset_iff, smul_eq_mul]
  let H := stabilizer G A
  have inv_smul_A {a} (ha : a ∈ A) : a⁻¹ • (A : Set G) = H := by
    ext x
    rw [Set.mem_inv_smul_set_iff, smul_eq_mul]
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · simpa [← smul_A ha, mul_smul] using smul_A hx
    · norm_cast
      rwa [← mul_mem_A_comm ha, ← smul_eq_mul, ← mem_inv_smul_finset_iff, inv_mem hx]
  refine ⟨?_, ?_⟩
  · rw [← inv_smul_A ha, smul_inv_smul]
  · rw [← inv_smul_A ha, smul_comm]
    norm_cast
    rw [← smul_A_eq_A_smul ha, inv_smul_smul]

/-- A non-empty set with no doubling is the left translate of its stabilizer. -/
@[to_additive "A non-empty set with no doubling is the left-translate of its stabilizer."]
lemma smul_stabilizer_of_no_doubling (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    a •> (stabilizer G A : Set G) = A := (smul_stabilizer_of_no_doubling_aux hA ha).1

/-- A non-empty set with no doubling is the right translate of its stabilizer. -/
@[to_additive "A non-empty set with no doubling is the right translate of its stabilizer."]
lemma op_smul_stabilizer_of_no_doubling (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    (stabilizer G A : Set G) <• a = A := (smul_stabilizer_of_no_doubling_aux hA ha).2

/-! ### Doubling strictly less than `3 / 2` -/

private lemma big_intersection (ha : a ∈ B) (hb : b ∈ B) :
    2 * #A ≤ #((a • A) ∩ (b • A)) + #(B * A) := by
  have : #((a • A) ∪ (b • A)) ≤ #(B * A) := by
    refine card_le_card ?_
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul ha, smul_finset_subset_mul hb⟩
  refine (add_le_add_left this _).trans_eq' ?_
  rw [card_inter_add_card_union]
  simp only [card_smul_finset, two_mul]

private lemma le_card_smul_inter_smul (hA : #(B * A) ≤ K * #A) (ha : a ∈ B) (hb : b ∈ B) :
    (2 - K) * #A ≤ #((a • A) ∩ (b • A)) := by
  have : 2 * (#A : ℝ) ≤ #(a •> A ∩ b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith

private lemma lt_card_smul_inter_smul (hA : #(B * A) < K * #A) (ha : a ∈ B) (hb : b ∈ B) :
    (2 - K) * #A < #((a • A) ∩ (b • A)) := by
  have : 2 * (#A : ℝ) ≤ #(a •> A ∩ b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith

private lemma card_smul_inter_smul (A : Finset G) (x y : G) :
    #((x • A) ∩ (y • A)) = #{wz ∈ A ×ˢ A | wz.1 * wz.2⁻¹ = x⁻¹ * y} :=
  card_nbij' (fun z ↦ (x⁻¹ * z, y⁻¹ * z)) (fun zw ↦ x • zw.1)
    (by simp +contextual [← inv_smul_mem_iff, mul_assoc])
    (by simp +contextual [← inv_smul_mem_iff]; simp +contextual [mul_inv_eq_iff_eq_mul, mul_assoc])
    (by simp)
    (by simp +contextual [mul_inv_eq_iff_eq_mul, mul_assoc])

private lemma card_inter_smul (A : Finset G) (x : G) :
    #(A ∩ (x • A)) = #{yz ∈ A ×ˢ A | yz.1 * yz.2⁻¹ = x} := by simpa using card_smul_inter_smul _ 1 x

private lemma le_card_mul_inv_eq (hA : #(B * A) ≤ K * #A) (hx : x ∈ B⁻¹ * B) :
    (2 - K) * #A ≤ #{ab ∈ A ×ˢ A | ab.1 * ab.2⁻¹ = x} := by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simpa [card_smul_inter_smul] using le_card_smul_inter_smul hA ha hb

private lemma lt_card_mul_inv_eq (hA : #(B * A) < K * #A) (hx : x ∈ B⁻¹ * B) :
    (2 - K) * #A < #{ab ∈ A ×ˢ A | ab.1 * ab.2⁻¹ = x} := by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simpa [card_smul_inter_smul] using lt_card_smul_inter_smul hA ha hb

private lemma mul_inv_eq_inv_mul_of_doubling_lt_two_aux (h : #(A * A) < 2 * #A) :
    A⁻¹ * A ⊆ A * A⁻¹ := by
  intro z
  simp only [mem_mul, forall_exists_index, and_imp, mem_inv,
    exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : (x • A ∩ y • A).Nonempty := by
    simpa using lt_card_smul_inter_smul (K := 2) (mod_cast h) hx hy
  simp only [mem_inter, mem_smul_finset, smul_eq_mul] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hzxwy, inv_mul_cancel_left]

-- TODO: is there a way to get wlog to make `mul_inv_eq_inv_mul_of_doubling_lt_two_aux` a goal?
-- ie wlog in the target rather than hypothesis
-- (BM: third time seeing this pattern)
-- I'm thinking something like wlog_suffices, where I could write
-- wlog_suffices : A⁻¹ * A ⊆ A * A⁻¹
-- which reverts *everything* (just like wlog does) and makes the side goal A⁻¹ * A = A * A⁻¹
-- under the assumption A⁻¹ * A ⊆ A * A⁻¹
-- and changes the main goal to A⁻¹ * A ⊆ A * A⁻¹
/-- If `A` has doubling strictly less than `2`, then `A * A⁻¹ = A⁻¹ * A`. -/
lemma mul_inv_eq_inv_mul_of_doubling_lt_two (h : #(A * A) < 2 * #A) : A * A⁻¹ = A⁻¹ * A := by
  refine Subset.antisymm ?_ (mul_inv_eq_inv_mul_of_doubling_lt_two_aux h)
  simpa using
    mul_inv_eq_inv_mul_of_doubling_lt_two_aux (A := A⁻¹) (by simpa [← mul_inv_rev] using h)

private lemma weaken_doubling (h : #(A * A) < (3 / 2 : ℚ) * #A) : #(A * A) < 2 * #A := by
  rw [← Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  linarith only [h]

private lemma nonempty_of_doubling (h : #(A * A) < (3 / 2 : ℚ) * #A) : A.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  simp at h

/-- If `A` has doubling strictly less than `3 / 2`, then `A⁻¹ * A` is a subgroup.

Note that this is sharp: `A = {0, 1}` in `ℤ` has doubling `3 / 2` and `A⁻¹ * A` isn't a subgroup. -/
def invMulSubgroup (A : Finset G) (h : #(A * A) < (3 / 2 : ℚ) * #A) : Subgroup G where
  carrier := A⁻¹ * A
  one_mem' := by
    have ⟨x, hx⟩ : A.Nonempty := nonempty_of_doubling h
    exact ⟨x⁻¹, inv_mem_inv hx, x, by simp [hx]⟩
  inv_mem' := by
    intro x
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, mem_coe,
      and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    norm_cast
    have h₁ x (hx : x ∈ A) y (hy : y ∈ A) : (1 / 2 : ℚ) * #A < #(x • A ∩ y • A) := by
      convert lt_card_smul_inter_smul (by simpa using Rat.cast_strictMono (K := ℝ) h) hx hy
      norm_num
      simp [← Rat.cast_lt (K := ℝ)]
    intro a c ha hc
    simp only [mem_mul, mem_inv'] at ha hc
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨c, hc, d, hd, rfl⟩ := hc
    have h₂ : (1 / 2 : ℚ) * #A < #(A ∩ (a * b)⁻¹ • A) := by
      refine (h₁ b hb _ ha).trans_le ?_
      rw [← card_smul_finset b⁻¹]
      simp [smul_smul, smul_finset_inter]
    have h₃ : (1 / 2 : ℚ) * #A < #(A ∩ (c * d) • A) := by
      refine (h₁ _ hc d hd).trans_le ?_
      rw [← card_smul_finset c]
      simp [smul_smul, smul_finset_inter]
    have ⟨t, ht⟩ : ((A ∩ (c * d) • A) ∩ (A ∩ (a * b)⁻¹ • A)).Nonempty := by
      rw [← card_pos, ← Nat.cast_pos (α := ℚ)]
      have := card_inter_add_card_union (A ∩ (c * d) • A) (A ∩ (a * b)⁻¹ • A)
      rw [← Nat.cast_inj (R := ℚ), Nat.cast_add, Nat.cast_add] at this
      have : (#((A ∩ (c * d) • A) ∪ (A ∩ (a * b)⁻¹ • A)) : ℚ) ≤ #A := by
        rw [Nat.cast_le, ← inter_union_distrib_left]
        exact card_le_card inter_subset_left
      linarith
    simp only [inter_inter_inter_comm, inter_self, mem_inter, ← inv_smul_mem_iff, inv_inv,
      smul_eq_mul, mul_assoc, mul_inv_rev] at ht
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), mem_mul]
    exact ⟨a * b * t, by simp [ht, mul_assoc], ((c * d)⁻¹ * t)⁻¹, by simp [ht, mul_assoc]⟩

lemma invMulSubgroup_eq_inv_mul (A : Finset G) (h) : (invMulSubgroup A h : Set G) = A⁻¹ * A := rfl

lemma invMulSubgroup_eq_mul_inv (A : Finset G) (h) : (invMulSubgroup A h : Set G) = A * A⁻¹ := by
  rw [invMulSubgroup_eq_inv_mul, eq_comm]
  norm_cast
  exact mul_inv_eq_inv_mul_of_doubling_lt_two (by qify at h ⊢; linarith)

instance (A : Finset G) (h) : Fintype (invMulSubgroup A h) := by
  simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, mem_coe]; infer_instance

private lemma weak_invMulSubgroup_bound (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    #(A⁻¹ * A) < 2 * #A := by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ a (ha : a ∈ A⁻¹ * A) : (1 / 2 : ℚ) * #A < #{xy ∈ A ×ˢ A | xy.1 * xy.2⁻¹ = a} := by
    convert lt_card_mul_inv_eq (by simpa using Rat.cast_strictMono (K := ℝ) h) ha
    norm_num
    simp [← Rat.cast_lt (K := ℝ)]
  have h₂ : ∀ x ∈ A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x ∈ A⁻¹ * A := by
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, ha, b⁻¹, by simp [hb], rfl⟩
  have : ((1 / 2 : ℚ) * #A) * #(A⁻¹ * A) < (#A : ℚ) ^ 2 := by
    rw [← Nat.cast_pow, sq, ← card_product, card_eq_sum_card_fiberwise h₂, Nat.cast_sum]
    refine (sum_lt_sum_of_nonempty (by simp [h₀]) h₁).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
  have : (0 : ℚ) < #A := by simpa [card_pos]
  rw [← Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  -- passing between ℕ- and ℚ-inequalities is annoying, here and above
  nlinarith

private lemma A_subset_aH (a : G) (ha : a ∈ A) : A ⊆ a • (A⁻¹ * A) := by
  rw [← smul_mul_assoc]
  exact subset_mul_right _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])

private lemma subgroup_strong_bound_left (h : #(A * A) < (3 / 2 : ℚ) * #A) (a : G) (ha : a ∈ A) :
    A * A ⊆ a • op a • (A⁻¹ * A) := by
  have h₁ : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj, coe_mul, coe_mul, ← invMulSubgroup_eq_inv_mul _ h, coe_mul_coe]
  have h₂ : a • op a • (A⁻¹ * A) = (a • (A⁻¹ * A)) * (op a • (A⁻¹ * A)) := by
    rw [mul_smul_comm, smul_mul_assoc, h₁, smul_comm]
  rw [h₂]
  refine mul_subset_mul (A_subset_aH a ha) ?_
  rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), ← mul_smul_comm]
  exact subset_mul_left _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])

private lemma subgroup_strong_bound_right (h : #(A * A) < (3 / 2 : ℚ) * #A) (a : G) (ha : a ∈ A) :
    a • op a • (A⁻¹ * A) ⊆ A * A := by
  intro z hz
  simp only [mem_smul_finset, smul_eq_mul_unop, unop_op, smul_eq_mul, mem_mul, mem_inv,
    exists_exists_and_eq_and] at hz
  obtain ⟨d, ⟨b, hb, c, hc, rfl⟩, hz⟩ := hz
  let l : Finset G := A ∩ ((z * a⁻¹) • (A⁻¹ * A))
    -- ^ set of x ∈ A st ∃ y ∈ H a with x y = z
  let r : Finset G := (a • (A⁻¹ * A)) ∩ (z • A⁻¹)
    -- ^ set of x ∈ a H st ∃ y ∈ A with x y = z
  have : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj, coe_mul, coe_mul, ← invMulSubgroup_eq_inv_mul _ h, coe_mul_coe]
  have hl : l = A := by
    rw [inter_eq_left, ← this, subset_smul_finset_iff]
    simp only [← hz, mul_inv_rev, inv_inv, ← mul_assoc]
    refine smul_finset_subset_mul ?_
    simp [mul_mem_mul, ha, hb, hc]
  have hr : r = z • A⁻¹ := by
    rw [inter_eq_right, ← this, mul_assoc _ A,
      ← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), subset_smul_finset_iff]
    simp only [← mul_assoc, smul_smul]
    refine smul_finset_subset_mul ?_
    simp [← hz, mul_mem_mul, ha, hb, hc]
  have lr : l ∪ r ⊆ a • (A⁻¹ * A) := by
    rw [union_subset_iff, hl]
    exact ⟨A_subset_aH a ha, inter_subset_left⟩
  have : #l = #A := by rw [hl]
  have : #r = #A := by rw [hr, card_smul_finset, card_inv]
  have : #(l ∪ r) < 2 * #A := by
    refine (card_le_card lr).trans_lt ?_
    rw [card_smul_finset]
    exact weak_invMulSubgroup_bound h
  have ⟨t, ht⟩ : (l ∩ r).Nonempty := by
    rw [← card_pos]
    linarith [card_inter_add_card_union l r]
  simp only [hl, hr, mem_inter, ← inv_smul_mem_iff, smul_eq_mul, mem_inv', mul_inv_rev,
    inv_inv] at ht
  rw [mem_mul]
  exact ⟨t, ht.1, t⁻¹ * z, ht.2, by simp⟩

open scoped RightActions in
lemma smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A)
    (ha : a ∈ A) : a •> ((A⁻¹ * A) <• a) = A * A :=
  (subgroup_strong_bound_right h a ha).antisymm (subgroup_strong_bound_left h a ha)

lemma card_inv_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    #(A⁻¹ * A) = #(A * A) := by
  obtain ⟨a, ha⟩ := nonempty_of_doubling h
  simp_rw [← smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves h ha, card_smul_finset]

lemma smul_inv_mul_eq_inv_mul_opSMul (h : #(A * A) < (3 / 2 : ℚ) * #A) (ha : a ∈ A) :
    a •> (A⁻¹ * A) = (A⁻¹ * A) <• a := by
  refine subset_antisymm ?_ ?_
  · rw [subset_smul_finset_iff, ← op_inv]
    calc
      a •> (A⁻¹ * A) <• a⁻¹ ⊆ a •> (A⁻¹ * A) * A⁻¹ := op_smul_finset_subset_mul (by simpa)
      _ ⊆ A * (A⁻¹ * A) * A⁻¹ := by gcongr; exact smul_finset_subset_mul (by simpa)
      _ = A⁻¹ * A := by
        simp_rw [← coe_inj, coe_mul]
        rw [← mul_assoc, ← invMulSubgroup_eq_mul_inv _ h, mul_assoc,
          ← invMulSubgroup_eq_mul_inv _ h, coe_mul_coe, invMulSubgroup_eq_inv_mul]
  · rw [subset_smul_finset_iff]
    calc
      a⁻¹ •> ((A⁻¹ * A) <• a) ⊆ A⁻¹ * (A⁻¹ * A) <• a := smul_finset_subset_mul (by simpa)
      _ ⊆ A⁻¹ * ((A⁻¹ * A) * A) := by gcongr; exact op_smul_finset_subset_mul (by simpa)
      _ = A⁻¹ * A := by
        rw [← mul_inv_eq_inv_mul_of_doubling_lt_two <| weaken_doubling h]
        simp_rw [← coe_inj, coe_mul]
        rw [mul_assoc, ← invMulSubgroup_eq_inv_mul _ h, ← mul_assoc,
          ← invMulSubgroup_eq_inv_mul _ h, ← invMulSubgroup_eq_mul_inv _ h, coe_mul_coe]

open scoped RightActions in
/-- If `A` has doubling strictly less than `3 / 2`, then there exists a subgroup `H` of the
normaliser of `A` of size strictly less than `3 / 2 * #A` such that `A` is a subset of a coset of
`H` (in fact a subset of `a • H` for every `a ∈ A`).

Note that this is sharp: `A = {0, 1}` in `ℤ` has doubling `3 / 2` and can't be covered by a subgroup
of size at most `2`.

This is Theorem 2.2.1 in [tointon2020]. -/
theorem doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H), Fintype.card H < (3 / 2 : ℚ) * #A ∧ ∀ a ∈ A,
      (A : Set G) ⊆ a • H ∧ a •> (H : Set G) = H <• a := by
  let H := invMulSubgroup A h
  refine ⟨H, inferInstance, ?_, fun a ha ↦ ⟨?_, ?_⟩⟩
  · simp [← Nat.card_eq_fintype_card, invMulSubgroup, ← coe_mul, - coe_inv, H]
    rwa [Nat.card_eq_finsetCard, card_inv_mul_of_doubling_lt_three_halves h]
  · rw [invMulSubgroup_eq_inv_mul]
    exact_mod_cast A_subset_aH a ha
  · simpa [H, invMulSubgroup_eq_inv_mul, ← coe_inv, ← coe_mul, ← coe_smul_finset]
      using smul_inv_mul_eq_inv_mul_opSMul h ha

/-! ### Doubling strictly less than `φ` -/

omit [DecidableEq G] in
private lemma op_smul_eq_of_mem {H : Subgroup G} {c : Set G} {x : G}
    (hc : c ∈ orbit Gᵐᵒᵖ (H : Set G)) (hx : x ∈ c) : H <• x = c := by
  obtain ⟨⟨a⟩, rfl⟩ := hc
  change _ = _ <• _
  rw [eq_comm, smul_eq_iff_eq_inv_smul, ← op_inv, op_smul_op_smul, rightCoset_mem_rightCoset]
  rwa [← op_smul_eq_mul, op_inv, ← SetLike.mem_coe, ← Set.mem_smul_set_iff_inv_smul_mem]

/-- Underlying structure for the set of representatives of a finite set of right cosets -/
private structure RCosRepFin (G : Type*) [Group G] [DecidableEq G] where
  H : Subgroup G
  A : Finset G
  preZ : Set (Set G)
  fin_preZ : preZ.Finite
  preZ' : Finset (Set G)
  chooseZ' : Set G → G
  chooseZ'_spec : ∀ cH ∈ preZ', chooseZ' cH ∈ cH ∩ (↑H * ↑A)
  Z' : Finset G
  toH : G → G
  toH_mem_H : ∀ z ∈ Z', toH z ∈ ↑H
  toA : G → G
  toA_mem_A : ∀ z ∈ Z', toA z ∈ A
  toH_mul_toA : ∀ z ∈ Z', toH z * toA z = z
  toZ : G → G
  toZ_comp_chooseZ'_mem_self {c : Set G} (hc : c ∈ preZ') : toZ (chooseZ' c) ∈ c
  Z : Finset G

private noncomputable def rCosRepFin (H : Subgroup G) [Fintype H] {A : Finset G}
    (hA : A.Nonempty) : RCosRepFin G := by
  -- we first take all right cosets that intersect `A`, show that there is finitely many
  -- of them and take for `Z'` a set of representatives of all these cosets; then we
  -- multiply every element of `Z'` with an appropriate element of `H` to make `Z ⊆ A`
  classical
  let preZ := {cH ∈ orbit Gᵐᵒᵖ (H : Set G) | (cH ∩ (H * A)).Nonempty}
  have fin_preZ : preZ.Finite := by
    obtain ⟨a, ha⟩ := hA
    let f_preZ : Set G → (H : Set G) * (A : Set G) := fun cH =>
      if h : cH ∈ preZ
      then ⟨Classical.choose h.2, by
        apply And.right at h
        apply Classical.choose_spec at h
        apply Set.mem_of_mem_inter_right at h
        exact h⟩
      else ⟨1 * a, Set.mul_mem_mul (H.one_mem) ha⟩

    have inj_f_preZ : Set.InjOn f_preZ preZ := by
      unfold Set.InjOn
      intro c₁ hc₁ c₂ hc₂ hc₁c₂
      unfold f_preZ at hc₁c₂
      simp_all only [↓reduceDIte, Subtype.mk.injEq]
      let s := Classical.choose hc₁.2
      have s_mem_c₁ : s ∈ c₁ := by
        apply And.right at hc₁
        apply Classical.choose_spec at hc₁
        exact Set.mem_of_mem_inter_left hc₁
      have s_mem_c₂ : s ∈ c₂ := by
        apply And.right at hc₂
        apply Classical.choose_spec at hc₂
        rw [← hc₁c₂] at hc₂
        exact Set.mem_of_mem_inter_left hc₂
      rw [← op_smul_eq_of_mem hc₁.1 s_mem_c₁, ← op_smul_eq_of_mem hc₂.1 s_mem_c₂]

    exact Finite.Set.finite_of_finite_image preZ inj_f_preZ

  let preZ' := fin_preZ.toFinset
  have elts_preZ'_nonempty (cH : Set G) (hcH : cH ∈ preZ') : (cH ∩ (H * A)).Nonempty := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf] at hcH
    exact hcH.2

  choose! chooseZ' chooseZ'_spec using elts_preZ'_nonempty
  let Z' := image chooseZ' preZ'

  have Z'_subset_HA : (Z' : Set G) ⊆ H * A := by
    simpa only [coe_image, Set.image_subset_iff, Z'] using fun x hx ↦ (chooseZ'_spec _ hx).2

  change ∀ (z : G), z ∈ (Z' : Set G) → z ∈ (H : Set G) * A at Z'_subset_HA
  simp only [mem_coe, Set.mem_mul] at Z'_subset_HA
  choose! toH toH_mem_H toA toA_mem_A toH_mul_toA using Z'_subset_HA
  let toZ := fun z' => (toH z')⁻¹ * z'

  have toZ_comp_chooseZ'_mem_self {c : Set G} (hc : c ∈ preZ')
      : toZ (chooseZ' c) ∈ c := by
    unfold toZ
    nth_rw 1 [← op_smul_eq_of_mem ((Set.Finite.mem_toFinset _).mp hc).1 (chooseZ'_spec _ hc).1]
    apply mem_rightCoset
    apply H.inv_mem
    exact toH_mem_H _ (mem_image_of_mem chooseZ' hc)

  let Z := image toZ Z'
  exact ⟨H, A, preZ, fin_preZ, preZ', chooseZ', chooseZ'_spec, Z', toH, toH_mem_H, toA,
          toA_mem_A, toH_mul_toA, toZ, toZ_comp_chooseZ'_mem_self, Z⟩

-- TODO: Here `Z` is defined by extracting a representative from each coset and the definitional
-- property is actually not (explicitely) proved as it is not needed here; as far as I could check,
-- no such coset representing set is available in the library at this point, although it might be
-- useful independently of this section
/-- Given a finite subset `A` of group `G` and a subgroup `H ≤ G`, right coset representing set of
`H * A` is a subset `Z` of `A` such that `H * Z = H * A` and `∀ z₁ z₂ ∈ Z → Hz₁ ≠ Hz₂` -/
private noncomputable def rightCosetRepresentingFinset (H : Subgroup G) [Fintype H] {A : Finset G}
    (hA : A.Nonempty) : Finset G :=
  (rCosRepFin H hA).Z

private lemma rightCosetRepresentingFinset_subset_finset (H : Subgroup G) [Fintype H] {A : Finset G}
    (hA : A.Nonempty) : rightCosetRepresentingFinset H hA ⊆ A := by
  intro z hz
  obtain ⟨z', hz'₁, (hz'₂ : ((rCosRepFin H hA).toH z')⁻¹ * z' = z)⟩ := mem_image.mp hz
  rw [← hz'₂, inv_mul_eq_of_eq_mul (Eq.symm ((rCosRepFin H hA).toH_mul_toA z' hz'₁))]
  exact (rCosRepFin H hA).toA_mem_A z' hz'₁

private lemma mul_rightCosetRepresentingFinset_eq_mul_set (H : Subgroup G) [Fintype H]
    {A : Finset G} (hA : A.Nonempty) : (H : Set G) * (rightCosetRepresentingFinset H hA) = H * A
    := by
  have H_eq_HH : (H : Set G) = H * H := by simp only [coe_mul_coe]
  let rcrf := rCosRepFin H hA
  apply Set.Subset.antisymm (Set.mul_subset_mul_left
          (coe_subset.mpr (rightCosetRepresentingFinset_subset_finset H hA)))
  intro x hx
  obtain ⟨h, hh, a, ha, hha⟩ := Set.mem_mul.mp hx
  rw [← hha, H_eq_HH, mul_assoc]
  apply Set.mul_mem_mul hh
  let ca := (H : Set G) <• a
  have ca_mem_preZ' : ca ∈ rcrf.preZ' := by
    change ca ∈ rcrf.fin_preZ.toFinset
    rw [Set.Finite.mem_toFinset]
    change ca ∈ {cH ∈ orbit Gᵐᵒᵖ (H : Set G) | (cH ∩ (H * A)).Nonempty}
    rw [Set.mem_setOf]
    constructor
    · simp_all only [coe_mul_coe, SetLike.mem_coe, mem_coe, mem_orbit, ca]
    · use a
      constructor
      · rw [← one_mul a]
        exact mem_rightCoset a (one_mem H)
      · rw [← one_mul a]
        exact Set.mul_mem_mul H.one_mem ha
  let z := rcrf.toZ (rcrf.chooseZ' ca)
  have z_mem_ca : z ∈ ca := rcrf.toZ_comp_chooseZ'_mem_self (ca_mem_preZ')
  have z_mem_Z : z ∈ rightCosetRepresentingFinset H hA :=
    mem_image_of_mem _ (mem_image_of_mem _ ca_mem_preZ')
  have a_mem_Hz : a ∈ (H: Set G) <• z := by
    rw [mem_rightCoset_iff, SetLike.mem_coe]
    rw [mem_rightCoset_iff, SetLike.mem_coe] at z_mem_ca
    apply inv_mem at z_mem_ca
    simp_all only [coe_mul_coe, SetLike.mem_coe, mem_coe, mul_inv_rev, inv_inv]
  exact Set.op_smul_set_subset_mul z_mem_Z a_mem_Hz

private lemma mul_rightCosetRepresentingFinset_eq_mul_finset (H : Subgroup G) [Fintype H]
    {A : Finset G} (hA : A.Nonempty)
    : Set.toFinset H * (rightCosetRepresentingFinset H hA) = Set.toFinset H * A := by
  simpa only [← coe_inj, coe_mul, Set.coe_toFinset]
    using mul_rightCosetRepresentingFinset_eq_mul_set H hA

private lemma card_mul_rightCosetRepresentingFinset_eq_mul_card (H : Subgroup G) [Fintype H]
    {A : Finset G} (hA : A.Nonempty) : #(Set.toFinset H * (rightCosetRepresentingFinset H hA))
    = Fintype.card H * #(rightCosetRepresentingFinset H hA) := by
  let rcrf := rCosRepFin H hA
  simp only [← SetLike.coe_sort_coe, ← Set.toFinset_card, card_mul_iff, Set.coe_toFinset]
  unfold Set.InjOn
  simp only [Set.mem_prod, SetLike.mem_coe, mem_coe, and_imp, Prod.forall, Prod.mk.injEq]
  intro h z hh (hz : z ∈ image rcrf.toZ rcrf.Z')
        g t hg (ht : t ∈ image rcrf.toZ rcrf.Z') hyp
  rw [mem_image] at hz ht

  obtain ⟨z', (hz'₁ : z' ∈ image rcrf.chooseZ' rcrf.preZ'), hz'₂⟩ := hz
  obtain ⟨t', (ht'₁ : t' ∈ image rcrf.chooseZ' rcrf.preZ'), ht'₂⟩ := ht
  rw [mem_image] at hz'₁ ht'₁

  obtain ⟨cz, hcz₁, hcz₂⟩ := hz'₁
  have hcz₃ : z ∈ cz := by simp only [← hz'₂, ← hcz₂, rcrf.toZ_comp_chooseZ'_mem_self hcz₁]
  change cz ∈ rcrf.fin_preZ.toFinset at hcz₁
  rw [Set.Finite.mem_toFinset rcrf.fin_preZ] at hcz₁
  have hcz₄ := op_smul_eq_of_mem hcz₁.1 hcz₃

  obtain ⟨ct, hct₁, hct₂⟩ := ht'₁
  have hct₃ : t ∈ ct := by simp only [← ht'₂, ← hct₂, rcrf.toZ_comp_chooseZ'_mem_self hct₁]
  change ct ∈ rcrf.fin_preZ.toFinset at hct₁
  rw [Set.Finite.mem_toFinset rcrf.fin_preZ] at hct₁
  have hct₄ := op_smul_eq_of_mem hct₁.1 hct₃

  rw [← inv_mul_eq_iff_eq_mul, ← mul_assoc] at hyp
  rw [← hyp, op_mul, ← smul_smul, rightCoset_mem_rightCoset H (H.mul_mem (H.inv_mem hg) hh),
      hcz₄] at hct₄
  rw [← hct₄, hcz₂] at hct₂
  apply congr_arg rcrf.toZ at hct₂
  rw [hz'₂, ht'₂] at hct₂
  rw [hct₂, mul_eq_right, inv_mul_eq_one] at hyp
  exact ⟨Eq.symm hyp, hct₂⟩

open goldenRatio in
/-- If `A` has doubling `K` strictly less than `φ`, then `A * A⁻¹` is covered by
at most a constant number of cosets of a finite subgroup of `G`. -/
theorem doubling_lt_golden_ratio (hK₁ : 1 < K) (hKφ : K < φ)
    (hA₁ : #(A⁻¹ * A) ≤ K * #A) (hA₂ : #(A * A⁻¹) ≤ K * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      #Z ≤ (2 - K) * K / ((φ - K) * (K - ψ)) ∧ (H : Set G) * Z = A * A⁻¹ := by
  classical
  -- Some useful initial calculations
  have K_pos : 0 < K := by positivity
  have hK₀ : 0 < K := by positivity
  have hKφ' : 0 < φ - K := by linarith
  have hKψ' : 0 < K - ψ := by linarith [goldConj_neg]
  have hK₂' : 0 < 2 - K := by linarith [gold_lt_two]
  have const_pos : 0 < K * (2 - K) / ((φ - K) * (K - ψ)) := by positivity
  -- We dispatch the trivial case `A = ∅` separately.
  obtain rfl | A_nonempty := A.eq_empty_or_nonempty
  · exact ⟨⊥, inferInstance, ∅, by simp; positivity⟩
  -- In the case where `A` is non-empty, we consider the set `S := A * A⁻¹` and its stabilizer `H`.
  let S := A * A⁻¹
  let H := stabilizer G S
  -- `S` is finite and non-empty (because `A` is), and therefore `H` is finite too.
  have S_nonempty : S.Nonempty := by simpa [S]
  have : Finite H := by simpa [H] using stabilizer_finite (by simpa) S.finite_toSet
  cases nonempty_fintype H
  -- By definition, `H * S = S`.
  have H_mul_S : (H : Set G) * S = S := by simp [H, ← stabilizer_coe_finset]
  -- Since `H` is a subgroup, find a finite set `Z ⊆ S` such that `H * Z = S` and `|H| * |Z| = |S|`.
  let Z := rightCosetRepresentingFinset H S_nonempty
  have H_mul_Z : (H : Set G) * Z = S := by
    simp [Z, mul_rightCosetRepresentingFinset_eq_mul_set H S_nonempty, H_mul_S]
  have H_toFinset_mul_Z : Set.toFinset H * Z = S := by simpa [← Finset.coe_inj]
  have card_H_mul_card_Z : Fintype.card H * #Z = #S := by
    rw [← card_mul_rightCosetRepresentingFinset_eq_mul_card H S_nonempty]
    exact congr_arg _ H_toFinset_mul_Z
  -- It remains to show that `|Z| ≤ C(K)` for some `C(K)` depending only on `K`.
  refine ⟨H, inferInstance, Z, ?_, mod_cast H_mul_Z⟩
  -- This is equivalent to showing that `|H| ≥ c(K)|S|` for some `c(K)` depending only on `K`.
  suffices ((φ - K) * (K - ψ)) / ((2 - K) * K) * #S ≤ Fintype.card H by
    calc
          (#Z : ℝ)
      _ = (Fintype.card H / #S : ℝ)⁻¹ := by simp [← card_H_mul_card_Z]
      _ ≤ (((φ - K) * (K - ψ) / ((2 - K) * K) * #S) / #S)⁻¹ := by gcongr
      _ = (2 - K) * K / ((φ - K) * (K - ψ)) := by
        have : (#S : ℝ) ≠ 0 := by positivity
        simp [this]
  -- Write `r(z)` the number of representations of `z ∈ S` as `x * y⁻¹` for `x, y ∈ A`.
  let r z : ℕ := #{xy ∈ A ×ˢ A | xy.1 * xy.2⁻¹ = z}
  -- `r` is invariant under inverses.
  have r_inv z : r z⁻¹ = r z := by
    apply card_nbij' Prod.swap Prod.swap <;> simp +contextual [← inv_eq_iff_eq_inv]
  -- We show that every `z ∈ S` with at least `(K - 1)|A|` representations lies in `H`,
  -- and that such `z` make up a proportion of at least `(2 - K) / ((φ - K) * (K - ψ))` of `S`.
  calc
        (φ - K) * (K - ψ) / ((2 - K) * K) * #S
    _ ≤ #{z ∈ S | (K - 1) * #A < r z} := ?_
    _ ≤ #(H : Set G).toFinset := ?_
    _ = Fintype.card H := by simp
  -- First, let's show that a large proportion of all `z ∈ S` have many representations.
  · -- Let `l` be that number.
    set l : ℕ := #{z ∈ S | (K - 1) * #A < r z} with hk
    -- By upper-bounding `r(z)` by `(K - 1)|A|` for the `z` with few representations,
    -- and by `|A|` for the `z` with many representations,
    -- we get `|A|² ≤ l|A| + (|S| - l)(K - 1)|A| = ((2 - K)l + (K - 1)|S|)|A|`.
    have ineq : #A * #A ≤ ((2 - K) * l + (K - 1) * #S) * #A := by
      calc
            (#A : ℝ) * #A
        _ = #(A ×ˢ A) := by simp
        _ = ∑ z ∈ S, ↑(r z) := by
          norm_cast
          exact card_eq_sum_card_fiberwise fun xy hxy ↦
            mul_mem_mul (mem_product.mp hxy).1 (inv_mem_inv (mem_product.mp hxy).2)
        _ = ∑ z ∈ S with (K - 1) * #A < r z, ↑(r z) + ∑ z ∈ S with r z ≤ (K - 1) * #A, ↑(r z) := by
          norm_cast; simp_rw [← not_lt, sum_filter_add_sum_filter_not]
        _ ≤ ∑ z ∈ S with (K - 1) * #A < r z, ↑(#A)
          + ∑ z ∈ S with r z ≤ (K - 1) * #A, (K - 1) * #A := by
          gcongr with z hz z hz
          · simp only [r, ← card_inter_smul]
            gcongr
            exact inter_subset_left
          · simp_all
        _ = l * #A + (#S - l) * (K - 1) * #A := by
          simp [hk, ← not_lt, mul_assoc,
            ← S.filter_card_add_filter_neg_card_eq_card fun z ↦ (K - 1) * #A < r z]
        _ = ((2 - K) * l + (K - 1) * #S) * #A := by ring
    -- By cancelling `|A|` on both sides, we get `|A| ≤ (2 - K)l + (K - 1)|S|`.
    -- By composing with `|S| ≤ K|A|`, we get `|S| ≤ (2 - K)Kl + (K - 1)K|S|`.
    have : 0 < #A := by positivity
    replace ineq := calc
          (#S : ℝ)
      _ ≤ K * #A := ‹_›
      _ ≤ K * ((2 - K) * l + (K - 1) * #S) := by
        gcongr; exact le_of_mul_le_mul_right ineq <| by positivity
      _ = (2 - K) * K * l + (K - 1) * K * #S := by ring
    -- Now, we are done.
    calc
          (φ - K) * (K - ψ) / ((2 - K) * K) * #S
      _ = (φ - K) * (K - ψ) * #S / ((2 - K) * K) := div_mul_eq_mul_div ..
      _ ≤ (2 - K) * K * l / ((2 - K) * K) := by
        have := gold_mul_goldConj
        have := gold_add_goldConj
        rw [show (φ - K) * (K - ψ) = 1 - (K - 1) * K by grind]
        gcongr ?_ / _
        linarith [ineq]
      _ = l := by field_simp
  -- Second, let's show that the `z ∈ S` with many representations are in `H`.
  · gcongr
    simp only [subset_iff, mem_filter, Set.mem_toFinset, SetLike.mem_coe, and_imp]
    rintro z hz hrz
    -- It's enough to show that `z * w ∈ S` for all `w ∈ S`.
    rw [mem_stabilizer_finset']
    rintro w hw
    -- Since `w ∈ S` and `|A⁻¹ * A| ≤ K|A|`, we know that `r(w) ≥ (2 - K)|A|`.
    have hrw : (2 - K) * #A ≤ r w := le_card_mul_inv_eq hA₁ (by simpa)
    -- But also `r(z⁻¹) = r(z) > (K - 1)|A|`.
    rw [← r_inv] at hrz
    simp only [r, ← card_inter_smul] at hrz hrw
    -- By inclusion-exclusion, we get that `(z⁻¹ •> A) ∩ (w •> A)` is non-empty.
    have : (0 : ℝ) < #((z⁻¹ •> A) ∩ (w •> A)) := by
      have : (#((A ∩ z⁻¹ •> A) ∩ (A ∩ w •> A)) : ℝ) ≤ #(z⁻¹ •> A ∩ w •> A) := by
        gcongr <;> exact inter_subset_right
      have : (#((A ∩ z⁻¹ •> A) ∪ (A ∩ w •> A)) : ℝ) ≤ #A := by
        gcongr; exact union_subset inter_subset_left inter_subset_left
      have :
          (#((A ∩ z⁻¹ •> A) ∩ (A ∩ w •> A)) + #((A ∩ z⁻¹ •> A) ∪ (A ∩ w •> A)) : ℝ) =
            #(A ∩ z⁻¹ •> A) + #(A ∩ w •> A) := mod_cast card_inter_add_card_union ..
      linarith
    -- This is exactly what we set out to prove.
    simpa [S, card_smul_inter_smul, Finset.Nonempty, mem_mul, mem_inv, -mem_inv', and_assoc]
      using this

end Finset
