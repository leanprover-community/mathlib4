/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Combinatorics.Additive.CovBySMul
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Combinatorics.Additive.SmallTripling

/-!
# Approximate subgroups

This file defines approximate subgroups of a group, namely symmetric sets `A` such that `A * A` can
be covered by a small number of translates of `A`.

## Main results

Approximate subgroups are a central concept in additive combinatorics, as a natural weakening and
flexible substitute of genuine subgroups. As such, they share numerous properties with subgroups:
* `IsApproximateSubgroup.image`: Group homomorphisms send approximate subgroups to approximate
  subgroups
* `IsApproximateSubgroup.pow_inter_pow`: The intersection of (non-trivial powers of) two approximate
  subgroups is an approximate subgroup. Warning: The intersection of two approximate subgroups isn't
  an approximate subgroup in general.

Approximate subgroups are close qualitatively and quantitatively to other concepts in additive
combinatorics:
* `IsApproximateSubgroup.card_pow_le`: An approximate subgroup has small powers.
* `IsApproximateSubgroup.of_small_tripling`: A set of small tripling can be made an approximate
  subgroup by squaring.

It can be readily confirmed that approximate subgroups are a weakening of subgroups:
* `isApproximateSubgroup_one`: A 1-approximate subgroup is the same thing as a subgroup.
-/

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A + A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
structure IsApproximateAddSubgroup {G : Type*} [AddGroup G] (K : ℝ) (A : Set G) : Prop where
  zero_mem : 0 ∈ A
  neg_eq_self : -A = A
  two_nsmul_covByVAdd : CovByVAdd G K (2 • A) A

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A * A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
@[to_additive]
structure IsApproximateSubgroup (K : ℝ) (A : Set G) : Prop where
  one_mem : 1 ∈ A
  inv_eq_self : A⁻¹ = A
  sq_covBySMul : CovBySMul G K (A ^ 2) A

namespace IsApproximateSubgroup

@[to_additive] lemma nonempty (hA : IsApproximateSubgroup K A) : A.Nonempty := ⟨1, hA.one_mem⟩

@[to_additive one_le]
lemma one_le (hA : IsApproximateSubgroup K A) : 1 ≤ K := by
  obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
  have hF₀ : F ≠ ∅ := by rintro rfl; simp [hA.nonempty.pow.ne_empty] at hSF
  exact hF.trans' <| by simpa [Finset.nonempty_iff_ne_empty]

@[to_additive]
lemma mono (hKL : K ≤ L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup L A where
  one_mem := hA.one_mem
  inv_eq_self := hA.inv_eq_self
  sq_covBySMul := hA.sq_covBySMul.mono hKL

@[to_additive]
lemma card_pow_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    ∀ {n}, #(A ^ n) ≤ K ^ (n - 1) * #A
  | 0 => by simpa using hA.nonempty
  | 1 => by simp
  | n + 2 => by
    obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
    calc
      (#(A ^ (n + 2)) : ℝ) ≤ #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by cutsat)
      _ ≤ #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ ≤ #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (n + 1) * #A := by gcongr

@[to_additive]
lemma card_mul_self_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    #(A * A) ≤ K * #A := by simpa [sq] using hA.card_pow_le (n := 2)

@[to_additive]
lemma image {F H : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup K (f '' A) where
  one_mem := ⟨1, hA.one_mem, map_one _⟩
  inv_eq_self := by simp [← Set.image_inv, hA.inv_eq_self]
  sq_covBySMul := by
    classical
    obtain ⟨F, hF, hAF⟩ := hA.sq_covBySMul
    refine ⟨F.image f, ?_, ?_⟩
    · calc
        (#(F.image f) : ℝ) ≤ #F := mod_cast F.card_image_le
        _ ≤ K := hF
    · simp only [← Set.image_pow, Finset.coe_image, ← Set.image_mul, smul_eq_mul] at hAF ⊢
      gcongr

@[to_additive]
lemma subgroup {S : Type*} [SetLike S G] [SubgroupClass S G] {H : S} :
    IsApproximateSubgroup 1 (H : Set G) where
  one_mem := OneMemClass.one_mem H
  inv_eq_self := inv_coe_set
  sq_covBySMul := ⟨{1}, by simp⟩

open Finset in
@[to_additive]
lemma of_small_tripling [DecidableEq G] {A : Finset G} (hA₁ : 1 ∈ A) (hAsymm : A⁻¹ = A)
    (hA : #(A ^ 3) ≤ K * #A) : IsApproximateSubgroup (K ^ 3) (A ^ 2 : Set G) where
  one_mem := by rw [sq, ← one_mul 1]; exact Set.mul_mem_mul hA₁ hA₁
  inv_eq_self := by simp [← inv_pow, hAsymm, ← coe_inv]
  sq_covBySMul := by
    replace hA := calc (#(A ^ 4 * A) : ℝ)
      _ = #(A ^ 5) := by rw [← pow_succ]
      _ ≤ K ^ 3 * #A := small_pow_of_small_tripling (by omega) hA hAsymm
    have hA₀ : A.Nonempty := ⟨1, hA₁⟩
    obtain ⟨F, -, hF, hAF⟩ := ruzsa_covering_mul hA₀ hA
    exact ⟨F, hF, by norm_cast; simpa [div_eq_mul_inv, pow_succ, mul_assoc, hAsymm] using hAF⟩

open Set in
@[to_additive]
lemma pow_inter_pow_covBySMul_sq_inter_sq
    (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    CovBySMul G (K ^ (m - 1) * L ^ (n - 1)) (A ^ m ∩ B ^ n) (A ^ 2 ∩ B ^ 2) := by
  classical
  obtain ⟨F₁, hF₁, hAF₁⟩ := hA.sq_covBySMul
  obtain ⟨F₂, hF₂, hBF₂⟩ := hB.sq_covBySMul
  have := hA.one_le
  choose f hf using exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul A B
  refine ⟨.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1)), ?_, ?_⟩
  · calc
      (#(.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) : ℝ)
      _ ≤ #(F₁ ^ (m - 1)) * #(F₂ ^ (n - 1)) := mod_cast Finset.card_image₂_le ..
      _ ≤ #F₁ ^ (m - 1) * #F₂ ^ (n - 1) := by gcongr <;> exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (m - 1) * L ^ (n - 1) := by gcongr
  · calc
      A ^ m ∩ B ^ n ⊆ (F₁ ^ (m - 1) * A) ∩ (F₂ ^ (n - 1) * B) := by
        gcongr <;> apply pow_subset_pow_mul_of_sq_subset_mul <;> norm_cast <;> omega
      _ = ⋃ (a ∈ F₁ ^ (m - 1)) (b ∈ F₂ ^ (n - 1)), a • A ∩ b • B := by
        simp_rw [← smul_eq_mul, ← iUnion_smul_set, iUnion₂_inter_iUnion₂]; norm_cast
      _ ⊆ ⋃ (a ∈ F₁ ^ (m - 1)) (b ∈ F₂ ^ (n - 1)), f a b • (A⁻¹ * A ∩ (B⁻¹ * B)) := by
        gcongr; exact hf ..
      _ = (Finset.image₂ f (F₁ ^ (m - 1)) (F₂ ^ (n - 1))) * (A ^ 2 ∩ B ^ 2) := by
        simp_rw [hA.inv_eq_self, hB.inv_eq_self, ← sq]
        rw [Finset.coe_image₂, ← smul_eq_mul, ← iUnion_smul_set, biUnion_image2]
        simp_rw [Finset.mem_coe]

open Set in
@[to_additive]
lemma pow_inter_pow (hA : IsApproximateSubgroup K A) (hB : IsApproximateSubgroup L B) (hm : 2 ≤ m)
    (hn : 2 ≤ n) :
    IsApproximateSubgroup (K ^ (2 * m - 1) * L ^ (2 * n - 1)) (A ^ m ∩ B ^ n) where
  one_mem := ⟨Set.one_mem_pow hA.one_mem, Set.one_mem_pow hB.one_mem⟩
  inv_eq_self := by simp_rw [inter_inv, ← inv_pow, hA.inv_eq_self, hB.inv_eq_self]
  sq_covBySMul := by
    refine (hA.pow_inter_pow_covBySMul_sq_inter_sq hB (by omega) (by omega)).subset ?_
      (by gcongr; exacts [hA.one_mem, hB.one_mem])
    calc
      (A ^ m ∩ B ^ n) ^ 2 ⊆ (A ^ m) ^ 2 ∩ (B ^ n) ^ 2 := Set.inter_pow_subset
      _ = A ^ (2 * m) ∩ B ^ (2 * n) := by simp [pow_mul']

end IsApproximateSubgroup

open Set in
/-- A `1`-approximate subgroup is the same thing as a subgroup. -/
@[to_additive (attr := simp)
/-- A `1`-approximate subgroup is the same thing as a subgroup. -/]
lemma isApproximateSubgroup_one {A : Set G} :
    IsApproximateSubgroup 1 (A : Set G) ↔ ∃ H : Subgroup G, H = A where
  mp hA := by
    suffices A * A ⊆ A from
      let H : Subgroup G :=
        { carrier := A
          one_mem' := hA.one_mem
          inv_mem' hx := by rwa [← hA.inv_eq_self, inv_mem_inv]
          mul_mem' hx hy := this (mul_mem_mul hx hy) }
      ⟨H, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : G, A * A ⊆ x • A := by
      obtain ⟨K, hK, hKA⟩ := hA.sq_covBySMul
      simp only [Nat.cast_le_one, Finset.card_le_one_iff_subset_singleton,
        Finset.subset_singleton_iff] at hK
      obtain ⟨x, rfl | rfl⟩ := hK
      · simp [hA.nonempty.ne_empty] at hKA
      · rw [Finset.coe_singleton, singleton_smul, sq] at hKA
        use x
    have hx' : x ⁻¹ • (A * A) ⊆ A := by rwa [← subset_smul_set_iff]
    have hx_inv : x⁻¹ ∈ A := by
      simpa using hx' (smul_mem_smul_set (mul_mem_mul hA.one_mem hA.one_mem))
    have hx_sq : x * x ∈ A := by
      rw [← hA.inv_eq_self]
      simpa using hx' (smul_mem_smul_set (mul_mem_mul hx_inv hA.one_mem))
    calc A * A ⊆ x • A := by assumption
      _ = x⁻¹ • (x * x) • A := by simp [smul_smul]
      _ ⊆ x⁻¹ • (A • A) := smul_set_mono (smul_set_subset_smul hx_sq)
      _ ⊆ A := hx'
  mpr := by rintro ⟨H, rfl⟩; exact .subgroup
