/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.GroupTheory.Artin.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Braid groups

This file defines the braid groups as Artin groups of type A.

## Main definitions

* `CoxeterMatrix.typeA`: The Coxeter matrix of type A_n.
* `BraidGroup`: The braid group B_n on n strands.
* `BraidGroup.σ`: The standard Artin generators σ_i of the braid group.
* `BraidGroup.toPermHom`: The canonical surjection from B_n to S_n.

## Overview

The braid group `B_n` is the group with presentation:
* Generators: σ_1, ..., σ_{n-1}
* Relations:
  - σ_i σ_j = σ_j σ_i for |i - j| ≥ 2 (far commutativity)
  - σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1} (braid relation)

This is the Artin group associated to the Coxeter matrix of type A_{n-1}.

There is a canonical surjection from `B_n` to the symmetric group `S_n` sending σ_i to
the adjacent transposition (i, i+1).

## References

* [Artin, *Theorie der Zöpfe*](artin1925)
-/

noncomputable section

open Equiv Fin

namespace CoxeterMatrix

/-! ### The Coxeter matrix of type A -/

/-- The Coxeter matrix of type A_n. This is the matrix with:
- M i i = 1 (diagonal)
- M i j = 3 if |i - j| = 1 (adjacent indices)
- M i j = 2 if |i - j| ≥ 2 (far indices commute)

This gives rise to the braid group B_{n+1}. -/
def typeA (n : ℕ) : CoxeterMatrix (Fin n) where
  M i j :=
    if i = j then 1
    else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 3
    else 2
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, Ne.symm hij, ↓reduceIte]
      by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
      · have hadj' : (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j := hadj.symm
        simp [hadj, hadj']
      · have hadj' : ¬((j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j) := by
          push_neg at hadj ⊢; exact hadj.symm
        simp [hadj, hadj']
  diagonal i := by simp only [↓reduceIte]
  off_diagonal i j hij := by
    simp only [hij, ↓reduceIte]
    intro h
    split_ifs at h with h1
    · omega
    · omega

@[simp]
theorem typeA_M_diag (n : ℕ) (i : Fin n) : (typeA n).M i i = 1 := by simp [typeA]

theorem typeA_M_adjacent (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    (typeA n).M i ⟨i.val + 1, hi⟩ = 3 := by
  simp [typeA, Fin.ext_iff]

theorem typeA_M_far (n : ℕ) (i j : Fin n) (h1 : i ≠ j) (h2 : (i : ℕ) + 1 ≠ j)
    (h3 : (j : ℕ) + 1 ≠ i) : (typeA n).M i j = 2 := by
  simp only [typeA, h1, ↓reduceIte]
  split_ifs with h4
  · obtain h4 | h4 := h4 <;> omega
  · rfl

end CoxeterMatrix

/-! ### The braid group -/

/-- The braid group `B_n` on `n` strands. This is the Artin group of type A_{n-1}. -/
abbrev BraidGroup (n : ℕ) : Type _ := (CoxeterMatrix.typeA (n - 1)).ArtinGroup

namespace BraidGroup

variable {n : ℕ}

/-- The i-th standard Artin generator σ_i of the braid group B_n.
This corresponds to crossing strand i over strand i+1. -/
def σ (i : Fin (n - 1)) : BraidGroup n :=
  (CoxeterMatrix.typeA (n - 1)).artinGenerator i

/-! ### The surjection to the symmetric group -/

variable (n) in
/-- The function sending generator i to the adjacent transposition (i, i+1).
Note: We require `2 ≤ n` to ensure `Fin (n-1)` maps properly into `Fin n`. -/
def swapFun (hn : 2 ≤ n) : Fin (n - 1) → Perm (Fin n) := fun i =>
  have h1 : i.val < n := Nat.lt_of_lt_of_le i.isLt (by omega)
  have h2 : i.val + 1 < n := by omega
  swap ⟨i.val, h1⟩ ⟨i.val + 1, h2⟩

/-- Far transpositions commute: if the ranges {i, i+1} and {j, j+1} are disjoint,
then swap i (i+1) and swap j (j+1) commute. -/
theorem swap_comm_of_disjoint {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    swap a b * swap c d = swap c d * swap a b := by
  -- swap_apply_of_ne_of_ne {a b x} : x ≠ a → x ≠ b → swap a b x = x
  ext x
  simp only [Perm.mul_apply]
  by_cases hxa : x = a
  · subst hxa
    -- Goal: swap a b (swap c d a) = swap c d (swap a b a)
    -- LHS: swap a b a = b (by swap_apply_left), and swap c d a = a (since a ≠ c, a ≠ d)
    -- RHS: swap a b a = b, then swap c d b = b (since b ≠ c, b ≠ d)
    rw [swap_apply_of_ne_of_ne hac had, swap_apply_left, swap_apply_of_ne_of_ne hbc hbd]
  by_cases hxb : x = b
  · subst hxb
    -- swap a b (swap c d b) = swap c d (swap a b b)
    rw [swap_apply_of_ne_of_ne hbc hbd, swap_apply_right, swap_apply_of_ne_of_ne hac had]
  by_cases hxc : x = c
  · subst hxc
    -- After subst: goal is swap a b (swap x d x) = swap x d (swap a b x)
    -- Note: hac becomes a ≠ x, hbc becomes b ≠ x, hcd becomes x ≠ d
    rw [swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm,
        swap_apply_of_ne_of_ne had.symm hbd.symm, swap_apply_left]
  by_cases hxd : x = d
  · subst hxd
    -- After subst: goal is swap a b (swap c x x) = swap c x (swap a b x)
    -- Note: had becomes a ≠ x, hbd becomes b ≠ x, hcd becomes c ≠ x
    rw [swap_apply_right, swap_apply_of_ne_of_ne had.symm hbd.symm,
        swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_right]
  · -- Neither a, b, c, nor d: both swaps leave x unchanged
    simp only [swap_apply_of_ne_of_ne hxc hxd, swap_apply_of_ne_of_ne hxa hxb]

/-- The braid relation for adjacent transpositions:
swap a b * swap b c * swap a b = swap b c * swap a b * swap b c -/
theorem swap_braid {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    swap a b * swap b c * swap a b = swap b c * swap a b * swap b c := by
  -- Both sides equal swap a c
  -- swap_mul_swap_mul_swap hxy hxz : swap y z * swap x y * swap y z = swap z x
  have rhs : swap b c * swap a b * swap b c = swap a c := by
    -- Need y=b, z=c, x=a, so hxy = hab, hxz = hac, result = swap c a
    rw [Equiv.swap_mul_swap_mul_swap hab hac, swap_comm]
  have lhs : swap a b * swap b c * swap a b = swap a c := by
    calc swap a b * swap b c * swap a b
        = swap b a * swap c b * swap b a := by simp only [swap_comm]
      -- Need y=b, z=a, x=c, so hxy = hbc.symm, hxz = hac.symm, result = swap a c
      _ = swap a c := Equiv.swap_mul_swap_mul_swap hbc.symm hac.symm
  rw [lhs, rhs]

/-- Adjacent transpositions satisfy the Artin relations (braid relations). -/
theorem swapFun_isArtinLiftable (hn : 2 ≤ n) :
    (CoxeterMatrix.typeA (n - 1)).IsArtinLiftable (swapFun n hn) := by
  intro i j
  by_cases hij : i = j
  · simp [hij]
  by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  · -- Adjacent case: m = 3, braid relation
    have hM : (CoxeterMatrix.typeA (n - 1)).M i j = 3 := by
      simp only [CoxeterMatrix.typeA, hij, ↓reduceIte, hadj]
    rw [hM]
    simp only [CoxeterMatrix.alternatingProd, one_mul]
    -- Need: swapFun i * swapFun j * swapFun i = swapFun j * swapFun i * swapFun j
    simp only [swapFun]
    obtain hadj | hadj := hadj
    · -- i + 1 = j case
      -- Identify the three Fin n elements involved
      have hj_eq : (j : ℕ) = i.val + 1 := hadj.symm
      have hi_lt : i.val < n - 1 := i.isLt
      have hj_lt : j.val < n - 1 := j.isLt
      have hi1 : i.val < n := Nat.lt_of_lt_of_le hi_lt (by omega)
      have hi2 : i.val + 1 < n := by omega
      have hi3 : i.val + 2 < n := by omega
      -- The goal reduces to swap_braid with a=i, b=i+1, c=i+2
      have key := swap_braid (a := ⟨i.val, hi1⟩) (b := ⟨i.val + 1, hi2⟩)
          (c := ⟨i.val + 2, hi3⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
          (by simp [Fin.ext_iff])
      convert key using 2
      all_goals simp_all
    · -- j + 1 = i case
      have hi_eq : (i : ℕ) = j.val + 1 := hadj.symm
      have hi_lt : i.val < n - 1 := i.isLt
      have hj_lt : j.val < n - 1 := j.isLt
      have hj1 : j.val < n := Nat.lt_of_lt_of_le hj_lt (by omega)
      have hj2 : j.val + 1 < n := by omega
      have hj3 : j.val + 2 < n := by omega
      -- swap_braid gives: swap a b * swap b c * swap a b = swap b c * swap a b * swap b c
      -- We need the .symm because the goal has swapFun i first, but i = j+1 corresponds to b
      have key := swap_braid (a := ⟨j.val, hj1⟩) (b := ⟨j.val + 1, hj2⟩)
          (c := ⟨j.val + 2, hj3⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
          (by simp [Fin.ext_iff])
      convert key.symm using 2
      all_goals simp_all
  · -- Far case: m = 2, commutativity
    have hM : (CoxeterMatrix.typeA (n - 1)).M i j = 2 := CoxeterMatrix.typeA_M_far _ i j hij
        (fun h => hadj (Or.inl h)) (fun h => hadj (Or.inr h))
    rw [hM]
    simp only [CoxeterMatrix.alternatingProd, one_mul]
    -- Need: swapFun j * swapFun i = swapFun i * swapFun j
    simp only [swapFun]
    push_neg at hadj
    apply swap_comm_of_disjoint
    · simp only [ne_eq, Fin.ext_iff]; omega
    · simp only [ne_eq, Fin.ext_iff]; omega
    · simp only [ne_eq, Fin.ext_iff]
      intro h; exact hij (Fin.ext h.symm)
    · simp only [ne_eq, Fin.ext_iff]; omega
    · simp only [ne_eq, Fin.ext_iff]; omega
    · simp only [ne_eq, Fin.ext_iff]; omega

/-- The canonical surjection from the braid group B_n to the symmetric group S_n,
sending σ_i to the adjacent transposition (i, i+1). -/
def toPermHom (hn : 2 ≤ n) : BraidGroup n →* Perm (Fin n) :=
  (CoxeterMatrix.typeA (n - 1)).artinLift (swapFun n hn) (swapFun_isArtinLiftable hn)

@[simp]
theorem toPermHom_σ (hn : 2 ≤ n) (i : Fin (n - 1)) :
    toPermHom hn (σ i) = swapFun n hn i := by
  simp [toPermHom, σ]

/-- The surjection from B_n to S_n is surjective. -/
theorem toPermHom_surjective (hn : 2 ≤ n) : Function.Surjective (toPermHom hn) := by
  -- The image of toPermHom contains all adjacent transpositions, which generate Perm (Fin n)
  -- We use mclosure_swap_castSucc_succ which is stated for Perm (Fin (m + 1)),
  -- and transport via the equivalence Fin (n - 1 + 1) ≃ Fin n.
  intro τ
  have hn' : n - 1 + 1 = n := by omega
  have hgen := Equiv.Perm.mclosure_swap_castSucc_succ (n - 1)
  -- Create the type equivalence
  let e : Fin (n - 1 + 1) ≃ Fin n := finCongr hn'
  let E : Perm (Fin (n - 1 + 1)) ≃* Perm (Fin n) := e.permCongrHom
  -- τ corresponds to E.symm τ in Perm (Fin (n - 1 + 1))
  have hτ' : E.symm τ ∈ (⊤ : Submonoid (Perm (Fin (n - 1 + 1)))) := Submonoid.mem_top _
  rw [← hgen] at hτ'
  -- E.symm τ is in Submonoid.closure of {swap i.castSucc i.succ}
  -- Prove that all elements of the closure map into the range
  suffices h : ∀ x, x ∈ Submonoid.closure (Set.range fun i : Fin (n - 1) =>
      swap (castSucc i) (succ i)) → E x ∈ (toPermHom hn).range by
    simpa using h (E.symm τ) hτ'
  intro x hx
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    -- Generator case: each swap i.castSucc i.succ maps to swapFun n hn i
    obtain ⟨i, rfl⟩ := hy
    simp only [MonoidHom.mem_range]
    use σ i
    simp only [toPermHom_σ, swapFun]
    -- Both are the same swap, just with different Fin types
    -- swapFun creates swap ⟨i.val, _⟩ ⟨i.val + 1, _⟩ in Perm (Fin n)
    -- E (swap i.castSucc i.succ) conjugates swap by finCongr, which is identity on values
    ext j
    simp only [E, e, Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.swap_apply_def,
      finCongr_symm, finCongr_apply, Fin.val_castSucc, Fin.val_succ, Fin.ext_iff, Fin.val_cast]
    -- Now the conditions and values are in terms of i.val, i.val+1, and j.val
    split_ifs with h1 h2 <;> simp_all
  | one =>
    -- Identity case
    simp only [map_one, Subgroup.one_mem]
  | mul a b _ _ ha hb =>
    -- Multiplication case
    simp only [map_mul]
    exact Subgroup.mul_mem _ ha hb

/-! ### Small braid groups -/

/-- The braid group B_0 is trivial (no generators). -/
instance : Unique (BraidGroup 0) :=
  inferInstanceAs (Unique (CoxeterMatrix.typeA 0).ArtinGroup)

/-- The braid group B_1 is trivial (no generators). -/
instance : Unique (BraidGroup 1) :=
  inferInstanceAs (Unique (CoxeterMatrix.typeA 0).ArtinGroup)

/-- The Artin relations for `typeA 1` are all trivial.
When i = j, the relation is `of i * (of i)⁻¹ = 1`. -/
theorem artinRelationsSet_typeA_one_eq_one :
    (CoxeterMatrix.typeA 1).artinRelationsSet = {1} := by
  ext r
  simp only [CoxeterMatrix.artinRelationsSet, Set.mem_range, Prod.exists, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, j, rfl⟩
    -- i, j : Fin 1, so i = j = 0
    fin_cases i; fin_cases j
    -- artinRelation 0 0 with M 0 0 = 1
    simp only [CoxeterMatrix.artinRelation, CoxeterMatrix.typeA_M_diag,
      CoxeterMatrix.alternatingWord_one, CoxeterMatrix.freeGroupProd_singleton, mul_inv_cancel]
  · intro hr
    use 0, 0
    simp only [CoxeterMatrix.artinRelation, CoxeterMatrix.typeA_M_diag,
      CoxeterMatrix.alternatingWord_one, CoxeterMatrix.freeGroupProd_singleton, mul_inv_cancel, hr]

/-- The braid group B_2 is isomorphic to ℤ (one generator, no non-trivial relations).
The isomorphism sends the unique generator σ_0 to 1 ∈ ℤ. -/
def braidGroupTwoEquivInt : BraidGroup 2 ≃* Multiplicative ℤ := by
  -- BraidGroup 2 = (typeA 1).ArtinGroup = PresentedGroup (typeA 1).artinRelationsSet
  -- The relations are all trivial, so this equals FreeGroup (Fin 1) / ⊥ ≃ FreeGroup (Fin 1)
  -- First, show the quotient is by the trivial subgroup
  have h : Subgroup.normalClosure (CoxeterMatrix.typeA 1).artinRelationsSet = ⊥ := by
    rw [artinRelationsSet_typeA_one_eq_one, Subgroup.normalClosure_singleton_one]
  -- Chain: PresentedGroup rels ≃* FreeGroup (Fin 1) ⧸ ⊥ ≃*
  --        FreeGroup (Fin 1) ≃* FreeGroup Unit ≃* Multiplicative ℤ
  exact (QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientBot.trans
      ((FreeGroup.freeGroupCongr (Equiv.equivPUnit (Fin 1))).trans
        FreeGroup.freeGroupUnitEquivMulInt))

/-- The generator σ_0 of B_2 maps to 1 under the isomorphism with ℤ. -/
@[simp]
theorem braidGroupTwoEquivInt_σ :
    braidGroupTwoEquivInt (σ ⟨0, by omega⟩) = Multiplicative.ofAdd 1 := by
  simp only [braidGroupTwoEquivInt, MulEquiv.trans_apply, QuotientGroup.quotientBot_apply,
    FreeGroup.freeGroupCongr_apply, FreeGroup.freeGroupUnitEquivMulInt]
  rfl

end BraidGroup
