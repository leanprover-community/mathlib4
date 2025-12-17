/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.GroupTheory.Artin.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Braid groups

This file defines the braid groups as Artin groups of type A.

## Main definitions

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

@[expose] public section

noncomputable section

open Equiv Fin

/-! ### The braid group -/

/-- The braid group `B_n` on `n` strands. This is the Artin group of type A_{n-1}. -/
abbrev BraidGroup (n : ℕ) : Type := (CoxeterMatrix.Aₙ (n - 1)).ArtinGroup

namespace BraidGroup

variable {n : ℕ}

/-- The i-th standard Artin generator σ_i of the braid group B_n.
This corresponds to crossing strand i over strand i+1. -/
def σ (i : Fin (n - 1)) : BraidGroup n :=
  (CoxeterMatrix.Aₙ (n - 1)).artinGenerator i

/-! ### The surjection to the symmetric group -/

/-- The function sending generator i to the adjacent transposition (i, i+1). -/
def swapFun (n : ℕ) : Fin n → Perm (Fin (n + 1)) := fun i =>
  swap i.castSucc i.succ

/-- Adjacent transpositions satisfy the Artin relations (braid relations). -/
theorem swapFun_isArtinLiftable (n : ℕ) :
    (CoxeterMatrix.Aₙ n).IsArtinLiftable (swapFun n) := by
  intro i j
  by_cases hij : i = j
  · simp [hij]
  by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  · -- Adjacent case: m = 3, braid relation
    have hM : (CoxeterMatrix.Aₙ n).M i j = 3 := by
      simp only [CoxeterMatrix.Aₙ, Matrix.of_apply, hij, ↓reduceIte]
      grind
    rw [hM]
    simp only [CoxeterMatrix.alternatingProd, one_mul]
    -- Need: swapFun i * swapFun j * swapFun i = swapFun j * swapFun i * swapFun j
    simp only [swapFun]
    obtain hadj | hadj := hadj
    · -- i + 1 = j case: j.castSucc = i.succ
      have hj_cast : j.castSucc = i.succ := by grind
      grind [Equiv.swap_conjugate]
    · -- j + 1 = i case: i.castSucc = j.succ
      have hi_cast : i.castSucc = j.succ := by grind
      grind [Equiv.swap_conjugate]
  · -- Far case: m = 2, commutativity
    have hM : (CoxeterMatrix.Aₙ n).M i j = 2 := CoxeterMatrix.Aₙ_far _ i j hij
        (fun h => hadj (Or.inl h)) (fun h => hadj (Or.inr h))
    rw [hM]
    simp only [CoxeterMatrix.alternatingProd, one_mul]
    -- Need: swapFun j * swapFun i = swapFun i * swapFun j
    simp only [swapFun]
    push_neg at hadj
    apply Equiv.swap_mul_swap_comm_of_disjoint <;>
      simp only [ne_eq, Fin.ext_iff] <;> grind

/-- The canonical surjection from the braid group B_{n+1} to the symmetric group S_{n+1},
sending σ_i to the adjacent transposition (i, i+1). -/
def toPermHom (n : ℕ) : BraidGroup (n + 1) →* Perm (Fin (n + 1)) :=
  (CoxeterMatrix.Aₙ n).artinLift (swapFun n) (swapFun_isArtinLiftable n)

@[simp]
theorem toPermHom_σ (n : ℕ) (i : Fin n) :
    toPermHom n (σ i) = swapFun n i := by
  change ((CoxeterMatrix.Aₙ n).artinLift (swapFun n) (swapFun_isArtinLiftable n))
      ((CoxeterMatrix.Aₙ n).artinGenerator i) = swapFun n i
  rw [CoxeterMatrix.artinLift_artinGenerator]

/-- The surjection from B_{n+1} to S_{n+1} is surjective. -/
theorem toPermHom_surjective (n : ℕ) : Function.Surjective (toPermHom n) := by
  -- The image of toPermHom contains all adjacent transpositions, which generate Perm (Fin (n + 1))
  intro τ
  have hgen := Equiv.Perm.mclosure_swap_castSucc_succ n
  have hτ : τ ∈ (⊤ : Submonoid (Perm (Fin (n + 1)))) := Submonoid.mem_top _
  rw [← hgen] at hτ
  -- τ is in Submonoid.closure of {swap i.castSucc i.succ}
  induction hτ using Submonoid.closure_induction with
  | mem y hy =>
    -- Generator case: each swap i.castSucc i.succ is in the range
    obtain ⟨i, rfl⟩ := hy
    use σ i
    grind [toPermHom_σ, swapFun]
  | one =>
    -- Identity case
    use 1
    grind
  | mul a b _ _ ha hb =>
    -- Multiplication case
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x * y
    grind

/-! ### Small braid groups -/

/-- The braid group B_0 is trivial (no generators). -/
instance : Unique (BraidGroup 0) :=
  inferInstanceAs (Unique (CoxeterMatrix.Aₙ 0).ArtinGroup)

/-- The braid group B_1 is trivial (no generators). -/
instance : Unique (BraidGroup 1) :=
  inferInstanceAs (Unique (CoxeterMatrix.Aₙ 0).ArtinGroup)

/-- The Artin relations for `Aₙ 1` are all trivial.
When i = j, the relation is `of i * (of i)⁻¹ = 1`. -/
theorem artinRelationsSet_Aₙ_one_eq_one :
    (CoxeterMatrix.Aₙ 1).artinRelationsSet = {1} := by
  ext r
  simp only [CoxeterMatrix.artinRelationsSet, Set.mem_range, Prod.exists, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, j, rfl⟩
    -- i, j : Fin 1, so i = j = 0
    fin_cases i; fin_cases j
    -- artinRelation 0 0 with M 0 0 = 1
    simp only [CoxeterMatrix.artinRelation, CoxeterMatrix.diagonal,
      CoxeterMatrix.alternatingWord_one, CoxeterMatrix.freeGroupProd_singleton, mul_inv_cancel]
  · intro hr
    use 0, 0
    simp only [CoxeterMatrix.artinRelation, CoxeterMatrix.diagonal,
      CoxeterMatrix.alternatingWord_one, CoxeterMatrix.freeGroupProd_singleton, mul_inv_cancel, hr]

/-- The braid group B_2 is isomorphic to ℤ (one generator, no non-trivial relations).
The isomorphism sends the unique generator σ_0 to 1 ∈ ℤ. -/
def braidGroupTwoEquivInt : BraidGroup 2 ≃* Multiplicative ℤ := by
  -- BraidGroup 2 = (Aₙ 1).ArtinGroup = PresentedGroup (Aₙ 1).artinRelationsSet
  -- The relations are all trivial, so this equals FreeGroup (Fin 1) / ⊥ ≃ FreeGroup (Fin 1)
  -- First, show the quotient is by the trivial subgroup
  have h : Subgroup.normalClosure (CoxeterMatrix.Aₙ 1).artinRelationsSet = ⊥ := by
    rw [artinRelationsSet_Aₙ_one_eq_one, Subgroup.normalClosure_singleton_one]
  -- Chain: PresentedGroup rels ≃* FreeGroup (Fin 1) ⧸ ⊥ ≃*
  --        FreeGroup (Fin 1) ≃* FreeGroup Unit ≃* Multiplicative ℤ
  exact (QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientBot.trans
      ((FreeGroup.freeGroupCongr (Equiv.equivPUnit (Fin 1))).trans
        FreeGroup.freeGroupUnitEquivMulInt))

/-- The generator σ_0 of B_2 maps to 1 under the isomorphism with ℤ. -/
@[simp]
theorem braidGroupTwoEquivInt_σ :
    braidGroupTwoEquivInt (σ 0) = Multiplicative.ofAdd 1 := by
  simp only [braidGroupTwoEquivInt, MulEquiv.trans_apply, QuotientGroup.quotientBot_apply,
    FreeGroup.freeGroupCongr_apply, FreeGroup.freeGroupUnitEquivMulInt]
  rfl

end BraidGroup
