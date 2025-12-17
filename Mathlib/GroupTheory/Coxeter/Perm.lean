/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Type A Coxeter groups and permutations

This file constructs the canonical homomorphism from the type A Coxeter group to the
symmetric group.

## Main definitions

* `swapFun`: The function sending generator `i` to the adjacent transposition `swap i (i+1)`.
* `CoxeterMatrix.typeAₙToPermHom`: The surjective homomorphism from the type A Coxeter group
  to the symmetric group.

## Main results

* `swapFun_isLiftable`: Adjacent transpositions satisfy the Coxeter relations.
* `typeAₙToPermHom_surjective`: The homomorphism is surjective.

## Future work

Show this is an isomorphism.
-/

@[expose] public section

noncomputable section

open Equiv Fin

/-! ### Adjacent transpositions -/

/-- The function sending generator `i` to the adjacent transposition `swap i.castSucc i.succ`.
This maps the `i`-th simple reflection to the transposition swapping positions `i` and `i+1`. -/
def swapFun (n : ℕ) : Fin n → Perm (Fin (n + 1)) := fun i =>
  swap i.castSucc i.succ

attribute [local grind] swapFun

/-! ### Permutation lemmas -/

/-- For involutions satisfying the braid relation, the cube of their product is one. -/
theorem mul_pow_three_eq_one_of_braid {G : Type*} [Group G]
    {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hbraid : a * b * a = b * a * b) :
    (a * b) ^ 3 = 1 := by
  grind only [pow_succ, mul_assoc, pow_zero, one_mul]

/-- For commuting involutions, the square of their product is one. -/
theorem mul_pow_two_eq_one_of_comm {G : Type*} [Group G]
    {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hcomm : a * b = b * a) :
    (a * b) ^ 2 = 1 := by
  grind only [pow_succ, mul_assoc, pow_zero, one_mul]

/-! ### Coxeter relations for adjacent transpositions -/

/-- Adjacent transpositions satisfy the Coxeter relations. -/
theorem swapFun_isLiftable (n : ℕ) :
    (CoxeterMatrix.Aₙ n).IsLiftable (swapFun n) := by
  intro i j
  by_cases hij : i = j
  · -- Diagonal case: M i i = 1, need (swap * swap)^1 = 1
    grind [CoxeterMatrix.diagonal, pow_one]
  by_cases hadj : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
  · -- Adjacent case: M i j = 3, need (swap i * swap j)^3 = 1
    have hM : (CoxeterMatrix.Aₙ n).M i j = 3 := CoxeterMatrix.Aₙ_adjacent _ i j hadj
    rw [hM]
    apply mul_pow_three_eq_one_of_braid <;> grind [pow_two]
  · -- Far case: M i j = 2, need (swap i * swap j)^2 = 1
    have hM : (CoxeterMatrix.Aₙ n).M i j = 2 := CoxeterMatrix.Aₙ_far _ i j hij
        (by grind) (by grind)
    rw [hM]
    apply mul_pow_two_eq_one_of_comm <;> grind [pow_two]

/-! ### The homomorphism from the type A Coxeter group -/

namespace CoxeterMatrix

/-- The canonical homomorphism from the type A Coxeter group to the symmetric group,
sending the simple reflection `s_i` to the adjacent transposition `swap i (i+1)`. -/
def typeAₙToPermHom (n : ℕ) : (Aₙ n).Group →* Perm (Fin (n + 1)) :=
  (Aₙ n).toCoxeterSystem.lift ⟨swapFun n, swapFun_isLiftable n⟩

@[simp]
theorem typeAₙToPermHom_simple (n : ℕ) (i : Fin n) :
    typeAₙToPermHom n ((Aₙ n).simple i) = swapFun n i :=
  CoxeterSystem.lift_apply_simple _ _ i

/-- The homomorphism from the type A Coxeter group to the symmetric group is surjective. -/
theorem typeAₙToPermHom_surjective (n : ℕ) : Function.Surjective (typeAₙToPermHom n) := by
  intro τ
  have hgen := Equiv.Perm.mclosure_swap_castSucc_succ n
  have hτ : τ ∈ (⊤ : Submonoid (Perm (Fin (n + 1)))) := Submonoid.mem_top _
  rw [← hgen] at hτ
  induction hτ using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    use (Aₙ n).simple i
    simp [swapFun]
  | one =>
    use 1
    simp
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    use x * y
    simp [hx, hy]

end CoxeterMatrix
