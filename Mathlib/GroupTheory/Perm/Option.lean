/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Fintype.Option
import Mathlib.GroupTheory.Perm.Sign

/-!
# Permutations of `Option α`
-/


open Equiv

@[simp]
theorem Equiv.optionCongr_one {α : Type*} : (1 : Perm α).optionCongr = 1 :=
  Equiv.optionCongr_refl

@[simp]
theorem Equiv.optionCongr_swap {α : Type*} [DecidableEq α] (x y : α) :
    optionCongr (swap x y) = swap (some x) (some y) := by
  ext (_ | i)
  · simp [swap_apply_of_ne_of_ne]
  · by_cases hx : i = x
    · simp only [hx, optionCongr_apply, Option.map_some, swap_apply_left, Option.mem_def,
             Option.some.injEq]
    by_cases hy : i = y <;> simp [hx, hy, swap_apply_of_ne_of_ne]

@[simp]
theorem Equiv.optionCongr_sign {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α) :
    Perm.sign e.optionCongr = Perm.sign e := by
  induction e using Perm.swap_induction_on with
  | one => simp [Perm.one_def]
  | swap_mul f x y hne h =>
    simp [h, hne, Perm.mul_def]

@[simp]
theorem map_equiv_removeNone {α : Type*} [DecidableEq α] (σ : Perm (Option α)) :
    (removeNone σ).optionCongr = swap none (σ none) * σ := by
  ext1 x
  have : Option.map (⇑(removeNone σ)) x = (swap none (σ none)) (σ x) := by
    obtain - | x := x
    · simp
    · cases h : σ (some _)
      · simp [removeNone_none _ h]
      · have hn : σ (some x) ≠ none := by simp [h]
        have hσn : σ (some x) ≠ σ none := σ.injective.ne (by simp)
        simp [removeNone_some _ ⟨_, h⟩, ← h, swap_apply_of_ne_of_ne hn hσn]
  simpa using this

/-- Permutations of `Option α` are equivalent to fixing an
`Option α` and permuting the remaining with a `Perm α`.
The fixed `Option α` is swapped with `none`. -/
@[simps]
def Equiv.Perm.decomposeOption {α : Type*} [DecidableEq α] :
    Perm (Option α) ≃ Option α × Perm α where
  toFun σ := (σ none, removeNone σ)
  invFun i := swap none i.1 * i.2.optionCongr
  left_inv σ := by simp
  right_inv := fun ⟨x, σ⟩ => by
    have : removeNone (swap none x * σ.optionCongr) = σ :=
      Equiv.optionCongr_injective (by simp [← mul_assoc])
    simp [← Perm.eq_inv_iff_eq, this]

theorem Equiv.Perm.decomposeOption_symm_of_none_apply {α : Type*} [DecidableEq α] (e : Perm α)
    (i : Option α) : Equiv.Perm.decomposeOption.symm (none, e) i = i.map e := by simp

theorem Equiv.Perm.decomposeOption_symm_sign {α : Type*} [DecidableEq α] [Fintype α] (e : Perm α) :
    Perm.sign (Equiv.Perm.decomposeOption.symm (none, e)) = Perm.sign e := by simp

/-- The set of all permutations of `Option α` can be constructed by augmenting the set of
permutations of `α` by each element of `Option α` in turn. -/
theorem Finset.univ_perm_option {α : Type*} [DecidableEq α] [Fintype α] :
    @Finset.univ (Perm <| Option α) _ =
      (Finset.univ : Finset <| Option α × Perm α).map Equiv.Perm.decomposeOption.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm
