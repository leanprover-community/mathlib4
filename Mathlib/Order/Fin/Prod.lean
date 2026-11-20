/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Prod.Lex.Basic

import Mathlib.Algebra.Order.Group.Nat

/-!
# Properties of the order on a binary product of `Fin` types

## Main definitions

* `finProdFinOrderIso`: `finProdFinEquiv` as an order isomorphism
  `Fin m ×ₗ Fin n ≃o Fin (m * n)` for the lexicographic order.
* `natProdFinOrderIso`: `natProdFinEquiv` as an order isomorphism `ℕ ×ₗ Fin n ≃o ℕ`
  for the lexicographic order.
-/

namespace Fin

variable {p q : ℕ}

public lemma prod_zero_zero_lt_iff (i : Fin (p + 1) × Fin (q + 1)) :
    (0, 0) < i ↔ 0 < i.1.val + i.2.val := by
  rw [Prod.lt_iff]
  grind

public lemma prod_lt_last_last_iff (i : Fin (p + 1) × Fin (q + 1)) :
    i < (Fin.last _, Fin.last _) ↔ i.1.val + i.2.val < p + q := by
  simp only [Prod.lt_iff, Fin.lt_def]
  grind

public lemma prod_exists_lt_lt_of_le_of_le
    (k₀ k₂ : Fin p × Fin q) (h₀₂ : k₀ ≤ k₂)
    (h : k₀.1.val + k₀.2.val + 2 ≤ k₂.1.val + k₂.2.val) :
    ∃ k₁, k₀ < k₁ ∧ k₁ < k₂ := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := p) (by grind)
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := q) (by grind)
  obtain ⟨x₀, y₀⟩ := k₀
  obtain ⟨x₂, y₂⟩ := k₂
  simp only [Prod.le_def] at h₀₂ h
  obtain ⟨hx, hy⟩ := h₀₂
  obtain hx' | rfl := hx.lt_or_eq
  · obtain hy' | rfl := hy.lt_or_eq
    · exact ⟨⟨x₀, y₂⟩, by aesop⟩
    · obtain ⟨x₂', rfl⟩ := x₂.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hx')
      refine ⟨⟨x₂'.castSucc, y₀⟩, ?_⟩
      rw [Fin.val_succ] at h
      simp [Fin.lt_def]
      grind
  · obtain ⟨y₂', rfl⟩ := y₂.eq_succ_of_ne_zero (by grind)
    refine ⟨⟨x₀, y₂'.castSucc⟩, ?_⟩
    rw [Fin.val_succ] at h
    simp [Fin.lt_def]
    lia

end Fin

/-- `finProdFinEquiv` as an order isomorphism, for the lexicographic order on
`Fin m × Fin n`. -/
@[expose, simps! apply]
public def finProdFinOrderIso {m n : ℕ} : Fin m ×ₗ Fin n ≃o Fin (m * n) where
  toEquiv := ofLex.trans finProdFinEquiv
  map_rel_iff' := Fin.mkDivMod_le_mkDivMod_iff.trans Prod.Lex.toLex_le_toLex.symm

@[simp]
public lemma finProdFinOrderIso_symm_apply {m n : ℕ} (k : Fin (m * n)) :
    finProdFinOrderIso.symm k = toLex (k.divNat, k.modNat) := rfl

/-- `natProdFinEquiv` as an order isomorphism, for the lexicographic order on `ℕ × Fin n`. -/
@[expose, simps! apply]
public def natProdFinOrderIso (n : ℕ) [NeZero n] : ℕ ×ₗ Fin n ≃o ℕ where
  toEquiv := ofLex.trans (natProdFinEquiv n)
  map_rel_iff' := Nat.mkDivMod_le_mkDivMod_iff.trans Prod.Lex.toLex_le_toLex.symm

@[simp]
public lemma natProdFinOrderIso_symm_apply (n : ℕ) [NeZero n] (k : ℕ) :
    (natProdFinOrderIso n).symm k = toLex (k / n, Fin.ofNat n k) := rfl
