/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Order.Interval.Finset.Nat

/-!
# Restriction of a function indexed by natural integers

Given a dependent function `f : (n : ℕ) → α n` and `n : ℕ`, one might want to consider
the restriction of `f` to integers ` ≤ n`.
This is defined in this file as `Nat.restrict n f`.
Similarly, if we have `m n : ℕ`, `hmn : m ≤ n` and `f : (i : ↑(Set.Iic n)) → α ↑i`,
one might want to restrict it to integers ` ≤ m`.
This is defined in this file as `Nat.restrict₂ hmn f`.

We also provide versions where the intervals are seen as finite sets, see `Nat.frestrict``
and `Nat.frestrict₂`.

## Main definitions
* `Nat.restrict n f`: Restricts the function `f` to the variables indexed by integers `≤ n`.
-/

namespace Nat

variable {α : ℕ → Type*}

section Set

open Set

/-- Restrict domain of a function `f` indexed by `ℕ` to integers `≤ n`. -/
def restrict (n : ℕ) := (Iic n).restrict (π := α)

@[simp]
lemma restrict_def (n : ℕ) (f : (n : ℕ) → α n) (i : Iic n) : n.restrict f i = f i := rfl

/-- If a function `f` indexed by `ℕ` is restricted to integers `≤ n`, and `m ≤ n`,
this is the restriction to integers `≤ m`. -/
def restrict₂ {m n : ℕ} (hmn : m ≤ n) := Set.restrict₂ (π := α) (Iic_subset_Iic.2 hmn)

@[simp]
lemma restrict₂_def {m n : ℕ} (hmn : m ≤ n) (f : (i : Iic n) → α i) (i : Iic m) :
    restrict₂ hmn f i = f ⟨i.1, Iic_subset_Iic.2 hmn i.2⟩ := rfl

theorem restrict₂_comp_restrict {m n : ℕ} (hmn : m ≤ n) :
    (restrict₂ (α := α) hmn) ∘ n.restrict = m.restrict := rfl

theorem restrict₂_comp_restrict₂ {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (restrict₂ (α := α) hmn) ∘ (restrict₂ hnk) = restrict₂ (hmn.trans hnk) := rfl

end Set

section Finset

open Finset

/-- Restrict domain of a function `f` indexed by `ℕ` to integers `≤ n`, seen as a finite set. -/
def frestrict (n : ℕ) := (Iic n).restrict (β := α)

@[simp]
lemma frestrict_def (n : ℕ) (f : (n : ℕ) → α n) (i : Iic n) : n.frestrict f i = f i := rfl

/-- If a function `f` indexed by `ℕ` is restricted to integers `≤ n`, and `m ≤ n`,
this is the restriction to integers `≤ m`. Interval are seen as finite sets. -/
def frestrict₂ {m n : ℕ} (hmn : m ≤ n) := Finset.restrict₂ (β := α) (Iic_subset_Iic.2 hmn)

@[simp]
lemma frestrict₂_def {m n : ℕ} (hmn : m ≤ n) (f : (i : Iic n) → α i) (i : Iic m) :
    frestrict₂ hmn f i = f ⟨i.1, Iic_subset_Iic.2 hmn i.2⟩ := rfl

theorem frestrict₂_comp_frestrict {m n : ℕ} (hmn : m ≤ n) :
    (frestrict₂ (α := α) hmn) ∘ n.frestrict = m.frestrict := rfl

theorem frestrict₂_comp_frestrict₂ {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    (frestrict₂ (α := α) hmn) ∘ (frestrict₂ hnk) = frestrict₂ (hmn.trans hnk) := rfl

end Finset

end Nat
