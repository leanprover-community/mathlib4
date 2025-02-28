/-
Copyright (c) 2025 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta, Eric Wieser
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Antidiag.Prod

/-! # Antidiagonal variations

## Main Definitions
* `antidiagonalTwoTwo n` is the finset of all `x : Finset ((A × A) × (A × A))` such that
  `x.1.1 + x.1.2 + x.2.1 + x.2.2 = n`.


TODO: add analogous definitions for other partitions of `n`.

-/

namespace Finset

variable {A : Type*} [AddMonoid A] [HasAntidiagonal A]

section TwoTwo

/-- `antidiagonalTwoTwo n` is the finset of all `x : Finset ((A × A) × (A × A))` such that
  `x.1.1 + x.1.2 + x.2.1 + x.2.2 = n`. -/
def antidiagonalTwoTwo (n : A) : Finset ((A × A) × (A × A)) :=
  (antidiagonal n).disjiUnion (fun k ↦ (antidiagonal k.1) ×ˢ (antidiagonal k.2))
  (fun k _ l _ hkl ↦ by
    simp_rw [disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [mem_product, mem_antidiagonal] at hx hy
    apply hkl
    ext
    · simp only [← hx.1, ← hy.1, hxy]
    · simp only [← hx.2, ← hy.2, hxy])

theorem mem_antidiagonalTwoTwo {n : A} {x : (A × A) × (A × A)} :
    x ∈ antidiagonalTwoTwo n ↔ x.1.1 + x.1.2 + x.2.1 + x.2.2 = n := by
  simp only [antidiagonalTwoTwo, mem_disjiUnion, mem_antidiagonal, mem_product]
  exact ⟨fun ⟨u, hu, hx⟩ ↦ by rw [add_assoc, hx.2, hx.1, hu], fun hx ↦
    ⟨(x.1.1 + x.1.2, x.2.1 + x.2.2), by simp only [← add_assoc, hx],
     Prod.mk.inj_iff.mp rfl⟩⟩

theorem sum_antidiagonalTwoTwo_eq {B : Type*} [AddCommMonoid B] (f : (A × A) × (A × A) → B)
    (n : A) : ∑ x ∈ antidiagonalTwoTwo n, f x =
      ∑ m ∈ antidiagonal n, ∑ x ∈ antidiagonal m.1, ∑ y ∈ antidiagonal m.2, f (x, y) := by
  simp_rw [antidiagonalTwoTwo, sum_disjiUnion, Finset.sum_product]

end TwoTwo

end Finset
