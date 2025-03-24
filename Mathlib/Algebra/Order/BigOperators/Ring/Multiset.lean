/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.Nonneg.Ring

import Mathlib.Algebra.BigOperators.Expect

/-!
# Big operators on a multiset in ordered rings

This file contains the results concerning the interaction of multiset big operators with ordered
rings.
-/

open Multiset

@[simp]
lemma CanonicallyOrderedAdd.multiset_prod_pos {R : Type*}
    [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R] [Nontrivial R]
    {m : Multiset R} : 0 < m.prod ↔ ∀ x ∈ m, 0 < x := by
  rcases m with ⟨l⟩
  rw [Multiset.quot_mk_to_coe'', Multiset.prod_coe]
  exact CanonicallyOrderedAdd.list_prod_pos

section OrderedCommSemiring

variable {α β : Type*} [CommMonoid α] [OrderedCommSemiring β]

theorem map_multiset_prod_le_of_submultiplicative_of_nonneg {f : α → β} (h0 : ∀ a, 0 ≤ f a)
    (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) :
    f s.prod ≤ (s.map f).prod := by
  set g : α → {b : β // 0 ≤ b} := fun x : α ↦ ⟨f x, h0 _⟩
  have hg_le : g s.prod ≤ (s.map g).prod := by
    apply Multiset.le_prod_of_submultiplicative
    · ext
      simp [g, Nonneg.coe_one, h_one]
    · intro a b
      rw [← Subtype.coe_le_coe, Nonneg.mk_mul_mk]
      exact h_mul _ _
  rw [← Subtype.coe_le_coe] at hg_le
  convert hg_le
  apply Multiset.induction_on s (p := fun s ↦ (Multiset.map f s).prod = ↑(Multiset.map g s).prod)
  · simp [Multiset.map_zero, prod_zero, Nonneg.coe_one, g]
  · intro a s hs
    simp only [map_cons, prod_cons, Nonneg.coe_mul, g, hs]

theorem Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg (f : α → β) (p : α → Prop)
    (h0 : ∀ a, 0 ≤ f a) (h_one : f 1 = 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  revert s
  refine Multiset.induction (by simp [le_of_eq h_one]) ?_
  intro a s hs hpsa
  have hps : ∀ x, x ∈ s → p x := fun x hx ↦ hpsa x (mem_cons_of_mem hx)
  have hp_prod : p s.prod := prod_induction p s hp_mul hp_one hps
  rw [prod_cons, map_cons, prod_cons]
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans
    (mul_le_mul_of_nonneg_left (hs hps) (h0 _))

theorem Multiset.le_prod_of_submultiplicative_of_nonneg (f : α → β) (h0 : ∀ a, 0 ≤ f a)
    (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) :
    f s.prod ≤ (s.map f).prod :=
  le_prod_of_submultiplicative_on_pred_of_nonneg f (fun _ ↦ True) h0 h_one trivial
    (fun x y _ _ ↦ h_mul x y) (by simp) s (by simp)

end OrderedCommSemiring
