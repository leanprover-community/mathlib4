/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

/-!
# Congruence modulo natural and integer numbers for big operators

In this file we prove various versions of the following theorem:
if `f i ≡ g i [MOD n]` for all `i ∈ s`, then `∏ i ∈ s, f i ≡ ∏ i ∈ s, g i [MOD n]`,
and similarly for sums.

We prove it for lists, multisets, and finsets, as well as for natural and integer numbers.
-/

@[expose] public section

namespace Nat

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

namespace ModEq

theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) :
    (l.map f).prod ≡ (l.map g).prod [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)

theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [MOD n]) : (l.map f).prod ≡ 1 [MOD n] :=
  (listProd_map h).trans <| by simp [ModEq.refl]

theorem listProd_one {l : List ℕ} (h : ∀ x ∈ l, x ≡ 1 [MOD n]) : l.prod ≡ 1 [MOD n] := by
  simpa using listProd_map_one h

theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) : (l.map f).sum ≡ (l.map g).sum [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)

theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [MOD n]) : (l.map f).sum ≡ 0 [MOD n] := by
  simpa using listSum_map h

theorem listSum_zero {l : List ℕ} (h : ∀ x ∈ l, x ≡ 0 [MOD n]) : l.sum ≡ 0 [MOD n] := by
  simpa using listSum_map h

theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).prod ≡ (s.map g).prod [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) :
    (s.map f).prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map h

theorem multisetProd_one {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 1 [MOD n]) : s.prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map_one h

theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).sum ≡ (s.map g).sum [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) :
    (s.map f).sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h

theorem multisetSum_zero {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 0 [MOD n]) : s.sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h

@[gcongr]
protected theorem prod {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (∏ x ∈ s, f x) ≡ ∏ x ∈ s, g x [MOD n] :=
  .multisetProd_map (s := s.1) h

theorem prod_one {s : Finset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) : ∏ x ∈ s, f x ≡ 1 [MOD n] := by
  simpa using ModEq.prod h

@[gcongr]
protected theorem sum {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (∑ x ∈ s, f x) ≡ ∑ x ∈ s, g x [MOD n] :=
  .multisetSum_map (s := s.1) h

theorem sum_zero {s : Finset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) : ∑ x ∈ s, f x ≡ 0 [MOD n] := by
  simpa using ModEq.sum h

end ModEq

theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [MOD n]) :
    (∏ x ∈ s, f x) ≡ if a ∈ s then f a else 1 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod, apply_ite Nat.cast] at *
  exact Finset.prod_eq_ite _ hf

theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 1 [MOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [MOD n]) :
    (∏ x ∈ s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [MOD n]) :
    (∑ x ∈ s, f x) ≡ if a ∈ s then f a else 0 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum, apply_ite Nat.cast] at *
  exact Finset.sum_eq_ite _ hf

theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 0 [MOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [MOD n]) :
    (∑ x ∈ s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

end Nat

namespace Int

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

namespace ModEq

theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [ZMOD n]) :
    (l.map f).prod ≡ (l.map g).prod [ZMOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)

theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [ZMOD n]) : (l.map f).prod ≡ 1 [ZMOD n] :=
  (listProd_map h).trans <| by simp

theorem listProd_one {l : List ℤ} (h : ∀ x ∈ l, x ≡ 1 [ZMOD n]) : l.prod ≡ 1 [ZMOD n] := by
  simpa using listProd_map_one h

theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [ZMOD n]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)

theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [ZMOD n]) : (l.map f).sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map h

theorem listSum_zero {l : List ℤ} (h : ∀ x ∈ l, x ≡ 0 [ZMOD n]) : l.sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map_zero h

theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (s.map f).prod ≡ (s.map g).prod [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [ZMOD n]) :
    (s.map f).prod ≡ 1 [ZMOD n] := by
  simpa using multisetProd_map h

theorem multisetProd_one {s : Multiset ℤ} (h : ∀ x ∈ s, x ≡ 1 [ZMOD n]) : s.prod ≡ 1 [ZMOD n] := by
  simpa using multisetProd_map_one h

theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (s.map f).sum ≡ (s.map g).sum [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [ZMOD n]) :
    (s.map f).sum ≡ 0 [ZMOD n] := by
  simpa using multisetSum_map h

theorem multisetSum_zero {s : Multiset ℤ} (h : ∀ x ∈ s, x ≡ 0 [ZMOD n]) : s.sum ≡ 0 [ZMOD n] := by
  simpa using multisetSum_map_zero h

@[gcongr]
protected theorem prod {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ ∏ x ∈ s, g x [ZMOD n] :=
  .multisetProd_map (s := s.1) h

theorem prod_one {s : Finset α} (h : ∀ x ∈ s, f x ≡ 1 [ZMOD n]) : ∏ x ∈ s, f x ≡ 1 [ZMOD n] := by
  simpa using ModEq.prod h

@[gcongr]
protected theorem sum {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ ∑ x ∈ s, g x [ZMOD n] :=
  .multisetSum_map (s := s.1) h

protected theorem sum_zero {s : Finset α} (h : ∀ x ∈ s, f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ 0 [ZMOD n] :=
  .multisetSum_map_zero (s := s.1) h

end ModEq

theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ if a ∈ s then f a else 1 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod,
    apply_ite Int.cast] at *
  exact Finset.prod_eq_ite _ hf

theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 1 [ZMOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ if a ∈ s then f a else 0 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum,
    apply_ite Int.cast] at *
  exact Finset.sum_eq_ite _ hf

theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 0 [ZMOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

end Int
