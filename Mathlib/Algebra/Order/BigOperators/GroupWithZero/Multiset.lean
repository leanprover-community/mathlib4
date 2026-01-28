/-
Copyright (c) 2021 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Big operators on a multiset in ordered groups with zeros

This file contains the results concerning the interaction of multiset big operators with ordered
groups with zeros.
-/

public section

namespace Multiset

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

lemma prod_nonneg {s : Multiset R} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_nonneg h

lemma one_le_prod {s : Multiset R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.one_le_prod h

theorem prod_map_le_prod_map₀ {ι : Type*} {s : Multiset ι} (f : ι → R) (g : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe] at *
  apply List.prod_map_le_prod_map₀ f g h0 h

theorem prod_map_le_pow_card₀ {ι : Type*} {f : ι → R} {r : R} {t : Multiset ι}
    (hf0 : ∀ x ∈ t, 0 ≤ f x) (hf : ∀ x ∈ t, f x ≤ r) :
    (map f t).prod ≤ r ^ card t := by
  convert prod_map_le_prod_map₀ f (Function.const ι r) hf0 hf
  simp

@[deprecated (since := "2026-01-18")] alias prod_map_le_pow_card := prod_map_le_pow_card₀

lemma prod_le_pow_card₀ (s : Multiset R) (n : R) (hf0 : ∀ (x : R), x ∈ s → 0 ≤ x)
    (hf : ∀ (x : R), x ∈ s → x ≤ n) :
    s.prod ≤ n ^ s.card := by
  convert prod_map_le_pow_card₀ (f := @id R) hf0 hf
  simp

omit [PosMulMono R]
variable [PosMulStrictMono R] [NeZero (1 : R)]

lemma prod_pos {s : Multiset R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, prod_coe] at *
  apply List.prod_pos h

theorem prod_map_lt_prod_map {ι : Type*} {s : Multiset ι} (hs : s ≠ 0)
    (f : ι → R) (g : ι → R) (h0 : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i < g i) :
    (map f s).prod < (map g s).prod := by
  cases s using Quotient.ind
  simp only [quot_mk_to_coe, mem_coe, map_coe, prod_coe, ne_eq, coe_eq_zero] at *
  apply List.prod_map_lt_prod_map hs f g h0 h

end Multiset
