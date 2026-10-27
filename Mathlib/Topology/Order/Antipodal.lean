/-
Copyright (c) 2026 Mingkai Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingkai Su
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.UniformSpace.Real

import Mathlib.Tactic.Linarith

/-!
# Zero-Crossing of Odd Maps on Antipodal Paths

This module formalizes zero-crossing existence for continuous odd maps under domain involutions
along connected paths.

## Main definitions
* `IsOddMap τ f`: Anti-invariance condition `f (τ x) = -f x`.

## Main statements
* `not_forall_pos_of_oddMap`: An odd map cannot be strictly positive everywhere.
* `not_forall_neg_of_oddMap`: An odd map cannot be strictly negative everywhere.
* `exists_zero_of_antipodal_path`: Any continuous odd map along a path connecting antipodal points
  `γ(b) = τ (γ(a))` has a zero `f (γ t*) = 0`.
-/

public section

open Set

/-- A scalar map `f : α → ℝ` is odd (anti-invariant) with respect to `τ`
if `f (τ x) = -f x`. -/
def IsOddMap {α : Type*} (τ : α → α) (f : α → ℝ) : Prop :=
  ∀ x, f (τ x) = -f x

/-- On any space equipped with a domain involution `τ`, an odd scalar map
cannot be strictly positive everywhere. -/
theorem not_forall_pos_of_oddMap {α : Type*} [Nonempty α]
    (τ : α → α) (f : α → ℝ) (h_odd : IsOddMap τ f) :
    ¬(∀ x, 0 < f x) := fun h_pos => by
  inhabit α
  nlinarith [h_pos default, h_pos (τ default), h_odd default]

/-- An odd scalar map cannot be strictly negative everywhere. -/
theorem not_forall_neg_of_oddMap {α : Type*} [Nonempty α]
    (τ : α → α) (f : α → ℝ) (h_odd : IsOddMap τ f) :
    ¬(∀ x, f x < 0) := fun h_neg => by
  inhabit α
  nlinarith [h_neg default, h_neg (τ default), h_odd default]

/-- Let `γ : [a, b] → α` be any continuous path connecting a point `γ(a)` to its
antipodal image `γ(b) = τ(γ(a))`. Then any odd map `f` continuous along the path
must possess a zero `γ(t*)` where `f(γ(t*)) = 0`. -/
theorem exists_zero_of_antipodal_path {α : Type*} (τ : α → α) (f : α → ℝ)
    (h_odd : IsOddMap τ f) {a b : ℝ} (hab : a ≤ b)
    (γ : ℝ → α)
    (h_cont : ContinuousOn (f ∘ γ) (Icc a b))
    (h_endpoints : γ b = τ (γ a)) :
    ∃ t ∈ Icc a b, f (γ t) = 0 := by
  let g := f ∘ γ
  have h_flip : g b = -g a := by dsimp [g]; rw [h_endpoints, h_odd]
  rcases le_total 0 (g a) with h_pos | h_neg
  · have h_mem : (0 : ℝ) ∈ Icc (g b) (g a) := ⟨by linarith, h_pos⟩
    rcases intermediate_value_Icc' hab h_cont h_mem with ⟨t, ht_icc, ht_eq⟩
    exact ⟨t, ht_icc, ht_eq⟩
  · have h_mem : (0 : ℝ) ∈ Icc (g a) (g b) := ⟨h_neg, by linarith⟩
    rcases intermediate_value_Icc hab h_cont h_mem with ⟨t, ht_icc, ht_eq⟩
    exact ⟨t, ht_icc, ht_eq⟩
