/-
Copyright (c) 2026 Mingkai Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingkai Su
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic.Linarith

public section

open Set

/-- A scalar map `f : α → ℝ` is odd (anti-invariant) with respect to `τ`
if `f (τ x) = -f x`. -/
def IsOddMap {α : Type*} (τ : α → α) (f : α → ℝ) : Prop :=
  ∀ x, f (τ x) = -f x

namespace IsOddMap

variable {α : Type*} {τ : α → α} {f : α → ℝ}

/-- On any space equipped with a domain involution `τ`, an odd scalar map
cannot be strictly positive everywhere. -/
theorem not_forall_pos [Nonempty α] (h_odd : IsOddMap τ f) :
    ¬(∀ x, 0 < f x) := fun h_pos => by
  obtain ⟨x⟩ := ‹Nonempty α›
  linarith [h_pos x, h_pos (τ x), h_odd x]

/-- An odd scalar map cannot be strictly negative everywhere. -/
theorem not_forall_neg [Nonempty α] (h_odd : IsOddMap τ f) :
    ¬(∀ x, f x < 0) := fun h_neg => by
  obtain ⟨x⟩ := ‹Nonempty α›
  linarith [h_neg x, h_neg (τ x), h_odd x]

/-- Let `γ : [a, b] → α` be any continuous path connecting a point `γ a` to its
antipodal image `γ b = τ (γ a)`. Then any odd map `f` continuous along the path
must possess a zero `γ t` where `f (γ t) = 0`. -/
theorem exists_zero_of_antipodal_path (h_odd : IsOddMap τ f) {a b : ℝ} (hab : a ≤ b)
    (γ : ℝ → α) (h_cont : ContinuousOn (f ∘ γ) (Icc a b))
    (h_endpoints : γ b = τ (γ a)) :
    ∃ t ∈ Icc a b, f (γ t) = 0 := by
  have h_flip : (f ∘ γ) b = -(f ∘ γ) a := by
    dsimp; rw [h_endpoints, h_odd]
  rcases le_total 0 ((f ∘ γ) a) with h | h
  · exact intermediate_value_Icc' hab h_cont ⟨by linarith, h⟩
  · exact intermediate_value_Icc hab h_cont ⟨h, by linarith⟩

end IsOddMap

end
