/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Une introduction à Lean : existence de points périodiques

Je vais illustrer l'assistant de preuves Lean par la première preuve de systèmes dynamiques :
soi `f : X → X` est une fonction sur un ensemble fini, alors il existe un point périodique
pour `f`.
-/

open Function

/-- Premier essai, pas vrai -/
lemma pas_vrai (X : Type*) (f : X → X) [Finite X] : ∃ (x : X) (n : ℕ), f^[n] x = x := sorry

lemma vrai_mais_trivial (X : Type*) (f : X → X) [Finite X] [h : Nonempty X] :
    ∃ (x : X), ∃ (n : ℕ), f^[n] x = x := by
  obtain ⟨x₀⟩ := h
  use x₀, 0
  simp

#lint

lemma vrai_et_moins_trivial (X : Type*) (f : X → X) [Finite X] [h : Nonempty X] :
    ∃ (x : X), ∃ (n : ℕ), 0 < n ∧ f^[n] x = x := by
  obtain ⟨x₀⟩ := h
  have : ¬ (Injective (fun n ↦ f^[n] x₀)) := by
    exact not_injective_infinite_finite (fun n ↦ f^[n] x₀)
  have : ∃ k l, k ≠ l ∧ f^[k] x₀ = f^[l] x₀ := by
    exact Finite.exists_ne_map_eq_of_infinite (fun n ↦ f^[n] x₀)
  obtain ⟨k, l, hkl : k ≠ l, h : f^[k] x₀ = f^[l] x₀⟩ := this
  have : (k < l) ∨ (l < k) := Nat.lt_or_lt_of_ne hkl
  rcases this with hkl | hlk
  · use f^[k] x₀, l - k
    constructor
    · omega
    · have H : l - k + k = l := by omega
      rw [← iterate_add_apply]
      rw [H]
      rw [h]
  · exact ⟨f^[l] x₀, k - l, by omega, by rw [← iterate_add_apply, Nat.sub_add_cancel hlk.le, h]⟩

#lint
