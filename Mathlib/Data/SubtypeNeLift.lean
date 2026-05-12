/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Logic.Equiv.Option

/-!
# Extending a function from the complement of a singleton

In this file, we define `Function.subtypeNeLift` which allows to
extend a (dependent) function defined on the complement of a singleton.

-/

@[expose] public section

variable {ι : Type*} [DecidableEq ι] (i₀ : ι)

namespace Function

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} (i₀ : ι)
  (f : ∀ (j : { i // i ≠ i₀ }), M j) (x : M i₀)

/-- Given `i₀ : ι` and `x : M i₀`, this is the (dependent) map `(i : ι) → M i`
whose value at `i₀` is `x` and which extends a given map on the complement of `{i₀}`. -/
def subtypeNeLift (i : ι) : M i :=
  if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]
lemma subtypeNeLift_self : subtypeNeLift i₀ f x i₀ = x := dif_pos rfl

lemma subtypeNeLift_of_neq (i : ι) (h : i ≠ i₀) :
    subtypeNeLift i₀ f x i = f ⟨i, h⟩ := dif_neg h

@[simp]
lemma subtypeNeLift_restriction (φ : ∀ i, M i) (i₀ : ι) :
    subtypeNeLift i₀ (fun i ↦ φ i) (φ i₀) = φ := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp
  · rw [subtypeNeLift_of_neq _ _ _ _ h]

end Function
