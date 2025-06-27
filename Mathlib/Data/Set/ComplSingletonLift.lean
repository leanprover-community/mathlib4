/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Data.Set.Basic

/-!
# Extending a function from the complement of a singleton

In this file, we define `Function.complSingletonLift` which allows to
extend a (dependant) function defined on the complement of a singleton.

-/


namespace Set

/-- The bijection `Unit ⊕ (({i₀})ᶜ : Set ι) ≃ ι` for any `i₀ : ι` -/
noncomputable def sumSingletonComplEquiv {ι : Type*} (i₀ : ι) :
    Unit ⊕ (({i₀})ᶜ : Set ι) ≃ ι :=
  .ofBijective
    (fun x ↦ match x with
      | .inl _ => i₀
      | .inr ⟨i, _⟩ => i) (by
  constructor
  · rintro (_ | ⟨_, hx⟩) (_ | ⟨_, hy⟩)
    · simp
    · simpa using Ne.symm hy
    · simpa
    · simp [Subtype.ext_iff_val]
  · intro i
    by_cases h : i = i₀
    · exact ⟨.inl Unit.unit, h.symm⟩
    · exact ⟨.inr ⟨i, by simpa using h⟩, rfl⟩)

@[simp]
lemma sumSingletonComplEquiv_inl {ι : Type*} (i₀ : ι) (u : Unit):
    sumSingletonComplEquiv i₀ (.inl u) = i₀ := rfl

@[simp]
lemma sumSingletonComplEquiv_inr {ι : Type*} (i₀ : ι) (i : ({i₀}ᶜ : Set ι)) :
    sumSingletonComplEquiv i₀ (.inr i) = i := rfl

end Set

namespace Function

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} (i₀ : ι)
  (f : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) (x : M i₀)

/-- Given `i₀ : ι` and `x : M i₀`, this is (dependent) map `(i : ι) → M i`
whose value at `i₀` is `x` and which extends a given map on the complement of `{i₀}`. -/
def complSingletonLift (i : ι) : M i :=
  if h : i = i₀ then by rw [h]; exact x else f ⟨i, h⟩

@[simp]
lemma complSingletonLift_self : complSingletonLift i₀ f x i₀ = x := dif_pos rfl

lemma complSingletonLift_of_neq (i : ι) (h : i ≠ i₀) :
    complSingletonLift i₀ f x i = f ⟨i, h⟩ := dif_neg h

@[simp]
lemma complSingletonLift_restriction (φ : ∀ i, M i) (i₀ : ι) :
    complSingletonLift i₀ (fun i ↦ φ i) (φ i₀) = φ := by
  ext i
  by_cases h : i = i₀
  · subst h
    simp
  · rw [complSingletonLift_of_neq _ _ _ _ h]

end Function
