/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# API for localized modules away from an element

We provide some specialized API for the localization of a module away from an element.
-/

public section

namespace IsLocalizedModule.Away

variable {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] {f : M →ₗ[R] N} {r : R}

lemma mk (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : ∀ (x : N), ∃ (n : ℕ) (y : M), r ^ n • x = f y)
    (h₃ : ∀ (x y : M), f x = f y → ∃ (n : ℕ), r ^ n • x = r ^ n • y) :
    IsLocalizedModule.Away r f where
  map_units := fun ⟨_, ⟨n, rfl⟩⟩ ↦ by simp [h₁.pow]
  surj x := by
    obtain ⟨n, y, hy⟩ := h₂ x
    use ⟨y, ⟨_, n, rfl⟩⟩, hy
  exists_of_eq {x y} hxy := by
    obtain ⟨n, hn⟩ := h₃ _ _ hxy
    use ⟨_, n, rfl⟩, hn

lemma mk_of_addCommGroup {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {f : M →ₗ[R] N} {r : R} (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : ∀ (x : N), ∃ (n : ℕ) (y : M), r ^ n • x = f y)
    (h₃ : ∀ (x : M), f x = 0 → ∃ (n : ℕ), r ^ n • x = 0) :
    IsLocalizedModule.Away r f := by
  refine IsLocalizedModule.Away.mk h₁ h₂ fun x y hxy ↦ ?_
  have : f (x - y) = 0 := by simp [hxy]
  obtain ⟨n, hn⟩ := h₃ _ this
  use n
  simpa [smul_sub, sub_eq_zero] using hn

variable (r) [IsLocalizedModule.Away r f]

variable (f) in
include f in
lemma isUnit_algebraMap : IsUnit (algebraMap R (Module.End R N) r) :=
  IsLocalizedModule.map_units (S := .powers r) f ⟨_, 1, by simp⟩

lemma exists_of_eq {x y : M} (h : f x = f y) : ∃ (n : ℕ), r ^ n • x = r ^ n • y := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := .powers r) h
  use n, hn

variable (f) in
lemma surj (y : N) : ∃ (n : ℕ) (x : M), r ^ n • y = f x := by
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalizedModule.surj (S := .powers r) f y
  use n, x, h

lemma of_associated {r r' : R} (h : Associated r r') [IsLocalizedModule.Away r f] :
    IsLocalizedModule.Away r' f := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  refine .mk ?_ ?_ ?_
  · simp [IsUnit.mul, isUnit_algebraMap f r, u.isUnit.map _]
  · intro y
    obtain ⟨n, x, hx⟩ := surj f r y
    use n, (u ^ n) • x
    simp [mul_pow, ← hx, mul_smul, Units.smul_def]
  · intro x y hxy
    obtain ⟨n, hn⟩ := exists_of_eq r hxy
    use n
    simp [mul_pow, mul_smul, hn]

lemma iff_of_associated {r r' : R} (h : Associated r r') :
    IsLocalizedModule.Away r f ↔ IsLocalizedModule.Away r' f :=
  ⟨fun _ ↦ .of_associated h, fun _ ↦ .of_associated h.symm⟩

end IsLocalizedModule.Away
