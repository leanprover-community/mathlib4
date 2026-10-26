/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Mapping divisibility across multiplication-preserving homomorphisms

## Tags

divisibility, divides
-/

public section

variable {E F M N : Type*} [Semigroup M] [Semigroup N] [FunLike F M N] [MulHomClass F M N]
  [EquivLike E M N] [MulEquivClass E M N] {a b : M}

@[gcongr] lemma map_dvd (f : F) : a ∣ b → f a ∣ f b | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f a c⟩
@[gcongr] lemma map_rightDvd (f : F) : a ∣ᵣ b → f a ∣ᵣ f b | ⟨c, h⟩ => ⟨f c, h.symm ▸ map_mul f c a⟩

@[simp]
lemma map_dvd_iff (e : E) : e a ∣ e b ↔ a ∣ b :=
  ⟨fun h ↦ by simpa using map_dvd (MulEquivClass.toMulEquiv e).symm h, map_dvd e⟩

@[simp]
lemma map_rightDvd_iff (e : E) : e a ∣ᵣ e b ↔ a ∣ᵣ b :=
  ⟨fun h ↦ by simpa using map_rightDvd (MulEquivClass.toMulEquiv e).symm h, map_rightDvd e⟩

@[deprecated map_dvd_iff +typeChanged (since := "2026-10-26")]
lemma map_dvd_iff_dvd_symm (e : E) {b : N} : e a ∣ b ↔ a ∣ (MulEquivClass.toMulEquiv e).symm b := by
  simp [← map_dvd_iff e]

protected lemma MulHom.map_dvd (f : M →ₙ* N) : a ∣ b → f a ∣ f b := map_dvd f

protected lemma MonoidHom.map_dvd {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {a b : M} :
    a ∣ b → f a ∣ f b := map_dvd f
