/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Divisibility.Prod
public import Mathlib.Algebra.GroupWithZero.Prod
public import Mathlib.Algebra.Prime.Defs

/-!
# Prime and irreducible elements in a product monoid

-/

@[expose] public section

variable {M N : Type*}

open Prod (isUnit_iff) in
@[to_additive]
theorem Irreducible.irreducible_isUnit_or [Monoid M] [Monoid N] {p : M × N} (h : Irreducible p) :
    (Irreducible p.1 ∧ IsUnit p.2) ∨ (Irreducible p.2 ∧ IsUnit p.1) := by
  apply (h.2 (a := (1, p.2)) (b := (p.1, 1)) (by simp)).imp <;> (intro hu; rw [isUnit_iff] at hu)
  · refine ⟨⟨fun h1 ↦ h.1 (isUnit_iff.mpr ⟨h1, hu.2⟩), fun a b eq ↦ ?_⟩, hu.2⟩
    apply (h.2 (a := (a, p.2)) (b := (b, 1)) (by simp [← eq])).imp <;>
    exact fun hu ↦ (isUnit_iff.mp hu).1
  · refine ⟨⟨fun h2 ↦ h.1 (isUnit_iff.mpr ⟨hu.1, h2⟩), fun a b eq ↦ ?_⟩, hu.1⟩
    apply (h.2 (a := (p.1, a)) (b := (1, b)) (by simp [← eq])).imp <;>
    exact fun hu ↦ (isUnit_iff.mp hu).2

@[to_additive] theorem Prod.irreducible_iff [CommMonoid M] [CommMonoid N] {p : M × N} :
    Irreducible p ↔ (Irreducible p.1 ∧ IsUnit p.2) ∨ (Irreducible p.2 ∧ IsUnit p.1) where
  mp h := h.irreducible_isUnit_or
  mpr h := .mk (fun hu ↦ have hu := p.isUnit_iff.mp hu; h.elim (·.1.1 hu.1) (·.1.1 hu.2)) <| by
    rintro a b rfl
    simp_rw [isUnit_iff]
    obtain h | h := h <;> obtain hu | hu := h.1.2 rfl
    · exact .inl ⟨hu, isUnit_of_mul_isUnit_left h.2⟩
    · exact .inr ⟨hu, isUnit_of_mul_isUnit_right h.2⟩
    · exact .inl ⟨isUnit_of_mul_isUnit_left h.2, hu⟩
    · exact .inr ⟨isUnit_of_mul_isUnit_right h.2, hu⟩

@[to_additive] theorem Prod.prime₀_iff [CommMonoid M] [CommMonoid N] {p : M × N} :
    Prime₀ p ↔ (Prime₀ p.1 ∧ IsUnit p.2) ∨ (Prime₀ p.2 ∧ IsUnit p.1) where
  mp h := by
    apply (h.2 (p.1, 1) (1, p.2) (by simp)).imp <;>
      (intro dvd; simp_rw [prod_dvd_iff, ← isUnit_iff_dvd_one] at dvd)
    · refine ⟨⟨fun h1 ↦ h.1 (isUnit_iff.mpr ⟨h1, dvd.2⟩), fun a b dvd ↦ ?_⟩, dvd.2⟩
      apply (h.2 (a, p.2) (b, 1) (prod_dvd_iff.mpr ⟨dvd, by simp⟩)).imp <;>
      exact fun hu ↦ (prod_dvd_iff.mp hu).1
    · refine ⟨⟨fun h2 ↦ h.1 (isUnit_iff.mpr ⟨dvd.1, h2⟩), fun a b dvd ↦ ?_⟩, dvd.1⟩
      apply (h.2 (p.1, a) (1, b) (prod_dvd_iff.mpr ⟨by simp, dvd⟩)).imp <;>
      exact fun hu ↦ (prod_dvd_iff.mp hu).2
  mpr h := .intro (fun hu ↦ have hu := isUnit_iff.mp hu; h.elim (·.1.1 hu.1) (·.1.1 hu.2))
    fun a b dvd ↦ by
      simp_rw [prod_dvd_iff] at dvd ⊢
      obtain h | h := h
      · apply (h.1.2 _ _ dvd.1).imp <;> exact (⟨·, h.2.dvd⟩)
      · apply (h.1.2 _ _ dvd.2).imp <;> exact (⟨h.2.dvd, ·⟩)

variable [CommMonoidWithZero M] [CommMonoidWithZero N] {p : M × N}

theorem Prime.of_prime_fst_isUnit_snd (hp1 : Prime p.1) (hp2 : IsUnit p.2) : Prime p :=
  ⟨by rintro rfl; exact hp1.1 rfl, Prod.prime₀_iff.mpr (.inl ⟨hp1.2, hp2⟩)⟩

theorem Prime.of_prime_snd_isUnit_fst (hp2 : Prime p.2) (hp1 : IsUnit p.1) : Prime p :=
  ⟨by rintro rfl; exact hp2.1 rfl, Prod.prime₀_iff.mpr (.inr ⟨hp2.2, hp1⟩)⟩
