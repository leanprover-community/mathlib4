/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Hom

/-! # Complements to pretransitive actions

When `f : X →ₑ[φ] Y` is an equivariant map with respect to a map
of monoids `φ: M → N`,

- `MulAction.IsPretransitive.of_surjective_map` shows that
  the action of `N` on `Y` is pretransitive
  if that of `M` on `X`  is pretransitive.

- `MulAction.isPretransitive_congr` shows that when
  `φ` is surjective, the action of `N` on `Y` is pretransitive
  iff that of `M` on `X`  is pretransitive.

Given `MulAction G X` where `G` is a group,
- `MulAction.isPretransitive_iff_base G a` shows that `IsPretransitive G X`
  iff every element is translated from `a`

- `MulAction.isPretransitive_iff_orbit_eq_univ G a` shows that `MulAction.IsPretransitive G X`
  iff `MulAction.orbit G a` is full.

-/

variable {G X : Type*} [Group G] [MulAction G X]

namespace MulAction

/-- An action of a group is pretransitive iff any element can be moved from a fixed given one. -/
@[to_additive
  "An additive action of an additive group is pretransitive
  iff any element can be moved from a fixed given one."]
theorem isPretransitive_iff_base (a : X) :
    IsPretransitive G X ↔ ∀ x : X, ∃ g : G, g • a = x where
  mp hG x := exists_smul_eq _ a x
  mpr hG := .mk fun x y ↦ by
    obtain ⟨g, hx⟩ := hG x
    obtain ⟨h, hy⟩ := hG y
    exact ⟨h * g⁻¹, by rw [← hx, smul_smul, inv_mul_cancel_right, hy]⟩

/-- An action of a group is pretransitive iff the orbit of every given element is full -/
@[to_additive
  "An action of a group is pretransitive iff the orbit of every given element is full"]
theorem isPretransitive_iff_orbit_eq_univ (a : X) :
    IsPretransitive G X ↔ orbit G a = .univ := by
  rw [isPretransitive_iff_base a, Set.ext_iff]
  apply forall_congr'
  intro x
  simp_rw [Set.mem_univ, iff_true, mem_orbit_iff]

variable {M N α β : Type*} [Monoid M] [Monoid N] [MulAction M α] [MulAction N β]

@[to_additive]
theorem IsPretransitive.of_surjective_map {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f) (h : IsPretransitive M α) :
    IsPretransitive N β := by
  apply MulAction.IsPretransitive.mk
  intro x y
  obtain ⟨x', rfl⟩ := hf x
  obtain ⟨y', rfl⟩ := hf y
  obtain ⟨g, rfl⟩ := h.exists_smul_eq x' y'
  exact ⟨φ g, by simp only [map_smulₛₗ]⟩

@[to_additive]
theorem isPretransitive_congr {φ : M → N} {f : α →ₑ[φ] β}
    (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPretransitive M α ↔ IsPretransitive N β := by
  constructor
  · apply IsPretransitive.of_surjective_map hf.surjective
  · intro hN
    apply IsPretransitive.mk
    intro x y
    obtain ⟨k, hk⟩ := hN.exists_smul_eq (f x) (f y)
    obtain ⟨g, rfl⟩ := hφ k
    use g
    apply hf.injective
    simp only [hk, map_smulₛₗ]

end MulAction
