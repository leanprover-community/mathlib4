/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module for_mathlib.pretransitive
-/

import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Complements to pretransitive actions

When `f : X →ₑ[φ] Y` is an equivariant map with respect to a map
of monoids `φ: M → N`,

- `IsPretransitive.of_surjective_map` shows that
the action of `N` on `Y` is pretransitive
if that of `M` on `X`  is pretransitive.

- `IsPretransitive.of_bijective_map` shows that when
`φ` is surjective, the action of `N` on `Y` is pretransitive
iff that of `M` on `X`  is pretransitive.

Given `MulAction G X` where `G` is a group,

- `IsPretransitive.mk_base G a` shows that `IsPretransitive G X`
iff every element is translated from `a`

- `IsPretransitive.iff_orbit_eq_top G a` shows that `IsPretransitive G X`
iff the `orbit G a` is full.


-/

variable (G : Type _) [Group G] {X : Type _} [MulAction G X]

namespace MulAction.IsPretransitive

open MulAction

variable {G}

/-- An action of a group is pretransitive iff any element can be moved from a fixed given one -/
theorem mk_base_iff (a : X) :
    IsPretransitive G X ↔ ∀ x : X, ∃ g : G, g • a = x := by
  constructor
  · exact fun hG x ↦ exists_smul_eq a x
  · intro hG
    apply IsPretransitive.mk
    intro x y
    obtain ⟨g, hx⟩ := hG x
    obtain ⟨h, hy⟩ := hG y
    exact ⟨h * g⁻¹, by rw [← hx, smul_smul, inv_mul_cancel_right, hy]⟩

/-- An action of a group is pretransitive iff the orbit of every given element is full -/
theorem iff_orbit_eq_top (a : X) :
    IsPretransitive G X ↔ orbit G a = ⊤ := by
  rw [IsPretransitive.mk_base_iff a, Set.ext_iff]
  apply forall_congr'
  intro x
  simp_rw [Set.top_eq_univ, Set.mem_univ, iff_true_iff, mem_orbit_iff]


variable {M : Type _} [Monoid M] {α : Type _} [MulAction M α]

variable {N β : Type _} [Monoid N] [MulAction N β]

theorem of_surjective_map {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f) (h : IsPretransitive M α) :
    IsPretransitive N β := by
  apply MulAction.IsPretransitive.mk
  intro x y
  obtain ⟨x', rfl⟩ := hf x
  obtain ⟨y', rfl⟩ := hf y
  obtain ⟨g, rfl⟩ := h.exists_smul_eq x' y'
  exact ⟨φ g, by simp only [map_smulₛₗ]⟩

theorem iff_of_bijective_map {φ : M → N} {f : α →ₑ[φ] β}
    (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPretransitive M α ↔ IsPretransitive N β := by
  constructor
  apply of_surjective_map hf.surjective
  · intro hN
    apply IsPretransitive.mk
    intro x y
    obtain ⟨k, hk⟩ := hN.exists_smul_eq (f x) (f y)
    obtain ⟨g, rfl⟩ := hφ k
    use g
    apply hf.injective
    simp only [hk, map_smulₛₗ]

end MulAction.IsPretransitive
