/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Group.Aut
import Mathlib.Data.Fintype.Card

/-!
# Fixed-point-free automorphisms

This file defines fixed-point-free automorphisms and proves some basic properties.

An automorphism `φ` of a group `G` is fixed-point-free if `1 : G` is the only fixed point of `φ`.
-/

namespace MulEquiv

/-- A function `φ : G → G` is fixed-point-free if `1 : G` is the only fixed point of `φ`. -/
def FixedPointFree {G : Type*} [One G] (φ : G → G) := ∀ g, φ g = g → g = 1

namespace FixedPointFree

variable {G : Type*} [Group G]

section MonoidHom

variable {F : Type*} [FunLike F G G] [MonoidHomClass F G G] {φ : F} (hφ : FixedPointFree φ)

theorem injective_commutatorMap : Function.Injective fun g => g⁻¹ * φ g := by
  refine' fun x y h ↦ mul_inv_eq_one.mp <| hφ _ _
  rwa [map_mul, map_inv, mul_inv_eq_iff_eq_mul, mul_assoc, ← inv_mul_eq_iff_eq_mul]

variable [Finite G]

theorem surjective_commutatorMap : Function.Surjective fun g => g⁻¹ * φ g :=
  Finite.surjective_of_injective hφ.injective_commutatorMap

end MonoidHom

variable [Finite G]

section MulEquiv

variable {φ : G ≃* G} (hφ : FixedPointFree φ)

theorem prod_pow_eq_one {n : ℕ} (hn : φ ^ n = 1) (g : G) :
    ((List.range n).map (fun k ↦ (φ ^ k) g)).prod = 1 := by
  obtain ⟨g, rfl⟩ := surjective_commutatorMap hφ g
  simp only [MonoidHom.coe_coe, map_mul, map_inv, ← MulAut.mul_apply, ← pow_succ']
  rw [List.prod_map_range_cancel, pow_zero, hn, inv_mul_self]

theorem eq_inv_of_sq_eq_one (hn : φ ^ 2 = 1) : ⇑φ = (·⁻¹) := by
  ext g
  have key : 1 * g * φ g = 1 := hφ.prod_pow_eq_one hn g
  rwa [one_mul, ← inv_eq_iff_mul_eq_one, eq_comm] at key

end MulEquiv

lemma eq_inv_of_involutive {F : Type*} [FunLike F G G] [MonoidHomClass F G G] {φ : F}
    (hφ₁ : FixedPointFree φ) (hφ₂ : Function.Involutive φ) : ⇑φ = (·⁻¹) :=
  eq_inv_of_sq_eq_one (φ := ofBijective φ hφ₂.bijective) hφ₁ (ext hφ₂)

end FixedPointFree

end MulEquiv
