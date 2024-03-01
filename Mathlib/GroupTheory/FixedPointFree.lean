/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Group.Aut
import Mathlib.Algebra.GroupPower.IterateHom
import Mathlib.Data.Fintype.Card

/-!
# Fixed-point-free automorphisms

This file defines fixed-point-free automorphisms and proves some basic properties.

An automorphism `φ` of a group `G` is fixed-point-free if `1 : G` is the only fixed point of `φ`.
-/

namespace MonoidHom

variable {G : Type*} {F : Type*} [FunLike F G G] (φ : F)

/-- A function `φ : G → G` is fixed-point-free if `1 : G` is the only fixed point of `φ`. -/
def FixedPointFree [One G] := ∀ g, φ g = g → g = 1

namespace FixedPointFree

variable [Group G]

/-- The commutator map `g ↦ g / φ g`. If `φ g = h * g * h⁻¹`, then `g / φ g` is exactly the
  commutator `[g, h] = g * h * g⁻¹ * h⁻¹`. -/
def CommutatorMap (g : G) := g / φ g

@[simp] theorem commutatorMap_apply (g : G) : CommutatorMap φ g = g / φ g := rfl

variable {φ} [MonoidHomClass F G G] (hφ : FixedPointFree φ)

theorem injective_commutatorMap : Function.Injective (CommutatorMap φ) := by
  refine' fun x y h ↦ inv_mul_eq_one.mp <| hφ _ _
  rwa [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_div_iff_mul_eq', ← division_def]

variable [Finite G]

theorem surjective_commutatorMap : Function.Surjective (CommutatorMap φ) :=
  Finite.surjective_of_injective hφ.injective_commutatorMap

theorem prod_pow_eq_one {n : ℕ} (hn : φ^[n] = id G) (g : G) :
    ((List.range n).map (fun k ↦ φ^[k] g)).prod = 1 := by
  obtain ⟨g, rfl⟩ := surjective_commutatorMap hφ g
  simp only [commutatorMap_apply, iterate_map_div, ← Function.iterate_succ_apply]
  rw [List.prod_range_div, Function.iterate_zero_apply, hn, id_apply, div_self']

theorem eq_inv_of_sq_eq_one (hn : φ^[2] = id G) : ⇑φ = (·⁻¹) := by
  ext g
  have key : 1 * g * φ g = 1 := hφ.prod_pow_eq_one hn g
  rwa [one_mul, ← inv_eq_iff_mul_eq_one, eq_comm] at key

lemma eq_inv_of_involutive {F : Type*} [FunLike F G G] [MonoidHomClass F G G] {φ : F}
    (hφ₁ : FixedPointFree φ) (hφ₂ : Function.Involutive φ) : ⇑φ = (·⁻¹) :=
  eq_inv_of_sq_eq_one hφ₁  (funext hφ₂)

end FixedPointFree

end MonoidHom
