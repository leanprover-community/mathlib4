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

-- todo: refactor Mathlib/Algebra/GroupPower/IterateHom to generalize φ to MonoidHomClass
variable {G : Type*}

section Definitions

variable (φ : G → G)

/-- A function `φ : G → G` is fixed-point-free if `1 : G` is the only fixed point of `φ`. -/
def FixedPointFree [One G] := ∀ g, φ g = g → g = 1

/-- The commutator map `g ↦ g / φ g`. If `φ g = h * g * h⁻¹`, then `g / φ g` is exactly the
  commutator `[g, h] = g * h * g⁻¹ * h⁻¹`. -/
def CommutatorMap [Div G] (g : G) := g / φ g

@[simp] theorem commutatorMap_apply [Div G] (g : G) : CommutatorMap φ g = g / φ g := rfl

end Definitions

namespace FixedPointFree

variable [Group G] {φ : G →* G} (hφ : FixedPointFree φ)

theorem injective_commutatorMap : Function.Injective (CommutatorMap φ) := by
  refine' fun x y h ↦ inv_mul_eq_one.mp <| hφ _ _
  rwa [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_div_iff_mul_eq', ← division_def]

variable [Finite G]

theorem surjective_commutatorMap : Function.Surjective (CommutatorMap φ) :=
  Finite.surjective_of_injective hφ.injective_commutatorMap

theorem prod_pow_eq_one {n : ℕ} (hn : φ^[n] = _root_.id) (g : G) :
    ((List.range n).map (fun k ↦ φ^[k] g)).prod = 1 := by
  obtain ⟨g, rfl⟩ := surjective_commutatorMap hφ g
  simp only [commutatorMap_apply, iterate_map_div, ← Function.iterate_succ_apply]
  rw [List.prod_range_div, Function.iterate_zero_apply, hn, Function.id_def, div_self']

theorem eq_inv_of_sq_eq_one (h2 : φ^[2] = _root_.id) : ⇑φ = (·⁻¹) := by
  ext g
  have key : 1 * g * φ g = 1 := hφ.prod_pow_eq_one h2 g
  rwa [one_mul, ← inv_eq_iff_mul_eq_one, eq_comm] at key

lemma eq_inv_of_involutive (h2 : Function.Involutive φ) : ⇑φ = (·⁻¹) :=
  eq_inv_of_sq_eq_one hφ  (funext h2)

end FixedPointFree

end MonoidHom
