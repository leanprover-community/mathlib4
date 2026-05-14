/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Fixed-point-free automorphisms

This file defines fixed-point-free automorphisms and proves some basic properties.

An automorphism `φ` of a group `G` is fixed-point-free if `1 : G` is the only fixed point of `φ`.
-/

@[expose] public section

namespace MonoidHom

variable {F G : Type*}

section Definitions

variable (φ : G → G)

/-- A function `φ : G → G` is fixed-point-free if `1 : G` is the only fixed point of `φ`. -/
def FixedPointFree [One G] := ∀ g, φ g = g → g = 1

/-- The commutator map `g ↦ g / φ g`. If `φ g = h * g * h⁻¹`, then `g / φ g` is exactly the
commutator `[g, h] = g * h * g⁻¹ * h⁻¹`. -/
def commutatorMap [Div G] (g : G) := g / φ g

@[simp] theorem commutatorMap_apply [Div G] (g : G) : commutatorMap φ g = g / φ g := rfl

end Definitions

namespace FixedPointFree
variable [Group G] [FunLike F G G] [MonoidHomClass F G G] {φ : F}

theorem commutatorMap_injective (hφ : FixedPointFree φ) : Function.Injective (commutatorMap φ) := by
  refine fun x y h ↦ inv_mul_eq_one.mp <| hφ _ ?_
  rwa [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_div_iff_mul_eq', ← division_def]

variable [Finite G]

theorem commutatorMap_surjective (hφ : FixedPointFree φ) : Function.Surjective (commutatorMap φ) :=
  Finite.surjective_of_injective hφ.commutatorMap_injective

theorem prod_pow_eq_one (hφ : FixedPointFree φ) {n : ℕ} (hn : φ^[n] = _root_.id) (g : G) :
    ((List.range n).map (fun k ↦ φ^[k] g)).prod = 1 := by
  obtain ⟨g, rfl⟩ := commutatorMap_surjective hφ g
  simp only [commutatorMap_apply, iterate_map_div, ← Function.iterate_succ_apply]
  rw [List.prod_range_div', Function.iterate_zero_apply, hn, Function.id_def, div_self']

theorem coe_eq_inv_of_sq_eq_one (hφ : FixedPointFree φ) (h2 : φ^[2] = _root_.id) : ⇑φ = (·⁻¹) := by
  ext g
  have key : g * φ g = 1 := by simpa [List.range_succ] using hφ.prod_pow_eq_one h2 g
  rwa [← inv_eq_iff_mul_eq_one, eq_comm] at key

section Involutive

theorem coe_eq_inv_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    ⇑φ = (·⁻¹) :=
  coe_eq_inv_of_sq_eq_one hφ (funext h2)

theorem commute_all_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g h : G) :
    Commute g h := by
  have key := map_mul φ g h
  rwa [hφ.coe_eq_inv_of_involutive h2, inv_eq_iff_eq_inv, mul_inv_rev, inv_inv, inv_inv] at key

/-- If a finite group admits a fixed-point-free involution, then it is commutative. -/
@[implicit_reducible]
def commGroupOfInvolutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    CommGroup G := .mk (hφ.commute_all_of_involutive h2)

theorem orderOf_ne_two_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G) :
    orderOf g ≠ 2 := by
  intro hg
  have key : φ g = g := by
    rw [hφ.coe_eq_inv_of_involutive h2, inv_eq_iff_mul_eq_one, ← sq, ← hg, pow_orderOf_eq_one]
  rw [hφ g key, orderOf_one] at hg
  contradiction

theorem odd_card_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    Odd (Nat.card G) := by
  have := Fintype.ofFinite G
  by_contra h
  rw [Nat.not_odd_iff_even, even_iff_two_dvd, Nat.card_eq_fintype_card] at h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 h
  exact hφ.orderOf_ne_two_of_involutive h2 g hg

theorem odd_orderOf_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G) :
    Odd (orderOf g) :=
  Odd.of_dvd_nat (hφ.odd_card_of_involutive h2) (orderOf_dvd_natCard g)

end Involutive

end FixedPointFree

end MonoidHom
