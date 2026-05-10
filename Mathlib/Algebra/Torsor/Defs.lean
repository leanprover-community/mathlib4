/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Torsors of group actions

This file defines torsors of additive and multiplicative group actions.

## Notation

The group elements are referred to as acting on points.  This file
uses the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element, as well as `•` and `/ₛ` for the
corresponding operations in multiplicative torsors.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. Multiplicative
torsors are not used much yet, but will play a central role in e.g. the development of the theory
of principal bundles. Most API is written multiplicatively and then also provided in additive form
via `to_additive`.

## Notation

* `v +ᵥ p` is a notation for `VAdd.vadd`, the left action of an additive monoid;
* `p₁ -ᵥ p₂` is a notation for `VSub.vsub`, the difference between two points in an additive torsor
  as an element of the corresponding additive group;
* `v • p` is a notation for `SMul.smul`, the left action of a multiplicative monoid;
* `p₁ /ₛ p₂` is a notation for `SDiv.sdiv`, the quotient of two points in a multiplicative
  torsor as an element of the corresponding multiplicative group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

@[expose] public section

assert_not_exists MonoidWithZero

/-- An `AddTorsor G P` gives a structure to the nonempty type `P`,
acted on by an `AddGroup G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class AddTorsor (G : outParam Type*) (P : Type*) [AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  /-- Torsor subtraction and addition with the same element cancels out. -/
  vsub_vadd' : ∀ p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  /-- Torsor addition and subtraction with the same element cancels out. -/
  vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g

/-- A `Torsor G P` gives a structure to the nonempty type `P`,
acted on by a `Group G` with a transitive and free action given
by the `•` operation and a corresponding division given by the
`/ₛ` operation. -/
@[to_additive existing]
class Torsor (G : outParam Type*) (P : Type*) [Group G] extends MulAction G P, SDiv G P where
  [nonempty : Nonempty P]
  /-- Scalar division and multiplication with the same element cancels out. -/
  sdiv_smul' : ∀ p₁ p₂ : P, (p₁ /ₛ p₂ : G) • p₂ = p₁
  /-- Scalar multiplication and division with the same element cancels out. -/
  smul_sdiv' : ∀ (g : G) (p : P), (g • p) /ₛ p = g

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): removed `nolint instance_priority`; lint not ported yet
attribute [instance 100] AddTorsor.nonempty
attribute [instance 100] Torsor.nonempty

/-- A `Group G` is a torsor for itself. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): linter not ported yet
--@[nolint instance_priority]
@[to_additive /-- An `AddGroup G` is a torsor for itself.-/]
instance Group.toTorsor (G : Type*) [Group G] : Torsor G G where
  sdiv := Div.div
  sdiv_smul' := div_mul_cancel
  smul_sdiv' := mul_div_cancel_right

@[deprecated (since := "2026-05-04")] alias addGroupIsAddTorsor := AddGroup.toAddTorsor

/-- Simplify division for a torsor for a `Group G` over itself. -/
@[to_additive (attr := simp) /-- Simplify subtraction for a torsor for an `AddGroup G` over
itself.-/]
theorem sdiv_eq_div {G : Type*} [Group G] (g₁ g₂ : G) : g₁ /ₛ g₂ = g₁ / g₂ :=
  rfl

section General

variable {G : Type*} {P : Type*} [Group G] [T : Torsor G P]

/-- Scalar multiplying the result of dividing another point produces that point. -/
@[to_additive (attr := simp) /-- Adding the result of subtracting from another point produces that
point. -/]
theorem sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂) • p₂ = p₁ :=
  Torsor.sdiv_smul' p₁ p₂

/-- Multiplying by a group element then dividing by the original point
produces that group element. -/
@[to_additive (attr := simp) /-- Adding a group element then subtracting the original point
produces that group element. -/]
theorem smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g :=
  Torsor.smul_sdiv' g p

/-- If the same point multiplied with two group elements produces equal
results, those group elements are equal. -/
@[to_additive /-- If the same point added to two group elements produces equal
results, those group elements are equal. -/]
theorem smul_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ • p = g₂ • p) : g₁ = g₂ := by
  rw [← smul_sdiv g₁ p, h, smul_sdiv]

@[to_additive (attr := simp)]
theorem smul_right_cancel_iff {g₁ g₂ : G} (p : P) : g₁ • p = g₂ • p ↔ g₁ = g₂ :=
  ⟨smul_right_cancel p, fun h => h ▸ rfl⟩

/-- Multiplying a group element with the point `p` is an injective function. -/
@[to_additive vadd_right_injective /-- Adding a group element to the point `p` is an injective
function. -/]
theorem smul_right_injective' (p : P) : Function.Injective ((· • p) : G → P) := fun _ _ =>
  smul_right_cancel p

/-- Multiplying a group element with a point, then dividing by another point,
produces the same result as dividing the points then multiplying the group element. -/
@[to_additive /-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the group element. -/]
theorem smul_sdiv_assoc (g : G) (p₁ p₂ : P) : (g • p₁) /ₛ p₂ = g * (p₁ /ₛ p₂) := by
  apply smul_right_cancel p₂
  rw [sdiv_smul, mul_smul, sdiv_smul]

/-- Dividing a point by itself produces 1. -/
@[to_additive (attr := simp) /-- Subtracting a point from itself produces 0. -/]
theorem sdiv_self (p : P) : p /ₛ p = (1 : G) := by
  rw [← one_mul (p /ₛ p), ← smul_sdiv_assoc, smul_sdiv]

/-- If dividing two points produces 1, they are equal. -/
@[to_additive /-- If subtracting two points produces 0, they are equal. -/]
theorem eq_of_sdiv_eq_one {p₁ p₂ : P} (h : p₁ /ₛ p₂ = (1 : G)) : p₁ = p₂ := by
  rw [← sdiv_smul p₁ p₂, h, one_smul]

/-- Dividing two points produces 1 if and only if they are equal. -/
@[to_additive (attr := simp) /-- Subtracting two points produces 0 if and only if they are
equal. -/]
theorem sdiv_eq_one_iff_eq {p₁ p₂ : P} : p₁ /ₛ p₂ = (1 : G) ↔ p₁ = p₂ :=
  Iff.intro eq_of_sdiv_eq_one fun h => h ▸ sdiv_self _

@[to_additive]
theorem sdiv_ne_one {p q : P} : p /ₛ q ≠ (1 : G) ↔ p ≠ q :=
  not_congr sdiv_eq_one_iff_eq

/-- Cancellation multiplying the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation adding the results of two subtractions. -/]
theorem sdiv_mul_sdiv_cancel (p₁ p₂ p₃ : P) : (p₁ /ₛ p₂) * (p₂ /ₛ p₃) = p₁ /ₛ p₃ := by
  apply smul_right_cancel p₃
  rw [mul_smul, sdiv_smul, sdiv_smul, sdiv_smul]

/-- Dividing two points in the reverse order produces the inverse of dividing them. -/
@[to_additive (attr := simp) /-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/]
theorem inv_sdiv_eq_sdiv_rev (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ = p₂ /ₛ p₁ := by
  refine inv_eq_of_mul_eq_one_right (smul_right_cancel p₁ ?_)
  rw [sdiv_mul_sdiv_cancel, sdiv_self]

@[to_additive]
theorem smul_sdiv_eq_div_sdiv (g : G) (p q : P) : (g • p) /ₛ q = g / (q /ₛ p) := by
  rw [smul_sdiv_assoc, div_eq_mul_inv, inv_sdiv_eq_sdiv_rev]

/-- Dividing by the result of multiplying with a group element produces the same result
as dividing the points and dividing by that group element. -/
@[to_additive /-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/]
theorem sdiv_smul_eq_sdiv_div (p₁ p₂ : P) (g : G) : p₁ /ₛ (g • p₂) = (p₁ /ₛ p₂) / g := by
  rw [← mul_right_inj (p₂ /ₛ p₁ : G), sdiv_mul_sdiv_cancel, ← inv_sdiv_eq_sdiv_rev, smul_sdiv, ←
    mul_div_assoc, ← inv_sdiv_eq_sdiv_rev, inv_mul_cancel, one_div]

/-- Cancellation dividing the results of two divisions. -/
@[to_additive (attr := simp) /-- Cancellation subtracting the results of two subtractions. -/]
theorem sdiv_div_sdiv_cancel_right (p₁ p₂ p₃ : P) : (p₁ /ₛ p₃) / (p₂ /ₛ p₃) = p₁ /ₛ p₂ := by
  rw [← sdiv_smul_eq_sdiv_div, sdiv_smul]

/-- Convert between an equality with multiplying a group element with a point
and an equality of a division of two points with a group element. -/
@[to_additive /-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group element. -/]
theorem eq_smul_iff_sdiv_eq (p₁ : P) (g : G) (p₂ : P) : p₁ = g • p₂ ↔ p₁ /ₛ p₂ = g :=
  ⟨fun h => h.symm ▸ smul_sdiv _ _, fun h => h ▸ (sdiv_smul _ _).symm⟩

@[to_additive]
theorem smul_eq_smul_iff_inv_mul_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₁⁻¹ * v₂ = p₁ /ₛ p₂ := by
  rw [eq_smul_iff_sdiv_eq, smul_sdiv_assoc, ← mul_right_inj v₁⁻¹, inv_mul_cancel_left, eq_comm]

@[to_additive (attr := simp)]
theorem smul_sdiv_smul_cancel_right (v₁ v₂ : G) (p : P) : (v₁ • p) /ₛ (v₂ • p) = v₁ / v₂ := by
  rw [sdiv_smul_eq_sdiv_div, smul_sdiv_assoc, sdiv_self, mul_one]

end General

namespace Equiv

variable {G : Type*} {P : Type*} [Group G] [Torsor G P]

/-- `v ↦ v • p` as an equivalence. -/
@[to_additive /-- `v ↦ v +ᵥ p` as an equivalence. -/]
def smulConst (p : P) : G ≃ P where
  toFun v := v • p
  invFun p' := p' /ₛ p
  left_inv _ := smul_sdiv _ _
  right_inv _ := sdiv_smul _ _

@[to_additive (attr := simp)]
theorem coe_smulConst (p : P) : ⇑(smulConst p) = fun v => v • p :=
  rfl

@[to_additive (attr := simp)]
theorem coe_smulConst_symm (p : P) : ⇑(smulConst p).symm = fun p' => p' /ₛ p :=
  rfl

/-- `p' ↦ p /ₛ p'` as an equivalence. -/
@[to_additive /-- `p' ↦ p -ᵥ p'` as an equivalence. -/]
def constSDiv (p : P) : P ≃ G where
  toFun := (p /ₛ ·)
  invFun := (·⁻¹ • p)
  left_inv p' := by simp
  right_inv v := by simp [sdiv_smul_eq_sdiv_div]

@[to_additive (attr := simp)]
lemma coe_constSDiv (p : P) : ⇑(constSDiv p) = (p /ₛ ·) := rfl

@[to_additive (attr := simp)]
theorem coe_constSDiv_symm (p : P) : ⇑(constSDiv p).symm = fun (v : G) => v⁻¹ • p :=
  rfl

variable (P)

/-- The permutation given by `p ↦ v • p`. -/
@[to_additive /-- The permutation given by `p ↦ v +ᵥ p`. -/]
def constSMul (v : G) : Equiv.Perm P where
  toFun := (v • ·)
  invFun := (v⁻¹ • ·)
  left_inv p := by simp [smul_smul]
  right_inv p := by simp [smul_smul]

@[to_additive (attr := simp)]
lemma coe_constSMul (v : G) : ⇑(constSMul P v) = (v • ·) := rfl

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

open Function

/-- Point reflection in `x` as a permutation. -/
def pointReflection (x : P) : Perm P :=
  (constVSub x).trans (vaddConst x)

theorem pointReflection_apply (x y : P) : pointReflection x y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
theorem pointReflection_vsub_left (x y : P) : pointReflection x y -ᵥ x = x -ᵥ y :=
  vadd_vsub ..

@[simp]
theorem pointReflection_vsub_right (x y : P) : pointReflection x y -ᵥ y = 2 • (x -ᵥ y) := by
  simp [pointReflection, two_nsmul, vadd_vsub_assoc]

@[simp]
theorem pointReflection_symm (x : P) : (pointReflection x).symm = pointReflection x :=
  ext <| by simp [pointReflection]

@[simp]
theorem pointReflection_self (x : P) : pointReflection x x = x :=
  vsub_vadd _ _

theorem pointReflection_involutive (x : P) : Involutive (pointReflection x : P → P) := fun y =>
  (Equiv.apply_eq_iff_eq_symm_apply _).2 <| by rw [pointReflection_symm]

end Equiv

@[to_additive]
theorem Torsor.subsingleton_iff (G P : Type*) [Group G] [Torsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.smulConst default).subsingleton_congr
