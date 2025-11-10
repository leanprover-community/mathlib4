/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Defs

/-!
# Torsors of additive group actions

This file defines torsors of additive group actions.

## Notation

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. It may be appropriate
to refactor in terms of the general definition of group actions, via `to_additive`, when there is a
use for multiplicative torsors (currently mathlib only develops the theory of group actions for
multiplicative group actions).

## Notation

* `v +ᵥ p` is a notation for `VAdd.vadd`, the left action of an additive monoid;

* `p₁ -ᵥ p₂` is a notation for `VSub.vsub`, difference between two points in an additive torsor
  as an element of the corresponding additive group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

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

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): removed `nolint instance_priority`; lint not ported yet
attribute [instance 100] AddTorsor.nonempty

/-- An `AddGroup G` is a torsor for itself. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/12096): linter not ported yet
--@[nolint instance_priority]
instance addGroupIsAddTorsor (G : Type*) [AddGroup G] : AddTorsor G G where
  vsub := Sub.sub
  vsub_vadd' := sub_add_cancel
  vadd_vsub' := add_sub_cancel_right

/-- Simplify subtraction for a torsor for an `AddGroup G` over
itself. -/
@[simp]
theorem vsub_eq_sub {G : Type*} [AddGroup G] (g₁ g₂ : G) : g₁ -ᵥ g₂ = g₁ - g₂ :=
  rfl

section General

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

/-- Adding the result of subtracting from another point produces that
point. -/
@[simp]
theorem vsub_vadd (p₁ p₂ : P) : (p₁ -ᵥ p₂) +ᵥ p₂ = p₁ :=
  AddTorsor.vsub_vadd' p₁ p₂

/-- Adding a group element then subtracting the original point
produces that group element. -/
@[simp]
theorem vadd_vsub (g : G) (p : P) : (g +ᵥ p) -ᵥ p = g :=
  AddTorsor.vadd_vsub' g p

/-- If the same point added to two group elements produces equal
results, those group elements are equal. -/
theorem vadd_right_cancel {g₁ g₂ : G} (p : P) (h : g₁ +ᵥ p = g₂ +ᵥ p) : g₁ = g₂ := by
  rw [← vadd_vsub g₁ p, h, vadd_vsub]

@[simp]
theorem vadd_right_cancel_iff {g₁ g₂ : G} (p : P) : g₁ +ᵥ p = g₂ +ᵥ p ↔ g₁ = g₂ :=
  ⟨vadd_right_cancel p, fun h => h ▸ rfl⟩

/-- Adding a group element to the point `p` is an injective
function. -/
theorem vadd_right_injective (p : P) : Function.Injective ((· +ᵥ p) : G → P) := fun _ _ =>
  vadd_right_cancel p

/-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
group element. -/
theorem vadd_vsub_assoc (g : G) (p₁ p₂ : P) : (g +ᵥ p₁) -ᵥ p₂ = g + (p₁ -ᵥ p₂) := by
  apply vadd_right_cancel p₂
  rw [vsub_vadd, add_vadd, vsub_vadd]

/-- Subtracting a point from itself produces 0. -/
@[simp]
theorem vsub_self (p : P) : p -ᵥ p = (0 : G) := by
  rw [← zero_add (p -ᵥ p), ← vadd_vsub_assoc, vadd_vsub]

/-- If subtracting two points produces 0, they are equal. -/
theorem eq_of_vsub_eq_zero {p₁ p₂ : P} (h : p₁ -ᵥ p₂ = (0 : G)) : p₁ = p₂ := by
  rw [← vsub_vadd p₁ p₂, h, zero_vadd]

/-- Subtracting two points produces 0 if and only if they are
equal. -/
@[simp]
theorem vsub_eq_zero_iff_eq {p₁ p₂ : P} : p₁ -ᵥ p₂ = (0 : G) ↔ p₁ = p₂ :=
  Iff.intro eq_of_vsub_eq_zero fun h => h ▸ vsub_self _

theorem vsub_ne_zero {p q : P} : p -ᵥ q ≠ (0 : G) ↔ p ≠ q :=
  not_congr vsub_eq_zero_iff_eq

/-- Cancellation adding the results of two subtractions. -/
@[simp]
theorem vsub_add_vsub_cancel (p₁ p₂ p₃ : P) : p₁ -ᵥ p₂ + (p₂ -ᵥ p₃) = p₁ -ᵥ p₃ := by
  apply vadd_right_cancel p₃
  rw [add_vadd, vsub_vadd, vsub_vadd, vsub_vadd]

/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
@[simp]
theorem neg_vsub_eq_vsub_rev (p₁ p₂ : P) : -(p₁ -ᵥ p₂) = p₂ -ᵥ p₁ := by
  refine neg_eq_of_add_eq_zero_right (vadd_right_cancel p₁ ?_)
  rw [vsub_add_vsub_cancel, vsub_self]

theorem vadd_vsub_eq_sub_vsub (g : G) (p q : P) : (g +ᵥ p) -ᵥ q = g - (q -ᵥ p) := by
  rw [vadd_vsub_assoc, sub_eq_add_neg, neg_vsub_eq_vsub_rev]

/-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/
theorem vsub_vadd_eq_vsub_sub (p₁ p₂ : P) (g : G) : p₁ -ᵥ (g +ᵥ p₂) = p₁ -ᵥ p₂ - g := by
  rw [← add_right_inj (p₂ -ᵥ p₁ : G), vsub_add_vsub_cancel, ← neg_vsub_eq_vsub_rev, vadd_vsub, ←
    add_sub_assoc, ← neg_vsub_eq_vsub_rev, neg_add_cancel, zero_sub]

/-- Cancellation subtracting the results of two subtractions. -/
@[simp]
theorem vsub_sub_vsub_cancel_right (p₁ p₂ p₃ : P) : p₁ -ᵥ p₃ - (p₂ -ᵥ p₃) = p₁ -ᵥ p₂ := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd]

/-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group
element. -/
theorem eq_vadd_iff_vsub_eq (p₁ : P) (g : G) (p₂ : P) : p₁ = g +ᵥ p₂ ↔ p₁ -ᵥ p₂ = g :=
  ⟨fun h => h.symm ▸ vadd_vsub _ _, fun h => h ▸ (vsub_vadd _ _).symm⟩

theorem vadd_eq_vadd_iff_neg_add_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ -v₁ + v₂ = p₁ -ᵥ p₂ := by
  rw [eq_vadd_iff_vsub_eq, vadd_vsub_assoc, ← add_right_inj (-v₁), neg_add_cancel_left, eq_comm]

@[simp]
theorem vadd_vsub_vadd_cancel_right (v₁ v₂ : G) (p : P) : (v₁ +ᵥ p) -ᵥ (v₂ +ᵥ p) = v₁ - v₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, vsub_self, add_zero]

end General

namespace Equiv

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

/-- `v ↦ v +ᵥ p` as an equivalence. -/
def vaddConst (p : P) : G ≃ P where
  toFun v := v +ᵥ p
  invFun p' := p' -ᵥ p
  left_inv _ := vadd_vsub _ _
  right_inv _ := vsub_vadd _ _

@[simp]
theorem coe_vaddConst (p : P) : ⇑(vaddConst p) = fun v => v +ᵥ p :=
  rfl

@[simp]
theorem coe_vaddConst_symm (p : P) : ⇑(vaddConst p).symm = fun p' => p' -ᵥ p :=
  rfl

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def constVSub (p : P) : P ≃ G where
  toFun := (p -ᵥ ·)
  invFun := (-· +ᵥ p)
  left_inv p' := by simp
  right_inv v := by simp [vsub_vadd_eq_vsub_sub]

@[simp] lemma coe_constVSub (p : P) : ⇑(constVSub p) = (p -ᵥ ·) := rfl

@[simp]
theorem coe_constVSub_symm (p : P) : ⇑(constVSub p).symm = fun (v : G) => -v +ᵥ p :=
  rfl

variable (P)

/-- The permutation given by `p ↦ v +ᵥ p`. -/
def constVAdd (v : G) : Equiv.Perm P where
  toFun := (v +ᵥ ·)
  invFun := (-v +ᵥ ·)
  left_inv p := by simp [vadd_vadd]
  right_inv p := by simp [vadd_vadd]

@[simp] lemma coe_constVAdd (v : G) : ⇑(constVAdd P v) = (v +ᵥ ·) := rfl

variable {P}

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

theorem AddTorsor.subsingleton_iff (G P : Type*) [AddGroup G] [AddTorsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.vaddConst default).subsingleton_congr
