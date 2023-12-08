/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathlib.Data.Set.Pointwise.SMul

#align_import algebra.add_torsor from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Torsors of additive group actions

This file defines torsors of additive group actions.

## Notations

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. It may be appropriate
to refactor in terms of the general definition of group actions, via `to_additive`, when there is a
use for multiplicative torsors (currently mathlib only develops the theory of group actions for
multiplicative group actions).

## Notations

* `v +ᵥ p` is a notation for `VAdd.vadd`, the left action of an additive monoid;

* `p₁ -ᵥ p₂` is a notation for `VSub.vsub`, difference between two points in an additive torsor
  as an element of the corresponding additive group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/

set_option autoImplicit true


/-- An `AddTorsor G P` gives a structure to the nonempty type `P`,
acted on by an `AddGroup G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class AddTorsor (G : outParam (Type*)) (P : Type*) [outParam <| AddGroup G] extends AddAction G P,
  VSub G P where
  [nonempty : Nonempty P]
  /-- Torsor subtraction and addition with the same element cancels out. -/
  vsub_vadd' : ∀ p1 p2 : P, (p1 -ᵥ p2 : G) +ᵥ p2 = p1
  /-- Torsor addition and subtraction with the same element cancels out. -/
  vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g
#align add_torsor AddTorsor

/-- A `MulTorsor G α` gives a structure to the nonempty type `α`,
acted on by an `Group G` with a transitive and free action given
by the `•` operation and a corresponding division given by the
`/ₛ` operation. -/
@[to_additive]
class MulTorsor (G : outParam (Type*)) (α : Type*) [outParam <| Group G]
    extends MulAction G α, SDiv G α where
  [nonempty : Nonempty α]
  /-- Torsor division and multiplication with the same element cancels out. -/
  sdiv_smul' : ∀ p1 p2 : α, (p1 /ₛ p2 : G) • p2 = p1
  /-- Torsor multiplication and division with the same element cancels out. -/
  smul_sdiv' : ∀ (g : G) (p : α), (g • p) /ₛ p = g

-- porting note: removers `nolint instance_priority`
attribute [instance 100] AddTorsor.nonempty
attribute [instance 100] MulTorsor.nonempty

--Porting note: removed
--attribute [nolint dangerous_instance] AddTorsor.toVSub

/- A `Group G` is a torsor for itself -/
@[to_additive "An `AddGroup G` is a torsor for itself"]
--@[nolint instance_priority] Porting note: linter does not exist
instance Group.toMulTorsor (G : Type*) [Group G] : MulTorsor G G where
  sdiv := HDiv.hDiv
  sdiv_smul' := div_mul_cancel'
  smul_sdiv' := mul_div_cancel''
#align add_group_is_add_torsor AddGroup.toAddTorsor

/-- Simplify division for a torsor for a `Group G` over itself. -/
@[to_additive (attr := simp) "Simplify subtraction for a torsor for an `AddGroup G` over itself."]
theorem sdiv_eq_div {G : Type*} [Group G] (g1 g2 : G) : g1 /ₛ g2 = g1 / g2 :=
  rfl
#align vsub_eq_sub vsub_eq_sub

section General

variable {G : Type*} {P : Type*} [Group G] [T : MulTorsor G P]


@[to_additive (attr := simp)
  "Adding the result of subtracting from another point produces that point."]
theorem sdiv_smul (p1 p2 : P) : (p1 /ₛ p2) • p2 = p1 :=
  MulTorsor.sdiv_smul' p1 p2
#align vsub_vadd vsub_vadd

@[to_additive (attr := simp)
  "Adding a group element then subtracting the original point produces that group element."]
theorem smul_sdiv (g : G) (p : P) : (g • p) /ₛ p = g :=
  MulTorsor.smul_sdiv' g p
#align vadd_vsub vadd_vsub

@[to_additive "If the same point added to two group elements produces equal
results, those group elements are equal."]
theorem smul_right_cancel {g1 g2 : G} (p : P) (h : g1 • p = g2 • p) : g1 = g2 := by
-- Porting note: vadd_vsub g₁ → vadd_vsub g₁ p
  rw [← smul_sdiv g1 p, h, smul_sdiv]
#align vadd_right_cancel vadd_right_cancel

@[to_additive (attr := simp)]
theorem smul_right_cancel_iff {g1 g2 : G} (p : P) : g1 • p = g2 • p ↔ g1 = g2 :=
  ⟨smul_right_cancel p, fun h => h ▸ rfl⟩
#align vadd_right_cancel_iff vadd_right_cancel_iff

-- TODO: deduplicate
@[to_additive vadd_right_injective "Adding a group element to the point `p` is an injective
function."]
theorem smul_right_injective' (p : P) : Function.Injective ((· • p) : G → P) := fun _ _ =>
  smul_right_cancel p
#align vadd_right_injective vadd_right_injective

@[to_additive "Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
group element."]
theorem smul_sdiv_assoc (g : G) (p1 p2 : P) : (g • p1) /ₛ p2 = g * (p1 /ₛ p2) := by
  apply smul_right_cancel p2
  rw [sdiv_smul, mul_smul, sdiv_smul]
#align vadd_vsub_assoc vadd_vsub_assoc

@[to_additive (attr := simp) "Subtracting a point from itself produces 0."]
theorem sdiv_self (p : P) : p /ₛ p = (1 : G) := by
  rw [← one_mul (p /ₛ p), ← smul_sdiv_assoc, smul_sdiv]
#align vsub_self vsub_self

@[to_additive "If subtracting two points produces 0, they are equal."]
theorem eq_of_sdiv_eq_one {p1 p2 : P} (h : p1 /ₛ p2 = (1 : G)) : p1 = p2 := by
  rw [← sdiv_smul p1 p2, h, one_smul]
#align eq_of_vsub_eq_zero eq_of_vsub_eq_zero

@[to_additive (attr := simp) "Subtracting two points produces 0 if and only if they are
equal."]
theorem sdiv_eq_one_iff_eq {p1 p2 : P} : p1 /ₛ p2 = (1 : G) ↔ p1 = p2 :=
  Iff.intro eq_of_sdiv_eq_one fun h => h ▸ sdiv_self _
#align vsub_eq_zero_iff_eq vsub_eq_zero_iff_eq

@[to_additive]
theorem sdiv_ne_zero {p q : P} : p /ₛ q ≠ (1 : G) ↔ p ≠ q :=
  not_congr sdiv_eq_one_iff_eq
#align vsub_ne_zero vsub_ne_zero

@[to_additive (attr := simp) "Cancellation adding the results of two subtractions."]
theorem sdiv_mul_sdiv_cancel (p1 p2 p3 : P) : (p1 /ₛ p2) * (p2 /ₛ p3) = p1 /ₛ p3 := by
  apply smul_right_cancel p3
  rw [mul_smul, sdiv_smul, sdiv_smul, sdiv_smul]
#align vsub_add_vsub_cancel vsub_add_vsub_cancel

@[to_additive (attr := simp) "Subtracting two points in the reverse order produces the negation
of subtracting them."]
theorem inv_sdiv_eq_sdiv_rev (p1 p2 : P) : (p1 /ₛ p2)⁻¹ = p2 /ₛ p1 := by
  refine' inv_eq_of_mul_eq_one_right (smul_right_cancel p1 _)
  rw [sdiv_mul_sdiv_cancel, sdiv_self]
#align neg_vsub_eq_vsub_rev neg_vsub_eq_vsub_rev

@[to_additive]
theorem smul_sdiv_eq_div_sdiv (g : G) (p q : P) : (g • p) /ₛ q = g / (q /ₛ p) := by
  rw [smul_sdiv_assoc, div_eq_mul_inv, inv_sdiv_eq_sdiv_rev]
#align vadd_vsub_eq_sub_vsub vadd_vsub_eq_sub_vsub

/-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/
@[to_additive]
theorem sdiv_smul_eq_sdiv_div (p1 p2 : P) (g : G) : p1 /ₛ (g • p2) = p1 /ₛ p2 / g := by
  rw [← mul_right_inj (p2 /ₛ p1 : G), sdiv_mul_sdiv_cancel, ← inv_sdiv_eq_sdiv_rev, smul_sdiv,
    ← mul_div_assoc, ← inv_sdiv_eq_sdiv_rev, inv_mul_self, one_div]
#align vsub_vadd_eq_vsub_sub vsub_vadd_eq_vsub_sub

/-- Cancellation subtracting the results of two subtractions. -/
@[to_additive (attr := simp)]
theorem sdiv_div_sdiv_cancel_right (p1 p2 p3 : P) : (p1 /ₛ p3) / (p2 /ₛ p3) = p1 /ₛ p2 := by
  rw [← sdiv_smul_eq_sdiv_div, sdiv_smul]
#align vsub_sub_vsub_cancel_right vsub_sub_vsub_cancel_right

/-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group
element. -/
@[to_additive]
theorem eq_smul_iff_sdiv_eq (p1 : P) (g : G) (p2 : P) : p1 = g • p2 ↔ p1 /ₛ p2 = g :=
  ⟨fun h => h.symm ▸ smul_sdiv _ _, fun h => h ▸ (sdiv_smul _ _).symm⟩
#align eq_vadd_iff_vsub_eq eq_vadd_iff_vsub_eq

@[to_additive]
theorem smul_eq_smul_iff_inv_mul_eq_sdiv {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₁⁻¹ * v₂ = p₁ /ₛ p₂ := by
  rw [eq_smul_iff_sdiv_eq, smul_sdiv_assoc, ← mul_right_inj (v₁⁻¹), inv_mul_cancel_left, eq_comm]
#align vadd_eq_vadd_iff_neg_add_eq_vsub vadd_eq_vadd_iff_neg_add_eq_vsub

namespace Set

open Pointwise

-- Porting note: simp can prove this
--@[to_additive (attr := simp)]
theorem singleton_vsub_self (p : P) : ({p} : Set P) /ₛ {p} = {(1 : G)} := by
  rw [Set.singleton_vsub_singleton, vsub_self]
#align set.singleton_vsub_self Set.singleton_vsub_self

end Set

@[to_additive (attr := simp)]
theorem vadd_vsub_vadd_cancel_right (v₁ v₂ : G) (p : P) : v₁ • p /ₛ (v₂ • p) = v₁ - v₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, vsub_self, add_zero]
#align vadd_vsub_vadd_cancel_right vadd_vsub_vadd_cancel_right

/-- If the same point subtracted from two points produces equal
results, those points are equal. -/
theorem vsub_left_cancel {p1 p2 p : P} (h : p1 /ₛ p = p2 /ₛ p) : p1 = p2 := by
  rwa [← sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h
#align vsub_left_cancel vsub_left_cancel

/-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/
@[to_additive (attr := simp)]
theorem vsub_left_cancel_iff {p1 p2 p : P} : p1 /ₛ p = p2 /ₛ p ↔ p1 = p2 :=
  ⟨vsub_left_cancel, fun h => h ▸ rfl⟩
#align vsub_left_cancel_iff vsub_left_cancel_iff

/-- Subtracting the point `p` is an injective function. -/
theorem vsub_left_injective (p : P) : Function.Injective ((· /ₛ p) : P → G) := fun _ _ =>
  vsub_left_cancel
#align vsub_left_injective vsub_left_injective

/-- If subtracting two points from the same point produces equal
results, those points are equal. -/
theorem vsub_right_cancel {p1 p2 p : P} (h : p /ₛ p1 = p /ₛ p2) : p1 = p2 := by
  refine' vadd_left_cancel (p /ₛ p2) _
  rw [vsub_vadd, ← h, vsub_vadd]
#align vsub_right_cancel vsub_right_cancel

/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[to_additive (attr := simp)]
theorem vsub_right_cancel_iff {p1 p2 p : P} : p /ₛ p1 = p /ₛ p2 ↔ p1 = p2 :=
  ⟨vsub_right_cancel, fun h => h ▸ rfl⟩
#align vsub_right_cancel_iff vsub_right_cancel_iff

/-- Subtracting a point from the point `p` is an injective
function. -/
theorem vsub_right_injective (p : P) : Function.Injective ((p /ₛ ·) : P → G) := fun _ _ =>
  vsub_right_cancel
#align vsub_right_injective vsub_right_injective

end General

section comm

variable {G : Type*} {P : Type*} [AddCommGroup G] [AddTorsor G P]

-- Porting note: Removed:
-- include G

/-- Cancellation subtracting the results of two subtractions. -/
@[to_additive (attr := simp)]
theorem vsub_sub_vsub_cancel_left (p1 p2 p3 : P) : p3 /ₛ p2 - (p3 /ₛ p1) = p1 /ₛ p2 := by
  rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm, vsub_add_vsub_cancel]
#align vsub_sub_vsub_cancel_left vsub_sub_vsub_cancel_left

@[to_additive (attr := simp)]
theorem vadd_vsub_vadd_cancel_left (v : G) (p1 p2 : P) : v • p1 /ₛ (v • p2) = p1 /ₛ p2 := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_cancel']
#align vadd_vsub_vadd_cancel_left vadd_vsub_vadd_cancel_left

theorem vsub_vadd_comm (p1 p2 p3 : P) : (p1 /ₛ p2 : G) • p3 = p3 /ₛ p2 • p1 := by
  rw [← @vsub_eq_zero_iff_eq G, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub]
  simp
#align vsub_vadd_comm vsub_vadd_comm

theorem vadd_eq_vadd_iff_sub_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ • p₁ = v₂ • p₂ ↔ v₂ - v₁ = p₁ /ₛ p₂ := by
  rw [vadd_eq_vadd_iff_neg_add_eq_vsub, neg_add_eq_sub]
#align vadd_eq_vadd_iff_sub_eq_vsub vadd_eq_vadd_iff_sub_eq_vsub

theorem vsub_sub_vsub_comm (p₁ p₂ p₃ p₄ : P) : p₁ /ₛ p₂ - (p₃ /ₛ p₄) = p₁ /ₛ p₃ - (p₂ /ₛ p₄) := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub]
#align vsub_sub_vsub_comm vsub_sub_vsub_comm

end comm

namespace Prod

variable {G : Type*} [AddGroup G] [AddGroup G'] [AddTorsor G P] [AddTorsor G' P']

instance instAddTorsor : AddTorsor (G × G') (P × P') where
  vadd v p := (v.1 • p.1, v.2 • p.2)
  zero_vadd _ := Prod.ext (zero_vadd _ _) (zero_vadd _ _)
  add_vadd _ _ _ := Prod.ext (add_vadd _ _ _) (add_vadd _ _ _)
  vsub p₁ p₂ := (p₁.1 /ₛ p₂.1, p₁.2 /ₛ p₂.2)
  nonempty := Prod.Nonempty
  vsub_vadd' _ _ := Prod.ext (vsub_vadd _ _) (vsub_vadd _ _)
  vadd_vsub' _ _ := Prod.ext (vadd_vsub _ _) (vadd_vsub _ _)

-- Porting note: The proofs above used to be shorter:
-- zero_vadd p := by simp ⊢ 0 • p = p
-- add_vadd := by simp [add_vadd] ⊢ ∀ (a : G) (b : G') (a_1 : G) (b_1 : G') (a_2 : P) (b_2 : P'),
--  (a + a_1, b + b_1) • (a_2, b_2) = (a, b) • ((a_1, b_1) • (a_2, b_2))
-- vsub_vadd' p₁ p₂ := show (p₁.1 /ₛ p₂.1 • p₂.1, _) = p₁ by simp
--   ⊢ (p₁.fst /ₛ p₂.fst • p₂.fst, ((p₁.fst /ₛ p₂.fst, p₁.snd /ₛ p₂.snd) • p₂).snd) = p₁
-- vadd_vsub' v p := show (v.1 • p.1 /ₛ p.1, v.2 • p.2 /ₛ p.2) = v by simp
--   ⊢ (v.fst • p.fst /ₛ p.fst, v.snd) = v

@[to_additive (attr := simp)]
theorem fst_vadd (v : G × G') (p : P × P') : (v • p).1 = v.1 • p.1 :=
  rfl
#align prod.fst_vadd Prod.fst_vadd

@[to_additive (attr := simp)]
theorem snd_vadd (v : G × G') (p : P × P') : (v • p).2 = v.2 • p.2 :=
  rfl
#align prod.snd_vadd Prod.snd_vadd

@[to_additive (attr := simp)]
theorem mk_vadd_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') • (p, p') = (v • p, v' • p') :=
  rfl
#align prod.mk_vadd_mk Prod.mk_vadd_mk

@[to_additive (attr := simp)]
theorem fst_vsub (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').1 = p₁.1 /ₛ p₂.1 :=
  rfl
#align prod.fst_vsub Prod.fst_vsub

@[to_additive (attr := simp)]
theorem snd_vsub (p₁ p₂ : P × P') : (p₁ /ₛ p₂ : G × G').2 = p₁.2 /ₛ p₂.2 :=
  rfl
#align prod.snd_vsub Prod.snd_vsub

@[to_additive (attr := simp)]
theorem mk_vsub_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') /ₛ (p₂, p₂') : G × G') = (p₁ /ₛ p₂, p₁' /ₛ p₂') :=
  rfl
#align prod.mk_vsub_mk Prod.mk_vsub_mk

end Prod

namespace Pi

universe u v w

variable {I : Type u} {fg : I → Type v} [∀ i, AddGroup (fg i)] {fp : I → Type w}

open AddAction AddTorsor

/-- A product of `AddTorsor`s is an `AddTorsor`. -/
instance instAddTorsor [∀ i, AddTorsor (fg i) (fp i)] : AddTorsor (∀ i, fg i) (∀ i, fp i) where
  vadd g p i := g i • p i
  zero_vadd p := funext fun i => zero_vadd (fg i) (p i)
  add_vadd g₁ g₂ p := funext fun i => add_vadd (g₁ i) (g₂ i) (p i)
  vsub p₁ p₂ i := p₁ i /ₛ p₂ i
  vsub_vadd' p₁ p₂ := funext fun i => vsub_vadd (p₁ i) (p₂ i)
  vadd_vsub' g p := funext fun i => vadd_vsub (g i) (p i)

end Pi

namespace Equiv

variable {G : Type*} {P : Type*} [AddGroup G] [AddTorsor G P]

-- Porting note: Removed:
-- include G

/-- `v ↦ v • p` as an equivalence. -/
def vaddConst (p : P) : G ≃ P where
  toFun v := v • p
  invFun p' := p' /ₛ p
  left_inv _ := vadd_vsub _ _
  right_inv _ := vsub_vadd _ _
#align equiv.vadd_const Equiv.vaddConst

@[to_additive (attr := simp)]
theorem coe_vaddConst (p : P) : ⇑(vaddConst p) = fun v => v • p :=
  rfl
#align equiv.coe_vadd_const Equiv.coe_vaddConst

@[to_additive (attr := simp)]
theorem coe_vaddConst_symm (p : P) : ⇑(vaddConst p).symm = fun p' => p' /ₛ p :=
  rfl
#align equiv.coe_vadd_const_symm Equiv.coe_vaddConst_symm

/-- `p' ↦ p /ₛ p'` as an equivalence. -/
def constVSub (p : P) : P ≃ G where
  toFun := (· /ₛ ·) p
  invFun v := -v • p
  left_inv p' := by simp
  right_inv v := by simp [vsub_vadd_eq_vsub_sub]
#align equiv.const_vsub Equiv.constVSub

@[to_additive (attr := simp)]
theorem coe_constVSub (p : P) : ⇑(constVSub p) = (· /ₛ ·) p :=
  rfl
#align equiv.coe_const_vsub Equiv.coe_constVSub

@[to_additive (attr := simp)]
theorem coe_constVSub_symm (p : P) : ⇑(constVSub p).symm = fun (v : G) => -v • p :=
  rfl
#align equiv.coe_const_vsub_symm Equiv.coe_constVSub_symm

variable (P)

/-- The permutation given by `p ↦ v • p`. -/
def constVAdd (v : G) : Equiv.Perm P where
  toFun := (· • ·) v
  invFun := (· • ·) (-v)
  left_inv p := by simp [vadd_vadd]
  right_inv p := by simp [vadd_vadd]
#align equiv.const_vadd Equiv.constVAdd

@[to_additive (attr := simp)]
theorem coe_constVAdd (v : G) : ⇑(constVAdd P v) = (· • ·) v :=
  rfl
#align equiv.coe_const_vadd Equiv.coe_constVAdd

variable (G)

@[to_additive (attr := simp)]
theorem constVAdd_zero : constVAdd P (1 : G) = 1 :=
  ext <| zero_vadd G
#align equiv.const_vadd_zero Equiv.constVAdd_zero

variable {G}

@[to_additive (attr := simp)]
theorem constVAdd_add (v₁ v₂ : G) : constVAdd P (v₁ + v₂) = constVAdd P v₁ * constVAdd P v₂ :=
  ext <| add_vadd v₁ v₂
#align equiv.const_vadd_add Equiv.constVAdd_add

/-- `Equiv.constVAdd` as a homomorphism from `Multiplicative G` to `Equiv.perm P` -/
def constVAddHom : Multiplicative G →* Equiv.Perm P where
  toFun v := constVAdd P (Multiplicative.toAdd v)
  map_one' := constVAdd_zero G P
  map_mul' := constVAdd_add P
#align equiv.const_vadd_hom Equiv.constVAddHom

variable {P}

-- Porting note: Previous code was:
-- open _Root_.Function
open Function

/-- Point reflection in `x` as a permutation. -/
def pointReflection (x : P) : Perm P :=
  (constVSub x).trans (vaddConst x)
#align equiv.point_reflection Equiv.pointReflection

theorem pointReflection_apply (x y : P) : pointReflection x y = x -ᵥ y +ᵥ x :=
  rfl
#align equiv.point_reflection_apply Equiv.pointReflection_apply

@[simp]
theorem pointReflection_vsub_left (x y : P) : pointReflection x y -ᵥ x = x -ᵥ y :=
  vadd_vsub ..

@[simp]
theorem left_vsub_pointReflection (x y : P) : x -ᵥ pointReflection x y = y -ᵥ x :=
  neg_injective <| by simp

@[simp]
theorem pointReflection_vsub_right (x y : P) : pointReflection x y -ᵥ y = 2 • (x -ᵥ y) := by
  simp [pointReflection, two_nsmul, vadd_vsub_assoc]

@[simp]
theorem right_vsub_pointReflection (x y : P) : y -ᵥ pointReflection x y = 2 • (y -ᵥ x) :=
  neg_injective <| by simp [← neg_nsmul]

@[simp]
theorem pointReflection_symm (x : P) : (pointReflection x).symm = pointReflection x :=
  ext <| by simp [pointReflection]
#align equiv.point_reflection_symm Equiv.pointReflection_symm

@[simp]
theorem pointReflection_self (x : P) : pointReflection x x = x :=
  vsub_vadd _ _
#align equiv.point_reflection_self Equiv.pointReflection_self

theorem pointReflection_involutive (x : P) : Involutive (pointReflection x : P → P) := fun y =>
  (Equiv.apply_eq_iff_eq_symm_apply _).2 <| by rw [pointReflection_symm]
#align equiv.point_reflection_involutive Equiv.pointReflection_involutive

set_option linter.deprecated false
/-- `x` is the only fixed point of `pointReflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem pointReflection_fixed_iff_of_injective_bit0 {x y : P} (h : Injective (bit0 : G → G)) :
    pointReflection x y = y ↔ y = x := by
  rw [pointReflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
    neg_eq_iff_add_eq_zero, ← bit0, ← bit0_zero, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]
#align equiv.point_reflection_fixed_iff_of_injective_bit0 Equiv.pointReflection_fixed_iff_of_injective_bit0

-- Porting note: Removed:
-- omit G

-- Porting note: need this to calm down CI
theorem injective_pointReflection_left_of_injective_bit0 {G P : Type*} [AddCommGroup G]
    [AddTorsor G P] (h : Injective (bit0 : G → G)) (y : P) :
    Injective fun x : P => pointReflection x y :=
  fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [pointReflection_apply, pointReflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero, ← bit0, ← bit0_zero,
    h.eq_iff, vsub_eq_zero_iff_eq] at hy
#align equiv.injective_point_reflection_left_of_injective_bit0 Equiv.injective_pointReflection_left_of_injective_bit0

end Equiv

theorem AddTorsor.subsingleton_iff (G P : Type*) [AddGroup G] [AddTorsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.vaddConst default).subsingleton_congr
#align add_torsor.subsingleton_iff AddTorsor.subsingleton_iff
