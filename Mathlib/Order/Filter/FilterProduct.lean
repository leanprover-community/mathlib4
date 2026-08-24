/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Order.Filter.Ring
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `Order.Filter.Germ`.

## Tags

ultrafilter, ultraproduct
-/

public section


universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

namespace Filter

local notation3 "∀* "(...)", "r:(scoped p => Filter.Eventually p (Ultrafilter.toFilter φ)) => r

namespace Germ

open Ultrafilter

local notation "β*" => Germ (φ : Filter α) β

instance instGroupWithZero [GroupWithZero β] : GroupWithZero β* where
  __ := instDivInvMonoid
  __ := instMonoidWithZero
  mul_inv_cancel := by
    intro f hf
    induction f using inductionOn with | coe f
    rw [← coe_inv, ← coe_mul, ← coe_one, coe_eq]
    rw [← coe_zero, ne_eq, coe_eq] at hf
    exact ((φ.em _).resolve_left hf).mono fun _ => mul_inv_cancel₀
  inv_zero := by
    simp_rw [← coe_zero, ← coe_inv, Pi.inv_def, Pi.zero_def, inv_zero]

instance instDivisionSemiring [DivisionSemiring β] : DivisionSemiring β* where
  toSemiring := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl

instance instDivisionRing [DivisionRing β] : DivisionRing β* where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl

instance instSemifield [Semifield β] : Semifield β* where
  __ := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field β] : Field β* where
  __ := instCommRing
  __ := instDivisionRing

theorem coe_lt [Preorder β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x := by
  simp only [lt_iff_le_not_ge, eventually_and, coe_le, eventually_not, EventuallyLE]

theorem coe_pos [Preorder β] [Zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x :=
  coe_lt

@[simp, norm_cast]
theorem const_lt_iff [Preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
  coe_lt.trans Filter.eventually_const

alias ⟨_, const_lt⟩ := const_lt_iff

theorem lt_def [Preorder β] : ((· < ·) : β* → β* → Prop) = LiftRel (· < ·) := by
  ext f g
  induction f, g using inductionOn₂ with | coe f g
  rw [coe_lt, liftRel_coe]

instance total [LE β] [@Std.Total β (· ≤ ·)] : @Std.Total β* (· ≤ ·) where
  total := by
    intro a b
    induction a, b using inductionOn₂ with | coe a b
    rw [coe_le, coe_le]
    exact eventually_or.1 (.of_forall fun _ => Std.Total.total _ _)

open scoped Classical in
/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
noncomputable instance instLinearOrder [LinearOrder β] : LinearOrder β* :=
  Lattice.toLinearOrder _

instance instIsStrictOrderedRing [Semiring β] [PartialOrder β] [IsStrictOrderedRing β] :
    IsStrictOrderedRing β* where
  mul_lt_mul_of_pos_left := by
    intro x hx y z hyz
    induction x, y, z using inductionOn₃ with | coe x y z
    rw [← coe_zero, coe_lt] at hx
    rw [coe_lt] at hyz
    rw [← coe_mul, ← coe_mul, coe_lt]
    exact hx.mp <| hyz.mono fun _ => mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := by
    intro x hx y z hyz
    induction x, y, z using inductionOn₃ with | coe x y z
    rw [← coe_zero, coe_lt] at hx
    rw [coe_lt] at hyz
    rw [← coe_mul, ← coe_mul, coe_lt]
    exact hx.mp <| hyz.mono fun _ => mul_lt_mul_of_pos_right

theorem max_def [LinearOrder β] (x y : β*) : max x y = map₂ max x y :=
  rfl

theorem min_def [K : LinearOrder β] (x y : β*) : min x y = map₂ min x y :=
  rfl

theorem abs_def [AddCommGroup β] [LinearOrder β] (x : β*) :
    |x| = map abs x := by
  unfold abs
  induction x using inductionOn with | coe x
  rw [max_def, ← coe_neg, map₂_coe, map_coe]
  rfl

theorem const_max [LinearOrder β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y := by
  rw [max_def, map₂_const]

theorem const_min [LinearOrder β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y := by
  rw [min_def, map₂_const]

@[simp]
theorem const_abs [AddCommGroup β] [LinearOrder β] (x : β) :
    (↑|x| : β*) = |↑x| := by
  rw [abs_def, map_const]

end Germ

end Filter
