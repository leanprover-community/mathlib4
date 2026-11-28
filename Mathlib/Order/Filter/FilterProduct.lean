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

variable {α : Type u} {β : Type v} {ε : α → Type v} {φ : Ultrafilter α}

namespace Filter

local notation3 "∀* "(...)", "r:(scoped p => Filter.Eventually p (Ultrafilter.toFilter φ)) => r

namespace Product

open Ultrafilter

local notation "β*" => Germ (φ : Filter α) β
local notation "ε*" => Product (φ : Filter α) ε

instance instGroupWithZero [∀ i, GroupWithZero (ε i)] : GroupWithZero ε* where
  mul_inv_cancel a := by
    induction a using inductionOn with | ofFun a
    simp only [← coe_mul, ← coe_inv, ← coe_zero, ← coe_one, ofFun_eq, ne_eq,
      Pi.zero_apply, Pi.one_apply, Pi.mul_apply, Pi.inv_apply]
    rw [← eventually_not]
    intro h
    filter_upwards [h] with x hx
    exact mul_inv_cancel₀ hx
  inv_zero := by simp [← coe_zero, ← coe_inv]

instance instNNRatCast {l : Filter α} [∀ i, NNRatCast (ε i)] : NNRatCast (Product l ε) where
  nnratCast q := ofFun fun _ => q

@[simp]
theorem nnratCast_def {l : Filter α} [∀ i, NNRatCast (ε i)] (q : ℚ≥0) :
    ((fun _ ↦ q : (x : α) → ε x) : Product l ε) = q := rfl

instance instDivisionSemiring [∀ i, DivisionSemiring (ε i)] : DivisionSemiring ε* where
  nnratCast_def := by simp [← nnratCast_def, ← natCast_def, ← coe_div, NNRat.cast_def]
  nnqsmul a b := a • b
  nnqsmul_def q a := by
    induction a using inductionOn with | ofFun a
    simp [← coe_smul, ← nnratCast_def, ← coe_mul, NNRat.smul_def]

instance instRatCast {l : Filter α} [∀ i, RatCast (ε i)] : RatCast (Product l ε) where
  ratCast q := ofFun fun _ => q

@[simp]
theorem ratCast_def {l : Filter α} [∀ i, RatCast (ε i)] (q : ℚ) :
    ((fun _ ↦ q : (x : α) → ε x) : Product l ε) = q := rfl

instance instDivisionRing [∀ i, DivisionRing (ε i)] : DivisionRing ε* where
  __ := instRing
  __ := instDivisionSemiring
  ratCast_def := by simp [← ratCast_def, ← natCast_def, ← intCast_def, ← coe_div, Rat.cast_def]
  qsmul a b := a • b
  qsmul_def q a := by
    induction a using inductionOn with | ofFun a
    simp [← coe_smul, ← ratCast_def, ← coe_mul, Rat.smul_def]

instance instSemifield [∀ i, Semifield (ε i)] : Semifield ε* where

instance instField [∀ i, Field (ε i)] : Field ε* where

theorem coe_lt [∀ i, Preorder (ε i)] {f g : (x : α) → ε x} : (f : ε*) < g ↔ ∀* x, f x < g x := by
  simp only [lt_iff_le_not_ge, eventually_and, coe_le, eventually_not]

theorem coe_pos [∀ i, Preorder (ε i)] [∀ i, Zero (ε i)] {f : (x : α) → ε x} :
    0 < (f : ε*) ↔ ∀* x, 0 < f x :=
  coe_lt

theorem _root_.Filter.Germ.const_lt [Preorder β] {x y : β} : x < y → (↑x : β*) < ↑y :=
  coe_lt.mpr ∘ Germ.liftRel_const

@[simp, norm_cast]
theorem _root_.Filter.Germ.const_lt_iff [Preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
  coe_lt.trans Germ.liftRel_const_iff

theorem lt_def [∀ i, Preorder (ε i)] : (LT.lt : ε* → ε* → Prop) = LiftRel fun _ x y => x < y := by
  ext ⟨f⟩ ⟨g⟩
  exact coe_lt

instance total [∀ i, LE (ε i)] [∀ i, @Std.Total (ε i) (· ≤ ·)] : @Std.Total ε* (· ≤ ·) where
  total a b := by
    induction a, b using inductionOn₂ with | ofFun a b
    simp [coe_le, ← eventually_or, Std.le_total]

open scoped Classical in
/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
noncomputable instance instLinearOrder [∀ i, LinearOrder (ε i)] : LinearOrder ε* :=
  Lattice.toLinearOrder _

instance instIsStrictOrderedRing [∀ i, Semiring (ε i)] [∀ i, PartialOrder (ε i)]
    [∀ i, IsStrictOrderedRing (ε i)] : IsStrictOrderedRing ε* where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp only [← coe_zero, ← coe_mul, coe_lt, Pi.zero_apply, Pi.mul_apply] at ha hbc ⊢
    filter_upwards [ha, hbc] with x hax hbcx
    exact mul_lt_mul_of_pos_left hbcx hax
  mul_lt_mul_of_pos_right a ha b c hbc := by
    induction a, b, c using inductionOn₃ with | ofFun a b c
    simp only [← coe_zero, ← coe_mul, coe_lt, Pi.zero_apply, Pi.mul_apply] at ha hbc ⊢
    filter_upwards [ha, hbc] with x hax hbcx
    exact mul_lt_mul_of_pos_right hbcx hax

theorem max_def {l : Filter α} [∀ i, SemilatticeSup (ε i)] (x y : Product l ε) :
    max x y = Product.map₂ (fun _ => max) x y := rfl

theorem min_def {l : Filter α} [∀ i, SemilatticeInf (ε i)] (x y : Product l ε) :
    min x y = Product.map₂ (fun _ => min) x y := rfl

theorem abs_def {l : Filter α} [∀ i, AddGroup (ε i)] [∀ i, Lattice (ε i)] (x : Product l ε) :
    |x| = map (fun _ => abs) x := by
  induction x using inductionOn with | ofFun x => simp [abs, ← coe_neg, ← coe_sup]

@[deprecated Germ.const_sup +typeChanged (since := "2026-10-06")]
theorem _root_.Filter.Germ.const_max
    [LinearOrder β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y := by
  simp

@[deprecated Germ.const_inf +typeChanged (since := "2026-10-06")]
theorem _root_.Filter.Germ.const_min
    [LinearOrder β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y := by
  simp

@[simp]
theorem _root_.Filter.Germ.const_abs [AddCommGroup β] [LinearOrder β] (x : β) :
    (↑|x| : β*) = |↑x| := by
  rw [abs_def, ← Germ.map_const]

end Product

end Filter
