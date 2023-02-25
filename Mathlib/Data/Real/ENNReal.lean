/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov

! This file was ported from Lean 3 source module data.real.ennreal
! leanprover-community/mathlib commit afdb4fa3b32d41106a4a09b371ce549ad7958abd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Real.NNReal
import Mathlib.Algebra.Order.Sub.WithTop

/-!
# Extended non-negative reals

We define `ennreal = ℝ≥0∞ := with_top ℝ≥0` to be the type of extended nonnegative real numbers,
i.e., the interval `[0, +∞]`. This type is used as the codomain of a `measure_theory.measure`,
and of the extended distance `edist` in a `emetric_space`.
In this file we define some algebraic operations and a linear order on `ℝ≥0∞`
and prove basic properties of these operations, order, and conversions to/from `ℝ`, `ℝ≥0`, and `ℕ`.

## Main definitions

* `ℝ≥0∞`: the extended nonnegative real numbers `[0, ∞]`; defined as `with_top ℝ≥0`; it is
  equipped with the following structures:

  - coercion from `ℝ≥0` defined in the natural way;

  - the natural structure of a complete dense linear order: `↑p ≤ ↑q ↔ p ≤ q` and `∀ a, a ≤ ∞`;

  - `a + b` is defined so that `↑p + ↑q = ↑(p + q)` for `(p q : ℝ≥0)` and `a + ∞ = ∞ + a = ∞`;

  - `a * b` is defined so that `↑p * ↑q = ↑(p * q)` for `(p q : ℝ≥0)`, `0 * ∞ = ∞ * 0 = 0`, and `a *
    ∞ = ∞ * a = ∞` for `a ≠ 0`;

  - `a - b` is defined as the minimal `d` such that `a ≤ d + b`; this way we have
    `↑p - ↑q = ↑(p - q)`, `∞ - ↑p = ∞`, `↑p - ∞ = ∞ - ∞ = 0`; note that there is no negation, only
    subtraction;

  - `a⁻¹` is defined as `Inf {b | 1 ≤ a * b}`. This way we have `(↑p)⁻¹ = ↑(p⁻¹)` for
    `p : ℝ≥0`, `p ≠ 0`, `0⁻¹ = ∞`, and `∞⁻¹ = 0`.

  - `a / b` is defined as `a * b⁻¹`.

  The addition and multiplication defined this way together with `0 = ↑0` and `1 = ↑1` turn
  `ℝ≥0∞` into a canonically ordered commutative semiring of characteristic zero.

* Coercions to/from other types:

  - coercion `ℝ≥0 → ℝ≥0∞` is defined as `has_coe`, so one can use `(p : ℝ≥0)` in a context that
    expects `a : ℝ≥0∞`, and Lean will apply `coe` automatically;

  - `ennreal.to_nnreal` sends `↑p` to `p` and `∞` to `0`;

  - `ennreal.to_real := coe ∘ ennreal.to_nnreal` sends `↑p`, `p : ℝ≥0` to `(↑p : ℝ)` and `∞` to `0`;

  - `ennreal.of_real := coe ∘ real.to_nnreal` sends `x : ℝ` to `↑⟨max x 0, _⟩`

  - `ennreal.ne_top_equiv_nnreal` is an equivalence between `{a : ℝ≥0∞ // a ≠ 0}` and `ℝ≥0`.

## Implementation notes

We define a `can_lift ℝ≥0∞ ℝ≥0` instance, so one of the ways to prove theorems about an `ℝ≥0∞`
number `a` is to consider the cases `a = ∞` and `a ≠ ∞`, and use the tactic `lift a to ℝ≥0 using ha`
in the second case. This instance is even more useful if one already has `ha : a ≠ ∞` in the
context, or if we have `(f : α → ℝ≥0∞) (hf : ∀ x, f x ≠ ∞)`.

## Notations

* `ℝ≥0∞`: the type of the extended nonnegative real numbers;
* `ℝ≥0`: the type of nonnegative real numbers `[0, ∞)`; defined in `data.real.nnreal`;
* `∞`: a localized notation in `ℝ≥0∞` for `⊤ : ℝ≥0∞`.

-/


open Classical Set

open Classical BigOperators NNReal

variable {α : Type _} {β : Type _}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
def ENNReal :=
  WithTop ℝ≥0deriving Zero, AddCommMonoidWithOne, SemilatticeSup, DistribLattice, OrderBot,
  BoundedOrder, CanonicallyOrderedCommSemiring, CompleteLinearOrder, DenselyOrdered, Nontrivial,
  CanonicallyLinearOrderedAddMonoid, Sub, OrderedSub, LinearOrderedAddCommMonoidWithTop
#align ennreal ENNReal

-- mathport name: ennreal
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal

-- mathport name: ennreal.top
scoped[ENNReal] notation "∞" => (⊤ : ENNReal)

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

-- TODO: why are the two covariant instances necessary? why aren't they inferred?
instance covariantClass_mul_le : CovariantClass ℝ≥0∞ ℝ≥0∞ (· * ·) (· ≤ ·) :=
  CanonicallyOrderedCommSemiring.toCovariantClassMulLE
#align ennreal.covariant_class_mul_le ENNReal.covariantClass_mul_le

instance covariantClass_add_le : CovariantClass ℝ≥0∞ ℝ≥0∞ (· + ·) (· ≤ ·) :=
  OrderedAddCommMonoid.to_covariantClass_left ℝ≥0∞
#align ennreal.covariant_class_add_le ENNReal.covariantClass_add_le

noncomputable instance : LinearOrderedCommMonoidWithZero ℝ≥0∞ :=
  { ENNReal.linearOrderedAddCommMonoidWithTop,
    show CommSemiring ℝ≥0∞ from
      inferInstance with
    mul_le_mul_left := fun a b => mul_le_mul_left'
    zero_le_one := zero_le 1 }

instance : Inhabited ℝ≥0∞ :=
  ⟨0⟩

instance : Coe ℝ≥0 ℝ≥0∞ :=
  ⟨Option.some⟩

instance canLift : CanLift ℝ≥0∞ ℝ≥0 coe fun r => r ≠ ∞
    where prf x hx := ⟨Option.get <| Option.ne_none_iff_isSome.1 hx, Option.some_get _⟩
#align ennreal.can_lift ENNReal.canLift

@[simp]
theorem none_eq_top : (none : ℝ≥0∞) = ∞ :=
  rfl
#align ennreal.none_eq_top ENNReal.none_eq_top

@[simp]
theorem some_eq_coe (a : ℝ≥0) : (choose a : ℝ≥0∞) = (↑a : ℝ≥0∞) :=
  rfl
#align ennreal.some_eq_coe ENNReal.some_eq_coe

/-- `to_nnreal x` returns `x` if it is real, otherwise 0. -/
protected def toNNReal : ℝ≥0∞ → ℝ≥0 :=
  WithTop.untop' 0
#align ennreal.to_nnreal ENNReal.toNNReal

/-- `to_real x` returns `x` if it is real, `0` otherwise. -/
protected def toReal (a : ℝ≥0∞) : Real :=
  coe a.toNNReal
#align ennreal.to_real ENNReal.toReal

/-- `of_real x` returns `x` if it is nonnegative, `0` otherwise. -/
protected noncomputable def ofReal (r : Real) : ℝ≥0∞ :=
  coe (Real.toNNReal r)
#align ennreal.of_real ENNReal.ofReal

@[simp, norm_cast]
theorem toNNReal_coe : (r : ℝ≥0∞).toNNReal = r :=
  rfl
#align ennreal.to_nnreal_coe ENNReal.toNNReal_coe

@[simp]
theorem coe_toNNReal : ∀ {a : ℝ≥0∞}, a ≠ ∞ → ↑a.toNNReal = a
  | some r, h => rfl
  | none, h => (h rfl).elim
#align ennreal.coe_to_nnreal ENNReal.coe_toNNReal

@[simp]
theorem ofReal_toReal {a : ℝ≥0∞} (h : a ≠ ∞) : ENNReal.ofReal a.toReal = a := by
  simp [ENNReal.toReal, ENNReal.ofReal, h]
#align ennreal.of_real_to_real ENNReal.ofReal_toReal

@[simp]
theorem toReal_ofReal {r : ℝ} (h : 0 ≤ r) : ENNReal.toReal (ENNReal.ofReal r) = r := by
  simp [ENNReal.toReal, ENNReal.ofReal, Real.coe_toNNReal _ h]
#align ennreal.to_real_of_real ENNReal.toReal_ofReal

theorem toReal_of_real' {r : ℝ} : ENNReal.toReal (ENNReal.ofReal r) = max r 0 :=
  rfl
#align ennreal.to_real_of_real' ENNReal.toReal_of_real'

theorem coe_toNNReal_le_self : ∀ {a : ℝ≥0∞}, ↑a.toNNReal ≤ a
  | some r => by rw [some_eq_coe, to_nnreal_coe] <;> exact le_rfl
  | none => le_top
#align ennreal.coe_to_nnreal_le_self ENNReal.coe_toNNReal_le_self

theorem coe_nNReal_eq (r : ℝ≥0) : (r : ℝ≥0∞) = ENNReal.ofReal r := by
  rw [ENNReal.ofReal, Real.toNNReal]
  cases' r with r h
  congr
  dsimp
  rw [max_eq_left h]
#align ennreal.coe_nnreal_eq ENNReal.coe_nNReal_eq

theorem ofReal_eq_coe_nNReal {x : ℝ} (h : 0 ≤ x) :
    ENNReal.ofReal x = @coe ℝ≥0 ℝ≥0∞ _ (⟨x, h⟩ : ℝ≥0) := by
  rw [coe_nnreal_eq]
  rfl
#align ennreal.of_real_eq_coe_nnreal ENNReal.ofReal_eq_coe_nNReal

@[simp]
theorem ofReal_coe_nNReal : ENNReal.ofReal p = p :=
  (coe_nNReal_eq p).symm
#align ennreal.of_real_coe_nnreal ENNReal.ofReal_coe_nNReal

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ≥0) = (0 : ℝ≥0∞) :=
  rfl
#align ennreal.coe_zero ENNReal.coe_zero

@[simp, norm_cast]
theorem coe_one : ↑(1 : ℝ≥0) = (1 : ℝ≥0∞) :=
  rfl
#align ennreal.coe_one ENNReal.coe_one

@[simp]
theorem toReal_nonneg {a : ℝ≥0∞} : 0 ≤ a.toReal := by simp [ENNReal.toReal]
#align ennreal.to_real_nonneg ENNReal.toReal_nonneg

@[simp]
theorem top_toNNReal : ∞.toNNReal = 0 :=
  rfl
#align ennreal.top_to_nnreal ENNReal.top_toNNReal

@[simp]
theorem top_toReal : ∞.toReal = 0 :=
  rfl
#align ennreal.top_to_real ENNReal.top_toReal

@[simp]
theorem one_toReal : (1 : ℝ≥0∞).toReal = 1 :=
  rfl
#align ennreal.one_to_real ENNReal.one_toReal

@[simp]
theorem one_toNNReal : (1 : ℝ≥0∞).toNNReal = 1 :=
  rfl
#align ennreal.one_to_nnreal ENNReal.one_toNNReal

@[simp]
theorem coe_toReal (r : ℝ≥0) : (r : ℝ≥0∞).toReal = r :=
  rfl
#align ennreal.coe_to_real ENNReal.coe_toReal

@[simp]
theorem zero_toNNReal : (0 : ℝ≥0∞).toNNReal = 0 :=
  rfl
#align ennreal.zero_to_nnreal ENNReal.zero_toNNReal

@[simp]
theorem zero_toReal : (0 : ℝ≥0∞).toReal = 0 :=
  rfl
#align ennreal.zero_to_real ENNReal.zero_toReal

@[simp]
theorem ofReal_zero : ENNReal.ofReal (0 : ℝ) = 0 := by simp [ENNReal.ofReal] <;> rfl
#align ennreal.of_real_zero ENNReal.ofReal_zero

@[simp]
theorem ofReal_one : ENNReal.ofReal (1 : ℝ) = (1 : ℝ≥0∞) := by simp [ENNReal.ofReal]
#align ennreal.of_real_one ENNReal.ofReal_one

theorem ofReal_toReal_le {a : ℝ≥0∞} : ENNReal.ofReal a.toReal ≤ a :=
  if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (ofReal_toReal ha)
#align ennreal.of_real_to_real_le ENNReal.ofReal_toReal_le

theorem forall_ennreal {p : ℝ≥0∞ → Prop} : (∀ a, p a) ↔ (∀ r : ℝ≥0, p r) ∧ p ∞ :=
  ⟨fun h => ⟨fun r => h _, h _⟩, fun ⟨h₁, h₂⟩ a =>
    match a with
    | some r => h₁ _
    | none => h₂⟩
#align ennreal.forall_ennreal ENNReal.forall_ennreal

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a «expr ≠ » ennreal.top()) -/
theorem forall_ne_top {p : ℝ≥0∞ → Prop} : (∀ (a) (_ : a ≠ ∞), p a) ↔ ∀ r : ℝ≥0, p r :=
  Option.ball_ne_none
#align ennreal.forall_ne_top ENNReal.forall_ne_top

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a «expr ≠ » ennreal.top()) -/
theorem exists_ne_top {p : ℝ≥0∞ → Prop} : (∃ (a : _)(_ : a ≠ ∞), p a) ↔ ∃ r : ℝ≥0, p r :=
  Option.bex_ne_none
#align ennreal.exists_ne_top ENNReal.exists_ne_top

theorem toNNReal_eq_zero_iff (x : ℝ≥0∞) : x.toNNReal = 0 ↔ x = 0 ∨ x = ∞ :=
  ⟨by
    cases x
    · simp [none_eq_top]
    · rintro (rfl : x = 0)
      exact Or.inl rfl, by rintro (h | h) <;> simp [h]⟩
#align ennreal.to_nnreal_eq_zero_iff ENNReal.toNNReal_eq_zero_iff

theorem toReal_eq_zero_iff (x : ℝ≥0∞) : x.toReal = 0 ↔ x = 0 ∨ x = ∞ := by
  simp [ENNReal.toReal, to_nnreal_eq_zero_iff]
#align ennreal.to_real_eq_zero_iff ENNReal.toReal_eq_zero_iff

theorem toNNReal_eq_one_iff (x : ℝ≥0∞) : x.toNNReal = 1 ↔ x = 1 := by
  refine' ⟨fun h => _, congr_arg _⟩
  cases x
  · exact False.elim (zero_ne_one <| ennreal.top_to_nnreal.symm.trans h)
  · exact congr_arg _ h
#align ennreal.to_nnreal_eq_one_iff ENNReal.toNNReal_eq_one_iff

theorem toReal_eq_one_iff (x : ℝ≥0∞) : x.toReal = 1 ↔ x = 1 := by
  rw [ENNReal.toReal, NNReal.coe_eq_one, ENNReal.toNNReal_eq_one_iff]
#align ennreal.to_real_eq_one_iff ENNReal.toReal_eq_one_iff

@[simp]
theorem coe_ne_top : (r : ℝ≥0∞) ≠ ∞ :=
  WithTop.coe_ne_top
#align ennreal.coe_ne_top ENNReal.coe_ne_top

@[simp]
theorem top_ne_coe : ∞ ≠ (r : ℝ≥0∞) :=
  WithTop.top_ne_coe
#align ennreal.top_ne_coe ENNReal.top_ne_coe

@[simp]
theorem ofReal_ne_top {r : ℝ} : ENNReal.ofReal r ≠ ∞ := by simp [ENNReal.ofReal]
#align ennreal.of_real_ne_top ENNReal.ofReal_ne_top

@[simp]
theorem ofReal_lt_top {r : ℝ} : ENNReal.ofReal r < ∞ :=
  lt_top_iff_ne_top.2 ofReal_ne_top
#align ennreal.of_real_lt_top ENNReal.ofReal_lt_top

@[simp]
theorem top_ne_ofReal {r : ℝ} : ∞ ≠ ENNReal.ofReal r := by simp [ENNReal.ofReal]
#align ennreal.top_ne_of_real ENNReal.top_ne_ofReal

@[simp]
theorem zero_ne_top : 0 ≠ ∞ :=
  coe_ne_top
#align ennreal.zero_ne_top ENNReal.zero_ne_top

@[simp]
theorem top_ne_zero : ∞ ≠ 0 :=
  top_ne_coe
#align ennreal.top_ne_zero ENNReal.top_ne_zero

@[simp]
theorem one_ne_top : 1 ≠ ∞ :=
  coe_ne_top
#align ennreal.one_ne_top ENNReal.one_ne_top

@[simp]
theorem top_ne_one : ∞ ≠ 1 :=
  top_ne_coe
#align ennreal.top_ne_one ENNReal.top_ne_one

@[simp, norm_cast]
theorem coe_eq_coe : (↑r : ℝ≥0∞) = ↑q ↔ r = q :=
  WithTop.coe_eq_coe
#align ennreal.coe_eq_coe ENNReal.coe_eq_coe

@[simp, norm_cast]
theorem coe_le_coe : (↑r : ℝ≥0∞) ≤ ↑q ↔ r ≤ q :=
  WithTop.coe_le_coe
#align ennreal.coe_le_coe ENNReal.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe : (↑r : ℝ≥0∞) < ↑q ↔ r < q :=
  WithTop.coe_lt_coe
#align ennreal.coe_lt_coe ENNReal.coe_lt_coe

theorem coe_mono : Monotone (coe : ℝ≥0 → ℝ≥0∞) := fun _ _ => coe_le_coe.2
#align ennreal.coe_mono ENNReal.coe_mono

@[simp, norm_cast]
theorem coe_eq_zero : (↑r : ℝ≥0∞) = 0 ↔ r = 0 :=
  coe_eq_coe
#align ennreal.coe_eq_zero ENNReal.coe_eq_zero

@[simp, norm_cast]
theorem zero_eq_coe : 0 = (↑r : ℝ≥0∞) ↔ 0 = r :=
  coe_eq_coe
#align ennreal.zero_eq_coe ENNReal.zero_eq_coe

@[simp, norm_cast]
theorem coe_eq_one : (↑r : ℝ≥0∞) = 1 ↔ r = 1 :=
  coe_eq_coe
#align ennreal.coe_eq_one ENNReal.coe_eq_one

@[simp, norm_cast]
theorem one_eq_coe : 1 = (↑r : ℝ≥0∞) ↔ 1 = r :=
  coe_eq_coe
#align ennreal.one_eq_coe ENNReal.one_eq_coe

@[simp]
theorem coe_nonneg : 0 ≤ (↑r : ℝ≥0∞) :=
  coe_le_coe.2 <| zero_le _
#align ennreal.coe_nonneg ENNReal.coe_nonneg

@[simp, norm_cast]
theorem coe_pos : 0 < (↑r : ℝ≥0∞) ↔ 0 < r :=
  coe_lt_coe
#align ennreal.coe_pos ENNReal.coe_pos

theorem coe_ne_zero : (r : ℝ≥0∞) ≠ 0 ↔ r ≠ 0 :=
  not_congr coe_eq_coe
#align ennreal.coe_ne_zero ENNReal.coe_ne_zero

@[simp, norm_cast]
theorem coe_add : ↑(r + p) = (r + p : ℝ≥0∞) :=
  WithTop.coe_add
#align ennreal.coe_add ENNReal.coe_add

@[simp, norm_cast]
theorem coe_mul : ↑(r * p) = (r * p : ℝ≥0∞) :=
  WithTop.coe_mul
#align ennreal.coe_mul ENNReal.coe_mul

@[simp, norm_cast]
theorem coe_bit0 : (↑(bit0 r) : ℝ≥0∞) = bit0 r :=
  coe_add
#align ennreal.coe_bit0 ENNReal.coe_bit0

@[simp, norm_cast]
theorem coe_bit1 : (↑(bit1 r) : ℝ≥0∞) = bit1 r := by simp [bit1]
#align ennreal.coe_bit1 ENNReal.coe_bit1

theorem coe_two : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_cast
#align ennreal.coe_two ENNReal.coe_two

theorem toNNReal_eq_toNNReal_iff (x y : ℝ≥0∞) :
    x.toNNReal = y.toNNReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 := by
  cases x
  ·
    simp only [@eq_comm ℝ≥0 _ y.to_nnreal, @eq_comm ℝ≥0∞ _ y, to_nnreal_eq_zero_iff, none_eq_top,
      top_to_nnreal, top_ne_zero, false_and_iff, eq_self_iff_true, true_and_iff, false_or_iff,
      or_comm' (y = ⊤)]
  · cases y <;> simp
#align ennreal.to_nnreal_eq_to_nnreal_iff ENNReal.toNNReal_eq_toNNReal_iff

theorem toReal_eq_toReal_iff (x y : ℝ≥0∞) :
    x.toReal = y.toReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 := by
  simp only [ENNReal.toReal, NNReal.coe_eq, to_nnreal_eq_to_nnreal_iff]
#align ennreal.to_real_eq_to_real_iff ENNReal.toReal_eq_toReal_iff

theorem toNNReal_eq_toNNReal_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x.toNNReal = y.toNNReal ↔ x = y := by
  simp only [ENNReal.toNNReal_eq_toNNReal_iff x y, hx, hy, and_false_iff, false_and_iff,
    or_false_iff]
#align ennreal.to_nnreal_eq_to_nnreal_iff' ENNReal.toNNReal_eq_toNNReal_iff'

theorem toReal_eq_toReal_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x.toReal = y.toReal ↔ x = y := by
  simp only [ENNReal.toReal, NNReal.coe_eq, to_nnreal_eq_to_nnreal_iff' hx hy]
#align ennreal.to_real_eq_to_real_iff' ENNReal.toReal_eq_toReal_iff'

protected theorem zero_lt_one : 0 < (1 : ℝ≥0∞) :=
  zero_lt_one
#align ennreal.zero_lt_one ENNReal.zero_lt_one

@[simp]
theorem one_lt_two : (1 : ℝ≥0∞) < 2 :=
  coe_one ▸ coe_two ▸ by exact_mod_cast (one_lt_two : 1 < 2)
#align ennreal.one_lt_two ENNReal.one_lt_two

@[simp]
theorem zero_lt_two : (0 : ℝ≥0∞) < 2 :=
  lt_trans zero_lt_one one_lt_two
#align ennreal.zero_lt_two ENNReal.zero_lt_two

theorem two_ne_zero : (2 : ℝ≥0∞) ≠ 0 :=
  (ne_of_lt zero_lt_two).symm
#align ennreal.two_ne_zero ENNReal.two_ne_zero

theorem two_ne_top : (2 : ℝ≥0∞) ≠ ∞ :=
  coe_two ▸ coe_ne_top
#align ennreal.two_ne_top ENNReal.two_ne_top

/-- `(1 : ℝ≥0∞) ≤ 1`, recorded as a `fact` for use with `Lp` spaces. -/
instance fact_one_le_one_ennreal : Fact ((1 : ℝ≥0∞) ≤ 1) :=
  ⟨le_rfl⟩
#align fact_one_le_one_ennreal fact_one_le_one_ennreal

/-- `(1 : ℝ≥0∞) ≤ 2`, recorded as a `fact` for use with `Lp` spaces. -/
instance fact_one_le_two_ennreal : Fact ((1 : ℝ≥0∞) ≤ 2) :=
  ⟨one_le_two⟩
#align fact_one_le_two_ennreal fact_one_le_two_ennreal

/-- `(1 : ℝ≥0∞) ≤ ∞`, recorded as a `fact` for use with `Lp` spaces. -/
instance fact_one_le_top_ennreal : Fact ((1 : ℝ≥0∞) ≤ ∞) :=
  ⟨le_top⟩
#align fact_one_le_top_ennreal fact_one_le_top_ennreal

/-- The set of numbers in `ℝ≥0∞` that are not equal to `∞` is equivalent to `ℝ≥0`. -/
def neTopEquivNNReal : { a | a ≠ ∞ } ≃ ℝ≥0
    where
  toFun x := ENNReal.toNNReal x
  invFun x := ⟨x, coe_ne_top⟩
  left_inv := fun ⟨x, hx⟩ => Subtype.eq <| coe_toNNReal hx
  right_inv x := toNNReal_coe
#align ennreal.ne_top_equiv_nnreal ENNReal.neTopEquivNNReal

theorem cinfi_ne_top [InfSet α] (f : ℝ≥0∞ → α) : (⨅ x : { x // x ≠ ∞ }, f x) = ⨅ x : ℝ≥0, f x :=
  Eq.symm <| neTopEquivNNReal.symm.Surjective.infᵢ_congr _ fun x => rfl
#align ennreal.cinfi_ne_top ENNReal.cinfi_ne_top

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ≠ » ennreal.top()) -/
theorem infᵢ_ne_top [CompleteLattice α] (f : ℝ≥0∞ → α) :
    (⨅ (x) (_ : x ≠ ∞), f x) = ⨅ x : ℝ≥0, f x := by rw [infᵢ_subtype', cinfi_ne_top]
#align ennreal.infi_ne_top ENNReal.infᵢ_ne_top

theorem csupr_ne_top [SupSet α] (f : ℝ≥0∞ → α) : (⨆ x : { x // x ≠ ∞ }, f x) = ⨆ x : ℝ≥0, f x :=
  @cinfi_ne_top αᵒᵈ _ _
#align ennreal.csupr_ne_top ENNReal.csupr_ne_top

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ≠ » ennreal.top()) -/
theorem supᵢ_ne_top [CompleteLattice α] (f : ℝ≥0∞ → α) :
    (⨆ (x) (_ : x ≠ ∞), f x) = ⨆ x : ℝ≥0, f x :=
  @infᵢ_ne_top αᵒᵈ _ _
#align ennreal.supr_ne_top ENNReal.supᵢ_ne_top

theorem infᵢ_ennreal {α : Type _} [CompleteLattice α] {f : ℝ≥0∞ → α} :
    (⨅ n, f n) = (⨅ n : ℝ≥0, f n) ⊓ f ∞ :=
  le_antisymm (le_inf (le_infᵢ fun i => infᵢ_le _ _) (infᵢ_le _ _))
    (le_infᵢ <| forall_ennreal.2 ⟨fun r => inf_le_of_left_le <| infᵢ_le _ _, inf_le_right⟩)
#align ennreal.infi_ennreal ENNReal.infᵢ_ennreal

theorem supᵢ_ennreal {α : Type _} [CompleteLattice α] {f : ℝ≥0∞ → α} :
    (⨆ n, f n) = (⨆ n : ℝ≥0, f n) ⊔ f ∞ :=
  @infᵢ_ennreal αᵒᵈ _ _
#align ennreal.supr_ennreal ENNReal.supᵢ_ennreal

@[simp]
theorem add_top : a + ∞ = ∞ :=
  add_top _
#align ennreal.add_top ENNReal.add_top

@[simp]
theorem top_add : ∞ + a = ∞ :=
  top_add _
#align ennreal.top_add ENNReal.top_add

/-- Coercion `ℝ≥0 → ℝ≥0∞` as a `ring_hom`. -/
def ofNNRealHom : ℝ≥0 →+* ℝ≥0∞ :=
  ⟨coe, coe_one, fun _ _ => coe_mul, coe_zero, fun _ _ => coe_add⟩
#align ennreal.of_nnreal_hom ENNReal.ofNNRealHom

@[simp]
theorem coe_ofNNRealHom : ⇑ofNNRealHom = coe :=
  rfl
#align ennreal.coe_of_nnreal_hom ENNReal.coe_ofNNRealHom

section Actions

/-- A `mul_action` over `ℝ≥0∞` restricts to a `mul_action` over `ℝ≥0`. -/
noncomputable instance {M : Type _} [MulAction ℝ≥0∞ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M ofNNRealHom.toMonoidHom

theorem smul_def {M : Type _} [MulAction ℝ≥0∞ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ≥0∞) • x :=
  rfl
#align ennreal.smul_def ENNReal.smul_def

instance {M N : Type _} [MulAction ℝ≥0∞ M] [MulAction ℝ≥0∞ N] [SMul M N] [IsScalarTower ℝ≥0∞ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := (smul_assoc (r : ℝ≥0∞) : _)

instance sMulCommClass_left {M N : Type _} [MulAction ℝ≥0∞ N] [SMul M N] [SMulCommClass ℝ≥0∞ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := (smul_comm (r : ℝ≥0∞) : _)
#align ennreal.smul_comm_class_left ENNReal.sMulCommClass_left

instance sMulCommClass_right {M N : Type _} [MulAction ℝ≥0∞ N] [SMul M N] [SMulCommClass M ℝ≥0∞ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := (smul_comm m (r : ℝ≥0∞) : _)
#align ennreal.smul_comm_class_right ENNReal.sMulCommClass_right

/-- A `distrib_mul_action` over `ℝ≥0∞` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
noncomputable instance {M : Type _} [AddMonoid M] [DistribMulAction ℝ≥0∞ M] :
    DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M ofNNRealHom.toMonoidHom

/-- A `module` over `ℝ≥0∞` restricts to a `module` over `ℝ≥0`. -/
noncomputable instance {M : Type _} [AddCommMonoid M] [Module ℝ≥0∞ M] : Module ℝ≥0 M :=
  Module.compHom M ofNNRealHom

/-- An `algebra` over `ℝ≥0∞` restricts to an `algebra` over `ℝ≥0`. -/
noncomputable instance {A : Type _} [Semiring A] [Algebra ℝ≥0∞ A] : Algebra ℝ≥0 A
    where
  smul := (· • ·)
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ≥0∞) x, smul_def]
  toRingHom := (algebraMap ℝ≥0∞ A).comp (ofNNRealHom : ℝ≥0 →+* ℝ≥0∞)

-- verify that the above produces instances we might care about
noncomputable example : Algebra ℝ≥0 ℝ≥0∞ :=
  inferInstance

noncomputable example : DistribMulAction ℝ≥0ˣ ℝ≥0∞ :=
  inferInstance

theorem coe_smul {R} (r : R) (s : ℝ≥0) [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0]
    [IsScalarTower R ℝ≥0 ℝ≥0∞] : (↑(r • s) : ℝ≥0∞) = r • ↑s := by
  rw [← smul_one_smul ℝ≥0 r (s : ℝ≥0∞), smul_def, smul_eq_mul, ← ENNReal.coe_mul, smul_mul_assoc,
    one_mul]
#align ennreal.coe_smul ENNReal.coe_smul

end Actions

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ≥0∞) = s.indicator (fun x => f x) a :=
  (ofNNRealHom : ℝ≥0 →+ ℝ≥0∞).map_indicator _ _ _
#align ennreal.coe_indicator ENNReal.coe_indicator

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : (↑(r ^ n) : ℝ≥0∞) = r ^ n :=
  ofNNRealHom.map_pow r n
#align ennreal.coe_pow ENNReal.coe_pow

@[simp]
theorem add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ :=
  WithTop.add_eq_top
#align ennreal.add_eq_top ENNReal.add_eq_top

@[simp]
theorem add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ :=
  WithTop.add_lt_top
#align ennreal.add_lt_top ENNReal.add_lt_top

theorem toNNReal_add {r₁ r₂ : ℝ≥0∞} (h₁ : r₁ ≠ ∞) (h₂ : r₂ ≠ ∞) :
    (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal := by
  lift r₁ to ℝ≥0 using h₁
  lift r₂ to ℝ≥0 using h₂
  rfl
#align ennreal.to_nnreal_add ENNReal.toNNReal_add

theorem not_lt_top {x : ℝ≥0∞} : ¬x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, Classical.not_not]
#align ennreal.not_lt_top ENNReal.not_lt_top

theorem add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ := by simpa only [lt_top_iff_ne_top] using add_lt_top
#align ennreal.add_ne_top ENNReal.add_ne_top

theorem mul_top : a * ∞ = if a = 0 then 0 else ∞ := by split_ifs; · simp [h];
  · exact WithTop.mul_top h
#align ennreal.mul_top ENNReal.mul_top

theorem top_mul : ∞ * a = if a = 0 then 0 else ∞ := by split_ifs; · simp [h];
  · exact WithTop.top_mul h
#align ennreal.top_mul ENNReal.top_mul

@[simp]
theorem top_mul_top : ∞ * ∞ = ∞ :=
  WithTop.top_mul_top
#align ennreal.top_mul_top ENNReal.top_mul_top

theorem top_pow {n : ℕ} (h : 0 < n) : ∞ ^ n = ∞ :=
  Nat.le_induction (pow_one _) (fun m hm hm' => by rw [pow_succ, hm', top_mul_top]) _
    (Nat.succ_le_of_lt h)
#align ennreal.top_pow ENNReal.top_pow

theorem mul_eq_top : a * b = ∞ ↔ a ≠ 0 ∧ b = ∞ ∨ a = ∞ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff
#align ennreal.mul_eq_top ENNReal.mul_eq_top

theorem mul_lt_top : a ≠ ∞ → b ≠ ∞ → a * b < ∞ :=
  WithTop.mul_lt_top
#align ennreal.mul_lt_top ENNReal.mul_lt_top

theorem mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ := by simpa only [lt_top_iff_ne_top] using mul_lt_top
#align ennreal.mul_ne_top ENNReal.mul_ne_top

theorem lt_top_of_mul_ne_top_left (h : a * b ≠ ∞) (hb : b ≠ 0) : a < ∞ :=
  lt_top_iff_ne_top.2 fun ha => h <| mul_eq_top.2 (Or.inr ⟨ha, hb⟩)
#align ennreal.lt_top_of_mul_ne_top_left ENNReal.lt_top_of_mul_ne_top_left

theorem lt_top_of_mul_ne_top_right (h : a * b ≠ ∞) (ha : a ≠ 0) : b < ∞ :=
  lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha
#align ennreal.lt_top_of_mul_ne_top_right ENNReal.lt_top_of_mul_ne_top_right

theorem mul_lt_top_iff {a b : ℝ≥0∞} : a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rw [← or_assoc', or_iff_not_imp_right, or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha.ne hb.ne, simp, simp]
#align ennreal.mul_lt_top_iff ENNReal.mul_lt_top_iff

theorem mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ := by
  rw [ENNReal.mul_lt_top_iff, and_self_iff, or_self_iff, or_iff_left_iff_imp]
  rintro rfl
  norm_num
#align ennreal.mul_self_lt_top_iff ENNReal.mul_self_lt_top_iff

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  CanonicallyOrderedCommSemiring.mul_pos
#align ennreal.mul_pos_iff ENNReal.mul_pos_iff

theorem mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
  mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩
#align ennreal.mul_pos ENNReal.mul_pos

@[simp]
theorem pow_eq_top_iff {n : ℕ} : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 := by
  induction' n with n ihn; · simp
  rw [pow_succ, mul_eq_top, ihn]
  fconstructor
  · rintro (⟨-, rfl, h0⟩ | ⟨rfl, h0⟩) <;> exact ⟨rfl, n.succ_ne_zero⟩
  · rintro ⟨rfl, -⟩
    exact Or.inr ⟨rfl, pow_ne_zero n top_ne_zero⟩
#align ennreal.pow_eq_top_iff ENNReal.pow_eq_top_iff

theorem pow_eq_top (n : ℕ) (h : a ^ n = ∞) : a = ∞ :=
  (pow_eq_top_iff.1 h).1
#align ennreal.pow_eq_top ENNReal.pow_eq_top

theorem pow_ne_top (h : a ≠ ∞) {n : ℕ} : a ^ n ≠ ∞ :=
  mt (pow_eq_top n) h
#align ennreal.pow_ne_top ENNReal.pow_ne_top

theorem pow_lt_top : a < ∞ → ∀ n : ℕ, a ^ n < ∞ := by
  simpa only [lt_top_iff_ne_top] using pow_ne_top
#align ennreal.pow_lt_top ENNReal.pow_lt_top

@[simp, norm_cast]
theorem coe_finset_sum {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a in s, f a) = (∑ a in s, f a : ℝ≥0∞) :=
  ofNNRealHom.map_sum f s
#align ennreal.coe_finset_sum ENNReal.coe_finset_sum

@[simp, norm_cast]
theorem coe_finset_prod {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a in s, f a) = (∏ a in s, f a : ℝ≥0∞) :=
  ofNNRealHom.map_prod f s
#align ennreal.coe_finset_prod ENNReal.coe_finset_prod

section Order

@[simp]
theorem bot_eq_zero : (⊥ : ℝ≥0∞) = 0 :=
  rfl
#align ennreal.bot_eq_zero ENNReal.bot_eq_zero

@[simp]
theorem coe_lt_top : coe r < ∞ :=
  WithTop.coe_lt_top r
#align ennreal.coe_lt_top ENNReal.coe_lt_top

@[simp]
theorem not_top_le_coe : ¬∞ ≤ ↑r :=
  WithTop.not_top_le_coe r
#align ennreal.not_top_le_coe ENNReal.not_top_le_coe

@[simp, norm_cast]
theorem one_le_coe_iff : (1 : ℝ≥0∞) ≤ ↑r ↔ 1 ≤ r :=
  coe_le_coe
#align ennreal.one_le_coe_iff ENNReal.one_le_coe_iff

@[simp, norm_cast]
theorem coe_le_one_iff : ↑r ≤ (1 : ℝ≥0∞) ↔ r ≤ 1 :=
  coe_le_coe
#align ennreal.coe_le_one_iff ENNReal.coe_le_one_iff

@[simp, norm_cast]
theorem coe_lt_one_iff : (↑p : ℝ≥0∞) < 1 ↔ p < 1 :=
  coe_lt_coe
#align ennreal.coe_lt_one_iff ENNReal.coe_lt_one_iff

@[simp, norm_cast]
theorem one_lt_coe_iff : 1 < (↑p : ℝ≥0∞) ↔ 1 < p :=
  coe_lt_coe
#align ennreal.one_lt_coe_iff ENNReal.one_lt_coe_iff

@[simp, norm_cast]
theorem coe_nat (n : ℕ) : ((n : ℝ≥0) : ℝ≥0∞) = n :=
  WithTop.coe_nat n
#align ennreal.coe_nat ENNReal.coe_nat

@[simp]
theorem ofReal_coe_nat (n : ℕ) : ENNReal.ofReal n = n := by simp [ENNReal.ofReal]
#align ennreal.of_real_coe_nat ENNReal.ofReal_coe_nat

@[simp]
theorem nat_ne_top (n : ℕ) : (n : ℝ≥0∞) ≠ ∞ :=
  WithTop.nat_ne_top n
#align ennreal.nat_ne_top ENNReal.nat_ne_top

@[simp]
theorem top_ne_nat (n : ℕ) : ∞ ≠ n :=
  WithTop.top_ne_nat n
#align ennreal.top_ne_nat ENNReal.top_ne_nat

@[simp]
theorem one_lt_top : 1 < ∞ :=
  coe_lt_top
#align ennreal.one_lt_top ENNReal.one_lt_top

@[simp, norm_cast]
theorem toNNReal_nat (n : ℕ) : (n : ℝ≥0∞).toNNReal = n := by
  conv_lhs => rw [← ENNReal.coe_nat n, ENNReal.toNNReal_coe]
#align ennreal.to_nnreal_nat ENNReal.toNNReal_nat

@[simp, norm_cast]
theorem toReal_nat (n : ℕ) : (n : ℝ≥0∞).toReal = n := by
  conv_lhs => rw [← ENNReal.ofReal_coe_nat n, ENNReal.toReal_ofReal (Nat.cast_nonneg _)]
#align ennreal.to_real_nat ENNReal.toReal_nat

theorem le_coe_iff : a ≤ ↑r ↔ ∃ p : ℝ≥0, a = p ∧ p ≤ r :=
  WithTop.le_coe_iff
#align ennreal.le_coe_iff ENNReal.le_coe_iff

theorem coe_le_iff : ↑r ≤ a ↔ ∀ p : ℝ≥0, a = p → r ≤ p :=
  WithTop.coe_le_iff
#align ennreal.coe_le_iff ENNReal.coe_le_iff

theorem lt_iff_exists_coe : a < b ↔ ∃ p : ℝ≥0, a = p ∧ ↑p < b :=
  WithTop.lt_iff_exists_coe
#align ennreal.lt_iff_exists_coe ENNReal.lt_iff_exists_coe

theorem toReal_le_coe_of_le_coe {a : ℝ≥0∞} {b : ℝ≥0} (h : a ≤ b) : a.toReal ≤ b :=
  show ↑a.toNNReal ≤ ↑b
    by
    have : ↑a.to_nnreal = a := ENNReal.coe_toNNReal (lt_of_le_of_lt h coe_lt_top).Ne
    rw [← this] at h
    exact_mod_cast h
#align ennreal.to_real_le_coe_of_le_coe ENNReal.toReal_le_coe_of_le_coe

@[simp, norm_cast]
theorem coe_finset_sup {s : Finset α} {f : α → ℝ≥0} : ↑(s.sup f) = s.sup fun x => (f x : ℝ≥0∞) :=
  Finset.comp_sup_eq_sup_comp_of_is_total _ coe_mono rfl
#align ennreal.coe_finset_sup ENNReal.coe_finset_sup

theorem pow_le_pow {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m := by
  cases a
  · cases m
    · rw [eq_bot_iff.mpr h]
      exact le_rfl
    · rw [none_eq_top, top_pow (Nat.succ_pos m)]
      exact le_top
  · rw [some_eq_coe, ← coe_pow, ← coe_pow, coe_le_coe]
    exact pow_le_pow (by simpa using ha) h
#align ennreal.pow_le_pow ENNReal.pow_le_pow

theorem one_le_pow_of_one_le (ha : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := by
  simpa using pow_le_pow ha (zero_le n)
#align ennreal.one_le_pow_of_one_le ENNReal.one_le_pow_of_one_le

@[simp]
theorem max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 := by
  simp only [nonpos_iff_eq_zero.symm, max_le_iff]
#align ennreal.max_eq_zero_iff ENNReal.max_eq_zero_iff

@[simp]
theorem max_zero_left : max 0 a = a :=
  max_eq_right (zero_le a)
#align ennreal.max_zero_left ENNReal.max_zero_left

@[simp]
theorem max_zero_right : max a 0 = a :=
  max_eq_left (zero_le a)
#align ennreal.max_zero_right ENNReal.max_zero_right

@[simp]
theorem sup_eq_max : a ⊔ b = max a b :=
  rfl
#align ennreal.sup_eq_max ENNReal.sup_eq_max

protected theorem pow_pos : 0 < a → ∀ n : ℕ, 0 < a ^ n :=
  CanonicallyOrderedCommSemiring.pow_pos
#align ennreal.pow_pos ENNReal.pow_pos

protected theorem pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a ^ n ≠ 0 := by
  simpa only [pos_iff_ne_zero] using ENNReal.pow_pos
#align ennreal.pow_ne_zero ENNReal.pow_ne_zero

@[simp]
theorem not_lt_zero : ¬a < 0 := by simp
#align ennreal.not_lt_zero ENNReal.not_lt_zero

protected theorem le_of_add_le_add_left : a ≠ ∞ → a + b ≤ a + c → b ≤ c :=
  WithTop.le_of_add_le_add_left
#align ennreal.le_of_add_le_add_left ENNReal.le_of_add_le_add_left

protected theorem le_of_add_le_add_right : a ≠ ∞ → b + a ≤ c + a → b ≤ c :=
  WithTop.le_of_add_le_add_right
#align ennreal.le_of_add_le_add_right ENNReal.le_of_add_le_add_right

protected theorem add_lt_add_left : a ≠ ∞ → b < c → a + b < a + c :=
  WithTop.add_lt_add_left
#align ennreal.add_lt_add_left ENNReal.add_lt_add_left

protected theorem add_lt_add_right : a ≠ ∞ → b < c → b + a < c + a :=
  WithTop.add_lt_add_right
#align ennreal.add_lt_add_right ENNReal.add_lt_add_right

protected theorem add_le_add_iff_left : a ≠ ∞ → (a + b ≤ a + c ↔ b ≤ c) :=
  WithTop.add_le_add_iff_left
#align ennreal.add_le_add_iff_left ENNReal.add_le_add_iff_left

protected theorem add_le_add_iff_right : a ≠ ∞ → (b + a ≤ c + a ↔ b ≤ c) :=
  WithTop.add_le_add_iff_right
#align ennreal.add_le_add_iff_right ENNReal.add_le_add_iff_right

protected theorem add_lt_add_iff_left : a ≠ ∞ → (a + b < a + c ↔ b < c) :=
  WithTop.add_lt_add_iff_left
#align ennreal.add_lt_add_iff_left ENNReal.add_lt_add_iff_left

protected theorem add_lt_add_iff_right : a ≠ ∞ → (b + a < c + a ↔ b < c) :=
  WithTop.add_lt_add_iff_right
#align ennreal.add_lt_add_iff_right ENNReal.add_lt_add_iff_right

protected theorem add_lt_add_of_le_of_lt : a ≠ ∞ → a ≤ b → c < d → a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt
#align ennreal.add_lt_add_of_le_of_lt ENNReal.add_lt_add_of_le_of_lt

protected theorem add_lt_add_of_lt_of_le : c ≠ ∞ → a < b → c ≤ d → a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le
#align ennreal.add_lt_add_of_lt_of_le ENNReal.add_lt_add_of_lt_of_le

instance contravariantClass_add_lt : ContravariantClass ℝ≥0∞ ℝ≥0∞ (· + ·) (· < ·) :=
  WithTop.contravariantClass_add_lt
#align ennreal.contravariant_class_add_lt ENNReal.contravariantClass_add_lt

theorem lt_add_right (ha : a ≠ ∞) (hb : b ≠ 0) : a < a + b := by
  rwa [← pos_iff_ne_zero, ← ENNReal.add_lt_add_iff_left ha, add_zero] at hb
#align ennreal.lt_add_right ENNReal.lt_add_right

theorem le_of_forall_pos_le_add : ∀ {a b : ℝ≥0∞}, (∀ ε : ℝ≥0, 0 < ε → b < ∞ → a ≤ b + ε) → a ≤ b
  | a, none, h => le_top
  | none, some a, h =>
    by
    have : ∞ ≤ ↑a + ↑(1 : ℝ≥0) := h 1 zero_lt_one coe_lt_top
    rw [← coe_add] at this <;> exact (not_top_le_coe this).elim
  | some a, some b, h => by
    simp only [none_eq_top, some_eq_coe, coe_add.symm, coe_le_coe, coe_lt_top, true_imp_iff] at
        * <;>
      exact NNReal.le_of_forall_pos_le_add h
#align ennreal.le_of_forall_pos_le_add ENNReal.le_of_forall_pos_le_add

theorem lt_iff_exists_rat_btwn :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ (Real.toNNReal q : ℝ≥0∞) < b :=
  ⟨fun h => by
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩
    rcases exists_between h with ⟨c, pc, cb⟩
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩
    rcases(NNReal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt_coe.2 qr) cb⟩, fun ⟨q, q0, qa, qb⟩ =>
    lt_trans qa qb⟩
#align ennreal.lt_iff_exists_rat_btwn ENNReal.lt_iff_exists_rat_btwn

theorem lt_iff_exists_real_btwn :
    a < b ↔ ∃ r : ℝ, 0 ≤ r ∧ a < ENNReal.ofReal r ∧ (ENNReal.ofReal r : ℝ≥0∞) < b :=
  ⟨fun h =>
    let ⟨q, q0, aq, qb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    ⟨q, Rat.cast_nonneg.2 q0, aq, qb⟩,
    fun ⟨q, q0, qa, qb⟩ => lt_trans qa qb⟩
#align ennreal.lt_iff_exists_real_btwn ENNReal.lt_iff_exists_real_btwn

theorem lt_iff_exists_nNReal_btwn : a < b ↔ ∃ r : ℝ≥0, a < r ∧ (r : ℝ≥0∞) < b :=
  WithTop.lt_iff_exists_coe_btwn
#align ennreal.lt_iff_exists_nnreal_btwn ENNReal.lt_iff_exists_nNReal_btwn

theorem lt_iff_exists_add_pos_lt : a < b ↔ ∃ r : ℝ≥0, 0 < r ∧ a + r < b := by
  refine' ⟨fun hab => _, fun ⟨r, rpos, hr⟩ => lt_of_le_of_lt le_self_add hr⟩
  cases a
  · simpa using hab
  rcases lt_iff_exists_real_btwn.1 hab with ⟨c, c_nonneg, ac, cb⟩
  let d : ℝ≥0 := ⟨c, c_nonneg⟩
  have ad : a < d := by
    rw [of_real_eq_coe_nnreal c_nonneg] at ac
    exact coe_lt_coe.1 ac
  refine' ⟨d - a, tsub_pos_iff_lt.2 ad, _⟩
  rw [some_eq_coe, ← coe_add]
  convert cb
  have : Real.toNNReal c = d :=
    by
    rw [← NNReal.coe_eq, Real.coe_toNNReal _ c_nonneg]
    rfl
  rw [add_comm, this]
  exact tsub_add_cancel_of_le ad.le
#align ennreal.lt_iff_exists_add_pos_lt ENNReal.lt_iff_exists_add_pos_lt

theorem coe_nat_lt_coe {n : ℕ} : (n : ℝ≥0∞) < r ↔ ↑n < r :=
  ENNReal.coe_nat n ▸ coe_lt_coe
#align ennreal.coe_nat_lt_coe ENNReal.coe_nat_lt_coe

theorem coe_lt_coe_nat {n : ℕ} : (r : ℝ≥0∞) < n ↔ r < n :=
  ENNReal.coe_nat n ▸ coe_lt_coe
#align ennreal.coe_lt_coe_nat ENNReal.coe_lt_coe_nat

@[simp, norm_cast]
theorem coe_nat_lt_coe_nat {m n : ℕ} : (m : ℝ≥0∞) < n ↔ m < n :=
  ENNReal.coe_nat n ▸ coe_nat_lt_coe.trans Nat.cast_lt
#align ennreal.coe_nat_lt_coe_nat ENNReal.coe_nat_lt_coe_nat

theorem coe_nat_mono : StrictMono (coe : ℕ → ℝ≥0∞) := fun _ _ => coe_nat_lt_coe_nat.2
#align ennreal.coe_nat_mono ENNReal.coe_nat_mono

@[simp, norm_cast]
theorem coe_nat_le_coe_nat {m n : ℕ} : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  coe_nat_mono.le_iff_le
#align ennreal.coe_nat_le_coe_nat ENNReal.coe_nat_le_coe_nat

instance : CharZero ℝ≥0∞ :=
  ⟨coe_nat_mono.Injective⟩

protected theorem exists_nat_gt {r : ℝ≥0∞} (h : r ≠ ∞) : ∃ n : ℕ, r < n := by
  lift r to ℝ≥0 using h
  rcases exists_nat_gt r with ⟨n, hn⟩
  exact ⟨n, coe_lt_coe_nat.2 hn⟩
#align ennreal.exists_nat_gt ENNReal.exists_nat_gt

@[simp]
theorem unionᵢ_Iio_coe_nat : (⋃ n : ℕ, Iio (n : ℝ≥0∞)) = {∞}ᶜ := by
  ext x
  rw [mem_Union]
  exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, ENNReal.exists_nat_gt⟩
#align ennreal.Union_Iio_coe_nat ENNReal.unionᵢ_Iio_coe_nat

@[simp]
theorem unionᵢ_Iic_coe_nat : (⋃ n : ℕ, Iic (n : ℝ≥0∞)) = {∞}ᶜ :=
  Subset.antisymm (unionᵢ_subset fun n x hx => ne_top_of_le_ne_top (nat_ne_top n) hx) <|
    unionᵢ_Iio_coe_nat ▸ unionᵢ_mono fun n => Iio_subset_Iic_self
#align ennreal.Union_Iic_coe_nat ENNReal.unionᵢ_Iic_coe_nat

@[simp]
theorem unionᵢ_Ioc_coe_nat : (⋃ n : ℕ, Ioc a n) = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iic, ← inter_Union, Union_Iic_coe_nat, diff_eq]
#align ennreal.Union_Ioc_coe_nat ENNReal.unionᵢ_Ioc_coe_nat

@[simp]
theorem unionᵢ_Ioo_coe_nat : (⋃ n : ℕ, Ioo a n) = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iio, ← inter_Union, Union_Iio_coe_nat, diff_eq]
#align ennreal.Union_Ioo_coe_nat ENNReal.unionᵢ_Ioo_coe_nat

@[simp]
theorem unionᵢ_Icc_coe_nat : (⋃ n : ℕ, Icc a n) = Ici a \ {∞} := by
  simp only [← Ici_inter_Iic, ← inter_Union, Union_Iic_coe_nat, diff_eq]
#align ennreal.Union_Icc_coe_nat ENNReal.unionᵢ_Icc_coe_nat

@[simp]
theorem unionᵢ_Ico_coe_nat : (⋃ n : ℕ, Ico a n) = Ici a \ {∞} := by
  simp only [← Ici_inter_Iio, ← inter_Union, Union_Iio_coe_nat, diff_eq]
#align ennreal.Union_Ico_coe_nat ENNReal.unionᵢ_Ico_coe_nat

@[simp]
theorem interᵢ_Ici_coe_nat : (⋂ n : ℕ, Ici (n : ℝ≥0∞)) = {∞} := by
  simp only [← compl_Iio, ← compl_Union, Union_Iio_coe_nat, compl_compl]
#align ennreal.Inter_Ici_coe_nat ENNReal.interᵢ_Ici_coe_nat

@[simp]
theorem interᵢ_Ioi_coe_nat : (⋂ n : ℕ, Ioi (n : ℝ≥0∞)) = {∞} := by
  simp only [← compl_Iic, ← compl_Union, Union_Iic_coe_nat, compl_compl]
#align ennreal.Inter_Ioi_coe_nat ENNReal.interᵢ_Ioi_coe_nat

theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d := by
  lift a to ℝ≥0 using ne_top_of_lt ac
  lift b to ℝ≥0 using ne_top_of_lt bd
  cases c; · simp; cases d; · simp
  simp only [← coe_add, some_eq_coe, coe_lt_coe] at *
  exact add_lt_add ac bd
#align ennreal.add_lt_add ENNReal.add_lt_add

@[norm_cast]
theorem coe_min : ((min r p : ℝ≥0) : ℝ≥0∞) = min r p :=
  coe_mono.map_min
#align ennreal.coe_min ENNReal.coe_min

@[norm_cast]
theorem coe_max : ((max r p : ℝ≥0) : ℝ≥0∞) = max r p :=
  coe_mono.map_max
#align ennreal.coe_max ENNReal.coe_max

theorem le_of_top_imp_top_of_toNNReal_le {a b : ℝ≥0∞} (h : a = ⊤ → b = ⊤)
    (h_nnreal : a ≠ ⊤ → b ≠ ⊤ → a.toNNReal ≤ b.toNNReal) : a ≤ b := by
  by_cases ha : a = ⊤
  · rw [h ha]
    exact le_top
  by_cases hb : b = ⊤
  · rw [hb]
    exact le_top
  rw [← coe_to_nnreal hb, ← coe_to_nnreal ha, coe_le_coe]
  exact h_nnreal ha hb
#align ennreal.le_of_top_imp_top_of_to_nnreal_le ENNReal.le_of_top_imp_top_of_toNNReal_le

end Order

section CompleteLattice

theorem coe_supₛ {s : Set ℝ≥0} : BddAbove s → (↑(supₛ s) : ℝ≥0∞) = ⨆ a ∈ s, ↑a :=
  WithTop.coe_supₛ
#align ennreal.coe_Sup ENNReal.coe_supₛ

theorem coe_infₛ {s : Set ℝ≥0} : s.Nonempty → (↑(infₛ s) : ℝ≥0∞) = ⨅ a ∈ s, ↑a :=
  WithTop.coe_infₛ
#align ennreal.coe_Inf ENNReal.coe_infₛ

@[simp]
theorem top_mem_upperBounds {s : Set ℝ≥0∞} : ∞ ∈ upperBounds s := fun x hx => le_top
#align ennreal.top_mem_upper_bounds ENNReal.top_mem_upperBounds

theorem coe_mem_upperBounds {s : Set ℝ≥0} :
    ↑r ∈ upperBounds ((coe : ℝ≥0 → ℝ≥0∞) '' s) ↔ r ∈ upperBounds s := by
  simp (config := { contextual := true }) [upperBounds, ball_image_iff, -mem_image, *]
#align ennreal.coe_mem_upper_bounds ENNReal.coe_mem_upperBounds

end CompleteLattice

section Mul

@[mono]
theorem mul_le_mul : a ≤ b → c ≤ d → a * c ≤ b * d :=
  mul_le_mul'
#align ennreal.mul_le_mul ENNReal.mul_le_mul

@[mono]
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := by
  rcases lt_iff_exists_nnreal_btwn.1 ac with ⟨a', aa', a'c⟩
  lift a to ℝ≥0 using ne_top_of_lt aa'
  rcases lt_iff_exists_nnreal_btwn.1 bd with ⟨b', bb', b'd⟩
  lift b to ℝ≥0 using ne_top_of_lt bb'
  norm_cast  at *
  calc
    ↑(a * b) < ↑(a' * b') :=
      coe_lt_coe.2 (mul_lt_mul' aa'.le bb' (zero_le _) ((zero_le a).trans_lt aa'))
    _ = ↑a' * ↑b' := coe_mul
    _ ≤ c * d := mul_le_mul a'c.le b'd.le
    
#align ennreal.mul_lt_mul ENNReal.mul_lt_mul

theorem mul_left_mono : Monotone ((· * ·) a) := fun b c => mul_le_mul le_rfl
#align ennreal.mul_left_mono ENNReal.mul_left_mono

theorem mul_right_mono : Monotone fun x => x * a := fun b c h => mul_le_mul h le_rfl
#align ennreal.mul_right_mono ENNReal.mul_right_mono

theorem pow_strictMono {n : ℕ} (hn : n ≠ 0) : StrictMono fun x : ℝ≥0∞ => x ^ n := by
  intro x y hxy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  induction' n with n IH
  · simp only [hxy, pow_one]
  · simp only [pow_succ _ n.succ, mul_lt_mul hxy (IH (Nat.succ_pos _).ne')]
#align ennreal.pow_strict_mono ENNReal.pow_strictMono

theorem max_mul : max a b * c = max (a * c) (b * c) :=
  mul_right_mono.map_max
#align ennreal.max_mul ENNReal.max_mul

theorem mul_max : a * max b c = max (a * b) (a * c) :=
  mul_left_mono.map_max
#align ennreal.mul_max ENNReal.mul_max

theorem mul_left_strictMono (h0 : a ≠ 0) (hinf : a ≠ ∞) : StrictMono ((· * ·) a) := by
  lift a to ℝ≥0 using hinf
  rw [coe_ne_zero] at h0
  intro x y h
  contrapose! h
  simpa only [← mul_assoc, ← coe_mul, inv_mul_cancel h0, coe_one, one_mul] using
    mul_le_mul' (le_refl ↑a⁻¹) h
#align ennreal.mul_left_strictMono ENNReal.mul_left_strictMono

theorem mul_eq_mul_left (h₀ : a ≠ 0) (hinf : a ≠ ∞) : a * b = a * c ↔ b = c :=
  (mul_left_strictMono h₀ hinf).Injective.eq_iff
#align ennreal.mul_eq_mul_left ENNReal.mul_eq_mul_left

theorem mul_eq_mul_right : c ≠ 0 → c ≠ ∞ → (a * c = b * c ↔ a = b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_eq_mul_left
#align ennreal.mul_eq_mul_right ENNReal.mul_eq_mul_right

theorem mul_le_mul_left (h₀ : a ≠ 0) (hinf : a ≠ ∞) : a * b ≤ a * c ↔ b ≤ c :=
  (mul_left_strictMono h₀ hinf).le_iff_le
#align ennreal.mul_le_mul_left ENNReal.mul_le_mul_left

theorem mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left
#align ennreal.mul_le_mul_right ENNReal.mul_le_mul_right

theorem mul_lt_mul_left (h₀ : a ≠ 0) (hinf : a ≠ ∞) : a * b < a * c ↔ b < c :=
  (mul_left_strictMono h₀ hinf).lt_iff_lt
#align ennreal.mul_lt_mul_left ENNReal.mul_lt_mul_left

theorem mul_lt_mul_right : c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left
#align ennreal.mul_lt_mul_right ENNReal.mul_lt_mul_right

end Mul

section Cancel

/-- An element `a` is `add_le_cancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
theorem addLECancellable_iff_ne {a : ℝ≥0∞} : AddLECancellable a ↔ a ≠ ∞ := by
  constructor
  · rintro h rfl
    refine' zero_lt_one.not_le (h _)
    simp
  · rintro h b c hbc
    apply ENNReal.le_of_add_le_add_left h hbc
#align ennreal.add_le_cancellable_iff_ne ENNReal.addLECancellable_iff_ne

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_ne {a : ℝ≥0∞} (h : a ≠ ∞) : AddLECancellable a :=
  addLECancellable_iff_ne.mpr h
#align ennreal.cancel_of_ne ENNReal.cancel_of_ne

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_lt {a : ℝ≥0∞} (h : a < ∞) : AddLECancellable a :=
  cancel_of_ne h.Ne
#align ennreal.cancel_of_lt ENNReal.cancel_of_lt

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_lt' {a b : ℝ≥0∞} (h : a < b) : AddLECancellable a :=
  cancel_of_ne h.ne_top
#align ennreal.cancel_of_lt' ENNReal.cancel_of_lt'

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_coe {a : ℝ≥0} : AddLECancellable (a : ℝ≥0∞) :=
  cancel_of_ne coe_ne_top
#align ennreal.cancel_coe ENNReal.cancel_coe

theorem add_right_inj (h : a ≠ ∞) : a + b = a + c ↔ b = c :=
  (cancel_of_ne h).inj
#align ennreal.add_right_inj ENNReal.add_right_inj

theorem add_left_inj (h : a ≠ ∞) : b + a = c + a ↔ b = c :=
  (cancel_of_ne h).inj_left
#align ennreal.add_left_inj ENNReal.add_left_inj

end Cancel

section Sub

theorem sub_eq_infₛ {a b : ℝ≥0∞} : a - b = infₛ { d | a ≤ d + b } :=
  le_antisymm (le_infₛ fun c => tsub_le_iff_right.mpr) <| infₛ_le le_tsub_add
#align ennreal.sub_eq_Inf ENNReal.sub_eq_infₛ

/-- This is a special case of `with_top.coe_sub` in the `ennreal` namespace -/
theorem coe_sub : (↑(r - p) : ℝ≥0∞) = ↑r - ↑p :=
  WithTop.coe_sub
#align ennreal.coe_sub ENNReal.coe_sub

/-- This is a special case of `with_top.top_sub_coe` in the `ennreal` namespace -/
theorem top_sub_coe : ∞ - ↑r = ∞ :=
  WithTop.top_sub_coe
#align ennreal.top_sub_coe ENNReal.top_sub_coe

/-- This is a special case of `with_top.sub_top` in the `ennreal` namespace -/
theorem sub_top : a - ∞ = 0 :=
  WithTop.sub_top
#align ennreal.sub_top ENNReal.sub_top

theorem sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ := by
  cases a <;> cases b <;> simp [← WithTop.coe_sub]
#align ennreal.sub_eq_top_iff ENNReal.sub_eq_top_iff

theorem sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ :=
  mt sub_eq_top_iff.mp <| mt And.left ha
#align ennreal.sub_ne_top ENNReal.sub_ne_top

@[simp, norm_cast]
theorem nat_cast_sub (m n : ℕ) : ↑(m - n) = (m - n : ℝ≥0∞) := by
  rw [← coe_nat, Nat.cast_tsub, coe_sub, coe_nat, coe_nat]
#align ennreal.nat_cast_sub ENNReal.nat_cast_sub

protected theorem sub_eq_of_eq_add (hb : b ≠ ∞) : a = c + b → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add
#align ennreal.sub_eq_of_eq_add ENNReal.sub_eq_of_eq_add

protected theorem eq_sub_of_add_eq (hc : c ≠ ∞) : a + c = b → a = b - c :=
  (cancel_of_ne hc).eq_tsub_of_add_eq
#align ennreal.eq_sub_of_add_eq ENNReal.eq_sub_of_add_eq

protected theorem sub_eq_of_eq_add_rev (hb : b ≠ ∞) : a = b + c → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add_rev
#align ennreal.sub_eq_of_eq_add_rev ENNReal.sub_eq_of_eq_add_rev

theorem sub_eq_of_add_eq (hb : b ≠ ∞) (hc : a + b = c) : c - b = a :=
  ENNReal.sub_eq_of_eq_add hb hc.symm
#align ennreal.sub_eq_of_add_eq ENNReal.sub_eq_of_add_eq

@[simp]
protected theorem add_sub_cancel_left (ha : a ≠ ∞) : a + b - a = b :=
  (cancel_of_ne ha).add_tsub_cancel_left
#align ennreal.add_sub_cancel_left ENNReal.add_sub_cancel_left

@[simp]
protected theorem add_sub_cancel_right (hb : b ≠ ∞) : a + b - b = a :=
  (cancel_of_ne hb).add_tsub_cancel_right
#align ennreal.add_sub_cancel_right ENNReal.add_sub_cancel_right

protected theorem lt_add_of_sub_lt_left (h : a ≠ ∞ ∨ b ≠ ∞) : a - b < c → a < b + c := by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (Classical.not_not.2 rfl)
  · exact (cancel_of_ne hb).lt_add_of_tsub_lt_left
#align ennreal.lt_add_of_sub_lt_left ENNReal.lt_add_of_sub_lt_left

protected theorem lt_add_of_sub_lt_right (h : a ≠ ∞ ∨ c ≠ ∞) : a - c < b → a < b + c :=
  add_comm c b ▸ ENNReal.lt_add_of_sub_lt_left h
#align ennreal.lt_add_of_sub_lt_right ENNReal.lt_add_of_sub_lt_right

theorem le_sub_of_add_le_left (ha : a ≠ ∞) : a + b ≤ c → b ≤ c - a :=
  (cancel_of_ne ha).le_tsub_of_add_le_left
#align ennreal.le_sub_of_add_le_left ENNReal.le_sub_of_add_le_left

theorem le_sub_of_add_le_right (hb : b ≠ ∞) : a + b ≤ c → a ≤ c - b :=
  (cancel_of_ne hb).le_tsub_of_add_le_right
#align ennreal.le_sub_of_add_le_right ENNReal.le_sub_of_add_le_right

protected theorem sub_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : a - c < b :=
  ((cancel_of_lt' <| hac.trans_lt h).tsub_lt_iff_right hac).mpr h
#align ennreal.sub_lt_of_lt_add ENNReal.sub_lt_of_lt_add

protected theorem sub_lt_iff_lt_right (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < c + b :=
  (cancel_of_ne hb).tsub_lt_iff_right hab
#align ennreal.sub_lt_iff_lt_right ENNReal.sub_lt_iff_lt_right

protected theorem sub_lt_self (ha : a ≠ ∞) (ha₀ : a ≠ 0) (hb : b ≠ 0) : a - b < a :=
  (cancel_of_ne ha).tsub_lt_self (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)
#align ennreal.sub_lt_self ENNReal.sub_lt_self

protected theorem sub_lt_self_iff (ha : a ≠ ∞) : a - b < a ↔ 0 < a ∧ 0 < b :=
  (cancel_of_ne ha).tsub_lt_self_iff
#align ennreal.sub_lt_self_iff ENNReal.sub_lt_self_iff

theorem sub_lt_of_sub_lt (h₂ : c ≤ a) (h₃ : a ≠ ∞ ∨ b ≠ ∞) (h₁ : a - b < c) : a - c < b :=
  ENNReal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ENNReal.lt_add_of_sub_lt_right h₃ h₁)
#align ennreal.sub_lt_of_sub_lt ENNReal.sub_lt_of_sub_lt

theorem sub_sub_cancel (h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b :=
  (cancel_of_ne <| sub_ne_top h).tsub_tsub_cancel_of_le h2
#align ennreal.sub_sub_cancel ENNReal.sub_sub_cancel

theorem sub_right_inj {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≤ a) (hc : c ≤ a) :
    a - b = a - c ↔ b = c :=
  (cancel_of_ne ha).tsub_right_inj (cancel_of_ne <| ne_top_of_le_ne_top ha hb)
    (cancel_of_ne <| ne_top_of_le_ne_top ha hc) hb hc
#align ennreal.sub_right_inj ENNReal.sub_right_inj

theorem sub_mul (h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c := by
  cases' le_or_lt a b with hab hab; · simp [hab, mul_right_mono hab]
  rcases eq_or_lt_of_le (zero_le b) with (rfl | hb); · simp
  exact (cancel_of_ne <| mul_ne_top hab.ne_top (h hb hab)).tsub_mul
#align ennreal.sub_mul ENNReal.sub_mul

theorem mul_sub (h : 0 < c → c < b → a ≠ ∞) : a * (b - c) = a * b - a * c := by
  simp only [mul_comm a]
  exact sub_mul h
#align ennreal.mul_sub ENNReal.mul_sub

end Sub

section Sum

open Finset

/-- A product of finite numbers is still finite -/
theorem prod_lt_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : (∏ a in s, f a) < ∞ :=
  WithTop.prod_lt_top h
#align ennreal.prod_lt_top ENNReal.prod_lt_top

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : (∑ a in s, f a) < ∞ :=
  WithTop.sum_lt_top h
#align ennreal.sum_lt_top ENNReal.sum_lt_top

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top_iff {s : Finset α} {f : α → ℝ≥0∞} : (∑ a in s, f a) < ∞ ↔ ∀ a ∈ s, f a < ∞ :=
  WithTop.sum_lt_top_iff
#align ennreal.sum_lt_top_iff ENNReal.sum_lt_top_iff

/-- A sum of numbers is infinite iff one of them is infinite -/
theorem sum_eq_top_iff {s : Finset α} {f : α → ℝ≥0∞} : (∑ x in s, f x) = ∞ ↔ ∃ a ∈ s, f a = ∞ :=
  WithTop.sum_eq_top_iff
#align ennreal.sum_eq_top_iff ENNReal.sum_eq_top_iff

theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℝ≥0∞} (h : (∑ x in s, f x) ≠ ∞) {a : α}
    (ha : a ∈ s) : f a < ∞ :=
  sum_lt_top_iff.1 h.lt_top a ha
#align ennreal.lt_top_of_sum_ne_top ENNReal.lt_top_of_sum_ne_top

/-- seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity -/
theorem toNNReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toNNReal (∑ a in s, f a) = ∑ a in s, ENNReal.toNNReal (f a) := by
  rw [← coe_eq_coe, coe_to_nnreal, coe_finset_sum, sum_congr rfl]
  · intro x hx
    exact (coe_to_nnreal (hf x hx)).symm
  · exact (sum_lt_top hf).Ne
#align ennreal.to_nnreal_sum ENNReal.toNNReal_sum

/-- seeing `ℝ≥0∞` as `real` does not change their sum, unless one of the `ℝ≥0∞` is infinity -/
theorem toReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.toReal (f a) := by
  rw [ENNReal.toReal, to_nnreal_sum hf, NNReal.coe_sum]
  rfl
#align ennreal.to_real_sum ENNReal.toReal_sum

theorem ofReal_sum_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∑ i in s, f i) = ∑ i in s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_sum, coe_eq_coe]
  exact Real.toNNReal_sum_of_nonneg hf
#align ennreal.of_real_sum_of_nonneg ENNReal.ofReal_sum_of_nonneg

theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hlt : ∀ i ∈ s, f i < g i) : (∑ i in s, f i) < ∑ i in s, g i := by
  induction' hs using Finset.Nonempty.cons_induction with a a s as hs IH
  · simp [Hlt _ (Finset.mem_singleton_self _)]
  · simp only [as, Finset.sum_cons, not_false_iff]
    exact
      ENNReal.add_lt_add (Hlt _ (Finset.mem_cons_self _ _))
        (IH fun i hi => Hlt _ (Finset.mem_cons.2 <| Or.inr hi))
#align ennreal.sum_lt_sum_of_nonempty ENNReal.sum_lt_sum_of_nonempty

theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hle : (∑ i in s, f i) ≤ ∑ i in s, g i) : ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle
  apply ENNReal.sum_lt_sum_of_nonempty hs Hle
#align ennreal.exists_le_of_sum_le ENNReal.exists_le_of_sum_le

end Sum

section Interval

variable {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set ℝ≥0∞}

protected theorem Ico_eq_Iio : Ico 0 y = Iio y :=
  Ico_bot
#align ennreal.Ico_eq_Iio ENNReal.Ico_eq_Iio

theorem mem_Iio_self_add : x ≠ ∞ → ε ≠ 0 → x ∈ Iio (x + ε) := fun xt ε0 => lt_add_right xt ε0
#align ennreal.mem_Iio_self_add ENNReal.mem_Iio_self_add

theorem mem_Ioo_self_sub_add : x ≠ ∞ → x ≠ 0 → ε₁ ≠ 0 → ε₂ ≠ 0 → x ∈ Ioo (x - ε₁) (x + ε₂) :=
  fun xt x0 ε0 ε0' => ⟨ENNReal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩
#align ennreal.mem_Ioo_self_sub_add ENNReal.mem_Ioo_self_sub_add

end Interval

section Bit

@[mono]
theorem bit0_strictMono : StrictMono (bit0 : ℝ≥0∞ → ℝ≥0∞) := fun a b h => add_lt_add h h
#align ennreal.bit0_strict_mono ENNReal.bit0_strictMono

theorem bit0_injective : Function.Injective (bit0 : ℝ≥0∞ → ℝ≥0∞) :=
  bit0_strictMono.Injective
#align ennreal.bit0_injective ENNReal.bit0_injective

@[simp]
theorem bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b :=
  bit0_strictMono.lt_iff_lt
#align ennreal.bit0_lt_bit0 ENNReal.bit0_lt_bit0

@[simp, mono]
theorem bit0_le_bit0 : bit0 a ≤ bit0 b ↔ a ≤ b :=
  bit0_strictMono.le_iff_le
#align ennreal.bit0_le_bit0 ENNReal.bit0_le_bit0

@[simp]
theorem bit0_inj : bit0 a = bit0 b ↔ a = b :=
  bit0_injective.eq_iff
#align ennreal.bit0_inj ENNReal.bit0_inj

@[simp]
theorem bit0_eq_zero_iff : bit0 a = 0 ↔ a = 0 :=
  bit0_injective.eq_iff' bit0_zero
#align ennreal.bit0_eq_zero_iff ENNReal.bit0_eq_zero_iff

@[simp]
theorem bit0_top : bit0 ∞ = ∞ :=
  add_top
#align ennreal.bit0_top ENNReal.bit0_top

@[simp]
theorem bit0_eq_top_iff : bit0 a = ∞ ↔ a = ∞ :=
  bit0_injective.eq_iff' bit0_top
#align ennreal.bit0_eq_top_iff ENNReal.bit0_eq_top_iff

@[mono]
theorem bit1_strictMono : StrictMono (bit1 : ℝ≥0∞ → ℝ≥0∞) := fun a b h =>
  ENNReal.add_lt_add_right one_ne_top (bit0_strictMono h)
#align ennreal.bit1_strict_mono ENNReal.bit1_strictMono

theorem bit1_injective : Function.Injective (bit1 : ℝ≥0∞ → ℝ≥0∞) :=
  bit1_strictMono.Injective
#align ennreal.bit1_injective ENNReal.bit1_injective

@[simp]
theorem bit1_lt_bit1 : bit1 a < bit1 b ↔ a < b :=
  bit1_strictMono.lt_iff_lt
#align ennreal.bit1_lt_bit1 ENNReal.bit1_lt_bit1

@[simp, mono]
theorem bit1_le_bit1 : bit1 a ≤ bit1 b ↔ a ≤ b :=
  bit1_strictMono.le_iff_le
#align ennreal.bit1_le_bit1 ENNReal.bit1_le_bit1

@[simp]
theorem bit1_inj : bit1 a = bit1 b ↔ a = b :=
  bit1_injective.eq_iff
#align ennreal.bit1_inj ENNReal.bit1_inj

@[simp]
theorem bit1_ne_zero : bit1 a ≠ 0 := by simp [bit1]
#align ennreal.bit1_ne_zero ENNReal.bit1_ne_zero

@[simp]
theorem bit1_top : bit1 ∞ = ∞ := by rw [bit1, bit0_top, top_add]
#align ennreal.bit1_top ENNReal.bit1_top

@[simp]
theorem bit1_eq_top_iff : bit1 a = ∞ ↔ a = ∞ :=
  bit1_injective.eq_iff' bit1_top
#align ennreal.bit1_eq_top_iff ENNReal.bit1_eq_top_iff

@[simp]
theorem bit1_eq_one_iff : bit1 a = 1 ↔ a = 0 :=
  bit1_injective.eq_iff' bit1_zero
#align ennreal.bit1_eq_one_iff ENNReal.bit1_eq_one_iff

end Bit

section Inv

noncomputable section

instance : Inv ℝ≥0∞ :=
  ⟨fun a => infₛ { b | 1 ≤ a * b }⟩

instance : DivInvMonoid ℝ≥0∞ :=
  { (inferInstance : Monoid ℝ≥0∞) with inv := Inv.inv }

theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]
#align ennreal.div_eq_inv_mul ENNReal.div_eq_inv_mul

@[simp]
theorem inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
  show infₛ { b : ℝ≥0∞ | 1 ≤ 0 * b } = ∞ by simp <;> rfl
#align ennreal.inv_zero ENNReal.inv_zero

@[simp]
theorem inv_top : ∞⁻¹ = 0 :=
  bot_unique <|
    le_of_forall_le_of_dense fun a (h : a > 0) => infₛ_le <| by simp [*, ne_of_gt h, top_mul]
#align ennreal.inv_top ENNReal.inv_top

theorem coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
  le_infₛ fun b (hb : 1 ≤ ↑r * b) =>
    coe_le_iff.2 <| by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb
#align ennreal.coe_inv_le ENNReal.coe_inv_le

@[simp, norm_cast]
theorem coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ :=
  coe_inv_le.antisymm <| infₛ_le <| le_of_eq <| by rw [← coe_mul, mul_inv_cancel hr, coe_one]
#align ennreal.coe_inv ENNReal.coe_inv

@[norm_cast]
theorem coe_inv_two : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by rw [coe_inv _root_.two_ne_zero, coe_two]
#align ennreal.coe_inv_two ENNReal.coe_inv_two

@[simp, norm_cast]
theorem coe_div (hr : r ≠ 0) : (↑(p / r) : ℝ≥0∞) = p / r := by
  rw [div_eq_mul_inv, div_eq_mul_inv, coe_mul, coe_inv hr]
#align ennreal.coe_div ENNReal.coe_div

theorem div_zero (h : a ≠ 0) : a / 0 = ∞ := by simp [div_eq_mul_inv, h]
#align ennreal.div_zero ENNReal.div_zero

instance : DivInvOneMonoid ℝ≥0∞ :=
  { ENNReal.divInvMonoid with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_eq_coe.2 inv_one }

protected theorem inv_pow {n : ℕ} : (a ^ n)⁻¹ = a⁻¹ ^ n := by
  cases n; · simp only [pow_zero, inv_one]
  induction a using WithTop.recTopCoe; · simp [top_pow n.succ_pos]
  rcases eq_or_ne a 0 with (rfl | ha); · simp [top_pow, zero_pow, n.succ_pos]
  rw [← coe_inv ha, ← coe_pow, ← coe_inv (pow_ne_zero _ ha), ← inv_pow, coe_pow]
#align ennreal.inv_pow ENNReal.inv_pow

protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
  lift a to ℝ≥0 using ht
  norm_cast  at *
  exact mul_inv_cancel h0
#align ennreal.mul_inv_cancel ENNReal.mul_inv_cancel

protected theorem inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
  mul_comm a a⁻¹ ▸ ENNReal.mul_inv_cancel h0 ht
#align ennreal.inv_mul_cancel ENNReal.inv_mul_cancel

protected theorem div_mul_cancel (h0 : a ≠ 0) (hI : a ≠ ∞) : b / a * a = b := by
  rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel h0 hI, mul_one]
#align ennreal.div_mul_cancel ENNReal.div_mul_cancel

protected theorem mul_div_cancel' (h0 : a ≠ 0) (hI : a ≠ ∞) : a * (b / a) = b := by
  rw [mul_comm, ENNReal.div_mul_cancel h0 hI]
#align ennreal.mul_div_cancel' ENNReal.mul_div_cancel'

instance : InvolutiveInv ℝ≥0∞ where
  inv := Inv.inv
  inv_inv a := by
    by_cases a = 0 <;> cases a <;> simp_all [none_eq_top, some_eq_coe, -coe_inv, (coe_inv _).symm]

@[simp]
theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 :=
  inv_zero ▸ inv_inj
#align ennreal.inv_eq_top ENNReal.inv_eq_top

theorem inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp
#align ennreal.inv_ne_top ENNReal.inv_ne_top

@[simp]
theorem inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]
#align ennreal.inv_lt_top ENNReal.inv_lt_top

theorem div_lt_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y < ∞ :=
  mul_lt_top h1 (inv_ne_top.mpr h2)
#align ennreal.div_lt_top ENNReal.div_lt_top

@[simp]
protected theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj
#align ennreal.inv_eq_zero ENNReal.inv_eq_zero

protected theorem inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp
#align ennreal.inv_ne_zero ENNReal.inv_ne_zero

protected theorem mul_inv {a b : ℝ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction b using WithTop.recTopCoe
  · replace ha : a ≠ 0 := ha.neg_resolve_right rfl
    simp [ha]
  induction a using WithTop.recTopCoe
  · replace hb : b ≠ 0 := coe_ne_zero.1 (hb.neg_resolve_left rfl)
    simp [hb]
  by_cases h'a : a = 0
  ·
    simp only [h'a, WithTop.top_mul, ENNReal.inv_zero, ENNReal.coe_ne_top, zero_mul, Ne.def,
      not_false_iff, ENNReal.coe_zero, ENNReal.inv_eq_zero]
  by_cases h'b : b = 0
  ·
    simp only [h'b, ENNReal.inv_zero, ENNReal.coe_ne_top, WithTop.mul_top, Ne.def, not_false_iff,
      mul_zero, ENNReal.coe_zero, ENNReal.inv_eq_zero]
  rw [← ENNReal.coe_mul, ← ENNReal.coe_inv, ← ENNReal.coe_inv h'a, ← ENNReal.coe_inv h'b, ←
    ENNReal.coe_mul, mul_inv_rev, mul_comm]
  simp [h'a, h'b]
#align ennreal.mul_inv ENNReal.mul_inv

protected theorem mul_div_mul_left (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    c * a / (c * b) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc) (Or.inl hc'), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hc', one_mul]
#align ennreal.mul_div_mul_left ENNReal.mul_div_mul_left

protected theorem mul_div_mul_right (a b : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    a * c / (b * c) = a / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hc') (Or.inr hc), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hc', mul_one]
#align ennreal.mul_div_mul_right ENNReal.mul_div_mul_right

protected theorem sub_div (h : 0 < b → b < a → c ≠ 0) : (a - b) / c = a / c - b / c := by
  simp_rw [div_eq_mul_inv]
  exact ENNReal.sub_mul (by simpa using h)
#align ennreal.sub_div ENNReal.sub_div

@[simp]
protected theorem inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
  pos_iff_ne_zero.trans ENNReal.inv_ne_zero
#align ennreal.inv_pos ENNReal.inv_pos

theorem inv_strictAnti : StrictAnti (Inv.inv : ℝ≥0∞ → ℝ≥0∞) := by
  intro a b h
  lift a to ℝ≥0 using h.ne_top
  induction b using WithTop.recTopCoe; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv h.ne_bot, ← coe_inv ha, coe_lt_coe]
  exact NNReal.inv_lt_inv ha h
#align ennreal.inv_strict_anti ENNReal.inv_strictAnti

@[simp]
protected theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strictAnti.lt_iff_lt
#align ennreal.inv_lt_inv ENNReal.inv_lt_inv

theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹
#align ennreal.inv_lt_iff_inv_lt ENNReal.inv_lt_iff_inv_lt

theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b
#align ennreal.lt_inv_iff_lt_inv ENNReal.lt_inv_iff_lt_inv

-- higher than le_inv_iff_mul_le
@[simp]
protected theorem inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  inv_strictAnti.le_iff_le
#align ennreal.inv_le_inv ENNReal.inv_le_inv

theorem inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹
#align ennreal.inv_le_iff_inv_le ENNReal.inv_le_iff_inv_le

theorem le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b
#align ennreal.le_inv_iff_le_inv ENNReal.le_inv_iff_le_inv

@[simp]
protected theorem inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a := by rw [inv_le_iff_inv_le, inv_one]
#align ennreal.inv_le_one ENNReal.inv_le_one

protected theorem one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 := by rw [le_inv_iff_le_inv, inv_one]
#align ennreal.one_le_inv ENNReal.one_le_inv

@[simp]
protected theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, inv_one]
#align ennreal.inv_lt_one ENNReal.inv_lt_one

@[simp]
protected theorem one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, inv_one]
#align ennreal.one_lt_inv ENNReal.one_lt_inv

/-- The inverse map `λ x, x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `order_dual` -/
@[simps apply]
def OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ
    where
  map_rel_iff' a b := ENNReal.inv_le_inv
  toEquiv := (Equiv.inv ℝ≥0∞).trans OrderDual.toDual
#align order_iso.inv_ennreal OrderIso.invENNReal

@[simp]
theorem OrderIso.invENNReal_symm_apply : OrderIso.invENNReal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl
#align order_iso.inv_ennreal_symm_apply OrderIso.invENNReal_symm_apply

protected theorem pow_le_pow_of_le_one {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n := by
  rw [← inv_inv a, ← ENNReal.inv_pow, ← @ENNReal.inv_pow a⁻¹, ENNReal.inv_le_inv]
  exact pow_le_pow (ENNReal.one_le_inv.2 ha) h
#align ennreal.pow_le_pow_of_le_one ENNReal.pow_le_pow_of_le_one

@[simp]
theorem div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]
#align ennreal.div_top ENNReal.div_top

@[simp]
theorem top_div_coe : ∞ / p = ∞ := by simp [div_eq_mul_inv, top_mul]
#align ennreal.top_div_coe ENNReal.top_div_coe

theorem top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ := by
  lift a to ℝ≥0 using h
  exact top_div_coe
#align ennreal.top_div_of_ne_top ENNReal.top_div_of_ne_top

theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ :=
  top_div_of_ne_top h.Ne
#align ennreal.top_div_of_lt_top ENNReal.top_div_of_lt_top

theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by
  by_cases a = ∞ <;> simp [top_div_of_ne_top, *]
#align ennreal.top_div ENNReal.top_div

@[simp]
protected theorem zero_div : 0 / a = 0 :=
  zero_mul a⁻¹
#align ennreal.zero_div ENNReal.zero_div

theorem div_eq_top : a / b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞ := by
  simp [div_eq_mul_inv, ENNReal.mul_eq_top]
#align ennreal.div_eq_top ENNReal.div_eq_top

protected theorem le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
    a ≤ c / b ↔ a * b ≤ c := by
  induction b using WithTop.recTopCoe
  · lift c to ℝ≥0 using ht.neg_resolve_left rfl
    rw [div_top, nonpos_iff_eq_zero, mul_top]
    rcases eq_or_ne a 0 with (rfl | ha) <;> simp [*]
  rcases eq_or_ne b 0 with (rfl | hb)
  · have hc : c ≠ 0 := h0.neg_resolve_left rfl
    simp [div_zero hc]
  · rw [← coe_ne_zero] at hb
    rw [← ENNReal.mul_le_mul_right hb coe_ne_top, ENNReal.div_mul_cancel hb coe_ne_top]
#align ennreal.le_div_iff_mul_le ENNReal.le_div_iff_mul_le

protected theorem div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    a / b ≤ c ↔ a ≤ c * b := by
  suffices a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹ by simpa [div_eq_mul_inv]
  refine' (ENNReal.le_div_iff_mul_le _ _).symm <;> simpa
#align ennreal.div_le_iff_le_mul ENNReal.div_le_iff_le_mul

protected theorem lt_div_iff_mul_lt (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    c < a / b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ENNReal.div_le_iff_le_mul hb0 hbt)
#align ennreal.lt_div_iff_mul_lt ENNReal.lt_div_iff_mul_lt

theorem div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b := by
  by_cases h0 : c = 0
  · have : a = 0 := by simpa [h0] using h
    simp [*]
  by_cases hinf : c = ∞; · simp [hinf]
  exact (ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h
#align ennreal.div_le_of_le_mul ENNReal.div_le_of_le_mul

theorem div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h
#align ennreal.div_le_of_le_mul' ENNReal.div_le_of_le_mul'

theorem mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b := by
  rw [← inv_inv c]
  exact div_le_of_le_mul h
#align ennreal.mul_le_of_le_div ENNReal.mul_le_of_le_div

theorem mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
  mul_comm a c ▸ mul_le_of_le_div h
#align ennreal.mul_le_of_le_div' ENNReal.mul_le_of_le_div'

protected theorem div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : c / b < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le <| ENNReal.le_div_iff_mul_le h0 ht
#align ennreal.div_lt_iff ENNReal.div_lt_iff

theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact ENNReal.div_le_of_le_mul h
#align ennreal.mul_lt_of_lt_div ENNReal.mul_lt_of_lt_div

theorem mul_lt_of_lt_div' (h : a < b / c) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h
#align ennreal.mul_lt_of_lt_div' ENNReal.mul_lt_of_lt_div'

theorem inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← one_div, ENNReal.div_le_iff_le_mul, mul_comm]
  exacts[or_not_of_imp h₁, not_or_of_imp h₂]
#align ennreal.inv_le_iff_le_mul ENNReal.inv_le_iff_le_mul

@[simp]
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  rw [← one_div, ENNReal.le_div_iff_mul_le] <;>
    · right
      simp
#align ennreal.le_inv_iff_mul_le ENNReal.le_inv_iff_mul_le

protected theorem div_le_div (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ ENNReal.mul_le_mul hab (ENNReal.inv_le_inv.mpr hdc)
#align ennreal.div_le_div ENNReal.div_le_div

protected theorem div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) : c / b ≤ c / a :=
  ENNReal.div_le_div le_rfl h
#align ennreal.div_le_div_left ENNReal.div_le_div_left

protected theorem div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c :=
  ENNReal.div_le_div h le_rfl
#align ennreal.div_le_div_right ENNReal.div_le_div_right

protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a, ← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ← mul_assoc, h,
    one_mul]
  rintro rfl
  simpa [left_ne_zero_of_mul_eq_one h] using h
#align ennreal.eq_inv_of_mul_eq_one_left ENNReal.eq_inv_of_mul_eq_one_left

theorem mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  rw [← @ENNReal.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, ENNReal.mul_inv_cancel hr₀ hr₁,
    one_mul]
#align ennreal.mul_le_iff_le_inv ENNReal.mul_le_iff_le_inv

theorem le_of_forall_nNReal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y := by
  refine' le_of_forall_ge_of_dense fun r hr => _
  lift r to ℝ≥0 using ne_top_of_lt hr
  exact h r hr
#align ennreal.le_of_forall_nnreal_lt ENNReal.le_of_forall_nNReal_lt

theorem le_of_forall_pos_nNReal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
  le_of_forall_nNReal_lt fun r hr =>
    (zero_le r).eq_or_lt.elim (fun h => h ▸ zero_le _) fun h0 => h r h0 hr
#align ennreal.le_of_forall_pos_nnreal_lt ENNReal.le_of_forall_pos_nNReal_lt

theorem eq_top_of_forall_nNReal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
  top_unique <| le_of_forall_nNReal_lt fun r hr => h r
#align ennreal.eq_top_of_forall_nnreal_le ENNReal.eq_top_of_forall_nNReal_le

protected theorem add_div : (a + b) / c = a / c + b / c :=
  right_distrib a b c⁻¹
#align ennreal.add_div ENNReal.add_div

protected theorem div_add_div_same {a b c : ℝ≥0∞} : a / c + b / c = (a + b) / c :=
  ENNReal.add_div.symm
#align ennreal.div_add_div_same ENNReal.div_add_div_same

protected theorem div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
  ENNReal.mul_inv_cancel h0 hI
#align ennreal.div_self ENNReal.div_self

theorem mul_div_le : a * (b / a) ≤ b :=
  mul_le_of_le_div' le_rfl
#align ennreal.mul_div_le ENNReal.mul_div_le

-- TODO: add this lemma for an `is_unit` in any `division_monoid`
theorem eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) : b = c / a ↔ a * b = c :=
  ⟨fun h => by rw [h, ENNReal.mul_div_cancel' ha ha'], fun h => by
    rw [← h, mul_div_assoc, ENNReal.mul_div_cancel' ha ha']⟩
#align ennreal.eq_div_iff ENNReal.eq_div_iff

protected theorem div_eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞) :
    c / b = d / a ↔ a * c = b * d := by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb', mul_div_assoc, eq_comm]
#align ennreal.div_eq_div_iff ENNReal.div_eq_div_iff

theorem div_eq_one_iff {a b : ℝ≥0∞} (hb₀ : b ≠ 0) (hb₁ : b ≠ ∞) : a / b = 1 ↔ a = b :=
  ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNReal.div_self hb₀ hb₁⟩
#align ennreal.div_eq_one_iff ENNReal.div_eq_one_iff

theorem inv_two_add_inv_two : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, ← div_eq_mul_inv, ENNReal.div_self two_ne_zero two_ne_top]
#align ennreal.inv_two_add_inv_two ENNReal.inv_two_add_inv_two

theorem inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 := by
  rw [show (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹ by ring, ← div_eq_mul_inv, ENNReal.div_self] <;> simp
#align ennreal.inv_three_add_inv_three ENNReal.inv_three_add_inv_three

@[simp]
protected theorem add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]
#align ennreal.add_halves ENNReal.add_halves

@[simp]
theorem add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]
#align ennreal.add_thirds ENNReal.add_thirds

@[simp]
theorem div_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by simp [div_eq_mul_inv]
#align ennreal.div_zero_iff ENNReal.div_zero_iff

@[simp]
theorem div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ := by simp [pos_iff_ne_zero, not_or]
#align ennreal.div_pos_iff ENNReal.div_pos_iff

protected theorem half_pos (h : a ≠ 0) : 0 < a / 2 := by simp [h]
#align ennreal.half_pos ENNReal.half_pos

protected theorem one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 :=
  ENNReal.inv_lt_one.2 <| one_lt_two
#align ennreal.one_half_lt_one ENNReal.one_half_lt_one

protected theorem half_lt_self (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a := by
  lift a to ℝ≥0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two, ← coe_div, coe_lt_coe]
  exacts[NNReal.half_lt_self hz, two_ne_zero' _]
#align ennreal.half_lt_self ENNReal.half_lt_self

protected theorem half_le_self : a / 2 ≤ a :=
  le_add_self.trans_eq <| ENNReal.add_halves _
#align ennreal.half_le_self ENNReal.half_le_self

theorem sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 := by
  lift a to ℝ≥0 using h
  exact sub_eq_of_add_eq (mul_ne_top coe_ne_top <| by simp) (ENNReal.add_halves a)
#align ennreal.sub_half ENNReal.sub_half

@[simp]
theorem one_sub_inv_two : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
  simpa only [div_eq_mul_inv, one_mul] using sub_half one_ne_top
#align ennreal.one_sub_inv_two ENNReal.one_sub_inv_two

/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `set.Iic (1 : ℝ≥0∞)`. -/
@[simps apply_coe]
def orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) := by
  refine'
    StrictMono.orderIsoOfRightInverse (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
      (fun x y hxy => _) (fun x => (x⁻¹ - 1)⁻¹) fun x => Subtype.ext _
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : ℝ≥0∞) ≤ x⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, Subtype.coe_mk, tsub_add_cancel_of_le this]
#align ennreal.order_iso_Iic_one_birational ENNReal.orderIsoIicOneBirational

@[simp]
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : ℝ≥0∞)) :
    orderIsoIicOneBirational.symm x = (x⁻¹ - 1)⁻¹ :=
  rfl
#align ennreal.order_iso_Iic_one_birational_symm_apply ENNReal.orderIsoIicOneBirational_symm_apply

/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps apply_coe]
def orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
      invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 <| coe_toNNReal_le_self.trans x.2⟩
      left_inv := fun x => Subtype.ext <| toNNReal_coe
      right_inv := fun x => Subtype.ext <| coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun x y => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_coe, coe_le_coe, Subtype.coe_le_coe] }
#align ennreal.order_iso_Iic_coe ENNReal.orderIsoIicCoe

@[simp]
theorem orderIsoIicCoe_symm_apply_coe (a : ℝ≥0) (b : Iic a) :
    ((orderIsoIicCoe a).symm b : ℝ≥0∞) = b :=
  rfl
#align ennreal.order_iso_Iic_coe_symm_apply_coe ENNReal.orderIsoIicCoe_symm_apply_coe

/-- An order isomorphism between the extended nonnegative real numbers and the unit interval. -/
def orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1 :=
  orderIsoIicOneBirational.trans <| (orderIsoIicCoe 1).trans <| (NNReal.orderIsoIccZeroCoe 1).symm
#align ennreal.order_iso_unit_interval_birational ENNReal.orderIsoUnitIntervalBirational

@[simp]
theorem orderIsoUnitIntervalBirational_apply_coe (x : ℝ≥0∞) :
    (orderIsoUnitIntervalBirational x : ℝ) = (x⁻¹ + 1)⁻¹.toReal :=
  rfl
#align ennreal.order_iso_unit_interval_birational_apply_coe ENNReal.orderIsoUnitIntervalBirational_apply_coe

theorem exists_inv_nat_lt {a : ℝ≥0∞} (h : a ≠ 0) : ∃ n : ℕ, (n : ℝ≥0∞)⁻¹ < a :=
  inv_inv a ▸ by simp only [ENNReal.inv_lt_inv, ENNReal.exists_nat_gt (inv_ne_top.2 h)]
#align ennreal.exists_inv_nat_lt ENNReal.exists_inv_nat_lt

theorem exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n > 0, b < (n : ℕ) * a := by
  have : b / a ≠ ∞ := mul_ne_top hb (inv_ne_top.2 ha)
  refine' (ENNReal.exists_nat_gt this).imp fun n hn => _
  have : ↑0 < (n : ℝ≥0∞) := lt_of_le_of_lt (by simp) hn
  refine' ⟨coe_nat_lt_coe_nat.1 this, _⟩
  rwa [← ENNReal.div_lt_iff (Or.inl ha) (Or.inr hb)]
#align ennreal.exists_nat_pos_mul_gt ENNReal.exists_nat_pos_mul_gt

theorem exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n : ℕ, b < n * a :=
  (exists_nat_pos_mul_gt ha hb).imp fun n => Exists.snd
#align ennreal.exists_nat_mul_gt ENNReal.exists_nat_mul_gt

theorem exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b :=
  by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  have : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 npos.lt.ne'
  use n, npos
  rwa [← one_mul b, ← ENNReal.inv_mul_cancel this (nat_ne_top n), mul_assoc,
    mul_lt_mul_left (ENNReal.inv_ne_zero.2 <| nat_ne_top _) (inv_ne_top.2 this)]
#align ennreal.exists_nat_pos_inv_mul_lt ENNReal.exists_nat_pos_inv_mul_lt

theorem exists_nNReal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ↑(n : ℝ≥0) * a < b := by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : ℝ≥0)⁻¹
  simp [*, npos.ne', zero_lt_one]
#align ennreal.exists_nnreal_pos_mul_lt ENNReal.exists_nNReal_pos_mul_lt

theorem exists_inv_two_pow_lt (ha : a ≠ 0) : ∃ n : ℕ, 2⁻¹ ^ n < a := by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine' ⟨n, lt_trans _ hn⟩
  rw [← ENNReal.inv_pow, ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow
#align ennreal.exists_inv_two_pow_lt ENNReal.exists_inv_two_pow_lt

@[simp, norm_cast]
theorem coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r ^ n) : ℝ≥0∞) = r ^ n := by
  cases n
  · simp only [Int.ofNat_eq_coe, coe_pow, zpow_ofNat]
  · have : r ^ n.succ ≠ 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]
#align ennreal.coe_zpow ENNReal.coe_zpow

theorem zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n := by
  cases n
  · exact ENNReal.pow_pos ha.bot_lt n
  ·
    simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne.def, not_false_iff, ENNReal.inv_pos,
      false_and_iff]
#align ennreal.zpow_pos ENNReal.zpow_pos

theorem zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ := by
  cases n
  · exact ENNReal.pow_lt_top h'a.lt_top _
  · simp only [ENNReal.pow_pos ha.bot_lt (n + 1), zpow_negSucc, inv_lt_top]
#align ennreal.zpow_lt_top ENNReal.zpow_lt_top

theorem exists_mem_Ico_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne.def, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1) :=
    by
    refine' NNReal.exists_mem_Ico_zpow _ (one_lt_coe_iff.1 hy)
    simpa only [Ne.def, coe_eq_zero] using hx
  refine' ⟨n, _, _⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
#align ennreal.exists_mem_Ico_zpow ENNReal.exists_mem_Ico_zpow

theorem exists_mem_Ioc_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne.def, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1) :=
    by
    refine' NNReal.exists_mem_Ioc_zpow _ (one_lt_coe_iff.1 hy)
    simpa only [Ne.def, coe_eq_zero] using hx
  refine' ⟨n, _, _⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
#align ennreal.exists_mem_Ioc_zpow ENNReal.exists_mem_Ioc_zpow

theorem Ioo_zero_top_eq_unionᵢ_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
    Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ n : ℤ, Ico (y ^ n) (y ^ (n + 1)) := by
  ext x
  simp only [mem_Union, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _
#align ennreal.Ioo_zero_top_eq_Union_Ico_zpow ENNReal.Ioo_zero_top_eq_unionᵢ_Ico_zpow

theorem zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  induction' a with a a <;> induction' b with b b
  · simp only [Int.ofNat_eq_coe, zpow_ofNat]
    exact pow_le_pow hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.ofNat_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_coe, zpow_ofNat]
    refine' (ENNReal.inv_le_one.2 _).trans _ <;> exact ENNReal.one_le_pow_of_one_le hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_le_pow hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.ofNat_add, Int.ofNat_one, Int.negSucc_eq] using
      h
#align ennreal.zpow_le_of_le ENNReal.zpow_le_of_le

theorem monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : Monotone ((· ^ ·) x : ℤ → ℝ≥0∞) := fun a b h =>
  zpow_le_of_le hx h
#align ennreal.monotone_zpow ENNReal.monotone_zpow

protected theorem zpow_add {x : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) :
    x ^ (m + n) = x ^ m * x ^ n := by
  lift x to ℝ≥0 using h'x
  replace hx : x ≠ 0; · simpa only [Ne.def, coe_eq_zero] using hx
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]
#align ennreal.zpow_add ENNReal.zpow_add

end Inv

section Real

theorem toReal_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  rfl
#align ennreal.to_real_add ENNReal.toReal_add

theorem toReal_sub_of_le {a b : ℝ≥0∞} (h : b ≤ a) (ha : a ≠ ∞) :
    (a - b).toReal = a.toReal - b.toReal := by
  lift b to ℝ≥0 using ne_top_of_le_ne_top ha h
  lift a to ℝ≥0 using ha
  simp only [← ENNReal.coe_sub, ENNReal.coe_toReal, NNReal.coe_sub (ennreal.coe_le_coe.mp h)]
#align ennreal.to_real_sub_of_le ENNReal.toReal_sub_of_le

theorem le_toReal_sub {a b : ℝ≥0∞} (hb : b ≠ ∞) : a.toReal - b.toReal ≤ (a - b).toReal := by
  lift b to ℝ≥0 using hb
  induction a using WithTop.recTopCoe
  · simp
  · simp only [← coe_sub, NNReal.sub_def, Real.coe_toNNReal', coe_to_real]
    exact le_max_left _ _
#align ennreal.le_to_real_sub ENNReal.le_toReal_sub

theorem toReal_add_le : (a + b).toReal ≤ a.toReal + b.toReal :=
  if ha : a = ∞ then by simp only [ha, top_add, top_to_real, zero_add, to_real_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, top_to_real, add_zero, to_real_nonneg]
    else le_of_eq (toReal_add ha hb)
#align ennreal.to_real_add_le ENNReal.toReal_add_le

theorem ofReal_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ENNReal.ofReal, ← coe_add, coe_eq_coe,
    Real.toNNReal_add hp hq]
#align ennreal.of_real_add ENNReal.ofReal_add

theorem ofReal_add_le {p q : ℝ} : ENNReal.ofReal (p + q) ≤ ENNReal.ofReal p + ENNReal.ofReal q :=
  coe_le_coe.2 Real.toNNReal_add_le
#align ennreal.of_real_add_le ENNReal.ofReal_add_le

@[simp]
theorem toReal_le_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal ≤ b.toReal ↔ a ≤ b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast
#align ennreal.to_real_le_to_real ENNReal.toReal_le_toReal

theorem toReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  (toReal_le_toReal (h.trans_lt (lt_top_iff_ne_top.2 hb)).Ne hb).2 h
#align ennreal.to_real_mono ENNReal.toReal_mono

@[simp]
theorem toReal_lt_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal < b.toReal ↔ a < b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast
#align ennreal.to_real_lt_to_real ENNReal.toReal_lt_toReal

theorem toReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toReal < b.toReal :=
  (toReal_lt_toReal (h.trans (lt_top_iff_ne_top.2 hb)).Ne hb).2 h
#align ennreal.to_real_strict_mono ENNReal.toReal_strict_mono

theorem toNNReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toNNReal ≤ b.toNNReal := by
  simpa [← ENNReal.coe_le_coe, hb, (h.trans_lt hb.lt_top).Ne]
#align ennreal.to_nnreal_mono ENNReal.toNNReal_mono

@[simp]
theorem toNNReal_le_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal ≤ b.toNNReal ↔ a ≤ b :=
  ⟨fun h => by rwa [← coe_to_nnreal ha, ← coe_to_nnreal hb, coe_le_coe], toNNReal_mono hb⟩
#align ennreal.to_nnreal_le_to_nnreal ENNReal.toNNReal_le_toNNReal

theorem toNNReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toNNReal < b.toNNReal := by
  simpa [← ENNReal.coe_lt_coe, hb, (h.trans hb.lt_top).Ne]
#align ennreal.to_nnreal_strict_mono ENNReal.toNNReal_strict_mono

@[simp]
theorem toNNReal_lt_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal < b.toNNReal ↔ a < b :=
  ⟨fun h => by rwa [← coe_to_nnreal ha, ← coe_to_nnreal hb, coe_lt_coe], toNNReal_strict_mono hb⟩
#align ennreal.to_nnreal_lt_to_nnreal ENNReal.toNNReal_lt_toNNReal

theorem toReal_max (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNReal.toReal (max a b) = max (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim
    (fun h => by simp only [h, (ENNReal.toReal_le_toReal hr hp).2 h, max_eq_right]) fun h => by
    simp only [h, (ENNReal.toReal_le_toReal hp hr).2 h, max_eq_left]
#align ennreal.to_real_max ENNReal.toReal_max

theorem toReal_min {a b : ℝ≥0∞} (hr : a ≠ ∞) (hp : b ≠ ∞) :
    ENNReal.toReal (min a b) = min (ENNReal.toReal a) (ENNReal.toReal b) :=
  (le_total a b).elim (fun h => by simp only [h, (ENNReal.toReal_le_toReal hr hp).2 h, min_eq_left])
    fun h => by simp only [h, (ENNReal.toReal_le_toReal hp hr).2 h, min_eq_right]
#align ennreal.to_real_min ENNReal.toReal_min

theorem toReal_sup {a b : ℝ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊔ b).toReal = a.toReal ⊔ b.toReal :=
  toReal_max
#align ennreal.to_real_sup ENNReal.toReal_sup

theorem toReal_inf {a b : ℝ≥0∞} : a ≠ ∞ → b ≠ ∞ → (a ⊓ b).toReal = a.toReal ⊓ b.toReal :=
  toReal_min
#align ennreal.to_real_inf ENNReal.toReal_inf

theorem toNNReal_pos_iff : 0 < a.toNNReal ↔ 0 < a ∧ a < ∞ := by
  induction a using WithTop.recTopCoe <;> simp
#align ennreal.to_nnreal_pos_iff ENNReal.toNNReal_pos_iff

theorem toNNReal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toNNReal :=
  toNNReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩
#align ennreal.to_nnreal_pos ENNReal.toNNReal_pos

theorem toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞ :=
  NNReal.coe_pos.trans toNNReal_pos_iff
#align ennreal.to_real_pos_iff ENNReal.toReal_pos_iff

theorem toReal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toReal :=
  toReal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩
#align ennreal.to_real_pos ENNReal.toReal_pos

theorem ofReal_le_ofReal {p q : ℝ} (h : p ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q := by
  simp [ENNReal.ofReal, Real.toNNReal_le_toNNReal h]
#align ennreal.of_real_le_of_real ENNReal.ofReal_le_ofReal

theorem ofReal_le_of_le_toReal {a : ℝ} {b : ℝ≥0∞} (h : a ≤ ENNReal.toReal b) :
    ENNReal.ofReal a ≤ b :=
  (ofReal_le_ofReal h).trans ofReal_toReal_le
#align ennreal.of_real_le_of_le_to_real ENNReal.ofReal_le_of_le_toReal

@[simp]
theorem ofReal_le_ofReal_iff {p q : ℝ} (h : 0 ≤ q) : ENNReal.ofReal p ≤ ENNReal.ofReal q ↔ p ≤ q :=
  by rw [ENNReal.ofReal, ENNReal.ofReal, coe_le_coe, Real.toNNReal_le_toNNReal_iff h]
#align ennreal.of_real_le_of_real_iff ENNReal.ofReal_le_ofReal_iff

@[simp]
theorem ofReal_eq_ofReal_iff {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_eq_coe, Real.toNNReal_eq_toNNReal_iff hp hq]
#align ennreal.of_real_eq_of_real_iff ENNReal.ofReal_eq_ofReal_iff

@[simp]
theorem ofReal_lt_ofReal_iff {p q : ℝ} (h : 0 < q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q :=
  by rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff h]
#align ennreal.of_real_lt_of_real_iff ENNReal.ofReal_lt_ofReal_iff

theorem ofReal_lt_ofReal_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q := by
  rw [ENNReal.ofReal, ENNReal.ofReal, coe_lt_coe, Real.toNNReal_lt_toNNReal_iff_of_nonneg hp]
#align ennreal.of_real_lt_of_real_iff_of_nonneg ENNReal.ofReal_lt_ofReal_iff_of_nonneg

@[simp]
theorem ofReal_pos {p : ℝ} : 0 < ENNReal.ofReal p ↔ 0 < p := by simp [ENNReal.ofReal]
#align ennreal.of_real_pos ENNReal.ofReal_pos

@[simp]
theorem ofReal_eq_zero {p : ℝ} : ENNReal.ofReal p = 0 ↔ p ≤ 0 := by simp [ENNReal.ofReal]
#align ennreal.of_real_eq_zero ENNReal.ofReal_eq_zero

@[simp]
theorem zero_eq_ofReal {p : ℝ} : 0 = ENNReal.ofReal p ↔ p ≤ 0 :=
  eq_comm.trans ofReal_eq_zero
#align ennreal.zero_eq_of_real ENNReal.zero_eq_ofReal

alias of_real_eq_zero ↔ _ of_real_of_nonpos
#align ennreal.of_real_of_nonpos ENNReal.ofReal_of_nonpos

theorem ofReal_sub (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q := by
  obtain h | h := le_total p q
  · rw [of_real_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (of_real_le_of_real h)]
  refine' ENNReal.eq_sub_of_add_eq of_real_ne_top _
  rw [← of_real_add (sub_nonneg_of_le h) hq, sub_add_cancel]
#align ennreal.of_real_sub ENNReal.ofReal_sub

theorem ofReal_le_iff_le_toReal {a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) :
    ENNReal.ofReal a ≤ b ↔ a ≤ ENNReal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_le_iff_le_coe
#align ennreal.of_real_le_iff_le_to_real ENNReal.ofReal_le_iff_le_toReal

theorem ofReal_lt_iff_lt_toReal {a : ℝ} {b : ℝ≥0∞} (ha : 0 ≤ a) (hb : b ≠ ∞) :
    ENNReal.ofReal a < b ↔ a < ENNReal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.toNNReal_lt_iff_lt_coe ha
#align ennreal.of_real_lt_iff_lt_to_real ENNReal.ofReal_lt_iff_lt_toReal

theorem le_ofReal_iff_toReal_le {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) (hb : 0 ≤ b) :
    a ≤ ENNReal.ofReal b ↔ ENNReal.toReal a ≤ b := by
  lift a to ℝ≥0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.le_toNNReal_iff_coe_le hb
#align ennreal.le_of_real_iff_to_real_le ENNReal.le_ofReal_iff_toReal_le

theorem toReal_le_of_le_ofReal {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ENNReal.ofReal b) :
    ENNReal.toReal a ≤ b :=
  have ha : a ≠ ∞ := ne_top_of_le_ne_top ofReal_ne_top h
  (le_ofReal_iff_toReal_le ha hb).1 h
#align ennreal.to_real_le_of_le_of_real ENNReal.toReal_le_of_le_ofReal

theorem lt_ofReal_iff_toReal_lt {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) :
    a < ENNReal.ofReal b ↔ ENNReal.toReal a < b := by
  lift a to ℝ≥0 using ha
  simpa [ENNReal.ofReal, ENNReal.toReal] using Real.lt_toNNReal_iff_coe_lt
#align ennreal.lt_of_real_iff_to_real_lt ENNReal.lt_ofReal_iff_toReal_lt

theorem ofReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  simp only [ENNReal.ofReal, ← coe_mul, Real.toNNReal_mul hp]
#align ennreal.of_real_mul ENNReal.ofReal_mul

theorem ofReal_mul' {p q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  rw [mul_comm, of_real_mul hq, mul_comm]
#align ennreal.of_real_mul' ENNReal.ofReal_mul'

theorem ofReal_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) : ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n :=
  by rw [of_real_eq_coe_nnreal hp, ← coe_pow, ← of_real_coe_nnreal, NNReal.coe_pow, NNReal.coe_mk]
#align ennreal.of_real_pow ENNReal.ofReal_pow

theorem ofReal_nsmul {x : ℝ} {n : ℕ} : ENNReal.ofReal (n • x) = n • ENNReal.ofReal x := by
  simp only [nsmul_eq_mul, ← of_real_coe_nat n, ← of_real_mul n.cast_nonneg]
#align ennreal.of_real_nsmul ENNReal.ofReal_nsmul

theorem ofReal_inv_of_pos {x : ℝ} (hx : 0 < x) : (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal x⁻¹ := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_eq_coe,
    real.to_nnreal_inv.symm]
#align ennreal.of_real_inv_of_pos ENNReal.ofReal_inv_of_pos

theorem ofReal_div_of_pos {x y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, of_real_mul' (inv_nonneg.2 hy.le), of_real_inv_of_pos hy]
#align ennreal.of_real_div_of_pos ENNReal.ofReal_div_of_pos

@[simp]
theorem toNNReal_mul {a b : ℝ≥0∞} : (a * b).toNNReal = a.toNNReal * b.toNNReal :=
  WithTop.untop'_zero_mul a b
#align ennreal.to_nnreal_mul ENNReal.toNNReal_mul

theorem toNNReal_mul_top (a : ℝ≥0∞) : ENNReal.toNNReal (a * ∞) = 0 := by simp
#align ennreal.to_nnreal_mul_top ENNReal.toNNReal_mul_top

theorem toNNReal_top_mul (a : ℝ≥0∞) : ENNReal.toNNReal (∞ * a) = 0 := by simp
#align ennreal.to_nnreal_top_mul ENNReal.toNNReal_top_mul

@[simp]
theorem smul_toNNReal (a : ℝ≥0) (b : ℝ≥0∞) : (a • b).toNNReal = a * b.toNNReal := by
  change ((a : ℝ≥0∞) * b).toNNReal = a * b.to_nnreal
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
#align ennreal.smul_to_nnreal ENNReal.smul_toNNReal

/-- `ennreal.to_nnreal` as a `monoid_hom`. -/
def toNNRealHom : ℝ≥0∞ →* ℝ≥0 where
  toFun := ENNReal.toNNReal
  map_one' := toNNReal_coe
  map_mul' _ _ := toNNReal_mul
#align ennreal.to_nnreal_hom ENNReal.toNNRealHom

@[simp]
theorem toNNReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toNNReal = a.toNNReal ^ n :=
  toNNRealHom.map_pow a n
#align ennreal.to_nnreal_pow ENNReal.toNNReal_pow

@[simp]
theorem toNNReal_prod {ι : Type _} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i in s, f i).toNNReal = ∏ i in s, (f i).toNNReal :=
  toNNRealHom.map_prod _ _
#align ennreal.to_nnreal_prod ENNReal.toNNReal_prod

/-- `ennreal.to_real` as a `monoid_hom`. -/
def toRealHom : ℝ≥0∞ →* ℝ :=
  (NNReal.toRealHom : ℝ≥0 →* ℝ).comp toNNRealHom
#align ennreal.to_real_hom ENNReal.toRealHom

@[simp]
theorem toReal_mul : (a * b).toReal = a.toReal * b.toReal :=
  toRealHom.map_mul a b
#align ennreal.to_real_mul ENNReal.toReal_mul

@[simp]
theorem toReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toReal = a.toReal ^ n :=
  toRealHom.map_pow a n
#align ennreal.to_real_pow ENNReal.toReal_pow

@[simp]
theorem toReal_prod {ι : Type _} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i in s, f i).toReal = ∏ i in s, (f i).toReal :=
  toRealHom.map_prod _ _
#align ennreal.to_real_prod ENNReal.toReal_prod

theorem toReal_ofReal_mul (c : ℝ) (a : ℝ≥0∞) (h : 0 ≤ c) :
    ENNReal.toReal (ENNReal.ofReal c * a) = c * ENNReal.toReal a := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h]
#align ennreal.to_real_of_real_mul ENNReal.toReal_ofReal_mul

theorem toReal_mul_top (a : ℝ≥0∞) : ENNReal.toReal (a * ∞) = 0 := by
  rw [to_real_mul, top_to_real, mul_zero]
#align ennreal.to_real_mul_top ENNReal.toReal_mul_top

theorem toReal_top_mul (a : ℝ≥0∞) : ENNReal.toReal (∞ * a) = 0 := by
  rw [mul_comm]
  exact to_real_mul_top _
#align ennreal.to_real_top_mul ENNReal.toReal_top_mul

theorem toReal_eq_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : ENNReal.toReal a = ENNReal.toReal b ↔ a = b :=
  by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  simp only [coe_eq_coe, NNReal.coe_eq, coe_to_real]
#align ennreal.to_real_eq_to_real ENNReal.toReal_eq_toReal

theorem toReal_smul (r : ℝ≥0) (s : ℝ≥0∞) : (r • s).toReal = r • s.toReal := by
  rw [ENNReal.smul_def, smul_eq_mul, to_real_mul, coe_to_real]
  rfl
#align ennreal.to_real_smul ENNReal.toReal_smul

protected theorem trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal := by
  simpa only [or_iff_not_imp_left] using to_real_pos
#align ennreal.trichotomy ENNReal.trichotomy

protected theorem trichotomy₂ {p q : ℝ≥0∞} (hpq : p ≤ q) :
    p = 0 ∧ q = 0 ∨
      p = 0 ∧ q = ∞ ∨
        p = 0 ∧ 0 < q.toReal ∨
          p = ∞ ∧ q = ∞ ∨
            0 < p.toReal ∧ q = ∞ ∨ 0 < p.toReal ∧ 0 < q.toReal ∧ p.toReal ≤ q.toReal := by
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with ((rfl : 0 = p) | (hp : 0 < p))
  · simpa using q.trichotomy
  rcases eq_or_lt_of_le (le_top : q ≤ ∞) with (rfl | hq)
  · simpa using p.trichotomy
  repeat' right
  have hq' : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq
  simp [ENNReal.toReal_le_toReal hp'.ne hq.ne, ENNReal.toReal_pos_iff, hpq, hp, hp', hq', hq]
#align ennreal.trichotomy₂ ENNReal.trichotomy₂

protected theorem dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal :=
  haveI : p = ⊤ ∨ 0 < p.to_real ∧ 1 ≤ p.to_real := by
    simpa using ENNReal.trichotomy₂ (Fact.out _ : 1 ≤ p)
  this.imp_right fun h => h.2
#align ennreal.dichotomy ENNReal.dichotomy

theorem toReal_pos_iff_ne_top (p : ℝ≥0∞) [Fact (1 ≤ p)] : 0 < p.toReal ↔ p ≠ ∞ :=
  ⟨fun h hp =>
    let this : (0 : ℝ) ≠ 0 := top_toReal ▸ (hp ▸ h.Ne : 0 ≠ ∞.toReal)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩
#align ennreal.to_real_pos_iff_ne_top ENNReal.toReal_pos_iff_ne_top

theorem toNNReal_inv (a : ℝ≥0∞) : a⁻¹.toNNReal = a.toNNReal⁻¹ := by
  induction a using WithTop.recTopCoe; · simp
  rcases eq_or_ne a 0 with (rfl | ha); · simp
  rw [← coe_inv ha, to_nnreal_coe, to_nnreal_coe]
#align ennreal.to_nnreal_inv ENNReal.toNNReal_inv

theorem toNNReal_div (a b : ℝ≥0∞) : (a / b).toNNReal = a.toNNReal / b.toNNReal := by
  rw [div_eq_mul_inv, to_nnreal_mul, to_nnreal_inv, div_eq_mul_inv]
#align ennreal.to_nnreal_div ENNReal.toNNReal_div

theorem toReal_inv (a : ℝ≥0∞) : a⁻¹.toReal = a.toReal⁻¹ := by
  simp_rw [ENNReal.toReal]
  norm_cast
  exact to_nnreal_inv a
#align ennreal.to_real_inv ENNReal.toReal_inv

theorem toReal_div (a b : ℝ≥0∞) : (a / b).toReal = a.toReal / b.toReal := by
  rw [div_eq_mul_inv, to_real_mul, to_real_inv, div_eq_mul_inv]
#align ennreal.to_real_div ENNReal.toReal_div

theorem ofReal_prod_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∏ i in s, f i) = ∏ i in s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_prod, coe_eq_coe]
  exact Real.toNNReal_prod_of_nonneg hf
#align ennreal.of_real_prod_of_nonneg ENNReal.ofReal_prod_of_nonneg

@[simp]
theorem toNNReal_bit0 {x : ℝ≥0∞} : (bit0 x).toNNReal = bit0 x.toNNReal := by
  induction x using WithTop.recTopCoe
  · simp
  · exact to_nnreal_add coe_ne_top coe_ne_top
#align ennreal.to_nnreal_bit0 ENNReal.toNNReal_bit0

@[simp]
theorem toNNReal_bit1 {x : ℝ≥0∞} (hx_top : x ≠ ∞) : (bit1 x).toNNReal = bit1 x.toNNReal := by
  simp [bit1, bit1, to_nnreal_add (by rwa [Ne.def, bit0_eq_top_iff]) ENNReal.one_ne_top]
#align ennreal.to_nnreal_bit1 ENNReal.toNNReal_bit1

@[simp]
theorem toReal_bit0 {x : ℝ≥0∞} : (bit0 x).toReal = bit0 x.toReal := by simp [ENNReal.toReal]
#align ennreal.to_real_bit0 ENNReal.toReal_bit0

@[simp]
theorem toReal_bit1 {x : ℝ≥0∞} (hx_top : x ≠ ∞) : (bit1 x).toReal = bit1 x.toReal := by
  simp [ENNReal.toReal, hx_top]
#align ennreal.to_real_bit1 ENNReal.toReal_bit1

@[simp]
theorem ofReal_bit0 (r : ℝ) : ENNReal.ofReal (bit0 r) = bit0 (ENNReal.ofReal r) := by
  simp [ENNReal.ofReal]
#align ennreal.of_real_bit0 ENNReal.ofReal_bit0

@[simp]
theorem ofReal_bit1 {r : ℝ} (hr : 0 ≤ r) : ENNReal.ofReal (bit1 r) = bit1 (ENNReal.ofReal r) :=
  (ofReal_add (by simp [hr]) zero_le_one).trans (by simp [Real.toNNReal_one, bit1])
#align ennreal.of_real_bit1 ENNReal.ofReal_bit1

end Real

section infᵢ

variable {ι : Sort _} {f g : ι → ℝ≥0∞}

theorem infᵢ_add : infᵢ f + a = ⨅ i, f i + a :=
  le_antisymm (le_infᵢ fun i => add_le_add (infᵢ_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_infᵢ fun i => tsub_le_iff_right.2 <| infᵢ_le _ _)
#align ennreal.infi_add ENNReal.infᵢ_add

theorem supᵢ_sub : (⨆ i, f i) - a = ⨆ i, f i - a :=
  le_antisymm (tsub_le_iff_right.2 <| supᵢ_le fun i => tsub_le_iff_right.1 <| le_supᵢ _ i)
    (supᵢ_le fun i => tsub_le_tsub (le_supᵢ _ _) (le_refl a))
#align ennreal.supr_sub ENNReal.supᵢ_sub

theorem sub_infᵢ : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine' eq_of_forall_ge_iff fun c => _
  rw [tsub_le_iff_right, add_comm, infi_add]
  simp [tsub_le_iff_right, sub_eq_add_neg, add_comm]
#align ennreal.sub_infi ENNReal.sub_infᵢ

theorem infₛ_add {s : Set ℝ≥0∞} : infₛ s + a = ⨅ b ∈ s, b + a := by simp [infₛ_eq_infᵢ, infi_add]
#align ennreal.Inf_add ENNReal.infₛ_add

theorem add_infᵢ {a : ℝ≥0∞} : a + infᵢ f = ⨅ b, a + f b := by
  rw [add_comm, infi_add] <;> simp [add_comm]
#align ennreal.add_infi ENNReal.add_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a a') -/
theorem infᵢ_add_infᵢ (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : infᵢ f + infᵢ g = ⨅ a, f a + g a :=
  suffices (⨅ a, f a + g a) ≤ infᵢ f + infᵢ g from
    le_antisymm (le_infᵢ fun a => add_le_add (infᵢ_le _ _) (infᵢ_le _ _)) this
  calc
    (⨅ a, f a + g a) ≤ ⨅ (a) (a'), f a + g a' :=
      le_infᵢ fun a =>
        le_infᵢ fun a' =>
          let ⟨k, h⟩ := h a a'
          infᵢ_le_of_le k h
    _ = infᵢ f + infᵢ g := by simp [add_infi, infi_add]
    
#align ennreal.infi_add_infi ENNReal.infᵢ_add_infᵢ

theorem infᵢ_sum {f : ι → α → ℝ≥0∞} {s : Finset α} [Nonempty ι]
    (h : ∀ (t : Finset α) (i j : ι), ∃ k, ∀ a ∈ t, f k a ≤ f i a ∧ f k a ≤ f j a) :
    (⨅ i, ∑ a in s, f i a) = ∑ a in s, ⨅ i, f i a := by
  induction' s using Finset.induction_on with a s ha ih
  · simp
  have : ∀ i j : ι, ∃ k : ι, (f k a + ∑ b in s, f k b) ≤ f i a + ∑ b in s, f j b :=
    by
    intro i j
    obtain ⟨k, hk⟩ := h (insert a s) i j
    exact
      ⟨k,
        add_le_add (hk a (Finset.mem_insert_self _ _)).left <|
          Finset.sum_le_sum fun a ha => (hk _ <| Finset.mem_insert_of_mem ha).right⟩
  simp [ha, ih.symm, infi_add_infi this]
#align ennreal.infi_sum ENNReal.infᵢ_sum

/-- If `x ≠ 0` and `x ≠ ∞`, then right multiplication by `x` maps infimum to infimum.
See also `ennreal.infi_mul` that assumes `[nonempty ι]` but does not require `x ≠ 0`. -/
theorem infᵢ_mul_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
    infᵢ f * x = ⨅ i, f i * x :=
  le_antisymm mul_right_mono.map_infᵢ_le
    ((ENNReal.div_le_iff_le_mul (Or.inl h0) <| Or.inl h).mp <|
      le_infᵢ fun i => (ENNReal.div_le_iff_le_mul (Or.inl h0) <| Or.inl h).mpr <| infᵢ_le _ _)
#align ennreal.infi_mul_of_ne ENNReal.infᵢ_mul_of_ne

/-- If `x ≠ ∞`, then right multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ennreal.infi_mul_of_ne` that assumes `x ≠ 0` but does not require `[nonempty ι]`. -/
theorem infᵢ_mul {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
    infᵢ f * x = ⨅ i, f i * x := by
  by_cases h0 : x = 0
  · simp only [h0, mul_zero, infᵢ_const]
  · exact infi_mul_of_ne h0 h
#align ennreal.infi_mul ENNReal.infᵢ_mul

/-- If `x ≠ ∞`, then left multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ennreal.mul_infi_of_ne` that assumes `x ≠ 0` but does not require `[nonempty ι]`. -/
theorem mul_infᵢ {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
    x * infᵢ f = ⨅ i, x * f i := by simpa only [mul_comm] using infi_mul h
#align ennreal.mul_infi ENNReal.mul_infᵢ

/-- If `x ≠ 0` and `x ≠ ∞`, then left multiplication by `x` maps infimum to infimum.
See also `ennreal.mul_infi` that assumes `[nonempty ι]` but does not require `x ≠ 0`. -/
theorem mul_infᵢ_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
    x * infᵢ f = ⨅ i, x * f i := by simpa only [mul_comm] using infi_mul_of_ne h0 h
#align ennreal.mul_infi_of_ne ENNReal.mul_infᵢ_of_ne

/-! `supr_mul`, `mul_supr` and variants are in `topology.instances.ennreal`. -/


end infᵢ

section supᵢ

@[simp]
theorem supᵢ_eq_zero {ι : Sort _} {f : ι → ℝ≥0∞} : (⨆ i, f i) = 0 ↔ ∀ i, f i = 0 :=
  supᵢ_eq_bot
#align ennreal.supr_eq_zero ENNReal.supᵢ_eq_zero

@[simp]
theorem supᵢ_zero_eq_zero {ι : Sort _} : (⨆ i : ι, (0 : ℝ≥0∞)) = 0 := by simp
#align ennreal.supr_zero_eq_zero ENNReal.supᵢ_zero_eq_zero

theorem sup_eq_zero {a b : ℝ≥0∞} : a ⊔ b = 0 ↔ a = 0 ∧ b = 0 :=
  sup_eq_bot_iff
#align ennreal.sup_eq_zero ENNReal.sup_eq_zero

theorem supᵢ_coe_nat : (⨆ n : ℕ, (n : ℝ≥0∞)) = ∞ :=
  (supᵢ_eq_top _).2 fun b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)
#align ennreal.supr_coe_nat ENNReal.supᵢ_coe_nat

end supᵢ

end ENNReal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0} {u : Set ℝ≥0∞}

theorem preimage_coe_nNReal_ennreal (h : u.OrdConnected) : (coe ⁻¹' u : Set ℝ≥0).OrdConnected :=
  h.preimage_mono ENNReal.coe_mono
#align set.ord_connected.preimage_coe_nnreal_ennreal Set.OrdConnected.preimage_coe_nNReal_ennreal

theorem image_coe_nNReal_ennreal (h : t.OrdConnected) : (coe '' t : Set ℝ≥0∞).OrdConnected := by
  refine' ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => _⟩
  rcases ENNReal.le_coe_iff.1 hz.2 with ⟨z, rfl, hzy⟩
  exact mem_image_of_mem _ (h.out hx hy ⟨ENNReal.coe_le_coe.1 hz.1, ENNReal.coe_le_coe.1 hz.2⟩)
#align set.ord_connected.image_coe_nnreal_ennreal Set.OrdConnected.image_coe_nNReal_ennreal

theorem preimage_ennreal_ofReal (h : u.OrdConnected) : (ENNReal.ofReal ⁻¹' u).OrdConnected :=
  h.preimage_coe_nNReal_ennreal.preimage_real_toNNReal
#align set.ord_connected.preimage_ennreal_of_real Set.OrdConnected.preimage_ennreal_ofReal

theorem image_ennreal_ofReal (h : s.OrdConnected) : (ENNReal.ofReal '' s).OrdConnected := by
  simpa only [image_image] using h.image_real_to_nnreal.image_coe_nnreal_ennreal
#align set.ord_connected.image_ennreal_of_real Set.OrdConnected.image_ennreal_ofReal

end OrdConnected

end Set

namespace Tactic

open Positivity

private theorem nnreal_coe_pos {r : ℝ≥0} : 0 < r → 0 < (r : ℝ≥0∞) :=
  ENNReal.coe_pos.2
#align tactic.nnreal_coe_pos tactic.nnreal_coe_pos

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ≥0∞`. -/
@[positivity]
unsafe def positivity_coe_nnreal_ennreal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ <| @coeBase _ _ ENNReal.hasCoe)
    let positive p ← core a
    -- We already know `0 ≤ r` for all `r : ℝ≥0∞`
        positive <$>
        mk_app `` nnreal_coe_pos [p]
  | e =>
    pp e >>=
      fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ≥0∞)` for `r : ℝ≥0`"
#align tactic.positivity_coe_nnreal_ennreal tactic.positivity_coe_nnreal_ennreal

private theorem ennreal_of_real_pos {r : ℝ} : 0 < r → 0 < ENNReal.ofReal r :=
  ENNReal.ofReal_pos.2
#align tactic.ennreal_of_real_pos tactic.ennreal_of_real_pos

/-- Extension for the `positivity` tactic: `ennreal.of_real` is positive if its input is. -/
@[positivity]
unsafe def positivity_ennreal_of_real : expr → tactic strictness
  | q(ENNReal.ofReal $(r)) => do
    let positive p ← core r
    positive <$> mk_app `` ennreal_of_real_pos [p]
  |-- This case is handled by `tactic.positivity_canon`
    e =>
    pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `ennreal.of_real r`"
#align tactic.positivity_ennreal_of_real tactic.positivity_ennreal_of_real

end Tactic

