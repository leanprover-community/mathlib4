/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.Real.NNReal
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Data.Set.Intervals.WithBotTop
import Mathlib.Tactic.GCongr.Core
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Algebra.Order.Monoid.WithTop

#align_import data.real.ennreal from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

/-!
# Extended non-negative reals

We define `ENNReal = ℝ≥0∞ := WithTop ℝ≥0` to be the type of extended nonnegative real numbers,
i.e., the interval `[0, +∞]`. This type is used as the codomain of a `MeasureTheory.Measure`,
and of the extended distance `edist` in an `EMetricSpace`.
In this file we define some algebraic operations and a linear order on `ℝ≥0∞`
and prove basic properties of these operations, order, and conversions to/from `ℝ`, `ℝ≥0`, and `ℕ`.

## Main definitions

* `ℝ≥0∞`: the extended nonnegative real numbers `[0, ∞]`; defined as `WithTop ℝ≥0`; it is
  equipped with the following structures:

  - coercion from `ℝ≥0` defined in the natural way;

  - the natural structure of a complete dense linear order: `↑p ≤ ↑q ↔ p ≤ q` and `∀ a, a ≤ ∞`;

  - `a + b` is defined so that `↑p + ↑q = ↑(p + q)` for `(p q : ℝ≥0)` and `a + ∞ = ∞ + a = ∞`;

  - `a * b` is defined so that `↑p * ↑q = ↑(p * q)` for `(p q : ℝ≥0)`, `0 * ∞ = ∞ * 0 = 0`, and
    `a * ∞ = ∞ * a = ∞` for `a ≠ 0`;

  - `a - b` is defined as the minimal `d` such that `a ≤ d + b`; this way we have
    `↑p - ↑q = ↑(p - q)`, `∞ - ↑p = ∞`, `↑p - ∞ = ∞ - ∞ = 0`; note that there is no negation, only
    subtraction;

  - `a⁻¹` is defined as `Inf {b | 1 ≤ a * b}`. This way we have `(↑p)⁻¹ = ↑(p⁻¹)` for
    `p : ℝ≥0`, `p ≠ 0`, `0⁻¹ = ∞`, and `∞⁻¹ = 0`.

  - `a / b` is defined as `a * b⁻¹`.

  The addition and multiplication defined this way together with `0 = ↑0` and `1 = ↑1` turn
  `ℝ≥0∞` into a canonically ordered commutative semiring of characteristic zero.

* Coercions to/from other types:

  - coercion `ℝ≥0 → ℝ≥0∞` is defined as `Coe`, so one can use `(p : ℝ≥0)` in a context that
    expects `a : ℝ≥0∞`, and Lean will apply `coe` automatically;

  - `ENNReal.toNNReal` sends `↑p` to `p` and `∞` to `0`;

  - `ENNReal.toReal := coe ∘ ENNReal.toNNReal` sends `↑p`, `p : ℝ≥0` to `(↑p : ℝ)` and `∞` to `0`;

  - `ENNReal.ofReal := coe ∘ Real.toNNReal` sends `x : ℝ` to `↑⟨max x 0, _⟩`

  - `ENNReal.neTopEquivNNReal` is an equivalence between `{a : ℝ≥0∞ // a ≠ 0}` and `ℝ≥0`.

## Implementation notes

We define a `CanLift ℝ≥0∞ ℝ≥0` instance, so one of the ways to prove theorems about an `ℝ≥0∞`
number `a` is to consider the cases `a = ∞` and `a ≠ ∞`, and use the tactic `lift a to ℝ≥0 using ha`
in the second case. This instance is even more useful if one already has `ha : a ≠ ∞` in the
context, or if we have `(f : α → ℝ≥0∞) (hf : ∀ x, f x ≠ ∞)`.

## Notations

* `ℝ≥0∞`: the type of the extended nonnegative real numbers;
* `ℝ≥0`: the type of nonnegative real numbers `[0, ∞)`; defined in `data.real.nnreal`;
* `∞`: a localized notation in `ℝ≥0∞` for `⊤ : ℝ≥0∞`.

-/


open Set BigOperators NNReal

variable {α : Type*} {β : Type*}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
def ENNReal := WithTop ℝ≥0
  deriving Zero, AddCommMonoidWithOne, SemilatticeSup, DistribLattice, Nontrivial
#align ennreal ENNReal

@[inherit_doc]
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal

/-- Notation for infinity as an `ENNReal` number. -/
scoped[ENNReal] notation "∞" => (⊤ : ENNReal)

namespace ENNReal

instance : OrderBot ℝ≥0∞ := inferInstanceAs (OrderBot (WithTop ℝ≥0))
instance : BoundedOrder ℝ≥0∞ := inferInstanceAs (BoundedOrder (WithTop ℝ≥0))
instance : CharZero ℝ≥0∞ := inferInstanceAs (CharZero (WithTop ℝ≥0))

noncomputable instance : CanonicallyOrderedCommSemiring ℝ≥0∞ :=
  inferInstanceAs (CanonicallyOrderedCommSemiring (WithTop ℝ≥0))

noncomputable instance : CompleteLinearOrder ℝ≥0∞ :=
  inferInstanceAs (CompleteLinearOrder (WithTop ℝ≥0))

instance : DenselyOrdered ℝ≥0∞ := inferInstanceAs (DenselyOrdered (WithTop ℝ≥0))

noncomputable instance : CanonicallyLinearOrderedAddCommMonoid ℝ≥0∞ :=
  inferInstanceAs (CanonicallyLinearOrderedAddCommMonoid (WithTop ℝ≥0))

noncomputable instance instSub : Sub ℝ≥0∞ := inferInstanceAs (Sub (WithTop ℝ≥0))
noncomputable instance : OrderedSub ℝ≥0∞ := inferInstanceAs (OrderedSub (WithTop ℝ≥0))

noncomputable instance : LinearOrderedAddCommMonoidWithTop ℝ≥0∞ :=
  inferInstanceAs (LinearOrderedAddCommMonoidWithTop (WithTop ℝ≥0))

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

-- porting note: are these 2 instances still required in Lean 4?
instance covariantClass_mul_le : CovariantClass ℝ≥0∞ ℝ≥0∞ (· * ·) (· ≤ ·) := inferInstance
#align ennreal.covariant_class_mul_le ENNReal.covariantClass_mul_le

instance covariantClass_add_le : CovariantClass ℝ≥0∞ ℝ≥0∞ (· + ·) (· ≤ ·) := inferInstance
#align ennreal.covariant_class_add_le ENNReal.covariantClass_add_le

-- porting note: todo: add a `WithTop` instance and use it here
noncomputable instance : LinearOrderedCommMonoidWithZero ℝ≥0∞ :=
  { inferInstanceAs (LinearOrderedAddCommMonoidWithTop ℝ≥0∞),
      inferInstanceAs (CommSemiring ℝ≥0∞) with
    mul_le_mul_left := fun _ _ => mul_le_mul_left'
    zero_le_one := zero_le 1 }

noncomputable instance : Unique (AddUnits ℝ≥0∞) where
  default := 0
  uniq a := AddUnits.ext <| le_zero_iff.1 <| by rw [← a.add_neg]; exact le_self_add

instance : Inhabited ℝ≥0∞ := ⟨0⟩

/-- Coercion from `ℝ≥0` to `ℝ≥0∞`. -/
@[coe, match_pattern] def ofNNReal : ℝ≥0 → ℝ≥0∞ := WithTop.some

instance : Coe ℝ≥0 ℝ≥0∞ := ⟨ofNNReal⟩

/-- A version of `WithTop.recTopCoe` that uses `ENNReal.ofNNReal`. -/
def recTopCoe {C : ℝ≥0∞ → Sort*} (top : C ∞) (coe : ∀ x : ℝ≥0, C x) (x : ℝ≥0∞) : C x :=
  WithTop.recTopCoe top coe x

instance canLift : CanLift ℝ≥0∞ ℝ≥0 ofNNReal (· ≠ ∞) := WithTop.canLift
#align ennreal.can_lift ENNReal.canLift

@[simp] theorem none_eq_top : (none : ℝ≥0∞) = ∞ := rfl
#align ennreal.none_eq_top ENNReal.none_eq_top

@[simp] theorem some_eq_coe (a : ℝ≥0) : (Option.some a : ℝ≥0∞) = (↑a : ℝ≥0∞) := rfl
#align ennreal.some_eq_coe ENNReal.some_eq_coe

@[simp] theorem some_eq_coe' (a : ℝ≥0) : (WithTop.some a : ℝ≥0∞) = (↑a : ℝ≥0∞) := rfl

protected theorem coe_injective : Function.Injective ((↑) : ℝ≥0 → ℝ≥0∞) := WithTop.coe_injective

theorem range_coe' : range ofNNReal = Iio ∞ := WithTop.range_coe
theorem range_coe : range ofNNReal = {∞}ᶜ := (isCompl_range_some_none ℝ≥0).symm.compl_eq.symm

/-- `toNNReal x` returns `x` if it is real, otherwise 0. -/
protected def toNNReal : ℝ≥0∞ → ℝ≥0 := WithTop.untop' 0
#align ennreal.to_nnreal ENNReal.toNNReal

/-- `toReal x` returns `x` if it is real, `0` otherwise. -/
protected def toReal (a : ℝ≥0∞) : Real := a.toNNReal
#align ennreal.to_real ENNReal.toReal

/-- `ofReal x` returns `x` if it is nonnegative, `0` otherwise. -/
protected noncomputable def ofReal (r : Real) : ℝ≥0∞ := r.toNNReal
#align ennreal.of_real ENNReal.ofReal

@[simp, norm_cast]
theorem toNNReal_coe : (r : ℝ≥0∞).toNNReal = r := rfl
#align ennreal.to_nnreal_coe ENNReal.toNNReal_coe

@[simp]
theorem coe_toNNReal : ∀ {a : ℝ≥0∞}, a ≠ ∞ → ↑a.toNNReal = a
  | ofNNReal _, _ => rfl
  | ⊤, h => (h rfl).elim
#align ennreal.coe_to_nnreal ENNReal.coe_toNNReal

@[simp]
theorem ofReal_toReal {a : ℝ≥0∞} (h : a ≠ ∞) : ENNReal.ofReal a.toReal = a := by
  simp [ENNReal.toReal, ENNReal.ofReal, h]
#align ennreal.of_real_to_real ENNReal.ofReal_toReal

@[simp]
theorem toReal_ofReal {r : ℝ} (h : 0 ≤ r) : (ENNReal.ofReal r).toReal = r :=
  max_eq_left h
#align ennreal.to_real_of_real ENNReal.toReal_ofReal

theorem toReal_ofReal' {r : ℝ} : (ENNReal.ofReal r).toReal = max r 0 := rfl
#align ennreal.to_real_of_real' ENNReal.toReal_ofReal'

theorem coe_toNNReal_le_self : ∀ {a : ℝ≥0∞}, ↑a.toNNReal ≤ a
  | ofNNReal r => by rw [toNNReal_coe]
  | ⊤ => le_top
#align ennreal.coe_to_nnreal_le_self ENNReal.coe_toNNReal_le_self

theorem coe_nnreal_eq (r : ℝ≥0) : (r : ℝ≥0∞) = ENNReal.ofReal r := by
  rw [ENNReal.ofReal, Real.toNNReal_coe]
#align ennreal.coe_nnreal_eq ENNReal.coe_nnreal_eq

theorem ofReal_eq_coe_nnreal {x : ℝ} (h : 0 ≤ x) :
    ENNReal.ofReal x = ofNNReal ⟨x, h⟩ :=
  (coe_nnreal_eq ⟨x, h⟩).symm
#align ennreal.of_real_eq_coe_nnreal ENNReal.ofReal_eq_coe_nnreal

@[simp] theorem ofReal_coe_nnreal : ENNReal.ofReal p = p := (coe_nnreal_eq p).symm
#align ennreal.of_real_coe_nnreal ENNReal.ofReal_coe_nnreal

@[simp, norm_cast] theorem coe_zero : ↑(0 : ℝ≥0) = (0 : ℝ≥0∞) := rfl
#align ennreal.coe_zero ENNReal.coe_zero

@[simp, norm_cast] theorem coe_one : ↑(1 : ℝ≥0) = (1 : ℝ≥0∞) := rfl
#align ennreal.coe_one ENNReal.coe_one

@[simp] theorem toReal_nonneg {a : ℝ≥0∞} : 0 ≤ a.toReal := a.toNNReal.2
#align ennreal.to_real_nonneg ENNReal.toReal_nonneg

@[simp] theorem top_toNNReal : ∞.toNNReal = 0 := rfl
#align ennreal.top_to_nnreal ENNReal.top_toNNReal

@[simp] theorem top_toReal : ∞.toReal = 0 := rfl
#align ennreal.top_to_real ENNReal.top_toReal

@[simp] theorem one_toReal : (1 : ℝ≥0∞).toReal = 1 := rfl
#align ennreal.one_to_real ENNReal.one_toReal

@[simp] theorem one_toNNReal : (1 : ℝ≥0∞).toNNReal = 1 := rfl
#align ennreal.one_to_nnreal ENNReal.one_toNNReal

@[simp] theorem coe_toReal (r : ℝ≥0) : (r : ℝ≥0∞).toReal = r := rfl
#align ennreal.coe_to_real ENNReal.coe_toReal

@[simp] theorem zero_toNNReal : (0 : ℝ≥0∞).toNNReal = 0 := rfl
#align ennreal.zero_to_nnreal ENNReal.zero_toNNReal

@[simp] theorem zero_toReal : (0 : ℝ≥0∞).toReal = 0 := rfl
#align ennreal.zero_to_real ENNReal.zero_toReal

@[simp] theorem ofReal_zero : ENNReal.ofReal (0 : ℝ) = 0 := by simp [ENNReal.ofReal]
#align ennreal.of_real_zero ENNReal.ofReal_zero

@[simp] theorem ofReal_one : ENNReal.ofReal (1 : ℝ) = (1 : ℝ≥0∞) := by simp [ENNReal.ofReal]
#align ennreal.of_real_one ENNReal.ofReal_one

theorem ofReal_toReal_le {a : ℝ≥0∞} : ENNReal.ofReal a.toReal ≤ a :=
  if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (ofReal_toReal ha)
#align ennreal.of_real_to_real_le ENNReal.ofReal_toReal_le

theorem forall_ennreal {p : ℝ≥0∞ → Prop} : (∀ a, p a) ↔ (∀ r : ℝ≥0, p r) ∧ p ∞ :=
  Option.forall.trans and_comm
#align ennreal.forall_ennreal ENNReal.forall_ennreal

theorem forall_ne_top {p : ℝ≥0∞ → Prop} : (∀ a, a ≠ ∞ → p a) ↔ ∀ r : ℝ≥0, p r :=
  Option.ball_ne_none
#align ennreal.forall_ne_top ENNReal.forall_ne_top

@[deprecated]
theorem exists_ne_top' {p : ℝ≥0∞ → Prop} : (∃ (a : ℝ≥0∞) (_ : a ≠ ∞), p a) ↔ ∃ r : ℝ≥0, p r :=
  Option.bex_ne_none
#align ennreal.exists_ne_top ENNReal.exists_ne_top'

set_option linter.deprecated false in
theorem exists_ne_top {p : ℝ≥0∞ → Prop} : (∃ a ≠ ∞, p a) ↔ ∃ r : ℝ≥0, p r := by
  simp only [exists_ne_top', ← exists_prop]

theorem toNNReal_eq_zero_iff (x : ℝ≥0∞) : x.toNNReal = 0 ↔ x = 0 ∨ x = ∞ :=
  WithTop.untop'_eq_self_iff
#align ennreal.to_nnreal_eq_zero_iff ENNReal.toNNReal_eq_zero_iff

theorem toReal_eq_zero_iff (x : ℝ≥0∞) : x.toReal = 0 ↔ x = 0 ∨ x = ∞ := by
  simp [ENNReal.toReal, toNNReal_eq_zero_iff]
#align ennreal.to_real_eq_zero_iff ENNReal.toReal_eq_zero_iff

theorem toNNReal_ne_zero : a.toNNReal ≠ 0 ↔ a ≠ 0 ∧ a ≠ ∞ :=
  a.toNNReal_eq_zero_iff.not.trans not_or
#align ennreal.to_nnreal_ne_zero ENNReal.toNNReal_ne_zero

theorem toReal_ne_zero : a.toReal ≠ 0 ↔ a ≠ 0 ∧ a ≠ ∞ :=
  a.toReal_eq_zero_iff.not.trans not_or
#align ennreal.to_real_ne_zero ENNReal.toReal_ne_zero

theorem toNNReal_eq_one_iff (x : ℝ≥0∞) : x.toNNReal = 1 ↔ x = 1 :=
  WithTop.untop'_eq_iff.trans <| by simp
#align ennreal.to_nnreal_eq_one_iff ENNReal.toNNReal_eq_one_iff

theorem toReal_eq_one_iff (x : ℝ≥0∞) : x.toReal = 1 ↔ x = 1 := by
  rw [ENNReal.toReal, NNReal.coe_eq_one, ENNReal.toNNReal_eq_one_iff]
#align ennreal.to_real_eq_one_iff ENNReal.toReal_eq_one_iff

theorem toNNReal_ne_one : a.toNNReal ≠ 1 ↔ a ≠ 1 :=
  a.toNNReal_eq_one_iff.not
#align ennreal.to_nnreal_ne_one ENNReal.toNNReal_ne_one

theorem toReal_ne_one : a.toReal ≠ 1 ↔ a ≠ 1 :=
  a.toReal_eq_one_iff.not
#align ennreal.to_real_ne_one ENNReal.toReal_ne_one

@[simp] theorem coe_ne_top : (r : ℝ≥0∞) ≠ ∞ := WithTop.coe_ne_top
#align ennreal.coe_ne_top ENNReal.coe_ne_top

@[simp] theorem top_ne_coe : ∞ ≠ (r : ℝ≥0∞) := WithTop.top_ne_coe
#align ennreal.top_ne_coe ENNReal.top_ne_coe

@[simp] theorem coe_lt_top : (r : ℝ≥0∞) < ∞ := WithTop.coe_lt_top r
#align ennreal.coe_lt_top ENNReal.coe_lt_top

@[simp] theorem ofReal_ne_top {r : ℝ} : ENNReal.ofReal r ≠ ∞ := coe_ne_top
#align ennreal.of_real_ne_top ENNReal.ofReal_ne_top

@[simp] theorem ofReal_lt_top {r : ℝ} : ENNReal.ofReal r < ∞ := coe_lt_top
#align ennreal.of_real_lt_top ENNReal.ofReal_lt_top

@[simp] theorem top_ne_ofReal {r : ℝ} : ∞ ≠ ENNReal.ofReal r := top_ne_coe
#align ennreal.top_ne_of_real ENNReal.top_ne_ofReal

@[simp]
theorem ofReal_toReal_eq_iff : ENNReal.ofReal a.toReal = a ↔ a ≠ ⊤ :=
  ⟨fun h => by
    rw [← h]
    exact ofReal_ne_top, ofReal_toReal⟩
#align ennreal.of_real_to_real_eq_iff ENNReal.ofReal_toReal_eq_iff

@[simp]
theorem toReal_ofReal_eq_iff {a : ℝ} : (ENNReal.ofReal a).toReal = a ↔ 0 ≤ a :=
  ⟨fun h => by
    rw [← h]
    exact toReal_nonneg, toReal_ofReal⟩
#align ennreal.to_real_of_real_eq_iff ENNReal.toReal_ofReal_eq_iff

@[simp] theorem zero_ne_top : 0 ≠ ∞ := coe_ne_top
#align ennreal.zero_ne_top ENNReal.zero_ne_top

@[simp] theorem top_ne_zero : ∞ ≠ 0 := top_ne_coe
#align ennreal.top_ne_zero ENNReal.top_ne_zero

@[simp] theorem one_ne_top : 1 ≠ ∞ := coe_ne_top
#align ennreal.one_ne_top ENNReal.one_ne_top

@[simp] theorem top_ne_one : ∞ ≠ 1 := top_ne_coe
#align ennreal.top_ne_one ENNReal.top_ne_one

@[simp] theorem zero_lt_top : 0 < ∞ := coe_lt_top

@[simp, norm_cast] theorem coe_eq_coe : (↑r : ℝ≥0∞) = ↑q ↔ r = q := WithTop.coe_eq_coe
#align ennreal.coe_eq_coe ENNReal.coe_eq_coe

@[simp, norm_cast] theorem coe_le_coe : (↑r : ℝ≥0∞) ≤ ↑q ↔ r ≤ q := WithTop.coe_le_coe
#align ennreal.coe_le_coe ENNReal.coe_le_coe

@[simp, norm_cast] theorem coe_lt_coe : (↑r : ℝ≥0∞) < ↑q ↔ r < q := WithTop.coe_lt_coe
#align ennreal.coe_lt_coe ENNReal.coe_lt_coe

-- Needed until `@[gcongr]` accepts iff statements
alias ⟨_, coe_le_coe_of_le⟩ := coe_le_coe
attribute [gcongr] ENNReal.coe_le_coe_of_le

-- Needed until `@[gcongr]` accepts iff statements
alias ⟨_, coe_lt_coe_of_le⟩ := coe_lt_coe
attribute [gcongr] ENNReal.coe_lt_coe_of_le

theorem coe_mono : Monotone ofNNReal := fun _ _ => coe_le_coe.2
#align ennreal.coe_mono ENNReal.coe_mono

theorem coe_strictMono : StrictMono ofNNReal := fun _ _ => coe_lt_coe.2

@[simp, norm_cast] theorem coe_eq_zero : (↑r : ℝ≥0∞) = 0 ↔ r = 0 := coe_eq_coe
#align ennreal.coe_eq_zero ENNReal.coe_eq_zero

@[simp, norm_cast] theorem zero_eq_coe : 0 = (↑r : ℝ≥0∞) ↔ 0 = r := coe_eq_coe
#align ennreal.zero_eq_coe ENNReal.zero_eq_coe

@[simp, norm_cast] theorem coe_eq_one : (↑r : ℝ≥0∞) = 1 ↔ r = 1 := coe_eq_coe
#align ennreal.coe_eq_one ENNReal.coe_eq_one

@[simp, norm_cast] theorem one_eq_coe : 1 = (↑r : ℝ≥0∞) ↔ 1 = r := coe_eq_coe
#align ennreal.one_eq_coe ENNReal.one_eq_coe

@[simp, norm_cast] theorem coe_pos : 0 < (r : ℝ≥0∞) ↔ 0 < r := coe_lt_coe
#align ennreal.coe_pos ENNReal.coe_pos

theorem coe_ne_zero : (r : ℝ≥0∞) ≠ 0 ↔ r ≠ 0 := not_congr coe_eq_coe
#align ennreal.coe_ne_zero ENNReal.coe_ne_zero

@[simp, norm_cast] theorem coe_add : ↑(r + p) = (r : ℝ≥0∞) + p := WithTop.coe_add _ _
#align ennreal.coe_add ENNReal.coe_add

@[simp, norm_cast]
theorem coe_mul : ↑(r * p) = (r : ℝ≥0∞) * p :=
  WithTop.coe_mul
#align ennreal.coe_mul ENNReal.coe_mul

#noalign ennreal.coe_bit0
#noalign ennreal.coe_bit1

-- See note [no_index around OfNat.ofNat]
@[simp, norm_cast] -- porting note: new
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n) : ℝ≥0) : ℝ≥0∞) = OfNat.ofNat n := rfl

-- porting note: todo: add lemmas about `OfNat.ofNat` and `<`/`≤`

theorem coe_two : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := rfl
#align ennreal.coe_two ENNReal.coe_two

theorem toNNReal_eq_toNNReal_iff (x y : ℝ≥0∞) :
    x.toNNReal = y.toNNReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 :=
  WithTop.untop'_eq_untop'_iff
#align ennreal.to_nnreal_eq_to_nnreal_iff ENNReal.toNNReal_eq_toNNReal_iff

theorem toReal_eq_toReal_iff (x y : ℝ≥0∞) :
    x.toReal = y.toReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 := by
  simp only [ENNReal.toReal, NNReal.coe_eq, toNNReal_eq_toNNReal_iff]
#align ennreal.to_real_eq_to_real_iff ENNReal.toReal_eq_toReal_iff

theorem toNNReal_eq_toNNReal_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x.toNNReal = y.toNNReal ↔ x = y := by
  simp only [ENNReal.toNNReal_eq_toNNReal_iff x y, hx, hy, and_false, false_and, or_false]
#align ennreal.to_nnreal_eq_to_nnreal_iff' ENNReal.toNNReal_eq_toNNReal_iff'

theorem toReal_eq_toReal_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x.toReal = y.toReal ↔ x = y := by
  simp only [ENNReal.toReal, NNReal.coe_eq, toNNReal_eq_toNNReal_iff' hx hy]
#align ennreal.to_real_eq_to_real_iff' ENNReal.toReal_eq_toReal_iff'

@[simp]
nonrec theorem one_lt_two : (1 : ℝ≥0∞) < 2 :=
  coe_one ▸ coe_two ▸ mod_cast (one_lt_two : 1 < 2)
#align ennreal.one_lt_two ENNReal.one_lt_two

@[simp] theorem two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := coe_ne_top
#align ennreal.two_ne_top ENNReal.two_ne_top

@[simp] theorem two_lt_top : (2 : ℝ≥0∞) < ∞ := coe_lt_top

/-- `(1 : ℝ≥0∞) ≤ 1`, recorded as a `Fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_one_ennreal : Fact ((1 : ℝ≥0∞) ≤ 1) :=
  ⟨le_rfl⟩
#align fact_one_le_one_ennreal fact_one_le_one_ennreal

/-- `(1 : ℝ≥0∞) ≤ 2`, recorded as a `Fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_two_ennreal : Fact ((1 : ℝ≥0∞) ≤ 2) :=
  ⟨one_le_two⟩
#align fact_one_le_two_ennreal fact_one_le_two_ennreal

/-- `(1 : ℝ≥0∞) ≤ ∞`, recorded as a `Fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_top_ennreal : Fact ((1 : ℝ≥0∞) ≤ ∞) :=
  ⟨le_top⟩
#align fact_one_le_top_ennreal fact_one_le_top_ennreal

/-- The set of numbers in `ℝ≥0∞` that are not equal to `∞` is equivalent to `ℝ≥0`. -/
def neTopEquivNNReal : { a | a ≠ ∞ } ≃ ℝ≥0 where
  toFun x := ENNReal.toNNReal x
  invFun x := ⟨x, coe_ne_top⟩
  left_inv := fun x => Subtype.eq <| coe_toNNReal x.2
  right_inv _ := toNNReal_coe
#align ennreal.ne_top_equiv_nnreal ENNReal.neTopEquivNNReal

theorem cinfi_ne_top [InfSet α] (f : ℝ≥0∞ → α) : ⨅ x : { x // x ≠ ∞ }, f x = ⨅ x : ℝ≥0, f x :=
  Eq.symm <| neTopEquivNNReal.symm.surjective.iInf_congr _ fun _ => rfl
#align ennreal.cinfi_ne_top ENNReal.cinfi_ne_top

theorem iInf_ne_top [CompleteLattice α] (f : ℝ≥0∞ → α) :
    ⨅ (x) (_ : x ≠ ∞), f x = ⨅ x : ℝ≥0, f x := by rw [iInf_subtype', cinfi_ne_top]
#align ennreal.infi_ne_top ENNReal.iInf_ne_top

theorem csupr_ne_top [SupSet α] (f : ℝ≥0∞ → α) : ⨆ x : { x // x ≠ ∞ }, f x = ⨆ x : ℝ≥0, f x :=
  @cinfi_ne_top αᵒᵈ _ _
#align ennreal.csupr_ne_top ENNReal.csupr_ne_top

theorem iSup_ne_top [CompleteLattice α] (f : ℝ≥0∞ → α) :
    ⨆ (x) (_ : x ≠ ∞), f x = ⨆ x : ℝ≥0, f x :=
  @iInf_ne_top αᵒᵈ _ _
#align ennreal.supr_ne_top ENNReal.iSup_ne_top

theorem iInf_ennreal {α : Type*} [CompleteLattice α] {f : ℝ≥0∞ → α} :
    ⨅ n, f n = (⨅ n : ℝ≥0, f n) ⊓ f ∞ :=
  (iInf_option f).trans inf_comm
#align ennreal.infi_ennreal ENNReal.iInf_ennreal

theorem iSup_ennreal {α : Type*} [CompleteLattice α] {f : ℝ≥0∞ → α} :
    ⨆ n, f n = (⨆ n : ℝ≥0, f n) ⊔ f ∞ :=
  @iInf_ennreal αᵒᵈ _ _
#align ennreal.supr_ennreal ENNReal.iSup_ennreal

/-- Coercion `ℝ≥0 → ℝ≥0∞` as a `RingHom`. -/
def ofNNRealHom : ℝ≥0 →+* ℝ≥0∞ where
  toFun := some
  map_one' := coe_one
  map_mul' _ _ := coe_mul
  map_zero' := coe_zero
  map_add' _ _ := coe_add
#align ennreal.of_nnreal_hom ENNReal.ofNNRealHom

@[simp] theorem coe_ofNNRealHom : ⇑ofNNRealHom = some := rfl
#align ennreal.coe_of_nnreal_hom ENNReal.coe_ofNNRealHom

-- TODO: generalize some of these (and subsequent lemmas about `smul`) to `WithTop α`
section Actions

/-- A `MulAction` over `ℝ≥0∞` restricts to a `MulAction` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [MulAction ℝ≥0∞ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M ofNNRealHom.toMonoidHom

theorem smul_def {M : Type*} [MulAction ℝ≥0∞ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ≥0∞) • x :=
  rfl
#align ennreal.smul_def ENNReal.smul_def

instance {M N : Type*} [MulAction ℝ≥0∞ M] [MulAction ℝ≥0∞ N] [SMul M N] [IsScalarTower ℝ≥0∞ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := (smul_assoc (r : ℝ≥0∞) : _)

instance smulCommClass_left {M N : Type*} [MulAction ℝ≥0∞ N] [SMul M N] [SMulCommClass ℝ≥0∞ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := (smul_comm (r : ℝ≥0∞) : _)
#align ennreal.smul_comm_class_left ENNReal.smulCommClass_left

instance smulCommClass_right {M N : Type*} [MulAction ℝ≥0∞ N] [SMul M N] [SMulCommClass M ℝ≥0∞ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := (smul_comm m (r : ℝ≥0∞) : _)
#align ennreal.smul_comm_class_right ENNReal.smulCommClass_right

/-- A `DistribMulAction` over `ℝ≥0∞` restricts to a `DistribMulAction` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [AddMonoid M] [DistribMulAction ℝ≥0∞ M] :
    DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M ofNNRealHom.toMonoidHom

/-- A `Module` over `ℝ≥0∞` restricts to a `Module` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [AddCommMonoid M] [Module ℝ≥0∞ M] : Module ℝ≥0 M :=
  Module.compHom M ofNNRealHom

/-- An `Algebra` over `ℝ≥0∞` restricts to an `Algebra` over `ℝ≥0`. -/
noncomputable instance {A : Type*} [Semiring A] [Algebra ℝ≥0∞ A] : Algebra ℝ≥0 A where
  smul := (· • ·)
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ≥0∞) x, smul_def]
  toRingHom := (algebraMap ℝ≥0∞ A).comp (ofNNRealHom : ℝ≥0 →+* ℝ≥0∞)

-- verify that the above produces instances we might care about
noncomputable example : Algebra ℝ≥0 ℝ≥0∞ := inferInstance

noncomputable example : DistribMulAction ℝ≥0ˣ ℝ≥0∞ := inferInstance

theorem coe_smul {R} (r : R) (s : ℝ≥0) [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0]
    [IsScalarTower R ℝ≥0 ℝ≥0∞] : (↑(r • s) : ℝ≥0∞) = (r : R) • (s : ℝ≥0∞) := by
  rw [← smul_one_smul ℝ≥0 r (s : ℝ≥0∞), smul_def, smul_eq_mul, ← ENNReal.coe_mul, smul_mul_assoc,
    one_mul]
#align ennreal.coe_smul ENNReal.coe_smul

end Actions

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ≥0∞) = s.indicator (fun x => ↑(f x)) a :=
  (ofNNRealHom : ℝ≥0 →+ ℝ≥0∞).map_indicator _ _ _
#align ennreal.coe_indicator ENNReal.coe_indicator

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : (↑(r ^ n) : ℝ≥0∞) = (r : ℝ≥0∞) ^ n :=
  ofNNRealHom.map_pow r n
#align ennreal.coe_pow ENNReal.coe_pow

@[simp] theorem add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := WithTop.add_eq_top
#align ennreal.add_eq_top ENNReal.add_eq_top

@[simp] theorem add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := WithTop.add_lt_top
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

theorem mul_top' : a * ∞ = if a = 0 then 0 else ∞ := by convert WithTop.mul_top' a
#align ennreal.mul_top ENNReal.mul_top'

-- porting note: added because `simp` no longer uses `WithTop` lemmas for `ℝ≥0∞`
@[simp] theorem mul_top (h : a ≠ 0) : a * ∞ = ∞ := WithTop.mul_top h

theorem top_mul' : ∞ * a = if a = 0 then 0 else ∞ := by convert WithTop.top_mul' a
#align ennreal.top_mul ENNReal.top_mul'

-- porting note: added because `simp` no longer uses `WithTop` lemmas for `ℝ≥0∞`
@[simp] theorem top_mul (h : a ≠ 0) : ∞ * a = ∞ := WithTop.top_mul h

theorem top_mul_top : ∞ * ∞ = ∞ := WithTop.top_mul_top
#align ennreal.top_mul_top ENNReal.top_mul_top

-- porting note: added missing `DecidableEq R`
theorem smul_top {R} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [NoZeroSMulDivisors R ℝ≥0∞] [DecidableEq R] (c : R) :
    c • ∞ = if c = 0 then 0 else ∞ := by
  rw [← smul_one_mul, mul_top']
  -- porting note: need the primed version of `one_ne_zero` now
  simp_rw [smul_eq_zero, or_iff_left (one_ne_zero' ℝ≥0∞)]
#align ennreal.smul_top ENNReal.smul_top

-- porting note: todo: assume `n ≠ 0` instead of `0 < n`
-- porting note: todo: generalize to `WithTop`
theorem top_pow {n : ℕ} (h : 0 < n) : ∞ ^ n = ∞ :=
  Nat.le_induction (pow_one _) (fun m _ hm => by rw [pow_succ, hm, top_mul_top]) _
    (Nat.succ_le_of_lt h)
#align ennreal.top_pow ENNReal.top_pow

theorem mul_eq_top : a * b = ∞ ↔ a ≠ 0 ∧ b = ∞ ∨ a = ∞ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff
#align ennreal.mul_eq_top ENNReal.mul_eq_top

theorem mul_lt_top : a ≠ ∞ → b ≠ ∞ → a * b < ∞ := WithTop.mul_lt_top
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
    rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha.ne hb.ne; simp; simp]
#align ennreal.mul_lt_top_iff ENNReal.mul_lt_top_iff

theorem mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ := by
  rw [ENNReal.mul_lt_top_iff, and_self, or_self, or_iff_left_iff_imp]
  rintro rfl
  exact zero_lt_top
#align ennreal.mul_self_lt_top_iff ENNReal.mul_self_lt_top_iff

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  CanonicallyOrderedCommSemiring.mul_pos
#align ennreal.mul_pos_iff ENNReal.mul_pos_iff

theorem mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
  mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩
#align ennreal.mul_pos ENNReal.mul_pos

-- porting note: todo: generalize to `WithTop`
@[simp] theorem pow_eq_top_iff {n : ℕ} : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 := by
  rcases n.eq_zero_or_pos with rfl | (hn : 0 < n)
  · simp
  · induction a using recTopCoe
    · simp only [Ne.def, hn.ne', top_pow hn, not_false_eq_true, and_self]
    · simp only [← coe_pow, coe_ne_top, false_and]
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
theorem coe_finset_sum {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℝ≥0∞) :=
  ofNNRealHom.map_sum f s
#align ennreal.coe_finset_sum ENNReal.coe_finset_sum

@[simp, norm_cast]
theorem coe_finset_prod {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℝ≥0∞) :=
  ofNNRealHom.map_prod f s
#align ennreal.coe_finset_prod ENNReal.coe_finset_prod

section Order

theorem bot_eq_zero : (⊥ : ℝ≥0∞) = 0 := rfl
#align ennreal.bot_eq_zero ENNReal.bot_eq_zero

-- `coe_lt_top` moved up

theorem not_top_le_coe : ¬∞ ≤ ↑r := WithTop.not_top_le_coe r
#align ennreal.not_top_le_coe ENNReal.not_top_le_coe

@[simp, norm_cast]
theorem one_le_coe_iff : (1 : ℝ≥0∞) ≤ ↑r ↔ 1 ≤ r := coe_le_coe
#align ennreal.one_le_coe_iff ENNReal.one_le_coe_iff

@[simp, norm_cast]
theorem coe_le_one_iff : ↑r ≤ (1 : ℝ≥0∞) ↔ r ≤ 1 := coe_le_coe
#align ennreal.coe_le_one_iff ENNReal.coe_le_one_iff

@[simp, norm_cast]
theorem coe_lt_one_iff : (↑p : ℝ≥0∞) < 1 ↔ p < 1 := coe_lt_coe
#align ennreal.coe_lt_one_iff ENNReal.coe_lt_one_iff

@[simp, norm_cast]
theorem one_lt_coe_iff : 1 < (↑p : ℝ≥0∞) ↔ 1 < p := coe_lt_coe
#align ennreal.one_lt_coe_iff ENNReal.one_lt_coe_iff

@[simp, norm_cast]
theorem coe_nat (n : ℕ) : ((n : ℝ≥0) : ℝ≥0∞) = n := rfl
#align ennreal.coe_nat ENNReal.coe_nat

@[simp, norm_cast] lemma ofReal_coe_nat (n : ℕ) : ENNReal.ofReal n = n := by simp [ENNReal.ofReal]
#align ennreal.of_real_coe_nat ENNReal.ofReal_coe_nat

-- See note [no_index around OfNat.ofNat]
@[simp] theorem ofReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    ENNReal.ofReal (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  ofReal_coe_nat n

@[simp] theorem nat_ne_top (n : ℕ) : (n : ℝ≥0∞) ≠ ∞ := WithTop.nat_ne_top n
#align ennreal.nat_ne_top ENNReal.nat_ne_top

@[simp] theorem top_ne_nat (n : ℕ) : ∞ ≠ n := WithTop.top_ne_nat n
#align ennreal.top_ne_nat ENNReal.top_ne_nat

@[simp] theorem one_lt_top : 1 < ∞ := coe_lt_top
#align ennreal.one_lt_top ENNReal.one_lt_top

@[simp, norm_cast]
theorem toNNReal_nat (n : ℕ) : (n : ℝ≥0∞).toNNReal = n := by
  rw [← ENNReal.coe_nat n, ENNReal.toNNReal_coe]
#align ennreal.to_nnreal_nat ENNReal.toNNReal_nat

@[simp, norm_cast]
theorem toReal_nat (n : ℕ) : (n : ℝ≥0∞).toReal = n := by
  rw [← ENNReal.ofReal_coe_nat n, ENNReal.toReal_ofReal (Nat.cast_nonneg _)]
#align ennreal.to_real_nat ENNReal.toReal_nat

-- See note [no_index around OfNat.ofNat]
@[simp] theorem toReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    ENNReal.toReal (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  toReal_nat n

theorem le_coe_iff : a ≤ ↑r ↔ ∃ p : ℝ≥0, a = p ∧ p ≤ r := WithTop.le_coe_iff
#align ennreal.le_coe_iff ENNReal.le_coe_iff

theorem coe_le_iff : ↑r ≤ a ↔ ∀ p : ℝ≥0, a = p → r ≤ p := WithTop.coe_le_iff
#align ennreal.coe_le_iff ENNReal.coe_le_iff

theorem lt_iff_exists_coe : a < b ↔ ∃ p : ℝ≥0, a = p ∧ ↑p < b :=
  WithTop.lt_iff_exists_coe
#align ennreal.lt_iff_exists_coe ENNReal.lt_iff_exists_coe

theorem toReal_le_coe_of_le_coe {a : ℝ≥0∞} {b : ℝ≥0} (h : a ≤ b) : a.toReal ≤ b := by
  lift a to ℝ≥0 using ne_top_of_le_ne_top coe_ne_top h
  simpa using h
#align ennreal.to_real_le_coe_of_le_coe ENNReal.toReal_le_coe_of_le_coe

@[simp, norm_cast]
theorem coe_finset_sup {s : Finset α} {f : α → ℝ≥0} : ↑(s.sup f) = s.sup fun x => (f x : ℝ≥0∞) :=
  Finset.comp_sup_eq_sup_comp_of_is_total _ coe_mono rfl
#align ennreal.coe_finset_sup ENNReal.coe_finset_sup

@[simp] theorem max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 := max_eq_bot
#align ennreal.max_eq_zero_iff ENNReal.max_eq_zero_iff

theorem max_zero_left : max 0 a = a :=
  max_eq_right (zero_le a)
#align ennreal.max_zero_left ENNReal.max_zero_left

theorem max_zero_right : max a 0 = a :=
  max_eq_left (zero_le a)
#align ennreal.max_zero_right ENNReal.max_zero_right

@[simp] theorem sup_eq_max : a ⊔ b = max a b := rfl
#align ennreal.sup_eq_max ENNReal.sup_eq_max

protected theorem pow_pos : 0 < a → ∀ n : ℕ, 0 < a ^ n :=
  CanonicallyOrderedCommSemiring.pow_pos
#align ennreal.pow_pos ENNReal.pow_pos

protected theorem pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a ^ n ≠ 0 := by
  simpa only [pos_iff_ne_zero] using ENNReal.pow_pos
#align ennreal.pow_ne_zero ENNReal.pow_ne_zero

theorem not_lt_zero : ¬a < 0 := by simp
#align ennreal.not_lt_zero ENNReal.not_lt_zero

protected theorem le_of_add_le_add_left : a ≠ ∞ → a + b ≤ a + c → b ≤ c :=
  WithTop.le_of_add_le_add_left
#align ennreal.le_of_add_le_add_left ENNReal.le_of_add_le_add_left

protected theorem le_of_add_le_add_right : a ≠ ∞ → b + a ≤ c + a → b ≤ c :=
  WithTop.le_of_add_le_add_right
#align ennreal.le_of_add_le_add_right ENNReal.le_of_add_le_add_right

@[gcongr] protected theorem add_lt_add_left : a ≠ ∞ → b < c → a + b < a + c :=
  WithTop.add_lt_add_left
#align ennreal.add_lt_add_left ENNReal.add_lt_add_left

@[gcongr] protected theorem add_lt_add_right : a ≠ ∞ → b < c → b + a < c + a :=
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

-- porting note: moved `le_of_forall_pos_le_add` down

theorem lt_iff_exists_rat_btwn :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ (Real.toNNReal q : ℝ≥0∞) < b :=
  ⟨fun h => by
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩
    rcases exists_between h with ⟨c, pc, cb⟩
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩
    rcases (NNReal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt_coe.2 qr) cb⟩,
      fun ⟨q, _, qa, qb⟩ => lt_trans qa qb⟩
#align ennreal.lt_iff_exists_rat_btwn ENNReal.lt_iff_exists_rat_btwn

theorem lt_iff_exists_real_btwn :
    a < b ↔ ∃ r : ℝ, 0 ≤ r ∧ a < ENNReal.ofReal r ∧ (ENNReal.ofReal r : ℝ≥0∞) < b :=
  ⟨fun h =>
    let ⟨q, q0, aq, qb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    ⟨q, Rat.cast_nonneg.2 q0, aq, qb⟩,
    fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩
#align ennreal.lt_iff_exists_real_btwn ENNReal.lt_iff_exists_real_btwn

theorem lt_iff_exists_nnreal_btwn : a < b ↔ ∃ r : ℝ≥0, a < r ∧ (r : ℝ≥0∞) < b :=
  WithTop.lt_iff_exists_coe_btwn
#align ennreal.lt_iff_exists_nnreal_btwn ENNReal.lt_iff_exists_nnreal_btwn

theorem lt_iff_exists_add_pos_lt : a < b ↔ ∃ r : ℝ≥0, 0 < r ∧ a + r < b := by
  refine' ⟨fun hab => _, fun ⟨r, _, hr⟩ => lt_of_le_of_lt le_self_add hr⟩
  rcases lt_iff_exists_nnreal_btwn.1 hab with ⟨c, ac, cb⟩
  lift a to ℝ≥0 using ac.ne_top
  rw [coe_lt_coe] at ac
  refine ⟨c - a, tsub_pos_iff_lt.2 ac, ?_⟩
  rwa [← coe_add, add_tsub_cancel_of_le ac.le]
#align ennreal.lt_iff_exists_add_pos_lt ENNReal.lt_iff_exists_add_pos_lt

theorem le_of_forall_pos_le_add (h : ∀ ε : ℝ≥0, 0 < ε → b < ∞ → a ≤ b + ε) : a ≤ b := by
  contrapose! h
  rcases lt_iff_exists_add_pos_lt.1 h with ⟨r, hr0, hr⟩
  exact ⟨r, hr0, h.trans_le le_top, hr⟩
#align ennreal.le_of_forall_pos_le_add ENNReal.le_of_forall_pos_le_add

theorem coe_nat_lt_coe {n : ℕ} : (n : ℝ≥0∞) < r ↔ ↑n < r :=
  ENNReal.coe_nat n ▸ coe_lt_coe
#align ennreal.coe_nat_lt_coe ENNReal.coe_nat_lt_coe

theorem coe_lt_coe_nat {n : ℕ} : (r : ℝ≥0∞) < n ↔ r < n :=
  ENNReal.coe_nat n ▸ coe_lt_coe
#align ennreal.coe_lt_coe_nat ENNReal.coe_lt_coe_nat

protected theorem exists_nat_gt {r : ℝ≥0∞} (h : r ≠ ∞) : ∃ n : ℕ, r < n := by
  lift r to ℝ≥0 using h
  rcases exists_nat_gt r with ⟨n, hn⟩
  exact ⟨n, coe_lt_coe_nat.2 hn⟩
#align ennreal.exists_nat_gt ENNReal.exists_nat_gt

@[simp]
theorem iUnion_Iio_coe_nat : ⋃ n : ℕ, Iio (n : ℝ≥0∞) = {∞}ᶜ := by
  ext x
  rw [mem_iUnion]
  exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, ENNReal.exists_nat_gt⟩
#align ennreal.Union_Iio_coe_nat ENNReal.iUnion_Iio_coe_nat

@[simp]
theorem iUnion_Iic_coe_nat : ⋃ n : ℕ, Iic (n : ℝ≥0∞) = {∞}ᶜ :=
  Subset.antisymm (iUnion_subset fun n _x hx => ne_top_of_le_ne_top (nat_ne_top n) hx) <|
    iUnion_Iio_coe_nat ▸ iUnion_mono fun _ => Iio_subset_Iic_self
#align ennreal.Union_Iic_coe_nat ENNReal.iUnion_Iic_coe_nat

@[simp]
theorem iUnion_Ioc_coe_nat : ⋃ n : ℕ, Ioc a n = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, diff_eq]
#align ennreal.Union_Ioc_coe_nat ENNReal.iUnion_Ioc_coe_nat

@[simp]
theorem iUnion_Ioo_coe_nat : ⋃ n : ℕ, Ioo a n = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, diff_eq]
#align ennreal.Union_Ioo_coe_nat ENNReal.iUnion_Ioo_coe_nat

@[simp]
theorem iUnion_Icc_coe_nat : ⋃ n : ℕ, Icc a n = Ici a \ {∞} := by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, diff_eq]
#align ennreal.Union_Icc_coe_nat ENNReal.iUnion_Icc_coe_nat

@[simp]
theorem iUnion_Ico_coe_nat : ⋃ n : ℕ, Ico a n = Ici a \ {∞} := by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, diff_eq]
#align ennreal.Union_Ico_coe_nat ENNReal.iUnion_Ico_coe_nat

@[simp]
theorem iInter_Ici_coe_nat : ⋂ n : ℕ, Ici (n : ℝ≥0∞) = {∞} := by
  simp only [← compl_Iio, ← compl_iUnion, iUnion_Iio_coe_nat, compl_compl]
#align ennreal.Inter_Ici_coe_nat ENNReal.iInter_Ici_coe_nat

@[simp]
theorem iInter_Ioi_coe_nat : ⋂ n : ℕ, Ioi (n : ℝ≥0∞) = {∞} := by
  simp only [← compl_Iic, ← compl_iUnion, iUnion_Iic_coe_nat, compl_compl]
#align ennreal.Inter_Ioi_coe_nat ENNReal.iInter_Ioi_coe_nat

-- porting note: todo: generalize to `WithTop`
@[gcongr] theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d := by
  lift a to ℝ≥0 using ac.ne_top
  lift b to ℝ≥0 using bd.ne_top
  cases c; · simp
  cases d; · simp
  simp only [← coe_add, some_eq_coe, coe_lt_coe] at *
  exact add_lt_add ac bd
#align ennreal.add_lt_add ENNReal.add_lt_add

@[simp, norm_cast]
theorem coe_min (r p : ℝ≥0) : ((min r p : ℝ≥0) : ℝ≥0∞) = min (r : ℝ≥0∞) p := rfl
#align ennreal.coe_min ENNReal.coe_min

@[simp, norm_cast]
theorem coe_max (r p : ℝ≥0) : ((max r p : ℝ≥0) : ℝ≥0∞) = max (r : ℝ≥0∞) p := rfl
#align ennreal.coe_max ENNReal.coe_max

theorem le_of_top_imp_top_of_toNNReal_le {a b : ℝ≥0∞} (h : a = ⊤ → b = ⊤)
    (h_nnreal : a ≠ ⊤ → b ≠ ⊤ → a.toNNReal ≤ b.toNNReal) : a ≤ b := by
  by_contra! hlt
  lift b to ℝ≥0 using hlt.ne_top
  lift a to ℝ≥0 using mt h coe_ne_top
  refine hlt.not_le ?_
  simpa using h_nnreal
#align ennreal.le_of_top_imp_top_of_to_nnreal_le ENNReal.le_of_top_imp_top_of_toNNReal_le

@[simp]
theorem abs_toReal {x : ℝ≥0∞} : |x.toReal| = x.toReal := by cases x <;> simp

end Order

section CompleteLattice
variable {ι : Sort*} {f : ι → ℝ≥0}

theorem coe_sSup {s : Set ℝ≥0} : BddAbove s → (↑(sSup s) : ℝ≥0∞) = ⨆ a ∈ s, ↑a :=
  WithTop.coe_sSup
#align ennreal.coe_Sup ENNReal.coe_sSup

theorem coe_sInf {s : Set ℝ≥0} : s.Nonempty → (↑(sInf s) : ℝ≥0∞) = ⨅ a ∈ s, ↑a :=
  WithTop.coe_sInf
#align ennreal.coe_Inf ENNReal.coe_sInf

theorem coe_iSup {ι : Sort*} {f : ι → ℝ≥0} (hf : BddAbove (range f)) :
    (↑(iSup f) : ℝ≥0∞) = ⨆ a, ↑(f a) :=
  WithTop.coe_iSup _ hf
#align ennreal.coe_supr ENNReal.coe_iSup

@[norm_cast]
theorem coe_iInf {ι : Sort*} [Nonempty ι] (f : ι → ℝ≥0) : (↑(iInf f) : ℝ≥0∞) = ⨅ a, ↑(f a) :=
  WithTop.coe_iInf f
#align ennreal.coe_infi ENNReal.coe_iInf

theorem coe_mem_upperBounds {s : Set ℝ≥0} :
    ↑r ∈ upperBounds (ofNNReal '' s) ↔ r ∈ upperBounds s := by
  simp (config := { contextual := true }) [upperBounds, ball_image_iff, -mem_image, *]
#align ennreal.coe_mem_upper_bounds ENNReal.coe_mem_upperBounds

lemma iSup_coe_eq_top : ⨆ i, (f i : ℝ≥0∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
lemma iSup_coe_lt_top : ⨆ i, (f i : ℝ≥0∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
lemma iInf_coe_eq_top : ⨅ i, (f i : ℝ≥0∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
lemma iInf_coe_lt_top : ⨅ i, (f i : ℝ≥0∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

end CompleteLattice

section Mul

-- porting note: todo: generalize to `WithTop`
@[mono, gcongr]
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := by
  rcases lt_iff_exists_nnreal_btwn.1 ac with ⟨a', aa', a'c⟩
  lift a to ℝ≥0 using ne_top_of_lt aa'
  rcases lt_iff_exists_nnreal_btwn.1 bd with ⟨b', bb', b'd⟩
  lift b to ℝ≥0 using ne_top_of_lt bb'
  norm_cast at *
  calc
    ↑(a * b) < ↑(a' * b') := coe_lt_coe.2 (mul_lt_mul₀ aa' bb')
    _ = ↑a' * ↑b' := coe_mul
    _ ≤ c * d := mul_le_mul' a'c.le b'd.le
#align ennreal.mul_lt_mul ENNReal.mul_lt_mul

-- TODO: generalize to `CovariantClass α α (· * ·) (· ≤ ·)`
theorem mul_left_mono : Monotone (a * ·) := fun _ _ => mul_le_mul' le_rfl
#align ennreal.mul_left_mono ENNReal.mul_left_mono

-- TODO: generalize to `CovariantClass α α (swap (· * ·)) (· ≤ ·)`
theorem mul_right_mono : Monotone (· * a) := fun _ _ h => mul_le_mul' h le_rfl
#align ennreal.mul_right_mono ENNReal.mul_right_mono

-- porting note: todo: generalize to `WithTop`
theorem pow_strictMono : ∀ {n : ℕ}, n ≠ 0 → StrictMono fun x : ℝ≥0∞ => x ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simpa only [pow_one] using strictMono_id
  | (n + 1 + 1), _ => fun x y h => mul_lt_mul h (pow_strictMono n.succ_ne_zero h)
#align ennreal.pow_strict_mono ENNReal.pow_strictMono

@[gcongr] protected theorem pow_lt_pow_left (h : a < b) {n : ℕ} (hn : n ≠ 0) :
    a ^ n < b ^ n :=
  ENNReal.pow_strictMono hn h

theorem max_mul : max a b * c = max (a * c) (b * c) := mul_right_mono.map_max
#align ennreal.max_mul ENNReal.max_mul

theorem mul_max : a * max b c = max (a * b) (a * c) := mul_left_mono.map_max
#align ennreal.mul_max ENNReal.mul_max

-- porting note: todo: generalize to `WithTop`
theorem mul_left_strictMono (h0 : a ≠ 0) (hinf : a ≠ ∞) : StrictMono (a * ·) := by
  lift a to ℝ≥0 using hinf
  rw [coe_ne_zero] at h0
  intro x y h
  contrapose! h
  simpa only [← mul_assoc, ← coe_mul, inv_mul_cancel h0, coe_one, one_mul]
    using mul_le_mul_left' h (↑a⁻¹)
#align ennreal.mul_left_strict_mono ENNReal.mul_left_strictMono

@[gcongr] protected theorem mul_lt_mul_left' (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_left_strictMono h0 hinf bc

@[gcongr] protected theorem mul_lt_mul_right' (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_left_strictMono h0 hinf bc

-- porting note: todo: generalize to `WithTop`
theorem mul_eq_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b = a * c ↔ b = c :=
  (mul_left_strictMono h0 hinf).injective.eq_iff
#align ennreal.mul_eq_mul_left ENNReal.mul_eq_mul_left

-- porting note: todo: generalize to `WithTop`
theorem mul_eq_mul_right : c ≠ 0 → c ≠ ∞ → (a * c = b * c ↔ a = b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_eq_mul_left
#align ennreal.mul_eq_mul_right ENNReal.mul_eq_mul_right

-- porting note: todo: generalize to `WithTop`
theorem mul_le_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : (a * b ≤ a * c ↔ b ≤ c) :=
  (mul_left_strictMono h0 hinf).le_iff_le
#align ennreal.mul_le_mul_left ENNReal.mul_le_mul_left

-- porting note: todo: generalize to `WithTop`
theorem mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left
#align ennreal.mul_le_mul_right ENNReal.mul_le_mul_right

-- porting note: todo: generalize to `WithTop`
theorem mul_lt_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : (a * b < a * c ↔ b < c) :=
  (mul_left_strictMono h0 hinf).lt_iff_lt
#align ennreal.mul_lt_mul_left ENNReal.mul_lt_mul_left

-- porting note: todo: generalize to `WithTop`
theorem mul_lt_mul_right : c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left
#align ennreal.mul_lt_mul_right ENNReal.mul_lt_mul_right

end Mul

section Cancel

-- porting note: todo: generalize to `WithTop`
/-- An element `a` is `AddLECancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
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
  cancel_of_ne h.ne
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

theorem sub_eq_sInf {a b : ℝ≥0∞} : a - b = sInf { d | a ≤ d + b } :=
  le_antisymm (le_sInf fun _ h => tsub_le_iff_right.mpr h) <| sInf_le <| mem_setOf.2 le_tsub_add
#align ennreal.sub_eq_Inf ENNReal.sub_eq_sInf

/-- This is a special case of `WithTop.coe_sub` in the `ENNReal` namespace -/
@[simp] theorem coe_sub : (↑(r - p) : ℝ≥0∞) = ↑r - ↑p := WithTop.coe_sub
#align ennreal.coe_sub ENNReal.coe_sub

/-- This is a special case of `WithTop.top_sub_coe` in the `ENNReal` namespace -/
@[simp] theorem top_sub_coe : ∞ - ↑r = ∞ := WithTop.top_sub_coe
#align ennreal.top_sub_coe ENNReal.top_sub_coe

/-- This is a special case of `WithTop.sub_top` in the `ENNReal` namespace -/
theorem sub_top : a - ∞ = 0 := WithTop.sub_top
#align ennreal.sub_top ENNReal.sub_top

-- porting note: added `@[simp]`
@[simp] theorem sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ := WithTop.sub_eq_top_iff
#align ennreal.sub_eq_top_iff ENNReal.sub_eq_top_iff

theorem sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ := mt sub_eq_top_iff.mp <| mt And.left ha
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
  rcases le_or_lt a b with hab | hab; · simp [hab, mul_right_mono hab]
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
theorem prod_lt_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : ∏ a in s, f a < ∞ :=
  WithTop.prod_lt_top h
#align ennreal.prod_lt_top ENNReal.prod_lt_top

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : ∑ a in s, f a < ∞ :=
  WithTop.sum_lt_top h
#align ennreal.sum_lt_top ENNReal.sum_lt_top

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top_iff {s : Finset α} {f : α → ℝ≥0∞} : ∑ a in s, f a < ∞ ↔ ∀ a ∈ s, f a < ∞ :=
  WithTop.sum_lt_top_iff
#align ennreal.sum_lt_top_iff ENNReal.sum_lt_top_iff

/-- A sum of numbers is infinite iff one of them is infinite -/
theorem sum_eq_top_iff {s : Finset α} {f : α → ℝ≥0∞} : ∑ x in s, f x = ∞ ↔ ∃ a ∈ s, f a = ∞ :=
  WithTop.sum_eq_top_iff
#align ennreal.sum_eq_top_iff ENNReal.sum_eq_top_iff

theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∑ x in s, f x ≠ ∞) {a : α}
    (ha : a ∈ s) : f a < ∞ :=
  sum_lt_top_iff.1 h.lt_top a ha
#align ennreal.lt_top_of_sum_ne_top ENNReal.lt_top_of_sum_ne_top

/-- Seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity -/
theorem toNNReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toNNReal (∑ a in s, f a) = ∑ a in s, ENNReal.toNNReal (f a) := by
  rw [← coe_eq_coe, coe_toNNReal, coe_finset_sum, sum_congr rfl]
  · intro x hx
    exact (coe_toNNReal (hf x hx)).symm
  · exact (sum_lt_top hf).ne
#align ennreal.to_nnreal_sum ENNReal.toNNReal_sum

/-- seeing `ℝ≥0∞` as `Real` does not change their sum, unless one of the `ℝ≥0∞` is infinity -/
theorem toReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toReal (∑ a in s, f a) = ∑ a in s, ENNReal.toReal (f a) := by
  rw [ENNReal.toReal, toNNReal_sum hf, NNReal.coe_sum]
  rfl
#align ennreal.to_real_sum ENNReal.toReal_sum

theorem ofReal_sum_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∑ i in s, f i) = ∑ i in s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_sum, coe_eq_coe]
  exact Real.toNNReal_sum_of_nonneg hf
#align ennreal.of_real_sum_of_nonneg ENNReal.ofReal_sum_of_nonneg

theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hlt : ∀ i ∈ s, f i < g i) : ∑ i in s, f i < ∑ i in s, g i := by
  induction' hs using Finset.Nonempty.cons_induction with a a s as _ IH
  · simp [Hlt _ (Finset.mem_singleton_self _)]
  · simp only [as, Finset.sum_cons, not_false_iff]
    exact
      ENNReal.add_lt_add (Hlt _ (Finset.mem_cons_self _ _))
        (IH fun i hi => Hlt _ (Finset.mem_cons.2 <| Or.inr hi))
#align ennreal.sum_lt_sum_of_nonempty ENNReal.sum_lt_sum_of_nonempty

theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hle : ∑ i in s, f i ≤ ∑ i in s, g i) : ∃ i ∈ s, f i ≤ g i := by
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

-- porting note: removed lemmas about `bit0` and `bit1`
-- TODO: add lemmas about `OfNat.ofNat`

#noalign ennreal.bit0_strict_mono
#noalign ennreal.bit0_injective
#noalign ennreal.bit0_lt_bit0
#noalign ennreal.bit0_le_bit0
#noalign ennreal.bit0_inj
#noalign ennreal.bit0_eq_zero_iff
#noalign ennreal.bit0_top
#noalign ennreal.bit0_eq_top_iff
#noalign ennreal.bit1_strict_mono
#noalign ennreal.bit1_injective
#noalign ennreal.bit1_lt_bit1
#noalign ennreal.bit1_le_bit1
#noalign ennreal.bit1_inj
#noalign ennreal.bit1_ne_zero
#noalign ennreal.bit1_top
#noalign ennreal.bit1_eq_top_iff
#noalign ennreal.bit1_eq_one_iff

end Bit

noncomputable section Inv

-- porting note: rfc: redefine using pattern matching?
instance : Inv ℝ≥0∞ := ⟨fun a => sInf { b | 1 ≤ a * b }⟩

instance : DivInvMonoid ℝ≥0∞ where

protected theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]
#align ennreal.div_eq_inv_mul ENNReal.div_eq_inv_mul

@[simp] theorem inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
  show sInf { b : ℝ≥0∞ | 1 ≤ 0 * b } = ∞ by simp
#align ennreal.inv_zero ENNReal.inv_zero

@[simp] theorem inv_top : ∞⁻¹ = 0 :=
  bot_unique <| le_of_forall_le_of_dense fun a (h : 0 < a) => sInf_le <| by simp [*, h.ne', top_mul]
#align ennreal.inv_top ENNReal.inv_top

theorem coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
  le_sInf fun b (hb : 1 ≤ ↑r * b) =>
    coe_le_iff.2 <| by
      rintro b rfl
      apply NNReal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb
#align ennreal.coe_inv_le ENNReal.coe_inv_le

@[simp, norm_cast]
theorem coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ :=
  coe_inv_le.antisymm <| sInf_le <| mem_setOf.2 <| by rw [← coe_mul, mul_inv_cancel hr, coe_one]
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
  { inferInstanceAs (DivInvMonoid ℝ≥0∞) with
    inv_one := by simpa only [coe_inv one_ne_zero, coe_one] using coe_eq_coe.2 inv_one }

protected theorem inv_pow : ∀ {a : ℝ≥0∞} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
  | _, 0 => by simp only [pow_zero, inv_one]
  | ⊤, n + 1 => by simp [top_pow]
  | (a : ℝ≥0), n + 1 => by
    rcases eq_or_ne a 0 with (rfl | ha)
    · simp [top_pow]
    · have := pow_ne_zero (n + 1) ha
      norm_cast
      rw [inv_pow]
#align ennreal.inv_pow ENNReal.inv_pow

protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
  lift a to ℝ≥0 using ht
  norm_cast at h0; norm_cast
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

-- porting note: `simp only [div_eq_mul_inv, mul_comm, mul_assoc]` doesn't work in the following two
protected theorem mul_comm_div : a / b * c = a * (c / b) := by
  simp only [div_eq_mul_inv, mul_right_comm, ← mul_assoc]
#align ennreal.mul_comm_div ENNReal.mul_comm_div

protected theorem mul_div_right_comm : a * b / c = a / c * b := by
  simp only [div_eq_mul_inv, mul_right_comm]
#align ennreal.mul_div_right_comm ENNReal.mul_div_right_comm

instance : InvolutiveInv ℝ≥0∞ where
  inv_inv a := by
    by_cases a = 0 <;> cases a <;> simp_all [none_eq_top, some_eq_coe, -coe_inv, (coe_inv _).symm]

@[simp] theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 := inv_zero ▸ inv_inj
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

protected theorem div_pos (ha : a ≠ 0) (hb : b ≠ ∞) : 0 < a / b :=
  ENNReal.mul_pos ha <| ENNReal.inv_ne_zero.2 hb
#align ennreal.div_pos ENNReal.div_pos

protected theorem mul_inv {a b : ℝ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction' b using recTopCoe with b
  · replace ha : a ≠ 0 := ha.neg_resolve_right rfl
    simp [ha]
  induction' a using recTopCoe with a
  · replace hb : b ≠ 0 := coe_ne_zero.1 (hb.neg_resolve_left rfl)
    simp [hb]
  by_cases h'a : a = 0
  · simp only [h'a, top_mul, ENNReal.inv_zero, ENNReal.coe_ne_top, zero_mul, Ne.def,
      not_false_iff, ENNReal.coe_zero, ENNReal.inv_eq_zero]
  by_cases h'b : b = 0
  · simp only [h'b, ENNReal.inv_zero, ENNReal.coe_ne_top, mul_top, Ne.def, not_false_iff,
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
  induction b using recTopCoe; · simp
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

@[gcongr] protected theorem inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h

@[gcongr] protected theorem inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

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

/-- The inverse map `fun x ↦ x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `OrderDual` -/
@[simps! apply]
def _root_.OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ where
  map_rel_iff' := ENNReal.inv_le_inv
  toEquiv := (Equiv.inv ℝ≥0∞).trans OrderDual.toDual
#align order_iso.inv_ennreal OrderIso.invENNReal
#align order_iso.inv_ennreal_apply OrderIso.invENNReal_apply

@[simp]
theorem _root_.OrderIso.invENNReal_symm_apply (a : ℝ≥0∞ᵒᵈ) :
    OrderIso.invENNReal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl
#align order_iso.inv_ennreal_symm_apply OrderIso.invENNReal_symm_apply

@[simp] theorem div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]
#align ennreal.div_top ENNReal.div_top

-- porting note: reordered 4 lemmas

theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by simp [div_eq_mul_inv, top_mul']
#align ennreal.top_div ENNReal.top_div

theorem top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ := by simp [top_div, h]
#align ennreal.top_div_of_ne_top ENNReal.top_div_of_ne_top

@[simp] theorem top_div_coe : ∞ / p = ∞ := top_div_of_ne_top coe_ne_top
#align ennreal.top_div_coe ENNReal.top_div_coe

theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ := top_div_of_ne_top h.ne
#align ennreal.top_div_of_lt_top ENNReal.top_div_of_lt_top

@[simp] protected theorem zero_div : 0 / a = 0 := zero_mul a⁻¹
#align ennreal.zero_div ENNReal.zero_div

theorem div_eq_top : a / b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞ := by
  simp [div_eq_mul_inv, ENNReal.mul_eq_top]
#align ennreal.div_eq_top ENNReal.div_eq_top

protected theorem le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
    a ≤ c / b ↔ a * b ≤ c := by
  induction' b using recTopCoe with b
  · lift c to ℝ≥0 using ht.neg_resolve_left rfl
    rw [div_top, nonpos_iff_eq_zero]
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

protected theorem div_self_le_one : a / a ≤ 1 := div_le_of_le_mul <| by rw [one_mul]

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

theorem div_lt_of_lt_mul (h : a < b * c) : a / c < b :=
  mul_lt_of_lt_div <| by rwa [div_eq_mul_inv, inv_inv]

theorem div_lt_of_lt_mul' (h : a < b * c) : a / b < c :=
  div_lt_of_lt_mul <| by rwa [mul_comm]

theorem inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← one_div, ENNReal.div_le_iff_le_mul, mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]
#align ennreal.inv_le_iff_le_mul ENNReal.inv_le_iff_le_mul

@[simp 900]
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  rw [← one_div, ENNReal.le_div_iff_mul_le] <;>
    · right
      simp
#align ennreal.le_inv_iff_mul_le ENNReal.le_inv_iff_mul_le

@[gcongr] protected theorem div_le_div (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)
#align ennreal.div_le_div ENNReal.div_le_div

@[gcongr] protected theorem div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) : c / b ≤ c / a :=
  ENNReal.div_le_div le_rfl h
#align ennreal.div_le_div_left ENNReal.div_le_div_left

@[gcongr] protected theorem div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c :=
  ENNReal.div_le_div h le_rfl
#align ennreal.div_le_div_right ENNReal.div_le_div_right

protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a, ← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ← mul_assoc, h,
    one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h
#align ennreal.eq_inv_of_mul_eq_one_left ENNReal.eq_inv_of_mul_eq_one_left

theorem mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  rw [← @ENNReal.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, ENNReal.mul_inv_cancel hr₀ hr₁,
    one_mul]
#align ennreal.mul_le_iff_le_inv ENNReal.mul_le_iff_le_inv

instance : PosSMulStrictMono ℝ≥0 ℝ≥0∞ where
  elim _r hr _a _b hab := ENNReal.mul_lt_mul_left' (coe_pos.2 hr).ne' coe_ne_top hab

instance : SMulPosMono ℝ≥0 ℝ≥0∞ where
  elim _r _ _a _b hab := mul_le_mul_right' (coe_le_coe.2 hab) _

#align ennreal.le_inv_smul_iff_of_pos le_inv_smul_iff_of_pos
#align ennreal.inv_smul_le_iff_of_pos inv_smul_le_iff_of_pos

theorem le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y := by
  refine' le_of_forall_ge_of_dense fun r hr => _
  lift r to ℝ≥0 using ne_top_of_lt hr
  exact h r hr
#align ennreal.le_of_forall_nnreal_lt ENNReal.le_of_forall_nnreal_lt

theorem le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
  le_of_forall_nnreal_lt fun r hr =>
    (zero_le r).eq_or_lt.elim (fun h => h ▸ zero_le _) fun h0 => h r h0 hr
#align ennreal.le_of_forall_pos_nnreal_lt ENNReal.le_of_forall_pos_nnreal_lt

theorem eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
  top_unique <| le_of_forall_nnreal_lt fun r _ => h r
#align ennreal.eq_top_of_forall_nnreal_le ENNReal.eq_top_of_forall_nnreal_le

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

theorem inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 :=
  calc (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹ := by ring
  _ = 1 := ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 <| by decide) coe_ne_top
#align ennreal.inv_three_add_inv_three ENNReal.inv_three_add_inv_three

@[simp]
protected theorem add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]
#align ennreal.add_halves ENNReal.add_halves

@[simp]
theorem add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]
#align ennreal.add_thirds ENNReal.add_thirds

@[simp] theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by simp [div_eq_mul_inv]
#align ennreal.div_zero_iff ENNReal.div_eq_zero_iff

@[simp] theorem div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ := by simp [pos_iff_ne_zero, not_or]
#align ennreal.div_pos_iff ENNReal.div_pos_iff

protected theorem half_pos (h : a ≠ 0) : 0 < a / 2 := by
  simp only [div_pos_iff, ne_eq, h, not_false_eq_true, two_ne_top, and_self]
#align ennreal.half_pos ENNReal.half_pos

protected theorem one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 :=
  ENNReal.inv_lt_one.2 <| one_lt_two
#align ennreal.one_half_lt_one ENNReal.one_half_lt_one

protected theorem half_lt_self (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a := by
  lift a to ℝ≥0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two, ← coe_div, coe_lt_coe]
  exacts [NNReal.half_lt_self hz, two_ne_zero' _]
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

/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)`. -/
@[simps! apply_coe]
def orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (x.1⁻¹ - 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : ℝ≥0∞) ≤ x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, Subtype.coe_mk, tsub_add_cancel_of_le this]
#align ennreal.order_iso_Iic_one_birational ENNReal.orderIsoIicOneBirational

@[simp]
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : ℝ≥0∞)) :
    orderIsoIicOneBirational.symm x = (x.1⁻¹ - 1)⁻¹ :=
  rfl
#align ennreal.order_iso_Iic_one_birational_symm_apply ENNReal.orderIsoIicOneBirational_symm_apply

/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps! apply_coe]
def orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
      invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 <| coe_toNNReal_le_self.trans x.2⟩
      left_inv := fun x => Subtype.ext <| toNNReal_coe
      right_inv := fun x => Subtype.ext <| coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }
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

theorem exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n > 0, b < (n : ℕ) * a :=
  let ⟨n, hn⟩ := ENNReal.exists_nat_gt (div_lt_top hb ha).ne
  ⟨n, Nat.cast_pos.1 ((zero_le _).trans_lt hn), by
    rwa [← ENNReal.div_lt_iff (Or.inl ha) (Or.inr hb)]⟩
#align ennreal.exists_nat_pos_mul_gt ENNReal.exists_nat_pos_mul_gt

theorem exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n : ℕ, b < n * a :=
  (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right
#align ennreal.exists_nat_mul_gt ENNReal.exists_nat_mul_gt

theorem exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
    ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b := by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  use n, npos
  rw [← ENNReal.div_eq_inv_mul]
  exact div_lt_of_lt_mul' hn
#align ennreal.exists_nat_pos_inv_mul_lt ENNReal.exists_nat_pos_inv_mul_lt

theorem exists_nnreal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ↑(n : ℝ≥0) * a < b := by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : ℝ≥0)⁻¹
  simp [*, npos.ne', zero_lt_one]
#align ennreal.exists_nnreal_pos_mul_lt ENNReal.exists_nnreal_pos_mul_lt

theorem exists_inv_two_pow_lt (ha : a ≠ 0) : ∃ n : ℕ, 2⁻¹ ^ n < a := by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine' ⟨n, lt_trans _ hn⟩
  rw [← ENNReal.inv_pow, ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow
#align ennreal.exists_inv_two_pow_lt ENNReal.exists_inv_two_pow_lt

@[simp, norm_cast]
theorem coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r ^ n) : ℝ≥0∞) = (r : ℝ≥0∞) ^ n := by
  cases' n with n n
  · simp only [Int.ofNat_eq_coe, coe_pow, zpow_ofNat]
  · have : r ^ n.succ ≠ 0 := pow_ne_zero (n + 1) hr
    simp only [zpow_negSucc, coe_inv this, coe_pow]
#align ennreal.coe_zpow ENNReal.coe_zpow

theorem zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n := by
  cases n
  · exact ENNReal.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, zpow_negSucc, Ne.def, not_false, ENNReal.inv_pos, false_and,
      not_false_eq_true]
#align ennreal.zpow_pos ENNReal.zpow_pos

theorem zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ := by
  cases n
  · exact ENNReal.pow_lt_top h'a.lt_top _
  · simp only [ENNReal.pow_pos ha.bot_lt, zpow_negSucc, inv_lt_top]
#align ennreal.zpow_lt_top ENNReal.zpow_lt_top

theorem exists_mem_Ico_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne.def, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
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
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1) := by
    refine' NNReal.exists_mem_Ioc_zpow _ (one_lt_coe_iff.1 hy)
    simpa only [Ne.def, coe_eq_zero] using hx
  refine' ⟨n, _, _⟩
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_lt_coe]
  · rwa [← ENNReal.coe_zpow A, ENNReal.coe_le_coe]
#align ennreal.exists_mem_Ioc_zpow ENNReal.exists_mem_Ioc_zpow

theorem Ioo_zero_top_eq_iUnion_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
    Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ n : ℤ, Ico (y ^ n) (y ^ (n + 1)) := by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _
#align ennreal.Ioo_zero_top_eq_Union_Ico_zpow ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow

@[gcongr]
theorem zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  induction' a with a a <;> induction' b with b b
  · simp only [Int.ofNat_eq_coe, zpow_ofNat]
    exact pow_le_pow_right hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.ofNat_nonneg _)
  · simp only [zpow_negSucc, Int.ofNat_eq_coe, zpow_ofNat]
    refine' (ENNReal.inv_le_one.2 _).trans _ <;> exact one_le_pow_of_one_le' hx _
  · simp only [zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_le_pow_right hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.ofNat_add, Int.ofNat_one, Int.negSucc_eq] using
      h
#align ennreal.zpow_le_of_le ENNReal.zpow_le_of_le

theorem monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : Monotone ((x ^ ·) : ℤ → ℝ≥0∞) := fun _ _ h =>
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
  simp only [← ENNReal.coe_sub, ENNReal.coe_toReal, NNReal.coe_sub (ENNReal.coe_le_coe.mp h)]
#align ennreal.to_real_sub_of_le ENNReal.toReal_sub_of_le

theorem le_toReal_sub {a b : ℝ≥0∞} (hb : b ≠ ∞) : a.toReal - b.toReal ≤ (a - b).toReal := by
  lift b to ℝ≥0 using hb
  induction a using recTopCoe
  · simp
  · simp only [← coe_sub, NNReal.sub_def, Real.coe_toNNReal', coe_toReal]
    exact le_max_left _ _
#align ennreal.le_to_real_sub ENNReal.le_toReal_sub

theorem toReal_add_le : (a + b).toReal ≤ a.toReal + b.toReal :=
  if ha : a = ∞ then by simp only [ha, top_add, top_toReal, zero_add, toReal_nonneg]
  else
    if hb : b = ∞ then by simp only [hb, add_top, top_toReal, add_zero, toReal_nonneg]
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
  (toReal_le_toReal (ne_top_of_le_ne_top hb h) hb).2 h
#align ennreal.to_real_mono ENNReal.toReal_mono

-- porting note: new lemma
theorem toReal_mono' (h : a ≤ b) (ht : b = ∞ → a = ∞) : a.toReal ≤ b.toReal := by
  rcases eq_or_ne a ∞ with rfl | ha
  · exact toReal_nonneg
  · exact toReal_mono (mt ht ha) h

@[simp]
theorem toReal_lt_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal < b.toReal ↔ a < b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast
#align ennreal.to_real_lt_to_real ENNReal.toReal_lt_toReal

theorem toReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toReal < b.toReal :=
  (toReal_lt_toReal h.ne_top hb).2 h
#align ennreal.to_real_strict_mono ENNReal.toReal_strict_mono

theorem toNNReal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toNNReal ≤ b.toNNReal :=
  toReal_mono hb h
#align ennreal.to_nnreal_mono ENNReal.toNNReal_mono

-- porting note: new lemma
/-- If `a ≤ b + c` and `a = ∞` whenever `b = ∞` or `c = ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add' (hle : a ≤ b + c) (hb : b = ∞ → a = ∞) (hc : c = ∞ → a = ∞) :
    a.toReal ≤ b.toReal + c.toReal := by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

-- porting note: new lemma
/-- If `a ≤ b + c`, `b ≠ ∞`, and `c ≠ ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add (hle : a ≤ b + c) (hb : b ≠ ∞) (hc : c ≠ ∞) :
    a.toReal ≤ b.toReal + c.toReal :=
  toReal_le_add' hle (flip absurd hb) (flip absurd hc)

@[simp]
theorem toNNReal_le_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal ≤ b.toNNReal ↔ a ≤ b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_le_coe], toNNReal_mono hb⟩
#align ennreal.to_nnreal_le_to_nnreal ENNReal.toNNReal_le_toNNReal

theorem toNNReal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toNNReal < b.toNNReal := by
  simpa [← ENNReal.coe_lt_coe, hb, h.ne_top]
#align ennreal.to_nnreal_strict_mono ENNReal.toNNReal_strict_mono

@[simp]
theorem toNNReal_lt_toNNReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNNReal < b.toNNReal ↔ a < b :=
  ⟨fun h => by rwa [← coe_toNNReal ha, ← coe_toNNReal hb, coe_lt_coe], toNNReal_strict_mono hb⟩
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
  induction a using recTopCoe <;> simp
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

lemma ofReal_le_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p ≤ .ofReal q ↔ p ≤ q ∨ p ≤ 0 :=
  coe_le_coe.trans Real.toNNReal_le_toNNReal_iff'

lemma ofReal_lt_ofReal_iff' {p q : ℝ} : ENNReal.ofReal p < .ofReal q ↔ p < q ∧ 0 < q :=
  coe_lt_coe.trans Real.toNNReal_lt_toNNReal_iff'

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

alias ⟨_, ofReal_of_nonpos⟩ := ofReal_eq_zero
#align ennreal.of_real_of_nonpos ENNReal.ofReal_of_nonpos

@[simp]
lemma ofReal_lt_nat_cast {p : ℝ} {n : ℕ} (hn : n ≠ 0) : ENNReal.ofReal p < n ↔ p < n := by
  exact mod_cast ofReal_lt_ofReal_iff (Nat.cast_pos.2 hn.bot_lt)

@[simp]
lemma ofReal_lt_one {p : ℝ} : ENNReal.ofReal p < 1 ↔ p < 1 := by
  exact mod_cast ofReal_lt_nat_cast one_ne_zero

@[simp]
lemma ofReal_lt_ofNat {p : ℝ} {n : ℕ} [h : n.AtLeastTwo] :
    ENNReal.ofReal p < no_index (OfNat.ofNat n) ↔ p < OfNat.ofNat n :=
  ofReal_lt_nat_cast h.ne_zero

@[simp]
lemma nat_cast_le_ofReal {n : ℕ} {p : ℝ} (hn : n ≠ 0) : n ≤ ENNReal.ofReal p ↔ n ≤ p := by
  simp only [← not_lt, ofReal_lt_nat_cast hn]

@[simp]
lemma one_le_ofReal {p : ℝ} : 1 ≤ ENNReal.ofReal p ↔ 1 ≤ p := by
  exact mod_cast nat_cast_le_ofReal one_ne_zero

@[simp]
lemma ofNat_le_ofReal {n : ℕ} [h : n.AtLeastTwo] {p : ℝ} :
    no_index (OfNat.ofNat n) ≤ ENNReal.ofReal p ↔ OfNat.ofNat n ≤ p :=
  nat_cast_le_ofReal h.ne_zero

@[simp]
lemma ofReal_le_nat_cast {r : ℝ} {n : ℕ} : ENNReal.ofReal r ≤ n ↔ r ≤ n :=
  coe_le_coe.trans Real.toNNReal_le_nat_cast

@[simp]
lemma ofReal_le_one {r : ℝ} : ENNReal.ofReal r ≤ 1 ↔ r ≤ 1 :=
  coe_le_coe.trans Real.toNNReal_le_one

@[simp]
lemma ofReal_le_ofNat {r : ℝ} {n : ℕ} [n.AtLeastTwo] :
    ENNReal.ofReal r ≤ no_index (OfNat.ofNat n) ↔ r ≤ OfNat.ofNat n :=
  ofReal_le_nat_cast

@[simp]
lemma nat_cast_lt_ofReal {n : ℕ} {r : ℝ} : n < ENNReal.ofReal r ↔ n < r :=
  coe_lt_coe.trans Real.nat_cast_lt_toNNReal

@[simp]
lemma one_lt_ofReal {r : ℝ} : 1 < ENNReal.ofReal r ↔ 1 < r := coe_lt_coe.trans Real.one_lt_toNNReal

@[simp]
lemma ofNat_lt_ofReal {n : ℕ} [n.AtLeastTwo] {r : ℝ} :
    no_index (OfNat.ofNat n) < ENNReal.ofReal r ↔ OfNat.ofNat n < r :=
  nat_cast_lt_ofReal

@[simp]
lemma ofReal_eq_nat_cast {r : ℝ} {n : ℕ} (h : n ≠ 0) : ENNReal.ofReal r = n ↔ r = n :=
  ENNReal.coe_eq_coe.trans <| Real.toNNReal_eq_nat_cast h

@[simp]
lemma ofReal_eq_one {r : ℝ} : ENNReal.ofReal r = 1 ↔ r = 1 :=
  ENNReal.coe_eq_coe.trans Real.toNNReal_eq_one

@[simp]
lemma ofReal_eq_ofNat {r : ℝ} {n : ℕ} [h : n.AtLeastTwo] :
    ENNReal.ofReal r = no_index (OfNat.ofNat n) ↔ r = OfNat.ofNat n :=
  ofReal_eq_nat_cast h.ne_zero

theorem ofReal_sub (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q := by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ofReal_le_ofReal h)]
  refine' ENNReal.eq_sub_of_add_eq ofReal_ne_top _
  rw [← ofReal_add (sub_nonneg_of_le h) hq, sub_add_cancel]
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

theorem ofReal_lt_coe_iff {a : ℝ} {b : ℝ≥0} (ha : 0 ≤ a) : ENNReal.ofReal a < b ↔ a < b :=
  (ofReal_lt_iff_lt_toReal ha coe_ne_top).trans <| by rw [coe_toReal]

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

theorem toReal_lt_of_lt_ofReal {b : ℝ} (h : a < ENNReal.ofReal b) : ENNReal.toReal a < b :=
  (lt_ofReal_iff_toReal_lt h.ne_top).1 h

theorem ofReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  simp only [ENNReal.ofReal, ← coe_mul, Real.toNNReal_mul hp]
#align ennreal.of_real_mul ENNReal.ofReal_mul

theorem ofReal_mul' {p q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q := by
  rw [mul_comm, ofReal_mul hq, mul_comm]
#align ennreal.of_real_mul' ENNReal.ofReal_mul'

theorem ofReal_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) : ENNReal.ofReal (p ^ n) = ENNReal.ofReal p ^ n :=
  by rw [ofReal_eq_coe_nnreal hp, ← coe_pow, ← ofReal_coe_nnreal, NNReal.coe_pow, NNReal.coe_mk]
#align ennreal.of_real_pow ENNReal.ofReal_pow

theorem ofReal_nsmul {x : ℝ} {n : ℕ} : ENNReal.ofReal (n • x) = n • ENNReal.ofReal x := by
  simp only [nsmul_eq_mul, ← ofReal_coe_nat n, ← ofReal_mul n.cast_nonneg]
#align ennreal.of_real_nsmul ENNReal.ofReal_nsmul

theorem ofReal_inv_of_pos {x : ℝ} (hx : 0 < x) : (ENNReal.ofReal x)⁻¹ = ENNReal.ofReal x⁻¹ := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ← @coe_inv (Real.toNNReal x) (by simp [hx]), coe_eq_coe,
    ← Real.toNNReal_inv]
#align ennreal.of_real_inv_of_pos ENNReal.ofReal_inv_of_pos

theorem ofReal_div_of_pos {x y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (x / y) = ENNReal.ofReal x / ENNReal.ofReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy.le), ofReal_inv_of_pos hy]
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
  change ((a : ℝ≥0∞) * b).toNNReal = a * b.toNNReal
  simp only [ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
#align ennreal.smul_to_nnreal ENNReal.smul_toNNReal

-- porting note: todo: upgrade to `→*₀`
/-- `ENNReal.toNNReal` as a `MonoidHom`. -/
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
theorem toNNReal_prod {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i in s, f i).toNNReal = ∏ i in s, (f i).toNNReal :=
  map_prod toNNRealHom _ _
#align ennreal.to_nnreal_prod ENNReal.toNNReal_prod

-- porting note: todo: upgrade to `→*₀`
/-- `ENNReal.toReal` as a `MonoidHom`. -/
def toRealHom : ℝ≥0∞ →* ℝ :=
  (NNReal.toRealHom : ℝ≥0 →* ℝ).comp toNNRealHom
#align ennreal.to_real_hom ENNReal.toRealHom

@[simp]
theorem toReal_mul : (a * b).toReal = a.toReal * b.toReal :=
  toRealHom.map_mul a b
#align ennreal.to_real_mul ENNReal.toReal_mul

theorem toReal_nsmul (a : ℝ≥0∞) (n : ℕ) : (n • a).toReal = n • a.toReal := by simp

@[simp]
theorem toReal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toReal = a.toReal ^ n :=
  toRealHom.map_pow a n
#align ennreal.to_real_pow ENNReal.toReal_pow

@[simp]
theorem toReal_prod {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i in s, f i).toReal = ∏ i in s, (f i).toReal :=
  map_prod toRealHom _ _
#align ennreal.to_real_prod ENNReal.toReal_prod

theorem toReal_ofReal_mul (c : ℝ) (a : ℝ≥0∞) (h : 0 ≤ c) :
    ENNReal.toReal (ENNReal.ofReal c * a) = c * ENNReal.toReal a := by
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h]
#align ennreal.to_real_of_real_mul ENNReal.toReal_ofReal_mul

theorem toReal_mul_top (a : ℝ≥0∞) : ENNReal.toReal (a * ∞) = 0 := by
  rw [toReal_mul, top_toReal, mul_zero]
#align ennreal.to_real_mul_top ENNReal.toReal_mul_top

theorem toReal_top_mul (a : ℝ≥0∞) : ENNReal.toReal (∞ * a) = 0 := by
  rw [mul_comm]
  exact toReal_mul_top _
#align ennreal.to_real_top_mul ENNReal.toReal_top_mul

theorem toReal_eq_toReal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal = b.toReal ↔ a = b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  simp only [coe_eq_coe, NNReal.coe_eq, coe_toReal]
#align ennreal.to_real_eq_to_real ENNReal.toReal_eq_toReal

theorem toReal_smul (r : ℝ≥0) (s : ℝ≥0∞) : (r • s).toReal = r • s.toReal := by
  rw [ENNReal.smul_def, smul_eq_mul, toReal_mul, coe_toReal]
  rfl
#align ennreal.to_real_smul ENNReal.toReal_smul

protected theorem trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal := by
  simpa only [or_iff_not_imp_left] using toReal_pos
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
  haveI : p = ⊤ ∨ 0 < p.toReal ∧ 1 ≤ p.toReal := by
    simpa using ENNReal.trichotomy₂ (Fact.out : 1 ≤ p)
  this.imp_right fun h => h.2
#align ennreal.dichotomy ENNReal.dichotomy

theorem toReal_pos_iff_ne_top (p : ℝ≥0∞) [Fact (1 ≤ p)] : 0 < p.toReal ↔ p ≠ ∞ :=
  ⟨fun h hp =>
    have : (0 : ℝ) ≠ 0 := top_toReal ▸ (hp ▸ h.ne : 0 ≠ ∞.toReal)
    this rfl,
    fun h => zero_lt_one.trans_le (p.dichotomy.resolve_left h)⟩
#align ennreal.to_real_pos_iff_ne_top ENNReal.toReal_pos_iff_ne_top

theorem toNNReal_inv (a : ℝ≥0∞) : a⁻¹.toNNReal = a.toNNReal⁻¹ := by
  induction' a using recTopCoe with a; · simp
  rcases eq_or_ne a 0 with (rfl | ha); · simp
  rw [← coe_inv ha, toNNReal_coe, toNNReal_coe]
#align ennreal.to_nnreal_inv ENNReal.toNNReal_inv

theorem toNNReal_div (a b : ℝ≥0∞) : (a / b).toNNReal = a.toNNReal / b.toNNReal := by
  rw [div_eq_mul_inv, toNNReal_mul, toNNReal_inv, div_eq_mul_inv]
#align ennreal.to_nnreal_div ENNReal.toNNReal_div

theorem toReal_inv (a : ℝ≥0∞) : a⁻¹.toReal = a.toReal⁻¹ := by
  simp only [ENNReal.toReal, toNNReal_inv, NNReal.coe_inv]
#align ennreal.to_real_inv ENNReal.toReal_inv

theorem toReal_div (a b : ℝ≥0∞) : (a / b).toReal = a.toReal / b.toReal := by
  rw [div_eq_mul_inv, toReal_mul, toReal_inv, div_eq_mul_inv]
#align ennreal.to_real_div ENNReal.toReal_div

theorem ofReal_prod_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∏ i in s, f i) = ∏ i in s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_prod, coe_eq_coe]
  exact Real.toNNReal_prod_of_nonneg hf
#align ennreal.of_real_prod_of_nonneg ENNReal.ofReal_prod_of_nonneg

#noalign ennreal.to_nnreal_bit0
#noalign ennreal.to_nnreal_bit1
#noalign ennreal.to_real_bit0
#noalign ennreal.to_real_bit1
#noalign ennreal.of_real_bit0
#noalign ennreal.of_real_bit1

end Real

section iInf

variable {ι : Sort*} {f g : ι → ℝ≥0∞}

theorem toNNReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toNNReal = ⨅ i, (f i).toNNReal := by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, top_toNNReal, NNReal.iInf_empty]
  · lift f to ι → ℝ≥0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]
#align ennreal.to_nnreal_infi ENNReal.toNNReal_iInf

theorem toNNReal_sInf (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  -- porting note: `← sInf_image'` had to be replaced by `← image_eq_range` as the lemmas are used
  -- in a different order.
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using (toNNReal_iInf hf)
#align ennreal.to_nnreal_Inf ENNReal.toNNReal_sInf

theorem toNNReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toNNReal = ⨆ i, (f i).toNNReal := by
  lift f to ι → ℝ≥0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, top_toNNReal]
#align ennreal.to_nnreal_supr ENNReal.toNNReal_iSup

theorem toNNReal_sSup (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toNNReal = sSup (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  -- porting note: `← sSup_image'` had to be replaced by `← image_eq_range` as the lemmas are used
  -- in a different order.
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using (toNNReal_iSup hf)
#align ennreal.to_nnreal_Sup ENNReal.toNNReal_sSup

theorem toReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toReal = ⨅ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]
#align ennreal.to_real_infi ENNReal.toReal_iInf

theorem toReal_sInf (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toReal = sInf (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]
#align ennreal.to_real_Inf ENNReal.toReal_sInf

theorem toReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toReal = ⨆ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]
#align ennreal.to_real_supr ENNReal.toReal_iSup

theorem toReal_sSup (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toReal = sSup (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]
#align ennreal.to_real_Sup ENNReal.toReal_sSup

theorem iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)
#align ennreal.infi_add ENNReal.iInf_add

theorem iSup_sub : (⨆ i, f i) - a = ⨆ i, f i - a :=
  le_antisymm (tsub_le_iff_right.2 <| iSup_le fun i => tsub_le_iff_right.1 <| le_iSup (f · - a) i)
    (iSup_le fun _ => tsub_le_tsub (le_iSup _ _) (le_refl a))
#align ennreal.supr_sub ENNReal.iSup_sub

theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine' eq_of_forall_ge_iff fun c => _
  rw [tsub_le_iff_right, add_comm, iInf_add]
  simp [tsub_le_iff_right, sub_eq_add_neg, add_comm]
#align ennreal.sub_infi ENNReal.sub_iInf

theorem sInf_add {s : Set ℝ≥0∞} : sInf s + a = ⨅ b ∈ s, b + a := by simp [sInf_eq_iInf, iInf_add]
#align ennreal.Inf_add ENNReal.sInf_add

theorem add_iInf {a : ℝ≥0∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm, iInf_add]; simp [add_comm]
#align ennreal.add_infi ENNReal.add_iInf

theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun a => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]
#align ennreal.infi_add_infi ENNReal.iInf_add_iInf

theorem iInf_sum {f : ι → α → ℝ≥0∞} {s : Finset α} [Nonempty ι]
    (h : ∀ (t : Finset α) (i j : ι), ∃ k, ∀ a ∈ t, f k a ≤ f i a ∧ f k a ≤ f j a) :
    ⨅ i, ∑ a in s, f i a = ∑ a in s, ⨅ i, f i a := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp only [Finset.sum_empty, ciInf_const]
  · simp only [Finset.sum_cons, ← ih]
    refine (iInf_add_iInf fun i j => ?_).symm
    refine (h (Finset.cons a s ha) i j).imp fun k hk => ?_
    rw [Finset.forall_mem_cons] at hk
    exact add_le_add hk.1.1 (Finset.sum_le_sum fun a ha => (hk.2 a ha).2)
#align ennreal.infi_sum ENNReal.iInf_sum

/-- If `x ≠ 0` and `x ≠ ∞`, then right multiplication by `x` maps infimum to infimum.
See also `ENNReal.iInf_mul` that assumes `[Nonempty ι]` but does not require `x ≠ 0`. -/
theorem iInf_mul_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
    iInf f * x = ⨅ i, f i * x :=
  le_antisymm mul_right_mono.map_iInf_le
    ((ENNReal.div_le_iff_le_mul (Or.inl h0) <| Or.inl h).mp <|
      le_iInf fun _ => (ENNReal.div_le_iff_le_mul (Or.inl h0) <| Or.inl h).mpr <| iInf_le _ _)
#align ennreal.infi_mul_of_ne ENNReal.iInf_mul_of_ne

/-- If `x ≠ ∞`, then right multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ENNReal.iInf_mul_of_ne` that assumes `x ≠ 0` but does not require `[Nonempty ι]`. -/
theorem iInf_mul {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
    iInf f * x = ⨅ i, f i * x := by
  by_cases h0 : x = 0
  · simp only [h0, mul_zero, iInf_const]
  · exact iInf_mul_of_ne h0 h
#align ennreal.infi_mul ENNReal.iInf_mul

/-- If `x ≠ ∞`, then left multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ENNReal.mul_iInf_of_ne` that assumes `x ≠ 0` but does not require `[Nonempty ι]`. -/
theorem mul_iInf {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
    x * iInf f = ⨅ i, x * f i := by simpa only [mul_comm] using iInf_mul h
#align ennreal.mul_infi ENNReal.mul_iInf

/-- If `x ≠ 0` and `x ≠ ∞`, then left multiplication by `x` maps infimum to infimum.
See also `ENNReal.mul_iInf` that assumes `[Nonempty ι]` but does not require `x ≠ 0`. -/
theorem mul_iInf_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
    x * iInf f = ⨅ i, x * f i := by simpa only [mul_comm] using iInf_mul_of_ne h0 h
#align ennreal.mul_infi_of_ne ENNReal.mul_iInf_of_ne

/-! `supr_mul`, `mul_supr` and variants are in `Topology.Instances.ENNReal`. -/

end iInf

section iSup

@[simp]
theorem iSup_eq_zero {ι : Sort*} {f : ι → ℝ≥0∞} : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  iSup_eq_bot
#align ennreal.supr_eq_zero ENNReal.iSup_eq_zero

@[simp]
theorem iSup_zero_eq_zero {ι : Sort*} : ⨆ _ : ι, (0 : ℝ≥0∞) = 0 := by simp
#align ennreal.supr_zero_eq_zero ENNReal.iSup_zero_eq_zero

theorem sup_eq_zero {a b : ℝ≥0∞} : a ⊔ b = 0 ↔ a = 0 ∧ b = 0 :=
  sup_eq_bot_iff
#align ennreal.sup_eq_zero ENNReal.sup_eq_zero

theorem iSup_coe_nat : ⨆ n : ℕ, (n : ℝ≥0∞) = ∞ :=
  (iSup_eq_top _).2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)
#align ennreal.supr_coe_nat ENNReal.iSup_coe_nat

end iSup

end ENNReal

open ENNReal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0} {u : Set ℝ≥0∞}

theorem preimage_coe_nnreal_ennreal (h : u.OrdConnected) : ((↑) ⁻¹' u : Set ℝ≥0).OrdConnected :=
  h.preimage_mono ENNReal.coe_mono
#align set.ord_connected.preimage_coe_nnreal_ennreal Set.OrdConnected.preimage_coe_nnreal_ennreal

-- porting note: todo: generalize to `WithTop`
theorem image_coe_nnreal_ennreal (h : t.OrdConnected) : ((↑) '' t : Set ℝ≥0∞).OrdConnected := by
  refine' ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => _⟩
  rcases ENNReal.le_coe_iff.1 hz.2 with ⟨z, rfl, -⟩
  exact mem_image_of_mem _ (h.out hx hy ⟨ENNReal.coe_le_coe.1 hz.1, ENNReal.coe_le_coe.1 hz.2⟩)
#align set.ord_connected.image_coe_nnreal_ennreal Set.OrdConnected.image_coe_nnreal_ennreal

theorem preimage_ennreal_ofReal (h : u.OrdConnected) : (ENNReal.ofReal ⁻¹' u).OrdConnected :=
  h.preimage_coe_nnreal_ennreal.preimage_real_toNNReal
#align set.ord_connected.preimage_ennreal_of_real Set.OrdConnected.preimage_ennreal_ofReal

theorem image_ennreal_ofReal (h : s.OrdConnected) : (ENNReal.ofReal '' s).OrdConnected := by
  simpa only [image_image] using h.image_real_toNNReal.image_coe_nnreal_ennreal
#align set.ord_connected.image_ennreal_of_real Set.OrdConnected.image_ennreal_ofReal

end OrdConnected

end Set

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNReal.toReal`. -/
@[positivity ENNReal.toReal _]
def evalENNRealtoReal : PositivityExt where eval {_ _} _zα _pα e := do
  let (.app (f : Q(ENNReal → Real)) (a : Q(ENNReal))) ← whnfR e | throwError "not ENNReal.toReal"
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(ENNReal.toReal)
  pure (.nonnegative (q(@ENNReal.toReal_nonneg $a) : Expr))

/-- Extension for the `positivity` tactic: `ENNReal.toReal`. -/
@[positivity ENNReal.ofReal _]
def evalENNRealOfReal : PositivityExt where eval {_ _} _zα _pα e := do
  let (.app (f : Q(Real → ENNReal)) (a : Q(Real))) ← whnfR e | throwError "not ENNReal.ofReal"
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(ENNReal.ofReal)
  let zα' ← synthInstanceQ (q(Zero Real) : Q(Type))
  let pα' ← synthInstanceQ (q(PartialOrder Real) : Q(Type))
  let ra ← core zα' pα' a
  assertInstancesCommute
  match ra with
  | .positive pa => pure (.positive (q(Iff.mpr (@ENNReal.ofReal_pos $a) $pa) : Expr))
  | _ => pure .none

/-- Extension for the `positivity` tactic: `ENNReal.ofNNReal`. -/
@[positivity ENNReal.ofNNReal _]
def evalENNRealOfNNReal : PositivityExt where eval {_ _} _zα _pα e := do
  let (.app (f : Q(NNReal → ENNReal)) (a : Q(NNReal))) ← whnfR e | throwError "not ENNReal.ofNNReal"
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(ENNReal.ofNNReal)
  let zα' ← synthInstanceQ (q(Zero NNReal) : Q(Type))
  let pα' ← synthInstanceQ (q(PartialOrder NNReal) : Q(Type))
  let ra ← core zα' pα' a
  assertInstancesCommute
  match ra with
  | .positive pa => pure (.positive (q(Iff.mpr (@ENNReal.coe_pos $a) $pa) : Expr))
  | _ => pure .none

end Mathlib.Meta.Positivity

/-!
### Deprecated lemmas

Those lemmas have been deprecated on the 2023/12/23.
-/

@[deprecated] protected alias ENNReal.le_inv_smul_iff_of_pos := le_inv_smul_iff_of_pos
@[deprecated] protected alias ENNReal.inv_smul_le_iff_of_pos := inv_smul_le_iff_of_pos
