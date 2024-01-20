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

#align_import data.real.ennreal from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

/-!
# Extended non-negative reals

We define `ENNReal = ℝ≥0∞ := WithTop ℝ≥0` to be the type of extended nonnegative real numbers,
i.e., the interval `[0, +∞]`. This type is used as the codomain of a `MeasureTheory.Measure`,
and of the extended distance `edist` in an `EMetricSpace`.

In this file we set up many of the instances on `ℝ≥0∞`, and provide relationships between `ℝ≥0∞` and
`ℝ≥0`, and between `ℝ≥0∞` and `ℝ`. In particular, we provide a coercion from `ℝ≥0` to `ℝ≥0∞` as well
as functions `ENNReal.toNNReal`, `ENNReal.ofReal` and `ENNReal.toReal`, all of which take the value
zero wherever they cannot be the identity. Also included is the relationship between `ℝ≥0∞` and `ℕ`.
The interaction of these functions, especially `ENNReal.ofReal` and `ENNReal.toReal`, with the
algebraic and lattice structure can be found in `Data.ENNReal.Real`

This file proves many of the order properties of `ℝ≥0∞`, with the exception of the ways those relate
to the algebraic structure, which are included in `Data.ENNReal.Operations`. The definition and
properties of the inversion and division are included in `Data.ENNReal.Inv`.

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
* `ℝ≥0`: the type of nonnegative real numbers `[0, ∞)`; defined in `Data.Real.NNReal`;
* `∞`: a localized notation in `ℝ≥0∞` for `⊤ : ℝ≥0∞`.

-/


open Set BigOperators NNReal

variable {α : Type*}

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

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ≥0∞) = s.indicator (fun x => ↑(f x)) a :=
  (ofNNRealHom : ℝ≥0 →+ ℝ≥0∞).map_indicator _ _ _
#align ennreal.coe_indicator ENNReal.coe_indicator

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
