/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard

! This file was ported from Lean 3 source module data.real.ereal
! leanprover-community/mathlib commit afdb4fa3b32d41106a4a09b371ce549ad7958abd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Sign

/-!
# The extended reals [-∞, ∞].

This file defines `ereal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥. It is implemented as `with_bot (with_top ℝ)`

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.

An ad hoc addition is defined, for which `ereal` is an `add_comm_monoid`, and even an ordered one
(if `a ≤ a'` and `b ≤ b'` then `a + b ≤ a' + b'`).
Note however that addition is badly behaved at `(⊥, ⊤)` and `(⊤, ⊥)` so this can not be upgraded
to a group structure. Our choice is that `⊥ + ⊤ = ⊤ + ⊥ = ⊥`, to make sure that the exponential
and the logarithm between `ereal` and `ℝ≥0∞` respect the operations (notice that the
convention `0 * ∞ = 0` on `ℝ≥0∞` is enforced by measure theory).

An ad hoc subtraction is then defined by `x - y = x + (-y)`. It does not have nice properties,
but it is sometimes convenient to have.

An ad hoc multiplication is defined, for which `ereal` is a `comm_monoid_with_zero`. We make the
choice that `0 * x = x * 0 = 0` for any `x` (while the other cases are defined non-ambiguously).
This does not distribute with addition, as `⊥ = ⊥ + ⊤ = 1*⊥ + (-1)*⊥ ≠ (1 - 1) * ⊥ = 0 * ⊥ = 0`.

`ereal` is a `complete_linear_order`; this is deduced by type class inference from
the fact that `with_bot (with_top L)` is a complete linear order if `L` is
a conditionally complete linear order.

Coercions from `ℝ` and from `ℝ≥0∞` are registered, and their basic properties are proved. The main
one is the real coercion, and is usually referred to just as `coe` (lemmas such as
`ereal.coe_add` deal with this coercion). The one from `ennreal` is usually called `coe_ennreal`
in the `ereal` namespace.

We define an absolute value `ereal.abs` from `ereal` to `ℝ≥0∞`. Two elements of `ereal` coincide
if and only if they have the same absolute value and the same sign.

## Tags

real, ereal, complete lattice
-/


open Function ENNReal NNReal

noncomputable section

/-- ereal : The type `[-∞, ∞]` -/
def EReal :=
  WithBot (WithTop ℝ)
  deriving Bot, Zero, One, Nontrivial, AddMonoid, SupSet, InfSet,
    CompleteLinearOrder, LinearOrderedAddCommMonoid, ZeroLEOneClass
#align ereal EReal

/-- The canonical inclusion froms reals to ereals. Do not use directly: as this is registered as
a coercion, use the coercion instead. -/
def Real.toEReal : ℝ → EReal :=
  some ∘ some
#align real.to_ereal Real.toEReal

namespace EReal

-- things unify with `with_bot.decidable_lt` later if we we don't provide this explicitly.
instance decidableLt : DecidableRel ((· < ·) : EReal → EReal → Prop) :=
  WithBot.decidableLT
#align ereal.decidable_lt EReal.decidableLt

-- TODO: Provide explicitly, otherwise it is inferred noncomputably from `complete_linear_order`
instance : Top EReal :=
  ⟨some ⊤⟩

instance : Coe ℝ EReal :=
  ⟨Real.toEReal⟩

theorem coe_strictMono : StrictMono (coe : ℝ → EReal) :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono
#align ereal.coe_strict_mono EReal.coe_strictMono

theorem coe_injective : Injective (coe : ℝ → EReal) :=
  coe_strictMono.Injective
#align ereal.coe_injective EReal.coe_injective

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℝ} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_strictMono.le_iff_le
#align ereal.coe_le_coe_iff EReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : ℝ} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_strictMono.lt_iff_lt
#align ereal.coe_lt_coe_iff EReal.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℝ} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_injective.eq_iff
#align ereal.coe_eq_coe_iff EReal.coe_eq_coe_iff

protected theorem coe_ne_coe_iff {x y : ℝ} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_injective.ne_iff
#align ereal.coe_ne_coe_iff EReal.coe_ne_coe_iff

/-- The canonical map from nonnegative extended reals to extended reals -/
def ENNReal.toEReal : ℝ≥0∞ → EReal
  | ⊤ => ⊤
  | some x => x.1
#align ennreal.to_ereal ENNReal.toEReal

instance hasCoeENNReal : Coe ℝ≥0∞ EReal :=
  ⟨ENNReal.toEReal⟩
#align ereal.has_coe_ennreal EReal.hasCoeENNReal

instance : Inhabited EReal :=
  ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : ℝ) : EReal) = 0 :=
  rfl
#align ereal.coe_zero EReal.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : ℝ) : EReal) = 1 :=
  rfl
#align ereal.coe_one EReal.coe_one

/-- A recursor for `ereal` in terms of the coercion.

A typical invocation looks like `induction x using ereal.rec`. Note that using `induction`
directly will unfold `ereal` to `option` which is undesirable.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim]
protected def rec {C : EReal → Sort _} (h_bot : C ⊥) (h_real : ∀ a : ℝ, C a) (h_top : C ⊤) :
    ∀ a : EReal, C a
  | ⊥ => h_bot
  | (a : ℝ) => h_real a
  | ⊤ => h_top
#align ereal.rec EReal.rec

/-- The multiplication on `ereal`. Our definition satisfies `0 * x = x * 0 = 0` for any `x`, and
picks the only sensible value elsewhere. -/
protected def mul : EReal → EReal → EReal
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊥, (y : ℝ) => if 0 < y then ⊥ else if y = 0 then 0 else ⊤
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | ⊤, (y : ℝ) => if 0 < y then ⊤ else if y = 0 then 0 else ⊥
  | (x : ℝ), ⊤ => if 0 < x then ⊤ else if x = 0 then 0 else ⊥
  | (x : ℝ), ⊥ => if 0 < x then ⊥ else if x = 0 then 0 else ⊤
  | (x : ℝ), (y : ℝ) => (x * y : ℝ)
#align ereal.mul EReal.mul

instance : Mul EReal :=
  ⟨EReal.mul⟩

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
theorem induction₂ {P : EReal → EReal → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : ∀ x : ℝ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥) (zero_top : P 0 ⊤)
    (coe_coe : ∀ x y : ℝ, P x y) (zero_bot : P 0 ⊥) (neg_top : ∀ x : ℝ, x < 0 → P x ⊤)
    (neg_bot : ∀ x : ℝ, x < 0 → P x ⊥) (bot_top : P ⊥ ⊤) (bot_pos : ∀ x : ℝ, 0 < x → P ⊥ x)
    (bot_zero : P ⊥ 0) (bot_neg : ∀ x : ℝ, x < 0 → P ⊥ x) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : ℝ) => by
    rcases lt_trichotomy 0 y with (hy | rfl | hy)
    exacts[bot_pos y hy, bot_zero, bot_neg y hy]
  | ⊥, ⊤ => bot_top
  | (x : ℝ), ⊥ => by
    rcases lt_trichotomy 0 x with (hx | rfl | hx)
    exacts[pos_bot x hx, zero_bot, neg_bot x hx]
  | (x : ℝ), (y : ℝ) => coe_coe _ _
  | (x : ℝ), ⊤ => by
    rcases lt_trichotomy 0 x with (hx | rfl | hx)
    exacts[pos_top x hx, zero_top, neg_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : ℝ) => by
    rcases lt_trichotomy 0 y with (hy | rfl | hy)
    exacts[top_pos y hy, top_zero, top_neg y hy]
  | ⊤, ⊤ => top_top
#align ereal.induction₂ EReal.induction₂

/-! `ereal` with its multiplication is a `comm_monoid_with_zero`. However, the proof of
associativity by hand is extremely painful (with 125 cases...). Instead, we will deduce it later
on from the facts that the absolute value and the sign are multiplicative functions taking value
in associative objects, and that they characterize an extended real number. For now, we only
record more basic properties of multiplication.
-/


instance : MulZeroOneClass EReal :=
  { EReal.hasMul, EReal.hasOne,
    EReal.hasZero with
    one_mul := fun x => by
      induction x using EReal.rec <;>
        · dsimp only [(· * ·)]
          simp only [EReal.mul, ← EReal.coe_one, zero_lt_one, if_true, one_mul]
    mul_one := fun x => by
      induction x using EReal.rec <;>
        · dsimp only [(· * ·)]
          simp only [EReal.mul, ← EReal.coe_one, zero_lt_one, if_true, mul_one]
    zero_mul := fun x => by
      induction x using EReal.rec <;>
        · simp only [(· * ·)]
          simp only [EReal.mul, ← EReal.coe_zero, zero_lt_one, if_true, if_false, lt_irrefl (0 : ℝ),
            eq_self_iff_true, zero_mul]
    mul_zero := fun x => by
      induction x using EReal.rec <;>
        · simp only [(· * ·)]
          simp only [EReal.mul, ← EReal.coe_zero, zero_lt_one, if_true, if_false, lt_irrefl (0 : ℝ),
            eq_self_iff_true, mul_zero] }

/-! ### Real coercion -/


instance canLift : CanLift EReal ℝ coe fun r => r ≠ ⊤ ∧ r ≠ ⊥
    where prf x hx := by
    induction x using EReal.rec
    · simpa using hx
    · simp
    · simpa using hx
#align ereal.can_lift EReal.canLift

/-- The map from extended reals to reals sending infinities to zero. -/
def toReal : EReal → ℝ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => x
#align ereal.to_real EReal.toReal

@[simp]
theorem toReal_top : toReal ⊤ = 0 :=
  rfl
#align ereal.to_real_top EReal.toReal_top

@[simp]
theorem toReal_bot : toReal ⊥ = 0 :=
  rfl
#align ereal.to_real_bot EReal.toReal_bot

@[simp]
theorem toReal_zero : toReal 0 = 0 :=
  rfl
#align ereal.to_real_zero EReal.toReal_zero

@[simp]
theorem toReal_one : toReal 1 = 1 :=
  rfl
#align ereal.to_real_one EReal.toReal_one

@[simp]
theorem toReal_coe (x : ℝ) : toReal (x : EReal) = x :=
  rfl
#align ereal.to_real_coe EReal.toReal_coe

@[simp]
theorem bot_lt_coe (x : ℝ) : (⊥ : EReal) < x :=
  WithBot.bot_lt_coe _
#align ereal.bot_lt_coe EReal.bot_lt_coe

@[simp]
theorem coe_ne_bot (x : ℝ) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe x).ne'
#align ereal.coe_ne_bot EReal.coe_ne_bot

@[simp]
theorem bot_ne_coe (x : ℝ) : (⊥ : EReal) ≠ x :=
  (bot_lt_coe x).Ne
#align ereal.bot_ne_coe EReal.bot_ne_coe

@[simp]
theorem coe_lt_top (x : ℝ) : (x : EReal) < ⊤ := by
  apply WithBot.coe_lt_coe.2
  exact WithTop.coe_lt_top _
#align ereal.coe_lt_top EReal.coe_lt_top

@[simp]
theorem coe_ne_top (x : ℝ) : (x : EReal) ≠ ⊤ :=
  (coe_lt_top x).Ne
#align ereal.coe_ne_top EReal.coe_ne_top

@[simp]
theorem top_ne_coe (x : ℝ) : (⊤ : EReal) ≠ x :=
  (coe_lt_top x).ne'
#align ereal.top_ne_coe EReal.top_ne_coe

@[simp]
theorem bot_lt_zero : (⊥ : EReal) < 0 :=
  bot_lt_coe 0
#align ereal.bot_lt_zero EReal.bot_lt_zero

@[simp]
theorem bot_ne_zero : (⊥ : EReal) ≠ 0 :=
  (coe_ne_bot 0).symm
#align ereal.bot_ne_zero EReal.bot_ne_zero

@[simp]
theorem zero_ne_bot : (0 : EReal) ≠ ⊥ :=
  coe_ne_bot 0
#align ereal.zero_ne_bot EReal.zero_ne_bot

@[simp]
theorem zero_lt_top : (0 : EReal) < ⊤ :=
  coe_lt_top 0
#align ereal.zero_lt_top EReal.zero_lt_top

@[simp]
theorem zero_ne_top : (0 : EReal) ≠ ⊤ :=
  coe_ne_top 0
#align ereal.zero_ne_top EReal.zero_ne_top

@[simp]
theorem top_ne_zero : (⊤ : EReal) ≠ 0 :=
  (coe_ne_top 0).symm
#align ereal.top_ne_zero EReal.top_ne_zero

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : (↑(x + y) : EReal) = x + y :=
  rfl
#align ereal.coe_add EReal.coe_add

@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : (↑(x * y) : EReal) = x * y :=
  rfl
#align ereal.coe_mul EReal.coe_mul

@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : EReal) = n • x :=
  map_nsmul (⟨coe, coe_zero, coe_add⟩ : ℝ →+ EReal) _ _
#align ereal.coe_nsmul EReal.coe_nsmul

@[simp, norm_cast]
theorem coe_bit0 (x : ℝ) : (↑(bit0 x) : EReal) = bit0 x :=
  rfl
#align ereal.coe_bit0 EReal.coe_bit0

@[simp, norm_cast]
theorem coe_bit1 (x : ℝ) : (↑(bit1 x) : EReal) = bit1 x :=
  rfl
#align ereal.coe_bit1 EReal.coe_bit1

@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : EReal) = 0 ↔ x = 0 :=
  EReal.coe_eq_coe_iff
#align ereal.coe_eq_zero EReal.coe_eq_zero

@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : EReal) = 1 ↔ x = 1 :=
  EReal.coe_eq_coe_iff
#align ereal.coe_eq_one EReal.coe_eq_one

theorem coe_ne_zero {x : ℝ} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  EReal.coe_ne_coe_iff
#align ereal.coe_ne_zero EReal.coe_ne_zero

theorem coe_ne_one {x : ℝ} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  EReal.coe_ne_coe_iff
#align ereal.coe_ne_one EReal.coe_ne_one

@[simp, norm_cast]
protected theorem coe_nonneg {x : ℝ} : (0 : EReal) ≤ x ↔ 0 ≤ x :=
  EReal.coe_le_coe_iff
#align ereal.coe_nonneg EReal.coe_nonneg

@[simp, norm_cast]
protected theorem coe_nonpos {x : ℝ} : (x : EReal) ≤ 0 ↔ x ≤ 0 :=
  EReal.coe_le_coe_iff
#align ereal.coe_nonpos EReal.coe_nonpos

@[simp, norm_cast]
protected theorem coe_pos {x : ℝ} : (0 : EReal) < x ↔ 0 < x :=
  EReal.coe_lt_coe_iff
#align ereal.coe_pos EReal.coe_pos

@[simp, norm_cast]
protected theorem coe_neg' {x : ℝ} : (x : EReal) < 0 ↔ x < 0 :=
  EReal.coe_lt_coe_iff
#align ereal.coe_neg' EReal.coe_neg'

theorem toReal_le_toReal {x y : EReal} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toReal ≤ y.toReal := by
  lift x to ℝ
  · simp [hx, (h.trans_lt (lt_top_iff_ne_top.2 hy)).Ne]
  lift y to ℝ
  · simp [hy, ((bot_lt_iff_ne_bot.2 hx).trans_le h).ne']
  simpa using h
#align ereal.to_real_le_to_real EReal.toReal_le_toReal

theorem coe_toReal {x : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toReal : EReal) = x := by
  induction x using EReal.rec
  · simpa using h'x
  · rfl
  · simpa using hx
#align ereal.coe_to_real EReal.coe_toReal

theorem le_coe_toReal {x : EReal} (h : x ≠ ⊤) : x ≤ x.toReal := by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_to_real h h']
#align ereal.le_coe_to_real EReal.le_coe_toReal

theorem coe_toReal_le {x : EReal} (h : x ≠ ⊥) : ↑x.toReal ≤ x := by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_to_real h' h]
#align ereal.coe_to_real_le EReal.coe_toReal_le

theorem eq_top_iff_forall_lt (x : EReal) : x = ⊤ ↔ ∀ y : ℝ, (y : EReal) < x := by
  constructor
  · rintro rfl
    exact EReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.to_real, le_coe_to_real h⟩
#align ereal.eq_top_iff_forall_lt EReal.eq_top_iff_forall_lt

theorem eq_bot_iff_forall_lt (x : EReal) : x = ⊥ ↔ ∀ y : ℝ, x < (y : EReal) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.to_real, coe_to_real_le h⟩
#align ereal.eq_bot_iff_forall_lt EReal.eq_bot_iff_forall_lt

/-! ### ennreal coercion -/


@[simp]
theorem toReal_coe_ennreal : ∀ {x : ℝ≥0∞}, toReal (x : EReal) = ENNReal.toReal x
  | ⊤ => rfl
  | some x => rfl
#align ereal.to_real_coe_ennreal EReal.toReal_coe_ennreal

@[simp]
theorem coe_ennreal_ofReal {x : ℝ} : (ENNReal.ofReal x : EReal) = max x 0 :=
  rfl
#align ereal.coe_ennreal_of_real EReal.coe_ennreal_ofReal

theorem coe_nNReal_eq_coe_real (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) = (x : ℝ) :=
  rfl
#align ereal.coe_nnreal_eq_coe_real EReal.coe_nNReal_eq_coe_real

@[simp, norm_cast]
theorem coe_ennreal_zero : ((0 : ℝ≥0∞) : EReal) = 0 :=
  rfl
#align ereal.coe_ennreal_zero EReal.coe_ennreal_zero

@[simp, norm_cast]
theorem coe_ennreal_one : ((1 : ℝ≥0∞) : EReal) = 1 :=
  rfl
#align ereal.coe_ennreal_one EReal.coe_ennreal_one

@[simp, norm_cast]
theorem coe_ennreal_top : ((⊤ : ℝ≥0∞) : EReal) = ⊤ :=
  rfl
#align ereal.coe_ennreal_top EReal.coe_ennreal_top

@[simp]
theorem coe_ennreal_eq_top_iff : ∀ {x : ℝ≥0∞}, (x : EReal) = ⊤ ↔ x = ⊤
  | ⊤ => by simp
  | some x => by
    simp only [ENNReal.coe_ne_top, iff_false_iff, ENNReal.some_eq_coe]
    decide
#align ereal.coe_ennreal_eq_top_iff EReal.coe_ennreal_eq_top_iff

theorem coe_nNReal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) ≠ ⊤ := by decide
#align ereal.coe_nnreal_ne_top EReal.coe_nNReal_ne_top

@[simp]
theorem coe_nNReal_lt_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) < ⊤ := by decide
#align ereal.coe_nnreal_lt_top EReal.coe_nNReal_lt_top

theorem coe_ennreal_strictMono : StrictMono (coe : ℝ≥0∞ → EReal)
  | ⊤, ⊤ => by simp
  | some x, ⊤ => by simp
  | ⊤, some y => by simp
  | some x, some y => by simp [coe_nnreal_eq_coe_real]
#align ereal.coe_ennreal_strict_mono EReal.coe_ennreal_strictMono

theorem coe_ennreal_injective : Injective (coe : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.Injective
#align ereal.coe_ennreal_injective EReal.coe_ennreal_injective

@[simp, norm_cast]
theorem coe_ennreal_le_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_ennreal_strictMono.le_iff_le
#align ereal.coe_ennreal_le_coe_ennreal_iff EReal.coe_ennreal_le_coe_ennreal_iff

@[simp, norm_cast]
theorem coe_ennreal_lt_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_ennreal_strictMono.lt_iff_lt
#align ereal.coe_ennreal_lt_coe_ennreal_iff EReal.coe_ennreal_lt_coe_ennreal_iff

@[simp, norm_cast]
theorem coe_ennreal_eq_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_ennreal_injective.eq_iff
#align ereal.coe_ennreal_eq_coe_ennreal_iff EReal.coe_ennreal_eq_coe_ennreal_iff

theorem coe_ennreal_ne_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_ennreal_injective.ne_iff
#align ereal.coe_ennreal_ne_coe_ennreal_iff EReal.coe_ennreal_ne_coe_ennreal_iff

@[simp, norm_cast]
theorem coe_ennreal_eq_zero {x : ℝ≥0∞} : (x : EReal) = 0 ↔ x = 0 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_zero]
#align ereal.coe_ennreal_eq_zero EReal.coe_ennreal_eq_zero

@[simp, norm_cast]
theorem coe_ennreal_eq_one {x : ℝ≥0∞} : (x : EReal) = 1 ↔ x = 1 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one]
#align ereal.coe_ennreal_eq_one EReal.coe_ennreal_eq_one

@[norm_cast]
theorem coe_ennreal_ne_zero {x : ℝ≥0∞} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  coe_ennreal_eq_zero.Not
#align ereal.coe_ennreal_ne_zero EReal.coe_ennreal_ne_zero

@[norm_cast]
theorem coe_ennreal_ne_one {x : ℝ≥0∞} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  coe_ennreal_eq_one.Not
#align ereal.coe_ennreal_ne_one EReal.coe_ennreal_ne_one

theorem coe_ennreal_nonneg (x : ℝ≥0∞) : (0 : EReal) ≤ x :=
  coe_ennreal_le_coe_ennreal_iff.2 (zero_le x)
#align ereal.coe_ennreal_nonneg EReal.coe_ennreal_nonneg

@[simp, norm_cast]
theorem coe_ennreal_pos {x : ℝ≥0∞} : (0 : EReal) < x ↔ 0 < x := by
  rw [← coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]
#align ereal.coe_ennreal_pos EReal.coe_ennreal_pos

@[simp]
theorem bot_lt_coe_ennreal (x : ℝ≥0∞) : (⊥ : EReal) < x :=
  (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)
#align ereal.bot_lt_coe_ennreal EReal.bot_lt_coe_ennreal

@[simp]
theorem coe_ennreal_ne_bot (x : ℝ≥0∞) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe_ennreal x).ne'
#align ereal.coe_ennreal_ne_bot EReal.coe_ennreal_ne_bot

@[simp, norm_cast]
theorem coe_ennreal_add (x y : ENNReal) : ((x + y : ℝ≥0∞) : EReal) = x + y := by
  cases x <;> cases y <;> rfl
#align ereal.coe_ennreal_add EReal.coe_ennreal_add

@[simp, norm_cast]
theorem coe_ennreal_mul : ∀ x y : ℝ≥0∞, ((x * y : ℝ≥0∞) : EReal) = x * y
  | ⊤, ⊤ => rfl
  | ⊤, (y : ℝ≥0) => by
    rw [ENNReal.top_mul]; split_ifs
    · simp only [h, coe_ennreal_zero, mul_zero]
    · have A : (0 : ℝ) < y := by
        simp only [ENNReal.coe_eq_zero] at h
        exact NNReal.coe_pos.2 (bot_lt_iff_ne_bot.2 h)
      simp only [coe_nnreal_eq_coe_real, coe_ennreal_top, (· * ·), EReal.mul, A, if_true]
  | (x : ℝ≥0), ⊤ => by
    rw [ENNReal.mul_top]; split_ifs
    · simp only [h, coe_ennreal_zero, zero_mul]
    · have A : (0 : ℝ) < x := by
        simp only [ENNReal.coe_eq_zero] at h
        exact NNReal.coe_pos.2 (bot_lt_iff_ne_bot.2 h)
      simp only [coe_nnreal_eq_coe_real, coe_ennreal_top, (· * ·), EReal.mul, A, if_true]
  | (x : ℝ≥0), (y : ℝ≥0) => by
    simp only [← ENNReal.coe_mul, coe_nnreal_eq_coe_real, NNReal.coe_mul, EReal.coe_mul]
#align ereal.coe_ennreal_mul EReal.coe_ennreal_mul

@[norm_cast]
theorem coe_ennreal_nsmul (n : ℕ) (x : ℝ≥0∞) : (↑(n • x) : EReal) = n • x :=
  map_nsmul (⟨coe, coe_ennreal_zero, coe_ennreal_add⟩ : ℝ≥0∞ →+ EReal) _ _
#align ereal.coe_ennreal_nsmul EReal.coe_ennreal_nsmul

@[simp, norm_cast]
theorem coe_ennreal_bit0 (x : ℝ≥0∞) : (↑(bit0 x) : EReal) = bit0 x :=
  coe_ennreal_add _ _
#align ereal.coe_ennreal_bit0 EReal.coe_ennreal_bit0

@[simp, norm_cast]
theorem coe_ennreal_bit1 (x : ℝ≥0∞) : (↑(bit1 x) : EReal) = bit1 x := by
  simp_rw [bit1, coe_ennreal_add, coe_ennreal_bit0, coe_ennreal_one]
#align ereal.coe_ennreal_bit1 EReal.coe_ennreal_bit1

/-! ### Order -/


theorem exists_rat_btwn_of_lt :
    ∀ {a b : EReal} (hab : a < b), ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b
  | ⊤, b, h => (not_top_lt h).elim
  | (a : ℝ), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
  | (a : ℝ), (b : ℝ), h => by simp [exists_rat_btwn (EReal.coe_lt_coe_iff.1 h)]
  | (a : ℝ), ⊤, h =>
    let ⟨b, hab⟩ := exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : ℝ), h =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, h => ⟨0, bot_lt_coe _, coe_lt_top _⟩
#align ereal.exists_rat_btwn_of_lt EReal.exists_rat_btwn_of_lt

theorem lt_iff_exists_rat_btwn {a b : EReal} :
    a < b ↔ ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨x, ax, xb⟩ => ax.trans xb⟩
#align ereal.lt_iff_exists_rat_btwn EReal.lt_iff_exists_rat_btwn

theorem lt_iff_exists_real_btwn {a b : EReal} : a < b ↔ ∃ x : ℝ, a < x ∧ (x : EReal) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : ℝ), ax, xb⟩,
    fun ⟨x, ax, xb⟩ => ax.trans xb⟩
#align ereal.lt_iff_exists_real_btwn EReal.lt_iff_exists_real_btwn

/-- The set of numbers in `ereal` that are not equal to `±∞` is equivalent to `ℝ`. -/
def neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ ℝ
    where
  toFun x := EReal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.eq <| by
      lift x to ℝ
      · simpa [not_or, and_comm'] using hx
      · simp
  right_inv x := by simp
#align ereal.ne_top_bot_equiv_real EReal.neTopBotEquivReal

/-! ### Addition -/


@[simp]
theorem add_bot (x : EReal) : x + ⊥ = ⊥ :=
  WithBot.add_bot _
#align ereal.add_bot EReal.add_bot

@[simp]
theorem bot_add (x : EReal) : ⊥ + x = ⊥ :=
  WithBot.bot_add _
#align ereal.bot_add EReal.bot_add

@[simp]
theorem top_add_top : (⊤ : EReal) + ⊤ = ⊤ :=
  rfl
#align ereal.top_add_top EReal.top_add_top

@[simp]
theorem top_add_coe (x : ℝ) : (⊤ : EReal) + x = ⊤ :=
  rfl
#align ereal.top_add_coe EReal.top_add_coe

@[simp]
theorem coe_add_top (x : ℝ) : (x : EReal) + ⊤ = ⊤ :=
  rfl
#align ereal.coe_add_top EReal.coe_add_top

theorem toReal_add :
    ∀ {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥),
      toReal (x + y) = toReal x + toReal y
  | ⊥, y, hx, h'x, hy, h'y => (h'x rfl).elim
  | ⊤, y, hx, h'x, hy, h'y => (hx rfl).elim
  | x, ⊤, hx, h'x, hy, h'y => (hy rfl).elim
  | x, ⊥, hx, h'x, hy, h'y => (h'y rfl).elim
  | (x : ℝ), (y : ℝ), hx, h'x, hy, h'y => by simp [← EReal.coe_add]
#align ereal.to_real_add EReal.toReal_add

theorem add_lt_add_right_coe {x y : EReal} (h : x < y) (z : ℝ) : x + z < y + z := by
  induction x using EReal.rec <;> induction y using EReal.rec
  · exact (lt_irrefl _ h).elim
  · simp only [← coe_add, bot_add, bot_lt_coe]
  · simp
  · exact (lt_irrefl _ (h.trans (bot_lt_coe x))).elim
  · norm_cast  at h⊢
    exact add_lt_add_right h _
  · simp only [← coe_add, top_add_coe, coe_lt_top]
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
#align ereal.add_lt_add_right_coe EReal.add_lt_add_right_coe

theorem add_lt_add_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x + z < y + t := by
  induction z using EReal.rec
  · simpa only using hz
  ·
    calc
      x + z < y + z := add_lt_add_right_coe h _
      _ ≤ y + t := add_le_add le_rfl h'
      
  · exact (ht (top_le_iff.1 h')).elim
#align ereal.add_lt_add_of_lt_of_le EReal.add_lt_add_of_lt_of_le

theorem add_lt_add_left_coe {x y : EReal} (h : x < y) (z : ℝ) : (z : EReal) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z
#align ereal.add_lt_add_left_coe EReal.add_lt_add_left_coe

theorem add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  induction x using EReal.rec
  · simp [bot_lt_iff_ne_bot, h1.ne', (bot_le.trans_lt h2).ne']
  ·
    calc
      (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
      _ ≤ y + t := add_le_add h1.le le_rfl
      
  · exact (lt_irrefl _ (h1.trans_le le_top)).elim
#align ereal.add_lt_add EReal.add_lt_add

@[simp]
theorem add_eq_bot_iff {x y : EReal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ := by
  induction x using EReal.rec <;> induction y using EReal.rec <;> simp [← EReal.coe_add]
#align ereal.add_eq_bot_iff EReal.add_eq_bot_iff

@[simp]
theorem bot_lt_add_iff {x y : EReal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot, not_or]
#align ereal.bot_lt_add_iff EReal.bot_lt_add_iff

theorem add_lt_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y < ⊤ := by
  rw [← EReal.top_add_top]
  exact EReal.add_lt_add hx.lt_top hy.lt_top
#align ereal.add_lt_top EReal.add_lt_top

/-! ### Negation -/


/-- negation on `ereal` -/
protected def neg : EReal → EReal
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℝ) => (-x : ℝ)
#align ereal.neg EReal.neg

instance : Neg EReal :=
  ⟨EReal.neg⟩

instance : SubNegZeroMonoid EReal :=
  { EReal.addMonoid, EReal.hasNeg with
    neg_zero := by
      change ((-0 : ℝ) : EReal) = 0
      simp }

@[norm_cast]
protected theorem neg_def (x : ℝ) : ((-x : ℝ) : EReal) = -x :=
  rfl
#align ereal.neg_def EReal.neg_def

@[simp]
theorem neg_top : -(⊤ : EReal) = ⊥ :=
  rfl
#align ereal.neg_top EReal.neg_top

@[simp]
theorem neg_bot : -(⊥ : EReal) = ⊤ :=
  rfl
#align ereal.neg_bot EReal.neg_bot

@[simp, norm_cast]
theorem coe_neg (x : ℝ) : (↑(-x) : EReal) = -x :=
  rfl
#align ereal.coe_neg EReal.coe_neg

@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : (↑(x - y) : EReal) = x - y :=
  rfl
#align ereal.coe_sub EReal.coe_sub

@[norm_cast]
theorem coe_zsmul (n : ℤ) (x : ℝ) : (↑(n • x) : EReal) = n • x :=
  map_zsmul' (⟨coe, coe_zero, coe_add⟩ : ℝ →+ EReal) coe_neg _ _
#align ereal.coe_zsmul EReal.coe_zsmul

instance : InvolutiveNeg EReal where
  neg := Neg.neg
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℝ) => by
      norm_cast
      simp [neg_neg a]

@[simp]
theorem toReal_neg : ∀ {a : EReal}, toReal (-a) = -toReal a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℝ) => rfl
#align ereal.to_real_neg EReal.toReal_neg

@[simp]
theorem neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥ := by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]
#align ereal.neg_eq_top_iff EReal.neg_eq_top_iff

@[simp]
theorem neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤ := by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]
#align ereal.neg_eq_bot_iff EReal.neg_eq_bot_iff

@[simp]
theorem neg_eq_zero_iff {x : EReal} : -x = 0 ↔ x = 0 := by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]
#align ereal.neg_eq_zero_iff EReal.neg_eq_zero_iff

/-- if `-a ≤ b` then `-b ≤ a` on `ereal`. -/
protected theorem neg_le_of_neg_le {a b : EReal} (h : -a ≤ b) : -b ≤ a := by
  induction a using EReal.rec <;> induction b using EReal.rec
  · exact h
  · simpa only [coe_ne_top, neg_bot, top_le_iff] using h
  · exact bot_le
  · simpa only [coe_ne_top, le_bot_iff] using h
  · norm_cast  at h⊢
    exact neg_le.1 h
  · exact bot_le
  · exact le_top
  · exact le_top
  · exact le_top
#align ereal.neg_le_of_neg_le EReal.neg_le_of_neg_le

/-- `-a ≤ b ↔ -b ≤ a` on `ereal`. -/
protected theorem neg_le {a b : EReal} : -a ≤ b ↔ -b ≤ a :=
  ⟨EReal.neg_le_of_neg_le, EReal.neg_le_of_neg_le⟩
#align ereal.neg_le EReal.neg_le

/-- `a ≤ -b → b ≤ -a` on ereal -/
theorem le_neg_of_le_neg {a b : EReal} (h : a ≤ -b) : b ≤ -a := by
  rwa [← neg_neg b, EReal.neg_le, neg_neg]
#align ereal.le_neg_of_le_neg EReal.le_neg_of_le_neg

@[simp]
theorem neg_le_neg_iff {a b : EReal} : -a ≤ -b ↔ b ≤ a := by conv_lhs => rw [EReal.neg_le, neg_neg]
#align ereal.neg_le_neg_iff EReal.neg_le_neg_iff

/-- Negation as an order reversing isomorphism on `ereal`. -/
def negOrderIso : EReal ≃o ERealᵒᵈ :=
  { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -x.ofDual
    map_rel_iff' := fun x y => neg_le_neg_iff }
#align ereal.neg_order_iso EReal.negOrderIso

theorem neg_lt_of_neg_lt {a b : EReal} (h : -a < b) : -b < a := by
  apply lt_of_le_of_ne (EReal.neg_le_of_neg_le h.le)
  intro H
  rw [← H, neg_neg] at h
  exact lt_irrefl _ h
#align ereal.neg_lt_of_neg_lt EReal.neg_lt_of_neg_lt

theorem neg_lt_iff_neg_lt {a b : EReal} : -a < b ↔ -b < a :=
  ⟨fun h => EReal.neg_lt_of_neg_lt h, fun h => EReal.neg_lt_of_neg_lt h⟩
#align ereal.neg_lt_iff_neg_lt EReal.neg_lt_iff_neg_lt

/-!
### Subtraction

Subtraction on `ereal` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `ereal`, beyond `sub_neg_zero_monoid`, because of this bad behavior.
-/


@[simp]
theorem bot_sub (x : EReal) : ⊥ - x = ⊥ :=
  bot_add x
#align ereal.bot_sub EReal.bot_sub

@[simp]
theorem sub_top (x : EReal) : x - ⊤ = ⊥ :=
  add_bot x
#align ereal.sub_top EReal.sub_top

@[simp]
theorem top_sub_bot : (⊤ : EReal) - ⊥ = ⊤ :=
  rfl
#align ereal.top_sub_bot EReal.top_sub_bot

@[simp]
theorem top_sub_coe (x : ℝ) : (⊤ : EReal) - x = ⊤ :=
  rfl
#align ereal.top_sub_coe EReal.top_sub_coe

@[simp]
theorem coe_sub_bot (x : ℝ) : (x : EReal) - ⊥ = ⊤ :=
  rfl
#align ereal.coe_sub_bot EReal.coe_sub_bot

theorem sub_le_sub {x y z t : EReal} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
  add_le_add h (neg_le_neg_iff.2 h')
#align ereal.sub_le_sub EReal.sub_le_sub

theorem sub_lt_sub_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x - t < y - z :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])
#align ereal.sub_lt_sub_of_lt_of_le EReal.sub_lt_sub_of_lt_of_le

theorem coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (x : ℝ) :
    (x : EReal) = Real.toNNReal x - Real.toNNReal (-x) := by
  rcases le_or_lt 0 x with (h | h)
  · have : Real.toNNReal x = ⟨x, h⟩ := by
      ext
      simp [h]
    simp only [Real.toNNReal_of_nonpos (neg_nonpos.mpr h), this, sub_zero, ENNReal.coe_zero,
      coe_ennreal_zero, coe_coe]
    rfl
  · have : (x : EReal) = -(-x : ℝ) := by simp
    conv_lhs => rw [this]
    have : Real.toNNReal (-x) = ⟨-x, neg_nonneg.mpr h.le⟩ :=
      by
      ext
      simp [neg_nonneg.mpr h.le]
    simp only [Real.toNNReal_of_nonpos h.le, this, zero_sub, neg_inj, coe_neg, ENNReal.coe_zero,
      coe_ennreal_zero, coe_coe]
    rfl
#align ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal

theorem toReal_sub {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x - y) = toReal x - toReal y := by
  rw [sub_eq_add_neg, to_real_add hx h'x, to_real_neg]
  · rfl
  · simpa using hy
  · simpa using h'y
#align ereal.to_real_sub EReal.toReal_sub

/-! ### Multiplication -/


protected theorem mul_comm (x y : EReal) : x * y = y * x := by
  induction x using EReal.rec <;> induction y using EReal.rec <;> try rfl
  dsimp only [(· * ·)]
  simp only [EReal.mul, mul_comm]
#align ereal.mul_comm EReal.mul_comm

@[simp]
theorem top_mul_top : (⊤ : EReal) * ⊤ = ⊤ :=
  rfl
#align ereal.top_mul_top EReal.top_mul_top

@[simp]
theorem top_mul_bot : (⊤ : EReal) * ⊥ = ⊥ :=
  rfl
#align ereal.top_mul_bot EReal.top_mul_bot

@[simp]
theorem bot_mul_top : (⊥ : EReal) * ⊤ = ⊥ :=
  rfl
#align ereal.bot_mul_top EReal.bot_mul_top

@[simp]
theorem bot_mul_bot : (⊥ : EReal) * ⊥ = ⊤ :=
  rfl
#align ereal.bot_mul_bot EReal.bot_mul_bot

theorem mul_top_of_pos {x : EReal} (h : 0 < x) : x * ⊤ = ⊤ := by
  induction x using EReal.rec
  · simpa only [not_lt_bot] using h
  · simp only [Mul.mul, EReal.mul, EReal.coe_pos.1 h, if_true]
  · rfl
#align ereal.mul_top_of_pos EReal.mul_top_of_pos

theorem mul_top_of_neg {x : EReal} (h : x < 0) : x * ⊤ = ⊥ := by
  induction x using EReal.rec
  · rfl
  · simp only [EReal.coe_neg'] at h
    simp only [Mul.mul, EReal.mul, not_lt.2 h.le, h.ne, if_false]
  · simpa only [not_top_lt] using h
#align ereal.mul_top_of_neg EReal.mul_top_of_neg

theorem top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_top_of_pos h
#align ereal.top_mul_of_pos EReal.top_mul_of_pos

theorem top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_top_of_neg h
#align ereal.top_mul_of_neg EReal.top_mul_of_neg

theorem coe_mul_top_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊤ = ⊤ :=
  mul_top_of_pos (EReal.coe_pos.2 h)
#align ereal.coe_mul_top_of_pos EReal.coe_mul_top_of_pos

theorem coe_mul_top_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊤ = ⊥ :=
  mul_top_of_neg (EReal.coe_neg'.2 h)
#align ereal.coe_mul_top_of_neg EReal.coe_mul_top_of_neg

theorem top_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊤ : EReal) * x = ⊤ :=
  top_mul_of_pos (EReal.coe_pos.2 h)
#align ereal.top_mul_coe_of_pos EReal.top_mul_coe_of_pos

theorem top_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊤ : EReal) * x = ⊥ :=
  top_mul_of_neg (EReal.coe_neg'.2 h)
#align ereal.top_mul_coe_of_neg EReal.top_mul_coe_of_neg

theorem mul_bot_of_pos {x : EReal} (h : 0 < x) : x * ⊥ = ⊥ := by
  induction x using EReal.rec
  · simpa only [not_lt_bot] using h
  · simp only [Mul.mul, EReal.mul, EReal.coe_pos.1 h, if_true]
  · rfl
#align ereal.mul_bot_of_pos EReal.mul_bot_of_pos

theorem mul_bot_of_neg {x : EReal} (h : x < 0) : x * ⊥ = ⊤ := by
  induction x using EReal.rec
  · rfl
  · simp only [EReal.coe_neg'] at h
    simp only [Mul.mul, EReal.mul, not_lt.2 h.le, h.ne, if_false]
  · simpa only [not_top_lt] using h
#align ereal.mul_bot_of_neg EReal.mul_bot_of_neg

theorem bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_pos h
#align ereal.bot_mul_of_pos EReal.bot_mul_of_pos

theorem bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_neg h
#align ereal.bot_mul_of_neg EReal.bot_mul_of_neg

theorem coe_mul_bot_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊥ = ⊥ :=
  mul_bot_of_pos (EReal.coe_pos.2 h)
#align ereal.coe_mul_bot_of_pos EReal.coe_mul_bot_of_pos

theorem coe_mul_bot_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊥ = ⊤ :=
  mul_bot_of_neg (EReal.coe_neg'.2 h)
#align ereal.coe_mul_bot_of_neg EReal.coe_mul_bot_of_neg

theorem bot_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊥ : EReal) * x = ⊥ :=
  bot_mul_of_pos (EReal.coe_pos.2 h)
#align ereal.bot_mul_coe_of_pos EReal.bot_mul_coe_of_pos

theorem bot_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊥ : EReal) * x = ⊤ :=
  bot_mul_of_neg (EReal.coe_neg'.2 h)
#align ereal.bot_mul_coe_of_neg EReal.bot_mul_coe_of_neg

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
theorem toReal_mul {x y : EReal} : toReal (x * y) = toReal x * toReal y := by
  -- TODO: replace with `induction using` in Lean 4, which supports multiple premises
    apply @induction₂ fun x y => to_real (x * y) = to_real x * to_real y <;>
    propagate_tags try dsimp only
  case top_zero | bot_zero | zero_top | zero_bot =>
    all_goals simp only [zero_mul, mul_zero, to_real_zero]
  case coe_coe x y => norm_cast
  case top_top => rw [top_mul_top, to_real_top, mul_zero]
  case top_bot => rw [top_mul_bot, to_real_top, to_real_bot, zero_mul]
  case bot_top => rw [bot_mul_top, to_real_bot, zero_mul]
  case bot_bot => rw [bot_mul_bot, to_real_top, to_real_bot, zero_mul]
  case pos_bot x hx => rw [to_real_bot, to_real_coe, coe_mul_bot_of_pos hx, to_real_bot, mul_zero]
  case neg_bot x hx => rw [to_real_bot, to_real_coe, coe_mul_bot_of_neg hx, to_real_top, mul_zero]
  case pos_top x hx => rw [to_real_top, to_real_coe, coe_mul_top_of_pos hx, to_real_top, mul_zero]
  case neg_top x hx => rw [to_real_top, to_real_coe, coe_mul_top_of_neg hx, to_real_bot, mul_zero]
  case top_pos y hy => rw [to_real_top, to_real_coe, top_mul_coe_of_pos hy, to_real_top, zero_mul]
  case top_neg y hy => rw [to_real_top, to_real_coe, top_mul_coe_of_neg hy, to_real_bot, zero_mul]
  case bot_pos y hy => rw [to_real_bot, to_real_coe, bot_mul_coe_of_pos hy, to_real_bot, zero_mul]
  case bot_neg y hy => rw [to_real_bot, to_real_coe, bot_mul_coe_of_neg hy, to_real_top, zero_mul]
#align ereal.to_real_mul EReal.toReal_mul

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
protected theorem neg_mul (x y : EReal) : -x * y = -(x * y) := by
  -- TODO: replace with `induction using` in Lean 4, which supports multiple premises
    apply @induction₂ fun x y => -x * y = -(x * y) <;>
    propagate_tags try dsimp only
  case top_top | bot_top | top_bot | bot_bot => all_goals rfl
  case top_zero | bot_zero | zero_top | zero_bot =>
    all_goals simp only [zero_mul, mul_zero, neg_zero]
  case coe_coe x y => norm_cast; exact neg_mul _ _
  case pos_bot x hx =>
    rw [coe_mul_bot_of_pos hx, neg_bot, ← coe_neg, coe_mul_bot_of_neg (neg_neg_of_pos hx)]
  case neg_bot x hx =>
    rw [coe_mul_bot_of_neg hx, neg_top, ← coe_neg, coe_mul_bot_of_pos (neg_pos_of_neg hx)]
  case pos_top x hx =>
    rw [coe_mul_top_of_pos hx, neg_top, ← coe_neg, coe_mul_top_of_neg (neg_neg_of_pos hx)]
  case neg_top x hx =>
    rw [coe_mul_top_of_neg hx, neg_bot, ← coe_neg, coe_mul_top_of_pos (neg_pos_of_neg hx)]
  case top_pos y hy => rw [top_mul_coe_of_pos hy, neg_top, bot_mul_coe_of_pos hy]
  case top_neg y hy => rw [top_mul_coe_of_neg hy, neg_top, neg_bot, bot_mul_coe_of_neg hy]
  case bot_pos y hy => rw [bot_mul_coe_of_pos hy, neg_bot, top_mul_coe_of_pos hy]
  case bot_neg y hy => rw [bot_mul_coe_of_neg hy, neg_bot, neg_top, top_mul_coe_of_neg hy]
#align ereal.neg_mul EReal.neg_mul

instance : HasDistribNeg EReal :=
  { EReal.hasInvolutiveNeg with
    neg_mul := EReal.neg_mul
    mul_neg := fun x y => by
      rw [x.mul_comm, x.mul_comm]
      exact y.neg_mul x }

/-! ### Absolute value -/


/-- The absolute value from `ereal` to `ℝ≥0∞`, mapping `⊥` and `⊤` to `⊤` and
a real `x` to `|x|`. -/
protected def abs : EReal → ℝ≥0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : ℝ) => ENNReal.ofReal (|x|)
#align ereal.abs EReal.abs

@[simp]
theorem abs_top : (⊤ : EReal).abs = ⊤ :=
  rfl
#align ereal.abs_top EReal.abs_top

@[simp]
theorem abs_bot : (⊥ : EReal).abs = ⊤ :=
  rfl
#align ereal.abs_bot EReal.abs_bot

theorem abs_def (x : ℝ) : (x : EReal).abs = ENNReal.ofReal (|x|) :=
  rfl
#align ereal.abs_def EReal.abs_def

theorem abs_coe_lt_top (x : ℝ) : (x : EReal).abs < ⊤ :=
  ENNReal.ofReal_lt_top
#align ereal.abs_coe_lt_top EReal.abs_coe_lt_top

@[simp]
theorem abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0 := by
  induction x using EReal.rec
  · simp only [abs_bot, ENNReal.top_ne_zero, bot_ne_zero]
  · simp only [EReal.abs, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]
#align ereal.abs_eq_zero_iff EReal.abs_eq_zero_iff

@[simp]
theorem abs_zero : (0 : EReal).abs = 0 := by rw [abs_eq_zero_iff]
#align ereal.abs_zero EReal.abs_zero

@[simp]
theorem coe_abs (x : ℝ) : ((x : EReal).abs : EReal) = (|x| : ℝ) := by
  rcases lt_trichotomy 0 x with (hx | rfl | hx) <;> simp [abs_def]
#align ereal.coe_abs EReal.coe_abs

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
@[simp]
theorem abs_mul (x y : EReal) : (x * y).abs = x.abs * y.abs := by
  -- TODO: replace with `induction using` in Lean 4, which supports multiple premises
    apply @induction₂ fun x y => (x * y).abs = x.abs * y.abs <;>
    propagate_tags try dsimp only
  case top_top | bot_top | top_bot | bot_bot => all_goals rfl
  case top_zero | bot_zero | zero_top | zero_bot =>
    all_goals simp only [zero_mul, mul_zero, abs_zero]
  case coe_coe x y => simp only [← coe_mul, EReal.abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  case pos_bot x hx =>
    simp only [coe_mul_bot_of_pos hx, hx.ne', abs_bot, WithTop.mul_top, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff]
  case neg_bot x hx =>
    simp only [coe_mul_bot_of_neg hx, hx.ne, abs_bot, WithTop.mul_top, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff, abs_top]
  case pos_top x hx =>
    simp only [coe_mul_top_of_pos hx, hx.ne', WithTop.mul_top, Ne.def, abs_eq_zero_iff, coe_eq_zero,
      not_false_iff, abs_top]
  case neg_top x hx =>
    simp only [coe_mul_top_of_neg hx, hx.ne, abs_bot, WithTop.mul_top, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff, abs_top]
  case top_pos y hy =>
    simp only [top_mul_coe_of_pos hy, hy.ne', WithTop.top_mul, Ne.def, abs_eq_zero_iff, coe_eq_zero,
      not_false_iff, abs_top]
  case top_neg y hy =>
    simp only [top_mul_coe_of_neg hy, hy.ne, abs_bot, WithTop.top_mul, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff, abs_top]
  case bot_pos y hy =>
    simp only [bot_mul_coe_of_pos hy, hy.ne', abs_bot, WithTop.top_mul, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff]
  case bot_neg y hy =>
    simp only [bot_mul_coe_of_neg hy, hy.ne, abs_bot, WithTop.top_mul, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff, abs_top]
#align ereal.abs_mul EReal.abs_mul

/-! ### Sign -/


@[simp]
theorem sign_top : SignType.sign (⊤ : EReal) = 1 :=
  rfl
#align ereal.sign_top EReal.sign_top

@[simp]
theorem sign_bot : SignType.sign (⊥ : EReal) = -1 :=
  rfl
#align ereal.sign_bot EReal.sign_bot

@[simp]
theorem sign_coe (x : ℝ) : SignType.sign (x : EReal) = SignType.sign x := by
  simp only [SignType.sign, OrderHom.coe_fun_mk, EReal.coe_pos, EReal.coe_neg']
#align ereal.sign_coe EReal.sign_coe

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
@[simp]
theorem sign_mul (x y : EReal) : SignType.sign (x * y) = SignType.sign x * SignType.sign y := by
  -- TODO: replace with `induction using` in Lean 4, which supports multiple premises
    apply @induction₂ fun x y => SignType.sign (x * y) = SignType.sign x * SignType.sign y <;>
    propagate_tags try dsimp only
  case top_top | bot_top | top_bot | bot_bot => all_goals rfl
  case top_zero | bot_zero | zero_top | zero_bot =>
    all_goals simp only [zero_mul, mul_zero, sign_zero]
  case coe_coe x y => simp only [← coe_mul, sign_coe, sign_mul]
  case pos_bot x hx => simp_rw [coe_mul_bot_of_pos hx, sign_coe, sign_pos hx, one_mul]
  case neg_bot x hx =>
    simp_rw [coe_mul_bot_of_neg hx, sign_coe, sign_neg hx, sign_top, sign_bot, neg_one_mul, neg_neg]
  case pos_top x hx => simp_rw [coe_mul_top_of_pos hx, sign_coe, sign_pos hx, one_mul]
  case neg_top x hx =>
    simp_rw [coe_mul_top_of_neg hx, sign_coe, sign_neg hx, sign_top, sign_bot, mul_one]
  case top_pos y hy => simp_rw [top_mul_coe_of_pos hy, sign_coe, sign_pos hy, mul_one]
  case top_neg y hy =>
    simp_rw [top_mul_coe_of_neg hy, sign_coe, sign_neg hy, sign_top, sign_bot, one_mul]
  case bot_pos y hy => simp_rw [bot_mul_coe_of_pos hy, sign_coe, sign_pos hy, mul_one]
  case bot_neg y hy =>
    simp_rw [bot_mul_coe_of_neg hy, sign_coe, sign_neg hy, sign_top, sign_bot, neg_one_mul, neg_neg]
#align ereal.sign_mul EReal.sign_mul

theorem sign_mul_abs (x : EReal) : (SignType.sign x * x.abs : EReal) = x := by
  induction x using EReal.rec
  · simp
  · rcases lt_trichotomy 0 x with (hx | rfl | hx)
    · simp [sign_pos hx, abs_of_pos hx]
    · simp
    · simp [sign_neg hx, abs_of_neg hx]
  · simp
#align ereal.sign_mul_abs EReal.sign_mul_abs

theorem sign_eq_and_abs_eq_iff_eq {x y : EReal} :
    x.abs = y.abs ∧ SignType.sign x = SignType.sign y ↔ x = y := by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs, ← y.sign_mul_abs, habs, hsign]
  · rintro rfl
    simp only [eq_self_iff_true, and_self_iff]
#align ereal.sign_eq_and_abs_eq_iff_eq EReal.sign_eq_and_abs_eq_iff_eq

theorem le_iff_sign {x y : EReal} :
    x ≤ y ↔
      SignType.sign x < SignType.sign y ∨
        SignType.sign x = SignType.neg ∧ SignType.sign y = SignType.neg ∧ y.abs ≤ x.abs ∨
          SignType.sign x = SignType.zero ∧ SignType.sign y = SignType.zero ∨
            SignType.sign x = SignType.pos ∧ SignType.sign y = SignType.pos ∧ x.abs ≤ y.abs := by
  constructor
  · intro h
    rcases(sign.monotone h).lt_or_eq with (hs | hs)
    · exact Or.inl hs
    · rw [← x.sign_mul_abs, ← y.sign_mul_abs] at h
      cases SignType.sign y <;> rw [hs] at *
      · simp
      · simp at h⊢
        exact Or.inl h
      · simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]
#align ereal.le_iff_sign EReal.le_iff_sign

instance : CommMonoidWithZero EReal :=
  { EReal.hasMul, EReal.hasOne, EReal.hasZero,
    EReal.mulZeroOneClass with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, eq_self_iff_true, sign_mul, and_self_iff]
    mul_comm := EReal.mul_comm }

instance : PosMulMono EReal :=
  posMulMono_iff_covariant_pos.2
    ⟨by
      rintro ⟨x, x0⟩ a b h; dsimp
      rcases le_iff_sign.mp h with (h | h | h | h)
      · rw [le_iff_sign]
        left
        simp [sign_pos x0, h]
      all_goals
        rw [← x.sign_mul_abs, ← a.sign_mul_abs, ← b.sign_mul_abs, sign_pos x0]
        simp only [h]; dsimp
        simp only [neg_mul, mul_neg, EReal.neg_le_neg_iff, one_mul, le_refl, zero_mul, mul_zero]
      all_goals norm_cast; exact mul_le_mul_left' h.2.2 _⟩

instance : MulPosMono EReal :=
  posMulMono_iff_mulPosMono.1 EReal.posMulMono

instance : PosMulReflectLT EReal :=
  PosMulMono.toPosMulReflectLT

instance : MulPosReflectLT EReal :=
  MulPosMono.toMulPosReflectLT

@[simp, norm_cast]
theorem coe_pow (x : ℝ) (n : ℕ) : (↑(x ^ n) : EReal) = x ^ n :=
  map_pow (⟨coe, coe_one, coe_mul⟩ : ℝ →* EReal) _ _
#align ereal.coe_pow EReal.coe_pow

@[simp, norm_cast]
theorem coe_ennreal_pow (x : ℝ≥0∞) (n : ℕ) : (↑(x ^ n) : EReal) = x ^ n :=
  map_pow (⟨coe, coe_ennreal_one, coe_ennreal_mul⟩ : ℝ≥0∞ →* EReal) _ _
#align ereal.coe_ennreal_pow EReal.coe_ennreal_pow

end EReal

namespace Tactic

open Positivity

private theorem ereal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : EReal) ≠ 0 :=
  EReal.coe_ne_zero.2
#align tactic.ereal_coe_ne_zero tactic.ereal_coe_ne_zero

private theorem ereal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : EReal) :=
  EReal.coe_nonneg.2
#align tactic.ereal_coe_nonneg tactic.ereal_coe_nonneg

private theorem ereal_coe_pos {r : ℝ} : 0 < r → 0 < (r : EReal) :=
  EReal.coe_pos.2
#align tactic.ereal_coe_pos tactic.ereal_coe_pos

private theorem ereal_coe_ennreal_pos {r : ℝ≥0∞} : 0 < r → 0 < (r : EReal) :=
  EReal.coe_ennreal_pos.2
#align tactic.ereal_coe_ennreal_pos tactic.ereal_coe_ennreal_pos

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ereal`. -/
@[positivity]
unsafe def positivity_coe_real_ereal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ <| @coeBase _ _ EReal.hasCoe)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` ereal_coe_pos [p]
      | nonnegative p => nonnegative <$> mk_mapp `` ereal_coe_nonneg [a, p]
      | nonzero p => nonzero <$> mk_mapp `` ereal_coe_ne_zero [a, p]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ereal)` for `r : ℝ`"
#align tactic.positivity_coe_real_ereal tactic.positivity_coe_real_ereal

/-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `ereal`. -/
@[positivity]
unsafe def positivity_coe_ennreal_ereal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ <| @coeBase _ _ EReal.hasCoeENNReal)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` ereal_coe_ennreal_pos [p]
      | _ => nonnegative <$> mk_mapp `ereal.coe_ennreal_nonneg [a]
  | e =>
    pp e >>=
      fail ∘ format.bracket "The expression " " is not of the form `(r : ereal)` for `r : ℝ≥0∞`"
#align tactic.positivity_coe_ennreal_ereal tactic.positivity_coe_ennreal_ereal

end Tactic

