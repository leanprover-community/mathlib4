/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Sign

#align_import data.real.ereal from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# The extended reals [-∞, ∞].

This file defines `EReal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥. It is implemented as `WithBot (WithTop ℝ)`

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.

An ad hoc addition is defined, for which `EReal` is an `AddCommMonoid`, and even an ordered one
(if `a ≤ a'` and `b ≤ b'` then `a + b ≤ a' + b'`).
Note however that addition is badly behaved at `(⊥, ⊤)` and `(⊤, ⊥)` so this can not be upgraded
to a group structure. Our choice is that `⊥ + ⊤ = ⊤ + ⊥ = ⊥`, to make sure that the exponential
and the logarithm between `EReal` and `ℝ≥0∞` respect the operations (notice that the
convention `0 * ∞ = 0` on `ℝ≥0∞` is enforced by measure theory).

An ad hoc subtraction is then defined by `x - y = x + (-y)`. It does not have nice properties,
but it is sometimes convenient to have.

An ad hoc multiplication is defined, for which `EReal` is a `CommMonoidWithZero`. We make the
choice that `0 * x = x * 0 = 0` for any `x` (while the other cases are defined non-ambiguously).
This does not distribute with addition, as `⊥ = ⊥ + ⊤ = 1*⊥ + (-1)*⊥ ≠ (1 - 1) * ⊥ = 0 * ⊥ = 0`.

`EReal` is a `CompleteLinearOrder`; this is deduced by type class inference from
the fact that `WithBot (WithTop L)` is a complete linear order if `L` is
a conditionally complete linear order.

Coercions from `ℝ` and from `ℝ≥0∞` are registered, and their basic properties are proved. The main
one is the real coercion, and is usually referred to just as `coe` (lemmas such as
`EReal.coe_add` deal with this coercion). The one from `ENNReal` is usually called `coe_ennreal`
in the `EReal` namespace.

We define an absolute value `EReal.abs` from `EReal` to `ℝ≥0∞`. Two elements of `EReal` coincide
if and only if they have the same absolute value and the same sign.

## Tags

real, ereal, complete lattice
-/

open Function ENNReal NNReal Set

noncomputable section

/-- ereal : The type `[-∞, ∞]` -/
def EReal := WithBot (WithTop ℝ)
  deriving Bot, Zero, One, Nontrivial, AddMonoid, PartialOrder
#align ereal EReal

instance : ZeroLEOneClass EReal := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop ℝ)))
instance : SupSet EReal := inferInstanceAs (SupSet (WithBot (WithTop ℝ)))
instance : InfSet EReal := inferInstanceAs (InfSet (WithBot (WithTop ℝ)))

instance : CompleteLinearOrder EReal :=
  inferInstanceAs (CompleteLinearOrder (WithBot (WithTop ℝ)))

instance : LinearOrderedAddCommMonoid EReal :=
  inferInstanceAs (LinearOrderedAddCommMonoid (WithBot (WithTop ℝ)))

instance : DenselyOrdered EReal :=
  inferInstanceAs (DenselyOrdered (WithBot (WithTop ℝ)))

/-- The canonical inclusion from reals to ereals. Registered as a coercion. -/
@[coe] def Real.toEReal : ℝ → EReal := some ∘ some
#align real.to_ereal Real.toEReal

namespace EReal

-- things unify with `WithBot.decidableLT` later if we don't provide this explicitly.
instance decidableLT : DecidableRel ((· < ·) : EReal → EReal → Prop) :=
  WithBot.decidableLT
#align ereal.decidable_lt EReal.decidableLT

-- TODO: Provide explicitly, otherwise it is inferred noncomputably from `CompleteLinearOrder`
instance : Top EReal := ⟨some ⊤⟩

instance : Coe ℝ EReal := ⟨Real.toEReal⟩

theorem coe_strictMono : StrictMono Real.toEReal :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono
#align ereal.coe_strict_mono EReal.coe_strictMono

theorem coe_injective : Injective Real.toEReal :=
  coe_strictMono.injective
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
@[coe] def _root_.ENNReal.toEReal : ℝ≥0∞ → EReal
  | ⊤ => ⊤
  | .some x => x.1
#align ennreal.to_ereal ENNReal.toEReal

instance hasCoeENNReal : Coe ℝ≥0∞ EReal :=
  ⟨ENNReal.toEReal⟩
#align ereal.has_coe_ennreal EReal.hasCoeENNReal

instance : Inhabited EReal := ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : ℝ) : EReal) = 0 := rfl
#align ereal.coe_zero EReal.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : ℝ) : EReal) = 1 := rfl
#align ereal.coe_one EReal.coe_one

/-- A recursor for `EReal` in terms of the coercion.

A typical invocation looks like `induction x using EReal.rec`. Note that using `induction`
directly will unfold `EReal` to `Option` which is undesirable.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim]
protected def rec {C : EReal → Sort*} (h_bot : C ⊥) (h_real : ∀ a : ℝ, C a) (h_top : C ⊤) :
    ∀ a : EReal, C a
  | ⊥ => h_bot
  | (a : ℝ) => h_real a
  | ⊤ => h_top
#align ereal.rec EReal.rec

/-- The multiplication on `EReal`. Our definition satisfies `0 * x = x * 0 = 0` for any `x`, and
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

instance : Mul EReal := ⟨EReal.mul⟩

@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : (↑(x * y) : EReal) = x * y :=
  rfl
#align ereal.coe_mul EReal.coe_mul

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
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
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [bot_neg y hy, bot_zero, bot_pos y hy]
    -- 🎉 no goals
  | ⊥, ⊤ => bot_top
  | (x : ℝ), ⊥ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_bot x hx, zero_bot, pos_bot x hx]
    -- 🎉 no goals
  | (x : ℝ), (y : ℝ) => coe_coe _ _
  | (x : ℝ), ⊤ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
    -- 🎉 no goals
  | ⊤, ⊥ => top_bot
  | ⊤, (y : ℝ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
    -- 🎉 no goals
  | ⊤, ⊤ => top_top
#align ereal.induction₂ EReal.induction₂

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
theorem induction₂_symm {P : EReal → EReal → Prop} (symm : Symmetric P) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0) (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x)
    (top_bot : P ⊤ ⊥) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥) (coe_coe : ∀ x y : ℝ, P x y)
    (zero_bot : P 0 ⊥) (neg_bot : ∀ x : ℝ, x < 0 → P x ⊥) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
  @induction₂ P top_top top_pos top_zero top_neg top_bot (fun _ h => symm <| top_pos _ h)
    pos_bot (symm top_zero) coe_coe zero_bot (fun _ h => symm <| top_neg _ h) neg_bot (symm top_bot)
    (fun _ h => symm <| pos_bot _ h) (symm zero_bot) (fun _ h => symm <| neg_bot _ h) bot_bot

/-! `EReal` with its multiplication is a `CommMonoidWithZero`. However, the proof of
associativity by hand is extremely painful (with 125 cases...). Instead, we will deduce it later
on from the facts that the absolute value and the sign are multiplicative functions taking value
in associative objects, and that they characterize an extended real number. For now, we only
record more basic properties of multiplication.
-/

protected theorem mul_comm (x y : EReal) : x * y = y * x := by
  induction' x using EReal.rec with x <;> induction' y using EReal.rec with y <;>
    try { rfl }
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- ⊢ ↑x * ↑y = ↑y * ↑x
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
  rw [← coe_mul, ← coe_mul, mul_comm]
  -- 🎉 no goals
#align ereal.mul_comm EReal.mul_comm

protected theorem one_mul : ∀ x : EReal, 1 * x = x
  | ⊤ => if_pos one_pos
  | ⊥ => if_pos one_pos
  | (x : ℝ) => congr_arg Real.toEReal (one_mul x)

protected theorem zero_mul : ∀ x : EReal, 0 * x = 0
  | ⊤ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
  | ⊥ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
  | (x : ℝ) => congr_arg Real.toEReal (zero_mul x)

instance : MulZeroOneClass EReal where
  one_mul := EReal.one_mul
  mul_one := fun x => by rw [EReal.mul_comm, EReal.one_mul]
                         -- 🎉 no goals
  zero_mul := EReal.zero_mul
  mul_zero := fun x => by rw [EReal.mul_comm, EReal.zero_mul]
                          -- 🎉 no goals

/-! ### Real coercion -/

instance canLift : CanLift EReal ℝ (↑) fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    induction x using EReal.rec
    · simp at hx
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
    · simp at hx
      -- 🎉 no goals
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
  (bot_lt_coe x).ne
#align ereal.bot_ne_coe EReal.bot_ne_coe

@[simp]
theorem coe_lt_top (x : ℝ) : (x : EReal) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _
#align ereal.coe_lt_top EReal.coe_lt_top

@[simp]
theorem coe_ne_top (x : ℝ) : (x : EReal) ≠ ⊤ :=
  (coe_lt_top x).ne
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

theorem range_coe : range Real.toEReal = {⊥, ⊤}ᶜ := by
  ext x
  -- ⊢ x ∈ range Real.toEReal ↔ x ∈ {⊥, ⊤}ᶜ
  induction x using EReal.rec <;> simp
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals

theorem range_coe_eq_Ioo : range Real.toEReal = Ioo ⊥ ⊤ := by
  ext x
  -- ⊢ x ∈ range Real.toEReal ↔ x ∈ Ioo ⊥ ⊤
  induction x using EReal.rec <;> simp
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : (↑(x + y) : EReal) = x + y :=
  rfl
#align ereal.coe_add EReal.coe_add

-- `coe_mul` moved up

@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨Real.toEReal, coe_zero⟩, coe_add⟩ : ℝ →+ EReal) _ _
#align ereal.coe_nsmul EReal.coe_nsmul

#noalign ereal.coe_bit0
#noalign ereal.coe_bit1

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
  lift x to ℝ using ⟨ne_top_of_le_ne_top hy h, hx⟩
  -- ⊢ toReal ↑x ≤ toReal y
  lift y to ℝ using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  -- ⊢ toReal ↑x ≤ toReal ↑y
  simpa using h
  -- 🎉 no goals
#align ereal.to_real_le_to_real EReal.toReal_le_toReal

theorem coe_toReal {x : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toReal : EReal) = x := by
  lift x to ℝ using ⟨hx, h'x⟩
  -- ⊢ ↑(toReal ↑x) = ↑x
  rfl
  -- 🎉 no goals
#align ereal.coe_to_real EReal.coe_toReal

theorem le_coe_toReal {x : EReal} (h : x ≠ ⊤) : x ≤ x.toReal := by
  by_cases h' : x = ⊥
  -- ⊢ x ≤ ↑(toReal x)
  · simp only [h', bot_le]
    -- 🎉 no goals
  · simp only [le_refl, coe_toReal h h']
    -- 🎉 no goals
#align ereal.le_coe_to_real EReal.le_coe_toReal

theorem coe_toReal_le {x : EReal} (h : x ≠ ⊥) : ↑x.toReal ≤ x := by
  by_cases h' : x = ⊤
  -- ⊢ ↑(toReal x) ≤ x
  · simp only [h', le_top]
    -- 🎉 no goals
  · simp only [le_refl, coe_toReal h' h]
    -- 🎉 no goals
#align ereal.coe_to_real_le EReal.coe_toReal_le

theorem eq_top_iff_forall_lt (x : EReal) : x = ⊤ ↔ ∀ y : ℝ, (y : EReal) < x := by
  constructor
  -- ⊢ x = ⊤ → ∀ (y : ℝ), ↑y < x
  · rintro rfl
    -- ⊢ ∀ (y : ℝ), ↑y < ⊤
    exact EReal.coe_lt_top
    -- 🎉 no goals
  · contrapose!
    -- ⊢ x ≠ ⊤ → ∃ y, x ≤ ↑y
    intro h
    -- ⊢ ∃ y, x ≤ ↑y
    exact ⟨x.toReal, le_coe_toReal h⟩
    -- 🎉 no goals
#align ereal.eq_top_iff_forall_lt EReal.eq_top_iff_forall_lt

theorem eq_bot_iff_forall_lt (x : EReal) : x = ⊥ ↔ ∀ y : ℝ, x < (y : EReal) := by
  constructor
  -- ⊢ x = ⊥ → ∀ (y : ℝ), x < ↑y
  · rintro rfl
    -- ⊢ ∀ (y : ℝ), ⊥ < ↑y
    exact bot_lt_coe
    -- 🎉 no goals
  · contrapose!
    -- ⊢ x ≠ ⊥ → ∃ y, ↑y ≤ x
    intro h
    -- ⊢ ∃ y, ↑y ≤ x
    exact ⟨x.toReal, coe_toReal_le h⟩
    -- 🎉 no goals
#align ereal.eq_bot_iff_forall_lt EReal.eq_bot_iff_forall_lt

/-! ### ennreal coercion -/

@[simp]
theorem toReal_coe_ennreal : ∀ {x : ℝ≥0∞}, toReal (x : EReal) = ENNReal.toReal x
  | ⊤ => rfl
  | .some _ => rfl
#align ereal.to_real_coe_ennreal EReal.toReal_coe_ennreal

@[simp]
theorem coe_ennreal_ofReal {x : ℝ} : (ENNReal.ofReal x : EReal) = max x 0 :=
  rfl
#align ereal.coe_ennreal_of_real EReal.coe_ennreal_ofReal

theorem coe_nnreal_eq_coe_real (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) = (x : ℝ) :=
  rfl
#align ereal.coe_nnreal_eq_coe_real EReal.coe_nnreal_eq_coe_real

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

theorem coe_ennreal_strictMono : StrictMono ((↑) : ℝ≥0∞ → EReal) :=
  WithTop.strictMono_iff.2 ⟨fun _ _ => EReal.coe_lt_coe_iff.2, fun _ => coe_lt_top _⟩
#align ereal.coe_ennreal_strict_mono EReal.coe_ennreal_strictMono

theorem coe_ennreal_injective : Injective ((↑) : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.injective
#align ereal.coe_ennreal_injective EReal.coe_ennreal_injective

@[simp]
theorem coe_ennreal_eq_top_iff {x : ℝ≥0∞} : (x : EReal) = ⊤ ↔ x = ⊤ :=
  coe_ennreal_injective.eq_iff' rfl
#align ereal.coe_ennreal_eq_top_iff EReal.coe_ennreal_eq_top_iff

theorem coe_nnreal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) ≠ ⊤ := coe_ne_top x
#align ereal.coe_nnreal_ne_top EReal.coe_nnreal_ne_top

@[simp]
theorem coe_nnreal_lt_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) < ⊤ := coe_lt_top x
#align ereal.coe_nnreal_lt_top EReal.coe_nnreal_lt_top

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
  -- 🎉 no goals
#align ereal.coe_ennreal_eq_zero EReal.coe_ennreal_eq_zero

@[simp, norm_cast]
theorem coe_ennreal_eq_one {x : ℝ≥0∞} : (x : EReal) = 1 ↔ x = 1 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one]
  -- 🎉 no goals
#align ereal.coe_ennreal_eq_one EReal.coe_ennreal_eq_one

@[norm_cast]
theorem coe_ennreal_ne_zero {x : ℝ≥0∞} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  coe_ennreal_eq_zero.not
#align ereal.coe_ennreal_ne_zero EReal.coe_ennreal_ne_zero

@[norm_cast]
theorem coe_ennreal_ne_one {x : ℝ≥0∞} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  coe_ennreal_eq_one.not
#align ereal.coe_ennreal_ne_one EReal.coe_ennreal_ne_one

theorem coe_ennreal_nonneg (x : ℝ≥0∞) : (0 : EReal) ≤ x :=
  coe_ennreal_le_coe_ennreal_iff.2 (zero_le x)
#align ereal.coe_ennreal_nonneg EReal.coe_ennreal_nonneg

@[simp] theorem range_coe_ennreal : range ((↑) : ℝ≥0∞ → EReal) = Set.Ici 0 :=
  Subset.antisymm (range_subset_iff.2 coe_ennreal_nonneg) fun x => match x with
    | ⊥ => fun h => absurd h bot_lt_zero.not_le
    | ⊤ => fun _ => ⟨⊤, rfl⟩
    | (x : ℝ) => fun h => ⟨.some ⟨x, EReal.coe_nonneg.1 h⟩, rfl⟩

instance : CanLift EReal ℝ≥0∞ (↑) (0 ≤ ·) := ⟨range_coe_ennreal.ge⟩

@[simp, norm_cast]
theorem coe_ennreal_pos {x : ℝ≥0∞} : (0 : EReal) < x ↔ 0 < x := by
  rw [← coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]
  -- 🎉 no goals
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
  -- ⊢ ↑(none + y) = ↑none + ↑y
              -- ⊢ ↑(none + none) = ↑none + ↑none
              -- ⊢ ↑(Option.some val✝ + none) = ↑(Option.some val✝) + ↑none
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
                          -- 🎉 no goals
#align ereal.coe_ennreal_add EReal.coe_ennreal_add

private theorem coe_ennreal_top_mul (x : ℝ≥0) : ((⊤ * x : ℝ≥0∞) : EReal) = ⊤ * x := by
  rcases eq_or_ne x 0 with (rfl | h0)
  -- ⊢ ↑(⊤ * ↑0) = ⊤ * ↑↑0
  · simp
    -- 🎉 no goals
  · rw [ENNReal.top_mul (ENNReal.coe_ne_zero.2 h0)]
    -- ⊢ ↑⊤ = ⊤ * ↑↑x
    exact Eq.symm <| if_pos <| NNReal.coe_pos.2 h0.bot_lt
    -- 🎉 no goals

@[simp, norm_cast]
theorem coe_ennreal_mul : ∀ x y : ℝ≥0∞, ((x * y : ℝ≥0∞) : EReal) = (x : EReal) * y
  | ⊤, ⊤ => rfl
  | ⊤, (y : ℝ≥0) => coe_ennreal_top_mul y
  | (x : ℝ≥0), ⊤ => by
    rw [mul_comm, coe_ennreal_top_mul, EReal.mul_comm, coe_ennreal_top]
    -- 🎉 no goals
  | (x : ℝ≥0), (y : ℝ≥0) => by
    simp only [← ENNReal.coe_mul, coe_nnreal_eq_coe_real, NNReal.coe_mul, EReal.coe_mul]
    -- 🎉 no goals
#align ereal.coe_ennreal_mul EReal.coe_ennreal_mul

@[norm_cast]
theorem coe_ennreal_nsmul (n : ℕ) (x : ℝ≥0∞) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨(↑), coe_ennreal_zero⟩, coe_ennreal_add⟩ : ℝ≥0∞ →+ EReal) _ _
#align ereal.coe_ennreal_nsmul EReal.coe_ennreal_nsmul

#noalign ereal.coe_ennreal_bit0
#noalign ereal.coe_ennreal_bit1

/-! ### Order -/

theorem exists_rat_btwn_of_lt :
    ∀ {a b : EReal}, a < b → ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b
  | ⊤, b, h => (not_top_lt h).elim
  | (a : ℝ), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
  | (a : ℝ), (b : ℝ), h => by simp [exists_rat_btwn (EReal.coe_lt_coe_iff.1 h)]
                              -- 🎉 no goals
  | (a : ℝ), ⊤, _ =>
    let ⟨b, hab⟩ := exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
           -- 🎉 no goals
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : ℝ), _ =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
                         -- 🎉 no goals
  | ⊥, ⊤, _ => ⟨0, bot_lt_coe _, coe_lt_top _⟩
#align ereal.exists_rat_btwn_of_lt EReal.exists_rat_btwn_of_lt

theorem lt_iff_exists_rat_btwn {a b : EReal} :
    a < b ↔ ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨_x, ax, xb⟩ => ax.trans xb⟩
#align ereal.lt_iff_exists_rat_btwn EReal.lt_iff_exists_rat_btwn

theorem lt_iff_exists_real_btwn {a b : EReal} : a < b ↔ ∃ x : ℝ, a < x ∧ (x : EReal) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : ℝ), ax, xb⟩,
    fun ⟨_x, ax, xb⟩ => ax.trans xb⟩
#align ereal.lt_iff_exists_real_btwn EReal.lt_iff_exists_real_btwn

/-- The set of numbers in `EReal` that are not equal to `±∞` is equivalent to `ℝ`. -/
def neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ ℝ where
  toFun x := EReal.toReal x
  invFun x := ⟨x, by simp⟩
                     -- 🎉 no goals
  left_inv := fun ⟨x, hx⟩ => by
    lift x to ℝ
    -- ⊢ x ≠ ⊤ ∧ x ≠ ⊥
    · simpa [not_or, and_comm] using hx
      -- 🎉 no goals
    · simp
      -- 🎉 no goals
  right_inv x := by simp
                    -- 🎉 no goals
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
theorem add_eq_bot_iff {x y : EReal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot
#align ereal.add_eq_bot_iff EReal.add_eq_bot_iff

@[simp]
theorem bot_lt_add_iff {x y : EReal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot, not_or]
  -- 🎉 no goals
#align ereal.bot_lt_add_iff EReal.bot_lt_add_iff

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

theorem toReal_add {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x + y) = toReal x + toReal y := by
  lift x to ℝ using ⟨hx, h'x⟩
  -- ⊢ toReal (↑x + y) = toReal ↑x + toReal y
  lift y to ℝ using ⟨hy, h'y⟩
  -- ⊢ toReal (↑x + ↑y) = toReal ↑x + toReal ↑y
  rfl
  -- 🎉 no goals
#align ereal.to_real_add EReal.toReal_add

theorem addLECancellable_coe (x : ℝ) : AddLECancellable (x : EReal)
  | _, ⊤, _ => le_top
  | ⊥, _, _ => bot_le
  | ⊤, (z : ℝ), h => by simp only [coe_add_top, ← coe_add, top_le_iff, coe_ne_top] at h
                        -- 🎉 no goals
  | _, ⊥, h => by simpa using h
                  -- 🎉 no goals
  | (y : ℝ), (z : ℝ), h => by
    simpa only [← coe_add, EReal.coe_le_coe_iff, add_le_add_iff_left] using h
    -- 🎉 no goals

-- porting note: todo: add `MulLECancellable.strictMono*` etc
theorem add_lt_add_right_coe {x y : EReal} (h : x < y) (z : ℝ) : x + z < y + z :=
  not_le.1 <| mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_le
#align ereal.add_lt_add_right_coe EReal.add_lt_add_right_coe

theorem add_lt_add_left_coe {x y : EReal} (h : x < y) (z : ℝ) : (z : EReal) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z
  -- 🎉 no goals
#align ereal.add_lt_add_left_coe EReal.add_lt_add_left_coe

theorem add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  -- ⊢ ⊥ + z < y + t
  · simp [h1, bot_le.trans_lt h2]
    -- 🎉 no goals
  · lift x to ℝ using ⟨h1.ne_top, hx⟩
    -- ⊢ ↑x + z < y + t
    calc (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
    _ ≤ y + t := add_le_add_right h1.le _
#align ereal.add_lt_add EReal.add_lt_add

theorem add_lt_add_of_lt_of_le' {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hbot : t ≠ ⊥)
    (htop : t = ⊤ → z = ⊤ → x = ⊥) : x + z < y + t := by
  rcases h'.eq_or_lt with (rfl | hlt)
  -- ⊢ x + z < y + z
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    -- ⊢ x + ⊤ < y + ⊤
    · obtain rfl := htop rfl rfl
      -- ⊢ ⊥ + ⊤ < y + ⊤
      simpa
      -- 🎉 no goals
    lift z to ℝ using ⟨hz, hbot⟩
    -- ⊢ x + ↑z < y + ↑z
    exact add_lt_add_right_coe h z
    -- 🎉 no goals
  · exact add_lt_add h hlt
    -- 🎉 no goals

/-- See also `EReal.add_lt_add_of_lt_of_le'` for a version with weaker but less convenient
assumptions. -/
theorem add_lt_add_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x + z < y + t :=
  add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') <| fun ht' => (ht ht').elim
#align ereal.add_lt_add_of_lt_of_le EReal.add_lt_add_of_lt_of_le

theorem add_lt_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y < ⊤ := by
  rw [← EReal.top_add_top]
  -- ⊢ x + y < ⊤ + ⊤
  exact EReal.add_lt_add hx.lt_top hy.lt_top
  -- 🎉 no goals
#align ereal.add_lt_top EReal.add_lt_top

/-! ### Negation -/

/-- negation on `EReal` -/
protected def neg : EReal → EReal
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℝ) => (-x : ℝ)
#align ereal.neg EReal.neg

instance : Neg EReal := ⟨EReal.neg⟩

instance : SubNegZeroMonoid EReal where
  neg_zero := congr_arg Real.toEReal neg_zero

@[simp]
theorem neg_top : -(⊤ : EReal) = ⊥ :=
  rfl
#align ereal.neg_top EReal.neg_top

@[simp]
theorem neg_bot : -(⊥ : EReal) = ⊤ :=
  rfl
#align ereal.neg_bot EReal.neg_bot

@[simp, norm_cast] theorem coe_neg (x : ℝ) : (↑(-x) : EReal) = -↑x := rfl
#align ereal.coe_neg EReal.coe_neg
#align ereal.neg_def EReal.coe_neg

@[simp, norm_cast] theorem coe_sub (x y : ℝ) : (↑(x - y) : EReal) = x - y := rfl
#align ereal.coe_sub EReal.coe_sub

@[norm_cast]
theorem coe_zsmul (n : ℤ) (x : ℝ) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : ℝ →+ EReal) coe_neg _ _
#align ereal.coe_zsmul EReal.coe_zsmul

instance : InvolutiveNeg EReal where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℝ) => congr_arg Real.toEReal (neg_neg a)

@[simp]
theorem toReal_neg : ∀ {a : EReal}, toReal (-a) = -toReal a
  | ⊤ => by simp
            -- 🎉 no goals
  | ⊥ => by simp
            -- 🎉 no goals
  | (x : ℝ) => rfl
#align ereal.to_real_neg EReal.toReal_neg

@[simp]
theorem neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl
#align ereal.neg_eq_top_iff EReal.neg_eq_top_iff

@[simp]
theorem neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl
#align ereal.neg_eq_bot_iff EReal.neg_eq_bot_iff

@[simp]
theorem neg_eq_zero_iff {x : EReal} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero
#align ereal.neg_eq_zero_iff EReal.neg_eq_zero_iff

theorem neg_strictAnti : StrictAnti (- · : EReal → EReal) :=
  WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨bot_lt_top, fun _ => coe_lt_top _⟩⟩

@[simp] theorem neg_le_neg_iff {a b : EReal} : -a ≤ -b ↔ b ≤ a := neg_strictAnti.le_iff_le
#align ereal.neg_le_neg_iff EReal.neg_le_neg_iff

-- porting note: new lemma
@[simp] theorem neg_lt_neg_iff {a b : EReal} : -a < -b ↔ b < a := neg_strictAnti.lt_iff_lt

/-- `-a ≤ b ↔ -b ≤ a` on `EReal`. -/
protected theorem neg_le {a b : EReal} : -a ≤ b ↔ -b ≤ a := by
 rw [← neg_le_neg_iff, neg_neg]
 -- 🎉 no goals
#align ereal.neg_le EReal.neg_le

/-- if `-a ≤ b` then `-b ≤ a` on `EReal`. -/
protected theorem neg_le_of_neg_le {a b : EReal} (h : -a ≤ b) : -b ≤ a := EReal.neg_le.mp h
#align ereal.neg_le_of_neg_le EReal.neg_le_of_neg_le

/-- `a ≤ -b → b ≤ -a` on ereal -/
theorem le_neg_of_le_neg {a b : EReal} (h : a ≤ -b) : b ≤ -a := by
  rwa [← neg_neg b, EReal.neg_le, neg_neg]
  -- 🎉 no goals
#align ereal.le_neg_of_le_neg EReal.le_neg_of_le_neg

/-- Negation as an order reversing isomorphism on `EReal`. -/
def negOrderIso : EReal ≃o ERealᵒᵈ :=
  { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }
#align ereal.neg_order_iso EReal.negOrderIso

theorem neg_lt_iff_neg_lt {a b : EReal} : -a < b ↔ -b < a := by
  rw [← neg_lt_neg_iff, neg_neg]
  -- 🎉 no goals
#align ereal.neg_lt_iff_neg_lt EReal.neg_lt_iff_neg_lt

theorem neg_lt_of_neg_lt {a b : EReal} (h : -a < b) : -b < a := neg_lt_iff_neg_lt.1 h
#align ereal.neg_lt_of_neg_lt EReal.neg_lt_of_neg_lt

/-!
### Subtraction

Subtraction on `EReal` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `EReal`, beyond `SubNegZeroMonoid`, because of this bad behavior.
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
                                                     -- 🎉 no goals
                                                                    -- 🎉 no goals
#align ereal.sub_lt_sub_of_lt_of_le EReal.sub_lt_sub_of_lt_of_le

theorem coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (x : ℝ) :
    (x : EReal) = Real.toNNReal x - Real.toNNReal (-x) := by
  rcases le_total 0 x with (h | h)
  -- ⊢ ↑x = ↑↑(Real.toNNReal x) - ↑↑(Real.toNNReal (-x))
  · lift x to ℝ≥0 using h
    -- ⊢ ↑↑x = ↑↑(Real.toNNReal ↑x) - ↑↑(Real.toNNReal (-↑x))
    rw [Real.toNNReal_of_nonpos (neg_nonpos.mpr x.coe_nonneg), Real.toNNReal_coe, ENNReal.coe_zero,
      coe_ennreal_zero, sub_zero]
    rfl
    -- 🎉 no goals
  · rw [Real.toNNReal_of_nonpos h, ENNReal.coe_zero, coe_ennreal_zero, coe_nnreal_eq_coe_real,
      Real.coe_toNNReal, zero_sub, coe_neg, neg_neg]
    exact neg_nonneg.2 h
    -- 🎉 no goals
#align ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal

theorem toReal_sub {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x - y) = toReal x - toReal y := by
  lift x to ℝ using ⟨hx, h'x⟩
  -- ⊢ toReal (↑x - y) = toReal ↑x - toReal y
  lift y to ℝ using ⟨hy, h'y⟩
  -- ⊢ toReal (↑x - ↑y) = toReal ↑x - toReal ↑y
  rfl
  -- 🎉 no goals
#align ereal.to_real_sub EReal.toReal_sub

/-! ### Multiplication -/

@[simp] theorem top_mul_top : (⊤ : EReal) * ⊤ = ⊤ := rfl
#align ereal.top_mul_top EReal.top_mul_top

@[simp] theorem top_mul_bot : (⊤ : EReal) * ⊥ = ⊥ := rfl
#align ereal.top_mul_bot EReal.top_mul_bot

@[simp] theorem bot_mul_top : (⊥ : EReal) * ⊤ = ⊥ := rfl
#align ereal.bot_mul_top EReal.bot_mul_top

@[simp] theorem bot_mul_bot : (⊥ : EReal) * ⊥ = ⊤ := rfl
#align ereal.bot_mul_bot EReal.bot_mul_bot

theorem coe_mul_top_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊤ = ⊤ :=
  if_pos h
#align ereal.coe_mul_top_of_pos EReal.coe_mul_top_of_pos

theorem coe_mul_top_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊤ = ⊥ :=
  (if_neg h.not_lt).trans (if_neg h.ne)
#align ereal.coe_mul_top_of_neg EReal.coe_mul_top_of_neg

theorem top_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊤ : EReal) * x = ⊤ :=
  if_pos h
#align ereal.top_mul_coe_of_pos EReal.top_mul_coe_of_pos

theorem top_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊤ : EReal) * x = ⊥ :=
  (if_neg h.not_lt).trans (if_neg h.ne)
#align ereal.top_mul_coe_of_neg EReal.top_mul_coe_of_neg

theorem mul_top_of_pos : ∀ {x : EReal}, 0 < x → x * ⊤ = ⊤
  | ⊥, h => absurd h not_lt_bot
  | (x : ℝ), h => coe_mul_top_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl
#align ereal.mul_top_of_pos EReal.mul_top_of_pos

theorem mul_top_of_neg : ∀ {x : EReal}, x < 0 → x * ⊤ = ⊥
  | ⊥, _ => rfl
  | (x : ℝ), h => coe_mul_top_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt
#align ereal.mul_top_of_neg EReal.mul_top_of_neg

theorem top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤ := by
  rw [EReal.mul_comm]
  -- ⊢ x * ⊤ = ⊤
  exact mul_top_of_pos h
  -- 🎉 no goals
#align ereal.top_mul_of_pos EReal.top_mul_of_pos

theorem top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥ := by
  rw [EReal.mul_comm]
  -- ⊢ x * ⊤ = ⊥
  exact mul_top_of_neg h
  -- 🎉 no goals
#align ereal.top_mul_of_neg EReal.top_mul_of_neg

theorem coe_mul_bot_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊥ = ⊥ :=
  if_pos h
#align ereal.coe_mul_bot_of_pos EReal.coe_mul_bot_of_pos

theorem coe_mul_bot_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊥ = ⊤ :=
  (if_neg h.not_lt).trans (if_neg h.ne)
#align ereal.coe_mul_bot_of_neg EReal.coe_mul_bot_of_neg

theorem bot_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊥ : EReal) * x = ⊥ :=
  if_pos h
#align ereal.bot_mul_coe_of_pos EReal.bot_mul_coe_of_pos

theorem bot_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊥ : EReal) * x = ⊤ :=
  (if_neg h.not_lt).trans (if_neg h.ne)
#align ereal.bot_mul_coe_of_neg EReal.bot_mul_coe_of_neg

theorem mul_bot_of_pos : ∀ {x : EReal}, 0 < x → x * ⊥ = ⊥
  | ⊥, h => absurd h not_lt_bot
  | (x : ℝ), h => coe_mul_bot_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl
#align ereal.mul_bot_of_pos EReal.mul_bot_of_pos

theorem mul_bot_of_neg : ∀ {x : EReal}, x < 0 → x * ⊥ = ⊤
  | ⊥, _ => rfl
  | (x : ℝ), h => coe_mul_bot_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt
#align ereal.mul_bot_of_neg EReal.mul_bot_of_neg

theorem bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥ := by
  rw [EReal.mul_comm]
  -- ⊢ x * ⊥ = ⊥
  exact mul_bot_of_pos h
  -- 🎉 no goals
#align ereal.bot_mul_of_pos EReal.bot_mul_of_pos

theorem bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤ := by
  rw [EReal.mul_comm]
  -- ⊢ x * ⊥ = ⊤
  exact mul_bot_of_neg h
  -- 🎉 no goals
#align ereal.bot_mul_of_neg EReal.bot_mul_of_neg

theorem toReal_mul {x y : EReal} : toReal (x * y) = toReal x * toReal y := by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [coe_mul_bot_of_pos h]
  | neg_bot _ h => simp [coe_mul_bot_of_neg h]
#align ereal.to_real_mul EReal.toReal_mul

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for all
`x`, `y`. -/
@[elab_as_elim]
theorem induction₂_neg_left {P : EReal → EReal → Prop} (neg_left : ∀ {x y}, P x y → P (-x) y)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (zero_top : P 0 ⊤) (zero_bot : P 0 ⊥)
    (pos_top : ∀ x : ℝ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℝ, P x y) : ∀ x y, P x y :=
  have : ∀ y, (∀ x : ℝ, 0 < x → P x y) → ∀ x : ℝ, x < 0 → P x y := fun _ h x hx =>
    neg_neg (x : EReal) ▸ neg_left <| h _ (neg_pos_of_neg hx)
  @induction₂ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (this _ pos_top) (this _ pos_bot) (neg_left top_top)
    (fun x hx => neg_left <| top_pos x hx) (neg_left top_zero)
    (fun x hx => neg_left <| top_neg x hx) (neg_left top_bot)

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P` is symmetric and `P x y` implies
`P (-x) y` for all `x`, `y`. -/
@[elab_as_elim]
theorem induction₂_symm_neg {P : EReal → EReal → Prop}
    (symm : Symmetric P) (neg_left : ∀ {x y}, P x y → P (-x) y) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0) (coe_coe : ∀ x y : ℝ, P x y) :
    ∀ x y, P x y :=
  have neg_right : ∀ {x y}, P x y → P x (-y) := fun h => symm <| neg_left <| symm h
  have : ∀ x, (∀ y : ℝ, 0 < y → P x y) → ∀ y : ℝ, y < 0 → P x y := fun _ h y hy =>
    neg_neg (y : EReal) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos top_zero (this _ top_pos) (neg_right top_top)
    (symm top_zero) (symm <| neg_left top_zero) (fun x hx => symm <| top_pos x hx)
    (fun x hx => symm <| neg_left <| top_pos x hx) coe_coe

protected theorem neg_mul (x y : EReal) : -x * y = -(x * y) := by
  induction x, y using induction₂_neg_left with
  | top_zero | zero_top | zero_bot => simp only [zero_mul, mul_zero, neg_zero]
  | top_top | top_bot => rfl
  | neg_left h => rw [h, neg_neg, neg_neg]
  | coe_coe => norm_cast; exact neg_mul _ _
  | top_pos _ h => rw [top_mul_coe_of_pos h, neg_top, bot_mul_coe_of_pos h]
  | pos_top _ h => rw [coe_mul_top_of_pos h, neg_top, ← coe_neg,
    coe_mul_top_of_neg (neg_neg_of_pos h)]
  | top_neg _ h => rw [top_mul_coe_of_neg h, neg_top, bot_mul_coe_of_neg h, neg_bot]
  | pos_bot _ h => rw [coe_mul_bot_of_pos h, neg_bot, ← coe_neg,
    coe_mul_bot_of_neg (neg_neg_of_pos h)]
#align ereal.neg_mul EReal.neg_mul

instance : HasDistribNeg EReal where
  neg_mul := EReal.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm, x.mul_comm]
    -- ⊢ -y * x = -(y * x)
    exact y.neg_mul x
    -- 🎉 no goals

/-! ### Absolute value -/

-- porting note: todo: use `Real.nnabs` for the case `(x : ℝ)`
/-- The absolute value from `EReal` to `ℝ≥0∞`, mapping `⊥` and `⊤` to `⊤` and
a real `x` to `|x|`. -/
protected def abs : EReal → ℝ≥0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : ℝ) => ENNReal.ofReal |x|
#align ereal.abs EReal.abs

@[simp] theorem abs_top : (⊤ : EReal).abs = ⊤ := rfl
#align ereal.abs_top EReal.abs_top

@[simp] theorem abs_bot : (⊥ : EReal).abs = ⊤ := rfl
#align ereal.abs_bot EReal.abs_bot

theorem abs_def (x : ℝ) : (x : EReal).abs = ENNReal.ofReal |x| := rfl
#align ereal.abs_def EReal.abs_def

theorem abs_coe_lt_top (x : ℝ) : (x : EReal).abs < ⊤ :=
  ENNReal.ofReal_lt_top
#align ereal.abs_coe_lt_top EReal.abs_coe_lt_top

@[simp]
theorem abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0 := by
  induction x using EReal.rec
  · simp only [abs_bot, ENNReal.top_ne_zero, bot_ne_zero]
    -- 🎉 no goals
  · simp only [abs_def, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
    -- 🎉 no goals
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]
    -- 🎉 no goals
#align ereal.abs_eq_zero_iff EReal.abs_eq_zero_iff

@[simp]
theorem abs_zero : (0 : EReal).abs = 0 := by rw [abs_eq_zero_iff]
                                             -- 🎉 no goals
#align ereal.abs_zero EReal.abs_zero

@[simp]
theorem coe_abs (x : ℝ) : ((x : EReal).abs : EReal) = (|x| : ℝ) := by
  rw [abs_def, ← Real.coe_nnabs, ENNReal.ofReal_coe_nnreal]; rfl
  -- ⊢ ↑↑(↑Real.nnabs x) = ↑↑(↑Real.nnabs x)
                                                             -- 🎉 no goals
#align ereal.coe_abs EReal.coe_abs

@[simp]
protected theorem abs_neg : ∀ x : EReal, (-x).abs = x.abs
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℝ) => by rw [abs_def, ← coe_neg, abs_def, abs_neg]
                  -- 🎉 no goals

@[simp]
theorem abs_mul (x y : EReal) : (x * y).abs = x.abs * y.abs := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [zero_mul, mul_zero, abs_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, abs_top, ENNReal.top_mul]
    rw [Ne.def, abs_eq_zero_iff, coe_eq_zero]
    exact h.ne'
  | neg_left h => rwa [neg_mul, EReal.abs_neg, EReal.abs_neg]
#align ereal.abs_mul EReal.abs_mul

/-! ### Sign -/

open SignType (sign)

theorem sign_top : sign (⊤ : EReal) = 1 := rfl
#align ereal.sign_top EReal.sign_top

theorem sign_bot : sign (⊥ : EReal) = -1 := rfl
#align ereal.sign_bot EReal.sign_bot

@[simp]
theorem sign_coe (x : ℝ) : sign (x : EReal) = sign x := by
  simp only [sign, OrderHom.coe_mk, EReal.coe_pos, EReal.coe_neg']
  -- 🎉 no goals
#align ereal.sign_coe EReal.sign_coe

@[simp, norm_cast]
theorem coe_coe_sign (x : SignType) : ((x : ℝ) : EReal) = x := by cases x <;> rfl
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals
                                                                              -- 🎉 no goals

@[simp] theorem sign_neg : ∀ x : EReal, sign (-x) = -sign x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℝ) => by rw [← coe_neg, sign_coe, sign_coe, Left.sign_neg]
                  -- 🎉 no goals

@[simp]
theorem sign_mul (x y : EReal) : sign (x * y) = sign x * sign y := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [zero_mul, mul_zero, sign_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, sign_coe, _root_.sign_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, sign_top, one_mul, sign_pos (EReal.coe_pos.2 h)]
  | neg_left h => rw [neg_mul, sign_neg, sign_neg, h, neg_mul]
#align ereal.sign_mul EReal.sign_mul

@[simp] protected theorem sign_mul_abs : ∀ x : EReal, (sign x * x.abs : EReal) = x
  | ⊥ => by simp
            -- 🎉 no goals
  | ⊤ => by simp
            -- 🎉 no goals
  | (x : ℝ) => by rw [sign_coe, coe_abs, ← coe_coe_sign, ← coe_mul, sign_mul_abs]
                  -- 🎉 no goals
#align ereal.sign_mul_abs EReal.sign_mul_abs

@[simp] protected theorem abs_mul_sign (x : EReal) : (x.abs * sign x : EReal) = x := by
  rw [EReal.mul_comm, EReal.sign_mul_abs]
  -- 🎉 no goals

theorem sign_eq_and_abs_eq_iff_eq {x y : EReal} :
    x.abs = y.abs ∧ sign x = sign y ↔ x = y := by
  constructor
  -- ⊢ EReal.abs x = EReal.abs y ∧ ↑sign x = ↑sign y → x = y
  · rintro ⟨habs, hsign⟩
    -- ⊢ x = y
    rw [← x.sign_mul_abs, ← y.sign_mul_abs, habs, hsign]
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ EReal.abs x = EReal.abs x ∧ ↑sign x = ↑sign x
    exact ⟨rfl, rfl⟩
    -- 🎉 no goals
#align ereal.sign_eq_and_abs_eq_iff_eq EReal.sign_eq_and_abs_eq_iff_eq

theorem le_iff_sign {x y : EReal} :
    x ≤ y ↔ sign x < sign y ∨
      sign x = SignType.neg ∧ sign y = SignType.neg ∧ y.abs ≤ x.abs ∨
        sign x = SignType.zero ∧ sign y = SignType.zero ∨
          sign x = SignType.pos ∧ sign y = SignType.pos ∧ x.abs ≤ y.abs := by
  constructor
  -- ⊢ x ≤ y → ↑sign x < ↑sign y ∨ ↑sign x = SignType.neg ∧ ↑sign y = SignType.neg  …
  · intro h
    -- ⊢ ↑sign x < ↑sign y ∨ ↑sign x = SignType.neg ∧ ↑sign y = SignType.neg ∧ EReal. …
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    -- ⊢ ↑sign x = SignType.neg ∧ ↑sign y = SignType.neg ∧ EReal.abs y ≤ EReal.abs x  …
    rw [← x.sign_mul_abs, ← y.sign_mul_abs] at h
    -- ⊢ ↑sign x = SignType.neg ∧ ↑sign y = SignType.neg ∧ EReal.abs y ≤ EReal.abs x  …
    cases hy : sign y <;> rw [hs, hy] at h ⊢
                          -- ⊢ SignType.zero = SignType.neg ∧ SignType.zero = SignType.neg ∧ EReal.abs y ≤  …
                          -- ⊢ SignType.neg = SignType.neg ∧ SignType.neg = SignType.neg ∧ EReal.abs y ≤ ER …
                          -- ⊢ SignType.pos = SignType.neg ∧ SignType.pos = SignType.neg ∧ EReal.abs y ≤ ER …
    · simp
      -- 🎉 no goals
    · left; simpa using h
      -- ⊢ SignType.neg = SignType.neg ∧ SignType.neg = SignType.neg ∧ EReal.abs y ≤ ER …
            -- 🎉 no goals
    · right; right; simpa using h
      -- ⊢ SignType.pos = SignType.zero ∧ SignType.pos = SignType.zero ∨ SignType.pos = …
             -- ⊢ SignType.pos = SignType.pos ∧ SignType.pos = SignType.pos ∧ EReal.abs x ≤ ER …
                    -- 🎉 no goals
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
      -- 🎉 no goals
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]
    -- 🎉 no goals
#align ereal.le_iff_sign EReal.le_iff_sign

instance : CommMonoidWithZero EReal :=
  { inferInstanceAs (MulZeroOneClass EReal) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      -- ⊢ EReal.abs (x * y * z) = EReal.abs (x * (y * z)) ∧ ↑sign (x * y * z) = ↑sign  …
      simp only [mul_assoc, abs_mul, eq_self_iff_true, sign_mul, and_self_iff]
      -- 🎉 no goals
    mul_comm := EReal.mul_comm }

instance : PosMulMono EReal := posMulMono_iff_covariant_pos.2 <| .mk <| by
  rintro ⟨x, x0⟩ a b h
  -- ⊢ (fun x y => ↑x * y) { val := x, property := x0 } a ≤ (fun x y => ↑x * y) { v …
  simp only [le_iff_sign, EReal.sign_mul, sign_pos x0, one_mul, EReal.abs_mul] at h ⊢
  -- ⊢ ↑sign a < ↑sign b ∨ ↑sign a = SignType.neg ∧ ↑sign b = SignType.neg ∧ EReal. …
  exact h.imp_right <| Or.imp (And.imp_right <| And.imp_right (mul_le_mul_left' · _)) <|
    Or.imp_right <| And.imp_right <| And.imp_right (mul_le_mul_left' · _)

instance : MulPosMono EReal := posMulMono_iff_mulPosMono.1 inferInstance

instance : PosMulReflectLT EReal := PosMulMono.toPosMulReflectLT

instance : MulPosReflectLT EReal :=
  MulPosMono.toMulPosReflectLT

@[simp, norm_cast]
theorem coe_pow (x : ℝ) (n : ℕ) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : ℝ →* EReal) _ _
#align ereal.coe_pow EReal.coe_pow

@[simp, norm_cast]
theorem coe_ennreal_pow (x : ℝ≥0∞) (n : ℕ) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_ennreal_one⟩, coe_ennreal_mul⟩ : ℝ≥0∞ →* EReal) _ _
#align ereal.coe_ennreal_pow EReal.coe_ennreal_pow

end EReal

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/6038): restore
/-
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

/-- Extension for the `positivity` tactic: cast from `ℝ` to `EReal`. -/
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

/-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `EReal`. -/
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
-/
