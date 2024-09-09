/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Sign

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

open Function ENNReal NNReal Set SignType

noncomputable section

/-- ereal : The type `[-∞, ∞]` -/
def EReal := WithBot (WithTop ℝ)
  deriving Bot, Zero, One, Nontrivial, AddMonoid, PartialOrder

instance : ZeroLEOneClass EReal := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop ℝ)))
instance : SupSet EReal := inferInstanceAs (SupSet (WithBot (WithTop ℝ)))
instance : InfSet EReal := inferInstanceAs (InfSet (WithBot (WithTop ℝ)))

instance : CompleteLinearOrder EReal :=
  inferInstanceAs (CompleteLinearOrder (WithBot (WithTop ℝ)))

instance : LinearOrderedAddCommMonoid EReal :=
  inferInstanceAs (LinearOrderedAddCommMonoid (WithBot (WithTop ℝ)))

instance : AddCommMonoidWithOne EReal :=
  inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop ℝ)))

instance : DenselyOrdered EReal :=
  inferInstanceAs (DenselyOrdered (WithBot (WithTop ℝ)))

/-- The canonical inclusion from reals to ereals. Registered as a coercion. -/
@[coe] def Real.toEReal : ℝ → EReal := some ∘ some

namespace EReal

-- things unify with `WithBot.decidableLT` later if we don't provide this explicitly.
instance decidableLT : DecidableRel ((· < ·) : EReal → EReal → Prop) :=
  WithBot.decidableLT

-- TODO: Provide explicitly, otherwise it is inferred noncomputably from `CompleteLinearOrder`
instance : Top EReal := ⟨some ⊤⟩

instance : Coe ℝ EReal := ⟨Real.toEReal⟩

theorem coe_strictMono : StrictMono Real.toEReal :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

theorem coe_injective : Injective Real.toEReal :=
  coe_strictMono.injective

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℝ} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : ℝ} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℝ} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : ℝ} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_injective.ne_iff

/-- The canonical map from nonnegative extended reals to extended reals -/
@[coe] def _root_.ENNReal.toEReal : ℝ≥0∞ → EReal
  | ⊤ => ⊤
  | .some x => x.1

instance hasCoeENNReal : Coe ℝ≥0∞ EReal :=
  ⟨ENNReal.toEReal⟩

instance : Inhabited EReal := ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : ℝ) : EReal) = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℝ) : EReal) = 1 := rfl

/-- A recursor for `EReal` in terms of the coercion.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {C : EReal → Sort*} (h_bot : C ⊥) (h_real : ∀ a : ℝ, C a) (h_top : C ⊤) :
    ∀ a : EReal, C a
  | ⊥ => h_bot
  | (a : ℝ) => h_real a
  | ⊤ => h_top

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

instance : Mul EReal := ⟨EReal.mul⟩

@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : (↑(x * y) : EReal) = x * y :=
  rfl

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
  | ⊥, ⊤ => bot_top
  | (x : ℝ), ⊥ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_bot x hx, zero_bot, pos_bot x hx]
  | (x : ℝ), (y : ℝ) => coe_coe _ _
  | (x : ℝ), ⊤ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : ℝ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `EReal`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
theorem induction₂_symm {P : EReal → EReal → Prop} (symm : ∀ {x y}, P x y → P y x)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℝ, P x y) (zero_bot : P 0 ⊥) (neg_bot : ∀ x : ℝ, x < 0 → P x ⊥)
    (bot_bot : P ⊥ ⊥) : ∀ x y, P x y :=
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
  induction x <;> induction y  <;>
    try { rfl }
  rw [← coe_mul, ← coe_mul, mul_comm]

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
  zero_mul := EReal.zero_mul
  mul_zero := fun x => by rw [EReal.mul_comm, EReal.zero_mul]

/-! ### Real coercion -/

instance canLift : CanLift EReal ℝ (↑) fun r => r ≠ ⊤ ∧ r ≠ ⊥ where
  prf x hx := by
    induction x
    · simp at hx
    · simp
    · simp at hx

/-- The map from extended reals to reals sending infinities to zero. -/
def toReal : EReal → ℝ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => x

@[simp]
theorem toReal_top : toReal ⊤ = 0 :=
  rfl

@[simp]
theorem toReal_bot : toReal ⊥ = 0 :=
  rfl

@[simp]
theorem toReal_zero : toReal 0 = 0 :=
  rfl

@[simp]
theorem toReal_one : toReal 1 = 1 :=
  rfl

@[simp]
theorem toReal_coe (x : ℝ) : toReal (x : EReal) = x :=
  rfl

@[simp]
theorem bot_lt_coe (x : ℝ) : (⊥ : EReal) < x :=
  WithBot.bot_lt_coe _

@[simp]
theorem coe_ne_bot (x : ℝ) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe x).ne'

@[simp]
theorem bot_ne_coe (x : ℝ) : (⊥ : EReal) ≠ x :=
  (bot_lt_coe x).ne

@[simp]
theorem coe_lt_top (x : ℝ) : (x : EReal) < ⊤ :=
  WithBot.coe_lt_coe.2 <| WithTop.coe_lt_top _

@[simp]
theorem coe_ne_top (x : ℝ) : (x : EReal) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
theorem top_ne_coe (x : ℝ) : (⊤ : EReal) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
theorem bot_lt_zero : (⊥ : EReal) < 0 :=
  bot_lt_coe 0

@[simp]
theorem bot_ne_zero : (⊥ : EReal) ≠ 0 :=
  (coe_ne_bot 0).symm

@[simp]
theorem zero_ne_bot : (0 : EReal) ≠ ⊥ :=
  coe_ne_bot 0

@[simp]
theorem zero_lt_top : (0 : EReal) < ⊤ :=
  coe_lt_top 0

@[simp]
theorem zero_ne_top : (0 : EReal) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
theorem top_ne_zero : (⊤ : EReal) ≠ 0 :=
  (coe_ne_top 0).symm

theorem range_coe : range Real.toEReal = {⊥, ⊤}ᶜ := by
  ext x
  induction x <;> simp

theorem range_coe_eq_Ioo : range Real.toEReal = Ioo ⊥ ⊤ := by
  ext x
  induction x <;> simp

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : (↑(x + y) : EReal) = x + y :=
  rfl

-- `coe_mul` moved up

@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨Real.toEReal, coe_zero⟩, coe_add⟩ : ℝ →+ EReal) _ _

@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : EReal) = 0 ↔ x = 0 :=
  EReal.coe_eq_coe_iff

@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : EReal) = 1 ↔ x = 1 :=
  EReal.coe_eq_coe_iff

theorem coe_ne_zero {x : ℝ} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  EReal.coe_ne_coe_iff

theorem coe_ne_one {x : ℝ} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  EReal.coe_ne_coe_iff

@[simp, norm_cast]
protected theorem coe_nonneg {x : ℝ} : (0 : EReal) ≤ x ↔ 0 ≤ x :=
  EReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_nonpos {x : ℝ} : (x : EReal) ≤ 0 ↔ x ≤ 0 :=
  EReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_pos {x : ℝ} : (0 : EReal) < x ↔ 0 < x :=
  EReal.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_neg' {x : ℝ} : (x : EReal) < 0 ↔ x < 0 :=
  EReal.coe_lt_coe_iff

theorem toReal_le_toReal {x y : EReal} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toReal ≤ y.toReal := by
  lift x to ℝ using ⟨ne_top_of_le_ne_top hy h, hx⟩
  lift y to ℝ using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
  simpa using h

theorem coe_toReal {x : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toReal : EReal) = x := by
  lift x to ℝ using ⟨hx, h'x⟩
  rfl

theorem le_coe_toReal {x : EReal} (h : x ≠ ⊤) : x ≤ x.toReal := by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_toReal h h']

theorem coe_toReal_le {x : EReal} (h : x ≠ ⊥) : ↑x.toReal ≤ x := by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_toReal h' h]

theorem eq_top_iff_forall_lt (x : EReal) : x = ⊤ ↔ ∀ y : ℝ, (y : EReal) < x := by
  constructor
  · rintro rfl
    exact EReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toReal, le_coe_toReal h⟩

theorem eq_bot_iff_forall_lt (x : EReal) : x = ⊥ ↔ ∀ y : ℝ, x < (y : EReal) := by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.toReal, coe_toReal_le h⟩

/-! ### Intervals and coercion from reals -/

lemma exists_between_coe_real {x z : EReal} (h : x < z) : ∃ y : ℝ, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction a with
  | h_bot => exact (not_lt_bot ha₁).elim
  | h_real a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | h_top => exact (not_top_lt ha₂).elim

@[simp]
lemma image_coe_Icc (x y : ℝ) : Real.toEReal '' Icc x y = Icc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Icc, WithBot.image_coe_Icc]
  rfl

@[simp]
lemma image_coe_Ico (x y : ℝ) : Real.toEReal '' Ico x y = Ico ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ico, WithBot.image_coe_Ico]
  rfl

@[simp]
lemma image_coe_Ici (x : ℝ) : Real.toEReal '' Ici x = Ico ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ici, WithBot.image_coe_Ico]
  rfl

@[simp]
lemma image_coe_Ioc (x y : ℝ) : Real.toEReal '' Ioc x y = Ioc ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioc, WithBot.image_coe_Ioc]
  rfl

@[simp]
lemma image_coe_Ioo (x y : ℝ) : Real.toEReal '' Ioo x y = Ioo ↑x ↑y := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioo, WithBot.image_coe_Ioo]
  rfl

@[simp]
lemma image_coe_Ioi (x : ℝ) : Real.toEReal '' Ioi x = Ioo ↑x ⊤ := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Ioi, WithBot.image_coe_Ioo]
  rfl

@[simp]
lemma image_coe_Iic (x : ℝ) : Real.toEReal '' Iic x = Ioc ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iic, WithBot.image_coe_Iic]
  rfl

@[simp]
lemma image_coe_Iio (x : ℝ) : Real.toEReal '' Iio x = Ioo ⊥ ↑x := by
  refine (image_comp WithBot.some WithTop.some _).trans ?_
  rw [WithTop.image_coe_Iio, WithBot.image_coe_Iio]
  rfl

@[simp]
lemma preimage_coe_Ici (x : ℝ) : Real.toEReal ⁻¹' Ici x = Ici x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ici (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ici, WithTop.preimage_coe_Ici]

@[simp]
lemma preimage_coe_Ioi (x : ℝ) : Real.toEReal ⁻¹' Ioi x = Ioi x := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi (WithBot.some (WithTop.some x))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi, WithTop.preimage_coe_Ioi]

@[simp]
lemma preimage_coe_Ioi_bot : Real.toEReal ⁻¹' Ioi ⊥ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Ioi ⊥) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Ioi_bot, preimage_univ]

@[simp]
lemma preimage_coe_Iic (y : ℝ) : Real.toEReal ⁻¹' Iic y = Iic y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iic (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iic, WithTop.preimage_coe_Iic]

@[simp]
lemma preimage_coe_Iio (y : ℝ) : Real.toEReal ⁻¹' Iio y = Iio y := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some (WithTop.some y))) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio]

@[simp]
lemma preimage_coe_Iio_top : Real.toEReal ⁻¹' Iio ⊤ = univ := by
  change (WithBot.some ∘ WithTop.some) ⁻¹' (Iio (WithBot.some ⊤)) = _
  refine preimage_comp.trans ?_
  simp only [WithBot.preimage_coe_Iio, WithTop.preimage_coe_Iio_top]

@[simp]
lemma preimage_coe_Icc (x y : ℝ) : Real.toEReal ⁻¹' Icc x y = Icc x y := by
  simp_rw [← Ici_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ico (x y : ℝ) : Real.toEReal ⁻¹' Ico x y = Ico x y := by
  simp_rw [← Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc (x y : ℝ) : Real.toEReal ⁻¹' Ioc x y = Ioc x y := by
  simp_rw [← Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo (x y : ℝ) : Real.toEReal ⁻¹' Ioo x y = Ioo x y := by
  simp_rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ico_top (x : ℝ) : Real.toEReal ⁻¹' Ico x ⊤ = Ici x := by
  rw [← Ici_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_top (x : ℝ) : Real.toEReal ⁻¹' Ioo x ⊤ = Ioi x := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioc_bot (y : ℝ) : Real.toEReal ⁻¹' Ioc ⊥ y = Iic y := by
  rw [← Ioi_inter_Iic]
  simp

@[simp]
lemma preimage_coe_Ioo_bot (y : ℝ) : Real.toEReal ⁻¹' Ioo ⊥ y = Iio y := by
  rw [← Ioi_inter_Iio]
  simp

@[simp]
lemma preimage_coe_Ioo_bot_top : Real.toEReal ⁻¹' Ioo ⊥ ⊤ = univ := by
  rw [← Ioi_inter_Iio]
  simp

/-! ### ennreal coercion -/

@[simp]
theorem toReal_coe_ennreal : ∀ {x : ℝ≥0∞}, toReal (x : EReal) = ENNReal.toReal x
  | ⊤ => rfl
  | .some _ => rfl

@[simp]
theorem coe_ennreal_ofReal {x : ℝ} : (ENNReal.ofReal x : EReal) = max x 0 :=
  rfl

theorem coe_nnreal_eq_coe_real (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) = (x : ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_zero : ((0 : ℝ≥0∞) : EReal) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_one : ((1 : ℝ≥0∞) : EReal) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_top : ((⊤ : ℝ≥0∞) : EReal) = ⊤ :=
  rfl

theorem coe_ennreal_strictMono : StrictMono ((↑) : ℝ≥0∞ → EReal) :=
  WithTop.strictMono_iff.2 ⟨fun _ _ => EReal.coe_lt_coe_iff.2, fun _ => coe_lt_top _⟩

theorem coe_ennreal_injective : Injective ((↑) : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.injective

@[simp]
theorem coe_ennreal_eq_top_iff {x : ℝ≥0∞} : (x : EReal) = ⊤ ↔ x = ⊤ :=
  coe_ennreal_injective.eq_iff' rfl

theorem coe_nnreal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) ≠ ⊤ := coe_ne_top x

@[simp]
theorem coe_nnreal_lt_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) < ⊤ := coe_lt_top x

@[simp, norm_cast]
theorem coe_ennreal_le_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_ennreal_strictMono.le_iff_le

@[simp, norm_cast]
theorem coe_ennreal_lt_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_ennreal_strictMono.lt_iff_lt

@[simp, norm_cast]
theorem coe_ennreal_eq_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_ennreal_injective.eq_iff

theorem coe_ennreal_ne_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_ennreal_injective.ne_iff

@[simp, norm_cast]
theorem coe_ennreal_eq_zero {x : ℝ≥0∞} : (x : EReal) = 0 ↔ x = 0 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_zero]

@[simp, norm_cast]
theorem coe_ennreal_eq_one {x : ℝ≥0∞} : (x : EReal) = 1 ↔ x = 1 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one]

@[norm_cast]
theorem coe_ennreal_ne_zero {x : ℝ≥0∞} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  coe_ennreal_eq_zero.not

@[norm_cast]
theorem coe_ennreal_ne_one {x : ℝ≥0∞} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  coe_ennreal_eq_one.not

theorem coe_ennreal_nonneg (x : ℝ≥0∞) : (0 : EReal) ≤ x :=
  coe_ennreal_le_coe_ennreal_iff.2 (zero_le x)

@[simp] theorem range_coe_ennreal : range ((↑) : ℝ≥0∞ → EReal) = Set.Ici 0 :=
  Subset.antisymm (range_subset_iff.2 coe_ennreal_nonneg) fun x => match x with
    | ⊥ => fun h => absurd h bot_lt_zero.not_le
    | ⊤ => fun _ => ⟨⊤, rfl⟩
    | (x : ℝ) => fun h => ⟨.some ⟨x, EReal.coe_nonneg.1 h⟩, rfl⟩

instance : CanLift EReal ℝ≥0∞ (↑) (0 ≤ ·) := ⟨range_coe_ennreal.ge⟩

@[simp, norm_cast]
theorem coe_ennreal_pos {x : ℝ≥0∞} : (0 : EReal) < x ↔ 0 < x := by
  rw [← coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]

@[simp]
theorem bot_lt_coe_ennreal (x : ℝ≥0∞) : (⊥ : EReal) < x :=
  (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)

@[simp]
theorem coe_ennreal_ne_bot (x : ℝ≥0∞) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe_ennreal x).ne'

@[simp, norm_cast]
theorem coe_ennreal_add (x y : ENNReal) : ((x + y : ℝ≥0∞) : EReal) = x + y := by
  cases x <;> cases y <;> rfl

private theorem coe_ennreal_top_mul (x : ℝ≥0) : ((⊤ * x : ℝ≥0∞) : EReal) = ⊤ * x := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · simp
  · rw [ENNReal.top_mul (ENNReal.coe_ne_zero.2 h0)]
    exact Eq.symm <| if_pos <| NNReal.coe_pos.2 h0.bot_lt

@[simp, norm_cast]
theorem coe_ennreal_mul : ∀ x y : ℝ≥0∞, ((x * y : ℝ≥0∞) : EReal) = (x : EReal) * y
  | ⊤, ⊤ => rfl
  | ⊤, (y : ℝ≥0) => coe_ennreal_top_mul y
  | (x : ℝ≥0), ⊤ => by
    rw [mul_comm, coe_ennreal_top_mul, EReal.mul_comm, coe_ennreal_top]
  | (x : ℝ≥0), (y : ℝ≥0) => by
    simp only [← ENNReal.coe_mul, coe_nnreal_eq_coe_real, NNReal.coe_mul, EReal.coe_mul]

@[norm_cast]
theorem coe_ennreal_nsmul (n : ℕ) (x : ℝ≥0∞) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_nsmul (⟨⟨(↑), coe_ennreal_zero⟩, coe_ennreal_add⟩ : ℝ≥0∞ →+ EReal) _ _

/-! ### nat coercion -/

theorem coe_coe_eq_natCast (n : ℕ) : (n : ℝ) = (n : EReal) := rfl

theorem natCast_ne_bot (n : ℕ) : (n : EReal) ≠ ⊥ := Ne.symm (ne_of_beq_false rfl)

theorem natCast_ne_top (n : ℕ) : (n : EReal) ≠ ⊤ := Ne.symm (ne_of_beq_false rfl)

@[simp, norm_cast]
theorem natCast_eq_iff {m n : ℕ} : (m : EReal) = (n : EReal) ↔ m = n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_eq_coe_iff, Nat.cast_inj]

theorem natCast_ne_iff {m n : ℕ} : (m : EReal) ≠ (n : EReal) ↔ m ≠ n :=
  not_iff_not.2 natCast_eq_iff

@[simp, norm_cast]
theorem natCast_le_iff {m n : ℕ} : (m : EReal) ≤ (n : EReal) ↔ m ≤ n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_le_coe_iff, Nat.cast_le]

@[simp, norm_cast]
theorem natCast_lt_iff {m n : ℕ} : (m : EReal) < (n : EReal) ↔ m < n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_lt_coe_iff, Nat.cast_lt]

@[simp, norm_cast]
theorem natCast_mul (m n : ℕ) :
    (m * n : ℕ) = (m : EReal) * (n : EReal) := by
  rw [← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_coe_eq_natCast, Nat.cast_mul, EReal.coe_mul]

/-! ### Order -/

theorem exists_rat_btwn_of_lt :
    ∀ {a b : EReal}, a < b → ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b
  | ⊤, b, h => (not_top_lt h).elim
  | (a : ℝ), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
  | (a : ℝ), (b : ℝ), h => by simp [exists_rat_btwn (EReal.coe_lt_coe_iff.1 h)]
  | (a : ℝ), ⊤, _ =>
    let ⟨b, hab⟩ := exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : ℝ), _ =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, _ => ⟨0, bot_lt_coe _, coe_lt_top _⟩

theorem lt_iff_exists_rat_btwn {a b : EReal} :
    a < b ↔ ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

theorem lt_iff_exists_real_btwn {a b : EReal} : a < b ↔ ∃ x : ℝ, a < x ∧ (x : EReal) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : ℝ), ax, xb⟩,
    fun ⟨_x, ax, xb⟩ => ax.trans xb⟩

/-- The set of numbers in `EReal` that are not equal to `±∞` is equivalent to `ℝ`. -/
def neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ ℝ where
  toFun x := EReal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ => by
    lift x to ℝ
    · simpa [not_or, and_comm] using hx
    · simp
  right_inv x := by simp

/-! ### Addition -/

@[simp]
theorem add_bot (x : EReal) : x + ⊥ = ⊥ :=
  WithBot.add_bot _

@[simp]
theorem bot_add (x : EReal) : ⊥ + x = ⊥ :=
  WithBot.bot_add _

@[simp]
theorem add_eq_bot_iff {x y : EReal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot

@[simp]
theorem bot_lt_add_iff {x y : EReal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot, not_or]

@[simp]
theorem top_add_top : (⊤ : EReal) + ⊤ = ⊤ :=
  rfl

@[simp]
theorem top_add_coe (x : ℝ) : (⊤ : EReal) + x = ⊤ :=
  rfl

/-- For any extended real number `x` which is not `⊥`, the sum of `⊤` and `x` is equal to `⊤`. -/
@[simp]
theorem top_add_of_ne_bot {x : EReal} (h : x ≠ ⊥) : ⊤ + x = ⊤ := by
  induction x
  · exfalso; exact h (Eq.refl ⊥)
  · exact top_add_coe _
  · exact top_add_top

/-- For any extended real number `x`, the sum of `⊤` and `x` is equal to `⊤`
if and only if `x` is not `⊥`. -/
theorem top_add_iff_ne_bot {x : EReal} : ⊤ + x = ⊤ ↔ x ≠ ⊥ := by
  constructor <;> intro h
  · rintro rfl
    rw [add_bot] at h
    exact bot_ne_top h
  · cases x with
    | h_bot => contradiction
    | h_top => rfl
    | h_real r => exact top_add_of_ne_bot h

/-- For any extended real number `x` which is not `⊥`, the sum of `x` and `⊤` is equal to `⊤`. -/
@[simp]
theorem add_top_of_ne_bot {x : EReal} (h : x ≠ ⊥) : x + ⊤ = ⊤ := by
  rw [add_comm, top_add_of_ne_bot h]

/-- For any extended real number `x`, the sum of `x` and `⊤` is equal to `⊤`
if and only if `x` is not `⊥`. -/
theorem add_top_iff_ne_bot {x : EReal} : x + ⊤ = ⊤ ↔ x ≠ ⊥ := by rw [add_comm, top_add_iff_ne_bot]

/-- For any two extended real numbers `a` and `b`, if both `a` and `b` are greater than `0`,
then their sum is also greater than `0`. -/
theorem add_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  induction a
  · exfalso; exact not_lt_bot ha
  · induction b
    · exfalso; exact not_lt_bot hb
    · norm_cast at *; exact Left.add_pos ha hb
    · exact add_top_of_ne_bot (bot_lt_zero.trans ha).ne' ▸ hb
  · rw [top_add_of_ne_bot (bot_lt_zero.trans hb).ne']
    exact ha

@[simp]
theorem coe_add_top (x : ℝ) : (x : EReal) + ⊤ = ⊤ :=
  rfl

theorem toReal_add {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x + y) = toReal x + toReal y := by
  lift x to ℝ using ⟨hx, h'x⟩
  lift y to ℝ using ⟨hy, h'y⟩
  rfl

theorem addLECancellable_coe (x : ℝ) : AddLECancellable (x : EReal)
  | _, ⊤, _ => le_top
  | ⊥, _, _ => bot_le
  | ⊤, (z : ℝ), h => by simp only [coe_add_top, ← coe_add, top_le_iff, coe_ne_top] at h
  | _, ⊥, h => by simpa using h
  | (y : ℝ), (z : ℝ), h => by
    simpa only [← coe_add, EReal.coe_le_coe_iff, add_le_add_iff_left] using h

-- Porting note (#11215): TODO: add `MulLECancellable.strictMono*` etc
theorem add_lt_add_right_coe {x y : EReal} (h : x < y) (z : ℝ) : x + z < y + z :=
  not_le.1 <| mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_le

theorem add_lt_add_left_coe {x y : EReal} (h : x < y) (z : ℝ) : (z : EReal) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z

theorem add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  · simp [h1, bot_le.trans_lt h2]
  · lift x to ℝ using ⟨h1.ne_top, hx⟩
    calc (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
    _ ≤ y + t := add_le_add_right h1.le _

theorem add_lt_add_of_lt_of_le' {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hbot : t ≠ ⊥)
    (htop : t = ⊤ → z = ⊤ → x = ⊥) : x + z < y + t := by
  rcases h'.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    · obtain rfl := htop rfl rfl
      simpa
    lift z to ℝ using ⟨hz, hbot⟩
    exact add_lt_add_right_coe h z
  · exact add_lt_add h hlt

/-- See also `EReal.add_lt_add_of_lt_of_le'` for a version with weaker but less convenient
assumptions. -/
theorem add_lt_add_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x + z < y + t :=
  add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') fun ht' => (ht ht').elim

theorem add_lt_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y < ⊤ := by
  rw [← EReal.top_add_top]
  exact EReal.add_lt_add hx.lt_top hy.lt_top

/-- We do not have a notion of `LinearOrderedAddCommMonoidWithBot` but we can at least make
the order dual of the extended reals into a `LinearOrderedAddCommMonoidWithTop`. -/
instance : LinearOrderedAddCommMonoidWithTop ERealᵒᵈ where
  le_top := by simp
  top_add' := by
    rw [OrderDual.forall]
    intro x
    rw [← OrderDual.toDual_bot, ← toDual_add, bot_add, OrderDual.toDual_bot]

/-! ### Negation -/

/-- negation on `EReal` -/
protected def neg : EReal → EReal
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℝ) => (-x : ℝ)

instance : Neg EReal := ⟨EReal.neg⟩

instance : SubNegZeroMonoid EReal where
  neg_zero := congr_arg Real.toEReal neg_zero
  zsmul := zsmulRec

@[simp]
theorem neg_top : -(⊤ : EReal) = ⊥ :=
  rfl

@[simp]
theorem neg_bot : -(⊥ : EReal) = ⊤ :=
  rfl

@[simp, norm_cast] theorem coe_neg (x : ℝ) : (↑(-x) : EReal) = -↑x := rfl

@[simp, norm_cast] theorem coe_sub (x y : ℝ) : (↑(x - y) : EReal) = x - y := rfl

@[norm_cast]
theorem coe_zsmul (n : ℤ) (x : ℝ) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : ℝ →+ EReal) coe_neg _ _

instance : InvolutiveNeg EReal where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℝ) => congr_arg Real.toEReal (neg_neg a)

@[simp]
theorem toReal_neg : ∀ {a : EReal}, toReal (-a) = -toReal a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℝ) => rfl

@[simp]
theorem neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
theorem neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
theorem neg_eq_zero_iff {x : EReal} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero

theorem neg_strictAnti : StrictAnti (- · : EReal → EReal) :=
  WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨bot_lt_top, fun _ => coe_lt_top _⟩⟩

@[simp] theorem neg_le_neg_iff {a b : EReal} : -a ≤ -b ↔ b ≤ a := neg_strictAnti.le_iff_le

@[simp] theorem neg_lt_neg_iff {a b : EReal} : -a < -b ↔ b < a := neg_strictAnti.lt_iff_lt

/-- `-a ≤ b ↔ -b ≤ a` on `EReal`. -/
protected theorem neg_le {a b : EReal} : -a ≤ b ↔ -b ≤ a := by
 rw [← neg_le_neg_iff, neg_neg]

/-- if `-a ≤ b` then `-b ≤ a` on `EReal`. -/
protected theorem neg_le_of_neg_le {a b : EReal} (h : -a ≤ b) : -b ≤ a := EReal.neg_le.mp h

/-- `a ≤ -b → b ≤ -a` on ereal -/
theorem le_neg_of_le_neg {a b : EReal} (h : a ≤ -b) : b ≤ -a := by
  rwa [← neg_neg b, EReal.neg_le, neg_neg]

/-- Negation as an order reversing isomorphism on `EReal`. -/
def negOrderIso : EReal ≃o ERealᵒᵈ :=
  { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }

theorem neg_lt_iff_neg_lt {a b : EReal} : -a < b ↔ -b < a := by
  rw [← neg_lt_neg_iff, neg_neg]

theorem neg_lt_of_neg_lt {a b : EReal} (h : -a < b) : -b < a := neg_lt_iff_neg_lt.1 h

lemma neg_add {x y : EReal} (h1 : x ≠ ⊥ ∨ y ≠ ⊤) (h2 : x ≠ ⊤ ∨ y ≠ ⊥) :
    - (x + y) = - x - y := by
  induction x <;> induction y <;> try tauto
  rw [← coe_add, ← coe_neg, ← coe_neg, ← coe_sub, neg_add']

lemma neg_sub {x y : EReal} (h1 : x ≠ ⊥ ∨ y ≠ ⊥) (h2 : x ≠ ⊤ ∨ y ≠ ⊤) :
    - (x - y) = - x + y := by
  rw [sub_eq_add_neg, neg_add _ _, sub_eq_add_neg, neg_neg] <;> simp_all

/-! ### Addition and order -/

lemma le_of_forall_lt_iff_le {x y : EReal} : (∀ z : ℝ, x < z → y ≤ z) ↔ y ≤ x := by
  refine ⟨fun h ↦ WithBot.le_of_forall_lt_iff_le.1 ?_, fun h _ x_z ↦ h.trans x_z.le⟩
  rw [WithTop.forall]
  aesop

lemma ge_of_forall_gt_iff_ge {x y : EReal} : (∀ z : ℝ, z < y → z ≤ x) ↔ y ≤ x := by
  refine ⟨fun h ↦ WithBot.ge_of_forall_gt_iff_ge.1 ?_, fun h _ x_z ↦ x_z.le.trans h⟩
  rw [WithTop.forall]
  aesop

/-- This lemma is superseded by `add_le_of_forall_add_le`. -/
private lemma top_add_le_of_forall_add_le {a b : EReal} (h : ∀ c < ⊤, ∀ d < a, c + d ≤ b) :
    ⊤ + a ≤ b := by
  induction a with
  | h_bot => exact add_bot ⊤ ▸ bot_le
  | h_real a =>
    refine top_add_coe a ▸ le_of_forall_lt_iff_le.1 fun c b_c ↦ ?_
    specialize h (c - a + 1) (coe_lt_top (c - a + 1)) (a - 1)
    rw [← coe_one, ← coe_sub, ← coe_sub, ← coe_add, ← coe_add, add_add_sub_cancel, sub_add_cancel,
      EReal.coe_lt_coe_iff] at h
    exact (not_le_of_lt b_c (h (sub_one_lt a))).rec
  | h_top =>
    refine top_add_top ▸ le_of_forall_lt_iff_le.1 fun c b_c ↦ ?_
    specialize h c (coe_lt_top c) 0 zero_lt_top
    rw [add_zero] at h
    exact (not_le_of_lt b_c h).rec

lemma add_le_of_forall_add_le {a b c : EReal} (h : ∀ d < a, ∀ e < b, d + e ≤ c) : a + b ≤ c := by
  induction a with
  | h_bot => exact bot_add b ▸ bot_le
  | h_real a => induction b with
    | h_bot => exact add_bot (a : EReal) ▸ bot_le
    | h_real b =>
      refine (@ge_of_forall_gt_iff_ge c (a+b)).1 fun d d_ab ↦ ?_
      rw [← coe_add, EReal.coe_lt_coe_iff] at d_ab
      rcases exists_between d_ab with ⟨e, e_d, e_ab⟩
      have key₁ : (a + d - e : ℝ) < (a : EReal) := by apply EReal.coe_lt_coe_iff.2; linarith
      have key₂ : (e - a : ℝ) < (b : EReal) := by apply EReal.coe_lt_coe_iff.2; linarith
      apply le_of_eq_of_le _ (h (a + d - e) key₁ (e - a) key₂)
      rw [← coe_add, ← coe_sub,  ← coe_sub, ← coe_add, sub_add_sub_cancel, add_sub_cancel_left]
    | h_top =>
      rw [add_comm (a : EReal) ⊤]
      exact top_add_le_of_forall_add_le fun d d_top e e_a ↦ (add_comm d e ▸ h e e_a d d_top)
  | h_top => exact top_add_le_of_forall_add_le h

lemma le_add_of_forall_le_add {a b c : EReal} (h₁ : a ≠ ⊥ ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ b ≠ ⊥)
    (h : ∀ d > a, ∀ e > b, c ≤ d + e) :
    c ≤ a + b := by
  rw [← neg_le_neg_iff, neg_add h₁ h₂]
  refine add_le_of_forall_add_le fun d d_a e e_b ↦ ?_
  have h₃ : d ≠ ⊥ ∨ e ≠ ⊤ := Or.inr (ne_top_of_lt e_b)
  have h₄ : d ≠ ⊤ ∨ e ≠ ⊥ := Or.inl (ne_top_of_lt d_a)
  rw [← neg_neg d, neg_lt_iff_neg_lt, neg_neg a] at d_a
  rw [← neg_neg e, neg_lt_iff_neg_lt, neg_neg b] at e_b
  exact le_neg_of_le_neg <| neg_add h₃ h₄ ▸ h (- d) d_a (- e) e_b

/-!
### Subtraction

Subtraction on `EReal` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `EReal`, beyond `SubNegZeroMonoid`, because of this bad behavior.
-/

@[simp]
theorem bot_sub (x : EReal) : ⊥ - x = ⊥ :=
  bot_add x

@[simp]
theorem sub_top (x : EReal) : x - ⊤ = ⊥ :=
  add_bot x

@[simp]
theorem top_sub_bot : (⊤ : EReal) - ⊥ = ⊤ :=
  rfl

@[simp]
theorem top_sub_coe (x : ℝ) : (⊤ : EReal) - x = ⊤ :=
  rfl

@[simp]
theorem coe_sub_bot (x : ℝ) : (x : EReal) - ⊥ = ⊤ :=
  rfl

theorem sub_le_sub {x y z t : EReal} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
  add_le_add h (neg_le_neg_iff.2 h')

theorem sub_lt_sub_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x - t < y - z :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])

theorem coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (x : ℝ) :
    (x : EReal) = Real.toNNReal x - Real.toNNReal (-x) := by
  rcases le_total 0 x with (h | h)
  · lift x to ℝ≥0 using h
    rw [Real.toNNReal_of_nonpos (neg_nonpos.mpr x.coe_nonneg), Real.toNNReal_coe, ENNReal.coe_zero,
      coe_ennreal_zero, sub_zero]
    rfl
  · rw [Real.toNNReal_of_nonpos h, ENNReal.coe_zero, coe_ennreal_zero, coe_nnreal_eq_coe_real,
      Real.coe_toNNReal, zero_sub, coe_neg, neg_neg]
    exact neg_nonneg.2 h

theorem toReal_sub {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x - y) = toReal x - toReal y := by
  lift x to ℝ using ⟨hx, h'x⟩
  lift y to ℝ using ⟨hy, h'y⟩
  rfl

lemma add_sub_cancel_right {a : EReal} {b : Real} : a + b - b = a := by
  induction a
  · rw [bot_add b, bot_sub b]
  · norm_cast; linarith
  · rw [top_add_of_ne_bot (coe_ne_bot b), top_sub_coe]

/-! ### Multiplication -/

@[simp] lemma top_mul_top : (⊤ : EReal) * ⊤ = ⊤ := rfl

@[simp] lemma top_mul_bot : (⊤ : EReal) * ⊥ = ⊥ := rfl

@[simp] lemma bot_mul_top : (⊥ : EReal) * ⊤ = ⊥ := rfl

@[simp] lemma bot_mul_bot : (⊥ : EReal) * ⊥ = ⊤ := rfl

lemma coe_mul_top_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊤ = ⊤ :=
  if_pos h

lemma coe_mul_top_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊤ = ⊥ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

lemma top_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊤ : EReal) * x = ⊤ :=
  if_pos h

lemma top_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊤ : EReal) * x = ⊥ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

lemma mul_top_of_pos : ∀ {x : EReal}, 0 < x → x * ⊤ = ⊤
  | ⊥, h => absurd h not_lt_bot
  | (x : ℝ), h => coe_mul_top_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl

lemma mul_top_of_neg : ∀ {x : EReal}, x < 0 → x * ⊤ = ⊥
  | ⊥, _ => rfl
  | (x : ℝ), h => coe_mul_top_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt

lemma top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_top_of_pos h

/-- The product of two positive extended real numbers is positive. -/
lemma mul_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  induction a
  · exfalso; exact not_lt_bot ha
  · induction b
    · exfalso; exact not_lt_bot hb
    · norm_cast at *; exact Left.mul_pos ha hb
    · rw [EReal.mul_comm, top_mul_of_pos ha]; exact hb
  · rw [top_mul_of_pos hb]; exact ha

lemma top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_top_of_neg h

lemma coe_mul_bot_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊥ = ⊥ :=
  if_pos h

lemma coe_mul_bot_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊥ = ⊤ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

lemma bot_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊥ : EReal) * x = ⊥ :=
  if_pos h

lemma bot_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊥ : EReal) * x = ⊤ :=
  (if_neg h.not_lt).trans (if_neg h.ne)

lemma mul_bot_of_pos : ∀ {x : EReal}, 0 < x → x * ⊥ = ⊥
  | ⊥, h => absurd h not_lt_bot
  | (x : ℝ), h => coe_mul_bot_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl

lemma mul_bot_of_neg : ∀ {x : EReal}, x < 0 → x * ⊥ = ⊤
  | ⊥, _ => rfl
  | (x : ℝ), h => coe_mul_bot_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt

lemma bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_pos h

lemma bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_neg h

lemma toReal_mul {x y : EReal} : toReal (x * y) = toReal x * toReal y := by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [coe_mul_bot_of_pos h]
  | neg_bot _ h => simp [coe_mul_bot_of_neg h]

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for all
`x`, `y`. -/
@[elab_as_elim]
lemma induction₂_neg_left {P : EReal → EReal → Prop} (neg_left : ∀ {x y}, P x y → P (-x) y)
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
lemma induction₂_symm_neg {P : EReal → EReal → Prop}
    (symm : ∀ {x y}, P x y → P y x)
    (neg_left : ∀ {x y}, P x y → P (-x) y) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0) (coe_coe : ∀ x y : ℝ, P x y) :
    ∀ x y, P x y :=
  have neg_right : ∀ {x y}, P x y → P x (-y) := fun h => symm <| neg_left <| symm h
  have : ∀ x, (∀ y : ℝ, 0 < y → P x y) → ∀ y : ℝ, y < 0 → P x y := fun _ h y hy =>
    neg_neg (y : EReal) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos top_zero (this _ top_pos) (neg_right top_top)
    (symm top_zero) (symm <| neg_left top_zero) (fun x hx => symm <| top_pos x hx)
    (fun x hx => symm <| neg_left <| top_pos x hx) coe_coe

protected lemma neg_mul (x y : EReal) : -x * y = -(x * y) := by
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

instance : HasDistribNeg EReal where
  neg_mul := EReal.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm, x.mul_comm]
    exact y.neg_mul x

lemma right_distrib_of_nonneg {a b c : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * c = a * c + b * c := by
  rcases eq_or_lt_of_le ha with (rfl | a_pos)
  · simp
  rcases eq_or_lt_of_le hb with (rfl | b_pos)
  · simp
  rcases lt_trichotomy c 0 with (c_neg | rfl | c_pos)
  · induction c
    · rw [mul_bot_of_pos a_pos, mul_bot_of_pos b_pos, mul_bot_of_pos (add_pos a_pos b_pos),
        add_bot ⊥]
    · induction a
      · exfalso; exact not_lt_bot a_pos
      · induction b
        · norm_cast
        · norm_cast; exact right_distrib _ _ _
        · norm_cast
          rw [add_top_of_ne_bot (coe_ne_bot _), top_mul_of_neg c_neg, add_bot]
      · rw [top_add_of_ne_bot (ne_bot_of_gt b_pos), top_mul_of_neg c_neg, bot_add]
    · exfalso; exact not_top_lt c_neg
  · simp
  · induction c
    · exfalso; exact not_lt_bot c_pos
    · induction a
      · exfalso; exact not_lt_bot a_pos
      · induction b
        · norm_cast
        · norm_cast; exact right_distrib _ _ _
        · norm_cast
          rw [add_top_of_ne_bot (coe_ne_bot _), top_mul_of_pos c_pos,
            add_top_of_ne_bot (coe_ne_bot _)]
      · rw [top_add_of_ne_bot (ne_bot_of_gt b_pos), top_mul_of_pos c_pos,
          top_add_of_ne_bot (ne_bot_of_gt (mul_pos b_pos c_pos))]
    · rw [mul_top_of_pos a_pos, mul_top_of_pos b_pos, mul_top_of_pos (add_pos a_pos b_pos),
        top_add_top]

lemma left_distrib_of_nonneg {a b c : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c * (a + b) = c * a + c * b := by
  nth_rewrite 1 [EReal.mul_comm]; nth_rewrite 2 [EReal.mul_comm]; nth_rewrite 3 [EReal.mul_comm]
  exact right_distrib_of_nonneg ha hb

/-! ### Absolute value -/

-- Porting note (#11215): TODO: use `Real.nnabs` for the case `(x : ℝ)`
/-- The absolute value from `EReal` to `ℝ≥0∞`, mapping `⊥` and `⊤` to `⊤` and
a real `x` to `|x|`. -/
protected def abs : EReal → ℝ≥0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : ℝ) => ENNReal.ofReal |x|

@[simp] theorem abs_top : (⊤ : EReal).abs = ⊤ := rfl

@[simp] theorem abs_bot : (⊥ : EReal).abs = ⊤ := rfl

theorem abs_def (x : ℝ) : (x : EReal).abs = ENNReal.ofReal |x| := rfl

theorem abs_coe_lt_top (x : ℝ) : (x : EReal).abs < ⊤ :=
  ENNReal.ofReal_lt_top

@[simp]
theorem abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0 := by
  induction x
  · simp only [abs_bot, ENNReal.top_ne_zero, bot_ne_zero]
  · simp only [abs_def, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]

@[simp]
theorem abs_zero : (0 : EReal).abs = 0 := by rw [abs_eq_zero_iff]

@[simp]
theorem coe_abs (x : ℝ) : ((x : EReal).abs : EReal) = (|x| : ℝ) := by
  rw [abs_def, ← Real.coe_nnabs, ENNReal.ofReal_coe_nnreal]; rfl

@[simp]
protected theorem abs_neg : ∀ x : EReal, (-x).abs = x.abs
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℝ) => by rw [abs_def, ← coe_neg, abs_def, abs_neg]

@[simp]
theorem abs_mul (x y : EReal) : (x * y).abs = x.abs * y.abs := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [zero_mul, mul_zero, abs_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, abs_top, ENNReal.top_mul]
    rw [Ne, abs_eq_zero_iff, coe_eq_zero]
    exact h.ne'
  | neg_left h => rwa [neg_mul, EReal.abs_neg, EReal.abs_neg]

/-! ### Sign -/

open SignType (sign)

theorem sign_top : sign (⊤ : EReal) = 1 := rfl

theorem sign_bot : sign (⊥ : EReal) = -1 := rfl

@[simp]
theorem sign_coe (x : ℝ) : sign (x : EReal) = sign x := by
  simp only [sign, OrderHom.coe_mk, EReal.coe_pos, EReal.coe_neg']

@[simp, norm_cast]
theorem coe_coe_sign (x : SignType) : ((x : ℝ) : EReal) = x := by cases x <;> rfl

@[simp] theorem sign_neg : ∀ x : EReal, sign (-x) = -sign x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℝ) => by rw [← coe_neg, sign_coe, sign_coe, Left.sign_neg]

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

@[simp] protected theorem sign_mul_abs : ∀ x : EReal, (sign x * x.abs : EReal) = x
  | ⊥ => by simp
  | ⊤ => by simp
  | (x : ℝ) => by rw [sign_coe, coe_abs, ← coe_coe_sign, ← coe_mul, sign_mul_abs]

@[simp] protected theorem abs_mul_sign (x : EReal) : (x.abs * sign x : EReal) = x := by
  rw [EReal.mul_comm, EReal.sign_mul_abs]

theorem sign_eq_and_abs_eq_iff_eq {x y : EReal} :
    x.abs = y.abs ∧ sign x = sign y ↔ x = y := by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs, ← y.sign_mul_abs, habs, hsign]
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem le_iff_sign {x y : EReal} :
    x ≤ y ↔ sign x < sign y ∨
      sign x = SignType.neg ∧ sign y = SignType.neg ∧ y.abs ≤ x.abs ∨
        sign x = SignType.zero ∧ sign y = SignType.zero ∨
          sign x = SignType.pos ∧ sign y = SignType.pos ∧ x.abs ≤ y.abs := by
  constructor
  · intro h
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    rw [← x.sign_mul_abs, ← y.sign_mul_abs] at h
    cases hy : sign y <;> rw [hs, hy] at h ⊢
    · simp
    · left; simpa using h
    · right; right; simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]

instance : CommMonoidWithZero EReal :=
  { inferInstanceAs (MulZeroOneClass EReal) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, eq_self_iff_true, sign_mul, and_self_iff]
    mul_comm := EReal.mul_comm }

instance : PosMulMono EReal := posMulMono_iff_covariant_pos.2 <| .mk <| by
  rintro ⟨x, x0⟩ a b h
  simp only [le_iff_sign, EReal.sign_mul, sign_pos x0, one_mul, EReal.abs_mul] at h ⊢
  exact h.imp_right <| Or.imp (And.imp_right <| And.imp_right (mul_le_mul_left' · _)) <|
    Or.imp_right <| And.imp_right <| And.imp_right (mul_le_mul_left' · _)

instance : MulPosMono EReal := posMulMono_iff_mulPosMono.1 inferInstance

instance : PosMulReflectLT EReal := PosMulMono.toPosMulReflectLT

instance : MulPosReflectLT EReal :=
  MulPosMono.toMulPosReflectLT

@[simp, norm_cast]
theorem coe_pow (x : ℝ) (n : ℕ) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : ℝ →* EReal) _ _

@[simp, norm_cast]
theorem coe_ennreal_pow (x : ℝ≥0∞) (n : ℕ) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_ennreal_one⟩, coe_ennreal_mul⟩ : ℝ≥0∞ →* EReal) _ _

/-! ### Min and Max -/

lemma min_neg_neg (x y : EReal) : min (-x) (-y) = -max x y := by
  rcases le_total x y with (h | h) <;> simp_all

lemma max_neg_neg (x y : EReal) : max (-x) (-y) = -min x y := by
  rcases le_total x y with (h | h) <;> simp_all

/-! ### Inverse -/

/-- Multiplicative inverse of an `EReal`. We choose `0⁻¹ = 0` to guarantee several good properties,
for instance `(a * b)⁻¹ = a⁻¹ * b⁻¹`. -/
protected def inv : EReal → EReal
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => (x⁻¹ : ℝ)

instance : Inv (EReal) := ⟨EReal.inv⟩

noncomputable instance : DivInvMonoid EReal where inv := EReal.inv

@[simp]
lemma inv_bot : (⊥ : EReal)⁻¹ = 0 := rfl

@[simp]
lemma inv_top : (⊤ : EReal)⁻¹ = 0 := rfl

lemma coe_inv (x : ℝ) : (x⁻¹ : ℝ) = (x : EReal)⁻¹ := rfl

@[simp]
lemma inv_zero : (0 : EReal)⁻¹ = 0 := by
  change (0 : ℝ)⁻¹ = (0 : EReal)
  rw [GroupWithZero.inv_zero, coe_zero]

noncomputable instance : DivInvOneMonoid EReal where
  inv_one := by nth_rw 1 [← coe_one, ← coe_inv 1, _root_.inv_one, coe_one]

lemma inv_neg (a : EReal) : (-a)⁻¹ = -a⁻¹ := by
  induction a
  · rw [neg_bot, inv_top, inv_bot, neg_zero]
  · rw [← coe_inv _, ← coe_neg _⁻¹, ← coe_neg _, ← coe_inv (-_)]
    exact EReal.coe_eq_coe_iff.2 _root_.inv_neg
  · rw [neg_top, inv_bot, inv_top, neg_zero]

lemma inv_inv {a : EReal} (h : a ≠ ⊥) (h' : a ≠ ⊤) : (a⁻¹)⁻¹ = a := by
  rw [← coe_toReal h' h, ← coe_inv a.toReal, ← coe_inv a.toReal⁻¹, _root_.inv_inv a.toReal]

lemma mul_inv (a b : EReal) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction a, b using EReal.induction₂_symm with
  | top_top | top_zero | top_bot | zero_bot | bot_bot => simp
  | @symm a b h => rw [mul_comm b a, mul_comm b⁻¹ a⁻¹]; exact h
  | top_pos x x_pos => rw [top_mul_of_pos (EReal.coe_pos.2 x_pos), inv_top, zero_mul]
  | top_neg x x_neg => rw [top_mul_of_neg (EReal.coe_neg'.2 x_neg), inv_bot, inv_top, zero_mul]
  | pos_bot x x_pos => rw [mul_bot_of_pos (EReal.coe_pos.2 x_pos), inv_bot, mul_zero]
  | coe_coe x y => rw [← coe_mul, ← coe_inv, _root_.mul_inv, coe_mul, coe_inv, coe_inv]
  | neg_bot x x_neg => rw [mul_bot_of_neg (EReal.coe_neg'.2 x_neg), inv_top, inv_bot, mul_zero]

/-! #### Inversion and Absolute Value -/

lemma sign_mul_inv_abs (a : EReal) : (sign a) * (a.abs : EReal)⁻¹ = a⁻¹ := by
  induction a with
  | h_bot | h_top => simp
  | h_real a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, ← inv_neg, abs_def a,
        coe_ennreal_ofReal, max_eq_left (abs_nonneg a), ← coe_neg |a|, abs_of_neg a_neg, neg_neg]
    · rw [coe_zero, sign_zero, SignType.coe_zero, abs_zero, coe_ennreal_zero, inv_zero, mul_zero]
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul]
      simp only [abs_def a, coe_ennreal_ofReal, abs_nonneg, max_eq_left]
      congr
      exact abs_of_pos a_pos

lemma sign_mul_inv_abs' (a : EReal) : (sign a) * ((a.abs⁻¹ : ℝ≥0∞) : EReal) = a⁻¹ := by
  induction a with
  | h_bot | h_top  => simp
  | h_real a =>
    rcases lt_trichotomy a 0 with (a_neg | rfl | a_pos)
    · rw [sign_coe, _root_.sign_neg a_neg, coe_neg_one, neg_one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_neg a_neg), coe_ennreal_ofReal,
        max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_neg |a|⁻¹, ← coe_inv a, abs_of_neg a_neg,
        ← _root_.inv_neg, neg_neg]
    · simp
    · rw [sign_coe, _root_.sign_pos a_pos, SignType.coe_one, one_mul, abs_def a,
        ← ofReal_inv_of_pos (abs_pos_of_pos a_pos), coe_ennreal_ofReal,
          max_eq_left (inv_nonneg.2 (abs_nonneg a)), ← coe_inv a]
      congr
      exact abs_of_pos a_pos

/-! #### Inversion and Positivity -/

lemma inv_nonneg_of_nonneg {a : EReal} (h : 0 ≤ a) : 0 ≤ a⁻¹ := by
  induction a with
  | h_bot | h_top => simp
  | h_real a => rw [← coe_inv a, EReal.coe_nonneg, inv_nonneg]; exact EReal.coe_nonneg.1 h

lemma inv_nonpos_of_nonpos {a : EReal} (h : a ≤ 0) : a⁻¹ ≤ 0 := by
  induction a with
  | h_bot | h_top => simp
  | h_real a => rw [← coe_inv a, EReal.coe_nonpos, inv_nonpos]; exact EReal.coe_nonpos.1 h

lemma inv_pos_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : 0 < a⁻¹ := by
  induction a with
  | h_bot => exact (not_lt_bot h).rec
  | h_real a =>  rw [← coe_inv a]; norm_cast at *; exact inv_pos_of_pos h
  | h_top => exact (h' (Eq.refl ⊤)).rec

lemma inv_neg_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : a⁻¹ < 0 := by
  induction a with
  | h_bot => exact (h' (Eq.refl ⊥)).rec
  | h_real a => rw [← coe_inv a]; norm_cast at *; exact inv_lt_zero.2 h
  | h_top => exact (not_top_lt h).rec

/-! ### Division -/

lemma div_eq_inv_mul (a b : EReal) : a / b = b⁻¹ * a := EReal.mul_comm a b⁻¹

lemma coe_div (a b : ℝ) : (a / b : ℝ) = (a : EReal) / (b : EReal) := rfl

theorem natCast_div_le (m n : ℕ) :
    (m / n : ℕ) ≤ (m : EReal) / (n : EReal) := by
  rw [← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_div,
    EReal.coe_le_coe_iff]
  exact Nat.cast_div_le

@[simp]
lemma div_bot {a : EReal} : a / ⊥ = 0 := inv_bot ▸ mul_zero a

@[simp]
lemma div_top {a : EReal} : a / ⊤ = 0 := inv_top ▸ mul_zero a

@[simp]
lemma div_zero {a : EReal} : a / 0 = 0 := by
  change a * 0⁻¹ = 0
  rw [inv_zero, mul_zero a]

@[simp]
lemma zero_div {a : EReal} : 0 / a = 0 := zero_mul a⁻¹

lemma top_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : ⊤ / a = ⊤ :=
  top_mul_of_pos (inv_pos_of_pos_ne_top h h')

lemma top_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : ⊤ / a = ⊥ :=
  top_mul_of_neg (inv_neg_of_neg_ne_bot h h')

lemma bot_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : ⊥ / a = ⊥ :=
  bot_mul_of_pos (inv_pos_of_pos_ne_top h h')

lemma bot_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : ⊥ / a = ⊤ :=
  bot_mul_of_neg (inv_neg_of_neg_ne_bot h h')

/-! #### Division and Multiplication -/

lemma div_self {a : EReal} (h₁ : a ≠ ⊥) (h₂ : a ≠ ⊤) (h₃ : a ≠ 0) : a / a = 1 := by
  rw [← coe_toReal h₂ h₁] at h₃ ⊢
  rw [← coe_div, _root_.div_self (coe_ne_zero.1 h₃), coe_one]

lemma mul_div (a b c : EReal) : a * (b / c) = (a * b) / c := by
  change a * (b * c⁻¹) = (a * b) * c⁻¹
  rw [mul_assoc]

lemma mul_div_right (a b c : EReal) : (a / b) * c = (a * c) / b := by
  rw [mul_comm, EReal.mul_div, mul_comm]

lemma div_div (a b c : EReal) : a / b / c = a / (b * c) := by
  change (a * b⁻¹) * c⁻¹ = a * (b * c)⁻¹
  rw [mul_assoc a b⁻¹, mul_inv]

lemma div_mul_cancel {a b : EReal} (h₁ : b ≠ ⊥) (h₂ : b ≠ ⊤) (h₃ : b ≠ 0) : (a / b) * b = a := by
  change (a * b⁻¹) * b = a
  rw [mul_assoc, mul_comm b⁻¹ b]
  change a * (b / b) = a
  rw [div_self h₁ h₂ h₃, mul_one]

lemma mul_div_cancel {a b : EReal} (h₁ : b ≠ ⊥) (h₂ : b ≠ ⊤) (h₃ : b ≠ 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel h₁ h₂ h₃]

lemma mul_div_mul_cancel {a b c : EReal} (h₁ : c ≠ ⊥) (h₂ : c ≠ ⊤) (h₃ : c ≠ 0) :
    (a * c) / (b * c) = a / b := by
  change (a * c) * (b * c)⁻¹ = a * b⁻¹
  rw [mul_assoc, mul_inv b c]
  congr
  exact mul_div_cancel h₁ h₂ h₃

/-! #### Division Distributivity -/

lemma div_right_distrib_of_nonneg {a b c : EReal} (h : 0 ≤ a) (h' : 0 ≤ b) :
    (a + b) / c = (a / c) + (b / c) :=
  EReal.right_distrib_of_nonneg h h'

/-! #### Division and Order s -/

lemma monotone_div_right_of_nonneg {b : EReal} (h : 0 ≤ b) : Monotone fun a ↦ a / b :=
  fun _ _ h' ↦ mul_le_mul_of_nonneg_right h' (inv_nonneg_of_nonneg h)

lemma div_le_div_right_of_nonneg {a a' b : EReal} (h : 0 ≤ b) (h' : a ≤ a') :
    a / b ≤ a' / b :=
  monotone_div_right_of_nonneg h h'

lemma strictMono_div_right_of_pos {b : EReal} (h : 0 < b) (h' : b ≠ ⊤) :
    StrictMono fun a ↦ a / b := by
  intro a a' a_lt_a'
  apply lt_of_le_of_ne <| div_le_div_right_of_nonneg (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h), hyp,
    @EReal.mul_div_cancel a' b (ne_bot_of_gt h) h' (ne_of_gt h)]

lemma div_lt_div_right_of_pos {a a' b : EReal} (h₁ : 0 < b) (h₂ : b ≠ ⊤)
    (h₃ : a < a') : a / b < a' / b :=
  strictMono_div_right_of_pos h₁ h₂ h₃

lemma antitone_div_right_of_nonpos {b : EReal} (h : b ≤ 0) : Antitone fun a ↦ a / b := by
  intro a a' h'
  change a' * b⁻¹ ≤ a * b⁻¹
  rw [← neg_neg (a * b⁻¹), ← neg_neg (a' * b⁻¹), neg_le_neg_iff, mul_comm a b⁻¹, mul_comm a' b⁻¹,
    ← neg_mul b⁻¹ a, ← neg_mul b⁻¹ a', mul_comm (-b⁻¹) a, mul_comm (-b⁻¹) a', ← inv_neg b]
  have : 0 ≤ -b := by apply le_neg_of_le_neg; simp [h]
  exact div_le_div_right_of_nonneg this h'

lemma div_le_div_right_of_nonpos {a a' b : EReal} (h : b ≤ 0) (h' : a ≤ a') :
    a' / b ≤ a / b :=
  antitone_div_right_of_nonpos h h'

lemma strictAnti_div_right_of_neg {b : EReal} (h : b < 0) (h' : b ≠ ⊥) :
    StrictAnti fun a ↦ a / b := by
  intro a a' a_lt_a'
  simp only
  apply lt_of_le_of_ne <| div_le_div_right_of_nonpos (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  rw [← @EReal.mul_div_cancel a b h' (ne_top_of_lt h) (ne_of_lt h), ← hyp,
    @EReal.mul_div_cancel a' b h' (ne_top_of_lt h) (ne_of_lt h)]

lemma div_lt_div_right_of_neg {a a' b : EReal} (h₁ : b < 0) (h₂ : b ≠ ⊥)
    (h₃ : a < a') : a' / b < a / b :=
  strictAnti_div_right_of_neg h₁ h₂ h₃

lemma le_div_iff_mul_le {a b c : EReal} (h : b > 0) (h' : b ≠ ⊤) :
    a ≤ c / b ↔ a * b ≤ c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [mul_div b a b, mul_comm a b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

lemma div_le_iff_le_mul {a b c : EReal} (h : 0 < b) (h' : b ≠ ⊤) :
    a / b ≤ c ↔ a ≤ b * c := by
  nth_rw 1 [← @mul_div_cancel c b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [mul_div b c b, mul_comm b]
  exact StrictMono.le_iff_le (strictMono_div_right_of_pos h h')

lemma div_nonneg {a b : EReal} (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a / b :=
  mul_nonneg h (inv_nonneg_of_nonneg h')

lemma div_nonpos_of_nonpos_of_nonneg {a b : EReal} (h : a ≤ 0) (h' : 0 ≤ b) : a / b ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg_of_nonneg h')

lemma div_nonpos_of_nonneg_of_nonpos {a b : EReal} (h : 0 ≤ a) (h' : b ≤ 0) : a / b ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos h (inv_nonpos_of_nonpos h')

lemma div_nonneg_of_nonpos_of_nonpos {a b : EReal} (h : a ≤ 0) (h' : b ≤ 0) : 0 ≤ a / b :=
  le_of_eq_of_le (Eq.symm zero_div) (div_le_div_right_of_nonpos h' h)

end EReal

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/6038): restore
/-
namespace Tactic

open Positivity

private theorem ereal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : EReal) ≠ 0 :=
  EReal.coe_ne_zero.2

private theorem ereal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : EReal) :=
  EReal.coe_nonneg.2

private theorem ereal_coe_pos {r : ℝ} : 0 < r → 0 < (r : EReal) :=
  EReal.coe_pos.2

private theorem ereal_coe_ennreal_pos {r : ℝ≥0∞} : 0 < r → 0 < (r : EReal) :=
  EReal.coe_ennreal_pos.2

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

end Tactic
-/

set_option linter.style.longFile 1800
