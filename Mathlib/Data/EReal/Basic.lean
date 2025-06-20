/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Data.ENNReal.Operations

/-!
# The extended real numbers

This file defines `EReal`, `ℝ` with a top element `⊤` and a bottom element `⊥`, implemented as
`WithBot (WithTop ℝ)`.

`EReal` is a `CompleteLinearOrder`, deduced by typeclass inference from the fact that
`WithBot (WithTop L)` completes a conditionally complete linear order `L`.

Coercions from `ℝ` (called `coe` in lemmas) and from `ℝ≥0∞` (`coe_ennreal`) are registered
and their basic properties proved. The latter takes up most of the rest of this file.

## Tags

real, ereal, complete lattice
-/

open Function ENNReal NNReal Set

noncomputable section

/-- The type of extended real numbers `[-∞, ∞]`, constructed as `WithBot (WithTop ℝ)`. -/
def EReal := WithBot (WithTop ℝ)
  deriving Bot, Zero, One, Nontrivial, AddMonoid, PartialOrder, AddCommMonoid

instance : ZeroLEOneClass EReal := inferInstanceAs (ZeroLEOneClass (WithBot (WithTop ℝ)))
instance : SupSet EReal := inferInstanceAs (SupSet (WithBot (WithTop ℝ)))
instance : InfSet EReal := inferInstanceAs (InfSet (WithBot (WithTop ℝ)))

instance : CompleteLinearOrder EReal :=
  inferInstanceAs (CompleteLinearOrder (WithBot (WithTop ℝ)))

instance : LinearOrder EReal :=
  inferInstanceAs (LinearOrder (WithBot (WithTop ℝ)))

instance : IsOrderedAddMonoid EReal :=
  inferInstanceAs (IsOrderedAddMonoid (WithBot (WithTop ℝ)))

instance : AddCommMonoidWithOne EReal :=
  inferInstanceAs (AddCommMonoidWithOne (WithBot (WithTop ℝ)))

instance : DenselyOrdered EReal :=
  inferInstanceAs (DenselyOrdered (WithBot (WithTop ℝ)))

instance : CharZero EReal := inferInstanceAs (CharZero (WithBot (WithTop ℝ)))

/-- The canonical inclusion from reals to ereals. Registered as a coercion. -/
@[coe] def Real.toEReal : ℝ → EReal := WithBot.some ∘ WithTop.some

namespace EReal

-- things unify with `WithBot.decidableLT` later if we don't provide this explicitly.
instance decidableLT : DecidableLT EReal :=
  WithBot.decidableLT

-- TODO: Provide explicitly, otherwise it is inferred noncomputably from `CompleteLinearOrder`
instance : Top EReal := ⟨WithBot.some ⊤⟩

instance : Coe ℝ EReal := ⟨Real.toEReal⟩

theorem coe_strictMono : StrictMono Real.toEReal :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono

theorem coe_injective : Injective Real.toEReal :=
  coe_strictMono.injective

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℝ} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[gcongr] protected alias ⟨_, coe_le_coe⟩ := EReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : ℝ} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[gcongr] protected alias ⟨_, coe_lt_coe⟩ := EReal.coe_lt_coe_iff

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℝ} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : ℝ} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_injective.ne_iff

@[simp, norm_cast]
protected theorem coe_natCast {n : ℕ} : ((n : ℝ) : EReal) = n := rfl

/-- The canonical map from nonnegative extended reals to extended reals. -/
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
protected def rec {motive : EReal → Sort*}
    (bot : motive ⊥) (coe : ∀ a : ℝ, motive a) (top : motive ⊤) : ∀ a : EReal, motive a
  | ⊥ => bot
  | (a : ℝ) => coe a
  | ⊤ => top

protected lemma «forall» {p : EReal → Prop} : (∀ r, p r) ↔ p ⊥ ∧ p ⊤ ∧ ∀ r : ℝ, p r where
  mp h := ⟨h _, h _, fun _ ↦ h _⟩
  mpr h := EReal.rec h.1 h.2.2 h.2.1

protected lemma «exists» {p : EReal → Prop} : (∃ r, p r) ↔ p ⊥ ∨ p ⊤ ∨ ∃ r : ℝ, p r where
  mp := by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩

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

lemma toReal_eq_zero_iff {x : EReal} : x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  cases x <;> norm_num

lemma toReal_ne_zero_iff {x : EReal} : x.toReal ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥ := by
  simp only [ne_eq, toReal_eq_zero_iff, not_or]

lemma toReal_eq_toReal {x y : EReal} (hx_top : x ≠ ⊤) (hx_bot : x ≠ ⊥)
    (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) :
    x.toReal = y.toReal ↔ x = y := by
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  lift y to ℝ using ⟨hy_top, hy_bot⟩
  simp

lemma toReal_nonneg {x : EReal} (hx : 0 ≤ x) : 0 ≤ x.toReal := by
  cases x
  · norm_num
  · exact toReal_coe _ ▸ EReal.coe_nonneg.mp hx
  · norm_num

lemma toReal_nonpos {x : EReal} (hx : x ≤ 0) : x.toReal ≤ 0 := by
  cases x
  · norm_num
  · exact toReal_coe _ ▸ EReal.coe_nonpos.mp hx
  · norm_num

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
  | bot => exact (not_lt_bot ha₁).elim
  | coe a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | top => exact (not_top_lt ha₂).elim

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

lemma coe_ennreal_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : (x.toReal : EReal) = x := by
  lift x to ℝ≥0 using hx
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
    | ⊥ => fun h => absurd h bot_lt_zero.not_ge
    | ⊤ => fun _ => ⟨⊤, rfl⟩
    | (x : ℝ) => fun h => ⟨.some ⟨x, EReal.coe_nonneg.1 h⟩, rfl⟩

instance : CanLift EReal ℝ≥0∞ (↑) (0 ≤ ·) := ⟨range_coe_ennreal.ge⟩

@[simp, norm_cast]
theorem coe_ennreal_pos {x : ℝ≥0∞} : (0 : EReal) < x ↔ 0 < x := by
  rw [← coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]

theorem coe_ennreal_pos_iff_ne_zero {x : ℝ≥0∞} : (0 : EReal) < x ↔ x ≠ 0 := by
  rw [coe_ennreal_pos, pos_iff_ne_zero]

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

/-! ### toENNReal -/

/-- `x.toENNReal` returns `x` if it is nonnegative, `0` otherwise. -/
noncomputable def toENNReal (x : EReal) : ℝ≥0∞ :=
  if x = ⊤ then ⊤
  else ENNReal.ofReal x.toReal

@[simp] lemma toENNReal_top : (⊤ : EReal).toENNReal = ⊤ := rfl

@[simp]
lemma toENNReal_of_ne_top {x : EReal} (hx : x ≠ ⊤) : x.toENNReal = ENNReal.ofReal x.toReal :=
  if_neg hx

@[simp]
lemma toENNReal_eq_top_iff {x : EReal} : x.toENNReal = ⊤ ↔ x = ⊤ := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toENNReal]

lemma toENNReal_ne_top_iff {x : EReal} : x.toENNReal ≠ ⊤ ↔ x ≠ ⊤ := toENNReal_eq_top_iff.not

@[simp]
lemma toENNReal_of_nonpos {x : EReal} (hx : x ≤ 0) : x.toENNReal = 0 := by
  rw [toENNReal, if_neg (fun h ↦ ?_)]
  · exact ENNReal.ofReal_of_nonpos (toReal_nonpos hx)
  · exact zero_ne_top <| top_le_iff.mp <| h ▸ hx

lemma toENNReal_bot : (⊥ : EReal).toENNReal = 0 := toENNReal_of_nonpos bot_le
lemma toENNReal_zero : (0 : EReal).toENNReal = 0 := toENNReal_of_nonpos le_rfl

lemma toENNReal_eq_zero_iff {x : EReal} : x.toENNReal = 0 ↔ x ≤ 0 := by
  induction x <;> simp [toENNReal]

lemma toENNReal_ne_zero_iff {x : EReal} : x.toENNReal ≠ 0 ↔ 0 < x := by
  simp [toENNReal_eq_zero_iff.not]

@[simp]
lemma toENNReal_pos_iff {x : EReal} : 0 < x.toENNReal ↔ 0 < x := by
  rw [pos_iff_ne_zero, toENNReal_ne_zero_iff]

@[simp]
lemma coe_toENNReal {x : EReal} (hx : 0 ≤ x) : (x.toENNReal : EReal) = x := by
  rw [toENNReal]
  by_cases h_top : x = ⊤
  · rw [if_pos h_top, h_top]
    rfl
  rw [if_neg h_top]
  simp only [coe_ennreal_ofReal, ge_iff_le, hx, toReal_nonneg, max_eq_left]
  exact coe_toReal h_top fun _ ↦ by simp_all only [le_bot_iff, zero_ne_bot]

lemma coe_toENNReal_eq_max {x : EReal} : x.toENNReal = max 0 x := by
  rcases le_total 0 x with (hx | hx)
  · rw [coe_toENNReal hx, max_eq_right hx]
  · rw [toENNReal_of_nonpos hx, max_eq_left hx, coe_ennreal_zero]

@[simp]
lemma toENNReal_coe {x : ℝ≥0∞} : (x : EReal).toENNReal = x := by
  by_cases h_top : x = ⊤
  · rw [h_top, coe_ennreal_top, toENNReal_top]
  rwa [toENNReal, if_neg _, toReal_coe_ennreal, ENNReal.ofReal_toReal_eq_iff]
  simp [h_top]

@[simp] lemma real_coe_toENNReal (x : ℝ) : (x : EReal).toENNReal = ENNReal.ofReal x := rfl

@[simp]
lemma toReal_toENNReal {x : EReal} (hx : 0 ≤ x) : x.toENNReal.toReal = x.toReal := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toReal_nonneg hx]

lemma toENNReal_eq_toENNReal {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x.toENNReal = y.toENNReal ↔ x = y := by
  induction x <;> induction y <;> simp_all

lemma toENNReal_le_toENNReal {x y : EReal} (h : x ≤ y) : x.toENNReal ≤ y.toENNReal := by
  induction x
  · simp
  · by_cases hy_top : y = ⊤
    · simp [hy_top]
    simp only [toENNReal, coe_ne_top, ↓reduceIte, toReal_coe, hy_top]
    exact ENNReal.ofReal_le_ofReal <| EReal.toReal_le_toReal h (coe_ne_bot _) hy_top
  · simp_all

lemma toENNReal_lt_toENNReal {x y : EReal} (hx : 0 ≤ x) (hxy : x < y) :
    x.toENNReal < y.toENNReal :=
  lt_of_le_of_ne (toENNReal_le_toENNReal hxy.le)
    fun h ↦ hxy.ne <| (toENNReal_eq_toENNReal hx (hx.trans_lt hxy).le).mp h

/-! ### nat coercion -/

theorem coe_coe_eq_natCast (n : ℕ) : (n : ℝ) = (n : EReal) := rfl

theorem natCast_ne_bot (n : ℕ) : (n : EReal) ≠ ⊥ := Ne.symm (ne_of_beq_false rfl)

theorem natCast_ne_top (n : ℕ) : (n : EReal) ≠ ⊤ := Ne.symm (ne_of_beq_false rfl)

@[norm_cast]
theorem natCast_eq_iff {m n : ℕ} : (m : EReal) = (n : EReal) ↔ m = n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_eq_coe_iff, Nat.cast_inj]

theorem natCast_ne_iff {m n : ℕ} : (m : EReal) ≠ (n : EReal) ↔ m ≠ n :=
  not_iff_not.2 natCast_eq_iff

@[norm_cast]
theorem natCast_le_iff {m n : ℕ} : (m : EReal) ≤ (n : EReal) ↔ m ≤ n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_le_coe_iff, Nat.cast_le]

@[norm_cast]
theorem natCast_lt_iff {m n : ℕ} : (m : EReal) < (n : EReal) ↔ m < n := by
  rw [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, EReal.coe_lt_coe_iff, Nat.cast_lt]

@[simp, norm_cast]
theorem natCast_mul (m n : ℕ) :
    (m * n : ℕ) = (m : EReal) * (n : EReal) := by
  rw [← coe_coe_eq_natCast, ← coe_coe_eq_natCast, ← coe_coe_eq_natCast, Nat.cast_mul, EReal.coe_mul]

/-! ### Miscellaneous lemmas -/

theorem exists_rat_btwn_of_lt :
    ∀ {a b : EReal}, a < b → ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b
  | ⊤, _, h => (not_top_lt h).elim
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

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: cast from `ℝ` to `EReal`. -/
@[positivity Real.toEReal _]
def evalRealToEReal : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(EReal), ~q(Real.toEReal $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(EReal.coe_pos.2 $pa))
    | .nonnegative pa => pure (.nonnegative q(EReal.coe_nonneg.2 $pa))
    | .nonzero pa => pure (.nonzero q(EReal.coe_ne_zero.2 $pa))
    | _ => pure .none
  | _, _, _ => throwError "not Real.toEReal"

/-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `EReal`. -/
@[positivity ENNReal.toEReal _]
def evalENNRealToEReal : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(EReal), ~q(ENNReal.toEReal $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(EReal.coe_ennreal_pos.2 $pa))
    | .nonzero pa => pure (.positive q(EReal.coe_ennreal_pos_iff_ne_zero.2 $pa))
    | _ => pure (.nonnegative q(EReal.coe_ennreal_nonneg $a))
  | _, _, _ => throwError "not ENNReal.toEReal"

/-- Extension for the `positivity` tactic: projection from `EReal` to `ℝ`.

We prove that `EReal.toReal x` is nonnegative whenever `x` is nonnegative.
Since `EReal.toReal ⊤ = 0`, we cannot prove a stronger statement,
at least without relying on a tactic like `finiteness`. -/
@[positivity EReal.toReal _]
def evalERealToReal : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(Real), ~q(EReal.toReal $a) =>
    assertInstancesCommute
    match (← core q(inferInstance) q(inferInstance) a).toNonneg with
    | .some pa => pure (.nonnegative q(EReal.toReal_nonneg $pa))
    | _ => pure .none
  | _, _, _ => throwError "not EReal.toReal"

/-- Extension for the `positivity` tactic: projection from `EReal` to `ℝ≥0∞`.

We show that `EReal.toENNReal x` is positive whenever `x` is positive,
and it is nonnegative otherwise.
We cannot deduce any corollaries from `x ≠ 0`, since `EReal.toENNReal x = 0` for `x < 0`.
-/
@[positivity EReal.toENNReal _]
def evalERealToENNReal : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ENNReal), ~q(EReal.toENNReal $a) =>
    assertInstancesCommute
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa => pure (.positive q(EReal.toENNReal_pos_iff.2 $pa))
    | _ => pure (.nonnegative q(zero_le $e))
  | _, _, _ => throwError "not EReal.toENNReal"

end Mathlib.Meta.Positivity
