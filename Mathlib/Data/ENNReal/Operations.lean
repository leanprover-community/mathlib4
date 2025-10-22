/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.ENNReal.Real

/-!
# Properties of addition, multiplication and subtraction on extended non-negative real numbers

In this file we prove elementary properties of algebraic operations on `ℝ≥0∞`, including addition,
multiplication, natural powers and truncated subtraction, as well as how these interact with the
order structure on `ℝ≥0∞`. Notably excluded from this list are inversion and division, the
definitions and properties of which can be found in `Mathlib/Data/ENNReal/Inv.lean`.

Note: the definitions of the operations included in this file can be found in
`Mathlib/Data/ENNReal/Basic.lean`.
-/

assert_not_exists Finset

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

section Mul

@[mono, gcongr]
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := WithTop.mul_lt_mul ac bd

protected lemma pow_right_strictMono {n : ℕ} (hn : n ≠ 0) : StrictMono fun a : ℝ≥0∞ ↦ a ^ n :=
  WithTop.pow_right_strictMono hn

protected lemma pow_le_pow_left_iff {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (ENNReal.pow_right_strictMono hn).le_iff_le

protected lemma pow_lt_pow_left_iff {n : ℕ} (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b :=
  (ENNReal.pow_right_strictMono hn).lt_iff_lt

@[mono, gcongr] protected lemma pow_le_pow_left {n : ℕ} (h : a ≤ b) : a ^ n ≤ b ^ n :=
  pow_le_pow_left' h n
@[mono, gcongr] protected alias ⟨_, pow_lt_pow_left⟩ := ENNReal.pow_lt_pow_left_iff

lemma mul_left_strictMono (h₀ : a ≠ 0) (hinf : a ≠ ∞) : StrictMono (· * a) :=
  WithTop.mul_left_strictMono (pos_iff_ne_zero.2 h₀) hinf

lemma mul_right_strictMono (h₀ : a ≠ 0) (hinf : a ≠ ∞) : StrictMono (a * ·) :=
  WithTop.mul_right_strictMono (pos_iff_ne_zero.2 h₀) hinf

@[gcongr] protected theorem mul_lt_mul_left' (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_right_strictMono h0 hinf bc

@[gcongr] protected theorem mul_lt_mul_right' (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_right_strictMono h0 hinf bc

-- TODO: generalize to `WithTop`
protected theorem mul_right_inj (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b = a * c ↔ b = c :=
  (mul_right_strictMono h0 hinf).injective.eq_iff

-- TODO: generalize to `WithTop`
protected theorem mul_left_inj (h0 : c ≠ 0) (hinf : c ≠ ∞) : a * c = b * c ↔ a = b :=
  mul_comm c a ▸ mul_comm c b ▸ ENNReal.mul_right_inj h0 hinf

-- TODO: generalize to `WithTop`
theorem mul_le_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b ≤ a * c ↔ b ≤ c :=
  (mul_right_strictMono h0 hinf).le_iff_le

-- TODO: generalize to `WithTop`
theorem mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left

-- TODO: generalize to `WithTop`
theorem mul_lt_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b < a * c ↔ b < c :=
  (mul_right_strictMono h0 hinf).lt_iff_lt

-- TODO: generalize to `WithTop`
theorem mul_lt_mul_right : c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left

protected lemma mul_eq_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * b = a ↔ b = 1 := by
  simpa using ENNReal.mul_right_inj ha₀ ha (c := 1)

protected lemma mul_eq_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b = b ↔ a = 1 := by
  simpa using ENNReal.mul_left_inj hb₀ hb (b := 1)

end Mul

section OperationsAndOrder

protected theorem pow_pos : 0 < a → ∀ n : ℕ, 0 < a ^ n :=
  CanonicallyOrderedAdd.pow_pos

protected theorem pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a ^ n ≠ 0 := by
  simpa only [pos_iff_ne_zero] using ENNReal.pow_pos

theorem not_lt_zero : ¬a < 0 := by simp

protected theorem le_of_add_le_add_left : a ≠ ∞ → a + b ≤ a + c → b ≤ c :=
  WithTop.le_of_add_le_add_left

protected theorem le_of_add_le_add_right : a ≠ ∞ → b + a ≤ c + a → b ≤ c :=
  WithTop.le_of_add_le_add_right

@[gcongr] protected theorem add_lt_add_left : a ≠ ∞ → b < c → a + b < a + c :=
  WithTop.add_lt_add_left

@[gcongr] protected theorem add_lt_add_right : a ≠ ∞ → b < c → b + a < c + a :=
  WithTop.add_lt_add_right

protected theorem add_le_add_iff_left : a ≠ ∞ → (a + b ≤ a + c ↔ b ≤ c) :=
  WithTop.add_le_add_iff_left

protected theorem add_le_add_iff_right : a ≠ ∞ → (b + a ≤ c + a ↔ b ≤ c) :=
  WithTop.add_le_add_iff_right

protected theorem add_lt_add_iff_left : a ≠ ∞ → (a + b < a + c ↔ b < c) :=
  WithTop.add_lt_add_iff_left

protected theorem add_lt_add_iff_right : a ≠ ∞ → (b + a < c + a ↔ b < c) :=
  WithTop.add_lt_add_iff_right

protected theorem add_lt_add_of_le_of_lt : a ≠ ∞ → a ≤ b → c < d → a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt

protected theorem add_lt_add_of_lt_of_le : c ≠ ∞ → a < b → c ≤ d → a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le

instance addLeftReflectLT : AddLeftReflectLT ℝ≥0∞ :=
  WithTop.addLeftReflectLT

theorem lt_add_right (ha : a ≠ ∞) (hb : b ≠ 0) : a < a + b := by
  rwa [← pos_iff_ne_zero, ← ENNReal.add_lt_add_iff_left ha, add_zero] at hb

end OperationsAndOrder

section OperationsAndInfty

variable {α : Type*} {n : ℕ}

@[simp] theorem add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := WithTop.add_eq_top

@[simp] theorem add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := WithTop.add_lt_top

theorem toNNReal_add {r₁ r₂ : ℝ≥0∞} (h₁ : r₁ ≠ ∞) (h₂ : r₂ ≠ ∞) :
    (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal := by
  lift r₁ to ℝ≥0 using h₁
  lift r₂ to ℝ≥0 using h₂
  rfl

/-- If `a ≤ b + c` and `a = ∞` whenever `b = ∞` or `c = ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add' (hle : a ≤ b + c) (hb : b = ∞ → a = ∞) (hc : c = ∞ → a = ∞) :
    a.toReal ≤ b.toReal + c.toReal := by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

/-- If `a ≤ b + c`, `b ≠ ∞`, and `c ≠ ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add (hle : a ≤ b + c) (hb : b ≠ ∞) (hc : c ≠ ∞) :
    a.toReal ≤ b.toReal + c.toReal :=
  toReal_le_add' hle (flip absurd hb) (flip absurd hc)

theorem not_lt_top {x : ℝ≥0∞} : ¬x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, Classical.not_not]

theorem add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ := by simpa only [lt_top_iff_ne_top] using add_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
protected lemma Finiteness.add_ne_top {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : a + b ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ha, hb⟩

theorem mul_top' : a * ∞ = if a = 0 then 0 else ∞ := by convert WithTop.mul_top' a

@[simp] theorem mul_top (h : a ≠ 0) : a * ∞ = ∞ := WithTop.mul_top h

theorem top_mul' : ∞ * a = if a = 0 then 0 else ∞ := by convert WithTop.top_mul' a

@[simp] theorem top_mul (h : a ≠ 0) : ∞ * a = ∞ := WithTop.top_mul h

theorem top_mul_top : ∞ * ∞ = ∞ := WithTop.top_mul_top

theorem mul_eq_top : a * b = ∞ ↔ a ≠ 0 ∧ b = ∞ ∨ a = ∞ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff

theorem mul_lt_top : a < ∞ → b < ∞ → a * b < ∞ := WithTop.mul_lt_top

-- This is unsafe because we could have `a = ∞` and `b = 0` or vice-versa
@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
theorem mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ := WithTop.mul_ne_top

theorem lt_top_of_mul_ne_top_left (h : a * b ≠ ∞) (hb : b ≠ 0) : a < ∞ :=
  lt_top_iff_ne_top.2 fun ha => h <| mul_eq_top.2 (Or.inr ⟨ha, hb⟩)

theorem lt_top_of_mul_ne_top_right (h : a * b ≠ ∞) (ha : a ≠ 0) : b < ∞ :=
  lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

theorem mul_lt_top_iff {a b : ℝ≥0∞} : a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha hb; simp; simp]

theorem mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ := by
  rw [ENNReal.mul_lt_top_iff, and_self, or_self, or_iff_left_iff_imp]
  rintro rfl
  exact zero_lt_top

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  CanonicallyOrderedAdd.mul_pos

theorem mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
  mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩

@[simp] lemma top_pow {n : ℕ} (hn : n ≠ 0) : (∞ : ℝ≥0∞) ^ n = ∞ := WithTop.top_pow hn

@[simp] lemma pow_eq_top_iff : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 := WithTop.pow_eq_top_iff

lemma pow_ne_top_iff : a ^ n ≠ ∞ ↔ a ≠ ∞ ∨ n = 0 := WithTop.pow_ne_top_iff

@[simp] lemma pow_lt_top_iff : a ^ n < ∞ ↔ a < ∞ ∨ n = 0 := WithTop.pow_lt_top_iff

lemma eq_top_of_pow (n : ℕ) (ha : a ^ n = ∞) : a = ∞ := WithTop.eq_top_of_pow n ha

@[deprecated (since := "2025-04-24")] alias pow_eq_top := eq_top_of_pow

@[aesop (rule_sets := [finiteness]) safe apply]
lemma pow_ne_top (ha : a ≠ ∞) : a ^ n ≠ ∞ := WithTop.pow_ne_top ha
lemma pow_lt_top (ha : a < ∞) : a ^ n < ∞ := WithTop.pow_lt_top ha

end OperationsAndInfty

-- TODO: generalize to `WithTop`
@[gcongr] protected theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d := by
  lift a to ℝ≥0 using ac.ne_top
  lift b to ℝ≥0 using bd.ne_top
  cases c; · simp
  cases d; · simp
  simp only [← coe_add, coe_lt_coe] at *
  exact add_lt_add ac bd

section Cancel

-- TODO: generalize to `WithTop`
/-- An element `a` is `AddLECancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
@[simp]
theorem addLECancellable_iff_ne {a : ℝ≥0∞} : AddLECancellable a ↔ a ≠ ∞ := by
  constructor
  · rintro h rfl
    refine zero_lt_one.not_ge (h ?_)
    simp
  · rintro h b c hbc
    apply ENNReal.le_of_add_le_add_left h hbc

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_ne {a : ℝ≥0∞} (h : a ≠ ∞) : AddLECancellable a :=
  addLECancellable_iff_ne.mpr h

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_lt {a : ℝ≥0∞} (h : a < ∞) : AddLECancellable a :=
  cancel_of_ne h.ne

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_lt' {a b : ℝ≥0∞} (h : a < b) : AddLECancellable a :=
  cancel_of_ne h.ne_top

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_coe {a : ℝ≥0} : AddLECancellable (a : ℝ≥0∞) :=
  cancel_of_ne coe_ne_top

theorem add_right_inj (h : a ≠ ∞) : a + b = a + c ↔ b = c :=
  (cancel_of_ne h).inj

theorem add_left_inj (h : a ≠ ∞) : b + a = c + a ↔ b = c :=
  (cancel_of_ne h).inj_left

end Cancel

section Sub

theorem sub_eq_sInf {a b : ℝ≥0∞} : a - b = sInf { d | a ≤ d + b } :=
  le_antisymm (le_sInf fun _ h => tsub_le_iff_right.mpr h) <| sInf_le <| mem_setOf.2 le_tsub_add

/-- This is a special case of `WithTop.coe_sub` in the `ENNReal` namespace -/
@[simp, norm_cast] theorem coe_sub : (↑(r - p) : ℝ≥0∞) = ↑r - ↑p := WithTop.coe_sub

/-- This is a special case of `WithTop.top_sub_coe` in the `ENNReal` namespace -/
@[simp] theorem top_sub_coe : ∞ - ↑r = ∞ := rfl

@[simp] lemma top_sub (ha : a ≠ ∞) : ∞ - a = ∞ := by lift a to ℝ≥0 using ha; exact top_sub_coe

/-- This is a special case of `WithTop.sub_top` in the `ENNReal` namespace -/
@[simp] theorem sub_top : a - ∞ = 0 := WithTop.sub_top

@[simp] theorem sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ := WithTop.sub_eq_top_iff
lemma sub_ne_top_iff : a - b ≠ ∞ ↔ a ≠ ∞ ∨ b = ∞ := WithTop.sub_ne_top_iff

-- This is unsafe because we could have `a = b = ∞`
@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
theorem sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ := mt sub_eq_top_iff.mp <| mt And.left ha

@[simp, norm_cast]
theorem natCast_sub (m n : ℕ) : ↑(m - n) = (m - n : ℝ≥0∞) := by
  rw [← coe_natCast, Nat.cast_tsub, coe_sub, coe_natCast, coe_natCast]

/-- See `ENNReal.sub_eq_of_eq_add'` for a version assuming that `a = c + b` itself is finite rather
than `b`. -/
protected theorem sub_eq_of_eq_add (hb : b ≠ ∞) : a = c + b → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add

/-- Weaker version of `ENNReal.sub_eq_of_eq_add` assuming that `a = c + b` itself is finite rather
han `b`. -/
protected lemma sub_eq_of_eq_add' (ha : a ≠ ∞) : a = c + b → a - b = c :=
  (cancel_of_ne ha).tsub_eq_of_eq_add'

/-- See `ENNReal.eq_sub_of_add_eq'` for a version assuming that `b = a + c` itself is finite rather
than `c`. -/
protected theorem eq_sub_of_add_eq (hc : c ≠ ∞) : a + c = b → a = b - c :=
  (cancel_of_ne hc).eq_tsub_of_add_eq

/-- Weaker version of `ENNReal.eq_sub_of_add_eq` assuming that `b = a + c` itself is finite rather
than `c`. -/
protected lemma eq_sub_of_add_eq' (hb : b ≠ ∞) : a + c = b → a = b - c :=
  (cancel_of_ne hb).eq_tsub_of_add_eq'

/-- See `ENNReal.sub_eq_of_eq_add_rev'` for a version assuming that `a = b + c` itself is finite
rather than `b`. -/
protected theorem sub_eq_of_eq_add_rev (hb : b ≠ ∞) : a = b + c → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add_rev

/-- Weaker version of `ENNReal.sub_eq_of_eq_add_rev` assuming that `a = b + c` itself is finite
rather than `b`. -/
protected lemma sub_eq_of_eq_add_rev' (ha : a ≠ ∞) : a = b + c → a - b = c :=
  (cancel_of_ne ha).tsub_eq_of_eq_add_rev'

protected theorem add_sub_cancel_left (ha : a ≠ ∞) : a + b - a = b := by
  simp [ha]

protected theorem add_sub_cancel_right (hb : b ≠ ∞) : a + b - b = a := by
  simp [hb]

protected theorem sub_add_eq_add_sub (hab : b ≤ a) (b_ne_top : b ≠ ∞) :
    a - b + c = a + c - b := by
  by_cases c_top : c = ∞
  · simpa [c_top] using ENNReal.eq_sub_of_add_eq b_ne_top rfl
  refine ENNReal.eq_sub_of_add_eq b_ne_top ?_
  simp only [add_assoc, add_comm c b]
  simpa only [← add_assoc] using (add_left_inj c_top).mpr <| tsub_add_cancel_of_le hab

lemma add_sub_add_eq_sub_right (hc : c ≠ ∞ := by finiteness) : (a + c) - (b + c) = a - b := by
  lift c to ℝ≥0 using hc
  cases a <;> cases b
  · simp
  · simp
  · simp
  · norm_cast
    rw [add_tsub_add_eq_tsub_right]

lemma add_sub_add_eq_sub_left (hc : c ≠ ∞ := by finiteness) : (c + a) - (c + b) = a - b := by
  simp_rw [add_comm c]
  exact ENNReal.add_sub_add_eq_sub_right hc

protected theorem lt_add_of_sub_lt_left (h : a ≠ ∞ ∨ b ≠ ∞) : a - b < c → a < b + c := by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (Classical.not_not.2 rfl)
  · exact (cancel_of_ne hb).lt_add_of_tsub_lt_left

protected theorem lt_add_of_sub_lt_right (h : a ≠ ∞ ∨ c ≠ ∞) : a - c < b → a < b + c :=
  add_comm c b ▸ ENNReal.lt_add_of_sub_lt_left h

theorem le_sub_of_add_le_left (ha : a ≠ ∞) : a + b ≤ c → b ≤ c - a :=
  (cancel_of_ne ha).le_tsub_of_add_le_left

theorem le_sub_of_add_le_right (hb : b ≠ ∞) : a + b ≤ c → a ≤ c - b :=
  (cancel_of_ne hb).le_tsub_of_add_le_right

protected theorem sub_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : a - c < b :=
  ((cancel_of_lt' <| hac.trans_lt h).tsub_lt_iff_right hac).mpr h

protected theorem sub_lt_iff_lt_right (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < c + b :=
  (cancel_of_ne hb).tsub_lt_iff_right hab

protected theorem sub_lt_iff_lt_left (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < b + c :=
  (cancel_of_ne hb).tsub_lt_iff_left hab

theorem le_sub_iff_add_le_left (hc : c ≠ ∞) (hcb : c ≤ b) : a ≤ b - c ↔ c + a ≤ b :=
  ⟨fun h ↦ add_le_of_le_tsub_left_of_le hcb h, le_sub_of_add_le_left hc⟩

theorem le_sub_iff_add_le_right (hc : c ≠ ∞) (hcb : c ≤ b) : a ≤ b - c ↔ a + c ≤ b :=
  ⟨fun h ↦ add_le_of_le_tsub_right_of_le hcb h, le_sub_of_add_le_right hc⟩

protected theorem sub_lt_self (ha : a ≠ ∞) (ha₀ : a ≠ 0) (hb : b ≠ 0) : a - b < a :=
  (cancel_of_ne ha).tsub_lt_self (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)

protected theorem sub_lt_self_iff (ha : a ≠ ∞) : a - b < a ↔ 0 < a ∧ 0 < b :=
  (cancel_of_ne ha).tsub_lt_self_iff

theorem sub_lt_of_sub_lt (h₂ : c ≤ a) (h₃ : a ≠ ∞ ∨ b ≠ ∞) (h₁ : a - b < c) : a - c < b :=
  ENNReal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ENNReal.lt_add_of_sub_lt_right h₃ h₁)

theorem sub_sub_cancel (h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b :=
  (cancel_of_ne <| sub_ne_top h).tsub_tsub_cancel_of_le h2

theorem sub_right_inj {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≤ a) (hc : c ≤ a) :
    a - b = a - c ↔ b = c :=
  (cancel_of_ne ha).tsub_right_inj (cancel_of_ne <| ne_top_of_le_ne_top ha hb)
    (cancel_of_ne <| ne_top_of_le_ne_top ha hc) hb hc

protected theorem sub_mul (h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c := by
  rcases le_or_gt a b with hab | hab; · simp [hab, mul_left_mono hab, tsub_eq_zero_of_le]
  rcases eq_or_lt_of_le (zero_le b) with (rfl | hb); · simp
  exact (cancel_of_ne <| mul_ne_top hab.ne_top (h hb hab)).tsub_mul

protected theorem mul_sub (h : 0 < c → c < b → a ≠ ∞) : a * (b - c) = a * b - a * c := by
  simp only [mul_comm a]
  exact ENNReal.sub_mul h

theorem sub_le_sub_iff_left (h : c ≤ a) (h' : a ≠ ∞) :
    (a - b ≤ a - c) ↔ c ≤ b :=
  (cancel_of_ne h').tsub_le_tsub_iff_left (cancel_of_ne (ne_top_of_le_ne_top h' h)) h

theorem le_toReal_sub {a b : ℝ≥0∞} (hb : b ≠ ∞) : a.toReal - b.toReal ≤ (a - b).toReal := by
  lift b to ℝ≥0 using hb
  induction a
  · simp
  · simp only [← coe_sub, NNReal.sub_def, Real.coe_toNNReal', coe_toReal]
    exact le_max_left _ _

@[simp]
lemma toNNReal_sub (hb : b ≠ ∞) : (a - b).toNNReal = a.toNNReal - b.toNNReal := by
  lift b to ℝ≥0 using hb; induction a <;> simp [← coe_sub]

@[simp]
lemma toReal_sub_of_le (hba : b ≤ a) (ha : a ≠ ∞) : (a - b).toReal = a.toReal - b.toReal := by
  simp [ENNReal.toReal, ne_top_of_le_ne_top ha hba, toNNReal_mono ha hba]

theorem ofReal_sub (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q := by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (ofReal_le_ofReal h)]
  refine ENNReal.eq_sub_of_add_eq ofReal_ne_top ?_
  rw [← ofReal_add (sub_nonneg_of_le h) hq, sub_add_cancel]

lemma sub_sub_sub_cancel_left (ha : a ≠ ∞) (h : b ≤ a) : a - c - (a - b) = b - c := by
  have hb : b ≠ ∞ := ne_top_of_le_ne_top ha h
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  cases c
  · simp
  · norm_cast
    rw [tsub_tsub_tsub_cancel_left]
    exact mod_cast h

end Sub

section Interval

variable {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set ℝ≥0∞}

protected theorem Ico_eq_Iio : Ico 0 y = Iio y :=
  Ico_bot

theorem mem_Iio_self_add : x ≠ ∞ → ε ≠ 0 → x ∈ Iio (x + ε) := fun xt ε0 => lt_add_right xt ε0

theorem mem_Ioo_self_sub_add : x ≠ ∞ → x ≠ 0 → ε₁ ≠ 0 → ε₂ ≠ 0 → x ∈ Ioo (x - ε₁) (x + ε₂) :=
  fun xt x0 ε0 ε0' => ⟨ENNReal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

@[simp]
theorem image_coe_Iic (x : ℝ≥0) : (↑) '' Iic x = Iic (x : ℝ≥0∞) := WithTop.image_coe_Iic

@[simp]
theorem image_coe_Ici (x : ℝ≥0) : (↑) '' Ici x = Ico ↑x ∞ := WithTop.image_coe_Ici

@[simp]
theorem image_coe_Iio (x : ℝ≥0) : (↑) '' Iio x = Iio (x : ℝ≥0∞) := WithTop.image_coe_Iio

@[simp]
theorem image_coe_Ioi (x : ℝ≥0) : (↑) '' Ioi x = Ioo ↑x ∞ := WithTop.image_coe_Ioi

@[simp]
theorem image_coe_Icc (x y : ℝ≥0) : (↑) '' Icc x y = Icc (x : ℝ≥0∞) y := WithTop.image_coe_Icc

@[simp]
theorem image_coe_Ico (x y : ℝ≥0) : (↑) '' Ico x y = Ico (x : ℝ≥0∞) y := WithTop.image_coe_Ico

@[simp]
theorem image_coe_Ioc (x y : ℝ≥0) : (↑) '' Ioc x y = Ioc (x : ℝ≥0∞) y := WithTop.image_coe_Ioc

@[simp]
theorem image_coe_Ioo (x y : ℝ≥0) : (↑) '' Ioo x y = Ioo (x : ℝ≥0∞) y := WithTop.image_coe_Ioo

@[simp]
theorem image_coe_uIcc (x y : ℝ≥0) : (↑) '' uIcc x y = uIcc (x : ℝ≥0∞) y := by simp [uIcc]

@[simp]
theorem image_coe_uIoc (x y : ℝ≥0) : (↑) '' uIoc x y = uIoc (x : ℝ≥0∞) y := by simp [uIoc]

@[simp]
theorem image_coe_uIoo (x y : ℝ≥0) : (↑) '' uIoo x y = uIoo (x : ℝ≥0∞) y := by simp [uIoo]

end Interval

section iInf

variable {ι : Sort*} {f g : ι → ℝ≥0∞}
variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

theorem toNNReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toNNReal = ⨅ i, (f i).toNNReal := by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, toNNReal_top, NNReal.iInf_empty]
  · lift f to ι → ℝ≥0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]

theorem toNNReal_sInf (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using (toNNReal_iInf hf)

theorem toReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toReal = ⨅ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]

theorem toReal_sInf (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toReal = sInf (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]

@[simp] lemma ofReal_iInf [Nonempty ι] (f : ι → ℝ) :
    ENNReal.ofReal (⨅ i, f i) = ⨅ i, ENNReal.ofReal (f i) := by
  obtain ⟨i, hi⟩ | h := em (∃ i, f i ≤ 0)
  · rw [(iInf_eq_bot _).2 fun _ _ ↦ ⟨i, by simpa [ofReal_of_nonpos hi]⟩]
    simp [Real.iInf_nonpos' ⟨i, hi⟩]
  replace h i : 0 ≤ f i := le_of_not_ge fun hi ↦ h ⟨i, hi⟩
  refine eq_of_forall_le_iff fun a ↦ ?_
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  rw [le_iInf_iff, le_ofReal_iff_toReal_le ha, le_ciInf_iff ⟨0, by simpa [mem_lowerBounds]⟩]
  · exact forall_congr' fun i ↦ (le_ofReal_iff_toReal_le ha (h _)).symm
  · exact Real.iInf_nonneg h

theorem iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_iInf fun _ => tsub_le_iff_right.2 <| iInf_le _ _)

theorem sub_iInf : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [tsub_le_iff_right, add_comm, iInf_add]
  simp [tsub_le_iff_right, add_comm]

theorem sInf_add {s : Set ℝ≥0∞} : sInf s + a = ⨅ b ∈ s, b + a := by simp [sInf_eq_iInf, iInf_add]

theorem add_iInf {a : ℝ≥0∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm, iInf_add]; simp [add_comm]

theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]

lemma iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≥ ·)] {f g : ι → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a, f a + g a :=
  iInf_add_iInf fun i j ↦ (exists_le_le i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules

lemma add_iInf₂ {κ : ι → Sort*} (f : (i : ι) → κ i → ℝ≥0∞) :
    a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j := by
  simp [add_iInf]

lemma iInf₂_add {κ : ι → Sort*} (f : (i : ι) → κ i → ℝ≥0∞) :
    (⨅ (i) (j), f i j) + a = ⨅ (i) (j), f i j + a := by
  simp only [add_comm, add_iInf₂]

lemma add_sInf {s : Set ℝ≥0∞} : a + sInf s = ⨅ b ∈ s, a + b := by
  rw [sInf_eq_iInf, add_iInf₂]

variable {κ : Sort*}

lemma le_iInf_add_iInf {g : κ → ℝ≥0∞} (h : ∀ i j, a ≤ f i + g j) :
    a ≤ iInf f + iInf g := by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

lemma le_iInf₂_add_iInf₂ {q₁ : ι → Sort*} {q₂ : κ → Sort*}
    {f : (i : ι) → q₁ i → ℝ≥0∞} {g : (k : κ) → q₂ k → ℝ≥0∞}
    (h : ∀ i pi k qk, a ≤ f i pi + g k qk) :
    a ≤ (⨅ (i) (qi), f i qi) + ⨅ (k) (qk), g k qk := by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

@[simp] lemma iInf_gt_eq_self (a : ℝ≥0∞) : ⨅ b, ⨅ _ : a < b, b = a := by
  refine le_antisymm ?_ (le_iInf₂ fun b hb ↦ hb.le)
  refine le_of_forall_gt fun c hac ↦ ?_
  obtain ⟨d, had, hdc⟩ := exists_between hac
  exact (iInf₂_le_of_le d had le_rfl).trans_lt hdc

lemma exists_add_lt_of_add_lt {x y z : ℝ≥0∞} (h : y + z < x) :
    ∃ y' > y, ∃ z' > z, y' + z' < x := by
  contrapose! h
  simpa using le_iInf₂_add_iInf₂ h

end iInf

section iSup

variable {ι κ : Sort*} {f g : ι → ℝ≥0∞} {s : Set ℝ≥0∞} {a : ℝ≥0∞}

theorem toNNReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toNNReal = ⨆ i, (f i).toNNReal := by
  lift f to ι → ℝ≥0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, toNNReal_top]

theorem toNNReal_sSup (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toNNReal = sSup (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using (toNNReal_iSup hf)

theorem toReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toReal = ⨆ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]

theorem toReal_sSup (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toReal = sSup (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]

theorem iSup_sub : (⨆ i, f i) - a = ⨆ i, f i - a :=
  le_antisymm (tsub_le_iff_right.2 <| iSup_le fun i => tsub_le_iff_right.1 <| le_iSup (f · - a) i)
    (iSup_le fun _ => tsub_le_tsub (le_iSup _ _) (le_refl a))

@[simp] lemma iSup_eq_zero : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 := iSup_eq_bot

@[simp] lemma iSup_zero : ⨆ _ : ι, (0 : ℝ≥0∞) = 0 := by simp

lemma iSup_natCast : ⨆ n : ℕ, (n : ℝ≥0∞) = ∞ :=
  (iSup_eq_top _).2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

lemma add_iSup [Nonempty ι] (f : ι → ℝ≥0∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  refine le_antisymm ?_ <| iSup_le fun i ↦ by grw [← le_iSup]
  refine add_le_of_le_tsub_left_of_le (le_iSup_of_le (Classical.arbitrary _) le_self_add) ?_
  exact iSup_le fun i ↦ ENNReal.le_sub_of_add_le_left ha <| le_iSup (a + f ·) i

lemma iSup_add [Nonempty ι] (f : ι → ℝ≥0∞) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  simp [add_comm, add_iSup]

lemma add_biSup' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℝ≥0∞) :
    a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i := by
  haveI : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

lemma biSup_add' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℝ≥0∞) :
    (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a := by simp only [add_comm, add_biSup' h]

lemma add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℝ≥0∞) :
    a + ⨆ i ∈ s, f i = ⨆ i ∈ s, a + f i := add_biSup' hs _

lemma biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℝ≥0∞) :
    (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a := biSup_add' hs _

lemma add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b ∈ s, a + b := by
  rw [sSup_eq_iSup, add_biSup hs]

lemma sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b ∈ s, b + a := by
  rw [sSup_eq_iSup, biSup_add hs]

lemma iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ → ℝ≥0∞} (h : ∀ i j, f i + g j ≤ a) :
    iSup f + iSup g ≤ a := by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

lemma biSup_add_biSup_le' {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {g : κ → ℝ≥0∞} (h : ∀ i, p i → ∀ j, q j → f i + g j ≤ a) :
    (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j ≤ a := by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

lemma biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι → ℝ≥0∞} {g : κ → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ i ∈ s, ∀ j ∈ t, f i + g j ≤ a) :
    (⨆ i ∈ s, f i) + ⨆ j ∈ t, g j ≤ a := biSup_add_biSup_le' hs ht h

lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp only [iSup_of_empty, bot_eq_zero, zero_add]
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f g : ι → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules

lemma sub_iSup [Nonempty ι] (ha : a ≠ ∞) : a - ⨆ i, f i = ⨅ i, a - f i := by
  obtain ⟨i, hi⟩ | h := em (∃ i, a < f i)
  · rw [tsub_eq_zero_iff_le.2 <| le_iSup_of_le _ hi.le, (iInf_eq_bot _).2, bot_eq_zero]
    exact fun x hx ↦ ⟨i, by simpa [hi.le, tsub_eq_zero_of_le]⟩
  simp_rw [not_exists, not_lt] at h
  refine le_antisymm (le_iInf fun i ↦ tsub_le_tsub_left (le_iSup ..) _) <|
    ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ha <| iSup_le h) <|
    add_le_of_le_tsub_right_of_le (iInf_le_of_le (Classical.arbitrary _) tsub_le_self) <|
    iSup_le fun i ↦ ?_
  rw [← sub_sub_cancel ha (h _)]
  exact tsub_le_tsub_left (iInf_le (a - f ·) i) _

@[simp] lemma iSup_lt_eq_self (a : ℝ≥0∞) : ⨆ b, ⨆ _ : b < a, b = a := by
  refine le_antisymm (iSup₂_le fun b hb ↦ hb.le) ?_
  refine le_of_forall_lt fun c hca ↦ ?_
  obtain ⟨d, hcd, hdb⟩ := exists_between hca
  exact hcd.trans_le <| le_iSup₂_of_le d hdb le_rfl

-- TODO: Prove the two one-side versions
lemma exists_lt_add_of_lt_add {x y z : ℝ≥0∞} (h : x < y + z) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ y' < y, ∃ z' < z, x < y' + z' := by
  contrapose! h
  simpa using biSup_add_biSup_le' (by exact ⟨0, hy.bot_lt⟩) (by exact ⟨0, hz.bot_lt⟩) h

end iSup

end ENNReal
