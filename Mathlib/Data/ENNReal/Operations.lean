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

@[gcongr] protected lemma pow_lt_pow_left (hab : a < b) {n : ℕ} (hn : n ≠ 0) : a ^ n < b ^ n :=
  WithTop.pow_lt_pow_left hab hn

-- TODO: generalize to `WithTop`
theorem mul_left_strictMono (h0 : a ≠ 0) (hinf : a ≠ ∞) : StrictMono (a * ·) := by
  lift a to ℝ≥0 using hinf
  rw [coe_ne_zero] at h0
  intro x y h
  contrapose! h
  simpa only [← mul_assoc, ← coe_mul, inv_mul_cancel₀ h0, coe_one, one_mul]
    using mul_le_mul_left' h (↑a⁻¹)

@[gcongr] protected theorem mul_lt_mul_left' (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_left_strictMono h0 hinf bc

@[gcongr] protected theorem mul_lt_mul_right' (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_left_strictMono h0 hinf bc

-- TODO: generalize to `WithTop`
protected theorem mul_right_inj (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b = a * c ↔ b = c :=
  (mul_left_strictMono h0 hinf).injective.eq_iff

@[deprecated (since := "2025-01-20")]
alias mul_eq_mul_left := ENNReal.mul_right_inj

-- TODO: generalize to `WithTop`
protected theorem mul_left_inj (h0 : c ≠ 0) (hinf : c ≠ ∞) : a * c = b * c ↔ a = b :=
  mul_comm c a ▸ mul_comm c b ▸ ENNReal.mul_right_inj h0 hinf

@[deprecated (since := "2025-01-20")]
alias mul_eq_mul_right := ENNReal.mul_left_inj

-- TODO: generalize to `WithTop`
theorem mul_le_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b ≤ a * c ↔ b ≤ c :=
  (mul_left_strictMono h0 hinf).le_iff_le

-- TODO: generalize to `WithTop`
theorem mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left

-- TODO: generalize to `WithTop`
theorem mul_lt_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b < a * c ↔ b < c :=
  (mul_left_strictMono h0 hinf).lt_iff_lt

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
  simp only [← coe_add, some_eq_coe, coe_lt_coe] at *
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
@[simp] theorem top_sub_coe : ∞ - ↑r = ∞ := WithTop.top_sub_coe

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
  rcases le_or_gt a b with hab | hab; · simp [hab, mul_right_mono hab, tsub_eq_zero_of_le]
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

end ENNReal
