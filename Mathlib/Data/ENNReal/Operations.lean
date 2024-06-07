/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.ENNReal.Basic

#align_import data.real.ennreal from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

/-!
# Properties of addition, multiplication and subtraction on extended non-negative real numbers

In this file we prove elementary properties of algebraic operations on `ℝ≥0∞`, including addition,
multiplication, natural powers and truncated subtraction, as well as how these interact with the
order structure on `ℝ≥0∞`. Notably excluded from this list are inversion and division, the
definitions and properties of which can be found in `Data.ENNReal.Inv`.

Note: the definitions of the operations included in this file can be found in `Data.ENNReal.Basic`.
-/

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

section Mul

-- Porting note (#11215): TODO: generalize to `WithTop`
@[mono, gcongr]
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := by
  rcases lt_iff_exists_nnreal_btwn.1 ac with ⟨a', aa', a'c⟩
  lift a to ℝ≥0 using ne_top_of_lt aa'
  rcases lt_iff_exists_nnreal_btwn.1 bd with ⟨b', bb', b'd⟩
  lift b to ℝ≥0 using ne_top_of_lt bb'
  norm_cast at *
  calc
    ↑(a * b) < ↑(a' * b') := coe_lt_coe.2 (mul_lt_mul₀ aa' bb')
    _ ≤ c * d := mul_le_mul' a'c.le b'd.le
#align ennreal.mul_lt_mul ENNReal.mul_lt_mul

-- TODO: generalize to `CovariantClass α α (· * ·) (· ≤ ·)`
theorem mul_left_mono : Monotone (a * ·) := fun _ _ => mul_le_mul' le_rfl
#align ennreal.mul_left_mono ENNReal.mul_left_mono

-- TODO: generalize to `CovariantClass α α (swap (· * ·)) (· ≤ ·)`
theorem mul_right_mono : Monotone (· * a) := fun _ _ h => mul_le_mul' h le_rfl
#align ennreal.mul_right_mono ENNReal.mul_right_mono

-- Porting note (#11215): TODO: generalize to `WithTop`
theorem pow_strictMono : ∀ {n : ℕ}, n ≠ 0 → StrictMono fun x : ℝ≥0∞ => x ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simpa only [pow_one] using strictMono_id
  | n + 2, _ => fun x y h ↦ by
    simp_rw [pow_succ _ (n + 1)]; exact mul_lt_mul (pow_strictMono n.succ_ne_zero h) h
#align ennreal.pow_strict_mono ENNReal.pow_strictMono

@[gcongr] protected theorem pow_lt_pow_left (h : a < b) {n : ℕ} (hn : n ≠ 0) :
    a ^ n < b ^ n :=
  ENNReal.pow_strictMono hn h

theorem max_mul : max a b * c = max (a * c) (b * c) := mul_right_mono.map_max
#align ennreal.max_mul ENNReal.max_mul

theorem mul_max : a * max b c = max (a * b) (a * c) := mul_left_mono.map_max
#align ennreal.mul_max ENNReal.mul_max

-- Porting note (#11215): TODO: generalize to `WithTop`
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

-- Porting note (#11215): TODO: generalize to `WithTop`
theorem mul_eq_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b = a * c ↔ b = c :=
  (mul_left_strictMono h0 hinf).injective.eq_iff
#align ennreal.mul_eq_mul_left ENNReal.mul_eq_mul_left

-- Porting note (#11215): TODO: generalize to `WithTop`
theorem mul_eq_mul_right : c ≠ 0 → c ≠ ∞ → (a * c = b * c ↔ a = b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_eq_mul_left
#align ennreal.mul_eq_mul_right ENNReal.mul_eq_mul_right

-- Porting note (#11215): TODO: generalize to `WithTop`
theorem mul_le_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : (a * b ≤ a * c ↔ b ≤ c) :=
  (mul_left_strictMono h0 hinf).le_iff_le
#align ennreal.mul_le_mul_left ENNReal.mul_le_mul_left

-- Porting note (#11215): TODO: generalize to `WithTop`
theorem mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left
#align ennreal.mul_le_mul_right ENNReal.mul_le_mul_right

-- Porting note (#11215): TODO: generalize to `WithTop`
theorem mul_lt_mul_left (h0 : a ≠ 0) (hinf : a ≠ ∞) : (a * b < a * c ↔ b < c) :=
  (mul_left_strictMono h0 hinf).lt_iff_lt
#align ennreal.mul_lt_mul_left ENNReal.mul_lt_mul_left

-- Porting note (#11215): TODO: generalize to `WithTop`
theorem mul_lt_mul_right : c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left
#align ennreal.mul_lt_mul_right ENNReal.mul_lt_mul_right

end Mul

section OperationsAndOrder

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

end OperationsAndOrder

section OperationsAndInfty

variable {α : Type*}

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

-- Porting note: added because `simp` no longer uses `WithTop` lemmas for `ℝ≥0∞`
@[simp] theorem mul_top (h : a ≠ 0) : a * ∞ = ∞ := WithTop.mul_top h

theorem top_mul' : ∞ * a = if a = 0 then 0 else ∞ := by convert WithTop.top_mul' a
#align ennreal.top_mul ENNReal.top_mul'

-- Porting note: added because `simp` no longer uses `WithTop` lemmas for `ℝ≥0∞`
@[simp] theorem top_mul (h : a ≠ 0) : ∞ * a = ∞ := WithTop.top_mul h

theorem top_mul_top : ∞ * ∞ = ∞ := WithTop.top_mul_top
#align ennreal.top_mul_top ENNReal.top_mul_top

-- Porting note (#11215): TODO: assume `n ≠ 0` instead of `0 < n`
-- Porting note (#11215): TODO: generalize to `WithTop`
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

-- Porting note (#11215): TODO: generalize to `WithTop`
@[simp] theorem pow_eq_top_iff {n : ℕ} : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 := by
  rcases n.eq_zero_or_pos with rfl | (hn : 0 < n)
  · simp
  · induction a
    · simp only [Ne, hn.ne', top_pow hn, not_false_eq_true, and_self]
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
theorem coe_finset_sum {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a ∈ s, f a) = ∑ a ∈ s, (f a : ℝ≥0∞) :=
  map_sum ofNNRealHom f s
#align ennreal.coe_finset_sum ENNReal.coe_finset_sum

@[simp, norm_cast]
theorem coe_finset_prod {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℝ≥0∞) :=
  map_prod ofNNRealHom f s
#align ennreal.coe_finset_prod ENNReal.coe_finset_prod

end OperationsAndInfty

-- Porting note (#11215): TODO: generalize to `WithTop`
@[gcongr] theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d := by
  lift a to ℝ≥0 using ac.ne_top
  lift b to ℝ≥0 using bd.ne_top
  cases c; · simp
  cases d; · simp
  simp only [← coe_add, some_eq_coe, coe_lt_coe] at *
  exact add_lt_add ac bd
#align ennreal.add_lt_add ENNReal.add_lt_add

section Cancel

-- Porting note (#11215): TODO: generalize to `WithTop`
/-- An element `a` is `AddLECancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
theorem addLECancellable_iff_ne {a : ℝ≥0∞} : AddLECancellable a ↔ a ≠ ∞ := by
  constructor
  · rintro h rfl
    refine zero_lt_one.not_le (h ?_)
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

-- Porting note: added `@[simp]`
@[simp] theorem sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ := WithTop.sub_eq_top_iff
#align ennreal.sub_eq_top_iff ENNReal.sub_eq_top_iff

theorem sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ := mt sub_eq_top_iff.mp <| mt And.left ha
#align ennreal.sub_ne_top ENNReal.sub_ne_top

@[simp, norm_cast]
theorem natCast_sub (m n : ℕ) : ↑(m - n) = (m - n : ℝ≥0∞) := by
  rw [← coe_natCast, Nat.cast_tsub, coe_sub, coe_natCast, coe_natCast]
#align ennreal.nat_cast_sub ENNReal.natCast_sub

@[deprecated (since := "2024-04-17")]
alias nat_cast_sub := natCast_sub

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

theorem sub_le_sub_iff_left (h : c ≤ a) (h' : a ≠ ∞) :
    (a - b ≤ a - c) ↔ c ≤ b :=
  (cancel_of_ne h').tsub_le_tsub_iff_left (cancel_of_ne (ne_top_of_le_ne_top h' h)) h

end Sub

section Sum

open Finset

variable {α : Type*}

/-- A product of finite numbers is still finite -/
theorem prod_lt_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : ∏ a ∈ s, f a < ∞ :=
  WithTop.prod_lt_top h
#align ennreal.prod_lt_top ENNReal.prod_lt_top

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : ∑ a ∈ s, f a < ∞ :=
  WithTop.sum_lt_top h
#align ennreal.sum_lt_top ENNReal.sum_lt_top

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top_iff {s : Finset α} {f : α → ℝ≥0∞} : ∑ a ∈ s, f a < ∞ ↔ ∀ a ∈ s, f a < ∞ :=
  WithTop.sum_lt_top_iff
#align ennreal.sum_lt_top_iff ENNReal.sum_lt_top_iff

/-- A sum of numbers is infinite iff one of them is infinite -/
theorem sum_eq_top_iff {s : Finset α} {f : α → ℝ≥0∞} : ∑ x ∈ s, f x = ∞ ↔ ∃ a ∈ s, f a = ∞ :=
  WithTop.sum_eq_top_iff
#align ennreal.sum_eq_top_iff ENNReal.sum_eq_top_iff

theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∑ x ∈ s, f x ≠ ∞) {a : α}
    (ha : a ∈ s) : f a < ∞ :=
  sum_lt_top_iff.1 h.lt_top a ha
#align ennreal.lt_top_of_sum_ne_top ENNReal.lt_top_of_sum_ne_top

/-- Seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity -/
theorem toNNReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toNNReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.toNNReal (f a) := by
  rw [← coe_inj, coe_toNNReal, coe_finset_sum, sum_congr rfl]
  · intro x hx
    exact (coe_toNNReal (hf x hx)).symm
  · exact (sum_lt_top hf).ne
#align ennreal.to_nnreal_sum ENNReal.toNNReal_sum

/-- seeing `ℝ≥0∞` as `Real` does not change their sum, unless one of the `ℝ≥0∞` is infinity -/
theorem toReal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
    ENNReal.toReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.toReal (f a) := by
  rw [ENNReal.toReal, toNNReal_sum hf, NNReal.coe_sum]
  rfl
#align ennreal.to_real_sum ENNReal.toReal_sum

theorem ofReal_sum_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) := by
  simp_rw [ENNReal.ofReal, ← coe_finset_sum, coe_inj]
  exact Real.toNNReal_sum_of_nonneg hf
#align ennreal.of_real_sum_of_nonneg ENNReal.ofReal_sum_of_nonneg

theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hlt : ∀ i ∈ s, f i < g i) : ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp [Hlt _ (Finset.mem_singleton_self _)]
  | cons _ _ _ _ ih =>
    simp only [Finset.sum_cons, forall_mem_cons] at Hlt ⊢
    exact ENNReal.add_lt_add Hlt.1 (ih Hlt.2)
#align ennreal.sum_lt_sum_of_nonempty ENNReal.sum_lt_sum_of_nonempty

theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞}
    (Hle : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i) : ∃ i ∈ s, f i ≤ g i := by
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

-- TODO: generalize some of these to `WithTop α`
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

-- Porting note: added missing `DecidableEq R`
theorem smul_top {R} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [NoZeroSMulDivisors R ℝ≥0∞] [DecidableEq R] (c : R) :
    c • ∞ = if c = 0 then 0 else ∞ := by
  rw [← smul_one_mul, mul_top']
  -- Porting note: need the primed version of `one_ne_zero` now
  simp_rw [smul_eq_zero, or_iff_left (one_ne_zero' ℝ≥0∞)]
#align ennreal.smul_top ENNReal.smul_top

end Actions

end ENNReal
