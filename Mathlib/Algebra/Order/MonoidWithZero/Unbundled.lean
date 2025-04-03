/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Typeclasses
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Bound.Attribute
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.Nontriviality

/-!
# Monotonicity of multiplication by positive elements in monoids with zero
-/

open Function

variable {M₀ α : Type*}

section MonoidWithZero
variable [MonoidWithZero M₀]

section Preorder
variable [Preorder M₀] {a b : M₀} {m n : ℕ}

@[simp] lemma pow_nonneg [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ n
  | 0 => pow_zero a ▸ zero_le_one
  | n + 1 => pow_succ a n ▸ mul_nonneg (pow_nonneg ha _) ha

lemma zero_pow_le_one [ZeroLEOneClass M₀] : ∀ n : ℕ, (0 : M₀) ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by rw [zero_pow n.succ_ne_zero]; exact zero_le_one

lemma pow_le_pow_of_le_one [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] (ha₀ : 0 ≤ a)
    (ha₁ : a ≤ 1) : ∀ {m n : ℕ}, m ≤ n → a ^ n ≤ a ^ m
  | _, _, Nat.le.refl => le_rfl
  | _, _, Nat.le.step h => by
    rw [pow_succ']
    exact (mul_le_of_le_one_left (pow_nonneg ha₀ _) ha₁).trans <| pow_le_pow_of_le_one ha₀ ha₁ h

lemma pow_le_of_le_one [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1)
    (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))

lemma sq_le [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) :
    a ^ 2 ≤ a := pow_le_of_le_one h₀ h₁ two_ne_zero

lemma one_le_mul_of_one_le_of_one_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : M₀) ≤ a * b := ha.trans <| le_mul_of_one_le_right (zero_le_one.trans ha) hb

lemma one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b := hb.trans_le <| le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

lemma one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b := ha.trans_le <| le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt

lemma mul_lt_one_of_nonneg_of_lt_one_left [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 := (mul_le_of_le_one_right ha₀ hb).trans_lt ha

lemma mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) :
    a * b < 1 := (mul_le_of_le_one_left hb₀ ha).trans_lt hb

section
variable [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]

@[bound]
protected lemma Bound.one_lt_mul : 1 ≤ a ∧ 1 < b ∨ 1 < a ∧ 1 ≤ b → 1 < a * b := by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]

@[bound]
lemma mul_le_one₀ (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  one_mul (1 : M₀) ▸ mul_le_mul ha hb hb₀ zero_le_one

lemma pow_le_one₀ : ∀ {n : ℕ}, 0 ≤ a → a ≤ 1 → a ^ n ≤ 1
  | 0, _, _ => (pow_zero a).le
  | n + 1, h₀, h₁ => (pow_succ a n).le.trans (mul_le_one₀ (pow_le_one₀ h₀ h₁) h₀ h₁)

lemma pow_lt_one₀ (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']; exact mul_lt_one_of_nonneg_of_lt_one_left h₀ h₁ (pow_le_one₀ h₀ h₁.le)

lemma one_le_pow₀ (ha : 1 ≤ a) : ∀ {n : ℕ}, 1 ≤ a ^ n
  | 0 => by rw [pow_zero]
  | n + 1 => by
    simpa only [pow_succ', mul_one]
      using mul_le_mul ha (one_le_pow₀ ha) zero_le_one (zero_le_one.trans ha)

lemma one_lt_pow₀ (ha : 1 < a) : ∀ {n : ℕ}, n ≠ 0 → 1 < a ^ n
  | 0, h => (h rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact one_lt_mul_of_lt_of_le ha (one_le_pow₀ ha.le)

lemma pow_right_mono₀ (h : 1 ≤ a) : Monotone (a ^ ·) :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succ']; exact le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans h) _) h

/-- `bound` lemma for branching on `1 ≤ a ∨ a ≤ 1` when proving `a ^ n ≤ a ^ m` -/
@[bound]
lemma Bound.pow_le_pow_right_of_le_one_or_one_le (h : 1 ≤ a ∧ n ≤ m ∨ 0 ≤ a ∧ a ≤ 1 ∧ m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

@[gcongr]
lemma pow_le_pow_right₀ (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := pow_right_mono₀ ha hmn

lemma le_self_pow₀ (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa only [pow_one] using pow_le_pow_right₀ ha <| Nat.pos_iff_ne_zero.2 hn

/-- The `bound` tactic can't handle `m ≠ 0` goals yet, so we express as `0 < m` -/
@[bound]
lemma Bound.le_self_pow_of_pos (ha : 1 ≤ a) (hn : 0 < n) : a ≤ a ^ n := le_self_pow₀ ha hn.ne'

@[mono, gcongr, bound]
theorem pow_le_pow_left₀ (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by simpa only [pow_succ']
      using mul_le_mul hab (pow_le_pow_left₀ ha hab _) (pow_nonneg ha _) (ha.trans hab)

lemma pow_left_monotoneOn : MonotoneOn (fun a : M₀ ↦ a ^ n) {x | 0 ≤ x} :=
  fun _a ha _b _ hab ↦ pow_le_pow_left₀ ha hab _

end

variable [Preorder α] {f g : α → M₀}

lemma monotone_mul_left_of_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ a * x :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha

lemma monotone_mul_right_of_nonneg [MulPosMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ x * a :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_right h ha

lemma Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp hf

lemma Monotone.const_mul [PosMulMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp hf

lemma Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp_antitone hf

lemma Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp_antitone hf

end Preorder


section PartialOrder
variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

lemma mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 ≤ a) (hab : a < b) :
    a * a < b * b := mul_lt_mul' hab.le hab ha <| ha.trans_lt hab

-- In the next lemma, we used to write `Set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `Set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
lemma strictMonoOn_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] :
    StrictMonoOn (fun x ↦ x * x) {x : M₀ | 0 ≤ x} := fun _ hx _ _ hxy ↦ mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
protected lemma Decidable.mul_lt_mul'' [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
    [DecidableLE M₀] (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 ↦ mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 ↦ by
    rw [← b0, mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

lemma lt_mul_left [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < b * a := by
  simpa using mul_lt_mul_of_pos_right hb ha

lemma lt_mul_right [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  simpa using mul_lt_mul_of_pos_left hb ha

lemma lt_mul_self [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a * a :=
  lt_mul_left (ha.trans_le' zero_le_one) ha

section strict_mono
variable [ZeroLEOneClass M₀] [PosMulStrictMono M₀]

@[simp] lemma pow_pos (ha : 0 < a) : ∀ n, 0 < a ^ n
  | 0 => by nontriviality; rw [pow_zero]; exact zero_lt_one
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_pos ha _) ha

lemma sq_pos_of_pos (ha : 0 < a) : 0 < a ^ 2 := pow_pos ha _

variable [MulPosStrictMono M₀]

@[gcongr, bound]
lemma pow_lt_pow_left₀ (hab : a < b)
    (ha : 0 ≤ a) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
  | n + 1, _ => by
    simpa only [pow_succ] using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (pow_le_pow_left₀ ha hab.le _) hab ha (pow_pos (ha.trans_lt hab) _)

/-- See also `pow_left_strictMono₀` and `Nat.pow_left_strictMono`. -/
lemma pow_left_strictMonoOn₀ (hn : n ≠ 0) : StrictMonoOn (· ^ n : M₀ → M₀) {a | 0 ≤ a} :=
  fun _a ha _b _ hab ↦ pow_lt_pow_left₀ hab ha hn

/-- See also `pow_right_strictMono'`. -/
lemma pow_right_strictMono₀ (h : 1 < a) : StrictMono (a ^ ·) :=
  have : 0 < a := zero_le_one.trans_lt h
  strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ'] using mul_lt_mul h (le_refl (a ^ n)) (pow_pos this _) this.le

@[gcongr]
lemma pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono₀ h hmn

lemma pow_lt_pow_iff_right₀ (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
  (pow_right_strictMono₀ h).lt_iff_lt

lemma pow_le_pow_iff_right₀ (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m :=
  (pow_right_strictMono₀ h).le_iff_le

lemma lt_self_pow₀ (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

lemma pow_right_strictAnti₀ (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  strictAnti_nat_of_succ_lt fun n => by
    simpa only [pow_succ', one_mul] using mul_lt_mul h₁ le_rfl (pow_pos h₀ n) zero_le_one

lemma pow_lt_pow_iff_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  (pow_right_strictAnti₀ h₀ h₁).lt_iff_lt

lemma pow_lt_pow_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  (pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁).2 hmn

lemma pow_lt_self_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a := by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ h₀ h₁ hn

end strict_mono

variable [Preorder α] {f g : α → M₀}

lemma strictMono_mul_left_of_pos [PosMulStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ a * x := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_left b_lt_c ha

lemma strictMono_mul_right_of_pos [MulPosStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ x * a := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_right b_lt_c ha

lemma StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp hf

lemma StrictMono.const_mul [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp hf

lemma StrictAnti.mul_const [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp_strictAnti hf

lemma StrictAnti.const_mul [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp_strictAnti hf

lemma StrictMono.mul_monotone [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 < g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

lemma Monotone.mul_strictMono [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 < f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

lemma StrictMono.mul [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

end PartialOrder

section LinearOrder
variable [LinearOrder M₀] [ZeroLEOneClass M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀] {a b : M₀}
  {m n : ℕ}

lemma pow_le_pow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (pow_left_strictMonoOn₀ hn).le_iff_le ha hb

lemma pow_lt_pow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b :=
  (pow_left_strictMonoOn₀ hn).lt_iff_lt ha hb

@[simp]
lemma pow_left_inj₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

lemma pow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective (a ^ ·) := by
  obtain ha₁ | ha₁ := ha₁.lt_or_lt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective

@[simp]
lemma pow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (pow_right_injective₀ ha₀ ha₁).eq_iff

lemma pow_le_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  simpa only [one_pow] using pow_le_pow_iff_left₀ ha zero_le_one hn

lemma one_le_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a := by
  simpa only [one_pow] using pow_le_pow_iff_left₀ zero_le_one ha hn

lemma pow_lt_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

lemma one_lt_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 < a ^ n ↔ 1 < a := by
  simpa only [one_pow] using pow_lt_pow_iff_left₀ zero_le_one ha hn

lemma pow_eq_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  simpa only [one_pow] using pow_left_inj₀ ha zero_le_one hn

lemma sq_le_one_iff₀ (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 :=
  pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma sq_lt_one_iff₀ (ha : 0 ≤ a) : a ^ 2 < 1 ↔ a < 1 :=
  pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma one_le_sq_iff₀ (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a :=
  one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma one_lt_sq_iff₀ (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a :=
  one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma lt_of_pow_lt_pow_left₀ (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left₀ hb hn _) h

lemma le_of_pow_le_pow_left₀ (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_not_lt fun h1 => not_le_of_lt (pow_lt_pow_left₀ h1 hb hn) h

@[simp]
lemma sq_eq_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b := pow_left_inj₀ ha hb (by decide)

lemma lt_of_mul_self_lt_mul_self₀ (hb : 0 ≤ b) : a * a < b * b → a < b := by
  simp_rw [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb

lemma sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b :=
  pow_lt_pow_iff_left₀ ha hb two_ne_zero

lemma sq_le_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b :=
  pow_le_pow_iff_left₀ ha hb two_ne_zero

end MonoidWithZero.LinearOrder

section CancelMonoidWithZero

variable [CancelMonoidWithZero α]

section PartialOrder

variable [PartialOrder α]

theorem PosMulMono.toPosMulStrictMono [PosMulMono α] : PosMulStrictMono α where
  elim := fun x _ _ h => (mul_le_mul_of_nonneg_left h.le x.2.le).lt_of_ne
    (h.ne ∘ mul_left_cancel₀ x.2.ne')

theorem posMulMono_iff_posMulStrictMono : PosMulMono α ↔ PosMulStrictMono α :=
  ⟨@PosMulMono.toPosMulStrictMono α _ _, @PosMulStrictMono.toPosMulMono α _ _⟩

theorem MulPosMono.toMulPosStrictMono [MulPosMono α] : MulPosStrictMono α where
  elim := fun x _ _ h => (mul_le_mul_of_nonneg_right h.le x.2.le).lt_of_ne
    (h.ne ∘ mul_right_cancel₀ x.2.ne')

theorem mulPosMono_iff_mulPosStrictMono : MulPosMono α ↔ MulPosStrictMono α :=
  ⟨@MulPosMono.toMulPosStrictMono α _ _, @MulPosStrictMono.toMulPosMono α _ _⟩

theorem PosMulReflectLT.toPosMulReflectLE [PosMulReflectLT α] : PosMulReflectLE α where
  elim := fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le

theorem posMulReflectLE_iff_posMulReflectLT : PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨@PosMulReflectLE.toPosMulReflectLT α _ _, @PosMulReflectLT.toPosMulReflectLE α _ _⟩

theorem MulPosReflectLT.toMulPosReflectLE [MulPosReflectLT α] : MulPosReflectLE α where
  elim := fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le

theorem mulPosReflectLE_iff_mulPosReflectLT : MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨@MulPosReflectLE.toMulPosReflectLT α _ _, @MulPosReflectLT.toMulPosReflectLE α _ _⟩

end PartialOrder

end CancelMonoidWithZero
