/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.GroupWithZero.Typeclasses
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Bound.Attribute
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.Nontriviality

/-!
# Lemmas on monotonicity of multiplication by positive elements
-/

open Function

variable {M₀ G₀ : Type*}

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

variable {α : Type*} [Preorder α] {f g : α → M₀}

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

variable {α : Type*} [Preorder α] {f g : α → M₀}

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

variable {α : Type*} [CancelMonoidWithZero α]

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

section GroupWithZero
variable [GroupWithZero G₀]

section Preorder
variable [Preorder G₀] [ZeroLEOneClass G₀]

/-- See `div_self` for the version with equality when `a ≠ 0`. -/
lemma div_self_le_one (a : G₀) : a / a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

end Preorder

section PartialOrder
variable [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀] {a b c : G₀}

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a :=
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  fun a ha ↦ flip lt_of_mul_lt_mul_left ha.le <| by simp [ne_of_gt ha, zero_lt_one]

alias ⟨_, inv_pos_of_pos⟩ := inv_pos

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg

lemma one_div_pos : 0 < 1 / a ↔ 0 < a := one_div a ▸ inv_pos
lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a := one_div a ▸ inv_nonneg

lemma div_pos [PosMulStrictMono G₀] (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)

lemma div_nonneg [PosMulMono G₀] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

lemma div_nonpos_of_nonpos_of_nonneg [MulPosMono G₀] (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb)

lemma zpow_nonneg [PosMulMono G₀] (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg ha _
  |-(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _

lemma zpow_pos [PosMulStrictMono G₀] (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_pos ha _
  |-(n + 1 : ℕ) => by rw [zpow_neg, inv_pos, zpow_natCast]; exact pow_pos ha _

@[deprecated (since := "2024-10-08")] alias zpow_pos_of_pos := zpow_pos

section PosMulMono
variable [PosMulMono G₀] {m n : ℤ}

/-- See `le_inv_mul_iff₀'` for a version with multiplication on the other side. -/
lemma le_inv_mul_iff₀ (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc.le)

/-- See `inv_mul_le_iff₀'` for a version with multiplication on the other side. -/
lemma inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ c * a where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc.le)

lemma one_le_inv_mul₀ (ha : 0 < a) : 1 ≤ a⁻¹ * b ↔ a ≤ b := by rw [le_inv_mul_iff₀ ha, mul_one]
lemma inv_mul_le_one₀ (ha : 0 < a) : a⁻¹ * b ≤ 1 ↔ b ≤ a := by rw [inv_mul_le_iff₀ ha, mul_one]

/-- See `inv_le_iff_one_le_mul₀` for a version with multiplication on the other side. -/
lemma inv_le_iff_one_le_mul₀' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← inv_mul_le_iff₀ ha, mul_one]

lemma one_le_inv₀ (ha : 0 < a) : 1 ≤ a⁻¹ ↔ a ≤ 1 := by simpa using one_le_inv_mul₀ ha (b := 1)
lemma inv_le_one₀ (ha : 0 < a) : a⁻¹ ≤ 1 ↔ 1 ≤ a := by simpa using inv_mul_le_one₀ ha (b := 1)

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀

@[bound]
lemma inv_le_one_of_one_le₀ (ha : 1 ≤ a) : a⁻¹ ≤ 1 := (inv_le_one₀ <| zero_lt_one.trans_le ha).2 ha

lemma one_le_inv_iff₀ : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans_le h),
    inv_inv a ▸ (inv_le_one₀ <| zero_lt_one.trans_le h).2 h⟩
  mpr h := (one_le_inv₀ h.1).2 h.2

/-- One direction of `le_inv_mul_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
lemma mul_le_of_le_inv_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c⁻¹ * b) : c * a ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_inv_mul_iff₀ hc] at h

/-- One direction of `inv_mul_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
lemma inv_mul_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c) : b⁻¹ * a ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [inv_mul_le_iff₀ hb]

@[bound]
lemma inv_mul_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : b⁻¹ * a ≤ 1 :=
  inv_mul_le_of_le_mul₀ hb zero_le_one <| by rwa [mul_one]

lemma zpow_right_mono₀ (ha : 1 ≤ a) : Monotone fun n : ℤ ↦ a ^ n := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans_le ha).ne']
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha

lemma zpow_right_anti₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) : Antitone fun n : ℤ ↦ a ^ n := by
  refine antitone_int_of_succ_le fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_le_of_le_one_right (zpow_nonneg ha₀.le _) ha₁

@[gcongr]
lemma zpow_le_zpow_right₀ (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono₀ ha hmn

@[gcongr]
lemma zpow_le_zpow_right_of_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hmn : m ≤ n) : a ^ n ≤ a ^ m :=
  zpow_right_anti₀ ha₀ ha₁ hmn

lemma one_le_zpow₀ (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n := by simpa using zpow_right_mono₀ ha hn

lemma zpow_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : 0 ≤ n) : a ^ n ≤ 1 := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

lemma zpow_le_one_of_nonpos₀ (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 := by
  simpa using zpow_right_mono₀ ha hn

lemma one_le_zpow_of_nonpos₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : n ≤ 0) : 1 ≤ a ^ n := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn

end PosMulMono

section MulPosMono
variable [MulPosMono G₀]

/-- See `le_mul_inv_iff₀'` for a version with multiplication on the other side. -/
lemma le_mul_inv_iff₀ (hc : 0 < c) : a ≤ b * c⁻¹ ↔ a * c ≤ b where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)

/-- See `mul_inv_le_iff₀'` for a version with multiplication on the other side. -/
lemma mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ a * c where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 hc.le)

/-- See `le_div_iff₀'` for a version with multiplication on the other side. -/
lemma le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]

/-- See `div_le_iff₀'` for a version with multiplication on the other side. -/
lemma div_le_iff₀ (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]

/-- See `inv_le_iff_one_le_mul₀'` for a version with multiplication on the other side. -/
lemma inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a := by
  rw [← mul_inv_le_iff₀ ha, one_mul]

lemma one_le_div₀ (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff₀ hb, one_mul]
lemma div_le_one₀ (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [div_le_iff₀ hb, one_mul]

/-- One direction of `le_mul_inv_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative).
-/
lemma mul_le_of_le_mul_inv₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b * c⁻¹) : a * c ≤ b := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using hb
  · rwa [le_mul_inv_iff₀ hc] at h

/-- One direction of `mul_inv_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative).
-/
lemma mul_inv_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a * b⁻¹ ≤ c := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [hc]
  · rwa [mul_inv_le_iff₀ hb]

/-- One direction of `le_div_iff₀` where `c` is allowed to be `0` (but `b` must be nonnegative). -/
lemma mul_le_of_le_div₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b / c) : a * c ≤ b :=
  mul_le_of_le_mul_inv₀ hb hc (div_eq_mul_inv b _ ▸ h)

/-- One direction of `div_le_iff₀` where `b` is allowed to be `0` (but `c` must be nonnegative). -/
lemma div_le_of_le_mul₀ (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c :=
  div_eq_mul_inv a _ ▸ mul_inv_le_of_le_mul₀ hb hc h

@[bound]
lemma mul_inv_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : a * b⁻¹ ≤ 1 :=
  mul_inv_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[bound]
lemma div_le_one_of_le₀ (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
  div_le_of_le_mul₀ hb zero_le_one <| by rwa [one_mul]

@[mono, gcongr, bound]
lemma div_le_div_of_nonneg_right (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_le_mul_of_nonneg_right hab (one_div_nonneg.2 hc)

variable [PosMulMono G₀]

/-- See `inv_anti₀` for the implication from right-to-left with one fewer assumption. -/
lemma inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [inv_le_iff_one_le_mul₀' ha, le_mul_inv_iff₀ hb, one_mul]

@[gcongr, bound]
lemma inv_anti₀ (hb : 0 < b) (hba : b ≤ a) : a⁻¹ ≤ b⁻¹ := (inv_le_inv₀ (hb.trans_le hba) hb).2 hba

/-- See also `inv_le_of_inv_le₀` for a one-sided implication with one fewer assumption. -/
lemma inv_le_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← inv_le_inv₀ hb (inv_pos.2 ha), inv_inv]

lemma inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
  (inv_le_comm₀ ha <| (inv_pos.2 ha).trans_le h).1 h

/-- See also `le_inv_of_le_inv₀` for a one-sided implication with one fewer assumption. -/
lemma le_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← inv_le_inv₀ (inv_pos.2 hb) ha, inv_inv]

lemma le_inv_of_le_inv₀ (ha : 0 < a) (h : a ≤ b⁻¹) : b ≤ a⁻¹ :=
  (le_inv_comm₀ ha <| inv_pos.1 <| ha.trans_le h).1 h

-- Not a `mono` lemma b/c `div_le_div₀` is strictly more general
@[gcongr]
lemma div_le_div_of_nonneg_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (hc.trans_le h) hc).mpr h) ha

end MulPosMono

section PosMulStrictMono
variable [PosMulStrictMono G₀] {m n : ℤ}

/-- See `lt_inv_mul_iff₀'` for a version with multiplication on the other side. -/
lemma lt_inv_mul_iff₀ (hc : 0 < c) : a < c⁻¹ * b ↔ c * a < b where
  mp h := by simpa [hc.ne'] using mul_lt_mul_of_pos_left h hc
  mpr h := by simpa [hc.ne'] using mul_lt_mul_of_pos_left h (inv_pos.2 hc)

/-- See `inv_mul_lt_iff₀'` for a version with multiplication on the other side. -/
lemma inv_mul_lt_iff₀ (hc : 0 < c) : c⁻¹ * b < a ↔ b < c * a where
  mp h := by simpa [hc.ne'] using mul_lt_mul_of_pos_left h hc
  mpr h := by simpa [hc.ne'] using mul_lt_mul_of_pos_left h (inv_pos.2 hc)

/-- See `inv_lt_iff_one_lt_mul₀` for a version with multiplication on the other side. -/
lemma inv_lt_iff_one_lt_mul₀' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b := by
  rw [← inv_mul_lt_iff₀ ha, mul_one]

lemma one_lt_inv_mul₀ (ha : 0 < a) : 1 < a⁻¹ * b ↔ a < b := by rw [lt_inv_mul_iff₀ ha, mul_one]
lemma inv_mul_lt_one₀ (ha : 0 < a) : a⁻¹ * b < 1 ↔ b < a := by rw [inv_mul_lt_iff₀ ha, mul_one]

lemma one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1 := by simpa using one_lt_inv_mul₀ ha (b := 1)
lemma inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a := by simpa using inv_mul_lt_one₀ ha (b := 1)

@[bound]
lemma inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1 := (inv_lt_one₀ <| zero_lt_one.trans ha).2 ha

lemma one_lt_inv_iff₀ : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 where
  mp h := ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ (inv_lt_one₀ <| zero_lt_one.trans h).2 h⟩
  mpr h := (one_lt_inv₀ h.1).2 h.2

lemma zpow_right_strictMono₀ (ha : 1 < a) : StrictMono fun n : ℤ ↦ a ^ n := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one₀ (zero_lt_one.trans ha).ne']
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha

lemma zpow_right_strictAnti₀ (ha₀ : 0 < a) (ha₁ : a < 1) : StrictAnti fun n : ℤ ↦ a ^ n := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one₀ ha₀.ne']
  exact mul_lt_of_lt_one_right (zpow_pos ha₀ _) ha₁

@[gcongr]
lemma zpow_lt_zpow_right₀ (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n :=
  zpow_right_strictMono₀ ha hmn

@[gcongr]
lemma zpow_lt_zpow_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  zpow_right_strictAnti₀ ha₀ ha₁ hmn

lemma one_lt_zpow₀ (ha : 1 < a) (hn : 0 < n) : 1 < a ^ n := by
  simpa using zpow_right_strictMono₀ ha hn

lemma zpow_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : 0 < n) : a ^ n < 1 := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

lemma zpow_lt_one_of_neg₀ (ha : 1 < a) (hn : n < 0) : a ^ n < 1 := by
  simpa using zpow_right_strictMono₀ ha hn

lemma one_lt_zpow_of_neg₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hn : n < 0) : 1 < a ^ n := by
  simpa using zpow_right_strictAnti₀ ha₀ ha₁ hn

@[simp] lemma zpow_le_zpow_iff_right₀ (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_right_strictMono₀ ha).le_iff_le

@[simp] lemma zpow_lt_zpow_iff_right₀ (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_right_strictMono₀ ha).lt_iff_lt

lemma zpow_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m ≤ a ^ n ↔ n ≤ m := (zpow_right_strictAnti₀ ha₀ ha₁).le_iff_le

lemma zpow_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) :
    a ^ m < a ^ n ↔ n < m := (zpow_right_strictAnti₀ ha₀ ha₁).lt_iff_lt

@[simp] lemma one_le_zpow_iff_right₀ (ha : 1 < a) : 1 ≤ a ^ n ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right₀ ha]

@[simp] lemma one_lt_zpow_iff_right₀ (ha : 1 < a) : 1 < a ^ n ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

@[simp] lemma one_le_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 ≤ a ^ n ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma one_lt_zpow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : 1 < a ^ n ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma zpow_le_one_iff_right₀ (ha : 1 < a) : a ^ n ≤ 1 ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right₀ ha]

@[simp] lemma zpow_lt_one_iff_right₀ (ha : 1 < a) : a ^ n < 1 ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right₀ ha]

@[simp] lemma zpow_le_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n ≤ 1 ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

@[simp] lemma zpow_lt_one_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ n < 1 ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁]

end PosMulStrictMono

section MulPosStrictMono
variable [MulPosStrictMono G₀]

/-- See `lt_mul_inv_iff₀'` for a version with multiplication on the other side. -/
lemma lt_mul_inv_iff₀ (hc : 0 < c) : a < b * c⁻¹ ↔ a * c < b where
  mp h := by simpa [hc.ne'] using mul_lt_mul_of_pos_right h hc
  mpr h := by simpa [hc.ne'] using mul_lt_mul_of_pos_right h (inv_pos.2 hc)

/-- See `mul_inv_lt_iff₀'` for a version with multiplication on the other side. -/
lemma mul_inv_lt_iff₀ (hc : 0 < c) : b * c⁻¹ < a ↔ b < a * c where
  mp h := by simpa [hc.ne'] using mul_lt_mul_of_pos_right h hc
  mpr h := by simpa [hc.ne'] using mul_lt_mul_of_pos_right h (inv_pos.2 hc)

/-- See `lt_div_iff₀'` for a version with multiplication on the other side. -/
lemma lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [div_eq_mul_inv, lt_mul_inv_iff₀ hc]

/-- See `div_lt_iff₀'` for a version with multiplication on the other side. -/
lemma div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c := by
  rw [div_eq_mul_inv, mul_inv_lt_iff₀ hc]

/-- See `inv_lt_iff_one_lt_mul₀'` for a version with multiplication on the other side. -/
lemma inv_lt_iff_one_lt_mul₀ (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a := by
  rw [← mul_inv_lt_iff₀ ha, one_mul]

@[gcongr, bound]
lemma div_lt_div_of_pos_right (h : a < b) (hc : 0 < c) : a / c < b / c := by
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c]
  exact mul_lt_mul_of_pos_right h (one_div_pos.2 hc)

variable [PosMulStrictMono G₀]

/-- See `inv_strictAnti₀` for the implication from right-to-left with one fewer assumption. -/
lemma inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [inv_lt_iff_one_lt_mul₀' ha, lt_mul_inv_iff₀ hb, one_mul]

@[gcongr, bound]
lemma inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹ :=
  (inv_lt_inv₀ (hb.trans hba) hb).2 hba

/-- See also `inv_lt_of_inv_lt₀` for a one-sided implication with one fewer assumption. -/
lemma inv_lt_comm₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a := by
  rw [← inv_lt_inv₀ hb (inv_pos.2 ha), inv_inv]

lemma inv_lt_of_inv_lt₀ (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
  (inv_lt_comm₀ ha <| (inv_pos.2 ha).trans h).1 h

/-- See also `lt_inv_of_lt_inv₀` for a one-sided implication with one fewer assumption. -/
lemma lt_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← inv_lt_inv₀ (inv_pos.2 hb) ha, inv_inv]

lemma lt_inv_of_lt_inv₀ (ha : 0 < a) (h : a < b⁻¹) : b < a⁻¹ :=
  (lt_inv_comm₀ ha <| inv_pos.1 <| ha.trans h).1 h

@[gcongr, bound]
lemma div_lt_div_of_pos_left (ha : 0 < a) (hc : 0 < c) (h : c < b) : a / b < a / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_left ((inv_lt_inv₀ (hc.trans h) hc).2 h) ha

end MulPosStrictMono
end PartialOrder

section LinearOrder
variable [LinearOrder G₀] [ZeroLEOneClass G₀] {a b c d : G₀}

section PosMulMono
variable [PosMulMono G₀]

@[simp] lemma inv_neg'' : a⁻¹ < 0 ↔ a < 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_le, inv_nonneg]

@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  have := PosMulMono.toPosMulReflectLT (α := G₀); simp only [← not_lt, inv_pos]

alias inv_lt_zero := inv_neg''

lemma one_div_neg : 1 / a < 0 ↔ a < 0 := one_div a ▸ inv_neg''
lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 := one_div a ▸ inv_nonpos

lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

lemma neg_of_div_neg_right (h : a / b < 0) (ha : 0 ≤ a) : b < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun hb ↦ (div_nonneg ha hb).not_lt h

lemma neg_of_div_neg_left (h : a / b < 0) (hb : 0 ≤ b) : a < 0 :=
  have := PosMulMono.toPosMulReflectLT (α := G₀)
  lt_of_not_ge fun ha ↦ (div_nonneg ha hb).not_lt h

end PosMulMono

variable [PosMulStrictMono G₀] {m n : ℤ}

lemma inv_lt_one_iff₀ : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a := by
  simp_rw [← not_le, one_le_inv_iff₀, not_and_or, not_lt]

lemma inv_le_one_iff₀ : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a := by
  simp only [← not_lt, one_lt_inv_iff₀, not_and_or]

lemma zpow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective fun n : ℤ ↦ a ^ n := by
  obtain ha₁ | ha₁ := ha₁.lt_or_lt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective

@[simp] lemma zpow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (zpow_right_injective₀ ha₀ ha₁).eq_iff

lemma zpow_eq_one_iff_right₀ (ha₀ : 0 ≤ a) (ha₁ : a ≠ 1) {n : ℤ} : a ^ n = 1 ↔ n = 0 := by
  obtain rfl | ha₀ := ha₀.eq_or_lt
  · exact zero_zpow_eq_one₀
  simpa using zpow_right_inj₀ ha₀ ha₁ (n := 0)

variable [MulPosStrictMono G₀]

lemma div_le_div_iff_of_pos_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b where
  mp := le_imp_le_of_lt_imp_lt fun hab ↦ div_lt_div_of_pos_right hab hc
  mpr hab := div_le_div_of_nonneg_right hab hc.le

lemma div_lt_div_iff_of_pos_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
  lt_iff_lt_of_le_iff_le <| div_le_div_iff_of_pos_right hc

lemma div_lt_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b < a / c ↔ c < b := by simp only [div_eq_mul_inv, mul_lt_mul_left ha, inv_lt_inv₀ hb hc]

lemma div_le_div_iff_of_pos_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 (div_lt_div_iff_of_pos_left ha hc hb)

@[mono, gcongr, bound]
lemma div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hac ((inv_le_inv₀ (hd.trans_le hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb) hc

@[gcongr]
lemma div_lt_div₀ (hac : a < c) (hdb : d ≤ b) (hc : 0 ≤ c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul hac ((inv_le_inv₀ (hd.trans_le hdb) hd).2 hdb) (inv_pos.2 <| hd.trans_le hdb) hc

lemma div_lt_div₀' (hac : a ≤ c) (hdb : d < b) (hc : 0 < c) (hd : 0 < d) : a / b < c / d := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_lt_mul' hac ((inv_lt_inv₀ (hd.trans hdb) hd).2 hdb)
    (inv_nonneg.2 <| hd.le.trans hdb.le) hc

end GroupWithZero.LinearOrder

section CommSemigroupHasZero

variable {α : Type*} [Mul α] [@Std.Commutative α (· * ·)] [Zero α] [Preorder α]

theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp only [posMulStrictMono_iff, mulPosStrictMono_iff, Std.Commutative.comm]

theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp only [posMulReflectLT_iff, mulPosReflectLT_iff, Std.Commutative.comm]

theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by
  simp only [posMulMono_iff, mulPosMono_iff, Std.Commutative.comm]

theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp only [posMulReflectLE_iff, mulPosReflectLE_iff, Std.Commutative.comm]

end CommSemigroupHasZero

section CommGroupWithZero
variable [CommGroupWithZero G₀]
variable [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]

section PosMulMono
variable [PosMulMono G₀] {a b c d : G₀}

/-- See `le_inv_mul_iff₀` for a version with multiplication on the other side. -/
lemma le_inv_mul_iff₀' (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b := by
  rw [le_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_le_iff₀` for a version with multiplication on the other side. -/
lemma inv_mul_le_iff₀' (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ a * c := by
  rw [inv_mul_le_iff₀ hc, mul_comm]

/-- See `le_mul_inv_iff₀` for a version with multiplication on the other side. -/
lemma le_mul_inv_iff₀' (hc : 0 < c) : a ≤ b * c⁻¹ ↔ c * a ≤ b := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [le_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_le_iff₀` for a version with multiplication on the other side. -/
lemma mul_inv_le_iff₀' (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ c * a := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [mul_inv_le_iff₀ hc, mul_comm]

lemma div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [div_le_iff₀ hb, ← mul_div_right_comm, le_div_iff₀ hd]

/-- See `le_div_iff₀` for a version with multiplication on the other side. -/
lemma le_div_iff₀' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [le_div_iff₀ hc, mul_comm]

/-- See `div_le_iff₀` for a version with multiplication on the other side. -/
lemma div_le_iff₀' (hc : 0 < c) : b / c ≤ a ↔ b ≤ c * a := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [div_le_iff₀ hc, mul_comm]

lemma le_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a ≤ b / c ↔ c ≤ b / a := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [le_div_iff₀ ha, le_div_iff₀' hc]

lemma div_le_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b ≤ c ↔ a / c ≤ b := by
  have := posMulMono_iff_mulPosMono.1 ‹_›
  rw [div_le_iff₀ hb, div_le_iff₀' hc]

end PosMulMono

section PosMulStrictMono
variable [PosMulStrictMono G₀] {a b c d : G₀}

/-- See `lt_inv_mul_iff₀` for a version with multiplication on the other side. -/
lemma lt_inv_mul_iff₀' (hc : 0 < c) : a < c⁻¹ * b ↔ a * c < b := by
  rw [lt_inv_mul_iff₀ hc, mul_comm]

/-- See `inv_mul_lt_iff₀` for a version with multiplication on the other side. -/
lemma inv_mul_lt_iff₀' (hc : 0 < c) : c⁻¹ * b < a ↔ b < a * c := by
  rw [inv_mul_lt_iff₀ hc, mul_comm]

/-- See `lt_mul_inv_iff₀` for a version with multiplication on the other side. -/
lemma lt_mul_inv_iff₀' (hc : 0 < c) : a < b * c⁻¹ ↔ c * a < b := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [lt_mul_inv_iff₀ hc, mul_comm]

/-- See `mul_inv_lt_iff₀` for a version with multiplication on the other side. -/
lemma mul_inv_lt_iff₀' (hc : 0 < c) : b * c⁻¹ < a ↔ b < c * a := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [mul_inv_lt_iff₀ hc, mul_comm]

lemma div_lt_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b < c / d ↔ a * d < c * b := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [div_lt_iff₀ hb, ← mul_div_right_comm, lt_div_iff₀ hd]

/-- See `lt_div_iff₀` for a version with multiplication on the other side. -/
lemma lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [lt_div_iff₀ hc, mul_comm]

/-- See `div_lt_iff₀` for a version with multiplication on the other side. -/
lemma div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [div_lt_iff₀ hc, mul_comm]

lemma lt_div_comm₀ (ha : 0 < a) (hc : 0 < c) : a < b / c ↔ c < b / a := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [lt_div_iff₀ ha, lt_div_iff₀' hc]

lemma div_lt_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b < c ↔ a / c < b := by
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  rw [div_lt_iff₀ hb, div_lt_iff₀' hc]

end PosMulStrictMono
end CommGroupWithZero
