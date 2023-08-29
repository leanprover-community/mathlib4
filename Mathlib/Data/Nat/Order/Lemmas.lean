/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Nat.Units
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Divisibility
import Mathlib.Algebra.GroupWithZero.Divisibility

#align_import data.nat.order.lemmas from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Further lemmas about the natural numbers

The distinction between this file and `Mathlib.Data.Nat.Order.Basic` is not particularly clear.
They are separated for now to minimize the porting requirements for tactics during the transition to
mathlib4. After `Mathlib.Data.Rat.Order` has been ported,
please feel free to reorganize these two files.
-/


universe u v

variable {a b m n k : ℕ}

namespace Nat

/-! ### Sets -/


instance Subtype.orderBot (s : Set ℕ) [DecidablePred (· ∈ s)] [h : Nonempty s] : OrderBot s where
  bot := ⟨Nat.find (nonempty_subtype.1 h), Nat.find_spec (nonempty_subtype.1 h)⟩
  bot_le x := Nat.find_min' _ x.2
#align nat.subtype.order_bot Nat.Subtype.orderBot

instance Subtype.semilatticeSup (s : Set ℕ) : SemilatticeSup s :=
  { Subtype.linearOrder s, LinearOrder.toLattice with }
#align nat.subtype.semilattice_sup Nat.Subtype.semilatticeSup

theorem Subtype.coe_bot {s : Set ℕ} [DecidablePred (· ∈ s)] [h : Nonempty s] :
    ((⊥ : s) : ℕ) = Nat.find (nonempty_subtype.1 h) :=
  rfl
#align nat.subtype.coe_bot Nat.Subtype.coe_bot

theorem set_eq_univ {S : Set ℕ} : S = Set.univ ↔ 0 ∈ S ∧ ∀ k : ℕ, k ∈ S → k + 1 ∈ S :=
  ⟨by rintro rfl; simp, fun ⟨h0, hs⟩ => Set.eq_univ_of_forall (set_induction h0 hs)⟩
      -- ⊢ 0 ∈ Set.univ ∧ ∀ (k : ℕ), k ∈ Set.univ → k + 1 ∈ Set.univ
                  -- 🎉 no goals
#align nat.set_eq_univ Nat.set_eq_univ

/-! ### `div` -/

protected theorem lt_div_iff_mul_lt {n d : ℕ} (hnd : d ∣ n) (a : ℕ) : a < n / d ↔ d * a < n := by
  rcases d.eq_zero_or_pos with (rfl | hd0); · simp [zero_dvd_iff.mp hnd]
  -- ⊢ a < n / 0 ↔ 0 * a < n
                                              -- 🎉 no goals
  rw [← mul_lt_mul_left hd0, ← Nat.eq_mul_of_div_eq_right hnd rfl]
  -- 🎉 no goals
#align nat.lt_div_iff_mul_lt Nat.lt_div_iff_mul_lt

-- porting note: new lemma
theorem mul_div_eq_iff_dvd {n d : ℕ} : d * (n / d) = n ↔ d ∣ n :=
  calc
    d * (n / d) = n ↔ d * (n / d) = d * (n / d) + (n % d) := by rw [div_add_mod]
                                                                -- 🎉 no goals
    _ ↔ d ∣ n := by rw [self_eq_add_right, dvd_iff_mod_eq_zero]
                    -- 🎉 no goals

-- porting note: new lemma
theorem mul_div_lt_iff_not_dvd {n d : ℕ} : d * (n / d) < n ↔ ¬(d ∣ n) :=
  (mul_div_le _ _).lt_iff_ne.trans mul_div_eq_iff_dvd.not

theorem div_eq_iff_eq_of_dvd_dvd {n x y : ℕ} (hn : n ≠ 0) (hx : x ∣ n) (hy : y ∣ n) :
    n / x = n / y ↔ x = y := by
  constructor
  -- ⊢ n / x = n / y → x = y
  · intro h
    -- ⊢ x = y
    rw [← mul_right_inj' hn]
    -- ⊢ n * x = n * y
    apply Nat.eq_mul_of_div_eq_left (dvd_mul_of_dvd_left hy x)
    -- ⊢ n * x / y = n
    rw [eq_comm, mul_comm, Nat.mul_div_assoc _ hy]
    -- ⊢ n = x * (n / y)
    exact Nat.eq_mul_of_div_eq_right hx h
    -- 🎉 no goals
  · intro h
    -- ⊢ n / x = n / y
    rw [h]
    -- 🎉 no goals
#align nat.div_eq_iff_eq_of_dvd_dvd Nat.div_eq_iff_eq_of_dvd_dvd

protected theorem div_eq_zero_iff {a b : ℕ} (hb : 0 < b) : a / b = 0 ↔ a < b :=
  ⟨fun h => by rw [← mod_add_div a b, h, mul_zero, add_zero]; exact mod_lt _ hb, fun h => by
               -- ⊢ a % b < b
                                                              -- 🎉 no goals
    rw [← mul_right_inj' hb.ne', ← @add_left_cancel_iff _ _ _ (a % b), mod_add_div, mod_eq_of_lt h,
      mul_zero, add_zero]⟩
#align nat.div_eq_zero_iff Nat.div_eq_zero_iff

protected theorem div_eq_zero {a b : ℕ} (hb : a < b) : a / b = 0 :=
  (Nat.div_eq_zero_iff <| (zero_le a).trans_lt hb).mpr hb
#align nat.div_eq_zero Nat.div_eq_zero

/-! ### `mod`, `dvd` -/


@[simp]
protected theorem dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1 :=
  ⟨eq_one_of_dvd_one, fun e => e.symm ▸ dvd_rfl⟩
#align nat.dvd_one Nat.dvd_one

set_option linter.deprecated false in
@[simp]
protected theorem not_two_dvd_bit1 (n : ℕ) : ¬2 ∣ bit1 n := by
  rw [bit1, Nat.dvd_add_right two_dvd_bit0, Nat.dvd_one]
  -- ⊢ ¬2 = 1
  -- Porting note: was `cc`
  decide
  -- 🎉 no goals
#align nat.not_two_dvd_bit1 Nat.not_two_dvd_bit1

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.-/
@[simp]
protected theorem dvd_add_self_left {m n : ℕ} : m ∣ m + n ↔ m ∣ n :=
  Nat.dvd_add_right (dvd_refl m)
#align nat.dvd_add_self_left Nat.dvd_add_self_left

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.-/
@[simp]
protected theorem dvd_add_self_right {m n : ℕ} : m ∣ n + m ↔ m ∣ n :=
  Nat.dvd_add_left (dvd_refl m)
#align nat.dvd_add_self_right Nat.dvd_add_self_right

-- TODO: update `Nat.dvd_sub` in core
theorem dvd_sub' {k m n : ℕ} (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n := by
  cases' le_total n m with H H
  -- ⊢ k ∣ m - n
  · exact dvd_sub H h₁ h₂
    -- 🎉 no goals
  · rw [tsub_eq_zero_iff_le.mpr H]
    -- ⊢ k ∣ 0
    exact dvd_zero k
    -- 🎉 no goals
#align nat.dvd_sub' Nat.dvd_sub'

theorem succ_div : ∀ a b : ℕ, (a + 1) / b = a / b + if b ∣ a + 1 then 1 else 0
  | a, 0 => by simp
               -- 🎉 no goals
  | 0, 1 => by simp
               -- 🎉 no goals
  | 0, b + 2 => by
    have hb2 : b + 2 > 1 := by simp
    -- ⊢ (0 + 1) / (b + 2) = 0 / (b + 2) + if b + 2 ∣ 0 + 1 then 1 else 0
    simp [ne_of_gt hb2, div_eq_of_lt hb2]
    -- 🎉 no goals
  | a + 1, b + 1 => by
    rw [Nat.div_eq]
    -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
    conv_rhs => rw [Nat.div_eq]
    -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
    by_cases hb_eq_a : b = a + 1
    -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
    · simp [hb_eq_a, le_refl]
      -- 🎉 no goals
    by_cases hb_le_a1 : b ≤ a + 1
    -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
    · have hb_le_a : b ≤ a := le_of_lt_succ (lt_of_le_of_ne hb_le_a1 hb_eq_a)
      -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
      have h₁ : 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 := ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a1⟩
      -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
      have h₂ : 0 < b + 1 ∧ b + 1 ≤ a + 1 := ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a⟩
      -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
      have dvd_iff : b + 1 ∣ a - b + 1 ↔ b + 1 ∣ a + 1 + 1 := by
        rw [Nat.dvd_add_iff_left (dvd_refl (b + 1)), ← add_tsub_add_eq_tsub_right a 1 b,
          add_comm (_ - _), add_assoc, tsub_add_cancel_of_le (succ_le_succ hb_le_a), add_comm 1]
      have wf : a - b < a + 1 := lt_succ_of_le tsub_le_self
      -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
      rw [if_pos h₁, if_pos h₂, @add_tsub_add_eq_tsub_right, ← tsub_add_eq_add_tsub hb_le_a,
        have := wf
        succ_div (a - b),
        @add_tsub_add_eq_tsub_right]
      simp [dvd_iff, succ_eq_add_one, add_comm 1, add_assoc]
      -- 🎉 no goals
    · have hba : ¬b ≤ a := not_le_of_gt (lt_trans (lt_succ_self a) (lt_of_not_ge hb_le_a1))
      -- ⊢ (if 0 < b + 1 ∧ b + 1 ≤ a + 1 + 1 then (a + 1 + 1 - (b + 1)) / (b + 1) + 1 e …
      have hb_dvd_a : ¬b + 1 ∣ a + 2 := fun h =>
        hb_le_a1 (le_of_succ_le_succ (le_of_dvd (succ_pos _) h))
      simp [hba, hb_le_a1, hb_dvd_a]
      -- 🎉 no goals
#align nat.succ_div Nat.succ_div

theorem succ_div_of_dvd {a b : ℕ} (hba : b ∣ a + 1) : (a + 1) / b = a / b + 1 := by
  rw [succ_div, if_pos hba]
  -- 🎉 no goals
#align nat.succ_div_of_dvd Nat.succ_div_of_dvd

theorem succ_div_of_not_dvd {a b : ℕ} (hba : ¬b ∣ a + 1) : (a + 1) / b = a / b := by
  rw [succ_div, if_neg hba, add_zero]
  -- 🎉 no goals
#align nat.succ_div_of_not_dvd Nat.succ_div_of_not_dvd

theorem dvd_iff_div_mul_eq (n d : ℕ) : d ∣ n ↔ n / d * d = n :=
  ⟨fun h => Nat.div_mul_cancel h, fun h => Dvd.intro_left (n / d) h⟩
#align nat.dvd_iff_div_mul_eq Nat.dvd_iff_div_mul_eq

theorem dvd_iff_le_div_mul (n d : ℕ) : d ∣ n ↔ n ≤ n / d * d :=
  ((dvd_iff_div_mul_eq _ _).trans le_antisymm_iff).trans (and_iff_right (div_mul_le_self n d))
#align nat.dvd_iff_le_div_mul Nat.dvd_iff_le_div_mul

theorem dvd_iff_dvd_dvd (n d : ℕ) : d ∣ n ↔ ∀ k : ℕ, k ∣ d → k ∣ n :=
  ⟨fun h _ hkd => dvd_trans hkd h, fun h => h _ dvd_rfl⟩
#align nat.dvd_iff_dvd_dvd Nat.dvd_iff_dvd_dvd

theorem dvd_div_of_mul_dvd {a b c : ℕ} (h : a * b ∣ c) : b ∣ c / a :=
  if ha : a = 0 then by simp [ha]
                        -- 🎉 no goals
  else
    have ha : 0 < a := Nat.pos_of_ne_zero ha
    have h1 : ∃ d, c = a * b * d := h
    let ⟨d, hd⟩ := h1
    have h2 : c / a = b * d := Nat.div_eq_of_eq_mul_right ha (by simpa [mul_assoc] using hd)
                                                                 -- 🎉 no goals
    show ∃ d, c / a = b * d from ⟨d, h2⟩
#align nat.dvd_div_of_mul_dvd Nat.dvd_div_of_mul_dvd

@[simp]
theorem dvd_div_iff {a b c : ℕ} (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
  ⟨fun h => mul_dvd_of_dvd_div hbc h, fun h => dvd_div_of_mul_dvd h⟩
#align nat.dvd_div_iff Nat.dvd_div_iff

@[simp]
theorem div_div_div_eq_div {a b c : ℕ} (dvd : b ∣ a) (dvd2 : a ∣ c) : c / (a / b) / b = c / a :=
  match a, b, c with
  | 0, _, _ => by simp
                  -- 🎉 no goals
  | a + 1, 0, _ => by simp at dvd
                      -- 🎉 no goals
  | a + 1, c + 1, _ => by
    have a_split : a + 1 ≠ 0 := succ_ne_zero a
    -- ⊢ x✝ / ((a + 1) / (c + 1)) / (c + 1) = x✝ / (a + 1)
    have c_split : c + 1 ≠ 0 := succ_ne_zero c
    -- ⊢ x✝ / ((a + 1) / (c + 1)) / (c + 1) = x✝ / (a + 1)
    rcases dvd2 with ⟨k, rfl⟩
    -- ⊢ (a + 1) * k / ((a + 1) / (c + 1)) / (c + 1) = (a + 1) * k / (a + 1)
    rcases dvd with ⟨k2, pr⟩
    -- ⊢ (a + 1) * k / ((a + 1) / (c + 1)) / (c + 1) = (a + 1) * k / (a + 1)
    have k2_nonzero : k2 ≠ 0 := fun k2_zero => by simp [k2_zero] at pr
    -- ⊢ (a + 1) * k / ((a + 1) / (c + 1)) / (c + 1) = (a + 1) * k / (a + 1)
    rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero a_split), pr,
      Nat.mul_div_cancel_left k2 (Nat.pos_of_ne_zero c_split), Nat.mul_comm ((c + 1) * k2) k, ←
      Nat.mul_assoc k (c + 1) k2, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero k2_nonzero),
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero c_split)]
#align nat.div_div_div_eq_div Nat.div_div_div_eq_div

/-- If a small natural number is divisible by a larger natural number,
the small number is zero. -/
theorem eq_zero_of_dvd_of_lt {a b : ℕ} (w : a ∣ b) (h : b < a) : b = 0 :=
  Nat.eq_zero_of_dvd_of_div_eq_zero w
    ((Nat.div_eq_zero_iff (lt_of_le_of_lt (zero_le b) h)).mpr h)
#align nat.eq_zero_of_dvd_of_lt Nat.eq_zero_of_dvd_of_lt

theorem le_of_lt_add_of_dvd (h : a < b + n) : n ∣ a → n ∣ b → a ≤ b := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  -- ⊢ n * a ≤ n * b
  -- porting note: Needed to give an explicit argument to `mul_add_one`
  rw [← mul_add_one n] at h
  -- ⊢ n * a ≤ n * b
  exact mul_le_mul_left' (lt_succ_iff.1 <| lt_of_mul_lt_mul_left h bot_le) _
  -- 🎉 no goals
#align nat.le_of_lt_add_of_dvd Nat.le_of_lt_add_of_dvd

@[simp]
theorem mod_div_self (m n : ℕ) : m % n / n = 0 := by
  cases n
  -- ⊢ m % zero / zero = 0
  · exact (m % 0).div_zero
    -- 🎉 no goals
  · case succ n => exact Nat.div_eq_zero (m.mod_lt n.succ_pos)
    -- 🎉 no goals
    -- 🎉 no goals
#align nat.mod_div_self Nat.mod_div_self

/-- `n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`. -/
theorem not_dvd_iff_between_consec_multiples (n : ℕ) {a : ℕ} (ha : 0 < a) :
    (∃ k : ℕ, a * k < n ∧ n < a * (k + 1)) ↔ ¬a ∣ n := by
  refine'
    ⟨fun ⟨k, hk1, hk2⟩ => not_dvd_of_between_consec_multiples hk1 hk2, fun han =>
      ⟨n / a, ⟨lt_of_le_of_ne (mul_div_le n a) _, lt_mul_div_succ _ ha⟩⟩⟩
  exact mt (Dvd.intro (n / a)) han
  -- 🎉 no goals
#align nat.not_dvd_iff_between_consec_multiples Nat.not_dvd_iff_between_consec_multiples

/-- Two natural numbers are equal if and only if they have the same multiples. -/
theorem dvd_right_iff_eq {m n : ℕ} : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
  ⟨fun h => dvd_antisymm ((h _).mpr dvd_rfl) ((h _).mp dvd_rfl), fun h n => by rw [h]⟩
                                                                               -- 🎉 no goals
#align nat.dvd_right_iff_eq Nat.dvd_right_iff_eq

/-- Two natural numbers are equal if and only if they have the same divisors. -/
theorem dvd_left_iff_eq {m n : ℕ} : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
  ⟨fun h => dvd_antisymm ((h _).mp dvd_rfl) ((h _).mpr dvd_rfl), fun h n => by rw [h]⟩
                                                                               -- 🎉 no goals
#align nat.dvd_left_iff_eq Nat.dvd_left_iff_eq

/-- `dvd` is injective in the left argument -/
theorem dvd_left_injective : Function.Injective ((· ∣ ·) : ℕ → ℕ → Prop) := fun _ _ h =>
  dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)
#align nat.dvd_left_injective Nat.dvd_left_injective

theorem div_lt_div_of_lt_of_dvd {a b d : ℕ} (hdb : d ∣ b) (h : a < b) : a / d < b / d := by
  rw [Nat.lt_div_iff_mul_lt hdb]
  -- ⊢ d * (a / d) < b
  exact lt_of_le_of_lt (mul_div_le a d) h
  -- 🎉 no goals
#align nat.div_lt_div_of_lt_of_dvd Nat.div_lt_div_of_lt_of_dvd

end Nat
