/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes, Daniel Weber
-/
import Mathlib.Algebra.Associated.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.ENat.Basic

/-!
# Multiplicity of a divisor

For a commutative monoid, this file introduces the notion of multiplicity of a divisor and proves
several basic results on it.

## Main definitions

* `emultiplicity a b`: for two elements `a` and `b` of a commutative monoid returns the largest
  number `n` such that `a ^ n ∣ b` or infinity, written `⊤`, if `a ^ n ∣ b` for all natural numbers
  `n`.
* `multiplicity a b`: a `ℕ`-valued version of `multiplicity`, defaulting for `1` instead of `⊤`.
  The reason for using `1` as a default value instead of `0` is to have `multiplicity_eq_zero_iff`.
* `multiplicity.Finite a b`: a predicate denoting that the multiplicity of `a` in `b` is finite.
-/


variable {α β : Type*}

open Nat

/-- `multiplicity.Finite a b` indicates that the multiplicity of `a` in `b` is finite. -/
abbrev multiplicity.Finite [Monoid α] (a b : α) : Prop :=
  ∃ n : ℕ, ¬a ^ (n + 1) ∣ b

open scoped Classical in
/-- `emultiplicity a b` returns the largest natural number `n` such that
  `a ^ n ∣ b`, as an `ℕ∞`. If `∀ n, a ^ n ∣ b` then it returns `⊤`. -/
noncomputable def emultiplicity [Monoid α] (a b : α) : ℕ∞ :=
  if h : multiplicity.Finite a b then Nat.find h else ⊤

/-- A `ℕ`-valued version of `emultiplicity`, returning `1` instead of `⊤`. -/
noncomputable def multiplicity [Monoid α] (a b : α) : ℕ :=
  (emultiplicity a b).untop' 1

open multiplicity

section Monoid

variable [Monoid α] [Monoid β] {a b : α}

@[simp]
theorem emultiplicity_eq_top :
    emultiplicity a b = ⊤ ↔ ¬Finite a b := by
  simp [emultiplicity]

theorem emultiplicity_lt_top {a b : α} : emultiplicity a b < ⊤ ↔ Finite a b := by
  simp [lt_top_iff_ne_top, emultiplicity_eq_top]

theorem finite_iff_emultiplicity_ne_top :
    Finite a b ↔ emultiplicity a b ≠ ⊤ := by simp

alias ⟨Finite.emultiplicity_ne_top, _⟩ := finite_iff_emultiplicity_ne_top

theorem finite_of_emultiplicity_eq_natCast {n : ℕ} (h : emultiplicity a b = n) :
    Finite a b := by
  by_contra! nh
  rw [← emultiplicity_eq_top, h] at nh
  trivial

theorem multiplicity_eq_of_emultiplicity_eq_some {n : ℕ} (h : emultiplicity a b = n) :
    multiplicity a b = n := by
  simp [multiplicity, h]
  rfl

theorem emultiplicity_ne_of_multiplicity_ne {n : ℕ} :
    multiplicity a b ≠ n → emultiplicity a b ≠ n :=
  mt multiplicity_eq_of_emultiplicity_eq_some

theorem multiplicity.Finite.emultiplicity_eq_multiplicity (h : Finite a b) :
    emultiplicity a b = multiplicity a b := by
  cases hm : emultiplicity a b
  · simp [h] at hm
  rw [multiplicity_eq_of_emultiplicity_eq_some hm]

theorem multiplicity.Finite.emultiplicity_eq_iff_multiplicity_eq {n : ℕ} (h : Finite a b) :
    emultiplicity a b = n ↔ multiplicity a b = n := by
  simp [h.emultiplicity_eq_multiplicity]

theorem emultiplicity_eq_iff_multiplicity_eq_of_ne_one {n : ℕ} (h : n ≠ 1) :
    emultiplicity a b = n ↔ multiplicity a b = n := by
  constructor
  · exact multiplicity_eq_of_emultiplicity_eq_some
  · intro h₂
    simpa [multiplicity, WithTop.untop'_eq_iff, h] using h₂

theorem emultiplicity_eq_zero_iff_multiplicity_eq_zero :
    emultiplicity a b = 0 ↔ multiplicity a b = 0 :=
  emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one

@[simp]
theorem multiplicity_eq_one_of_not_finite (h : ¬Finite a b) :
    multiplicity a b = 1 := by
  simp [multiplicity, emultiplicity_eq_top.2 h]

@[simp]
theorem multiplicity_le_emultiplicity :
    multiplicity a b ≤ emultiplicity a b := by
  by_cases hf : Finite a b
  · simp [hf.emultiplicity_eq_multiplicity]
  · simp [hf, emultiplicity_eq_top.2]

@[simp]
theorem multiplicity_eq_of_emultiplicity_eq {c d : β}
    (h : emultiplicity a b = emultiplicity c d) : multiplicity a b = multiplicity c d := by
  unfold multiplicity
  rw [h]

theorem multiplicity_le_of_emultiplicity_le {n : ℕ} (h : emultiplicity a b ≤ n) :
    multiplicity a b ≤ n := by
  exact_mod_cast multiplicity_le_emultiplicity.trans h

theorem multiplicity.Finite.emultiplicity_le_of_multiplicity_le (hfin : Finite a b)
    {n : ℕ} (h : multiplicity a b ≤ n) : emultiplicity a b ≤ n := by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast

theorem le_emultiplicity_of_le_multiplicity {n : ℕ} (h : n ≤ multiplicity a b) :
    n ≤ emultiplicity a b := by
  exact_mod_cast (WithTop.coe_mono h).trans multiplicity_le_emultiplicity

theorem multiplicity.Finite.le_multiplicity_of_le_emultiplicity (hfin : Finite a b)
    {n : ℕ} (h : n ≤ emultiplicity a b) : n ≤ multiplicity a b := by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast

theorem multiplicity_lt_of_emultiplicity_lt {n : ℕ} (h : emultiplicity a b < n) :
    multiplicity a b < n := by
  exact_mod_cast multiplicity_le_emultiplicity.trans_lt h

theorem multiplicity.Finite.emultiplicity_lt_of_multiplicity_lt (hfin : Finite a b)
    {n : ℕ} (h : multiplicity a b < n) : emultiplicity a b < n := by
  rw [emultiplicity_eq_multiplicity hfin]
  assumption_mod_cast

theorem lt_emultiplicity_of_lt_multiplicity {n : ℕ} (h : n < multiplicity a b) :
    n < emultiplicity a b := by
  exact_mod_cast (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity

theorem multiplicity.Finite.lt_multiplicity_of_lt_emultiplicity (hfin : Finite a b)
    {n : ℕ} (h : n < emultiplicity a b) : n < multiplicity a b := by
  rw [emultiplicity_eq_multiplicity hfin] at h
  assumption_mod_cast

theorem emultiplicity_pos_iff :
    0 < emultiplicity a b ↔ 0 < multiplicity a b := by
  simp [pos_iff_ne_zero, pos_iff_ne_zero, emultiplicity_eq_zero_iff_multiplicity_eq_zero]

theorem multiplicity.Finite.def : Finite a b ↔ ∃ n : ℕ, ¬a ^ (n + 1) ∣ b :=
  Iff.rfl

theorem multiplicity.Finite.not_dvd_of_one_right : Finite a 1 → ¬a ∣ 1 := fun ⟨n, hn⟩ ⟨d, hd⟩ =>
  hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩

@[norm_cast]
theorem Int.natCast_emultiplicity (a b : ℕ) :
    emultiplicity (a : ℤ) (b : ℤ) = emultiplicity a b := by
  unfold emultiplicity multiplicity.Finite
  congr! <;> norm_cast

@[norm_cast]
theorem Int.natCast_multiplicity (a b : ℕ) : multiplicity (a : ℤ) (b : ℤ) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (natCast_emultiplicity a b)

@[deprecated (since := "2024-04-05")] alias Int.coe_nat_multiplicity := Int.natCast_multiplicity

theorem multiplicity.Finite.not_iff_forall : ¬Finite a b ↔ ∀ n : ℕ, a ^ n ∣ b :=
  ⟨fun h n =>
    Nat.casesOn n
      (by
        rw [_root_.pow_zero]
        exact one_dvd _)
      (by simpa [multiplicity.Finite, Classical.not_not] using h),
    by simp [multiplicity.Finite, multiplicity, Classical.not_not]; tauto⟩

theorem multiplicity.Finite.not_unit (h : Finite a b) : ¬IsUnit a :=
  let ⟨n, hn⟩ := h
  hn ∘ IsUnit.dvd ∘ IsUnit.pow (n + 1)

theorem multiplicity.Finite.mul_left {c : α} : Finite a (b * c) → Finite a b := fun ⟨n, hn⟩ =>
  ⟨n, fun h => hn (h.trans (dvd_mul_right _ _))⟩

theorem pow_dvd_of_le_emultiplicity {k : ℕ} (hk : k ≤ emultiplicity a b) :
    a ^ k ∣ b := by classical
  cases k
  · simp
  unfold emultiplicity at hk
  split at hk
  · norm_cast at hk
    simpa using (Nat.find_min _ (lt_of_succ_le hk))
  · apply Finite.not_iff_forall.mp ‹_›

theorem pow_dvd_of_le_multiplicity {k : ℕ} (hk : k ≤ multiplicity a b) :
    a ^ k ∣ b := pow_dvd_of_le_emultiplicity (le_emultiplicity_of_le_multiplicity hk)

@[simp]
theorem pow_multiplicity_dvd (a b : α) : a ^ (multiplicity a b) ∣ b :=
  pow_dvd_of_le_multiplicity le_rfl

theorem not_pow_dvd_of_emultiplicity_lt {m : ℕ} (hm : emultiplicity a b < m) :
    ¬a ^ m ∣ b := fun nh => by
  unfold emultiplicity at hm
  split at hm
  · simp only [cast_lt, find_lt_iff] at hm
    obtain ⟨n, hn1, hn2⟩ := hm
    exact hn2 ((pow_dvd_pow _ hn1).trans nh)
  · simp at hm

theorem multiplicity.Finite.not_pow_dvd_of_multiplicity_lt (hf : Finite a b) {m : ℕ}
    (hm : multiplicity a b < m) : ¬a ^ m ∣ b := by
  apply not_pow_dvd_of_emultiplicity_lt
  rw [hf.emultiplicity_eq_multiplicity]
  norm_cast

theorem multiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < multiplicity a b := by
  refine zero_lt_iff.2 fun h => ?_
  simpa [hdiv] using Finite.not_pow_dvd_of_multiplicity_lt
    (by by_contra! nh; simp [nh] at h) (lt_one_iff.mpr h)

theorem emultiplicity_pos_of_dvd (hdiv : a ∣ b) : 0 < emultiplicity a b :=
  lt_emultiplicity_of_lt_multiplicity (multiplicity_pos_of_dvd hdiv)

theorem emultiplicity_eq_of_dvd_of_not_dvd {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    emultiplicity a b = k := by classical
  have : Finite a b := ⟨k, hsucc⟩
  simp only [emultiplicity, this, ↓reduceDIte, Nat.cast_inj, find_eq_iff, hsucc, not_false_eq_true,
    Decidable.not_not, true_and]
  exact fun n hn ↦ (pow_dvd_pow _ hn).trans hk

theorem multiplicity_eq_of_dvd_of_not_dvd {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    multiplicity a b = k :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_eq_of_dvd_of_not_dvd hk hsucc)

theorem le_emultiplicity_of_pow_dvd {k : ℕ} (hk : a ^ k ∣ b) :
    k ≤ emultiplicity a b :=
  le_of_not_gt fun hk' => not_pow_dvd_of_emultiplicity_lt hk' hk

theorem multiplicity.Finite.le_multiplicity_of_pow_dvd (hf : Finite a b) {k : ℕ} (hk : a ^ k ∣ b) :
    k ≤ multiplicity a b :=
  hf.le_multiplicity_of_le_emultiplicity (le_emultiplicity_of_pow_dvd hk)

theorem pow_dvd_iff_le_emultiplicity {k : ℕ} :
    a ^ k ∣ b ↔ k ≤ emultiplicity a b :=
  ⟨le_emultiplicity_of_pow_dvd, pow_dvd_of_le_emultiplicity⟩

theorem multiplicity.Finite.pow_dvd_iff_le_multiplicity (hf : Finite a b) {k : ℕ} :
    a ^ k ∣ b ↔ k ≤ multiplicity a b := by
  exact_mod_cast hf.emultiplicity_eq_multiplicity ▸ pow_dvd_iff_le_emultiplicity

theorem emultiplicity_lt_iff_not_dvd {k : ℕ} :
    emultiplicity a b < k ↔ ¬a ^ k ∣ b := by rw [pow_dvd_iff_le_emultiplicity, not_le]

theorem multiplicity.Finite.multiplicity_lt_iff_not_dvd {k : ℕ} (hf : Finite a b) :
    multiplicity a b < k ↔ ¬a ^ k ∣ b := by rw [hf.pow_dvd_iff_le_multiplicity, not_le]

theorem emultiplicity_eq_coe {n : ℕ} :
    emultiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b := by
  constructor
  · intro h
    constructor
    · apply pow_dvd_of_le_emultiplicity
      simp [h]
    · apply not_pow_dvd_of_emultiplicity_lt
      rw [h]
      norm_cast
      simp
  · rw [and_imp]
    apply emultiplicity_eq_of_dvd_of_not_dvd

theorem multiplicity.Finite.multiplicity_eq_iff (hf : Finite a b) {n : ℕ} :
    multiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b := by
  simp [← emultiplicity_eq_coe, hf.emultiplicity_eq_multiplicity]

@[simp]
theorem multiplicity.Finite.not_of_isUnit_left (b : α) (ha : IsUnit a) : ¬Finite a b :=
  (·.not_unit ha)

theorem multiplicity.Finite.not_of_one_left (b : α) : ¬ Finite 1 b := by simp

@[simp]
theorem emultiplicity_one_left (b : α) : emultiplicity 1 b = ⊤ :=
  emultiplicity_eq_top.2 (Finite.not_of_one_left _)

@[simp]
theorem multiplicity.Finite.one_right (ha : Finite a 1) : multiplicity a 1 = 0 := by
  simp [ha.multiplicity_eq_iff, ha.not_dvd_of_one_right]

theorem multiplicity.Finite.not_of_unit_left (a : α) (u : αˣ) : ¬ Finite (u : α) a :=
  Finite.not_of_isUnit_left a u.isUnit

theorem emultiplicity_eq_zero :
    emultiplicity a b = 0 ↔ ¬a ∣ b := by
  by_cases hf : Finite a b
  · rw [← ENat.coe_zero, emultiplicity_eq_coe]
    simp
  · simpa [emultiplicity_eq_top.2 hf] using Finite.not_iff_forall.1 hf 1

theorem multiplicity_eq_zero :
    multiplicity a b = 0 ↔ ¬a ∣ b :=
  (emultiplicity_eq_iff_multiplicity_eq_of_ne_one zero_ne_one).symm.trans emultiplicity_eq_zero

theorem emultiplicity_ne_zero :
    emultiplicity a b ≠ 0 ↔ a ∣ b := by
  simp [emultiplicity_eq_zero]

theorem multiplicity_ne_zero :
    multiplicity a b ≠ 0 ↔ a ∣ b := by
  simp [multiplicity_eq_zero]

theorem multiplicity.Finite.exists_eq_pow_mul_and_not_dvd (hfin : Finite a b) :
    ∃ c : α, b = a ^ multiplicity a b * c ∧ ¬a ∣ c := by
  obtain ⟨c, hc⟩ := pow_multiplicity_dvd a b
  refine ⟨c, hc, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk, ← mul_assoc, ← _root_.pow_succ] at hc
  have h₁ : a ^ (multiplicity a b + 1) ∣ b := ⟨k, hc⟩
  exact (hfin.multiplicity_eq_iff.1 (by simp)).2 h₁

theorem emultiplicity_le_emultiplicity_iff {c d : β} :
    emultiplicity a b ≤ emultiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d := by classical
  constructor
  · exact fun h n hab ↦ pow_dvd_of_le_emultiplicity (le_trans (le_emultiplicity_of_pow_dvd hab) h)
  · intro h
    unfold emultiplicity
    -- aesop? says
    split
    next h_1 =>
      obtain ⟨w, h_1⟩ := h_1
      split
      next h_2 =>
        simp_all only [cast_le, le_find_iff, lt_find_iff, Decidable.not_not, le_refl,
          not_true_eq_false, not_false_eq_true, implies_true]
      next h_2 => simp_all only [not_exists, Decidable.not_not, le_top]
    next h_1 =>
      simp_all only [not_exists, Decidable.not_not, not_true_eq_false, top_le_iff,
        dite_eq_right_iff, ENat.coe_ne_top, imp_false, not_false_eq_true, implies_true]

theorem multiplicity.Finite.multiplicity_le_multiplicity_iff {c d : β} (hab : Finite a b)
    (hcd : Finite c d) : multiplicity a b ≤ multiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d := by
  rw [← WithTop.coe_le_coe, ENat.some_eq_coe, ← hab.emultiplicity_eq_multiplicity,
    ← hcd.emultiplicity_eq_multiplicity]
  apply emultiplicity_le_emultiplicity_iff

theorem emultiplicity_eq_emultiplicity_iff {c d : β} :
    emultiplicity a b = emultiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b ↔ c ^ n ∣ d :=
  ⟨fun h n =>
    ⟨emultiplicity_le_emultiplicity_iff.1 h.le n, emultiplicity_le_emultiplicity_iff.1 h.ge n⟩,
    fun h => le_antisymm (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mp)
      (emultiplicity_le_emultiplicity_iff.2 fun n => (h n).mpr)⟩

theorem le_emultiplicity_map {F : Type*} [FunLike F α β] [MonoidHomClass F α β]
    (f : F) {a b : α} :
    emultiplicity a b ≤ emultiplicity (f a) (f b) :=
  emultiplicity_le_emultiplicity_iff.2 fun n ↦ by rw [← map_pow]; exact map_dvd f

theorem emultiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
    (f : F) {a b : α} : emultiplicity (f a) (f b) = emultiplicity a b := by
  simp [emultiplicity_eq_emultiplicity_iff, ← map_pow, map_dvd_iff]

theorem multiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
    (f : F) {a b : α} : multiplicity (f a) (f b) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_map_eq f)

theorem emultiplicity_le_emultiplicity_of_dvd_right {a b c : α} (h : b ∣ c) :
    emultiplicity a b ≤ emultiplicity a c :=
  emultiplicity_le_emultiplicity_iff.2 fun _ hb => hb.trans h

theorem emultiplicity_eq_of_associated_right {a b c : α} (h : Associated b c) :
    emultiplicity a b = emultiplicity a c :=
  le_antisymm (emultiplicity_le_emultiplicity_of_dvd_right h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_right h.symm.dvd)

theorem multiplicity_eq_of_associated_right {a b c : α} (h : Associated b c) :
    multiplicity a b = multiplicity a c :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_right h)

theorem dvd_of_emultiplicity_pos {a b : α} (h : 0 < emultiplicity a b) : a ∣ b :=
  pow_one a ▸ pow_dvd_of_le_emultiplicity (Order.add_one_le_of_lt h)

theorem dvd_of_multiplicity_pos {a b : α} (h : 0 < multiplicity a b) : a ∣ b :=
  dvd_of_emultiplicity_pos (lt_emultiplicity_of_lt_multiplicity h)

theorem dvd_iff_multiplicity_pos {a b : α} : 0 < multiplicity a b ↔ a ∣ b :=
  ⟨dvd_of_multiplicity_pos, fun hdvd => Nat.pos_of_ne_zero (by simpa [multiplicity_eq_zero])⟩

theorem dvd_iff_emultiplicity_pos {a b : α} : 0 < emultiplicity a b ↔ a ∣ b :=
  emultiplicity_pos_iff.trans dvd_iff_multiplicity_pos

theorem Nat.multiplicity_finite_iff {a b : ℕ} : Finite a b ↔ a ≠ 1 ∧ 0 < b := by
  rw [← not_iff_not, Finite.not_iff_forall, not_and_or, Ne, Classical.not_not, not_lt,
    Nat.le_zero]
  exact
    ⟨fun h =>
      or_iff_not_imp_right.2 fun hb =>
        have ha : a ≠ 0 := fun ha => hb <| zero_dvd_iff.mp <| by rw [ha] at h; exact h 1
        Classical.by_contradiction fun ha1 : a ≠ 1 =>
          have ha_gt_one : 1 < a :=
            lt_of_not_ge fun _ =>
              match a with
              | 0 => ha rfl
              | 1 => ha1 rfl
              | b+2 => by omega
          not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero hb) (h b)) (lt_pow_self ha_gt_one b),
      fun h => by cases h <;> simp [*]⟩

alias ⟨_, Dvd.multiplicity_pos⟩ := dvd_iff_multiplicity_pos

end Monoid

section CommMonoid

variable [CommMonoid α]

theorem multiplicity.Finite.mul_right {a b c : α} (hf : Finite a (b * c)) : Finite a c :=
  (mul_comm b c ▸ hf).mul_left

theorem emultiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a)
    (hb : IsUnit b) : emultiplicity a b = 0 :=
  emultiplicity_eq_zero.mpr fun h ↦ ha (isUnit_of_dvd_unit h hb)

theorem multiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a)
    (hb : IsUnit b) : multiplicity a b = 0 :=
  multiplicity_eq_zero.mpr fun h ↦ ha (isUnit_of_dvd_unit h hb)

theorem emultiplicity_of_one_right {a : α} (ha : ¬IsUnit a) : emultiplicity a 1 = 0 :=
  emultiplicity_of_isUnit_right ha isUnit_one

theorem multiplicity_of_one_right {a : α} (ha : ¬IsUnit a) : multiplicity a 1 = 0 :=
  multiplicity_of_isUnit_right ha isUnit_one

theorem emultiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : emultiplicity a u = 0 :=
  emultiplicity_of_isUnit_right ha u.isUnit

theorem multiplicity_of_unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : multiplicity a u = 0 :=
  multiplicity_of_isUnit_right ha u.isUnit

theorem emultiplicity_le_emultiplicity_of_dvd_left {a b c : α} (hdvd : a ∣ b) :
    emultiplicity b c ≤ emultiplicity a c :=
  emultiplicity_le_emultiplicity_iff.2 fun n h => (pow_dvd_pow_of_dvd hdvd n).trans h

theorem emultiplicity_eq_of_associated_left {a b c : α} (h : Associated a b) :
    emultiplicity b c = emultiplicity a c :=
  le_antisymm (emultiplicity_le_emultiplicity_of_dvd_left h.dvd)
    (emultiplicity_le_emultiplicity_of_dvd_left h.symm.dvd)

theorem multiplicity_eq_of_associated_left {a b c : α} (h : Associated a b) :
    multiplicity b c = multiplicity a c :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_eq_of_associated_left h)

theorem emultiplicity_mk_eq_emultiplicity {a b : α} :
    emultiplicity (Associates.mk a) (Associates.mk b) = emultiplicity a b := by
  simp [emultiplicity_eq_emultiplicity_iff, ← Associates.mk_pow, Associates.mk_dvd_mk]

end CommMonoid

section MonoidWithZero

variable [MonoidWithZero α]

theorem multiplicity.Finite.ne_zero {a b : α} (h : Finite a b) : b ≠ 0 :=
  let ⟨n, hn⟩ := h
  fun hb => by simp [hb] at hn

@[simp]
theorem emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤ :=
  emultiplicity_eq_top.2 (fun v ↦ v.ne_zero rfl)

@[simp]
theorem emultiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a ≠ 0) : emultiplicity 0 a = 0 :=
  emultiplicity_eq_zero.2 <| mt zero_dvd_iff.1 ha

@[simp]
theorem multiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a ≠ 0) : multiplicity 0 a = 0 :=
  multiplicity_eq_zero.2 <| mt zero_dvd_iff.1 ha

end MonoidWithZero

section Semiring

variable [Semiring α]

theorem multiplicity.Finite.or_of_add {p a b : α} (hf : Finite p (a + b)) :
    Finite p a ∨ Finite p b := by
  by_contra! nh
  obtain ⟨c, hc⟩ := hf
  simp_all [dvd_add]

theorem min_le_emultiplicity_add {p a b : α} :
    min (emultiplicity p a) (emultiplicity p b) ≤ emultiplicity p (a + b) := by
  cases hm : min (emultiplicity p a) (emultiplicity p b)
  · simp only [top_le_iff, min_eq_top, emultiplicity_eq_top] at hm ⊢
    contrapose hm
    simp only [not_and_or, not_not] at hm ⊢
    exact hm.or_of_add
  · apply le_emultiplicity_of_pow_dvd
    simp [dvd_add, pow_dvd_of_le_emultiplicity, ← hm]

end Semiring

section Ring

variable [Ring α]

@[simp]
theorem multiplicity.Finite.neg_iff {a b : α} : Finite a (-b) ↔ Finite a b := by
  unfold Finite
  congr! 3
  simp only [dvd_neg]

alias ⟨_, multiplicity.Finite.neg⟩ := Finite.neg_iff

@[simp]
theorem emultiplicity_neg (a b : α) : emultiplicity a (-b) = emultiplicity a b := by
  rw [emultiplicity_eq_emultiplicity_iff]
  simp

@[simp]
theorem multiplicity_neg (a b : α) : multiplicity a (-b) = multiplicity a b :=
  multiplicity_eq_of_emultiplicity_eq (emultiplicity_neg a b)

theorem Int.emultiplicity_natAbs (a : ℕ) (b : ℤ) :
    emultiplicity a b.natAbs = emultiplicity (a : ℤ) b := by
  cases' Int.natAbs_eq b with h h <;> conv_rhs => rw [h]
  · rw [Int.natCast_emultiplicity]
  · rw [emultiplicity_neg, Int.natCast_emultiplicity]

theorem Int.multiplicity_natAbs (a : ℕ) (b : ℤ) :
    multiplicity a b.natAbs = multiplicity (a : ℤ) b :=
  multiplicity_eq_of_emultiplicity_eq (Int.emultiplicity_natAbs a b)

theorem emultiplicity_add_of_gt {p a b : α} (h : emultiplicity p b < emultiplicity p a) :
    emultiplicity p (a + b) = emultiplicity p b := by
  have : Finite p b := finite_iff_emultiplicity_ne_top.2 (by simp [·] at h)
  rw [this.emultiplicity_eq_multiplicity] at *
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · apply dvd_add
    · apply pow_dvd_of_le_emultiplicity
      exact h.le
    · simp
  · rw [dvd_add_right]
    · apply this.not_pow_dvd_of_multiplicity_lt
      simp
    apply pow_dvd_of_le_emultiplicity
    exact Order.add_one_le_of_lt h

theorem multiplicity.Finite.multiplicity_add_of_gt {p a b : α} (hf : Finite p b)
    (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a + b) = multiplicity p b :=
  multiplicity_eq_of_emultiplicity_eq <| emultiplicity_add_of_gt (hf.emultiplicity_eq_multiplicity ▸
      (WithTop.coe_strictMono h).trans_le multiplicity_le_emultiplicity)

theorem emultiplicity_sub_of_gt {p a b : α} (h : emultiplicity p b < emultiplicity p a) :
    emultiplicity p (a - b) = emultiplicity p b := by
  rw [sub_eq_add_neg, emultiplicity_add_of_gt] <;> rw [emultiplicity_neg]; assumption

theorem multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a)
    (hfin : Finite p b) : multiplicity p (a - b) = multiplicity p b := by
  rw [sub_eq_add_neg, hfin.neg.multiplicity_add_of_gt] <;> rw [multiplicity_neg]; assumption

theorem emultiplicity_add_eq_min {p a b : α}
    (h : emultiplicity p a ≠ emultiplicity p b) :
    emultiplicity p (a + b) = min (emultiplicity p a) (emultiplicity p b) := by
  rcases lt_trichotomy (emultiplicity p a) (emultiplicity p b) with (hab | _ | hab)
  · rw [add_comm, emultiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [emultiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

theorem multiplicity_add_eq_min {p a b : α} (ha : Finite p a) (hb : Finite p b)
    (h : multiplicity p a ≠ multiplicity p b) :
    multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) := by
  rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with (hab | _ | hab)
  · rw [add_comm, ha.multiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [hb.multiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab

end Ring

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

/- Porting note:
Pulled a b intro parameters since Lean parses that more easily -/
theorem multiplicity.finite_mul_aux {p : α} (hp : Prime p) {a b : α} :
    ∀ {n m : ℕ}, ¬p ^ (n + 1) ∣ a → ¬p ^ (m + 1) ∣ b → ¬p ^ (n + m + 1) ∣ a * b
  | n, m => fun ha hb ⟨s, hs⟩ =>
    have : p ∣ a * b := ⟨p ^ (n + m) * s, by simp [hs, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩
    (hp.2.2 a b this).elim
      (fun ⟨x, hx⟩ =>
        have hn0 : 0 < n :=
          Nat.pos_of_ne_zero fun hn0 => by simp [hx, hn0] at ha
        have hpx : ¬p ^ (n - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          ha (hx.symm ▸ ⟨y, mul_right_cancel₀ hp.1 <| by
            rw [tsub_add_cancel_of_le (succ_le_of_lt hn0)] at hy
            simp [hy, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩)
        have : 1 ≤ n + m := le_trans hn0 (Nat.le_add_right n m)
        finite_mul_aux hp hpx hb
          ⟨s, mul_right_cancel₀ hp.1 (by
                rw [tsub_add_eq_add_tsub (succ_le_of_lt hn0), tsub_add_cancel_of_le this]
                simp_all [mul_comm, mul_assoc, mul_left_comm, pow_add])⟩)
      fun ⟨x, hx⟩ =>
        have hm0 : 0 < m :=
          Nat.pos_of_ne_zero fun hm0 => by simp [hx, hm0] at hb
        have hpx : ¬p ^ (m - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          hb
            (hx.symm ▸
              ⟨y,
                mul_right_cancel₀ hp.1 <| by
                  rw [tsub_add_cancel_of_le (succ_le_of_lt hm0)] at hy
                  simp [hy, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩)
        finite_mul_aux hp ha hpx
        ⟨s, mul_right_cancel₀ hp.1 (by
              rw [add_assoc, tsub_add_cancel_of_le (succ_le_of_lt hm0)]
              simp_all [mul_comm, mul_assoc, mul_left_comm, pow_add])⟩

theorem Prime.multiplicity_finite_mul {p a b : α} (hp : Prime p) :
    Finite p a → Finite p b → Finite p (a * b) :=
  fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, finite_mul_aux hp hn hm⟩

theorem multiplicity.Finite.mul_iff {p a b : α} (hp : Prime p) :
    Finite p (a * b) ↔ Finite p a ∧ Finite p b :=
  ⟨fun h => ⟨h.mul_left, h.mul_right⟩, fun h =>
    hp.multiplicity_finite_mul h.1 h.2⟩

theorem multiplicity.Finite.pow {p a : α} (hp : Prime p)
    (hfin : Finite p a) {k : ℕ} : Finite p (a ^ k) :=
  match k, hfin with
  | 0, _ => ⟨0, by simp [mt isUnit_iff_dvd_one.2 hp.2.1]⟩
  | k + 1, ha => by rw [_root_.pow_succ']; exact hp.multiplicity_finite_mul ha (ha.pow hp)

@[simp]
theorem multiplicity_self {a : α} : multiplicity a a = 1 := by
  by_cases ha : Finite a a
  · rw [ha.multiplicity_eq_iff]
    simp only [pow_one, dvd_refl, reduceAdd, true_and]
    rintro ⟨v, hv⟩
    nth_rw 1 [← mul_one a] at hv
    simp only [sq, mul_assoc, mul_eq_mul_left_iff] at hv
    obtain hv | rfl := hv
    · have : IsUnit a := isUnit_of_mul_eq_one a v hv.symm
      simpa [this] using ha.not_unit
    · simpa using ha.ne_zero
  · simp [ha]

@[simp]
theorem multiplicity.Finite.emultiplicity_self {a : α} (hfin : Finite a a) :
    emultiplicity a a = 1 := by
  simp [hfin.emultiplicity_eq_multiplicity]

theorem multiplicity_mul {p a b : α} (hp : Prime p) (hfin : Finite p (a * b)) :
    multiplicity p (a * b) = multiplicity p a + multiplicity p b := by
  have hdiva : p ^ multiplicity p a ∣ a := pow_multiplicity_dvd ..
  have hdivb : p ^ multiplicity p b ∣ b := pow_multiplicity_dvd ..
  have hdiv : p ^ (multiplicity p a + multiplicity p b) ∣ a * b := by
    rw [pow_add]; apply mul_dvd_mul <;> assumption
  have hsucc : ¬p ^ (multiplicity p a + multiplicity p b + 1) ∣ a * b :=
    fun h =>
    not_or_intro (hfin.mul_left.not_pow_dvd_of_multiplicity_lt (lt_succ_self _))
      (hfin.mul_right.not_pow_dvd_of_multiplicity_lt (lt_succ_self _))
      (_root_.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul hp hdiva hdivb h)
  rw [hfin.multiplicity_eq_iff]
  exact ⟨hdiv, hsucc⟩

theorem emultiplicity_mul {p a b : α} (hp : Prime p) :
    emultiplicity p (a * b) = emultiplicity p a + emultiplicity p b := by
  by_cases hfin : Finite p (a * b)
  · rw [hfin.emultiplicity_eq_multiplicity, hfin.mul_left.emultiplicity_eq_multiplicity,
      hfin.mul_right.emultiplicity_eq_multiplicity]
    norm_cast
    exact multiplicity_mul hp hfin
  · rw [emultiplicity_eq_top.2 hfin, eq_comm, WithTop.add_eq_top, emultiplicity_eq_top,
      emultiplicity_eq_top]
    simpa only [Finite.mul_iff hp, not_and_or] using hfin

theorem Finset.emultiplicity_prod {β : Type*} {p : α} (hp : Prime p) (s : Finset β) (f : β → α) :
    emultiplicity p (∏ x ∈ s, f x) = ∑ x ∈ s, emultiplicity p (f x) := by classical
    induction' s using Finset.induction with a s has ih h
    · simp only [Finset.sum_empty, Finset.prod_empty]
      exact emultiplicity_of_one_right hp.not_unit
    · simpa [has, ← ih] using emultiplicity_mul hp

theorem emultiplicity_pow {p a : α} (hp : Prime p) {k : ℕ} :
    emultiplicity p (a ^ k) = k * emultiplicity p a := by
  induction' k with k hk
  · simp [emultiplicity_of_one_right hp.not_unit]
  · simp [pow_succ, emultiplicity_mul hp, hk, add_mul]

protected theorem multiplicity.Finite.multiplicity_pow {p a : α} (hp : Prime p)
    (ha : Finite p a) {k : ℕ} : multiplicity p (a ^ k) = k * multiplicity p a := by
  exact_mod_cast (ha.pow hp).emultiplicity_eq_multiplicity ▸
    ha.emultiplicity_eq_multiplicity ▸ emultiplicity_pow hp

theorem emultiplicity_pow_self {p : α} (h0 : p ≠ 0) (hu : ¬IsUnit p) (n : ℕ) :
    emultiplicity p (p ^ n) = n := by
  apply emultiplicity_eq_of_dvd_of_not_dvd
  · rfl
  · rw [pow_dvd_pow_iff h0 hu]
    apply Nat.not_succ_le_self

theorem multiplicity_pow_self {p : α} (h0 : p ≠ 0) (hu : ¬IsUnit p) (n : ℕ) :
    multiplicity p (p ^ n) = n :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_pow_self h0 hu n)

theorem emultiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : ℕ) :
    emultiplicity p (p ^ n) = n :=
  emultiplicity_pow_self hp.ne_zero hp.not_unit n

theorem multiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : ℕ) :
    multiplicity p (p ^ n) = n :=
  multiplicity_pow_self hp.ne_zero hp.not_unit n

end CancelCommMonoidWithZero

section Nat

open multiplicity

theorem multiplicity_eq_zero_of_coprime {p a b : ℕ} (hp : p ≠ 1)
    (hle : multiplicity p a ≤ multiplicity p b) (hab : Nat.Coprime a b) : multiplicity p a = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro nh
  have da : p ∣ a := by simpa [multiplicity_eq_zero] using nh.ne.symm
  have db : p ∣ b := by simpa [multiplicity_eq_zero] using (nh.trans_le hle).ne.symm
  have := Nat.dvd_gcd da db
  rw [Coprime.gcd_eq_one hab, Nat.dvd_one] at this
  exact hp this

end Nat

theorem Int.multiplicity_finite_iff_natAbs_finite {a b : ℤ} :
    Finite a b ↔ Finite a.natAbs b.natAbs := by
  simp only [Finite.def, ← Int.natAbs_dvd_natAbs, Int.natAbs_pow]

theorem Int.multiplicity_finite_iff {a b : ℤ} : Finite a b ↔ a.natAbs ≠ 1 ∧ b ≠ 0 := by
  rw [multiplicity_finite_iff_natAbs_finite, Nat.multiplicity_finite_iff,
    pos_iff_ne_zero, Int.natAbs_ne_zero]

instance Nat.decidableMultiplicityFinite : DecidableRel fun a b : ℕ => Finite a b := fun _ _ =>
  decidable_of_iff' _ Nat.multiplicity_finite_iff

instance Int.decidableMultiplicityFinite : DecidableRel fun a b : ℤ => Finite a b := fun _ _ =>
  decidable_of_iff' _ Int.multiplicity_finite_iff
