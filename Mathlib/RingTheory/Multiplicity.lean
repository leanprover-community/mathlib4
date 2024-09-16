/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes, Daniel Weber
-/
import Mathlib.Algebra.Associated.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.SMulWithZero
import Mathlib.Tactic.Linarith
import Mathlib.Data.ENat.Basic

/-!
# Multiplicity of a divisor

For a commutative monoid, this file introduces the notion of multiplicity of a divisor and proves
several basic results on it.

## Main definitions

* `multiplicity a b`: for two elements `a` and `b` of a commutative monoid returns the largest
  number `n` such that `a ^ n ∣ b` or infinity, written `⊤`, if `a ^ n ∣ b` for all natural numbers
  `n`.
* `multiplicity.Finite a b`: a predicate denoting that the multiplicity of `a` in `b` is finite.
-/


variable {α β : Type*}

open Nat

/-- `multiplicity.Finite a b` indicates that the multiplicity of `a` in `b` is finite. -/
abbrev multiplicity.Finite [Monoid α] (a b : α) : Prop :=
  ∃ n : ℕ, ¬a ^ (n + 1) ∣ b

open scoped Classical in
/-- `multiplicity a b` returns the largest natural number `n` such that
  `a ^ n ∣ b`, as a `ℕ`. If `∀ n, a ^ n ∣ b`,
  then it returns the junk value of 0. -/
noncomputable def multiplicity [Monoid α] (a b : α) : ℕ :=
  if h : multiplicity.Finite a b then Nat.find h else 1

namespace multiplicity

section Monoid

variable [Monoid α] [Monoid β]

@[simp]
theorem multiplicity_eq_one_of_not_finite {a b : α} (h : ¬Finite a b) :
    multiplicity a b = 1 := by
  simp [multiplicity, h]

theorem finite_def {a b : α} : Finite a b ↔ ∃ n : ℕ, ¬a ^ (n + 1) ∣ b :=
  Iff.rfl

theorem not_dvd_one_of_finite_one_right {a : α} : Finite a 1 → ¬a ∣ 1 := fun ⟨n, hn⟩ ⟨d, hd⟩ =>
  hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩

@[norm_cast]
theorem Int.natCast_multiplicity (a b : ℕ) : multiplicity (a : ℤ) (b : ℤ) = multiplicity a b := by
  unfold multiplicity Finite
  congr! <;> norm_cast

@[deprecated (since := "2024-04-05")] alias Int.coe_nat_multiplicity := Int.natCast_multiplicity

theorem not_finite_iff_forall {a b : α} : ¬Finite a b ↔ ∀ n : ℕ, a ^ n ∣ b :=
  ⟨fun h n =>
    Nat.casesOn n
      (by
        rw [_root_.pow_zero]
        exact one_dvd _)
      (by simpa [Finite, Classical.not_not] using h),
    by simp [Finite, multiplicity, Classical.not_not]; tauto⟩

theorem Finite.not_unit {a b : α} (h : Finite a b) : ¬IsUnit a :=
  let ⟨n, hn⟩ := h
  hn ∘ IsUnit.dvd ∘ IsUnit.pow (n + 1)

theorem finite_of_finite_mul_right {a b c : α} : Finite a (b * c) → Finite a b := fun ⟨n, hn⟩ =>
  ⟨n, fun h => hn (h.trans (dvd_mul_right _ _))⟩

theorem pow_dvd_of_le_multiplicity {a b : α} {k : ℕ} (hk : k ≤ multiplicity a b) :
    a ^ k ∣ b := by classical
  cases k
  · simp
  unfold multiplicity at hk
  split at hk
  · simpa using (Nat.find_min _ (lt_of_succ_le hk))
  · apply not_finite_iff_forall.mp ‹_›

@[simp]
theorem pow_multiplicity_dvd (a b : α) : a ^ (multiplicity a b) ∣ b :=
  pow_dvd_of_le_multiplicity le_rfl

theorem is_greatest {a b : α} {m : ℕ} (hf : Finite a b) (hm : multiplicity a b < m) :
    ¬a ^ m ∣ b := fun nh => by
  simp only [multiplicity, hf, ↓reduceDIte, find_lt_iff] at hm
  obtain ⟨n, hn1, hn2⟩ := hm
  exact hn2 ((pow_dvd_pow _ hn1).trans nh)

theorem pos_of_dvd {a b : α} (hdiv : a ∣ b) :
    0 < multiplicity a b := by
  refine zero_lt_iff.2 fun h => ?_
  simpa [hdiv] using is_greatest (by by_contra! nh; simp [nh, multiplicity] at h) (lt_one_iff.mpr h)

theorem unique {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    multiplicity a b = k := by classical
  have : Finite a b := ⟨k, hsucc⟩
  simp only [multiplicity, this, ↓reduceDIte, find_eq_iff, hsucc, not_false_eq_true,
    Decidable.not_not, true_and]
  exact fun n hn ↦ (pow_dvd_pow _ hn).trans hk

theorem le_multiplicity_of_pow_dvd {a b : α} {k : ℕ} (h : Finite a b) (hk : a ^ k ∣ b) :
    k ≤ multiplicity a b :=
  le_of_not_gt fun hk' => is_greatest h hk' hk

theorem pow_dvd_iff_le_multiplicity_of_finite {a b : α} {k : ℕ} (hf : Finite a b) :
    a ^ k ∣ b ↔ k ≤ multiplicity a b :=
  ⟨le_multiplicity_of_pow_dvd hf, pow_dvd_of_le_multiplicity⟩

theorem pow_dvd_iff_le_multiplicity_or_infinite {a b : α} {k : ℕ} :
    a ^ k ∣ b ↔ (k ≤ multiplicity a b ∨ ¬ Finite a b) :=
  ⟨fun a ↦ or_not_of_imp (le_multiplicity_of_pow_dvd · a),
    fun h ↦ h.elim pow_dvd_of_le_multiplicity (not_finite_iff_forall.mp · _)⟩

theorem multiplicity_lt_iff_not_dvd {a b : α} {k : ℕ} (hf : Finite a b) :
    multiplicity a b < k ↔ ¬a ^ k ∣ b := by rw [pow_dvd_iff_le_multiplicity_of_finite hf, not_le]

theorem eq_iff_of_finite {a b : α} {n : ℕ} (hf : Finite a b) :
    multiplicity a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b := by
  constructor
  · rintro rfl
    simp only [pow_multiplicity_dvd, true_and]
    apply is_greatest hf (by simp)
  · rw [and_imp]
    apply unique

@[simp]
theorem isUnit_left {a : α} (b : α) (ha : IsUnit a) : ¬Finite a b :=
  (·.not_unit ha)

theorem not_finite_one_left (b : α) : ¬ Finite 1 b := by simp

@[simp]
theorem one_left (b : α) : multiplicity 1 b = 1 :=
  multiplicity_eq_one_of_not_finite (not_finite_one_left _)

@[simp]
theorem get_one_right {a : α} (ha : Finite a 1) : multiplicity a 1 = 0 := by
  simp [eq_iff_of_finite ha, not_dvd_one_of_finite_one_right ha]

theorem not_finite_unit_left (a : α) (u : αˣ) : ¬ Finite (u : α) a :=
  isUnit_left a u.isUnit

theorem multiplicity_eq_zero {a b : α} :
    multiplicity a b = 0 ↔ ¬a ∣ b := by
  by_cases hf : Finite a b
  · simp [eq_iff_of_finite hf]
  · simpa [multiplicity_eq_one_of_not_finite hf] using not_finite_iff_forall.1 hf 1

theorem multiplicity_ne_zero {a b : α} :
    multiplicity a b ≠ 0 ↔ a ∣ b := by
  simp [multiplicity_eq_zero]

theorem exists_eq_pow_mul_and_not_dvd {a b : α} (hfin : Finite a b) :
    ∃ c : α, b = a ^ multiplicity a b * c ∧ ¬a ∣ c := by
  obtain ⟨c, hc⟩ := multiplicity.pow_multiplicity_dvd a b
  refine ⟨c, hc, ?_⟩
  rintro ⟨k, hk⟩
  rw [hk, ← mul_assoc, ← _root_.pow_succ] at hc
  have h₁ : a ^ (multiplicity a b + 1) ∣ b := ⟨k, hc⟩
  exact ((multiplicity.eq_iff_of_finite hfin).1 (by simp)).2 h₁

theorem multiplicity_le_multiplicity_iff {a b : α} {c d : β} (ha : Finite a b) (hc : Finite c d) :
    multiplicity a b ≤ multiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d := by classical
  constructor
  · exact fun h n hab ↦ pow_dvd_of_le_multiplicity (le_trans (le_multiplicity_of_pow_dvd ha hab) h)
  · intro h
    simp [multiplicity, ha, hc]
    intro _ hm
    apply h
    apply hm
    rfl

theorem multiplicity_eq_multiplicity_iff {a b : α} {c d : β} (ha : Finite a b) (hc : Finite c d) :
    multiplicity a b = multiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b ↔ c ^ n ∣ d :=
  ⟨fun h n =>
    ⟨(multiplicity_le_multiplicity_iff ha hc).mp h.le n,
        (multiplicity_le_multiplicity_iff hc ha).mp h.ge n⟩,
    fun h =>
    le_antisymm ((multiplicity_le_multiplicity_iff ha hc).mpr fun n => (h n).mp)
      ((multiplicity_le_multiplicity_iff hc ha).mpr fun n => (h n).mpr)⟩

theorem Finite.of_map {F : Type*} [FunLike F α β] [MonoidHomClass F α β]
    {f : F} {a b : α} (hf : Finite (f a) (f b)) : Finite a b :=
  have ⟨c, hc⟩ := hf
  ⟨c, fun h ↦ hc (by simp [← map_pow, map_dvd, h])⟩

theorem le_multiplicity_map {F : Type*} [FunLike F α β] [MonoidHomClass F α β]
    (f : F) {a b : α} (hf : Finite (f a) (f b)) :
    multiplicity a b ≤ multiplicity (f a) (f b) :=
  (multiplicity_le_multiplicity_iff hf.of_map hf).mpr
    fun n ↦ by rw [← map_pow]; exact map_dvd f

@[simp]
theorem Finite.equiv_iff {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
    {f : F} {a b : α} : Finite (f a) (f b) ↔ Finite a b := by
  unfold Finite
  simp [← map_pow, map_dvd_iff f]

alias ⟨_, Finite.map⟩ := Finite.equiv_iff

theorem multiplicity_map_eq {F : Type*} [EquivLike F α β] [MulEquivClass F α β]
    (f : F) {a b : α} : multiplicity (f a) (f b) = multiplicity a b := by
  by_cases hfin : Finite a b
  · rw [multiplicity_eq_multiplicity_iff hfin.map hfin]
    simp [← map_pow, map_dvd_iff]
  · simp [hfin, multiplicity_eq_one_of_not_finite]

theorem Finite.of_dvd_right {a b c : α} (hfin : Finite a c) (h : b ∣ c) : Finite a b :=
  hfin.elim (⟨·, fun nh ↦ · (nh.trans h)⟩)

theorem multiplicity_le_multiplicity_of_dvd_right {a b c : α} (h : b ∣ c) (hfin : Finite a c) :
    multiplicity a b ≤ multiplicity a c :=
  (multiplicity_le_multiplicity_iff (hfin.of_dvd_right h) hfin).2 fun _ hb => hb.trans h

theorem eq_of_associated_right {a b c : α} (h : Associated b c) (hfin : Finite a b) :
    multiplicity a b = multiplicity a c :=
  le_antisymm (multiplicity_le_multiplicity_of_dvd_right h.dvd (hfin.of_dvd_right h.symm.dvd))
    (multiplicity_le_multiplicity_of_dvd_right h.symm.dvd hfin)

theorem dvd_of_multiplicity_pos {a b : α} (h : 0 < multiplicity a b) : a ∣ b := by
  rw [← pow_one a]
  apply pow_dvd_of_le_multiplicity
  omega

theorem dvd_iff_multiplicity_pos {a b : α} : 0 < multiplicity a b ↔ a ∣ b :=
  ⟨dvd_of_multiplicity_pos, fun hdvd => Nat.pos_of_ne_zero (by simpa [multiplicity_eq_zero])⟩

theorem finite_nat_iff {a b : ℕ} : Finite a b ↔ a ≠ 1 ∧ 0 < b := by
  rw [← not_iff_not, not_finite_iff_forall, not_and_or, Ne, Classical.not_not, not_lt,
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

alias ⟨_, _root_.Dvd.multiplicity_pos⟩ := dvd_iff_multiplicity_pos

end Monoid

section CommMonoid

variable [CommMonoid α]

theorem Finite.of_dvd_left {a b c : α} (hfin : Finite a c) (h : a ∣ b) : Finite b c :=
  hfin.elim (⟨·, fun nh ↦ · ((pow_dvd_pow_of_dvd h _).trans nh)⟩)

theorem finite_of_finite_mul_left {a b c : α} : Finite a (b * c) → Finite a c := by
  rw [mul_comm]; exact finite_of_finite_mul_right

theorem isUnit_right {a b : α} (ha : ¬IsUnit a) (hb : IsUnit b) : multiplicity a b = 0 :=
  multiplicity_eq_zero.mpr fun h ↦ ha (isUnit_of_dvd_unit h hb)

theorem one_right {a : α} (ha : ¬IsUnit a) : multiplicity a 1 = 0 :=
  isUnit_right ha isUnit_one

theorem unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : multiplicity a u = 0 :=
  isUnit_right ha u.isUnit

theorem multiplicity_le_multiplicity_of_dvd_left {a b c : α} (hdvd : a ∣ b) (hfin : Finite a c) :
    multiplicity b c ≤ multiplicity a c :=
  (multiplicity_le_multiplicity_iff (hfin.of_dvd_left hdvd) hfin).2
    fun n h => (pow_dvd_pow_of_dvd hdvd n).trans h

theorem eq_of_associated_left {a b c : α} (h : Associated a b) (hfin : Finite a c) :
    multiplicity b c = multiplicity a c :=
  le_antisymm (multiplicity_le_multiplicity_of_dvd_left h.dvd hfin)
    (multiplicity_le_multiplicity_of_dvd_left h.symm.dvd (hfin.of_dvd_left h.dvd))

-- Porting note: this was doing nothing in mathlib3 also
-- alias dvd_iff_multiplicity_pos ↔ _ _root_.has_dvd.dvd.multiplicity_pos

end CommMonoid

section MonoidWithZero

variable [MonoidWithZero α]

theorem Finite.ne_zero {a b : α} (h : Finite a b) : b ≠ 0 :=
  let ⟨n, hn⟩ := h
  fun hb => by simp [hb] at hn

@[simp]
protected theorem zero (a : α) : multiplicity a 0 = 1 :=
  multiplicity_eq_one_of_not_finite fun ⟨_, hk⟩ => hk (dvd_zero _)

@[simp]
theorem multiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a ≠ 0) : multiplicity 0 a = 0 :=
  multiplicity.multiplicity_eq_zero.2 <| mt zero_dvd_iff.1 ha

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero α]

theorem multiplicity_mk_eq_multiplicity {a b : α} :
    multiplicity (Associates.mk a) (Associates.mk b) = multiplicity a b := by
  by_cases h : Finite a b
  · apply unique <;> rw [← Associates.mk_pow, Associates.mk_dvd_mk]
    · exact pow_multiplicity_dvd a b
    · apply is_greatest h
      exact lt_add_one (multiplicity a b)
  · rw [multiplicity_eq_one_of_not_finite h, multiplicity_eq_one_of_not_finite]
    refine
      not_finite_iff_forall.mpr fun n => by
        rw [← Associates.mk_pow, Associates.mk_dvd_mk]
        exact not_finite_iff_forall.mp h n

end CommMonoidWithZero

section Semiring

variable [Semiring α]

theorem Finite.or_of_add {p a b : α} (hf : Finite p (a + b)) :
    Finite p a ∨ Finite p b := by
  by_contra! nh
  obtain ⟨c, hc⟩ := hf
  simp_all [dvd_add]


theorem min_le_multiplicity_add {p a b : α} (hf : Finite p (a + b)) :
    min (multiplicity p a) (multiplicity p b) ≤ multiplicity p (a + b) := by
  apply le_multiplicity_of_pow_dvd hf
  simp [dvd_add, pow_dvd_of_le_multiplicity]

end Semiring

section Ring

variable [Ring α]

@[simp]
theorem Finite.neg_iff {a b : α} : Finite a (-b) ↔ Finite a b := by
  unfold Finite
  congr! 3
  simp only [dvd_neg]

alias ⟨_, Finite.neg⟩ := Finite.neg_iff

@[simp]
protected theorem neg (a b : α) : multiplicity a (-b) = multiplicity a b := by
  by_cases hfin : Finite a b
  · apply unique
    · simp
    · simp only [dvd_neg]
      apply is_greatest hfin
      omega
  · simp [hfin]

theorem Int.natAbs (a : ℕ) (b : ℤ) : multiplicity a b.natAbs = multiplicity (a : ℤ) b := by
  cases' Int.natAbs_eq b with h h <;> conv_rhs => rw [h]
  · rw [Int.natCast_multiplicity]
  · rw [multiplicity.neg, Int.natCast_multiplicity]

theorem multiplicity_add_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a)
    (hfin : Finite p b) : multiplicity p (a + b) = multiplicity p b := by
  apply unique
  · apply dvd_add
    · apply pow_dvd_of_le_multiplicity
      exact h.le
    · simp
  · rw [dvd_add_right]
    · apply is_greatest hfin (by simp)
    apply pow_dvd_of_le_multiplicity
    omega

theorem multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a)
    (hfin : Finite p b) : multiplicity p (a - b) = multiplicity p b := by
  rw [sub_eq_add_neg, multiplicity_add_of_gt _ hfin.neg] <;> rw [multiplicity.neg]; assumption

theorem multiplicity_add_eq_min {p a b : α} (ha : Finite p a) (hb : Finite p b)
    (h : multiplicity p a ≠ multiplicity p b) :
    multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) := by
  rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with (hab | _ | hab)
  · rw [add_comm, multiplicity_add_of_gt hab ha, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [multiplicity_add_of_gt hab hb, min_eq_right]
    exact le_of_lt hab

end Ring

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

/- Porting note:
Pulled a b intro parameters since Lean parses that more easily -/
theorem finite_mul_aux {p : α} (hp : Prime p) {a b : α} :
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

theorem finite_mul {p a b : α} (hp : Prime p) : Finite p a → Finite p b → Finite p (a * b) :=
  fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, finite_mul_aux hp hn hm⟩

theorem finite_mul_iff {p a b : α} (hp : Prime p) : Finite p (a * b) ↔ Finite p a ∧ Finite p b :=
  ⟨fun h => ⟨finite_of_finite_mul_right h, finite_of_finite_mul_left h⟩, fun h =>
    finite_mul hp h.1 h.2⟩

alias ⟨Finite.mul, _⟩ := finite_mul_iff

theorem Finite.mul_left {p a b : α} (hp : Prime p) (hfin : Finite p (a * b)) : Finite p a :=
  (hfin.mul hp).1

theorem Finite.mul_right {p a b : α} (hp : Prime p) (hfin : Finite p (a * b)) : Finite p b :=
  (hfin.mul hp).2

theorem finite_pow {p a : α} (hp : Prime p) : ∀ {k : ℕ} (_ : Finite p a), Finite p (a ^ k)
  | 0, _ => ⟨0, by simp [mt isUnit_iff_dvd_one.2 hp.2.1]⟩
  | k + 1, ha => by rw [_root_.pow_succ']; exact finite_mul hp ha (finite_pow hp ha)

@[simp]
theorem multiplicity_self {a : α} : multiplicity a a = 1 := by
  by_cases ha : Finite a a
  · rw [eq_iff_of_finite ha]
    simp only [pow_one, dvd_refl, reduceAdd, true_and]
    rintro ⟨v, hv⟩
    nth_rw 1 [← mul_one a] at hv
    simp only [sq, mul_assoc, mul_eq_mul_left_iff] at hv
    obtain hv | rfl := hv
    · have : IsUnit a := isUnit_of_mul_eq_one a v hv.symm
      simpa [this] using ha.not_unit
    · simpa using ha.ne_zero
  · simp [ha]

protected theorem mul {p a b : α} (hp : Prime p) (hfin : Finite p (a * b)) :
    multiplicity p (a * b) = multiplicity p a + multiplicity p b := by
  have hdiva : p ^ multiplicity p a ∣ a := pow_multiplicity_dvd ..
  have hdivb : p ^ multiplicity p b ∣ b := pow_multiplicity_dvd ..
  have hpoweq : p ^ (multiplicity p a + multiplicity p b) =
      p ^ multiplicity p a * p ^ multiplicity p b := by
    simp [pow_add]
  have hdiv : p ^ (multiplicity p a + multiplicity p b) ∣ a * b := by
    rw [hpoweq]; apply mul_dvd_mul <;> assumption
  have hsucc : ¬p ^ (multiplicity p a + multiplicity p b + 1) ∣ a * b :=
    fun h =>
    not_or_intro (is_greatest (hfin.mul_left hp) (lt_succ_self _))
      (is_greatest (hfin.mul_right hp) (lt_succ_self _))
      (_root_.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul hp hdiva hdivb h)
  rw [eq_iff_of_finite hfin]
  exact ⟨hdiv, hsucc⟩

theorem Finset.prod {β : Type*} {p : α} (hp : Prime p) (s : Finset β) (f : β → α)
    (hfin : Finite p (∏ x ∈ s, f x)) :
    multiplicity p (∏ x ∈ s, f x) = ∑ x ∈ s, multiplicity p (f x) := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp only [Finset.sum_empty, Finset.prod_empty]
      convert one_right hp.not_unit
    · simp only [has, not_false_eq_true, Finset.prod_insert] at hfin
      simpa [has, ← ih (hfin.mul_right hp)] using multiplicity.mul hp hfin

protected theorem pow {p a : α} (hp : Prime p) (ha : Finite p a) :
    ∀ {k : ℕ}, multiplicity p (a ^ k) = k * multiplicity p a := by
  intro k
  induction' k with k hk
  · simp [one_right hp.not_unit]
  · rw [pow_succ, multiplicity.mul hp, hk, add_mul, one_mul, add_comm]
    rw [← pow_succ]
    exact finite_pow hp ha

theorem multiplicity_pow_self {p : α} (h0 : p ≠ 0) (hu : ¬IsUnit p) (n : ℕ) :
    multiplicity p (p ^ n) = n := by
  apply unique
  · rfl
  · rw [pow_dvd_pow_iff h0 hu]
    apply Nat.not_succ_le_self

theorem multiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : ℕ) :
    multiplicity p (p ^ n) = n :=
  multiplicity_pow_self hp.ne_zero hp.not_unit n

end CancelCommMonoidWithZero

end multiplicity

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

namespace multiplicity

theorem finite_int_iff_natAbs_finite {a b : ℤ} : Finite a b ↔ Finite a.natAbs b.natAbs := by
  simp only [finite_def, ← Int.natAbs_dvd_natAbs, Int.natAbs_pow]

theorem finite_int_iff {a b : ℤ} : Finite a b ↔ a.natAbs ≠ 1 ∧ b ≠ 0 := by
  rw [finite_int_iff_natAbs_finite, finite_nat_iff, pos_iff_ne_zero, Int.natAbs_ne_zero]

end multiplicity
