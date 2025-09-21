/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Equivalence of real-valued absolute values

Two absolute values `v₁, v₂ : AbsoluteValue R ℝ` are *equivalent* if there exists a
positive real number `c` such that `v₁ x ^ c = v₂ x` for all `x : R`.
-/

namespace AbsoluteValue

section OrderedSemiring

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S]
  (v w : AbsoluteValue R S)

/-- Two absolute values `v` and `w` are *equivalent* if `v x ≤ v y` precisely when
`w x ≤ w y`.

Note that for real absolute values this condition is equivalent to the existence of a positive
real number `c` such that `v x ^ c = w x` for all `x`. See
`AbsoluteValue.isEquiv_iff_exists_rpow_eq`. -/
def IsEquiv : Prop := ∀ x y, v x ≤ v y ↔ w x ≤ w y

theorem IsEquiv.refl : v.IsEquiv v := fun _ _ ↦ .rfl

variable {v w}

theorem IsEquiv.rfl : v.IsEquiv v := fun _ _ ↦ .rfl

theorem IsEquiv.symm (h : v.IsEquiv w) : w.IsEquiv v := fun _ _ ↦ (h _ _).symm

theorem IsEquiv.trans {u : AbsoluteValue R S} (h₁ : v.IsEquiv w)
    (h₂ : w.IsEquiv u) : v.IsEquiv u := fun _ _ ↦ (h₁ _ _).trans (h₂ _ _)

@[deprecated (since := "2025-09-12")] alias isEquiv_refl := IsEquiv.refl
@[deprecated (since := "2025-09-12")] alias isEquiv_symm := IsEquiv.symm
@[deprecated (since := "2025-09-12")] alias isEquiv_trans := IsEquiv.trans

instance : Setoid (AbsoluteValue R S) where
  r := IsEquiv
  iseqv := {
    refl := .refl
    symm := .symm
    trans := .trans
  }

theorem IsEquiv.le_iff_le (h : v.IsEquiv w) {x y : R} : v x ≤ v y ↔ w x ≤ w y := h ..

theorem IsEquiv.lt_iff_lt (h : v.IsEquiv w) {x y : R} : v x < v y ↔ w x < w y :=
  lt_iff_lt_of_le_iff_le' (h y x) (h x y)

theorem IsEquiv.eq_iff_eq (h : v.IsEquiv w) {x y : R} : v x = v y ↔ w x = w y := by
  simp [le_antisymm_iff, h x y, h y x]

variable [IsDomain S] [Nontrivial R]

theorem IsEquiv.lt_one_iff (h : v.IsEquiv w) {x : R} :
    v x < 1 ↔ w x < 1 := by
  simpa only [map_one] using h.lt_iff_lt (y := 1)

theorem IsEquiv.one_lt_iff (h : v.IsEquiv w) {x : R} :
    1 < v x ↔ 1 < w x := by
  simpa only [map_one] using h.lt_iff_lt (x := 1)

theorem IsEquiv.le_one_iff (h : v.IsEquiv w) {x : R} :
    v x ≤ 1 ↔ w x ≤ 1 := by
  simpa only [map_one] using h x 1

theorem IsEquiv.one_le_iff (h : v.IsEquiv w) {x : R} :
    1 ≤ v x ↔ 1 ≤ w x := by
  simpa only [map_one] using h 1 x

theorem IsEquiv.eq_one_iff (h : v.IsEquiv w) {x : R} : v x = 1 ↔ w x = 1 := by
  simpa only [map_one] using h.eq_iff_eq (x := x) (y := 1)

theorem IsEquiv.isNontrivial_congr {w : AbsoluteValue R S} (h : v.IsEquiv w) :
    v.IsNontrivial ↔ w.IsNontrivial :=
  not_iff_not.1 <| by aesop (add simp [not_isNontrivial_iff, h.eq_one_iff])

alias ⟨IsEquiv.isNontrivial, _⟩ := IsEquiv.isNontrivial_congr

end OrderedSemiring

section LinearOrderedSemifield

variable {R S : Type*} [Field R] [Semifield S] [LinearOrder S] {v w : AbsoluteValue R S}

/-- An absolute value is equivalent to the trivial iff it is trivial itself. -/
@[simp]
lemma isEquiv_trivial_iff_eq_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    [IsStrictOrderedRing S] {f : AbsoluteValue R S} :
    f.IsEquiv .trivial ↔ f = .trivial :=
  ⟨fun h ↦ by aesop (add simp [h.eq_one_iff, AbsoluteValue.trivial]), fun h ↦ h ▸ .rfl⟩

@[deprecated (since := "2025-09-12")]
alias eq_trivial_of_isEquiv_trivial := isEquiv_trivial_iff_eq_trivial

variable [IsStrictOrderedRing S]

theorem isEquiv_iff_lt_one_iff :
    v.IsEquiv w ↔ ∀ x, v x < 1 ↔ w x < 1 := by
  refine ⟨fun h _ ↦ h.lt_one_iff, fun h x y ↦ ?_⟩
  rcases eq_or_ne (v x) 0 with (_ | hy₀) <;> simp_all
  rw [le_iff_le_iff_lt_iff_lt, ← one_mul (v x), ← mul_inv_lt_iff₀ (by simp_all), ← one_mul (w x),
    ← mul_inv_lt_iff₀ (by simp_all), ← map_inv₀, ← map_mul, ← map_inv₀, ← map_mul]
  exact h _

variable [Archimedean S] [ExistsAddOfLE S]

theorem isEquiv_of_lt_one_imp (hv : v.IsNontrivial) (h : ∀ x, v x < 1 → w x < 1) : v.IsEquiv w := by
  refine isEquiv_iff_lt_one_iff.2 fun a ↦ ?_
  rcases eq_or_ne a 0 with (rfl | ha₀) <;> try simp
  refine ⟨h a, fun hw ↦ ?_⟩
  let ⟨x₀, hx₀⟩ := hv.exists_abv_lt_one
  have hpow (n : ℕ) (hv : 1 ≤ v a) : w x₀ < w a ^ n := by
    rw [← one_mul (_ ^ _), ← mul_inv_lt_iff₀ (pow_pos (by simp_all) _),
      ← map_pow, ← map_inv₀, ← map_mul]
    apply h
    rw [map_mul, map_inv₀, map_pow, mul_inv_lt_iff₀ (pow_pos (by simp [ha₀]) _), one_mul]
    exact lt_of_lt_of_le hx₀.2 <| one_le_pow₀ hv
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (w.pos hx₀.1) hw
  exact not_le.1 <| mt (hpow n) <| not_lt.2 hn.le

/--
If `v` and `w` are inequivalent absolute values and `v` is non-trivial, then we can find an `a : R`
such that `v a < 1` while `1 ≤ w a`.
-/
theorem exists_lt_one_one_le_of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNontrivial)
    (h : ¬v.IsEquiv w) : ∃ a : R, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact isEquiv_of_lt_one_imp hv h

/--
If `v` and `w` are two non-trivial and inequivalent absolute values then we can find an `a : R`
such that `1 < v a` while `w a < 1`.
-/
theorem exists_one_lt_lt_one_of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNontrivial)
    (hw : w.IsNontrivial) (h : ¬v.IsEquiv w) :
    ∃ a : R, 1 < v a ∧ w a < 1 := by
  let ⟨a, hva, hwa⟩ := exists_lt_one_one_le_of_not_isEquiv hv h
  let ⟨b, hwb, hvb⟩ := exists_lt_one_one_le_of_not_isEquiv hw (mt .symm h)
  exact ⟨b / a, by simp [w.pos_iff.1 (lt_of_lt_of_le zero_lt_one hwa), one_lt_div, div_lt_one,
    lt_of_le_of_lt' hvb hva, lt_of_le_of_lt' hwa hwb]⟩

end LinearOrderedSemifield

section Real

open Real

variable {F : Type*} [Field F] {v w : AbsoluteValue F ℝ}

theorem IsEquiv.log_div_log_pos (h : v.IsEquiv w) {a : F} (ha₀ : a ≠ 0) (ha₁ : w a ≠ 1) :
    0 < (w a).log / (v a).log := by
  rcases ha₁.lt_or_gt with hwa | hwa
  · simpa using div_pos (neg_pos_of_neg <| log_neg (w.pos ha₀) (hwa))
      (neg_pos_of_neg <| log_neg (v.pos ha₀) (h.lt_one_iff.2 hwa))
  · exact div_pos (log_pos <| hwa) (log_pos (h.one_lt_iff.2 hwa))

/--
If $v$ and $w$ are two real absolute values on a field $F$, equivalent in the sense that
$v(x) \leq v(y)$ if and only if $w(x) \leq w(y)$, then $\frac{\log (v(a))}{\log (w(a))}$ is
constant for all $0 \neq a\in F$ with $v(a) \neq 1$.
-/
theorem IsEquiv.log_div_log_eq_log_div_log (h : v.IsEquiv w)
    {a : F} (ha₀ : a ≠ 0) (ha₁ : v a ≠ 1) {b : F} (hb₀ : b ≠ 0) (hb₁ : v b ≠ 1) :
    (v b).log / (w b).log = (v a).log / (w a).log := by
  by_contra! h_ne
  wlog ha : 1 < v a generalizing a b
  · apply this (inv_ne_zero ha₀) (by simpa) hb₀ hb₁ (by simpa)
    simpa using one_lt_inv_iff₀.2 ⟨v.pos ha₀, ha₁.lt_of_le (not_lt.1 ha)⟩
  wlog hb : 1 < v b generalizing a b
  · apply this ha₀ ha₁ (inv_ne_zero hb₀) (by simpa) (by simpa) ha
    simpa using one_lt_inv_iff₀.2 ⟨v.pos hb₀, hb₁.lt_of_le (not_lt.1 hb)⟩
  wlog h_lt : (v b).log / (w b).log < (v a).log / (w a).log generalizing a b
  · exact this hb₀ hb₁ ha₀ ha₁ h_ne.symm hb ha <| lt_of_le_of_ne (not_lt.1 h_lt) h_ne.symm
  have hwa := h.one_lt_iff.1 ha
  have hwb := h.one_lt_iff.1 hb
  rw [div_lt_div_iff₀ (log_pos hwb) (log_pos hwa), mul_comm (v a).log,
    ← div_lt_div_iff₀ (log_pos ha) (log_pos hwa)] at h_lt
  let ⟨q, ⟨hq₁, hq₂⟩⟩ := exists_rat_btwn h_lt
  rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hq₁ hq₂
  rw [div_lt_div_iff₀ (log_pos ha) (by simp [q.den_pos]), mul_comm, ← log_pow, ← log_zpow,
    log_lt_log_iff (pow_pos (by linarith) _) (zpow_pos (by linarith) _),
    ← div_lt_one (zpow_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at hq₁
  rw [div_lt_div_iff₀ (by simp [q.den_pos]) (log_pos hwa), mul_comm (w _).log,
    ← log_pow, ← log_zpow, log_lt_log_iff (zpow_pos (by linarith) _) (pow_pos (by linarith) _),
    ← one_lt_div (zpow_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at hq₂
  exact not_lt_of_gt (h.lt_one_iff.1 hq₁) hq₂

/--
If `v` and `w` are two real absolute values on a field `F`, then `v` and `w` are equivalent if
and only if there exists a positive real constant `c` such that for all `x : R`, `(f x)^c = g x`.
-/
theorem isEquiv_iff_exists_rpow_eq {v w : AbsoluteValue F ℝ} :
    v.IsEquiv w ↔ ∃ c : ℝ, 0 < c ∧ (v · ^ c) = w := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht, h⟩ ↦ isEquiv_iff_lt_one_iff.2
    fun x ↦ h ▸ (rpow_lt_one_iff' (v.nonneg x) ht).symm⟩
  by_cases hw : w.IsNontrivial
  · let ⟨a, ha₀, ha₁⟩ := hw
    refine ⟨(w a).log / (v a).log, h.log_div_log_pos ha₀ ha₁, funext fun b ↦ ?_⟩
    rcases eq_or_ne b 0 with rfl | hb₀; · simp [zero_rpow (by linarith [h.log_div_log_pos ha₀ ha₁])]
    rcases eq_or_ne (w b) 1 with hb₁ | hb₁; · simp [hb₁, h.eq_one_iff.2 hb₁]
    rw [← h.symm.log_div_log_eq_log_div_log ha₀ ha₁ hb₀ hb₁, div_eq_inv_mul, rpow_mul (v.nonneg _),
      rpow_inv_log (v.pos hb₀) (h.eq_one_iff.not.2 hb₁), exp_one_rpow, exp_log (w.pos hb₀)]
  · exact ⟨1, zero_lt_one, funext fun x ↦ by rcases eq_or_ne x 0 with rfl | h₀ <;>
      aesop (add simp [h.isNontrivial_congr])⟩

end Real

end AbsoluteValue
