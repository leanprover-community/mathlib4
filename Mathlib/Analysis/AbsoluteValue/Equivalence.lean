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

/-- Two absolute values `v` and `w` are *order equivalent* if `v x ≤ v y` precisely when
`w x ≤ w y`.

Note that this is equivalent to `v.IsEquiv w` when `v` and `w` are real absolute values. -/
def IsEquiv : Prop := ∀ x y, v x ≤ v y ↔ w x ≤ w y

theorem IsEquiv.refl : v.IsEquiv v := fun _ _ ↦ .rfl

variable {v w}

theorem IsEquiv.symm (h : v.IsEquiv w) : w.IsEquiv v := fun _ _ ↦ (h _ _).symm

theorem IsEquiv.trans {u : AbsoluteValue R S} (h₁ : v.IsEquiv w)
    (h₂ : w.IsEquiv u) : v.IsEquiv u := fun _ _ ↦ (h₁ _ _).trans (h₂ _ _)

@[deprecated (since := "2025-09-10")] alias isEquiv_refl := IsEquiv.refl
@[deprecated (since := "2025-09-10")] alias isEquiv_symm := IsEquiv.symm
@[deprecated (since := "2025-09-10")] alias isEquiv_trans := IsEquiv.trans

instance : Setoid (AbsoluteValue R S) where
  r := IsEquiv
  iseqv := {
    refl := .refl
    symm := .symm
    trans := .trans
  }

end OrderedSemiring

section LinearOrderedSemifield

variable {R S : Type*} [Field R] [Semifield S] [LinearOrder S] {v w : AbsoluteValue R S}

theorem IsEquiv.lt_iff_lt (h : v.IsEquiv w) {x y : R} : v x < v y ↔ w x < w y := by
  rw [← le_iff_le_iff_lt_iff_lt, h]

theorem IsEquiv.lt_one_iff (h : v.IsEquiv w) {x : R} : v x < 1 ↔ w x < 1 := by
  simpa using h.lt_iff_lt (y := 1)

variable [IsStrictOrderedRing S]

theorem isEquiv_iff_lt_one_iff :
    v.IsEquiv w ↔ ∀ x, v x < 1 ↔ w x < 1 := by
  refine ⟨fun h _ ↦ h.lt_one_iff, fun h x y ↦ ?_⟩
  rcases eq_or_ne (v x) 0 with (_ | hy₀) <;> simp_all
  rw [le_iff_le_iff_lt_iff_lt, ← one_mul (v x), ← mul_inv_lt_iff₀ (by simp_all), ← one_mul (w x),
    ← mul_inv_lt_iff₀ (by simp_all), ← map_inv₀, ← map_mul, ← map_inv₀, ← map_mul]
  exact h _

private theorem one_lt_imp_of_lt_one_imp (h : ∀ x, v x < 1 → w x < 1) {x : R}
    (hv : 1 < v x) : 1 < w x :=
  (inv_lt_one_iff₀.1 <| map_inv₀ w _ ▸ h _ <| map_inv₀ v _ ▸ inv_lt_one_of_one_lt₀ hv).resolve_left
    fun hw ↦ not_lt.2 zero_le_one (by simpa [(map_eq_zero _).1 <| w.nonpos_iff.1 hw] using hv)

theorem IsEquiv.one_lt_iff (h : v.IsEquiv w) (x : R) : 1 < v x ↔ 1 < w x :=
  ⟨fun hv => one_lt_imp_of_lt_one_imp (fun _ => h.lt_one_iff.1) hv,
    fun hw => one_lt_imp_of_lt_one_imp (fun _ => h.lt_one_iff.2) hw⟩

private theorem IsEquiv.eq_one_imp (h : v.IsEquiv w) {x : R} (hv : v x = 1) :
    w x = 1 := by
  cases eq_or_lt_of_le (not_lt.1 <| h.lt_one_iff.not.1 hv.not_lt) with
  | inl hl => rw [← hl]
  | inr hr => rw [← h.one_lt_iff] at hr; absurd hv; exact ne_of_gt hr

theorem IsEquiv.eq_one_iff (h : v.IsEquiv w) (x : R) : v x = 1 ↔ w x = 1 :=
  ⟨fun hv => h.eq_one_imp hv, fun hw => h.symm.eq_one_imp hw⟩

theorem IsEquiv.isNontrivial {w : AbsoluteValue R S}
    (h : v.IsEquiv w) (hv : w.IsNontrivial) : v.IsNontrivial := by
  obtain ⟨x, h₀, h₁⟩ := hv
  cases lt_or_lt_iff_ne.2 h₁ with
  | inl hw => exact ⟨x, h₀, h.lt_one_iff.2 hw |>.ne⟩
  | inr hw =>
    exact ⟨x⁻¹, inv_ne_zero h₀, h.lt_one_iff.2 (map_inv₀ w _ ▸ inv_lt_one_of_one_lt₀ hw) |>.ne⟩

end LinearOrderedSemifield

section LinearOrderedField

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}

theorem isEquiv_of_lt_one_imp [Archimedean S] [IsStrictOrderedRing S] (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 → w x < 1) :
    v.IsEquiv w := by
  refine isEquiv_iff_lt_one_iff.2 fun a ↦ ?_
  rcases eq_or_ne a 0 with (rfl | ha₀) <;> try simp
  refine ⟨h a, fun hw ↦ ?_⟩
  let ⟨x₀, hx₀⟩ := hv.exists_abv_lt_one
  by_contra! hv
  have (n : ℕ) : w x₀ < w a ^ n := by
    rw [← one_mul (_ ^ _), ← mul_inv_lt_iff₀ (pow_pos (v.pos_of_pos w (v.pos ha₀)) _),
      ← map_pow, ← map_inv₀, ← map_mul]
    apply h
    rw [map_mul, map_inv₀, map_pow, mul_inv_lt_iff₀ (pow_pos (by simp_all) _), one_mul]
    exact lt_of_lt_of_le hx₀.2 <| one_le_pow₀ hv
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (w.pos hx₀.1) hw
  linarith [this n]

/-- An absolute value is equivalent to the trivial iff it is trivial itself. -/
@[simp]
lemma isEquiv_trivial_iff_eq_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    [IsStrictOrderedRing S] (f : AbsoluteValue R S) :
    f.IsEquiv .trivial ↔ f = .trivial := by
  refine ⟨fun h ↦ ext fun x ↦ ?_, fun h ↦ h ▸ .refl _⟩
  rcases eq_or_ne x 0 with rfl | hx <;> try simp
  exact trivial_apply (S := S) hx ▸ (h.eq_one_iff x |>.2 <| trivial_apply hx)

@[deprecated (since := "2025-09-10")]
alias eq_trivial_of_isEquiv_trivial := isEquiv_trivial_iff_eq_trivial

end LinearOrderedField

section Real

variable {F : Type*} [Field F] {v w : AbsoluteValue F ℝ}

open Real in
/--
If $v$ and $w$ are two real absolute values on a field $F$ and $v(x) < 1$ if
and only if $w(x) < 1$, then $\frac{\log (v(a))}{\log (w(a))}$ is constant for all $a\in F$
with $1 < v(a)$.
-/
theorem IsEquiv.log_div_log_eq_log_div_log (h : v.IsEquiv w)
    {a : F} (ha : 1 < v a) {b : F} (hb : 1 < v b) :
    (v b).log / (w b).log = (v a).log / (w a).log := by
  by_contra! h_ne
  wlog h_lt : (v b).log / (w b).log < (v a).log / (w a).log generalizing a b
  · exact this hb ha h_ne.symm <| lt_of_le_of_ne (not_lt.1 h_lt) h_ne.symm
  have hwa := (h.one_lt_iff _).1 ha
  have hwb := (h.one_lt_iff _).1 hb
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

open Real in
theorem IsEquiv.exists_rpow_eq_of_one_lt {v w : AbsoluteValue F ℝ} (h : v.IsEquiv w) :
    ∃ (t : ℝ) (_ : 0 < t), ∀ x, 1 < w x → v x ^ t = w x := by
  by_cases hw : w.IsNontrivial
  · let ⟨a, ha⟩ := hw.exists_abv_gt_one
    refine ⟨(w a).log / (v a).log,
      div_pos (log_pos ha) (log_pos ((h.symm.one_lt_iff a).1 ha)), fun b hb ↦ ?_⟩
    have := (h.symm.one_lt_iff b).1 hb
    rw [← h.symm.log_div_log_eq_log_div_log ha hb, div_eq_inv_mul, rpow_mul (v.nonneg _),
      rpow_inv_log (by linarith) (by linarith), exp_one_rpow, exp_log (by linarith)]
  · refine ⟨1, zero_lt_one, fun x _ ↦ ?_⟩
    rcases eq_or_ne x 0 with rfl | h₀; · simp
    simp [not_isNontrivial_apply hw h₀, not_isNontrivial_apply (mt h.symm.isNontrivial hw) h₀]

open Real in
/--
If `v` and `w` are two real absolute values on a field `F`, then `v` and `w` are equivalent if
and only if there exists a positive real constant `c` such that for all `x : R`, `(f x)^c = g x`.
-/
theorem isEquiv_iff_exists_rpow_eq {v w : AbsoluteValue F ℝ} :
    v.IsEquiv w ↔ ∃ c : ℝ, 0 < c ∧ (v · ^ c) = w := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht, h⟩ ↦ isEquiv_iff_lt_one_iff.2
    fun x ↦ h ▸ (rpow_lt_one_iff' (v.nonneg x) ht).symm⟩
  obtain ⟨t, ht₀, ht⟩ := h.exists_rpow_eq_of_one_lt
  refine ⟨t, ht₀, funext fun x ↦ ?_⟩
  rcases eq_or_ne (v x) 0 with (h₀ | h₀); · simp [(map_eq_zero v).1 h₀, zero_rpow ht₀.ne.symm]
  rcases eq_or_ne (w x) 1 with (h₁ | h₁); · simp [h₁, (h.symm.eq_one_iff x).1 h₁]
  by_cases h₂ : 0 < w x ∧ w x < 1
  · rw [← inv_inj, ← map_inv₀ w, ← ht _ (map_inv₀ w _ ▸ one_lt_inv_iff₀.2 h₂), map_inv₀,
      inv_rpow (v.nonneg _)]
  · have hw_le : (w x)⁻¹ ≤ 1 := not_lt.1 <| one_lt_inv_iff₀.not.2 h₂
    rw [inv_le_one₀ (w.pos <| v.ne_zero_iff.mp h₀)] at hw_le
    exact ht _ <| lt_of_le_of_ne hw_le h₁.symm

/--
If `v` and `w` are inequivalent absolute values and `v` is non-trivial, then we can find an `a : F`
such that `v a < 1` while `1 ≤ w a`.
-/
theorem exists_lt_one_one_le_of_not_isEquiv {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (h : ¬v.IsEquiv w) :
    ∃ a : F, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact isEquiv_of_lt_one_imp hv h

/--
If `v` and `w` are two non-trivial and inequivalent absolute values then
we can find an `a : K` such that `1 < v a` while `w a < 1`.
-/
theorem exists_one_lt_lt_one_of_not_isEquiv {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (hw : w.IsNontrivial) (h : ¬v.IsEquiv w) :
    ∃ a : F, 1 < v a ∧ w a < 1 := by
  let ⟨a, ha⟩ := exists_lt_one_one_le_of_not_isEquiv hv h
  let ⟨b, hb⟩ := exists_lt_one_one_le_of_not_isEquiv hw (mt .symm h)
  exact ⟨b / a, by simpa using ⟨one_lt_div (w.pos_of_pos v (by linarith)) |>.2 (by linarith),
    div_lt_one (by linarith) |>.2 (by linarith)⟩⟩

end Real

end AbsoluteValue
