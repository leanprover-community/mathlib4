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
def IsOrderEquiv : Prop := ∀ x y, v x ≤ v y ↔ w x ≤ w y

theorem IsOrderEquiv.refl : v.IsOrderEquiv v := fun _ _ ↦ .rfl

variable {v w}

theorem IsOrderEquiv.symm (h : v.IsOrderEquiv w) : w.IsOrderEquiv v := fun _ _ ↦ (h _ _).symm

theorem IsOrderEquiv.trans {u : AbsoluteValue R S} (h₁ : v.IsOrderEquiv w)
    (h₂ : w.IsOrderEquiv u) : v.IsOrderEquiv u := fun _ _ ↦ (h₁ _ _).trans (h₂ _ _)

end OrderedSemiring

section LinearOrderedSemifield

variable {R S : Type*} [Field R] [Semifield S] [LinearOrder S] {v w : AbsoluteValue R S}

theorem IsOrderEquiv.lt_iff_lt (h : v.IsOrderEquiv w) {x y : R} : v x < v y ↔ w x < w y := by
  rw [← le_iff_le_iff_lt_iff_lt, h]

theorem IsOrderEquiv.lt_one_iff (h : v.IsOrderEquiv w) {x : R} : v x < 1 ↔ w x < 1 := by
  simpa using h.lt_iff_lt (y := 1)

variable [IsStrictOrderedRing S]

theorem isOrderEquiv_iff_lt_one_iff :
    v.IsOrderEquiv w ↔ ∀ x, v x < 1 ↔ w x < 1 := by
  refine ⟨fun h _ ↦ h.lt_one_iff, fun h x y ↦ ?_⟩
  rcases eq_or_ne (v x) 0 with (_ | hy₀) <;> simp_all
  rw [le_iff_le_iff_lt_iff_lt, ← one_mul (v x), ← mul_inv_lt_iff₀ (by simp_all), ← one_mul (w x),
    ← mul_inv_lt_iff₀ (by simp_all), ← map_inv₀, ← map_mul, ← map_inv₀, ← map_mul]
  exact h _

private theorem one_lt_imp_of_lt_one_imp (h : ∀ x, v x < 1 → w x < 1) {x : R}
    (hv : 1 < v x) : 1 < w x :=
  (inv_lt_one_iff₀.1 <| map_inv₀ w _ ▸ h _ <| map_inv₀ v _ ▸ inv_lt_one_of_one_lt₀ hv).resolve_left
    fun hw ↦ not_lt.2 zero_le_one (by simpa [(map_eq_zero _).1 <| w.nonpos_iff.1 hw] using hv)

theorem IsOrderEquiv.one_lt_iff (h : v.IsOrderEquiv w) (x : R) : 1 < v x ↔ 1 < w x :=
  ⟨fun hv => one_lt_imp_of_lt_one_imp (fun _ => h.lt_one_iff.1) hv,
    fun hw => one_lt_imp_of_lt_one_imp (fun _ => h.lt_one_iff.2) hw⟩

private theorem IsOrderEquiv.eq_one_imp (h : v.IsOrderEquiv w) {x : R} (hv : v x = 1) :
    w x = 1 := by
  cases eq_or_lt_of_le (not_lt.1 <| h.lt_one_iff.not.1 hv.not_lt) with
  | inl hl => rw [← hl]
  | inr hr => rw [← h.one_lt_iff] at hr; absurd hv; exact ne_of_gt hr

theorem IsOrderEquiv.eq_one_iff (h : v.IsOrderEquiv w) (x : R) : v x = 1 ↔ w x = 1 :=
  ⟨fun hv => h.eq_one_imp hv, fun hw => h.symm.eq_one_imp hw⟩

theorem IsOrderEquiv.isNontrivial {w : AbsoluteValue R S}
    (h : v.IsOrderEquiv w) (hv : w.IsNontrivial) : v.IsNontrivial := by
  obtain ⟨x, h₀, h₁⟩ := hv
  cases lt_or_lt_iff_ne.2 h₁ with
  | inl hw => exact ⟨x, h₀, h.lt_one_iff.2 hw |>.ne⟩
  | inr hw =>
    exact ⟨x⁻¹, inv_ne_zero h₀, h.lt_one_iff.2 (map_inv₀ w _ ▸ inv_lt_one_of_one_lt₀ hw) |>.ne⟩

end LinearOrderedSemifield

section LinearOrderedField

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}

theorem isOrderEquiv_of_lt_one_imp [Archimedean S] [IsStrictOrderedRing S] (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 → w x < 1) :
    v.IsOrderEquiv w := by
  refine isOrderEquiv_iff_lt_one_iff.2 fun a ↦ ?_
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

end LinearOrderedField

section Real

variable {R : Type*} [Semiring R]

/-- Two absolute values `f, g` on `R` with values in `ℝ` are *equivalent* if there exists
a positive real constant `c` such that for all `x : R`, `(f x)^c = g x`. -/
def IsEquiv (f g : AbsoluteValue R ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ (f · ^ c) = g

/-- Equivalence of absolute values is reflexive. -/
lemma isEquiv_refl (f : AbsoluteValue R ℝ) : IsEquiv f f :=
  ⟨1, Real.zero_lt_one, funext fun x ↦ Real.rpow_one (f x)⟩

/-- Equivalence of absolute values is symmetric. -/
lemma isEquiv_symm {f g : AbsoluteValue R ℝ} (hfg : IsEquiv f g) : IsEquiv g f := by
  rcases hfg with ⟨c, hcpos, h⟩
  refine ⟨1 / c, one_div_pos.mpr hcpos, ?_⟩
  simp [← h, Real.rpow_rpow_inv (apply_nonneg f _) (ne_of_lt hcpos).symm]

/-- Equivalence of absolute values is transitive. -/
lemma isEquiv_trans {f g k : AbsoluteValue R ℝ} (hfg : IsEquiv f g) (hgk : IsEquiv g k) :
    IsEquiv f k := by
  rcases hfg with ⟨c, hcPos, hfg⟩
  rcases hgk with ⟨d, hdPos, hgk⟩
  refine ⟨c * d, mul_pos hcPos hdPos, ?_⟩
  simp [← hgk, ← hfg, Real.rpow_mul (apply_nonneg f _)]

instance : Setoid (AbsoluteValue R ℝ) where
  r := IsEquiv
  iseqv := {
    refl := isEquiv_refl
    symm := isEquiv_symm
    trans := isEquiv_trans
  }

/-- An absolute value is equivalent to the trivial iff it is trivial itself. -/
@[simp]
lemma eq_trivial_of_isEquiv_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    (f : AbsoluteValue R ℝ) :
    f ≈ .trivial ↔ f = .trivial := by
  refine ⟨fun ⟨c, hc₀, hc⟩ ↦ ext fun x ↦ ?_, fun H ↦ H ▸ isEquiv_refl f⟩
  apply_fun (· x) at hc
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp only [ne_eq, hx, not_false_eq_true, trivial_apply] at hc ⊢
    exact (Real.rpow_left_inj (f.nonneg x) zero_le_one hc₀.ne').mp <| (Real.one_rpow c).symm ▸ hc

lemma isEquiv_of_not_isNontrivial {f g : AbsoluteValue R ℝ} (hf : ¬f.IsNontrivial)
    (hg : ¬g.IsNontrivial) : f ≈ g := by
  refine ⟨1, zero_lt_one, funext fun x ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx <;> simp only [AbsoluteValue.map_zero, Real.rpow_one]
  rw [not_isNontrivial_apply hf hx, not_isNontrivial_apply hg hx]

variable {F : Type*} [Field F] {v w : AbsoluteValue F ℝ}

open Real in
/--
If $v$ and $w$ are two real absolute values on a field $F$ and $v(x) < 1$ if
and only if $w(x) < 1$, then $\frac{\log (v(a))}{\log (w(a))}$ is constant for all $a\in F$
with $1 < v(a)$.
-/
theorem IsOrderEquiv.log_div_log_eq_log_div_log (h : v.IsOrderEquiv w)
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
theorem IsOrderEquiv.exists_rpow_eq {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (h : v.IsOrderEquiv w) :
    ∃ (t : ℝ) (_ : 0 < t), ∀ x, 1 < v x → w x ^ t = v x := by
  let ⟨a, ha⟩ := hv.exists_abv_gt_one
  refine ⟨(v a).log / (w a).log,
    div_pos (log_pos ha) (log_pos ((h.one_lt_iff a).1 ha)), fun b hb ↦ ?_⟩
  rw [← h.log_div_log_eq_log_div_log ha hb, div_eq_inv_mul, rpow_mul (w.nonneg _),
    rpow_inv_log (by linarith [(h.one_lt_iff b).1 hb]) (by linarith [(h.one_lt_iff b).1 hb]),
    exp_one_rpow, exp_log (by linarith)]

open Real in
/--
If `v` and `w` are two real absolute values on a field `F`, where `v` is non-trivial, then `v` and
`w` are equivalent if and only if `v x < 1` exactly when `w x < 1`.
-/
theorem isEquiv_iff_isOrderEquiv {v w : AbsoluteValue F ℝ} :
    v.IsEquiv w ↔ v.IsOrderEquiv w := by
  refine ⟨fun ⟨t, ht, h⟩ ↦ isOrderEquiv_iff_lt_one_iff.2
    fun x ↦ h ▸ (rpow_lt_one_iff' (v.nonneg x) ht).symm, fun h ↦ isEquiv_symm ?_⟩
  by_cases hv : v.IsNontrivial
  · obtain ⟨t, ht₀, ht⟩ := h.exists_rpow_eq hv
    refine ⟨t, ht₀, funext fun x ↦ ?_⟩
    rcases eq_or_ne (v x) 0 with (h₀ | h₀); · simp [(map_eq_zero v).1 h₀, zero_rpow ht₀.ne.symm]
    rcases eq_or_ne (v x) 1 with (h₁ | h₁); · simp [h₁, (h.eq_one_iff x).1 h₁]
    by_cases h₂ : 0 < v x ∧ v x < 1
    · rw [← inv_inj, ← map_inv₀ v, ← ht _ (map_inv₀ v _ ▸ one_lt_inv_iff₀.2 h₂), map_inv₀,
        inv_rpow (w.nonneg _)]
    · have hv_le : (v x)⁻¹ ≤ 1 := not_lt.1 <| one_lt_inv_iff₀.not.2 h₂
      rw [inv_le_one₀ (v.pos <| v.ne_zero_iff.mp h₀)] at hv_le
      exact ht _ <| lt_of_le_of_ne hv_le h₁.symm
  · exact isEquiv_of_not_isNontrivial (mt h.isNontrivial hv) hv

/--
If `v` and `w` are inequivalent absolute values and `v` is non-trivial, then we can find an `a : F`
such that `v a < 1` while `1 ≤ w a`.
-/
theorem exists_lt_one_one_le_of_not_isEquiv {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (h : ¬v.IsEquiv w) :
    ∃ a : F, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact isEquiv_iff_isOrderEquiv.2 <| isOrderEquiv_of_lt_one_imp hv h

/--
If `v` and `w` are two non-trivial and inequivalent absolute values then
we can find an `a : K` such that `1 < v a` while `w a < 1`.
-/
theorem exists_one_lt_lt_one_of_not_isEquiv {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (hw : w.IsNontrivial) (h : ¬v.IsEquiv w) :
    ∃ a : F, 1 < v a ∧ w a < 1 := by
  let ⟨a, ha⟩ := exists_lt_one_one_le_of_not_isEquiv hv h
  let ⟨b, hb⟩ := exists_lt_one_one_le_of_not_isEquiv hw (mt w.isEquiv_symm h)
  exact ⟨b / a, by simpa using ⟨one_lt_div (w.pos_of_pos v (by linarith)) |>.2 (by linarith),
    div_lt_one (by linarith) |>.2 (by linarith)⟩⟩

end Real

end AbsoluteValue
