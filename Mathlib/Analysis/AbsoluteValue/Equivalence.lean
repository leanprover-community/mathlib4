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

open scoped Topology

namespace AbsoluteValue

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

section LinearOrderedField

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] [IsStrictOrderedRing S]
  {v w : AbsoluteValue R S}

theorem lt_one_iff_of_abv_lt_one_imp [Archimedean S] (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 → w x < 1) {a : R} :
    v a < 1 ↔ w a < 1 := by
  let ⟨x₀, hx₀⟩ := hv.exists_abv_lt_one
  by_cases ha₀ : a = 0
  · simp only [ha₀, AbsoluteValue.map_zero, zero_lt_one]
  refine ⟨h a, fun hw ↦ ?_⟩
  by_contra! hv
  have (n : ℕ) : w x₀ < w a ^ n := by
    rw [← one_mul (_ ^ _), ← mul_inv_lt_iff₀ (pow_pos (v.pos_of_abv_pos w (v.pos ha₀)) _),
      ← map_pow, ← map_inv₀, ← map_mul]
    apply h
    rw [map_mul, map_inv₀, map_pow, mul_inv_lt_iff₀ (pow_pos (by simp_all) _), one_mul]
    exact lt_of_lt_of_le hx₀.2 <| one_le_pow₀ hv
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (w.pos hx₀.1) hw
  linarith [this n]

end LinearOrderedField

variable {F : Type*} [Field F] {v w : AbsoluteValue F ℝ}

open Real in
/--
If $v$ and $w$ are two real absolute values on a field $F$, $v$ is non-trivial, and $v(x) < 1$ if
and only if $w(x) < 1$, then $\frac{\log (v(a))}{\log (w(a))}$ is constant for all $a ∈ F$
with $1 < v(a)$.
-/
theorem log_div_image_eq_singleton_of_abv_lt_one_iff (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    letI f : F → ℝ := fun a ↦ (v a).log / (w a).log
    ∃ (a : F) (_ : 1 < v a), ∀ (b : F) (_ : 1 < v b), f b = f a := by
  let ⟨a, ha⟩ := hv.exists_abv_gt_one
  refine ⟨a, ha, fun b hb₁ ↦ ?_⟩
  by_contra! hb₂
  wlog h_lt : (v b).log / (w b).log < (v a).log / (w a).log generalizing a b
  · exact this b hb₁ a ha hb₂.symm <| lt_of_le_of_ne (not_lt.1 h_lt) hb₂.symm
  have hwa := (v.one_lt_iff_of_lt_one_iff h _).1 ha
  have hwb := (v.one_lt_iff_of_lt_one_iff h _).1 hb₁
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
  exact not_lt_of_gt ((h _).1 hq₁) hq₂

open Real in
theorem exists_rpow_of_abv_one_lt_iff {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    ∃ (t : ℝ) (_ : 0 < t), ∀ x, 1 < v x → w x ^ t = v x := by
  obtain ⟨a, ha, hlog⟩ := log_div_image_eq_singleton_of_abv_lt_one_iff hv h
  refine ⟨(v a).log / (w a).log,
    div_pos (log_pos ha) (log_pos ((v.one_lt_iff_of_lt_one_iff h a).1 ha)), fun b hb ↦ ?_⟩
  simp_rw [← hlog b hb]
  have := (v.one_lt_iff_of_lt_one_iff h b).1 hb
  rw [div_eq_inv_mul, rpow_mul (w.nonneg _), rpow_inv_log (by linarith) (by linarith),
    exp_one_rpow, exp_log (by linarith)]

open Real in
/--
If $v$ and $w$ be two real absolute values on a field $F$, where $v$ is non-trivial, then $v$ and
$w$ are equivalent if and only if $v(x) < 1$ exactly when $w(x) < 1$.
-/
theorem isEquiv_iff_abv_lt_one_iff {v : AbsoluteValue F ℝ} (w : AbsoluteValue F ℝ)
    (hv : v.IsNontrivial) : w.IsEquiv v ↔ (∀ x, v x < 1 ↔ w x < 1) := by
  refine ⟨fun ⟨t, ht, h⟩ x ↦ h ▸ (rpow_lt_one_iff' (w.nonneg x) ht), fun h ↦ ?_⟩
  obtain ⟨t, ht, h_imp⟩ := exists_rpow_of_abv_one_lt_iff hv h
  refine ⟨t, ht, funext fun x ↦ ?_⟩
  by_cases h₀ : v x = 0
  · rw [(map_eq_zero v).1 h₀, map_zero, map_zero, zero_rpow (by linarith)]
  · by_cases h₁ : v x = 1
    · rw [h₁, (v.eq_one_iff_of_lt_one_iff h x).1 h₁, one_rpow]
    · by_cases h₂ : 0 < v x ∧ v x < 1
      · rw [← inv_inj, ← map_inv₀ v, ← h_imp _ (map_inv₀ v _ ▸ one_lt_inv_iff₀.2 h₂), map_inv₀,
          inv_rpow (w.nonneg _)]
      · rw [← one_lt_inv_iff₀, ← map_inv₀, not_lt] at h₂
        rw [← ne_eq, ← inv_ne_one, ← map_inv₀] at h₁
        exact h_imp _ <| (v.inv_lt_one_iff.1 <| lt_of_le_of_ne h₂ h₁).resolve_left
          ((map_ne_zero v).1 h₀)

/--
If $v$ and $w$ are inequivalent absolute values and $v$ is non-trivial, then we can find an $a ∈ F$
such that $v(a) < 1$ while $1 ≤ w(a)$.
-/
theorem exists_abv_lt_one_abv_one_le_of_not_isEquiv {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (h : ¬w.IsEquiv v) :
    ∃ a : F, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact isEquiv_iff_abv_lt_one_iff _ hv |>.2 <| fun  _ ↦ v.lt_one_iff_of_abv_lt_one_imp hv h

/--
If $v$ and $w$ are two non-trivial and inequivalent absolute values then
we can find an $a ∈ K$ such that $1 < v a$ while $w a < 1$.
-/
theorem exists_abv_one_lt_abv_lt_one_of_not_isEquiv {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (hw : w.IsNontrivial) (h : ¬w.IsEquiv v) :
    ∃ a : F, 1 < v a ∧ w a < 1 := by
  let ⟨a, ha⟩ := exists_abv_lt_one_abv_one_le_of_not_isEquiv hv h
  let ⟨b, hb⟩ := exists_abv_lt_one_abv_one_le_of_not_isEquiv hw (mt v.isEquiv_symm h)
  exact ⟨b / a, by simpa using ⟨one_lt_div (w.pos_of_abv_pos v (by linarith)) |>.2 (by linarith),
    div_lt_one (by linarith) |>.2 (by linarith)⟩⟩

end AbsoluteValue
