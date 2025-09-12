/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Ring.WithAbs

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

theorem IsEquiv.isNontrivial_iff {w : AbsoluteValue R S} (h : v.IsEquiv w) :
    v.IsNontrivial ↔ w.IsNontrivial :=
  not_iff_not.1 <| by aesop (add simp [not_isNontrivial_iff, h.eq_one_iff])
alias ⟨IsEquiv.isNontrivial, _⟩ := IsEquiv.isNontrivial_iff

end OrderedSemiring

section LinearOrderedSemifield

variable {R S : Type*} [Field R] [Semifield S] [LinearOrder S] {v w : AbsoluteValue R S}

/-- An absolute value is equivalent to the trivial iff it is trivial itself. -/
@[simp]
lemma isEquiv_trivial_iff_eq_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    [IsStrictOrderedRing S] {f : AbsoluteValue R S} :
    f.IsEquiv .trivial ↔ f = .trivial :=
  ⟨fun h ↦ by aesop (add simp [h.eq_one_iff, AbsoluteValue.trivial]), fun h ↦ h ▸ .rfl⟩

@[deprecated (since := "2025-09-10")]
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

variable {F : Type*} [Field F] {v w : AbsoluteValue F ℝ}

open Real in
theorem IsEquiv.log_div_log_pos (h : v.IsEquiv w) {a : F} (ha₀ : a ≠ 0) (ha₁ : w a ≠ 1) :
    0 < (w a).log / (v a).log := by
  rcases ha₁.lt_or_gt with hwa | hwa
  · simpa using div_pos (neg_pos_of_neg <| log_neg (w.pos ha₀) (hwa))
      (neg_pos_of_neg <| log_neg (v.pos ha₀) (h.lt_one_iff.2 hwa))
  · exact div_pos (log_pos <| hwa) (log_pos (h.one_lt_iff.2 hwa))

open Real in
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

open Real in
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
      aesop (add simp [h.isNontrivial_iff])⟩

end Real

/--
The limit $v\left(\frac{1}{1 + a ^ n}\right)\to 1$, for an absolute value $v$ on a field
$F$ if $v(a) < 1$.
-/
theorem tendsto_div_one_add_pow_nhds_one {v : AbsoluteValue F ℝ} {a : F} (ha : v a < 1) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n))) Filter.atTop (𝓝 1) := by
  simp_rw [v.isAbsoluteValue.abv_div, v.map_one]
  nth_rw 2 [show (1 : ℝ) = 1 / 1 by norm_num]
  apply Tendsto.div tendsto_const_nhds _ one_ne_zero
  have h_add := Tendsto.const_add 1 <| tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha
  have h_sub := Tendsto.const_sub 1 <| tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha
  simp only [add_zero, sub_zero] at h_add h_sub
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_sub h_add
    (fun n ↦ le_trans (by rw [map_one, map_pow]) (v.le_add _ _))
    (fun n ↦ le_trans (v.add_le _ _) (by rw [map_one, map_pow]))

/--
The limit $v \left(\frac{1}{1 + a ^ n}\right)\to 0$, for an absolute value $v$ on a field
$F$ if $1 < v(a)$.
-/
theorem tendsto_pow_div_one_add_pow_zero {v : AbsoluteValue F ℝ} {a : F} (ha : 1 < v a) :
    Filter.Tendsto (fun (n : ℕ) => v (1 / (1 + a ^ n))) Filter.atTop (𝓝 0) := by
  simp_rw [div_eq_mul_inv, one_mul, map_inv₀, fun n => add_comm 1 (a ^ n)]
  apply Filter.Tendsto.inv_tendsto_atTop
  apply Filter.tendsto_atTop_mono (fun n => v.le_add _ _)
  simp_rw [map_one, map_pow v]
  apply Filter.tendsto_atTop_add_right_of_le _ _ _ (fun _ => le_rfl)
  refine tendsto_atTop_of_geom_le (by simp only [pow_zero, zero_lt_one]) ha fun n => ?_
  rw [← map_pow, ← map_pow, ← map_mul, pow_succ']

open Filter in
/--
- $F$: field;
- $a, b\in F$;
- $v_1, ..., v_k, w$: absolute values on $F$;
- $1 < v_i(a)$ and $1 < v_i(b)$;
- $v_j(a) < 1$ for $j \neq i$;
- $w(a) = 1$ and $w(b) < 1$.

There is a sequence of values that tends to $\infty$
under $v_i$, tends to $0$ under $v_j$, and is always $< 1$ under $w$.
An example sequence is given by $a ^ n \cdot b$.
-/
theorem exists_tendsto_zero_tendsto_atTop_tendsto_const
    {ι : Type*} {v : ι → AbsoluteValue F ℝ} {w : AbsoluteValue F ℝ} {a b : F} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : w a = 1) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ c : ℕ → F,
      Tendsto (fun n => (v i) (c n)) atTop atTop ∧
        (∀ j ≠ i, Tendsto (fun n => (v j) (c n)) atTop (𝓝 0)) ∧
          (∀ n, w (c n) < 1) := by
  refine ⟨fun n => a ^ n * b, ?_⟩; simp_rw [map_mul, map_pow, haw, one_pow, one_mul]
  refine ⟨Tendsto.atTop_mul_const (by linarith) (tendsto_pow_atTop_atTop_of_one_lt ha),
    fun j hj => ?_, fun _ => hbw⟩
  rw [← zero_mul <| v j b]
  exact Tendsto.mul_const _ <| tendsto_pow_atTop_nhds_zero_of_lt_one ((v j).nonneg _) (haj j hj)

open scoped Classical in
/--
- $F$: field;
- $a, b\in F$;
- $v_1, ..., v_k, w$: absolute values on $F$;
- $1 < v_i(a)$ and $1 < v_i(b)$;
- $v_j(a) < 1$ for $j \neq i$;
- $w(a) = 1$ and $w(b) < 1$.

There is a $k\in F$ such that $1 < v_i(k)$ while $v_j(k) < 1$ for all
$j \neq i$ and $w(k) < 1$.
This is given by taking large enough values of a witness sequence to
`exists_tendsto_zero_tendsto_atTop_tendsto_const` (for example $a ^ n \cdot b$ works).
-/
theorem exists_one_lt_lt_one_lt_one_of_eq_one
    {ι : Type*} [Fintype ι] {v : ι → AbsoluteValue F ℝ} {w : AbsoluteValue F ℝ} {a b : F} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : w a = 1) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : F, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  let ⟨c, hc⟩ := exists_tendsto_zero_tendsto_atTop_tendsto_const ha haj haw hb hbw
  simp_rw [Metric.tendsto_nhds, Filter.tendsto_atTop_atTop, Filter.eventually_atTop,
    dist_zero_right, ← WithAbs.norm_eq_abv, norm_norm] at hc
  choose r₁ hr₁ using hc.1 2
  choose rₙ hrₙ using fun j hj => hc.2.1 j hj 1 (by linarith)
  let r := Finset.univ.sup fun j => if h : j = i then r₁ else rₙ j h
  refine ⟨c r, lt_of_lt_of_le (by linarith) (hr₁ r ?_), fun j hj => ?_, hc.2.2 r⟩
  · exact Finset.le_sup_dite_pos (p := fun j => j = i) (f := fun _ _ => r₁) (Finset.mem_univ _) rfl
  · convert hrₙ j hj _ <| Finset.le_sup_dite_neg (fun j => j = i) (Finset.mem_univ j) _

open Filter in
/--
- $F$: field;
- $a, b\in F$;
- $v_1, ..., v_k, w$: absolute values on $F$;
- $1 < v_i(a)$;
- $v_j(a) < 1$ for $j \neq i$;
- $1 < w(a)$.

There is a sequence of elements in $F$ that tendsto $v_i b$ under $v_i$, tends to $0$ under
$v_j$ for $j ≠ i$, and tends to $w b$ under $w$.
Such a sequence is given by $\frac{1}{1 + a ^ {- n}}$.
-/
theorem exists_tendsto_const_tendsto_zero_tendsto_const
    {ι : Type*} {v : ι → AbsoluteValue F ℝ} {w : AbsoluteValue F ℝ} {a : F} {i : ι}
    (b : F) (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : 1 < w a) :
    ∃ c : ℕ → F,
      Tendsto (fun n => (v i) (c n)) atTop (𝓝 ((v i) b)) ∧
        (∀ j ≠ i, Tendsto (fun n => v j (c n)) atTop (𝓝 0)) ∧
          Tendsto (fun n => w (c n)) atTop (𝓝 (w b)) := by
  refine ⟨fun n => (1 / (1 + a⁻¹ ^ n) * b), ?_⟩; simp_rw [map_mul]
  nth_rw 2 [← one_mul (v i b), ← one_mul (w b)]
  let hai := map_inv₀ (v i) _ ▸ inv_lt_one_of_one_lt₀ ha
  replace haw := (map_inv₀ w _ ▸ inv_lt_one_of_one_lt₀ haw)
  refine ⟨Tendsto.mul_const _ (tendsto_div_one_add_pow_nhds_one hai), fun j hj => ?_,
      Tendsto.mul_const _ (tendsto_div_one_add_pow_nhds_one haw)⟩
  replace haj := map_inv₀ (v j) _ ▸
    (one_lt_inv₀ (pos_of_abv_pos (v j) (by linarith))).2 (haj j hj)
  exact zero_mul (v j b) ▸ Tendsto.mul_const _ (tendsto_pow_div_one_add_pow_zero haj)

open scoped Classical in
/--
- $F$: field;
- $a, b\in F$;
- $v_1, ..., v_k, w$: absolute values on $F$;
- $1 < v_i(a)$;
- $v_j(a) < 1$ for $j \neq i$;
- $1 < w(a)$.

There is a $k ∈ F$ such that $1 < v_i(k)$ while $v_j(k) < 1$ for all
$j ≠ i$ and $w(k) < 1$. This is given by taking large enough values of a witness sequence to
`exists_tendsto_const_tendsto_zero_tendsto_const` (for example $\frac{1}{1 + a ^ {- n}}$ works).

Note that this is the result `exists_one_lt_lt_one_lt_one_of_eq_one` replacing the condition
that $w(a) = 1$ with $1 < w(a)$ and removing the condition on $w(b)$.
-/
theorem exists_one_lt_lt_one_lt_one_of_one_lt
    {ι : Type*} [Fintype ι] {v : ι → AbsoluteValue F ℝ} {w : AbsoluteValue F ℝ} {a b : F} {i : ι}
    (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1) (haw : 1 < w a) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : F, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  let ⟨c, hc⟩ := exists_tendsto_const_tendsto_zero_tendsto_const b ha haj haw
  have hₙ := fun j hj => Metric.tendsto_nhds.1 <| hc.2.1 j hj
  simp_rw [Filter.eventually_atTop, dist_zero_right] at hₙ
  choose r₁ hr₁ using Filter.eventually_atTop.1 <| Filter.Tendsto.eventually_const_lt hb hc.1
  choose rₙ hrₙ using fun j hj => hₙ j hj 1 (by linarith)
  choose rN hrN using Filter.eventually_atTop.1 <| Filter.Tendsto.eventually_lt_const hbw hc.2.2
  let r := max (Finset.univ.sup fun j => if h : j = i then r₁ else rₙ j h) rN
  refine ⟨c r, hr₁ r ?_, fun j hj => ?_, ?_⟩
  · exact le_max_iff.2 <| Or.inl <|
      Finset.le_sup_dite_pos (p := fun j => j = i) (f := fun _ _ => r₁) (Finset.mem_univ _) rfl
  · simp only [← WithAbs.norm_eq_abv, norm_norm] at hrₙ
    exact hrₙ j hj _ <| le_max_iff.2 <| Or.inl <|
      Finset.le_sup_dite_neg (fun j => j = i) (Finset.mem_univ j) _
  · exact hrN _ <| le_max_iff.2 (Or.inr le_rfl)

/--
Let $v_1, ..., v_k$ be a collection of at least two non-trivial and pairwise inequivalent
absolute values on a field $F$. There is an $a ∈ F$ such that $1 < v_1(a)$ while
$v_j(a) < 1$ for all other $j ≠ 1$.
-/
theorem exists_one_lt_lt_one {n : ℕ} {v : Fin (n + 2) → AbsoluteValue F ℝ}
    (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j => ¬(v i).IsEquiv (v j)) :
    ∃ (a : F), 1 < v 0 a ∧ ∀ j ≠ 0, v j a < 1 := by
  induction n using Nat.case_strong_induction_on with
  | hz =>
    let ⟨a, ha⟩ := (v 0).exists_abv_one_lt_abv_lt_one_of_not_isEquiv (h 0) (h 1)
      (hv zero_ne_one.symm)
    exact ⟨a, ha.1, by simp [Fin.forall_fin_two]; exact ha.2⟩
  | hi n ih =>
    -- Assume the result is true for all smaller collections of absolute values
    -- Let `a : K` be the value from the collection with the last absolute value removed
    let ⟨a, ha⟩ := ih n le_rfl (fun _ => h _) (hv.comp_of_injective <| Fin.castSucc_injective _)
    -- Let `b : K` be the value using the first and last absolute value
    have : ![0, Fin.last (n + 2)].Injective := by simp [Function.Injective, Fin.forall_fin_two]
    let ⟨b, hb⟩ := ih 0 (by linarith) (fun _ => h _) <| hv.comp_of_injective this
    simp [Fin.forall_fin_two] at hb
    -- If `v last < 1` then `a` works.
    by_cases ha₀ : v (Fin.last _) a < 1
    · refine ⟨a, ha.1, fun j hj => ?_⟩
      by_cases hj' : j = Fin.last (n + 2)
      · exact hj' ▸ ha₀
      · exact ha.2 (Fin.castPred _ (ne_eq _ _ ▸  hj')) <| Fin.castPred_ne_zero _ hj
    -- If `v last = 1` then this is given by `exists_one_lt_lt_one_lt_one_of_eq_one` with
    -- `w = v last`.
    · by_cases ha₁ : v (Fin.last _) a = 1
      · let ⟨k, hk⟩ := exists_one_lt_lt_one_lt_one_of_eq_one
          (v := fun i : Fin (n + 2) => v i.castSucc) ha.1 ha.2 ha₁ hb.1 hb.2
        refine ⟨k, hk.1, fun j hj => ?_⟩
        by_cases h : j ≠ Fin.last (n + 2)
        · exact ne_eq _ _ ▸ hk.2.1 (j.castPred h) <| Fin.castPred_ne_zero _ hj
        · exact not_ne_iff.1 h ▸ hk.2.2
      -- The last cast `1 < v last` is given by `exists_one_lt_lt_one_lt_one_of_one_lt` with
      -- `w = v last`.
      · let ⟨k, hk⟩ := exists_one_lt_lt_one_lt_one_of_one_lt
          (v := fun i : Fin (n + 2) => v i.castSucc) ha.1 ha.2
            (lt_of_le_of_ne (not_lt.1 ha₀) (ne_eq _ _ ▸ ha₁).symm) hb.1 hb.2
        refine ⟨k, hk.1, fun j hj => ?_⟩
        by_cases h : j ≠ Fin.last _
        · apply ne_eq _ _ ▸ hk.2.1 (j.castPred h)
          rwa [← Fin.castPred_zero, Fin.castPred_inj]
        · exact not_ne_iff.1 h ▸ hk.2.2

end AbsoluteValue
