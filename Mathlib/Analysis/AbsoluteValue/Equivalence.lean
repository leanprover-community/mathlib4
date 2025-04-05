/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Ring.WithAbs

/-!
# Equivalence of real-valued absolute values

Two absolute values `v₁, v₂ : AbsoluteValue R ℝ` are *equivalent* if there exists a
positive real number `c` such that `v₁ x ^ c = v₂ x` for all `x : R`.
-/

open Filter

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

variable {F S : Type*} [Field F] [LinearOrderedField S] {v w : AbsoluteValue F S}

open Filter in
theorem lt_one_iff_of_lt_one_imp [Archimedean S] [TopologicalSpace S]
    [OrderTopology S]
    (hv : v.IsNontrivial) (h : ∀ x, v x < 1 → w x < 1) {a : F} :
    v a < 1 ↔ w a < 1:= by
  let ⟨x₀, hx₀⟩ := hv.exists_abv_lt_one
  refine ⟨h a, fun hw => ?_⟩
  by_contra! hv
  have (n : ℕ) : w x₀ < w a ^ n := (mul_one_div_pow_lt_iff _ (pos_of_pos w (by linarith))).1 <|
    h _ ((mul_one_div_pow_lt_iff _ (by linarith)).2 (lt_of_lt_of_le hx₀.2 <| one_le_pow₀ hv))
  have hcontr : atTop.Tendsto (fun (_ : ℕ) => w x₀) (𝓝 0) := by
    let hwn := tendsto_pow_atTop_nhds_zero_iff.2 <| by convert abs_eq_self.2 (w.nonneg _) ▸ hw
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwn
      (Eventually.of_forall fun _ => w.nonneg x₀) (by simpa using ⟨1, fun n _ => le_of_lt (this n)⟩)
  linarith [tendsto_nhds_unique hcontr tendsto_const_nhds, w.pos hx₀.1]

/--
If $v$ and $w$ are two real absolute values on a field $F$, $v$ is non-trivial, and $v(x) < 1$ if
and only if $w(x) < 1$, then $\frac{\log (v(a))}{\log (w(a))}$ is constant for all $a ∈ F$
with $1 < v(a)$.
-/
theorem log_div_image_eq_singleton_of_le_one_iff {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    let f : F → ℝ := fun a => Real.log (v a) / Real.log (w a)
    ∃ (a : F) (_ : 1 < v a), ∀ (b : F) (_ : 1 < v b), f b = f a := by
  obtain ⟨a, ha⟩ := hv.exists_abv_gt_one
  refine ⟨a, ha, fun b hb₁ => ?_⟩
  by_contra! hb₂
  wlog hwlog : Real.log (v b) / Real.log (w b) < Real.log (v a) / Real.log (w a) generalizing a b
  · exact this b hb₁ a ha hb₂.symm <| lt_of_le_of_ne (not_lt.1 hwlog) hb₂.symm
  have : Real.log (v b) / Real.log (v a) < Real.log (w b) / Real.log (w a) := by
    have hwa := Real.log_pos <| (one_lt_iff_of_lt_one_iff h _).1 ha
    have hwb := Real.log_pos <| (one_lt_iff_of_lt_one_iff h _).1 hb₁
    rwa [div_lt_div_iff₀ (Real.log_pos ha) hwa, mul_comm (Real.log (w _)),
      ← div_lt_div_iff₀ hwb hwa]
  let ⟨q, hq⟩ := exists_rat_btwn this
  rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hq
  have h₀ : v (b ^ q.den / a ^ q.num) < 1 := by
    have := hq.1
    rwa [div_lt_div_iff₀ (Real.log_pos ha) (by simp only [Nat.cast_pos, q.den_pos]), mul_comm,
      ← Real.log_pow, ← Real.log_zpow, Real.log_lt_log_iff (pow_pos (by linarith) _)
      (zpow_pos (by linarith) _), ← div_lt_one (zpow_pos (by linarith) _),
      ← map_pow, ← map_zpow₀, ← map_div₀] at this
  have h₁ : 1 < w (b ^ q.den / a ^ q.num) := by
    have hwa := (one_lt_iff_of_lt_one_iff h _).1 ha
    have := hq.2
    rwa [div_lt_div_iff₀ (by simp only [Nat.cast_pos, q.den_pos]) (Real.log_pos hwa),
      mul_comm (Real.log (w _)), ← Real.log_pow, ← Real.log_zpow,
      Real.log_lt_log_iff (zpow_pos (by linarith) _)
      (pow_pos (by linarith [(one_lt_iff_of_lt_one_iff h _).1 hb₁]) _),
      ← one_lt_div (zpow_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at this
  exact not_lt_of_lt ((h _).1 h₀) h₁

theorem exists_rpow_of_one_lt {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (h : ∀ x, v x < 1 ↔ w x < 1) :
    ∃ (t : ℝ) (_ : 0 < t), ∀ x, 1 < v x → w x ^ t = v x := by
  obtain ⟨a, ha, hlog⟩ := log_div_image_eq_singleton_of_le_one_iff hv h
  refine ⟨Real.log (v a) / Real.log (w a),
    div_pos (Real.log_pos ha) (Real.log_pos ((one_lt_iff_of_lt_one_iff h a).1 ha)), fun b hb => ?_⟩
  simp_rw [← hlog b hb]
  letI := (one_lt_iff_of_lt_one_iff h b).1 hb
  rw [div_eq_inv_mul, Real.rpow_mul (w.nonneg _), Real.rpow_inv_log (by linarith) (by linarith),
    Real.exp_one_rpow, Real.exp_log (by linarith)]

open Real in
/--
If $v$ and $w$ be two real absolute values on a field $F$, where $v$ is non-trivial, then $v$ and
$w$ are equivalent if and only if $v(x) < 1$ exactly when $w(x) < 1$.
-/
theorem isEquiv_iff_lt_one_iff {v : AbsoluteValue F ℝ} (w : AbsoluteValue F ℝ)
    (hv : v.IsNontrivial) : w.IsEquiv v ↔ (∀ x, v x < 1 ↔ w x < 1) := by
  refine ⟨fun ⟨t, ht, h⟩ x => h ▸ (Real.rpow_lt_one_iff' (w.nonneg x) ht), fun h => ?_⟩
  obtain ⟨t, ht, hsuff⟩ := exists_rpow_of_one_lt hv h
  refine ⟨t, ht, funext fun x => ?_⟩
  by_cases h₀ : v x = 0
  · rw [(map_eq_zero v).1 h₀, map_zero, map_zero, zero_rpow (by linarith)]
  · by_cases h₁ : v x = 1
    · rw [h₁, (eq_one_iff_of_lt_one_iff h x).1 h₁, one_rpow]
    · by_cases h₂ : 0 < v x ∧ v x < 1
      · rw [← inv_inj, ← map_inv₀ v, ← hsuff _ (map_inv₀ v _ ▸ one_lt_inv_iff₀.2 h₂), map_inv₀,
          inv_rpow (w.nonneg _)]
      · rw [← one_lt_inv_iff₀, ← map_inv₀, not_lt] at h₂
        rw [← ne_eq, ← inv_ne_one, ← map_inv₀] at h₁
        exact hsuff _ <| (inv_lt_one_iff.1 <| lt_of_le_of_ne h₂ h₁).resolve_left
          ((map_ne_zero v).1 h₀)

/--
If $v$ and $w$ are inequivalent absolute values and $v$ is non-trivial, then we can find an $a ∈ F$
such that $v(a) < 1$ while $1 ≤ w(a)$.
-/
theorem exists_lt_one_one_le_of_not_isEquiv {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (h : ¬w.IsEquiv v) :
    ∃ a : F, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact isEquiv_iff_lt_one_iff _ hv |>.2 <| fun  _ => lt_one_iff_of_lt_one_imp hv h

/--
If $v$ and $w$ are two non-trivial and inequivalent absolute values then
we can find an $a ∈ K$ such that $1 < v a$ while $w a < 1$.
-/
theorem exists_one_lt_lt_one_of_not_isEquiv {v w : AbsoluteValue F ℝ} (hv : v.IsNontrivial)
    (hw : w.IsNontrivial) (h : ¬w.IsEquiv v) :
    ∃ a : F, 1 < v a ∧ w a < 1 := by
  let ⟨a, ha⟩ := exists_lt_one_one_le_of_not_isEquiv hv h
  let ⟨b, hb⟩ := exists_lt_one_one_le_of_not_isEquiv hw (mt isEquiv_symm h)
  refine ⟨b / a, ?_⟩
  simpa using ⟨one_lt_div (pos_of_pos v (by linarith)) |>.2 (by linarith),
    div_lt_one (by linarith) |>.2 (by linarith)⟩

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
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_sub h_add (v.one_sub_pow_le _)
    (v.one_add_pow_le _)

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
  refine tendsto_atTop_of_geom_le (by simp only [pow_zero, inv_one, zero_lt_one]) ha fun n => ?_
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
  replace haj := map_inv₀ (v j) _ ▸ (one_lt_inv₀ (pos_of_pos (v j) (by linarith))).2 (haj j hj)
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
    let ⟨a, ha⟩ := (v 0).exists_one_lt_lt_one_of_not_isEquiv (h 0) (h 1) (hv zero_ne_one.symm)
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
