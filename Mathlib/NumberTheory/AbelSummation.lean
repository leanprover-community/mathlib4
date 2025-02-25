/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Order.IsLocallyClosed

/-!
# Abel's summation formula

We prove several versions of Abel's summation formula.

## Results

* `sum_mul_eq_sub_sub_integral_mul`: general statement of the formula for a sum between two
  (nonnegative) reals `a` and `b`.

* `sum_mul_eq_sub_integral_mul`: a specialized version of `sum_mul_eq_sub_sub_integral_mul` for
  the case `a = 0`.

* `sum_mul_eq_sub_integral_mul₀`: a specialized version of `sum_mul_eq_sub_integral_mul` for
  when the first coefficient of the sequence is `0`. This is useful for `ArithmeticFunction`.

Primed versions of the three results above are also stated for when the endpoints are `Nat`.

* `tendsto_sum_mul_atTop_nhds_one_sub_integral`: limit version of `sum_mul_eq_sub_integral_mul`
  when `a` tends to `∞`.

* `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`: limit version of `sum_mul_eq_sub_integral_mul₀`
  when `a` tends to `∞`.

* `summable_mul_of_bigO_atTop`: let `c : ℕ → 𝕜` and `f : ℝ → 𝕜` with `𝕜 = ℝ` or `ℂ`, prove the
  summability of `n ↦ (c n) * (f n)` using Abel's formula under some `bigO` assumptions at infinity.

## References

* <https://en.wikipedia.org/wiki/Abel%27s_summation_formula>

-/

noncomputable section

open Finset MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] (c : ℕ → 𝕜) {f : ℝ → 𝕜} {a b : ℝ}

namespace abelSummationProof

open intervalIntegral IntervalIntegrable

private theorem sumlocc {m : ℕ} (n : ℕ) :
    ∀ᵐ t, t ∈ Set.Icc (n : ℝ) (n + 1) → ∑ k ∈ Icc m ⌊t⌋₊, c k = ∑ k ∈ Icc m n, c k := by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]

private theorem integralmulsum (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) (t₁ t₂ : ℝ) (n : ℕ) (h : t₁ ≤ t₂)
    (h₁ : n ≤ t₁) (h₂ : t₂ ≤ n + 1) (h₃ : a ≤ t₁) (h₄ : t₂ ≤ b) :
    ∫ t in t₁..t₂, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
      (f t₂ - f t₁) * ∑ k ∈ Icc 0 n, c k := by
  have h_inc₁ : Ι t₁ t₂ ⊆ Set.Icc n (n + 1) :=
    Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc h₁ h₂
  have h_inc₂ : Set.uIcc t₁ t₂ ⊆ Set.Icc a b := Set.uIcc_of_le h ▸ Set.Icc_subset_Icc h₃ h₄
  rw [← integral_deriv_eq_sub (fun t ht ↦ hf_diff t (h_inc₂ ht)), ← integral_mul_const]
  · refine integral_congr_ae ?_
    filter_upwards [sumlocc c n] with t h h'
    rw [h (h_inc₁ h')]
  · refine (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (hf_int.mono_set ?_)
    rwa [← Set.uIcc_of_le h]

private theorem ineqofmemIco {k : ℕ} (hk : k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  constructor
  · have := (Set.mem_Ico.mp hk).1
    exact le_of_lt <| (Nat.floor_lt' (by omega)).mp this
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

private theorem ineqofmemIco' {k : ℕ} (hk : k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b :=
  ineqofmemIco (by rwa [← Finset.coe_Ico])

theorem _root_.integrableOn_mul_sum_Icc {m : ℕ} (ha : 0 ≤ a) {g : ℝ → 𝕜}
    (hg_int : IntegrableOn g (Set.Icc a b)) :
    IntegrableOn (fun t ↦ g t * ∑ k ∈ Icc m ⌊t⌋₊, c k) (Set.Icc a b) := by
  obtain hab | hab := le_or_gt a b
  · obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
    · have : ∀ᵐ t, t ∈ Set.Icc a b → ∑ k ∈ Icc m ⌊a⌋₊, c k = ∑ k ∈ Icc m ⌊t⌋₊, c k := by
        filter_upwards [sumlocc c ⌊a⌋₊] with t ht₁ ht₂
        rw [ht₁ ⟨(Nat.floor_le ha).trans ht₂.1, hb ▸ ht₂.2.trans (Nat.lt_floor_add_one b).le⟩]
      rw [← ae_restrict_iff' measurableSet_Icc] at this
      exact IntegrableOn.congr_fun_ae
        (hg_int.mul_const _) ((Filter.EventuallyEq.refl _ g).mul this)
    · have h_locint {t₁ t₂ : ℝ} {n : ℕ} (h : t₁ ≤ t₂) (h₁ : n ≤ t₁) (h₂ : t₂ ≤ n + 1)
          (h₃ : a ≤ t₁) (h₄ : t₂ ≤ b) :
          IntervalIntegrable (fun t ↦ g t * ∑ k ∈ Icc m ⌊t⌋₊, c k) volume t₁ t₂ := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le h]
        exact (IntegrableOn.mono_set (hg_int.mul_const _) (Set.Icc_subset_Icc h₃ h₄)).congr
          <| ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc h₁ h₂)
            <| (ae_restrict_iff' measurableSet_Icc).mpr
              (by filter_upwards [sumlocc c n] with t h ht using by rw [h ht])
      have aux1 : 0 ≤ b := (Nat.pos_of_floor_pos <| (Nat.zero_le _).trans_lt hb).le
      have aux2 : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one, ← Nat.le_floor_iff aux1]
      have aux3 : a ≤ ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
      have aux4 : a ≤ ⌊b⌋₊ := le_of_lt (by rwa [← Nat.floor_lt ha])
      -- now break up into 3 subintervals
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (aux3.trans aux2)]
      have I1 : IntervalIntegrable _ volume a ↑(⌊a⌋₊ + 1) :=
        h_locint (mod_cast aux3) (Nat.floor_le ha) (mod_cast le_rfl) le_rfl (mod_cast aux2)
      have I2 : IntervalIntegrable _ volume ↑(⌊a⌋₊ + 1) ⌊b⌋₊ :=
        trans_iterate_Ico hb fun k hk ↦ h_locint (mod_cast k.le_succ)
          le_rfl (mod_cast le_rfl) (ineqofmemIco hk).1 (mod_cast (ineqofmemIco hk).2)
      have I3 : IntervalIntegrable _ volume ⌊b⌋₊ b :=
        h_locint (Nat.floor_le aux1) le_rfl (Nat.lt_floor_add_one _).le aux4 le_rfl
      exact (I1.trans I2).trans I3
  · rw [Set.Icc_eq_empty_of_lt hab]
    exact integrableOn_empty

/-- Abel's summation formula. -/
theorem _root_.sum_mul_eq_sub_sub_integral_mul (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc a b)) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - f a * (∑ k ∈ Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  rw [← integral_of_le hab]
  have aux1 : ⌊a⌋₊ ≤ a := Nat.floor_le ha
  have aux2 : b ≤ ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  -- We consider two cases depending on whether the sum is empty or not
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_rfl, sum_empty, ← sub_mul,
      integralmulsum c hf_diff hf_int _ _ ⌊b⌋₊ hab (hb ▸ aux1) aux2 le_rfl le_rfl, sub_self]
  have aux3 : a ≤ ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  have aux4 : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one,  ← Nat.le_floor_iff (ha.trans hab)]
  have aux5 : ⌊b⌋₊ ≤ b := Nat.floor_le (ha.trans hab)
  have aux6 : a ≤ ⌊b⌋₊ := Nat.floor_lt ha |>.mp hb |>.le
  simp_rw [← smul_eq_mul, sum_Ioc_by_parts (fun k ↦ f k) _ hb, range_eq_Ico,
    Ico_add_one_right_eq_Icc, smul_eq_mul]
  have : ∑ k ∈ Ioc ⌊a⌋₊ (⌊b⌋₊ - 1), (f ↑(k + 1) - f k) * ∑ n ∈ Icc 0 k, c n =
        ∑ k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊, ∫ t in k..↑(k + 1), deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n := by
    rw [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (by omega), Eq.comm]
    exact sum_congr rfl fun k hk ↦ (integralmulsum c hf_diff hf_int _ _ _  (mod_cast k.le_succ)
      le_rfl (mod_cast le_rfl) (ineqofmemIco' hk).1 <| mod_cast (ineqofmemIco' hk).2)
  rw [this, sum_integral_adjacent_intervals_Ico hb, Nat.cast_add, Nat.cast_one,
    ← integral_interval_sub_left (a := a) (c := ⌊a⌋₊ + 1),
    ← integral_add_adjacent_intervals (b := ⌊b⌋₊) (c := b),
    integralmulsum c hf_diff hf_int _ _ _ aux3 aux1 le_rfl le_rfl aux4,
    integralmulsum c hf_diff hf_int _ _ _ aux5 le_rfl aux2 aux6 le_rfl]
  · ring
  -- now deal with the integrability side goals
  -- (Note we have 5 goals, but the 1st and 3rd are identical. TODO: find a non-hacky way of dealing
  -- with both at once.)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux5]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_left aux6)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux3]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux4)
  · exact fun k hk ↦ (intervalIntegrable_iff_integrableOn_Icc_of_le (mod_cast k.le_succ)).mpr
      <| (integrableOn_mul_sum_Icc c ha hf_int).mono_set
        <| (Set.Icc_subset_Icc_iff (mod_cast k.le_succ)).mpr <| mod_cast (ineqofmemIco hk)

/-- A version of `sum_mul_eq_sub_sub_integral_mul` where the endpoints are `Nat`. -/
theorem _root_.sum_mul_eq_sub_sub_integral_mul' {n m : ℕ} (h : n ≤ m)
    (hf_diff : ∀ t ∈ Set.Icc (n : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (n : ℝ) m)) :
    ∑ k ∈ Ioc n m, f k * c k =
      f m * (∑ k ∈ Icc 0 m, c k) - f n * (∑ k ∈ Icc 0 n, c k) -
        ∫ t in Set.Ioc (n : ℝ) m, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  convert sum_mul_eq_sub_sub_integral_mul c n.cast_nonneg (Nat.cast_le.mpr h) hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

end abelSummationProof

section specialversions

/-- Specialized version of `sum_mul_eq_sub_sub_integral_mul` for the case `a = 0` -/
theorem sum_mul_eq_sub_integral_mul {b : ℝ} (hb : 0 ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc 0 b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 0 b)) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 0 b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _)]
  rw [sum_cons, ← Nat.floor_zero (α := ℝ), sum_mul_eq_sub_sub_integral_mul c le_rfl hb hf_diff
    hf_int, Nat.floor_zero, Nat.cast_zero, Icc_self, sum_singleton]
  ring

/-- A version of `sum_mul_eq_sub_integral_mul` where the endpoint is a `Nat`. -/
theorem sum_mul_eq_sub_integral_mul' (m : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (0 : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (0 : ℝ) m)) :
    ∑ k ∈ Icc 0 m, f k * c k =
      f m * (∑ k ∈ Icc 0 m, c k) -
        ∫ t in Set.Ioc (0 : ℝ) m, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  convert sum_mul_eq_sub_integral_mul c m.cast_nonneg hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

/-- Specialized version of `sum_mul_eq_sub_integral_mul` when the first coefficient of the sequence
`c` is equal to `0`. -/
theorem sum_mul_eq_sub_integral_mul₀ (hc : c 0 = 0) (b : ℝ)
    (hf_diff : ∀ t ∈ Set.Icc 1 b, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc 1 b)) :
    ∑ k ∈ Icc 0 ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∫ t in Set.Ioc 1 b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  obtain hb | hb := le_or_gt 1 b
  · have : 1 ≤ ⌊b⌋₊ := (Nat.one_le_floor_iff _).mpr hb
    nth_rewrite 1 [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, ← Icc_add_one_left_eq_Ioc,
      Icc_eq_cons_Ioc (by omega), sum_cons]
    rw [zero_add, ← Nat.floor_one (α := ℝ),
      sum_mul_eq_sub_sub_integral_mul c zero_le_one hb hf_diff hf_int, Nat.floor_one, Nat.cast_one,
      Icc_eq_cons_Ioc zero_le_one, sum_cons, show 1 = 0 + 1 by rfl, Nat.Ioc_succ_singleton,
      zero_add, sum_singleton, hc, mul_zero, zero_add]
    ring
  · simp_rw [Nat.floor_eq_zero.mpr hb, Icc_self, sum_singleton, Nat.cast_zero, hc, mul_zero,
      Set.Ioc_eq_empty_of_le hb.le, Measure.restrict_empty, integral_zero_measure, sub_self]

/-- A version of `sum_mul_eq_sub_integral_mul₀` where the endpoint is a `Nat`. -/
theorem sum_mul_eq_sub_integral_mul₀' (hc : c 0 = 0) (m : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) m)) :
    ∑ k ∈ Icc 0 m, f k * c k =
      f m * (∑ k ∈ Icc 0 m, c k) -
        ∫ t in Set.Ioc (1 : ℝ) m, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  convert sum_mul_eq_sub_integral_mul₀ c hc m hf_diff hf_int
  all_goals rw [Nat.floor_natCast]

end specialversions

section limit

open Filter Topology abelSummationProof intervalIntegral

theorem locallyIntegrableOn_mul_sum_Icc {m : ℕ} (ha : 0 ≤ a) {g : ℝ → 𝕜}
    (hg : LocallyIntegrableOn g (Set.Ici a)) :
    LocallyIntegrableOn (fun t ↦ g t * ∑ k ∈ Icc m ⌊t⌋₊, c k) (Set.Ici a) := by
  refine (locallyIntegrableOn_iff isLocallyClosed_Ici).mpr fun K hK₁ hK₂ ↦ ?_
  by_cases hK₃ : K.Nonempty
  · have h_inf : a ≤ sInf K := (hK₁ (hK₂.sInf_mem hK₃))
    refine IntegrableOn.mono_set ?_ (Bornology.IsBounded.subset_Icc_sInf_sSup hK₂.isBounded)
    refine integrableOn_mul_sum_Icc _ (ha.trans h_inf) ?_
    refine hg.integrableOn_compact_subset ?_ isCompact_Icc
    exact (Set.Icc_subset_Ici_iff (Real.sInf_le_sSup _ hK₂.bddBelow hK₂.bddAbove)).mpr h_inf
  · rw [Set.not_nonempty_iff_eq_empty.mp hK₃]
    exact integrableOn_empty

theorem tendsto_sum_mul_atTop_nhds_one_sub_integral
    (hf_diff : ∀ t ∈ Set.Ici 0, DifferentiableAt ℝ f t)
    (hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 0)) {l : 𝕜}
    (h_lim : Tendsto (fun n : ℕ ↦ f n * ∑ k ∈ Icc 0 n, c k) atTop (𝓝 l))
    {g : ℝ → 𝕜} (hg_dom : (fun t ↦ deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] g)
    (hg_int : IntegrableAtFilter g atTop) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k * c k) atTop
      (𝓝 (l - ∫ t in Set.Ioi 0, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) := by
  have h_lim' : Tendsto (fun n : ℕ ↦ ∫ t in Set.Ioc (0 : ℝ) n, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)
      atTop (𝓝 (∫ t in Set.Ioi 0, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) := by
    refine Tendsto.congr (fun _ ↦ by rw [← integral_of_le (Nat.cast_nonneg _)]) ?_
    refine intervalIntegral_tendsto_integral_Ioi _ ?_ tendsto_natCast_atTop_atTop
    exact integrableOn_Ici_iff_integrableOn_Ioi.mp
      <| (locallyIntegrableOn_mul_sum_Icc c le_rfl hf_int).integrableOn_of_isBigO_atTop
        hg_dom hg_int
  refine (h_lim.sub h_lim').congr (fun _ ↦ ?_)
  rw [sum_mul_eq_sub_integral_mul' _ _ (fun t ht ↦ hf_diff _ ht.1)]
  exact hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc

theorem tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (hc : c 0 = 0)
    (hf_diff : ∀ t ∈ Set.Ici 1, DifferentiableAt ℝ f t)
    (hf_int : LocallyIntegrableOn (deriv f) (Set.Ici 1)) {l : 𝕜}
    (h_lim: Tendsto (fun n : ℕ ↦ f n * ∑ k ∈ Icc 0 n, c k) atTop (𝓝 l))
    {g : ℝ → ℝ} (hg_dom : (fun t ↦ deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] g)
    (hg_int : IntegrableAtFilter g atTop) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Icc 0 n, f k * c k) atTop
      (𝓝 (l - ∫ t in Set.Ioi 1, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) := by
  have h : (fun n : ℕ ↦ ∫ (x : ℝ) in (1 : ℝ)..n, deriv f x * ∑ k ∈ Icc 0 ⌊x⌋₊, c k) =ᶠ[atTop]
      (fun n : ℕ ↦ ∫ (t : ℝ) in Set.Ioc 1 ↑n, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
    filter_upwards [eventually_ge_atTop 1] with _ h
    rw [← integral_of_le (Nat.one_le_cast.mpr h)]
  have h_lim' : Tendsto (fun n : ℕ ↦ ∫ t in Set.Ioc (1 : ℝ) n, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)
      atTop (𝓝 (∫ t in Set.Ioi 1, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) := by
    refine Tendsto.congr' h (intervalIntegral_tendsto_integral_Ioi _ ?_ tendsto_natCast_atTop_atTop)
    exact integrableOn_Ici_iff_integrableOn_Ioi.mp
      <| (locallyIntegrableOn_mul_sum_Icc c zero_le_one hf_int).integrableOn_of_isBigO_atTop
        hg_dom hg_int
  refine (h_lim.sub h_lim').congr (fun _ ↦ ?_)
  rw [sum_mul_eq_sub_integral_mul₀' _ hc _ (fun t ht ↦ hf_diff _ ht.1)]
  exact hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc

end limit

section summable

open Filter abelSummationProof

private theorem summable_mul_of_bigO_atTop_aux (m : ℕ)
    (h_bdd : (fun n : ℕ ↦ ‖f n‖ * ∑ k ∈ Icc 0 n, ‖c k‖) =O[atTop] fun _ ↦ (1 : ℝ))
    (hf_int : LocallyIntegrableOn (deriv (fun t ↦ ‖f t‖)) (Set.Ici (m : ℝ)))
    (hf : ∀ n : ℕ, ∑ k ∈ Icc 0 n, ‖f k‖ * ‖c k‖ =
      ‖f n‖ * ∑ k ∈ Icc 0 n, ‖c k‖ -
        ∫ (t : ℝ) in Set.Ioc ↑m ↑n, deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖)
    {g : ℝ → ℝ}
    (hg₁ : (fun t ↦ deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : ℕ ↦ f n * c n) := by
  obtain ⟨C₁, hC₁⟩ := Asymptotics.isBigO_one_nat_atTop_iff.mp h_bdd
  let C₂ := ∫ t in Set.Ioi (m : ℝ), ‖deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖‖
  refine summable_of_sum_range_norm_le (c := max (C₁ + C₂) 1) fun n ↦ ?_
  cases n with
  | zero => simp only [range_zero, norm_mul, sum_empty, le_sup_iff, zero_le_one, or_true]
  | succ n =>
      have h_mes : Measurable fun t ↦ deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖ :=
        (measurable_deriv _).mul <| Measurable.comp' (g := fun n : ℕ ↦ ∑ k ∈ Icc 0 n, ‖c k‖)
          (fun _ _ ↦ trivial) Nat.measurable_floor
      rw [Nat.range_eq_Icc_zero_sub_one _ n.add_one_ne_zero, add_tsub_cancel_right]
      calc
        _ = ∑ k ∈ Icc 0 n, ‖f k‖ * ‖c k‖ := by simp_rw [norm_mul]
        _ = ‖f n‖ * ∑ k ∈ Icc 0 n, ‖c k‖ -
              ∫ t in Set.Ioc ↑m ↑n, deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖ := ?_
        _ ≤ C₁ - ∫ t in Set.Ioc ↑m ↑n, deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖ := ?_
        _ ≤ C₁ + ∫ t in Set.Ioc ↑m ↑n, ‖deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖‖ := ?_
        _ ≤ C₁ + C₂ := ?_
        _ ≤ max (C₁ + C₂) 1 := le_max_left _ _
      · exact hf _
      · refine tsub_le_tsub_right (le_of_eq_of_le (Real.norm_of_nonneg ?_).symm (hC₁ n)) _
        exact mul_nonneg (norm_nonneg _) (sum_nonneg fun _ _ ↦ norm_nonneg _)
      · exact add_le_add_left
          (le_trans (neg_le_abs _) (Real.norm_eq_abs _ ▸ norm_integral_le_integral_norm _)) _
      · refine add_le_add_left (setIntegral_mono_set ?_ ?_ Set.Ioc_subset_Ioi_self.eventuallyLE) C₁
        · exact integrableOn_Ici_iff_integrableOn_Ioi.mp <|
            (integrable_norm_iff h_mes.aestronglyMeasurable).mpr <|
              (locallyIntegrableOn_mul_sum_Icc _ m.cast_nonneg hf_int).integrableOn_of_isBigO_atTop
                hg₁ hg₂
        · filter_upwards with t using norm_nonneg _

theorem summable_mul_of_bigO_atTop
    (hf_diff : ∀ t ∈ Set.Ici 0, DifferentiableAt ℝ (fun x ↦ ‖f x‖) t)
    (hf_int : LocallyIntegrableOn (deriv (fun t ↦ ‖f t‖)) (Set.Ici 0))
    (h_bdd : (fun n : ℕ ↦ ‖f n‖ * ∑ k ∈ Icc 0 n, ‖c k‖) =O[atTop] fun _ ↦ (1 : ℝ))
    {g : ℝ → ℝ} (hg₁ : (fun t ↦ deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 0 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : ℕ ↦ f n * c n) := by
  refine summable_mul_of_bigO_atTop_aux c 0 h_bdd (by rwa [Nat.cast_zero]) (fun n ↦ ?_) hg₁ hg₂
  exact_mod_cast sum_mul_eq_sub_integral_mul' _ _ (fun _ ht ↦ hf_diff _ ht.1)
    (hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)

/-- A version of `summable_mul_of_bigO_atTop` that can be useful to avoid difficulties near zero. -/
theorem summable_mul_of_bigO_atTop'
    (hf_diff : ∀ t ∈ Set.Ici 1, DifferentiableAt ℝ (fun x ↦ ‖f x‖) t)
    (hf_int : LocallyIntegrableOn (deriv (fun t ↦ ‖f t‖)) (Set.Ici 1))
    (h_bdd : (fun n : ℕ ↦ ‖f n‖ * ∑ k ∈ Icc 1 n, ‖c k‖) =O[atTop] fun _ ↦ (1 : ℝ))
    {g : ℝ → ℝ} (hg₁ : (fun t ↦ deriv (fun t ↦ ‖f t‖) t * ∑ k ∈ Icc 1 ⌊t⌋₊, ‖c k‖) =O[atTop] g)
    (hg₂ : IntegrableAtFilter g atTop) :
    Summable (fun n : ℕ ↦ f n * c n) := by
  have h : ∀ n, ∑ k ∈ Icc 1 n, ‖c k‖ = ∑ k ∈ Icc 0 n, ‖(fun n ↦ if n = 0 then 0 else c n) k‖ := by
    intro n
    rw [Icc_eq_cons_Ioc n.zero_le, sum_cons, ← Icc_add_one_left_eq_Ioc, zero_add]
    simp_rw [if_pos, norm_zero, zero_add]
    exact Finset.sum_congr rfl fun _ h ↦ by rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp h).1).ne']
  simp_rw [h] at h_bdd hg₁
  refine Summable.congr_atTop (summable_mul_of_bigO_atTop_aux (fun n ↦ if n = 0 then 0 else c n) 1
    h_bdd (by rwa [Nat.cast_one]) (fun n ↦ ?_) hg₁ hg₂) ?_
  · exact_mod_cast sum_mul_eq_sub_integral_mul₀' _ (by simp only [reduceIte, norm_zero]) n
      (fun _ ht ↦ hf_diff _ ht.1)
      (hf_int.integrableOn_compact_subset Set.Icc_subset_Ici_self isCompact_Icc)
  · filter_upwards [eventually_ne_atTop 0] with k hk
    simp_rw [if_neg hk]

end summable
