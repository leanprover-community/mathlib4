/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib

open Filter Nat Real Finset
open Asymptotics
open MeasureTheory

set_option linter.style.longLine false

attribute [bound] tsum_nonneg ArithmeticFunction.vonMangoldt_nonneg sum_nonneg
section fun_prop

@[fun_prop]
theorem MeasureTheory.AEStronglyMeasurable.mul' {α : Type*} {β : Type*} [TopologicalSpace β] {m₀ : MeasurableSpace α} {mu : Measure α} {f g : α → β} [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f mu) (hg : AEStronglyMeasurable g mu) :
    AEStronglyMeasurable (fun x ↦ f x * g x) mu := hf.mul hg

@[fun_prop]
theorem MeasureTheory.AEStronglyMeasurable.inv' {α : Type*} {β : Type*} [TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measure α} {f : α → β} [Inv β] [ContinuousInv β] (hf : AEStronglyMeasurable f μ) :
AEStronglyMeasurable (fun x ↦ (f x)⁻¹) μ := hf.inv

@[fun_prop]
theorem MeasureTheory.AEStronglyMeasurable.pow' {α : Type*} {β : Type*} [TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measure α} {f : α → β} [Monoid β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (n : ℕ) :
    AEStronglyMeasurable (fun x ↦ f x ^ n) μ := hf.pow n

attribute [fun_prop] measurable_log Measurable.aestronglyMeasurable

end fun_prop


section MeasureTheory
variable {α : Type*} {E : Type*} {F : Type*} [TopologicalSpace α] [Norm E] [Norm F]

def Asymptotics.IsLocallyBigO  (l : Filter α) (f : α → E) (g : α → F) :
  Prop :=
  ∀ᶠ x in l, f =O[l ⊓ (nhds x)] g

example : cocompact α ⊔ sSup (nhds '' Set.univ) = ⊤ := by
  rw [← nhdsSet_univ, nhdsSet]
  sorry

example (f : α → E) (g : α → F) (l : Filter α) (h : f =O[cocompact α] g) (h' : IsLocallyBigO ⊤ f g) :
  f =O[⊤] g := by
  obtain ⟨c, h⟩ := h.isBigOWith
  rw [IsBigOWith, Filter.Eventually, mem_cocompact] at h
  obtain ⟨t, ht, htc⟩ := h
  rw [IsLocallyBigO] at h'
  simp only [le_top, inf_of_le_right, eventually_top, ]  at h'
  simp only [IsBigO, IsBigOWith, Filter.eventually_iff_exists_mem] at h'
  choose C h using h'
  choose U hU hU' using h
  obtain ⟨s, hs, ht_sub⟩ := ht.elim_nhds_subcover U (fun x _ ↦ hU x)
  by_cases hs_empty : s = ∅
  · simp_all
    have (x : α) := Set.mem_univ x
    simp [← htc] at this
    exact ⟨c, this⟩
  simp only at hs_empty
  simp only [isBigO_top]
  use max c (s.sup' (Finset.nonempty_of_ne_empty hs_empty) C )
  --yes this works but the proof needs polishing
  sorry



open Bornology
example (f g : ℝ → ℝ) (l : Filter ℝ) (h : f =O[cocompact ℝ ⊓ l] g) (hg : (fun _ ↦ (1:ℝ)) =O[l] g) (h : (cobounded ℝ).comap f ≤ cobounded ℝ) :
    f =O[l] g := by

  sorry

theorem integrableAtFilter_principal_iff
  {α : Type*} {E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E} {S : Set α} {mu : Measure α}  :
  IntegrableAtFilter f (𝓟 S) mu ↔ IntegrableOn f S mu := by
  rw [IntegrableAtFilter]
  simp only [mem_principal]
  refine ⟨fun ⟨s, hsS, hfs⟩ ↦ hfs.mono hsS le_rfl, fun h ↦ ⟨S, le_rfl, h⟩⟩

theorem MeasureTheory.IntegrableAtFilter.integrableOn_of_principal
    {α : Type*} {E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E} {S : Set α} {mu : Measure α}
    (h : IntegrableAtFilter f (𝓟 S) mu) : IntegrableOn f S mu :=
  integrableAtFilter_principal_iff.mp h

theorem MeasureTheory.IntegrableOn.integrableAtFilter
    {α : Type*} {E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {f : α → E} {S : Set α} {mu : Measure α}
    (h : IntegrableOn f S mu) : IntegrableAtFilter f (𝓟 S) mu :=
  integrableAtFilter_principal_iff.mpr h

theorem IsBigO.set_integral_isBigO {α E F : Type*} [NormedAddCommGroup E] {l : Filter α} {ι : Type*} [MeasurableSpace ι] {f g : ι × α → ℝ} {s : Set ι} {μ : Measure ι}  [NormedSpace ℝ E] [NormedAddCommGroup F]
    (hf : f =O[𝓟 s ×ˢ l] g) (hg : (∀ i ∈ s, ∀ x, 0 ≤ g (i, x))) (hs : MeasurableSet s):
    (fun x ↦ ∫ i in s, f (i, x) ∂μ) =O[l] (fun x ↦ ∫ i in s, g (i, x) ∂μ) := by
  obtain ⟨C, hC⟩ := hf.bound
  obtain ⟨t, htl, ht⟩ := hC.exists_mem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp htl
  refine isBigO_iff.mpr ⟨C, eventually_iff_exists_mem.mpr ⟨v, hv, fun x hx ↦ ?_⟩⟩

  -- rw [← smul_eq_mul (a' := ‖g x‖), ← MeasureTheory.Measure.restrict_apply_univ,
  --   ← integral_const, mul_comm, ← smul_eq_mul, ← integral_smul_const]
  -- haveI : IsFiniteMeasure (μ.restrict s) := ⟨by rw [Measure.restrict_apply_univ s]; exact hμ⟩
  refine (norm_integral_le_integral_norm _).trans <| ?_
  simp only [norm_eq_abs]
  rw [abs_of_nonneg (setIntegral_nonneg hs (fun i h ↦ hg i h x)), ← smul_eq_mul, ← integral_smul]
  gcongr
  · sorry

  -- filter_upwards [MeasureTheory.self_mem_ae_restrict hs]
  · sorry
  · sorry
  -- intro y hy
  -- rw [smul_eq_mul, mul_comm]
  -- exact ht (y, x) <| huv ⟨hu hy, hx⟩
theorem MeasureTheory.setIntegral_mono_on' {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} {s : Set X} (hf : Measurable f) (hg : IntegrableOn g s μ)
    (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ g x) :
    ∫ (x : X) in s, f x ∂μ ≤ ∫ (x : X) in s, g x ∂μ := by
  sorry

end MeasureTheory

open scoped ArithmeticFunction

axiom hpsi_cheby : (fun n => ∑ k ∈ Finset.range (n+1), Λ k) =O[atTop] (fun n ↦ (n:ℝ))

theorem ArithmeticFunction.sum_range_mul_zeta
    {R : Type*} [Semiring R] (f : ArithmeticFunction R) (N : ℕ) :
    ∑ d in range (N + 1), (f * ζ) d = ∑ d in range (N + 1), (N / d) • f d := by
  induction N with
  | zero => simp
  | succ n h_ind =>
    rw [Finset.sum_range_succ]
    simp_rw [Nat.succ_div, add_smul, Finset.sum_add_distrib, h_ind]
    congr 1
    · apply Finset.sum_subset
      · refine range_subset.mpr (le_succ _)
      · simp only [mem_range, not_lt, nsmul_eq_mul]
        intro d hd1 hd2
        obtain rfl : d = n+1 := by omega
        apply mul_eq_zero_of_left
        convert cast_zero
        simp only [Nat.div_eq_zero_iff, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
          lt_add_iff_pos_right, zero_lt_one, or_true]
    · simp_rw [boole_smul, ← Finset.sum_filter]
      rw [Nat.filter_dvd_eq_divisors (add_one_ne_zero n)]
      exact coe_mul_zeta_apply

theorem log_stirling :
  Tendsto (fun n => Real.log (n)!
    - (n * Real.log n - n + Real.log n / 2 + Real.log π / 2 + Real.log 2 / 2))
    atTop (nhds 0) := by
  have :=  Stirling.factorial_isEquivalent_stirling
  rw [Asymptotics.isEquivalent_iff_tendsto_one ?case] at this
  case case =>
    filter_upwards [eventually_ge_atTop 1]
    intro n hn
    positivity
  have tendsto_log_one_zero : Tendsto Real.log (nhds 1) (nhds 0) := by
    convert ContinuousAt.tendsto ?_
    · simp only [log_one]
    · simp only [continuousAt_log_iff, ne_eq, one_ne_zero, not_false_eq_true]
  apply  (tendsto_log_one_zero.comp this).congr'
  filter_upwards [eventually_ne_atTop 0]
  intro n hn
  have hsqrt_pi : √π ≠ 0 := by
    simp [Real.pi_nonneg, Real.pi_ne_zero]
  simp only [ofNat_pos, mul_nonneg_iff_of_pos_left, cast_nonneg, ofNat_nonneg,
    Function.comp_apply, Pi.div_apply]
  rw [Real.log_div (by positivity) (by simp [hn, hsqrt_pi])]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_div (by positivity) (by positivity)]
  simp only [log_exp, sub_right_inj]
  ring

theorem multiplicity_factorial
    {p : ℕ} (hp : Nat.Prime p) {n b : ℕ} (hlog : Nat.log p n < b) :
    multiplicity p n.factorial = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  apply multiplicity_eq_of_emultiplicity_eq_some
  exact Prime.emultiplicity_factorial hp hlog

theorem factorization_factorial
    {p : ℕ} (hp : Nat.Prime p) {n b : ℕ} (hlog : Nat.log p n < b) :
    n.factorial.factorization p = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  rw [← multiplicity_factorial hp hlog]
  refine Eq.symm (multiplicity_eq_factorization hp (factorial_ne_zero n))

theorem isBigO_pow_right_of_le {a b : ℕ} (h : a ≤ b) :
    (fun (x:ℝ) ↦ x^a) =O[atTop]  (fun x ↦ x^b) := by
  refine Eventually.isBigO ?_
  filter_upwards [Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop 0]
  intro x hx hx'
  simp only [norm_pow, norm_eq_abs, abs_of_nonneg hx']
  gcongr
  exact hx

example : (fun _ ↦ 1 : ℝ → ℝ) =O[atTop] (fun x ↦ (x : ℝ)) := by
  convert isBigO_pow_right_of_le zero_le_one with x
  simp


/- One pain point I'm running into here is finding the right theorems in the library - say I need a
IsBigO statement but it's phrased as IsLittleO in the library. Things like natCast_atTop also make
exact? and the like less useful.
-/
theorem log_fac_sub_id_mul_log_isBigO_id :
    (fun n ↦ Real.log (n !) - n * Real.log n) =O[atTop] (fun n ↦ (n:ℝ)) := by
  have hstirling := log_stirling
  rw [← Asymptotics.isLittleO_one_iff ℝ] at hstirling
  have : (fun _ ↦ 1 : ℝ → ℝ) =O[atTop] (fun x ↦ (x : ℝ)) := by
    convert isBigO_pow_right_of_le zero_le_one with x
    simp
  have const_isBigO (c : ℝ) : (fun (_ : ℕ) ↦ c) =O[atTop] (fun (n : ℕ) ↦ (n : ℝ)) := by
    convert (this.const_mul_left c).natCast_atTop
    simp only [mul_one]
  have hlog : Real.log =O[atTop] id := by
    exact Real.isLittleO_log_id_atTop.isBigO
  have hlarger := hstirling.isBigO.trans (const_isBigO 1).natCast_atTop
  have hrfl : (fun (n : ℕ) ↦ (n : ℝ)) =O[atTop] (fun (n : ℕ) ↦ (n : ℝ)) :=
    Asymptotics.isBigO_refl (α := ℕ) (fun n ↦ (n:ℝ)) atTop
  convert ((hlarger.sub hrfl).add (const_isBigO (Real.log π / 2 + Real.log 2 / 2))).add
    (hlog.const_mul_left (1/2) |>.natCast_atTop) using 1
  ext x
  ring





-- theorem factorial_eq_prod {n : ℕ} :
--   n ! = ∏ p in primesBelow (n+1), p ^ (

-- This is another general result about convolutions :
-- ∑ (k <= n), (1*f) k =  ∑ (k <= n), (n/d) * f d
-- Not currently in mathlib, in PNT+:
-- https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/fea8d484879ed4697fcbb22cae90d9a127c93fb5/PrimeNumberTheoremAnd/Mathlib/NumberTheory/ArithmeticFunction.lean#L17


theorem Real.log_factorial (n : ℕ) :
  Real.log (n)! = ∑ k ∈ Finset.range (n+1), Real.log k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by norm_cast) (mod_cast Nat.factorial_ne_zero n), sum_range_succ, add_comm, ih]
  -- stop
  -- rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod, Real.log_prod]
  -- · apply Finset.sum_subset
  --   · intro x
  --     simp
  --   · simp only [mem_range, mem_Ico, not_and, not_lt, log_eq_zero, cast_eq_zero, cast_eq_one]
  --     omega
  -- simp only [mem_Ico, ne_eq, cast_eq_zero, and_imp]
  -- omega

theorem log_factorial (n : ℕ) :
  Real.log (n)! = ∑ d ∈ Finset.range (n+1), ↑(n / d) * Λ d := by
  simp_rw [Real.log_factorial, ← ArithmeticFunction.log_apply, ← ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.sum_range_mul_zeta, nsmul_eq_mul]
  -- induction n with
  -- | zero => simp
  -- | succ n h_ind =>
  --   rw [Nat.factorial_succ]
  --   push_cast
  --   rw [mul_comm, Real.log_mul (by positivity) (by norm_cast)]
  --   simp_rw [Nat.succ_div, cast_add, add_mul, Finset.sum_add_distrib, h_ind]
  --   congr 1
  --   · apply Finset.sum_subset
  --     · intro d hd
  --       simp at hd ⊢
  --       omega
  --     intro d hd hdnin
  --     obtain rfl : d = n+1 := by
  --       simp_all
  --       omega
  --     simp only [_root_.mul_eq_zero, cast_eq_zero, Nat.div_eq_zero_iff,
  --       AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, lt_add_iff_pos_right, zero_lt_one,
  --       or_true, true_or]
  --   · push_cast
  --     simp_rw [boole_mul, ← Finset.sum_filter]
  --     rw [Nat.filter_dvd_eq_divisors (add_one_ne_zero n)]
  --     exact_mod_cast ArithmeticFunction.vonMangoldt_sum.symm



theorem sum_floor_mul_vonmangoldt (n : ℕ) : ∑ d ∈ Finset.range (n+1), ↑(n / d) * Λ d =
  n * ∑ d ∈ Finset.range (n+1), Λ d / d + ∑ d ∈ Finset.range (n+1), (↑(n/d) - n/d) * Λ d := by
  rw [mul_sum, ← sum_add_distrib]
  congr 1 with d
  ring
-- Nat.Prime.emultiplicity_factorial
-- Nat.multiplicity_eq_factorization
-- emultiplicity_eq_iff_multiplicity_eq_of_ne_one




theorem floor_approx (x : ℝ) (hx : 0 ≤ x) : |↑((Nat.floor x)) - x| ≤ 1  := by
  rw [abs_le]
  refine ⟨by linarith [Nat.lt_floor_add_one x], by linarith [Nat.floor_le hx]⟩

theorem abs_natCast_div_sub_div_le_one {n d : ℕ}: |(↑(n/d) - n/d:ℝ)| ≤ 1 := by
  rw [← Nat.floor_div_eq_div (α := ℝ)]
  apply floor_approx
  positivity

theorem sum_integer_mul_vonMangoldt : (fun n ↦ ∑ d ∈ Finset.range (n+1), (↑(n/d) - n/d) * Λ d)
    =O[atTop] (fun n ↦ (n : ℝ)) := by
  calc
    _ =O[atTop] (fun n ↦ ∑ d ∈ Finset.range (n+1), 1 * Λ d)  := by
      apply Filter.Eventually.isBigO
      filter_upwards
      intro n
      simp only [norm_eq_abs, eventually_atTop, ge_iff_le]
      apply (abs_sum_le_sum_abs ..).trans _
      gcongr with d hd
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      gcongr
      · exact ArithmeticFunction.vonMangoldt_nonneg
      · exact abs_natCast_div_sub_div_le_one
    _ =O[atTop] _ := by
      simp only [one_mul]
      exact hpsi_cheby

-- n! = ∏ k ≤ n, n.factorization.prod fun p i => p ^ i = ∏ k ≤ n, ∏ p in primesBelow n, p ^ (Nat.factorization k n)
-- Nat.prod_factorization_eq_prod_primeFactors ()
theorem sum_cheby_div_id :
  (fun n : ℕ ↦ (∑ k ∈ Finset.range (n+1), Λ k / k) - Real.log n) =O[atTop] fun _ ↦ (1:ℝ) := by
  have : (fun n ↦ n * ∑ d in Finset.range (n+1), Λ d / d - n * Real.log n) =O[atTop]
      (fun n ↦ (n:ℝ)) := by
    have := log_fac_sub_id_mul_log_isBigO_id
    simp_rw [log_factorial, sum_floor_mul_vonmangoldt] at this
    convert this.sub sum_integer_mul_vonMangoldt using 2 with n
    ring
  apply this.mul (isBigO_refl (fun (n : ℕ) ↦ (n : ℝ)⁻¹) atTop) |>.congr'
  · filter_upwards [eventually_gt_atTop 0]
    intro x hx
    field_simp
    ring
  · filter_upwards [eventually_ne_atTop 0]
    intro x hx
    field_simp

@[simp]
theorem pow_prime_iff (n k : ℕ) : Nat.Prime (n ^ k) ↔ n.Prime ∧ k = 1 := by
  constructor
  · intro h
    obtain rfl := Nat.Prime.eq_one_of_pow h
    simp_all
  · simp +contextual

@[simp]
theorem Nat.Primes.prime (p : Nat.Primes) : Nat.Prime p := p.2

theorem sq_isBigO_id_mul_sub_one : (fun x ↦ x^2) =O[atTop] fun x:ℝ ↦ x * (x - 1) := by
  let P : Polynomial ℝ := .X^2
  let Q : Polynomial ℝ := .X * (.X - 1)
  convert Polynomial.isBigO_of_degree_le P Q ?_ with x x <;> simp only [P, Q]
  · simp
  · simp
  convert_to (Polynomial.X^2).degree ≤ 2 using 1
  · compute_degree
    · norm_num
    · decide
  compute_degree

theorem mul_sub_one_inv_isBigO_neg_two :
    (fun x:ℝ ↦ (x * (x - 1))⁻¹) =O[atTop] fun x ↦ x^(-2:ℝ) := by
  apply (sq_isBigO_id_mul_sub_one.inv_rev _).congr'
  · rfl
  · filter_upwards [eventually_ge_atTop 0]
    intro x hx
    rw [rpow_neg hx]
    norm_num
  filter_upwards [eventually_ne_atTop 0] with a ha ha'
  simp_all

theorem isBigO_fun : (fun x ↦ Real.log x / (x * (x - 1)))
    =O[atTop] fun x ↦ x ^ (-3 / 2:ℝ) := by
  have hlog := isLittleO_log_rpow_atTop (show 0 < (1/2:ℝ) by norm_num)
  have hpoly : (fun x ↦ x^2) =O[atTop] fun x:ℝ ↦ x * (x - 1) := sq_isBigO_id_mul_sub_one
  have := mul_sub_one_inv_isBigO_neg_two
  apply (hlog.isBigO.mul this).congr'
  · simp_rw [div_eq_mul_inv]
    rfl
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp_rw [← rpow_add hx]
    norm_num

theorem sum_strictPow_convergent : Summable (fun (n:ℕ) ↦
  if ¬ Nat.Prime n then Λ n / n else 0) := by
  convert_to Summable ({k : ℕ | IsPrimePow k}.indicator
    fun (n:ℕ) ↦ if ¬ Nat.Prime n then Λ n / n else 0)
  · ext n
    by_cases h : IsPrimePow n
    · simp [h]
    · simp [h, ArithmeticFunction.vonMangoldt_eq_zero_iff]
  rw [← summable_subtype_iff_indicator]

  have hassum_p (p : Primes) :
      HasSum (fun y => if y = 0 then 0 else Real.log p / p^(y+1)) (Real.log p / (p * (p-1))) := by
    have hp : (p : ℝ) ≠ 0 := by
      exact_mod_cast p.2.ne_zero
    have hp' : (p : ℝ)⁻¹ ≠ 0 := by
      exact inv_ne_zero hp
    rw [← hasSum_nat_add_iff' 1]
    simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, ↓reduceIte, range_one,
      sum_singleton, sub_zero, div_eq_mul_inv, ]
    rw [hasSum_mul_left_iff (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne.symm, ]
    simp_rw [← inv_pow, pow_succ]
    rw [show (p * (p - 1 : ℝ))⁻¹ = (1-(p:ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ from ?rw]
    case rw =>
      rw [← mul_inv, sub_mul]
      simp only [mul_inv_rev, one_mul, isUnit_iff_ne_zero, ne_eq, hp,
        not_false_eq_true, IsUnit.inv_mul_cancel]
    rw [hasSum_mul_right_iff hp', hasSum_mul_right_iff hp']
    apply hasSum_geometric_of_lt_one (r := (p:ℝ)⁻¹) (by positivity)
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast p.2.one_lt
  set f := (fun (n:ℕ) ↦ if ¬ Nat.Prime n then Λ n / n else 0) ∘
    (fun x : {k : ℕ | IsPrimePow k} ↦ (x : ℕ))
  let e := Nat.Primes.prodNatEquiv
  rw [← Equiv.summable_iff e]
  have : f ∘ e = fun p ↦ if p.2 = 0 then 0 else Real.log p.1 / p.1 ^ (p.2+1) := by
    ext ⟨p, k⟩
    simp +contextual [Set.coe_setOf, Set.mem_setOf_eq, ite_not, Function.comp_apply,
      Primes.prodNatEquiv_apply, pow_prime_iff, Primes.prime, add_left_eq_self, true_and, cast_pow,
      f, e, ArithmeticFunction.vonMangoldt_apply_pow, ArithmeticFunction.vonMangoldt_apply_prime]
  rw [this, summable_prod_of_nonneg]
  · refine ⟨?_, ?_⟩
    · intro p
      apply (hassum_p p).summable
    simp_rw [fun p : Primes ↦ (hassum_p p).tsum_eq]
    simp [Primes]
    -- need Nat not Primes...
    -- -- why do I need to give f here...
    -- apply Summable.comp_injective (i := (fun p : Primes ↦ (p : ℕ)))
    --   (f := fun (n: ℕ) => Real.log n / (n * (n - 1:ℝ)) )
    apply summable_of_isBigO (g := fun p : Primes ↦ (p:ℝ) ^ (-3/2:ℝ))
    · rw [Nat.Primes.summable_rpow]
      norm_num
    convert_to (((fun x ↦ Real.log x / (x * (x-1))) ∘ (fun n : ℕ ↦ (n : ℝ))) ∘
      (fun p : Primes ↦ (p : ℕ)))
      =O[cofinite] (((fun x ↦ x^(-3/2:ℝ)) ∘ (fun n : ℕ ↦ (n : ℝ))) ∘ (fun p : Primes ↦ (p : ℕ)))
    apply Asymptotics.IsBigO.comp_tendsto (l := cofinite)
    · rw [Nat.cofinite_eq_atTop]
      exact Asymptotics.IsBigO.comp_tendsto isBigO_fun tendsto_natCast_atTop_atTop
    · apply Function.Injective.tendsto_cofinite Primes.coe_nat_injective
  · intro p
    simp only [Pi.zero_apply, e, f]
    positivity

theorem sum_primesBelow_log_div_id_eq_vonMangoldt_sub (n : ℕ) :
  ∑ p ∈ primesBelow (n+1), Real.log p / p = ∑ k ∈ Finset.range (n+1), Λ k / k
    - ∑ k ∈ Finset.range (n+1), if ¬ Nat.Prime k then Λ k / k else 0 := by
  trans ∑ p ∈ primesBelow (n+1), Λ p / p
  · apply sum_congr rfl
    simp +contextual [mem_primesBelow, ArithmeticFunction.vonMangoldt_apply_prime]
  rw [eq_sub_iff_add_eq, ← Finset.sum_filter, ← Finset.sum_union]
  · apply sum_subset <;>
    · intro a
      simp +contextual only [mem_union, mem_primesBelow, mem_filter, mem_range]
      tauto
  · rw [Finset.disjoint_left]
    simp +contextual only [mem_primesBelow, mem_filter, mem_range, not_true_eq_false, and_false,
      not_false_eq_true, implies_true]

theorem sum_properPower_vonMangoldt_div_id_isBigO_one :
  (fun n ↦ ∑ k ∈ Finset.range (n+1), if ¬ Nat.Prime k then Λ k / k else 0) =O[atTop]
    (fun _ ↦ (1 : ℝ)) := by
  apply Filter.IsBoundedUnder.isBigO_one
  use (∑' (n:ℕ), if ¬ Nat.Prime n then Λ n / n else 0)
  simp only [norm_eq_abs, eventually_map, ge_iff_le]
  filter_upwards with a
  rw [abs_of_nonneg ?pos]
  case pos =>
    bound
    -- apply Finset.sum_nonneg
    -- intro k __
    -- have := ArithmeticFunction.vonMangoldt_nonneg (n:=k)
    -- positivity
  apply sum_le_tsum (Finset.range (a+1)) _ (sum_strictPow_convergent)
  bound
  -- intro k _
  -- have := ArithmeticFunction.vonMangoldt_nonneg (n:=k)
  -- positivity

theorem tmp_eventually {f g : ℕ → ℝ} (hfg : f =O[atTop] g) (l : Filter ℕ) (h : ∀ᶠ n in l, g n = 0 → f n = 0) :
    f =O[l] g := by
  obtain ⟨C, hC_pos, hC⟩ := Asymptotics.bound_of_isBigO_nat_atTop hfg
  refine isBigO_iff.mpr ?_
  use C
  filter_upwards [h] with x h
  by_cases hf : f x = 0
  · simp [hf, hC_pos]
  apply hC
  exact fun a ↦ hf (h a)

theorem tmp {f g : ℕ → ℝ} (hfg : f =O[atTop] g) (h : ∀ n, g n = 0 → f n = 0) : f =O[⊤] g := by
  obtain ⟨C, hC_pos, hC⟩ := Asymptotics.bound_of_isBigO_nat_atTop hfg
  refine isBigO_top.mpr ?_
  use C
  intro x
  by_cases hf : f x = 0
  · simp [hf, hC_pos]
  apply hC
  exact fun a ↦ hf (h x a)

theorem mertens_first : (fun n : ℕ ↦ (∑ p ∈ primesBelow (n+1), Real.log p / p) - Real.log n)
    =O[⊤] (fun _ ↦ (1 : ℝ)) := by
  apply tmp _ (fun _ h ↦ (one_ne_zero h).elim)
  simp_rw [sum_primesBelow_log_div_id_eq_vonMangoldt_sub]
  have h₀ := sum_properPower_vonMangoldt_div_id_isBigO_one
  have h₁ := sum_cheby_div_id
  apply (h₁.sub h₀).congr <;>
  · intro x
    ring
set_option linter.style.longLine false

@[reducible]
private noncomputable def E₁ (t : ℝ) : ℝ := (∑ p ∈ primesBelow (⌊t⌋₊+1), Real.log p / p) - Real.log t

private theorem E₁_eq : E₁ = fun t ↦ (∑ p ∈ primesBelow (⌊t⌋₊+1), Real.log p / p) - Real.log t := rfl

theorem E₁_eq_add (t : ℝ) : (∑ p ∈ primesBelow (⌊t⌋₊+1), Real.log p / p) = Real.log t + E₁ t := by
  rw [E₁_eq]
  ring

theorem E₁_of_lt_two (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : t < 2) : E₁ t = - Real.log t := by
  have : ⌊t⌋₊ ≤ 1 := by
    apply Nat.le_of_lt_succ
    rw [Nat.floor_lt ht_nonneg]
    exact ht
  have : (⌊t⌋₊ + 1).primesBelow = ∅ := by
    ext p
    simp [mem_primesBelow]
    intro h hp
    have := hp.two_le
    omega
  rw [E₁, this, Finset.sum_empty, zero_sub]

@[fun_prop, measurability]
theorem E₁_measurable : Measurable E₁ := by
  rw [E₁_eq]
  apply Measurable.sub
  · apply (measurable_from_nat (f := fun n ↦ ∑ p ∈ primesBelow (n+1), Real.log p / p)).comp
      Nat.measurable_floor
  · fun_prop

theorem Asymptotics.IsBigO.nat_floor {f g : ℕ → ℝ} (h : f =O[⊤] g) :
  (fun x ↦ f (Nat.floor x)) =O[⊤] (fun x ↦ (g (Nat.floor x)) : ℝ → ℝ) := by
  apply h.comp_tendsto tendsto_top

open Filter
theorem antitoneOn_id_div_sub : AntitoneOn (fun x : ℝ ↦ x / (x-1)) (Set.Ioi 1) := by
  have := (sub_inv_antitoneOn_Ioi (c:=(1:ℝ))).add_const 1
  apply this.congr
  intro x hx
  simp only [Set.mem_Ioi] at hx
  apply Eq.symm
  calc _ = ((x-1) + 1)/(x-1) := by ring
    _ = _ := by
      rw [_root_.add_div, div_self (by linarith)]
      ring

@[bound]
theorem floor_pos_of {α : Type* } [inst : LinearOrderedSemiring α] [inst_1 : FloorSemiring α] {a : α} (h : 1 ≤ a) :  0 < ⌊a⌋₊ := by
  apply Nat.floor_pos.mpr h

attribute [bound] Nat.floor_le
-- ouchie
/- There should be some general theorem: given f : ℕ → ℝ and g h : ℝ → ℝ, got from f n - g n =O h n
 to f ⌊x⌋₊ - g x =O h x under certain "smoothnes"/monotonicity assumptions on g -/
theorem E₁_isBigO_one {t : ℝ} (ht : 1 < t) : E₁ =O[𝓟 <| Set.Ici t] (fun _ ↦ (1:ℝ)) := by
  have h₀ : (fun t ↦ Real.log t - Real.log (⌊t⌋₊)) =O[𝓟 <| Set.Ici t] (fun t ↦ Real.log t - Real.log (t-1)) := by
    have h1 (t : ℝ) (ht : 1 < t) : Real.log (t-1) ≤ Real.log (⌊t⌋₊) := by
      bound [Nat.lt_floor_add_one t]
      -- gcongr
      -- · linarith only [ht]
      -- · linarith only [Nat.lt_floor_add_one t]
    have h2 (t : ℝ) (ht : 1 ≤ t) : Real.log (⌊t⌋₊) ≤ Real.log t := by
      bound
      -- gcongr
      -- · exact_mod_cast Nat.floor_pos.mpr ht
      -- · apply Nat.floor_le (zero_le_one.trans ht)
    apply Eventually.isBigO
    simp only [norm_eq_abs, eventually_principal, Set.mem_Ici]
    intro t ht
    rw [abs_of_nonneg (by bound)] --; linarith only [h2 t (by linarith)])]
    gcongr
    · linarith
    · linarith only [Nat.lt_floor_add_one t]
  have h₁ : (fun t ↦ Real.log t - Real.log (t-1)) =O[𝓟 <| Set.Ici t] (fun _ ↦ (1:ℝ)) := by
    apply IsBigO.trans _ (Asymptotics.isBigO_const_const (t/(t-1)) one_ne_zero _)
    apply Filter.Eventually.isBigO
    simp only [norm_eq_abs, eventually_principal, Set.mem_Ici]
    intro x hx
    rw [abs_of_nonneg ?nonneg]
    case nonneg =>
      rw [sub_nonneg]
      gcongr <;> linarith
    rw [← Real.log_div]
    · apply (Real.log_le_self _).trans
      · apply antitoneOn_id_div_sub _ _ hx <;> simp only [Set.mem_Ioi, ht]
        linarith
      bound
      -- apply div_nonneg (by linarith)
      -- linarith
    · linarith
    · exact sub_ne_zero_of_ne (by linarith)
  simp_rw [E₁_eq]
  apply ((mertens_first.mono le_top).nat_floor.mono le_top |>.sub (h₀.trans h₁)).congr <;>
  · intro x
    ring

section MertensSecond

theorem Icc_filter_prime (n : ℕ) : filter (fun a ↦ Nat.Prime a) (Icc 0 n) = Nat.primesBelow (n+1) := by
  ext p
  simp only [mem_filter, mem_Icc, _root_.zero_le, true_and, mem_primesBelow, and_congr_left_iff]
  omega

theorem helper1 (n : ℕ) :
    ∑ x ∈ Icc 0 n, (if Nat.Prime x then Real.log ↑x / ↑x else 0) =
    ∑ p ∈ (n+1).primesBelow, Real.log p / p := by
  rw [← sum_filter, sum_congr]
  · ext p
    simp only [mem_filter, mem_Icc, _root_.zero_le, true_and, mem_primesBelow, and_congr_left_iff]
    omega
  · simp only [implies_true]

theorem extracted_1 (a b : ℝ) (ha : 1 < a):
  MeasureTheory.Integrable (fun t ↦ t⁻¹ * (Real.log t)⁻¹)
    (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  rw [← MeasureTheory.IntegrableOn]
  have hsub : Set.Icc a b ⊆ {0}ᶜ := by
    simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le]
    intros
    linarith
  apply ((continuousOn_inv₀.mono hsub).mul ((continuousOn_log.mono hsub).inv₀ ?_))
    |>.integrableOn_compact isCompact_Icc
  intro x
  simp only [Set.mem_Icc, ne_eq, not_or, and_imp]
  -- bound
  intro hx _
  apply (Real.log_pos (by linarith)).ne.symm

section IntegralLogInv

/-- Computing the integral of $(log x)^{-1}$-/

theorem hasDerivAt_log_inv (x : ℝ) (hx : 1 < x): HasDerivAt (fun x ↦ (Real.log x)⁻¹) (- x⁻¹ * (Real.log x)⁻¹^2) x := by
  have hlog :
    HasDerivAt Real.log (x⁻¹) (x) := by
    convert Real.hasDerivAt_log (by linarith)
  convert (hasDerivAt_inv (Real.log_pos hx).ne.symm).comp x hlog using 1
  ring

theorem integrable_inv_mul_log_inv_sq (x : ℝ) (hx : 1 < x) :
    MeasureTheory.IntegrableOn (fun t ↦ t⁻¹ * (Real.log t)⁻¹ ^ 2)  (Set.Ici x) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have (t : ℝ) (ht : t ∈ Set.Ioi x): HasDerivAt (fun x ↦ - (Real.log x)⁻¹) (t⁻¹ * (Real.log t)⁻¹^2) t := by
    simp only [Set.mem_Ioi] at ht
    convert (hasDerivAt_log_inv t (hx.trans ht)).neg using 1
    ring

  apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg _ this (l := 0)
  · simp only [Set.mem_Ioi]
    bound
    -- intro t hxt
    -- have : 0 < t := by linarith
    -- have := Real.log_pos (hx.trans hxt)
    -- positivity
  · rw [← neg_zero]
    apply (tendsto_inv_atTop_zero.comp tendsto_log_atTop).neg
  · refine ((continuousAt_log (by linarith)).continuousWithinAt).inv₀ (Real.log_pos hx).ne.symm |>.neg

theorem setIntegral_Ioi_inv_mul_inv_log_sq (a : ℝ) (ha : 1 < a) :
    ∫ t in Set.Ioi a, t⁻¹ * (Real.log t)⁻¹ ^ 2 = (Real.log a)⁻¹ := by
  rw [show (Real.log a)⁻¹ = 0 - -(Real.log a)⁻¹ by ring]
  apply integral_Ioi_of_hasDerivAt_of_tendsto
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.neg
    refine ContinuousAt.comp' ?_ ?_
    · refine continuousAt_inv₀ (Real.log_pos (by linarith)).ne.symm
    · refine continuousAt_log (by linarith)
  · intro x hx
    simp only [Set.mem_Ioi] at hx
    convert (hasDerivAt_log_inv _ _).neg using 1
    · ring
    · linarith
  · rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    apply integrable_inv_mul_log_inv_sq a ha
  · rw [← neg_zero]
    apply Tendsto.neg
    apply Tendsto.comp tendsto_inv_atTop_zero tendsto_log_atTop

end IntegralLogInv

theorem mul_E₁_measurable : Measurable (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a) := by
  fun_prop

theorem integrableOn_Ici_fun_mul_E₁ (t : ℝ) (ht : 1 < t) :
    MeasureTheory.IntegrableOn (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a) (Set.Ici t) := by
  have isBigO : (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a) =O[𝓟 (Set.Ici t)] (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2) := by
    simp_rw [mul_assoc]
    convert (isBigO_refl (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2) _).mul (E₁_isBigO_one ht) using 1
    · ext; ring
    · ext; ring
  have hmg : (𝓟 (Set.Ici t)).IsMeasurablyGenerated := principal_isMeasurablyGenerated_iff.mpr
    measurableSet_Ici
  have := isBigO.integrableAtFilter («μ» := volume) (mul_E₁_measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
    (integrable_inv_mul_log_inv_sq t ht).integrableAtFilter
  rw [integrableAtFilter_principal_iff] at this
  exact this

theorem integral_mul_E₁_eq_const_sub_integral (x a : ℝ) (ha : 1 < a) (hx : a ≤ x) :
    ∫ (t : ℝ) in Set.Icc a x, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t =
    (∫ (t : ℝ) in Set.Ioi a, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) - ∫ (t : ℝ) in Set.Ioi x, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t := by
  rw [eq_sub_iff_add_eq, ← setIntegral_union]
  · rw [← integral_Ici_eq_integral_Ioi]
    congr
    refine Set.Icc_union_Ioi_eq_Ici hx
  · rw [Set.disjoint_iff]
    intro t
    simp
  · measurability
  · apply (integrableOn_Ici_fun_mul_E₁ a ha).mono Set.Icc_subset_Ici_self le_rfl
  · apply (integrableOn_Ici_fun_mul_E₁ a ha).mono (Set.Ioi_subset_Ici hx) le_rfl

/-- Let `f : X x Y → Z`. If as `y` tends to `l`, `f(x, y) = O(g(y))` uniformly on `s : Set X`
of finite measure, then the integral of `f` along `s` is `O(g(y))`. -/

theorem integral_mul_E₁_tail_isBigO (a : ℝ) (ha : 1 < a) :
    (fun x ↦ ∫ (t : ℝ) in Set.Ioi x, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t)
    =O[𝓟 (Set.Ioi a)] (fun x ↦ (Real.log x)⁻¹) := by
  obtain ⟨C, hC_pos, hC⟩ := (E₁_isBigO_one ha).exists_pos
  rw [isBigO_iff]
  use C
  simp only [isBigOWith_principal, Set.mem_Ici, norm_eq_abs, norm_one, mul_one] at hC
  simp only [norm_eq_abs, norm_inv, eventually_principal, Set.mem_Ioi]
  intro x hx
  calc
    _ ≤ ∫ t in Set.Ioi x, |t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t| := by
      apply abs_integral_le_integral_abs
    _ = ∫ t in Set.Ioi x, t⁻¹ * (Real.log t)⁻¹ ^ 2 * |E₁ t| := by
      apply setIntegral_congr_fun
      · exact measurableSet_Ioi
      intro t ht
      simp only [Set.mem_Ioi] at ht
      simp_rw [abs_mul, abs_pow]
      rw [abs_of_nonneg, abs_of_nonneg]
      · bound
        -- rw [inv_nonneg]
        -- apply Real.log_nonneg (by linarith)
      · bound
        -- rw [inv_nonneg]
        -- linarith
    _ ≤ C * ∫ t in Set.Ioi x, t⁻¹ * (Real.log t)⁻¹ ^ 2 := by
      simp_rw [← smul_eq_mul, ← integral_smul, smul_eq_mul]
      apply setIntegral_mono_on
      · rw [← integrableOn_Ici_iff_integrableOn_Ioi]
        apply ((integrable_norm_iff _).mpr (integrableOn_Ici_fun_mul_E₁ ..)).congr'
        · apply Measurable.aestronglyMeasurable
          fun_prop
        · simp only [inv_pow, norm_mul, norm_inv, norm_eq_abs, norm_pow, sq_abs, abs_abs,
          measurableSet_Ici, ae_restrict_eq, eventually_true]
        · apply Measurable.aestronglyMeasurable
          fun_prop
        · linarith
      · rw [IntegrableOn]
        apply Integrable.const_mul
        rw [← IntegrableOn]
        apply (integrable_inv_mul_log_inv_sq x (ha.trans hx)).mono _ le_rfl
        exact Set.Ioi_subset_Ici_self
      · exact measurableSet_Ioi
      intro t ht
      simp only [Set.mem_Ioi] at ht
      rw [mul_comm C]
      gcongr
      · bound
      -- · have : 0 ≤ t := by linarith
      --   have : 0 ≤ Real.log t := (Real.log_nonneg (by linarith))
      --   positivity
      · apply hC _ (hx.trans ht).le
    _ = _ := by
      rw [abs_of_nonneg, setIntegral_Ioi_inv_mul_inv_log_sq ]
      · exact ha.trans hx
      · bound
        -- apply Real.log_nonneg (by linarith)

-- This was a pain point: I want uniform bounds to show integrability of E₁, since E₁ is definitely not continuous
-- Perhaps one could argue, E₁ is a step function plus a

theorem integrable_mul_E₁ (a b : ℝ) (ha : 1 < a) :
  MeasureTheory.Integrable (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a)
    (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  rw [← IntegrableOn]
  apply (integrableOn_Ici_fun_mul_E₁ a (by linarith)).mono Set.Icc_subset_Ici_self le_rfl

theorem hasDerivAt_loglog (x : ℝ) (hx : 1 < x) : HasDerivAt (fun t ↦ Real.log (Real.log t)) (x⁻¹ * (Real.log x)⁻¹) x := by
  rw [← Function.comp_def, mul_comm]
  apply (hasDerivAt_log (Real.log_pos hx).ne.symm).comp
  apply hasDerivAt_log (by linarith)

theorem integral_inv_mul_invlog (a b : ℝ) (ha : 1 < a) (hb : a ≤ b) :
    ∫ (t : ℝ) in Set.Ioc a b, (t⁻¹ * (Real.log t)⁻¹) =
      Real.log (Real.log b) - Real.log (Real.log a) := by
  have hsub : Set.uIcc (3 / 2) b ⊆ {0}ᶜ := by
    simp only [Set.subset_compl_singleton_iff]
    refine Set.not_mem_uIcc_of_lt (by norm_num) (by linarith)
  have htzero : b ≠ 0 := by linarith
  have hlogzero : Real.log b ≠ 0 := (Real.log_pos (by linarith)).ne.symm
  rw [← intervalIntegral.integral_of_le hb]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x
    simpa only [hasDerivAt_loglog, Set.uIcc_of_le hb, Set.mem_Icc, and_imp] using
      fun h _ ↦ hasDerivAt_loglog _ (by linarith)
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le hb, MeasureTheory.IntegrableOn]
  exact extracted_1 a b ha

noncomputable def mertens₂Const : ℝ := (∫ (t : ℝ) in Set.Ioi 2, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t)
  - Real.log (Real.log 2) + 1

theorem mertens₂Const_eq (a : ℝ) (ha : 1 < a) (ha' : a ≤ 2) :
  mertens₂Const = (∫ (t : ℝ) in Set.Ioi a, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t)
  - Real.log (Real.log a) + 1 := by
  have h₀ : ∫ (t : ℝ) in Set.Ioi a, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t =
    (∫ (t : ℝ) in Set.Ioc a 2, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) +
      ∫ (t : ℝ) in Set.Ioi 2, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t := by
    rw [← setIntegral_union]
    · rw [Set.Ioc_union_Ioi_eq_Ioi ha']
    · exact Set.Ioc_disjoint_Ioi_same
    · exact measurableSet_Ioi
    · apply (integrableOn_Ici_fun_mul_E₁ a ha).mono _ le_rfl
      intro x
      simp +contextual only [Set.mem_Ioc, Set.mem_Ici, LT.lt.le, implies_true]
    · apply (integrableOn_Ici_fun_mul_E₁ a ha).mono _ le_rfl
      intro x
      simp only [Set.mem_Ioi, Set.mem_Ici]
      intro hx
      apply (ha'.trans hx.le)
  have h₁ := calc
    ∫ (t : ℝ) in Set.Ioc a 2, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t = - ∫ (t : ℝ) in Set.Ioc a 2, t⁻¹ * (Real.log t)⁻¹ := by
      rw [← integral_neg]
      simp_rw [integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (by measurability)] with t ht
      simp only [Set.mem_Ioo] at ht
      rw [E₁_of_lt_two t (by linarith) ht.2]
      have : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne.symm
      have : t ≠ 0 := by linarith
      field_simp
      ring
    _ = Real.log (Real.log a) - Real.log (Real.log 2) := by
      rw [integral_inv_mul_invlog a 2 ha ha']
      ring
  rw [h₀, h₁, mertens₂Const]
  ring

/-
Notable pain points: positivity / nonnegativity and log, proving Real.log x ≠ 0 is annoying. Automation
like `positivity` and `field_simp` can't work with this very well.
-/


-- TODO : replace 1 / p with p⁻¹
theorem mertens_second (a : ℝ) (ha : 1 < a) (ha' : a < 2)
: (fun t : ℝ ↦ (∑ p ∈ primesBelow (⌊t⌋₊+1), 1 / (p : ℝ)) - (Real.log (Real.log t) + mertens₂Const))
    =O[𝓟 (Set.Ioi a)] (fun n ↦ (Real.log n)⁻¹) := by
  have ha_pos : 0 < a := by linarith
  let ϕ (x : ℝ) : ℝ := (Real.log x)⁻¹
  let c (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0
  have h' (b : ℝ) : ContinuousOn (fun x:ℝ ↦ - x⁻¹ * (Real.log x)⁻¹^2) (Set.Icc a b) := by
    intro x
    simp only [Set.mem_Icc, inv_pow, neg_mul, and_imp]
    intro hx _
    apply ContinuousAt.continuousWithinAt
    have : x ≠ 0 := by linarith
    apply (continuousAt_inv₀ this).mul ((continuousAt_inv₀ _).comp ((continuousAt_id.log this).pow 2)) |>.neg
    simp only [id_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, log_eq_zero,
      not_or]
    refine ⟨this, ?_, ?_⟩ <;> linarith
  have hϕ := hasDerivAt_log_inv
  have hfloor : ⌊(a : ℝ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    norm_num
    constructor <;> linarith
  have (b : ℝ) (hb : a ≤ b) :
      ∑ k ∈ Finset.Ioc 1 ⌊b⌋₊, ϕ k * c k = ϕ b * ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k - ϕ a * 0 -
        ∫ t in Set.Ioc a b, deriv ϕ t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
    convert sum_mul_eq_sub_sub_integral_mul c ?_ hb ?_ ?_
    · rw [hfloor]
    · apply (sum_eq_zero ..).symm
      simp only [hfloor, mem_Icc, _root_.zero_le, true_and, ite_eq_right_iff, div_eq_zero_iff,
        log_eq_zero, cast_eq_zero, cast_eq_one, c]
      omega
    · exact ha_pos.le
    · simp only [Set.mem_Icc, and_imp, c]
      intro t ht _
      exact (hϕ t (by linarith)).differentiableAt
    · apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact
      · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
        apply (h' b).congr
        intro x
        simp only [Set.mem_Icc, inv_pow, neg_mul, and_imp, c]
        intro hx _
        rw [(hϕ x (by linarith)).deriv]
        ring
      · exact isCompact_Icc
  simp only [mul_zero, sub_zero, ϕ, c, ← sum_filter, Icc_filter_prime, E₁_eq_add] at this

  have eqn (t : ℝ) (ht : a ≤ t) :=
    have hlogt : Real.log t ≠ 0 := (Real.log_pos (ha.trans_le ht)).ne.symm
    calc
    ∑ p ∈ (⌊t⌋₊ + 1).primesBelow, 1 / ↑p = (∑ x ∈ Ioc 1 ⌊t⌋₊, (Real.log ↑x)⁻¹ * if Nat.Prime x then Real.log ↑x / ↑x else 0) := by
      simp_rw [mul_ite, mul_zero, ← sum_filter]
      apply sum_congr
      · ext p
        simp only [mem_primesBelow, mem_filter, mem_Ioc, and_congr_left_iff, ϕ, c]
        intro hp
        refine ⟨fun hpt ↦ ⟨hp.one_lt, (by omega)⟩, fun ⟨_, hpt⟩ ↦ (by omega)⟩
      simp only [mem_filter, mem_Ioc, one_div, and_imp]
      intro x hx _ _
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀, one_mul]
      apply (Real.log_pos (mod_cast hx)).ne.symm
    _ =
     (1 + (Real.log t)⁻¹ * E₁ t) -
        ∫ (t : ℝ) in Set.Ioc a t, deriv (fun x ↦ (Real.log x)⁻¹) t * (Real.log t + E₁ t) := by
      convert this t ht using 2
      rw [mul_add, inv_mul_cancel₀ hlogt]
    _ =
     (1 + (Real.log t)⁻¹ * E₁ t) -
        ∫ (t : ℝ) in Set.Ioc a t, (- t⁻¹ * (Real.log t)⁻¹ ^ 2) * (Real.log t + E₁ t) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)]
      intro x
      simp only [Set.mem_Ioc, add_sub_cancel, inv_pow, neg_mul, and_imp]
      intro hx _
      rw [(hϕ x (by linarith)).deriv]
      ring
    _ =
     (1 + (Real.log t)⁻¹ * E₁ t) +
        (∫ (t : ℝ) in Set.Icc a t, t⁻¹ * (Real.log t)⁻¹ + t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) := by
      simp_rw [← MeasureTheory.integral_Icc_eq_integral_Ioc, neg_mul, MeasureTheory.integral_neg, sub_neg_eq_add, mul_add]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)]
      intro x
      simp only [Set.mem_Icc, add_left_inj, and_imp]
      intro hx _
      have := (Real.log_pos (by linarith)).ne.symm
      field_simp [show x ≠ 0 by linarith]
      ring
    _ =
     (1 + (Real.log t)⁻¹ * E₁ t) +
        ((∫ (t : ℝ) in Set.Icc a t, t⁻¹ * (Real.log t)⁻¹) +
          ∫ (t : ℝ) in Set.Icc a t, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) := by
      rw [MeasureTheory.integral_add (extracted_1 _ _ (by linarith)) (integrable_mul_E₁ _ _ (by linarith))]
    _ =
        Real.log (Real.log t) + mertens₂Const + (Real.log t)⁻¹ * E₁ t -
          ∫ (t : ℝ) in Set.Ioi t, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t := by
      rw [mertens₂Const_eq a ha ha'.le, integral_Icc_eq_integral_Ioc, integral_inv_mul_invlog _ _ ha ht,
        integral_mul_E₁_eq_const_sub_integral _ _ ha ht]
      ring

  apply Asymptotics.IsBigO.congr'  (f₁ := fun t ↦ (Real.log t)⁻¹ * E₁ t -
    ∫ (t : ℝ) in Set.Ioi t, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) (g₁ := fun t ↦ (Real.log t)⁻¹)
      (g₂ := fun t ↦ (Real.log t)⁻¹)
  · apply Asymptotics.IsBigO.sub
    · apply (Asymptotics.isBigO_refl (fun t ↦ (Real.log t)⁻¹) _).mul (E₁_isBigO_one ha) |>.mono _ |>.congr_right
      · simp only [mul_one, implies_true]
      · simp only [le_principal_iff, mem_principal, Set.Ioi_subset_Ici_iff, le_refl]
    · exact integral_mul_E₁_tail_isBigO a ha
  · simp only [eventuallyEq_principal]
    intro t ht
    simp only [Set.mem_Ioi] at ht
    simp only
    rw [eqn t ht.le]
    ring
  · exact fun ⦃a_1⦄ ↦ congrFun rfl

end MertensSecond

-- #print axioms mertens_second



section MertensThird

theorem hasSum_pow_div_add_two {x : ℝ} (hx : |x| < 1) : HasSum (fun n : ℕ ↦ x ^ (n+2) / (n+2)) (-Real.log (1-x) - x) := by
  norm_cast
  erw [hasSum_nat_add_iff (f := fun n ↦ x ^ (n+1) / ↑(n+1)) 1]
  simp only [cast_add, cast_one, range_one, sum_singleton, zero_add, pow_one, CharP.cast_eq_zero,
    div_one]
  convert Real.hasSum_pow_div_log_of_abs_lt_one hx using 1
  ring

theorem sum_inv_sub_sum_log (n : ℕ)  :
  ∑ p in primesBelow (n+1), -Real.log (1 - (p:ℝ)⁻¹) - ∑ p in primesBelow (n + 1), (p:ℝ)⁻¹ =
    ∑ p in primesBelow (n+1), ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2)  := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  simp only [mem_primesBelow] at hp
  rw [(hasSum_pow_div_add_two _).tsum_eq]
  rw [abs_inv, inv_lt_one_iff₀]
  simp only [abs_cast, cast_nonpos, one_lt_cast, hp.2.one_lt, or_true]


theorem tsum_inv_pow_div_id_le (p : ℕ) (hp : 1 < p)  :
  ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) ≤ (p * (p-1):ℝ)⁻¹ :=
  have geom : HasSum (fun n : ℕ ↦ (p : ℝ)⁻¹ ^ n) ((1 - (p:ℝ)⁻¹)⁻¹) := by
    apply hasSum_geometric_of_abs_lt_one
    rw [abs_inv, inv_lt_one_iff₀]
    simp [hp]
  have summable : Summable fun i ↦ (p:ℝ)⁻¹ ^ (i + 2) := by
    rw [summable_nat_add_iff]
    exact geom.summable
  calc
  _ ≤ ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) := by
    apply tsum_le_tsum
    · intro n
      apply _root_.div_le_self
      · positivity
      · norm_cast
        omega
    · apply (hasSum_pow_div_add_two _).summable
      · simp [abs_inv, hp]
        simp [inv_lt_one_iff₀, hp]
    · apply summable
  _ = (p * (p - 1):ℝ)⁻¹  := by
    have : HasSum (fun n : ℕ ↦ (p : ℝ)⁻¹^(n+2)) ((1-(p:ℝ)⁻¹)⁻¹*(p:ℝ)⁻¹^2) := by
      simp_rw [pow_add, ]
      rw [hasSum_mul_right_iff (by positivity)]
      · exact geom
    convert this.tsum_eq using 1
    rw [inv_pow, ← mul_inv]
    congr 1
    field_simp [show (p : ℝ) ≠ 0 by positivity]
    ring

theorem summable_aux :
    Summable (fun n : ℕ ↦ (n * (n-1):ℝ)⁻¹) := by
  apply summable_of_isBigO_nat (g := fun n:ℕ ↦ n ^ (-2:ℝ))
  · simp only [summable_nat_rpow, neg_lt_neg_iff, one_lt_ofNat]
  apply mul_sub_one_inv_isBigO_neg_two.comp_tendsto tendsto_natCast_atTop_atTop

theorem summable_thing :
  Summable (fun p : ℕ ↦ ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2)) := by
  apply Summable.of_norm_bounded_eventually_nat _ summable_aux
  filter_upwards [eventually_gt_atTop 1] with p hp
  rw [norm_eq_abs, abs_of_nonneg]
  · exact tsum_inv_pow_div_id_le p hp
  · bound
    -- apply tsum_nonneg
    -- intro n
    -- positivity


theorem summable_thing' :
  Summable (fun p : ℕ ↦ if p.Prime then ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) else 0) := by
  simp_rw (singlePass := true)[← Set.mem_setOf (p := Nat.Prime), ← Set.indicator_apply {n : ℕ | n.Prime} (fun p ↦ ∑' (n : ℕ), (↑p:ℝ)⁻¹ ^ (n + 2) / (↑n + 2))]
  apply Summable.indicator
  exact summable_thing

-- theorem hasSum_primes_iff (f : ℕ → ℝ) (x : ℝ):
--   HasSum (fun p : Primes ↦ f p) x ↔ HasSum (({n | n.Prime}.indicator f)) x := by
--   rw [← hasSum_subtype_iff_indicator]
--   -- evil
--   rfl

-- theorem summable_primes_iff (f : ℕ → ℝ) :
--   Summable (fun p : Primes ↦ f p) ↔ Summable (({n | n.Prime}.indicator f)) := by
--   rw [← summable_subtype_iff_indicator]
--   --evil
--   rfl

-- theorem tsum_primes (f : ℕ → ℝ) :
--   ∑' p : Primes, f p = ∑' n, ({n | n.Prime}.indicator f n) := by
--   rw [← _root_.tsum_subtype]
--   --evil
--   rfl

theorem sum_primesBelow_tsum_eq_tsum_sub_tsum (k : ℕ):
    ∑ p in primesBelow (k+1), ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) =
      (∑' p : ℕ, if p.Prime then ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) else 0)
      - (∑' p : ℕ, if (p + k + 1).Prime then ∑' n : ℕ, (↑(p+k+1):ℝ)⁻¹^(n+2) / (n+2) else 0) := by
  rw [Nat.primesBelow, sum_filter, eq_sub_iff_add_eq]
  apply sum_add_tsum_nat_add (k := k+1) (f := fun p ↦ if p.Prime then ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) else 0)
  convert summable_thing' with p

theorem telescoping_series (f : ℕ → ℝ) (hf : Antitone f) (htends : Tendsto f atTop (nhds 0)) :
    ∑' n, (f n - f (n + 1)) = f 0 := by
  have (n : ℕ): ∑ i ∈ Finset.range n, (f i - f (i+1)) = f 0 - f n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      ring
  have : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (f i - f (i+1))) atTop (nhds (f 0)) := by
    simp_rw [this]
    convert tendsto_const_nhds.sub htends
    ring
  apply tendsto_nhds_unique (HasSum.Multipliable.tendsto_sum_tsum_nat ?_) this
  rw [summable_iff_not_tendsto_nat_atTop_of_nonneg]
  · exact not_tendsto_atTop_of_tendsto_nhds this
  intro n
  linarith [hf (le_succ n)]

theorem tsum_mul_succ_inv (k : ℕ) (hk : 0 < k) : (∑' n : ℕ, (↑(n+k+1) * (↑(n+k+1)-1) : ℝ)⁻¹) = (k:ℝ)⁻¹  := by
  let f (n : ℕ) := (↑(n + k):ℝ)⁻¹
  have (n : ℕ) : f n - f (n+1) = (↑(n+k+1) * (↑(n+k+1)-1) : ℝ)⁻¹ := by
    simp only [f]
    field_simp
    ring
  simp_rw [← this]
  convert telescoping_series f ?_ ?_
  · ring
  · simp only [f]
    intro a b hab
    simp only [cast_add, f]
    gcongr
  · simp only [f]
    apply tendsto_inv_atTop_zero.comp
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_add_atTop_nat k

private theorem tailSum_isBigO_inv_nat : (fun k ↦ ∑' p : ℕ, if (p + k + 1).Prime then ∑' n : ℕ, (↑(p+k+1):ℝ)⁻¹^(n+2) / (n+2) else 0)
    =O[atTop] fun n : ℕ ↦ (n:ℝ)⁻¹ := by
  calc
    _ =O[atTop] fun k : ℕ ↦ (∑' p : ℕ, (↑(p + k + 1) * (↑(p + k + 1) - 1))⁻¹ : ℝ) := by
      apply Filter.Eventually.isBigO
      filter_upwards [eventually_gt_atTop 1] with k hk
      rw [norm_eq_abs, abs_of_nonneg ?nonneg]
      case nonneg =>
        -- all because positivity doesn't support tsum_nonneg / intros. This seems like an easy extension to write. See Mathlib/Tactic/Positivity/Finset.lean
        -- Ah, but `bound` works too!
        bound
        -- apply tsum_nonneg
        -- intros
        -- split_ifs
        -- · apply tsum_nonneg
        --   intros
        --   positivity
        -- · rfl
      apply tsum_le_tsum
      · bound [tsum_inv_pow_div_id_le]
      -- · intro p
      --   split_ifs
      --   · exact tsum_inv_pow_div_id_le (p+k+1) (by omega)
      --   · push_cast
      --     ring_nf
      --     positivity
      · apply (summable_nat_add_iff (k+1)).mpr summable_thing'
      · apply (summable_nat_add_iff (k+1)).mpr summable_aux
    _ =ᶠ[atTop] _ := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      apply tsum_mul_succ_inv k hk

private theorem tailSum_isBigO_inv_nat_Ici : (fun k ↦ ∑' p : ℕ, if (p + k + 1).Prime then ∑' n : ℕ, (↑(p+k+1):ℝ)⁻¹^(n+2) / (n+2) else 0)
    =O[𝓟 <| Set.Ici 1] fun n : ℕ ↦ (n:ℝ)⁻¹ := by
  apply tmp_eventually tailSum_isBigO_inv_nat
  simp only [inv_eq_zero, cast_eq_zero, cast_add, cast_one, inv_pow, eventually_principal,
    Set.mem_Ici]
  intros
  omega

theorem tendsto_floor_Ici_Ici (n : ℕ) : Tendsto (Nat.floor : ℝ → ℕ) (𝓟 <| Set.Ici n) (𝓟 <| Set.Ici n) := by
  simp +contextual [Nat.le_floor]

private theorem tailSum_isBigO_inv : (fun x:ℝ ↦ ∑' p : ℕ, if (p + ⌊x⌋₊ + 1).Prime then ∑' n : ℕ, (↑(p+⌊x⌋₊+1):ℝ)⁻¹^(n+2) / (n+2) else 0)
    =O[𝓟 <| Set.Ici 1] fun x : ℝ ↦ (⌊x⌋₊:ℝ)⁻¹ := by
  apply tailSum_isBigO_inv_nat_Ici.comp_tendsto (mod_cast (tendsto_floor_Ici_Ici 1))

theorem le_two_mul_floor (x : ℝ) : x / ↑⌊x⌋₊ ≤ 2 := by
  by_cases hx' : x < 1
  · rw [Nat.floor_eq_zero.mpr hx']
    · simp
  rw [div_le_iff₀ (by bound)] -- rw_mod_cast [Nat.floor_pos]; linarith)]
  by_cases h : 2 ≤ x
  · bound [Nat.lt_floor_add_one x]
    -- have := Nat.lt_floor_add_one x
    -- have := Nat.floor_le (show 0 ≤ x by linarith)
    -- linarith
  · have : ⌊x⌋₊ = 1 := by
      rw [Nat.floor_eq_iff]
      -- bound
      · constructor <;> norm_num <;> linarith
      · linarith
    simp only [this, cast_one, mul_one, ge_iff_le]
    linarith

theorem floor_inv_isBigO_inv : (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)⁻¹) =O[⊤] (fun x : ℝ ↦ x⁻¹) := by
  rw [Asymptotics.isBigO_iff]
  use 2
  simp only [norm_inv, RCLike.norm_natCast, norm_eq_abs, eventually_top]
  intro x
  by_cases hx' : x < 1
  · rw [Nat.floor_eq_zero.mpr hx']
    · simp
  rw [abs_of_nonneg (by linarith), le_mul_inv_iff₀ (by linarith), mul_comm,
    ← div_eq_mul_inv]
  exact le_two_mul_floor x

  -- simp only [floor_nat, tendsto_principal, id_eq, Set.mem_Ici, eventually_principal, imp_self,
  --   implies_true]

-- example (a : ℝ) (ha : 1 < a) :

theorem mertens3_sub_mertens2_isBigO (a : ℝ) (ha : 1 < a) : (fun x ↦ (∑ p in primesBelow (⌊x⌋₊ + 1), -Real.log (1 - (p:ℝ)⁻¹)
  - ∑ p in primesBelow (⌊x⌋₊ + 1), (p:ℝ)⁻¹)
  - (∑' p : ℕ, if p.Prime then ∑' n : ℕ, (↑(p):ℝ)⁻¹^(n+2) / (n+2) else 0))
    =O[𝓟 <| Set.Ioi a]  (fun x ↦ x⁻¹) := by
  simp_rw [sum_inv_sub_sum_log, sum_primesBelow_tsum_eq_tsum_sub_tsum]
  apply (tailSum_isBigO_inv.neg_left.mono _).trans (floor_inv_isBigO_inv.mono le_top) |>.congr'
  · filter_upwards with x
    ring
  · rfl
  · simp [ha.le]

noncomputable def mertens₃Const : ℝ := (∑' p : ℕ, if p.Prime then ∑' n : ℕ, (p:ℝ)⁻¹^(n+2) / (n+2) else 0) + mertens₂Const

theorem inv_isBigO_inv_log_Ioi (a : ℝ) (ha : 1 < a) :
  (fun x : ℝ ↦ x⁻¹) =O[𝓟 (Set.Ioi a)] (fun x : ℝ ↦ (Real.log x)⁻¹) := by
  rw [isBigO_iff]
  use 1
  simp only [norm_inv, norm_eq_abs, one_mul, eventually_principal, Set.mem_Ioi]
  intro x hx
  have hxpos : 0 < x := by linarith
  rw [abs_of_nonneg hxpos.le, abs_of_nonneg (Real.log_nonneg (ha.trans hx).le), inv_le_inv₀]
  · apply Real.log_le_self hxpos.le
  · linarith
  · apply Real.log_pos (ha.trans hx)

theorem mertens_third_log_aux (a : ℝ) (ha : 1 < a) (ha' : a < 2) :
    (fun x : ℝ ↦ ∑ p in primesBelow (⌊x⌋₊ + 1), -Real.log (1 - (p:ℝ)⁻¹) -
      (Real.log (Real.log x) + mertens₃Const))
      =O[𝓟 (Set.Ioi a)] (fun x ↦ (Real.log x)⁻¹) := by
  have h₀ := mertens3_sub_mertens2_isBigO a ha |>.trans <| inv_isBigO_inv_log_Ioi a ha
  have h₁ := mertens_second a ha ha'
  simp_rw [sub_sub] at h₀
  rw [mertens₃Const]
  -- have h₂ {a b c d e : ℝ} : a - (b + c) + (b - (d + e)) = a - (d + (c + e)) := by ring
  apply (h₀.add h₁).congr
  · simp_rw [one_div]
    intro x
    ring
  · intro
    rfl

theorem mertens_third_log (a : ℝ) (ha : 1 < a) (ha' : a < 2):
  (fun x : ℝ ↦ ∑ p in primesBelow (⌊x⌋₊ + 1), Real.log (1 - (p:ℝ)⁻¹) -
    (-Real.log (Real.log x) - mertens₃Const))
    =O[𝓟 (Set.Ioi a)] (fun x ↦ (Real.log x)⁻¹) := by
  convert (mertens_third_log_aux a ha ha').neg_left using 2 with x
  simp only [sum_neg_distrib, neg_sub, sub_neg_eq_add]
  ring

theorem mertens_third_log_isLittleO_one :
  (fun x : ℝ ↦ ∑ p in primesBelow (⌊x⌋₊ + 1), Real.log (1 - (p:ℝ)⁻¹) -
  (-Real.log (Real.log x) - mertens₃Const))
    =o[atTop] (fun _ ↦ (1:ℝ)) := by
  have h₀ : (fun x ↦ (Real.log x)⁻¹) =o[atTop] (fun x ↦ (1:ℝ)) := by
    simp_rw [Asymptotics.isLittleO_one_iff]
    apply tendsto_inv_atTop_zero.comp  tendsto_log_atTop
  apply (mertens_third_log (3/2) (by norm_num) (by norm_num)).mono ?_ |>.trans_isLittleO h₀
  intro s hs
  have := Filter.Ioi_mem_atTop (3/2:ℝ)
  apply Filter.mem_of_superset this
  simpa [this]

@[bound]
theorem test (x : ℝ) (n : ℕ) (hx : exp^[n+1] 1 < x):
    exp^[n] 1 < Real.log x := by
  sorry

-- theorem test (a b : ℝ) (ha : 0 < a)  (hb : a < b) : (fun x ↦ exp x - 1) =O[𝓟 <| Set.Ioo a b] fun x ↦ x := by
--   sorry
--   -- bound

-- Asymptotics.isEquivalent_iff_tendsto_one

theorem mertens_third :
  IsEquivalent atTop (fun x ↦ ∏ p in primesBelow (⌊x⌋₊ + 1), (1 - (p : ℝ)⁻¹)) (fun x ↦ exp (- mertens₃Const) * (Real.log x)⁻¹) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · have h₀ := mertens_third_log_isLittleO_one
    rw [Asymptotics.isLittleO_one_iff] at h₀
    have h₁ := tendsto_exp_nhds_zero_nhds_one.comp h₀
    apply h₁.congr'
    filter_upwards [eventually_gt_atTop 1] with x hx
    simp
    rw [exp_sub, sub_eq_add_neg, exp_sum]
    congr 1
    · apply prod_congr rfl
      intro p hp
      simp only [mem_primesBelow] at hp
      have hp' : 1 < (p:ℝ) := mod_cast hp.2.one_lt
      rw [exp_log]
      rw [sub_pos, inv_lt_one₀ (by linarith)]
      exact hp'
    · rw [add_comm, exp_add, exp_neg (Real.log _), exp_log]
      apply Real.log_pos hx
  · filter_upwards [eventually_gt_atTop 100] with x hx
    apply _root_.ne_of_gt
    bound
    -- have : 0 < Real.log x := by bound
    -- positivity


#print axioms mertens_third


end MertensThird
