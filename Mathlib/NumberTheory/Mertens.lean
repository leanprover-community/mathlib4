/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib

open Filter Nat Real Finset
open Asymptotics
open MeasureTheory
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


theorem log_factorial (n : ℕ) :
  Real.log (n)! = ∑ d ∈ Finset.range (n+1), ↑(n / d) * Λ d := by
  induction n with
  | zero => simp
  | succ n h_ind =>
    rw [Nat.factorial_succ]
    push_cast
    rw [mul_comm, Real.log_mul (by positivity) (by norm_cast)]
    simp_rw [Nat.succ_div, cast_add, add_mul, Finset.sum_add_distrib, h_ind]
    congr 1
    · apply Finset.sum_subset
      · intro d hd
        simp at hd ⊢
        linarith
      intro d hd hdnin
      obtain rfl : d = n+1 := by
        simp_all
        linarith
      simp only [_root_.mul_eq_zero, cast_eq_zero, Nat.div_eq_zero_iff,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, lt_add_iff_pos_right, zero_lt_one,
        or_true, true_or]
    · push_cast
      simp_rw [boole_mul, ← Finset.sum_filter]
      rw [Nat.filter_dvd_eq_divisors (add_one_ne_zero n)]
      exact_mod_cast ArithmeticFunction.vonMangoldt_sum.symm



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

theorem isBigO_fun : (fun x ↦ Real.log x / (x * (x - 1)))
    =O[atTop] fun x ↦ x ^ (-3 / 2:ℝ) := by
  have hlog := isLittleO_log_rpow_atTop (show 0 < (1/2:ℝ) by norm_num)
  have hpoly : (fun x ↦ x^2) =O[atTop] fun x:ℝ ↦ x * (x - 1) := by
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
  have := hpoly.inv_rev ?inv
  case inv =>
    filter_upwards [eventually_ne_atTop 0] with a ha ha'
    simp_all
  apply (hlog.isBigO.mul this).congr'
  · simp_rw [div_eq_mul_inv]
    rfl
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp_rw [← rpow_natCast, ← rpow_neg hx.le, ← rpow_add hx]
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
    apply Finset.sum_nonneg
    intro k __
    have := ArithmeticFunction.vonMangoldt_nonneg (n:=k)
    positivity
  apply sum_le_tsum (Finset.range (a+1)) _ (sum_strictPow_convergent)
  intro k _
  have := ArithmeticFunction.vonMangoldt_nonneg (n:=k)
  positivity


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

theorem Nat.le_floor_add_one (x : ℝ) : x ≤ ⌊x⌋₊ + 1 := by calc
  x ≤ ⌈x⌉₊ := Nat.le_ceil x
  _ ≤ ⌊x⌋₊ + 1 := mod_cast (Nat.ceil_le_floor_add_one x)

example : atTop.map Nat.cast = (atTop : Filter ℝ) := by

  apply le_antisymm
  · apply tendsto_natCast_atTop_atTop

  apply Filter.le_map
  simp only [mem_atTop_sets, ge_iff_le, Set.mem_image, forall_exists_index]


  sorry

-- example : atTop.comap Nat.floor = (atTop : Filter ℝ) := by
--   -- apply Filter.comap_embedding_atTop


--   apply le_antisymm
--   · apply tendsto_natCast_atTop_atTop

--   apply Filter.le_map
--   simp only [mem_atTop_sets, ge_iff_le, Set.mem_image, forall_exists_index]


  -- sorry
-- something something GaloisConnection?
theorem Asymptotics.IsBigO.nat_floor {f g : ℕ → ℝ} (h : f =O[⊤] g) :
  (fun x ↦ f (Nat.floor x)) =O[⊤] (fun x ↦ (g (Nat.floor x)) : ℝ → ℝ) := by
  apply h.comp_tendsto tendsto_top


open Filter
-- ouchie
/- There should be some general theorem: given f : ℕ → ℝ and g h : ℝ → ℝ, got from f n - g n =O h n
 to f ⌊x⌋₊ - g x =O h x under certain "smoothnes"/monotonicity assumptions on g -/
theorem E₁_isBigO_one : E₁ =O[𝓟 <| Set.Ici (3/2:ℝ)] (fun _ ↦ (1:ℝ)) := by
  have h₀ : (fun t ↦ Real.log t - Real.log (⌊t⌋₊)) =O[𝓟 <| Set.Ici (3/2:ℝ)] (fun t ↦ Real.log t - Real.log (t-1)) := by
    have h1 (t : ℝ) (ht : 1 < t) : Real.log (t-1) ≤ Real.log (⌊t⌋₊) := by
      gcongr
      · linarith only [ht]
      · linarith only [Nat.le_floor_add_one t]
    have h2 (t : ℝ) (ht : 1 ≤ t) : Real.log (⌊t⌋₊) ≤ Real.log t := by
      gcongr
      · exact_mod_cast Nat.floor_pos.mpr ht
      · apply Nat.floor_le (zero_le_one.trans ht)
    apply Eventually.isBigO
    simp only [norm_eq_abs, eventually_principal, Set.mem_Ici]
    intro t ht
    rw [abs_of_nonneg (by linarith only [h2 t (by linarith)])]
    gcongr
    · linarith
    · linarith only [Nat.le_floor_add_one t]
  have h₁ : (fun t ↦ Real.log t - Real.log (t-1)) =O[𝓟 <| Set.Ici (3/2:ℝ)] (fun _ ↦ (1:ℝ)) := by
    apply IsBigO.trans _ (Asymptotics.isBigO_const_const (100:ℝ) one_ne_zero _)
    apply Filter.Eventually.isBigO
    simp only [norm_eq_abs, eventually_principal, Set.mem_Ici]
    intro x hx
    rw [abs_of_nonneg ?nonneg]
    case nonneg =>
      rw [sub_nonneg]
      gcongr <;> linarith
    rw [← Real.log_div]
    · apply (Real.log_le_self _).trans
      · rw [div_le_iff₀] <;> linarith
      apply div_nonneg (by linarith)
      linarith
    · linarith
    · exact sub_ne_zero_of_ne (by linarith)
  simp_rw [E₁_eq]
  apply ((mertens_first.mono le_top).nat_floor.mono le_top |>.sub (h₀.trans h₁)).congr <;>
  · intro x
    ring

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

theorem extracted_1 (t : ℝ) :
  MeasureTheory.Integrable (fun a ↦ a⁻¹ * (Real.log a)⁻¹)
    (MeasureTheory.volume.restrict (Set.Icc (3 / 2) t)) := by
  rw [← MeasureTheory.IntegrableOn]
  have hsub : Set.Icc (3 / 2) t ⊆ {0}ᶜ := by
    simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le, isEmpty_Prop,
      ofNat_pos, div_pos_iff_of_pos_left, IsEmpty.forall_iff]
  apply ((continuousOn_inv₀.mono hsub).mul ((continuousOn_log.mono hsub).inv₀ ?_))
    |>.integrableOn_compact isCompact_Icc
  intro x
  simp only [Set.mem_Icc, ne_eq, not_or, and_imp]
  intro hx _
  apply (Real.log_pos (by linarith)).ne.symm

theorem integrable_inv_mul_log_inv_sq (t : ℝ) (ht : 3 / 2 ≤ t) (hlogt : Real.log t ≠ 0) :
  MeasureTheory.Integrable (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2)
    (MeasureTheory.volume.restrict (Set.Icc (3 / 2) t)) := by
  sorry

theorem IntegrableAtFilter.principal  {α : Type*} {ε : Type*} [MeasurableSpace α] [ENorm ε] [TopologicalSpace ε] (f : α → ε) (S : Set α) (mu : MeasureTheory.Measure α := by volume_tac) :
  IntegrableAtFilter f (𝓟 S) mu ↔ IntegrableOn f S mu := by
  sorry
theorem tmp' : (𝓟 (Set.Ici (3 / 2))).IsMeasurablyGenerated := by
  exact principal_isMeasurablyGenerated_iff.mpr trivial
-- This was a pain point: I want uniform bounds to show integrability of E₁, since E₁ is definitely not continuous
-- Perhaps one could argue, E₁ is a step function plus a
theorem extracted_2 (t : ℝ) (ht : 3 / 2 ≤ t) (hlogt : Real.log t ≠ 0) :
  MeasureTheory.Integrable (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a)
    (MeasureTheory.volume.restrict (Set.Icc (3 / 2) t)) := by
  have isBigO : (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2 * E₁ a) =O[𝓟 (Set.Ici (3/2))] (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2) := by
    simp_rw [mul_assoc]
    convert (isBigO_refl (fun a ↦ a⁻¹ * (Real.log a)⁻¹ ^ 2) _).mul E₁_isBigO_one using 1
    · ext; ring
    · ext; ring
  have hmg : (𝓟 (Set.Ici (3 / 2 : ℝ))).IsMeasurablyGenerated := principal_isMeasurablyGenerated_iff.mpr
    measurableSet_Ici
  rw [← IntegrableOn]
  have := isBigO.integrableAtFilter («μ» := volume) sorry sorry
  sorry

theorem helper2 (t : ℝ) (ht : 3/2 ≤ t) :
    ∫ (t : ℝ) in Set.Ioc (3 / 2) t, (t⁻¹ * (Real.log t)⁻¹) =
      Real.log (Real.log t) - Real.log (Real.log (3/2)) := by
  have hsub : Set.uIcc (3 / 2) t ⊆ {0}ᶜ := by
    simp only [Set.subset_compl_singleton_iff]
    refine Set.not_mem_uIcc_of_lt (by norm_num) (by linarith)
  have htzero : t ≠ 0 := by linarith
  have hlogzero : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne.symm
  have h {x : ℝ} (hx : 3/2 ≤ x) : HasDerivAt (Real.log ∘ Real.log) (x⁻¹ * (Real.log x)⁻¹) x := by
    rw [mul_comm]
    apply HasDerivAt.comp
    · refine hasDerivAt_log (Real.log_pos (by linarith)).ne.symm
    · refine hasDerivAt_log (by linarith)
  rw [← intervalIntegral.integral_of_le ht]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x
    simpa only [h, Set.uIcc_of_le ht, Set.mem_Icc, and_imp] using fun hx _ ↦ h hx
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le ht, MeasureTheory.IntegrableOn]
  exact extracted_1 t

theorem mertens_second : (fun t : ℝ ↦ (∑ p ∈ primesBelow (⌊t⌋₊+1), 1 / (p : ℝ)) - Real.log (Real.log t))
    =O[atTop] (fun n ↦ 1 / Real.log n) := by
  let ϕ (x : ℝ) : ℝ := (Real.log x)⁻¹
  let c (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0
  have hlog (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt Real.log (x⁻¹) (x) := by
    convert Real.hasDerivAt_log (hx)
  have h (x : ℝ) (hx : 3/2 ≤ x) := HasDerivAt.comp x (hasDerivAt_inv ?ne_zero) (hlog x (by linarith))
  case ne_zero =>
    simp only [ne_eq, log_eq_zero, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> linarith only [hx]
  have hϕ (x : ℝ) (hx : 3/2 ≤ x): HasDerivAt ϕ (- x⁻¹ * (Real.log x)⁻¹ ^ 2) x := by
    convert h x hx using 1
    ring
  have h' (b : ℝ) : ContinuousOn (fun x:ℝ ↦ - x⁻¹ * (Real.log x)⁻¹^2) (Set.Icc (3/2) b) := by
    intro x
    simp only [Set.mem_Icc, inv_pow, neg_mul, and_imp]
    intro hx _
    apply ContinuousAt.continuousWithinAt
    have : x ≠ 0 := by linarith
    apply (continuousAt_inv₀ this).mul ((continuousAt_inv₀ _).comp ((continuousAt_id.log this).pow 2)) |>.neg
    simp only [id_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, log_eq_zero,
      not_or]
    refine ⟨this, ?_, ?_⟩ <;> linarith

  have hfloor : ⌊(3/2 : ℝ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have (b : ℝ) (hb : 3/2 ≤ b) :
      ∑ k ∈ Finset.Ioc 1 ⌊b⌋₊, ϕ k * c k = ϕ b * ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k - ϕ (3/2) * 0 -
        ∫ t in Set.Ioc (3/2) b, deriv ϕ t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
    convert sum_mul_eq_sub_sub_integral_mul c ?_ hb ?_ ?_
    · rw [hfloor]
    · apply (sum_eq_zero ..).symm
      simp only [hfloor, mem_Icc, _root_.zero_le, true_and, ite_eq_right_iff, div_eq_zero_iff,
        log_eq_zero, cast_eq_zero, cast_eq_one, c]
      omega
    · norm_num
    · simp only [Set.mem_Icc, and_imp, c]
      intro t ht _
      exact (h t ht).differentiableAt
    · apply MeasureTheory.LocallyIntegrableOn.integrableOn_isCompact
      · apply ContinuousOn.locallyIntegrableOn _ (by measurability)
        apply (h' b).congr
        intro x
        simp only [Set.mem_Icc, inv_pow, neg_mul, and_imp, c]
        intro hx _
        rw [(hϕ x hx).deriv]
        ring
      · exact isCompact_Icc
  simp only [mul_zero, sub_zero, ϕ, c, ← sum_filter, Icc_filter_prime, E₁_eq_add] at this

  have eqn (t : ℝ) (ht : 3/2 ≤ t) :=
    have hlogt : Real.log t ≠ 0 := by sorry
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
        ∫ (t : ℝ) in Set.Ioc (3 / 2) t, deriv (fun x ↦ (Real.log x)⁻¹) t * (Real.log t + E₁ t) := by
      convert this t ht using 2
      rw [mul_add, inv_mul_cancel₀ hlogt]
    _ =
     (1 + (Real.log t)⁻¹ * E₁ t) -
        ∫ (t : ℝ) in Set.Ioc (3 / 2) t, (- t⁻¹ * (Real.log t)⁻¹ ^ 2) * (Real.log t + E₁ t) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)]
      intro x
      simp only [Set.mem_Ioc, add_sub_cancel, inv_pow, neg_mul, and_imp]
      intro hx _
      rw [(hϕ x hx.le).deriv]
      ring
    _ =
     (1 + (Real.log t)⁻¹ * E₁ t) +
        (∫ (t : ℝ) in Set.Icc (3 / 2) t, t⁻¹ * (Real.log t)⁻¹ + t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) := by
      simp_rw [← MeasureTheory.integral_Icc_eq_integral_Ioc, neg_mul, MeasureTheory.integral_neg, sub_neg_eq_add, mul_add]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)]
      intro x
      simp only [Set.mem_Icc, add_left_inj, and_imp]
      intro hx _
      have := (Real.log_pos (by linarith)).ne.symm
      field_simp
      ring
    _ =
     (1 + (Real.log t)⁻¹ * E₁ t) +
        ((∫ (t : ℝ) in Set.Icc (3 / 2) t, t⁻¹ * (Real.log t)⁻¹) + ∫ (t : ℝ) in Set.Icc (3 / 2) t, t⁻¹ * (Real.log t)⁻¹ ^ 2 * E₁ t) := by
      rw [MeasureTheory.integral_add (extracted_1 _) sorry]
  sorry
