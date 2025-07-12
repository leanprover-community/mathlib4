/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Computability.AkraBazzi.GrowsPolynomially
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Akra-Bazzi theorem: the sum transform

We develop further required preliminaries for the theorem, up to the sum transform.

## Main definitions and results

* `AkraBazziRecurrence T g a b r`: the predicate stating that `T : ℕ → ℝ` satisfies an Akra-Bazzi
  recurrence with parameters `g`, `a`, `b` and `r` as above.
* `GrowsPolynomially`: The growth condition that `g` must satisfy for the theorem to apply.
  It roughly states that
  `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for u between b*n and n for any constant `b ∈ (0,1)`.
* `sumTransform`: The transformation which turns a function `g` into
  `n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)`.


## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

open Finset Real Filter Asymptotics
open scoped Topology

/-!
#### Definition of Akra-Bazzi recurrences

This section defines the predicate `AkraBazziRecurrence T g a b r` which states that `T`
satisfies the recurrence
`T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)`
with appropriate conditions on the various parameters.
-/

/-- An Akra-Bazzi recurrence is a function that satisfies the recurrence
`T n = (∑ i, a i * T (r i n)) + g n`. -/
structure AkraBazziRecurrence {α : Type*} [Fintype α] [Nonempty α]
    (T : ℕ → ℝ) (g : ℝ → ℝ) (a : α → ℝ) (b : α → ℝ) (r : α → ℕ → ℕ) where
  /-- Point below which the recurrence is in the base case -/
  n₀ : ℕ
  /-- `n₀` is always `> 0` -/
  n₀_gt_zero : 0 < n₀
  /-- The `a`'s are nonzero -/
  a_pos : ∀ i, 0 < a i
  /-- The `b`'s are nonzero -/
  b_pos : ∀ i, 0 < b i
  /-- The b's are less than 1 -/
  b_lt_one : ∀ i, b i < 1
  /-- `g` is nonnegative -/
  g_nonneg : ∀ x ≥ 0, 0 ≤ g x
  /-- `g` grows polynomially -/
  g_grows_poly : AkraBazziRecurrence.GrowsPolynomially g
  /-- The actual recurrence -/
  h_rec (n : ℕ) (hn₀ : n₀ ≤ n) : T n = (∑ i, a i * T (r i n)) + g n
  /-- Base case: `T(n) > 0` whenever `n < n₀` -/
  T_gt_zero' (n : ℕ) (hn : n < n₀) : 0 < T n
  /-- The `r`'s always reduce `n` -/
  r_lt_n : ∀ i n, n₀ ≤ n → r i n < n
  /-- The `r`'s approximate the `b`'s -/
  dist_r_b : ∀ i, (fun n => (r i n : ℝ) - b i * n) =o[atTop] fun n => n / (log n) ^ 2

namespace AkraBazziRecurrence

section min_max

variable {α : Type*} [Finite α] [Nonempty α]

/-- Smallest `b i` -/
noncomputable def min_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_min b

/-- Largest `b i` -/
noncomputable def max_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_max b

@[aesop safe apply]
lemma min_bi_le {b : α → ℝ} (i : α) : b (min_bi b) ≤ b i :=
  Classical.choose_spec (Finite.exists_min b) i

@[aesop safe apply]
lemma max_bi_le {b : α → ℝ} (i : α) : b i ≤ b (max_bi b) :=
  Classical.choose_spec (Finite.exists_max b) i

end min_max

lemma isLittleO_self_div_log_id :
    (fun (n : ℕ) => n / log n ^ 2) =o[atTop] (fun (n : ℕ) => (n : ℝ)) := by
  calc (fun (n : ℕ) => (n : ℝ) / log n ^ 2) = fun (n : ℕ) => (n : ℝ) * ((log n) ^ 2)⁻¹ := by
                  simp_rw [div_eq_mul_inv]
         _ =o[atTop] fun (n : ℕ) => (n : ℝ) * 1⁻¹ := by
                  refine IsBigO.mul_isLittleO (isBigO_refl _ _) ?_
                  refine IsLittleO.inv_rev ?main ?zero
                  case zero => simp
                  case main => calc
                    _ = (fun (_ : ℕ) => ((1 : ℝ) ^ 2)) := by simp
                    _ =o[atTop] (fun (n : ℕ) => (log n) ^ 2) :=
                          IsLittleO.pow (IsLittleO.natCast_atTop
                            <| isLittleO_const_log_atTop) (by norm_num)
         _ = (fun (n : ℕ) => (n : ℝ)) := by ext; simp

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)
section
include R

lemma dist_r_b' : ∀ᶠ n in atTop, ∀ i, ‖(r i n : ℝ) - b i * n‖ ≤ n / log n ^ 2 := by
  rw [Filter.eventually_all]
  intro i
  simpa using IsLittleO.eventuallyLE (R.dist_r_b i)

lemma eventually_b_le_r : ∀ᶠ (n : ℕ) in atTop, ∀ i, (b i : ℝ) * n - (n / log n ^ 2) ≤ r i n := by
  filter_upwards [R.dist_r_b'] with n hn
  intro i
  have h₁ : 0 ≤ b i := le_of_lt <| R.b_pos _
  rw [sub_le_iff_le_add, add_comm, ← sub_le_iff_le_add]
  calc (b i : ℝ) * n - r i n = ‖b i * n‖ - ‖(r i n : ℝ)‖ := by
                            simp only [norm_mul, RCLike.norm_natCast,
                                       Real.norm_of_nonneg h₁]
                         _ ≤ ‖(b i * n : ℝ) - r i n‖ := norm_sub_norm_le _ _
                         _ = ‖(r i n : ℝ) - b i * n‖ := norm_sub_rev _ _
                         _ ≤ n / log n ^ 2 := hn i

lemma eventually_r_le_b : ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n ≤ (b i : ℝ) * n + (n / log n ^ 2) := by
  filter_upwards [R.dist_r_b'] with n hn
  intro i
  calc r i n = b i * n + (r i n - b i * n) := by ring
             _ ≤ b i * n + ‖r i n - b i * n‖ := by gcongr; exact Real.le_norm_self _
             _ ≤ b i * n + n / log n ^ 2 := by gcongr; exact hn i

lemma eventually_r_lt_n : ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n < n := by
  filter_upwards [eventually_ge_atTop R.n₀] with n hn
  exact fun i => R.r_lt_n i n hn

lemma eventually_bi_mul_le_r : ∀ᶠ (n : ℕ) in atTop, ∀ i, (b (min_bi b) / 2) * n ≤ r i n := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo (by positivity : 0 < b (min_bi b) / 2)
  filter_upwards [hlo', R.eventually_b_le_r] with n hn hn'
  intro i
  simp only [Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ))] at hn
  calc b (min_bi b) / 2 * n = b (min_bi b) * n - b (min_bi b) / 2 * n := by ring
                          _ ≤ b (min_bi b) * n - ‖n / log n ^ 2‖ := by gcongr
                          _ ≤ b i * n - ‖n / log n ^ 2‖ := by gcongr; aesop
                          _ = b i * n - n / log n ^ 2 := by
                                congr
                                exact Real.norm_of_nonneg <| by positivity
                          _ ≤ r i n := hn' i

lemma bi_min_div_two_lt_one : b (min_bi b) / 2 < 1 := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  calc b (min_bi b) / 2 < b (min_bi b) := by aesop (add safe apply div_two_lt_of_pos)
                      _ < 1 := R.b_lt_one _

lemma bi_min_div_two_pos : 0 < b (min_bi b) / 2 := div_pos (R.b_pos _) (by norm_num)

lemma exists_eventually_const_mul_le_r :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop, ∀ i, c * n ≤ r i n := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  exact ⟨b (min_bi b) / 2, ⟨⟨by positivity, R.bi_min_div_two_lt_one⟩, R.eventually_bi_mul_le_r⟩⟩

lemma eventually_r_ge (C : ℝ) : ∀ᶠ (n : ℕ) in atTop, ∀ i, C ≤ r i n := by
  obtain ⟨c, hc_mem, hc⟩ := R.exists_eventually_const_mul_le_r
  filter_upwards [eventually_ge_atTop ⌈C / c⌉₊, hc] with n hn₁ hn₂
  have h₁ := hc_mem.1
  intro i
  calc C = c * (C / c) := by
            rw [← mul_div_assoc]
            exact (mul_div_cancel_left₀ _ (by positivity)).symm
       _ ≤ c * ⌈C / c⌉₊ := by gcongr; simp [Nat.le_ceil]
       _ ≤ c * n := by gcongr
       _ ≤ r i n := hn₂ i

lemma tendsto_atTop_r (i : α) : Tendsto (r i) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have := R.eventually_r_ge b
  rw [Filter.eventually_all] at this
  exact_mod_cast this i

lemma tendsto_atTop_r_real (i : α) : Tendsto (fun n => (r i n : ℝ)) atTop atTop :=
  Tendsto.comp tendsto_natCast_atTop_atTop (R.tendsto_atTop_r i)

lemma exists_eventually_r_le_const_mul :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n ≤ c * n := by
  let c := b (max_bi b) + (1 - b (max_bi b)) / 2
  have h_max_bi_pos : 0 < b (max_bi b) := R.b_pos _
  have h_max_bi_lt_one : 0 < 1 - b (max_bi b) := by
    have : b (max_bi b) < 1 := R.b_lt_one _
    linarith
  have hc_pos : 0 < c := by positivity
  have h₁ : 0 < (1 - b (max_bi b)) / 2 := by positivity
  have hc_lt_one : c < 1 :=
    calc b (max_bi b) + (1 - b (max_bi b)) / 2 = b (max_bi b) * (1 / 2) + 1 / 2 := by ring
                                             _ < 1 * (1 / 2) + 1 / 2 := by
                                                  gcongr
                                                  exact R.b_lt_one _
                                             _ = 1 := by norm_num
  refine ⟨c, ⟨hc_pos, hc_lt_one⟩, ?_⟩
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo h₁
  filter_upwards [hlo', R.eventually_r_le_b] with n hn hn'
  intro i
  rw [Real.norm_of_nonneg (by positivity)] at hn
  simp only [Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ))] at hn
  calc r i n ≤ b i * n + n / log n ^ 2 := by exact hn' i
             _ ≤ b i * n + (1 - b (max_bi b)) / 2 * n := by gcongr
             _ = (b i + (1 - b (max_bi b)) / 2) * n := by ring
             _ ≤ (b (max_bi b) + (1 - b (max_bi b)) / 2) * n := by gcongr; exact max_bi_le _

lemma eventually_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < r i n := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually_gt_atTop 0

lemma eventually_log_b_mul_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < log (b i * n) := by
  rw [Filter.eventually_all]
  intro i
  have h : Tendsto (fun (n : ℕ) => log (b i * n)) atTop atTop :=
    Tendsto.comp tendsto_log_atTop
      <| Tendsto.const_mul_atTop (b_pos R i) tendsto_natCast_atTop_atTop
  exact h.eventually_gt_atTop 0

@[aesop safe apply] lemma T_pos (n : ℕ) : 0 < T n := by
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    cases lt_or_ge n R.n₀ with
    | inl hn => exact R.T_gt_zero' n hn -- n < R.n₀
    | inr hn => -- R.n₀ ≤ n
      rw [R.h_rec n hn]
      have := R.g_nonneg
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos ?sum_elems univ_nonempty) (by aesop)
      exact fun i _ => mul_pos (R.a_pos i) <| h_ind _ (R.r_lt_n i _ hn)

@[aesop safe apply]
lemma T_nonneg (n : ℕ) : 0 ≤ T n := le_of_lt <| R.T_pos n

end

/-!
#### Smoothing function

We define `ε` as the "smoothing function" `fun n => 1 / log n`, which will be used in the form of a
factor of `1 ± ε n` needed to make the induction step go through.

This is its own definition to make it easier to switch to a different smoothing function.
For example, choosing `1 / log n ^ δ` for a suitable choice of `δ` leads to a slightly tighter
theorem at the price of a more complicated proof.

This part of the file then proves several properties of this function that will be needed later in
the proof.
-/

/-- The "smoothing function" is defined as `1 / log n`. This is defined as an `ℝ → ℝ` function
as opposed to `ℕ → ℝ` since this is more convenient for the proof, where we need to e.g. take
derivatives. -/
noncomputable def smoothingFn (n : ℝ) : ℝ := 1 / log n

local notation "ε" => smoothingFn

lemma one_add_smoothingFn_le_two {x : ℝ} (hx : exp 1 ≤ x) : 1 + ε x ≤ 2 := by
  simp only [smoothingFn, ← one_add_one_eq_two]
  gcongr
  have : 1 < x := by
    calc 1 = exp 0 := by simp
         _ < exp 1 := by simp
         _ ≤ x := hx
  rw [div_le_one (log_pos this)]
  calc 1 = log (exp 1) := by simp
       _ ≤ log x := log_le_log (exp_pos _) hx

lemma isLittleO_smoothingFn_one : ε =o[atTop] (fun _ => (1 : ℝ)) := by
  unfold smoothingFn
  refine isLittleO_of_tendsto (fun _ h => False.elim <| one_ne_zero h) ?_
  simp only [one_div, div_one]
  exact Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop

lemma isEquivalent_one_add_smoothingFn_one : (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : ℝ)) :=
  IsEquivalent.add_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

lemma isEquivalent_one_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : ℝ)) :=
  IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

lemma growsPolynomially_one_sub_smoothingFn : GrowsPolynomially fun x => 1 - ε x :=
  GrowsPolynomially.of_isEquivalent_const isEquivalent_one_sub_smoothingFn_one

lemma growsPolynomially_one_add_smoothingFn : GrowsPolynomially fun x => 1 + ε x :=
  GrowsPolynomially.of_isEquivalent_const isEquivalent_one_add_smoothingFn_one

lemma eventually_one_sub_smoothingFn_gt_const_real (c : ℝ) (hc : c < 1) :
    ∀ᶠ (x : ℝ) in atTop, c < 1 - ε x := by
  have h₁ : Tendsto (fun x => 1 - ε x) atTop (𝓝 1) := by
    rw [← isEquivalent_const_iff_tendsto one_ne_zero]
    exact isEquivalent_one_sub_smoothingFn_one
  rw [tendsto_order] at h₁
  exact h₁.1 c hc

lemma eventually_one_sub_smoothingFn_gt_const (c : ℝ) (hc : c < 1) :
    ∀ᶠ (n : ℕ) in atTop, c < 1 - ε n :=
  Eventually.natCast_atTop (p := fun n => c < 1 - ε n)
    <| eventually_one_sub_smoothingFn_gt_const_real c hc

lemma eventually_one_sub_smoothingFn_pos_real : ∀ᶠ (x : ℝ) in atTop, 0 < 1 - ε x :=
  eventually_one_sub_smoothingFn_gt_const_real 0 zero_lt_one

lemma eventually_one_sub_smoothingFn_pos : ∀ᶠ (n : ℕ) in atTop, 0 < 1 - ε n :=
  (eventually_one_sub_smoothingFn_pos_real).natCast_atTop

lemma eventually_one_sub_smoothingFn_nonneg : ∀ᶠ (n : ℕ) in atTop, 0 ≤ 1 - ε n := by
  filter_upwards [eventually_one_sub_smoothingFn_pos] with n hn; exact le_of_lt hn

include R in
lemma eventually_one_sub_smoothingFn_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < 1 - ε (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r_real i).eventually eventually_one_sub_smoothingFn_pos_real

@[aesop safe apply]
lemma differentiableAt_smoothingFn {x : ℝ} (hx : 1 < x) : DifferentiableAt ℝ ε x := by
  have : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  change DifferentiableAt ℝ (fun z => 1 / log z) x
  simp_rw [one_div]
  exact DifferentiableAt.inv (differentiableAt_log (by positivity)) this

@[aesop safe apply]
lemma differentiableAt_one_sub_smoothingFn {x : ℝ} (hx : 1 < x) :
    DifferentiableAt ℝ (fun z => 1 - ε z) x :=
  DifferentiableAt.sub (differentiableAt_const _) <| differentiableAt_smoothingFn hx

lemma differentiableOn_one_sub_smoothingFn : DifferentiableOn ℝ (fun z => 1 - ε z) (Set.Ioi 1) :=
  fun _ hx => (differentiableAt_one_sub_smoothingFn hx).differentiableWithinAt

@[aesop safe apply]
lemma differentiableAt_one_add_smoothingFn {x : ℝ} (hx : 1 < x) :
    DifferentiableAt ℝ (fun z => 1 + ε z) x :=
  DifferentiableAt.add (differentiableAt_const _) <| differentiableAt_smoothingFn hx

lemma differentiableOn_one_add_smoothingFn : DifferentiableOn ℝ (fun z => 1 + ε z) (Set.Ioi 1) :=
  fun _ hx => (differentiableAt_one_add_smoothingFn hx).differentiableWithinAt

lemma deriv_smoothingFn {x : ℝ} (hx : 1 < x) : deriv ε x = -x⁻¹ / (log x ^ 2) := by
  have : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  change deriv (fun z => 1 / log z) x = -x⁻¹ / (log x ^ 2)
  rw [deriv_fun_div] <;> aesop

lemma isLittleO_deriv_smoothingFn : deriv ε =o[atTop] fun x => x⁻¹ := calc
  deriv ε =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
            filter_upwards [eventually_gt_atTop 1] with x hx
            rw [deriv_smoothingFn hx]
    _ = fun x => (-x * log x ^ 2)⁻¹ := by
            simp_rw [neg_div, div_eq_mul_inv, ← mul_inv, neg_inv, neg_mul]
    _ =o[atTop] fun x => (x * 1)⁻¹ := by
            refine IsLittleO.inv_rev ?_ ?_
            · refine IsBigO.mul_isLittleO
                (by rw [isBigO_neg_right]; aesop (add safe isBigO_refl)) ?_
              rw [isLittleO_one_left_iff]
              exact Tendsto.comp tendsto_norm_atTop_atTop
                <| Tendsto.comp (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
            · exact Filter.Eventually.of_forall (fun x hx => by rw [mul_one] at hx; simp [hx])
    _ = fun x => x⁻¹ := by simp

lemma eventually_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) := calc
  deriv (fun x => 1 - ε x) =ᶠ[atTop] -(deriv ε) := by
        filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) := by
        filter_upwards [eventually_gt_atTop 1] with x hx
        simp [deriv_smoothingFn hx, neg_div]

lemma eventually_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := calc
  deriv (fun x => 1 + ε x) =ᶠ[atTop] deriv ε := by
          filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
          filter_upwards [eventually_gt_atTop 1] with x hx
          simp [deriv_smoothingFn hx]

lemma isLittleO_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =o[atTop] fun (x : ℝ) => x⁻¹ := calc
  deriv (fun x => 1 - ε x) =ᶠ[atTop] fun z => -(deriv ε z) := by
          filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := by rw [isLittleO_neg_left]; exact isLittleO_deriv_smoothingFn

lemma isLittleO_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =o[atTop] fun (x : ℝ) => x⁻¹ := calc
  deriv (fun x => 1 + ε x) =ᶠ[atTop] fun z => deriv ε z := by
          filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := isLittleO_deriv_smoothingFn

lemma eventually_one_add_smoothingFn_pos : ∀ᶠ (n : ℕ) in atTop, 0 < 1 + ε n := by
  have h₁ := isLittleO_smoothingFn_one
  rw [isLittleO_iff] at h₁
  refine Eventually.natCast_atTop (p := fun n => 0 < 1 + ε n) ?_
  filter_upwards [h₁ (by norm_num : (0 : ℝ) < 1 / 2), eventually_gt_atTop 1] with x _ hx'
  have : 0 < log x := Real.log_pos hx'
  change 0 < 1 + 1 / log x
  positivity

include R in
lemma eventually_one_add_smoothingFn_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < 1 + ε (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually (f := r i) eventually_one_add_smoothingFn_pos

lemma eventually_one_add_smoothingFn_nonneg : ∀ᶠ (n : ℕ) in atTop, 0 ≤ 1 + ε n := by
  filter_upwards [eventually_one_add_smoothingFn_pos] with n hn; exact le_of_lt hn

lemma strictAntiOn_smoothingFn : StrictAntiOn ε (Set.Ioi 1) := by
  change StrictAntiOn (fun x => 1 / log x) (Set.Ioi 1)
  simp_rw [one_div]
  refine StrictAntiOn.comp_strictMonoOn inv_strictAntiOn ?log fun _ hx => log_pos hx
  refine StrictMonoOn.mono strictMonoOn_log (fun x hx => ?_)
  exact Set.Ioi_subset_Ioi zero_le_one hx

lemma strictMonoOn_one_sub_smoothingFn :
    StrictMonoOn (fun (x : ℝ) => (1 : ℝ) - ε x) (Set.Ioi 1) := by
  simp_rw [sub_eq_add_neg]
  exact StrictMonoOn.const_add (StrictAntiOn.neg <| strictAntiOn_smoothingFn) 1

lemma strictAntiOn_one_add_smoothingFn : StrictAntiOn (fun (x : ℝ) => (1 : ℝ) + ε x) (Set.Ioi 1) :=
  StrictAntiOn.const_add strictAntiOn_smoothingFn 1

section
include R

lemma isEquivalent_smoothingFn_sub_self (i : α) :
    (fun (n : ℕ) => ε (b i * n) - ε n) ~[atTop] fun n => -log (b i) / (log n) ^ 2 := by
  calc (fun (n : ℕ) => 1 / log (b i * n) - 1 / log n)
        =ᶠ[atTop] fun (n : ℕ) => (log n - log (b i * n)) / (log (b i * n) * log n) := by
            filter_upwards [eventually_gt_atTop 1, R.eventually_log_b_mul_pos] with n hn hn'
            have h_log_pos : 0 < log n := Real.log_pos <| by aesop
            simp only [one_div]
            rw [inv_sub_inv (by have := hn' i; positivity) (by aesop)]
      _ =ᶠ[atTop] (fun (n : ℕ) ↦ (log n - log (b i) - log n) / ((log (b i) + log n) * log n)) := by
            filter_upwards [eventually_ne_atTop 0] with n hn
            have : 0 < b i := R.b_pos i
            rw [log_mul (by positivity) (by aesop), sub_add_eq_sub_sub]
      _ = (fun (n : ℕ) => -log (b i) / ((log (b i) + log n) * log n)) := by ext; congr; ring
      _ ~[atTop] (fun (n : ℕ) => -log (b i) / (log n * log n)) := by
            refine IsEquivalent.div (IsEquivalent.refl) <| IsEquivalent.mul ?_ (IsEquivalent.refl)
            have : (fun (n : ℕ) => log (b i) + log n) = fun (n : ℕ) => log n + log (b i) := by
              ext; simp [add_comm]
            rw [this]
            exact IsEquivalent.add_isLittleO IsEquivalent.refl
              <| IsLittleO.natCast_atTop (f := fun (_ : ℝ) => log (b i))
                isLittleO_const_log_atTop
      _ = (fun (n : ℕ) => -log (b i) / (log n) ^ 2) := by ext; congr 1; rw [← pow_two]

lemma isTheta_smoothingFn_sub_self (i : α) :
    (fun (n : ℕ) => ε (b i * n) - ε n) =Θ[atTop] fun n => 1 / (log n) ^ 2 := by
  calc (fun (n : ℕ) => ε (b i * n) - ε n) =Θ[atTop] fun n => (-log (b i)) / (log n) ^ 2 := by
                  exact (R.isEquivalent_smoothingFn_sub_self i).isTheta
    _ = fun (n : ℕ) => (-log (b i)) * 1 / (log n) ^ 2 := by simp only [mul_one]
    _ = fun (n : ℕ) => -log (b i) * (1 / (log n) ^ 2) := by simp_rw [← mul_div_assoc]
    _ =Θ[atTop] fun (n : ℕ) => 1 / (log n) ^ 2 := by
                  have : -log (b i) ≠ 0 := by
                    rw [neg_ne_zero]
                    exact Real.log_ne_zero_of_pos_of_ne_one
                            (R.b_pos i) (ne_of_lt <| R.b_lt_one i)
                  rw [← isTheta_const_mul_right this]

/-!
#### Akra-Bazzi exponent `p`

Every Akra-Bazzi recurrence has an associated exponent, denoted by `p : ℝ`, such that
`∑ a_i b_i^p = 1`.  This section shows the existence and uniqueness of this exponent `p` for any
`R : AkraBazziRecurrence`, and defines `R.asympBound` to be the asymptotic bound satisfied by `R`,
namely `n^p (1 + ∑_{u < n} g(u) / u^(p+1))`. -/

@[continuity]
lemma continuous_sumCoeffsExp : Continuous (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine continuous_finset_sum Finset.univ fun i _ => Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))

lemma strictAnti_sumCoeffsExp : StrictAnti (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  rw [← Finset.sum_fn]
  refine Finset.sum_induction_nonempty _ _ (fun _ _ => StrictAnti.add) univ_nonempty ?terms
  refine fun i _ => StrictAnti.const_mul ?_ (R.a_pos i)
  exact Real.strictAnti_rpow_of_base_lt_one (R.b_pos i) (R.b_lt_one i)

lemma tendsto_zero_sumCoeffsExp : Tendsto (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) atTop (𝓝 0) := by
  have h₁ : Finset.univ.sum (fun _ : α => (0 : ℝ)) = 0 := by simp
  rw [← h₁]
  refine tendsto_finset_sum (univ : Finset α) (fun i _ => ?_)
  rw [← mul_zero (a i)]
  refine Tendsto.mul (by simp) <| tendsto_rpow_atTop_of_base_lt_one _ ?_ (R.b_lt_one i)
  have := R.b_pos i
  linarith

lemma tendsto_atTop_sumCoeffsExp : Tendsto (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) atBot atTop := by
  have h₁ : Tendsto (fun p : ℝ => (a (max_bi b) : ℝ) * b (max_bi b) ^ p) atBot atTop :=
    Tendsto.const_mul_atTop (R.a_pos (max_bi b)) <| tendsto_rpow_atBot_of_base_lt_one _
      (by have := R.b_pos (max_bi b); linarith) (R.b_lt_one _)
  refine tendsto_atTop_mono (fun p => ?_) h₁
  refine Finset.single_le_sum (f := fun i => (a i : ℝ) * b i ^ p) (fun i _ => ?_) (mem_univ _)
  have h₁ : 0 < a i := R.a_pos i
  have h₂ : 0 < b i := R.b_pos i
  positivity

lemma one_mem_range_sumCoeffsExp : 1 ∈ Set.range (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine mem_range_of_exists_le_of_exists_ge R.continuous_sumCoeffsExp ?le_one ?ge_one
  case le_one =>
    exact R.tendsto_zero_sumCoeffsExp.eventually_le_const zero_lt_one |>.exists
  case ge_one =>
    exact R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop _ |>.exists

/-- The function x ↦ ∑ a_i b_i^x is injective. This implies the uniqueness of `p`. -/
lemma injective_sumCoeffsExp : Function.Injective (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) :=
    R.strictAnti_sumCoeffsExp.injective

end

variable (a b) in
/-- The exponent `p` associated with a particular Akra-Bazzi recurrence. -/
noncomputable irreducible_def p : ℝ := Function.invFun (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) 1

include R in
-- Cannot be @[simp] because `T`, `g`, `r`, and `R` can not be inferred by `simp`.
lemma sumCoeffsExp_p_eq_one : ∑ i, a i * (b i) ^ p a b = 1 := by
  simp only [p]
  exact Function.invFun_eq (by rw [← Set.mem_range]; exact R.one_mem_range_sumCoeffsExp)

/-!
#### The sum transform

This section defines the "sum transform" of a function `g` as
`∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)`,
and uses it to define `asympBound` as the bound satisfied by an Akra-Bazzi recurrence.

Several properties of the sum transform are then proven.
-/

/-- The transformation which turns a function `g` into
`n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)`. -/
noncomputable def sumTransform (p : ℝ) (g : ℝ → ℝ) (n₀ n : ℕ) :=
  n ^ p * ∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1)

lemma sumTransform_def {p : ℝ} {g : ℝ → ℝ} {n₀ n : ℕ} :
    sumTransform p g n₀ n = n ^ p * ∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1) := rfl


variable (g) (a) (b)
/-- The asymptotic bound satisfied by an Akra-Bazzi recurrence, namely
`n^p (1 + ∑_{u < n} g(u) / u^(p+1))`. -/
noncomputable def asympBound (n : ℕ) : ℝ := n ^ p a b + sumTransform (p a b) g 0 n

lemma asympBound_def {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b + sumTransform (p a b) g 0 n := rfl

variable {g} {a} {b}

lemma asympBound_def' {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b * (1 + (∑ u ∈ range n, g u / u ^ (p a b + 1))) := by
  simp [asympBound_def, sumTransform, mul_add, mul_one]

section
include R

lemma asympBound_pos (n : ℕ) (hn : 0 < n) : 0 < asympBound g a b n := by
  calc 0 < (n : ℝ) ^ p a b * (1 + 0) := by aesop (add safe Real.rpow_pos_of_pos)
       _ ≤ asympBound g a b n := by
                    simp only [asympBound_def']
                    gcongr n ^ p a b * (1 + ?_)
                    have := R.g_nonneg
                    aesop (add safe Real.rpow_nonneg,
                               safe div_nonneg,
                               safe Finset.sum_nonneg)

lemma eventually_asympBound_pos : ∀ᶠ (n : ℕ) in atTop, 0 < asympBound g a b n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact R.asympBound_pos n hn

lemma eventually_asympBound_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < asympBound g a b (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually R.eventually_asympBound_pos

lemma eventually_atTop_sumTransform_le :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ i, sumTransform (p a b) g (r i n) n ≤ c * g n := by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_le_nat hc₁_mem
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  refine ⟨max c₂ (c₂ / c₁ ^ (p a b + 1)), by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, R.eventually_r_pos, R.eventually_r_lt_n, eventually_gt_atTop 0]
    with n hn₁ hn₂ hrpos hr_lt_n hn_pos
  intro i
  have hrpos_i := hrpos i
  have g_nonneg : 0 ≤ g n := R.g_nonneg n (by positivity)
  cases le_or_gt 0 (p a b + 1) with
  | inl hp => -- 0 ≤ p a b + 1
    calc sumTransform (p a b) g (r i n) n
           = n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := by rfl
         _ ≤ n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
                gcongr with u hu
                rw [Finset.mem_Ico] at hu
                have hu' : u ∈ Set.Icc (r i n) n := ⟨hu.1, by omega⟩
                refine hn₂ u ?_
                rw [Set.mem_Icc]
                refine ⟨?_, by norm_cast; omega⟩
                calc c₁ * n ≤ r i n := by exact hn₁ i
                          _ ≤ u := by exact_mod_cast hu'.1
         _ ≤ n ^ (p a b) * (∑ _u ∈ Finset.Ico (r i n) n, c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
                  gcongr with u hu; rw [Finset.mem_Ico] at hu; exact hu.1
         _ ≤ n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / r i n ^ (p a b + 1)) := by
                  gcongr; exact Finset.sum_le_card_nsmul _ _ _ (fun x _ => by rfl)
         _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / r i n ^ (p a b + 1)) := by
                  rw [nsmul_eq_mul, mul_assoc]
         _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
                  congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
         _ ≤ n ^ (p a b) * n * (c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
                  gcongr; simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg]
         _ ≤ n ^ (p a b) * n * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
                gcongr; exact hn₁ i
         _ = c₂ * g n * n ^ ((p a b) + 1) / (c₁ * n) ^ ((p a b) + 1) := by
                rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
         _ = c₂ * g n * n ^ ((p a b) + 1) / (n ^ ((p a b) + 1) * c₁ ^ ((p a b) + 1)) := by
                rw [mul_comm c₁, Real.mul_rpow (by positivity) (by positivity)]
         _ = c₂ * g n * (n ^ ((p a b) + 1) / (n ^ ((p a b) + 1))) / c₁ ^ ((p a b) + 1) := by ring
         _ = c₂ * g n / c₁ ^ ((p a b) + 1) := by rw [div_self (by positivity), mul_one]
         _ = (c₂ / c₁ ^ ((p a b) + 1)) * g n := by ring
         _ ≤ max c₂ (c₂ / c₁ ^ ((p a b) + 1)) * g n := by gcongr; exact le_max_right _ _
  | inr hp => -- p a b + 1 < 0
    calc sumTransform (p a b) g (r i n) n
           = n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := by rfl
         _ ≤ n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
                gcongr with u hu
                rw [Finset.mem_Ico] at hu
                have hu' : u ∈ Set.Icc (r i n) n := ⟨hu.1, by omega⟩
                refine hn₂ u ?_
                rw [Set.mem_Icc]
                refine ⟨?_, by norm_cast; omega⟩
                calc c₁ * n ≤ r i n := by exact hn₁ i
                          _ ≤ u     := by exact_mod_cast hu'.1
         _ ≤ n ^ (p a b) * (∑ _u ∈ Finset.Ico (r i n) n, c₂ * g n / n ^ ((p a b) + 1)) := by
                gcongr n ^ (p a b) * (Finset.Ico (r i n) n).sum (fun _ => c₂ * g n / ?_) with u hu
                rw [Finset.mem_Ico] at hu
                have : 0 < u := calc
                  0 < r i n := by exact hrpos_i
                  _ ≤ u := by exact hu.1
                exact rpow_le_rpow_of_exponent_nonpos (by positivity)
                  (by exact_mod_cast (le_of_lt hu.2)) (le_of_lt hp)
         _ ≤ n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / n ^ (p a b + 1)) := by
                  gcongr; exact Finset.sum_le_card_nsmul _ _ _ (fun x _ => by rfl)
         _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / n ^ (p a b + 1)) := by
                  rw [nsmul_eq_mul, mul_assoc]
         _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
                  congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
         _ ≤ n ^ (p a b) * n * (c₂ * g n / n ^ ((p a b) + 1)) := by
                gcongr; simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg]
         _ = c₂ * (n^((p a b) + 1) / n ^ ((p a b) + 1)) * g n := by
                rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
         _ = c₂ * g n := by rw [div_self (by positivity), mul_one]
         _ ≤ max c₂ (c₂ / c₁ ^ ((p a b) + 1)) * g n := by gcongr; exact le_max_left _ _

lemma eventually_atTop_sumTransform_ge :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ i, c * g n ≤ sumTransform (p a b) g (r i n) n := by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_ge_nat hc₁_mem
  obtain ⟨c₃, hc₃_mem, hc₃⟩ := R.exists_eventually_r_le_const_mul
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  have hc₃' : 0 < (1 - c₃) := by have := hc₃_mem.2; linarith
  refine ⟨min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁^((p a b) + 1)), by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, hc₃, R.eventually_r_pos, R.eventually_r_lt_n, eventually_gt_atTop 0]
    with n hn₁ hn₂ hn₃ hrpos hr_lt_n hn_pos
  intro i
  have hrpos_i := hrpos i
  have g_nonneg : 0 ≤ g n := R.g_nonneg n (by positivity)
  cases le_or_gt 0 (p a b + 1) with
  | inl hp => -- 0 ≤ (p a b) + 1
    calc sumTransform (p a b) g (r i n) n
           = n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))    := rfl
         _ ≥ n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, c₂ * g n / u^((p a b) + 1)) := by
                gcongr with u hu
                rw [Finset.mem_Ico] at hu
                have hu' : u ∈ Set.Icc (r i n) n := ⟨hu.1, by omega⟩
                refine hn₂ u ?_
                rw [Set.mem_Icc]
                refine ⟨?_, by norm_cast; omega⟩
                calc c₁ * n ≤ r i n := by exact hn₁ i
                          _ ≤ u     := by exact_mod_cast hu'.1
         _ ≥ n ^ (p a b) * (∑ _u ∈ Finset.Ico (r i n) n, c₂ * g n / n ^ ((p a b) + 1)) := by
                gcongr with u hu
                · rw [Finset.mem_Ico] at hu
                  have := calc 0 < r i n := hrpos_i
                              _ ≤ u := hu.1
                  positivity
                · rw [Finset.mem_Ico] at hu
                  exact le_of_lt hu.2
         _ ≥ n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / n ^ (p a b + 1)) := by
                gcongr; exact Finset.card_nsmul_le_sum _ _ _ (fun x _ => by rfl)
         _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / n ^ (p a b + 1)) := by
                rw [nsmul_eq_mul, mul_assoc]
         _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
                congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
         _ ≥ n ^ (p a b) * (n - c₃ * n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
                gcongr; exact hn₃ i
         _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / n ^ ((p a b) + 1)) := by ring
         _ = c₂ * (1 - c₃) * g n * (n ^ ((p a b) + 1) / n ^ ((p a b) + 1)) := by
                rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
         _ = c₂ * (1 - c₃) * g n := by rw [div_self (by positivity), mul_one]
         _ ≥ min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁ ^ ((p a b) + 1)) * g n := by
                gcongr; exact min_le_left _ _
  | inr hp => -- (p a b) + 1 < 0
    calc sumTransform (p a b) g (r i n) n
        = n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u^((p a b) + 1))        := by rfl
      _ ≥ n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
             gcongr with u hu
             rw [Finset.mem_Ico] at hu
             have hu' : u ∈ Set.Icc (r i n) n := ⟨hu.1, by omega⟩
             refine hn₂ u ?_
             rw [Set.mem_Icc]
             refine ⟨?_, by norm_cast; omega⟩
             calc c₁ * n ≤ r i n := by exact hn₁ i
                       _ ≤ u := by exact_mod_cast hu'.1
      _ ≥ n ^ (p a b) * (∑ _u ∈ Finset.Ico (r i n) n, c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
             gcongr n^(p a b) * (Finset.Ico (r i n) n).sum (fun _ => c₂ * g n / ?_) with u hu
             · rw [Finset.mem_Ico] at hu
               have := calc 0 < r i n := hrpos_i
                           _ ≤ u := hu.1
               positivity
             · rw [Finset.mem_Ico] at hu
               exact rpow_le_rpow_of_exponent_nonpos (by positivity)
                 (by exact_mod_cast hu.1) (le_of_lt hp)
      _ ≥ n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / r i n ^ (p a b + 1)) := by
             gcongr; exact Finset.card_nsmul_le_sum _ _ _ (fun x _ => by rfl)
      _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / r i n ^ (p a b + 1)) := by
             rw [nsmul_eq_mul, mul_assoc]
      _ ≥ n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / (c₁ * n) ^ (p a b + 1)) := by
             gcongr n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / ?_)
             exact rpow_le_rpow_of_exponent_nonpos (by positivity) (hn₁ i) (le_of_lt hp)
      _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
             congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
      _ ≥ n ^ (p a b) * (n - c₃ * n) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
             gcongr; exact hn₃ i
      _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by ring
      _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / (c₁ ^ ((p a b) + 1) * n ^ ((p a b) + 1))) := by
             rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (n ^ ((p a b) + 1) / n ^ ((p a b) + 1)) * (1 - c₃) * c₂ * g n / c₁ ^ ((p a b) + 1) := by
             rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
      _ = (1 - c₃) * c₂ / c₁ ^ ((p a b) + 1) * g n := by
             rw [div_self (by positivity), one_mul]; ring
      _ ≥ min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁ ^ ((p a b) + 1)) * g n := by
             gcongr; exact min_le_right _ _

end


end AkraBazziRecurrence
