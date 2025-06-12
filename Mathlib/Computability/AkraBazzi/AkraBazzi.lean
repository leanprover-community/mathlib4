/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Computability.AkraBazzi.GrowsPolynomially
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Divide-and-conquer recurrences and the Akra-Bazzi theorem

A divide-and-conquer recurrence is a function `T : ℕ → ℝ` that satisfies a recurrence relation of
the form `T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)` for large enough `n`, where `r_i(n)` is some
function where `‖r_i(n) - b_i n‖ ∈ o(n / (log n)^2)` for every `i`, the `a_i`'s are some positive
coefficients, and the `b_i`'s are reals `∈ (0,1)`. (Note that this can be improved to
`O(n / (log n)^(1+ε))`, this is left as future work.) These recurrences arise mainly in the
analysis of divide-and-conquer algorithms such as mergesort or Strassen's algorithm for matrix
multiplication.  This class of algorithms works by dividing an instance of the problem of size `n`,
into `k` smaller instances, where the `i`'th instance is of size roughly `b_i n`, and calling itself
recursively on those smaller instances. `T(n)` then represents the running time of the algorithm,
and `g(n)` represents the running time required to actually divide up the instance and process the
answers that come out of the recursive calls. Since virtually all such algorithms produce instances
that are only approximately of size `b_i n` (they have to round up or down at the very least), we
allow the instance sizes to be given by some function `r_i(n)` that approximates `b_i n`.

The Akra-Bazzi theorem gives the asymptotic order of such a recurrence: it states that
`T(n) ∈ Θ(n^p (1 + ∑_{u=0}^{n-1} g(n) / u^{p+1}))`,
where `p` is the unique real number such that `∑ a_i b_i^p = 1`.

## Main definitions and results

* `AkraBazziRecurrence T g a b r`: the predicate stating that `T : ℕ → ℝ` satisfies an Akra-Bazzi
  recurrence with parameters `g`, `a`, `b` and `r` as above.
* `GrowsPolynomially`: The growth condition that `g` must satisfy for the theorem to apply.
  It roughly states that
  `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for u between b*n and n for any constant `b ∈ (0,1)`.
* `sumTransform`: The transformation which turns a function `g` into
  `n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)`.
* `asympBound`: The asymptotic bound satisfied by an Akra-Bazzi recurrence, namely
  `n^p (1 + ∑ g(u) / u^(p+1))`
* `isTheta_asympBound`: The main result stating that
  `T(n) ∈ Θ(n^p (1 + ∑_{u=0}^{n-1} g(n) / u^{p+1}))`

## Implementation

Note that the original version of the theorem has an integral rather than a sum in the above
expression, and first considers the `T : ℝ → ℝ` case before moving on to `ℕ → ℝ`. We prove the
above version with a sum, as it is simpler and more relevant for algorithms.

## TODO

* Specialize this theorem to the very common case where the recurrence is of the form
  `T(n) = ℓT(r_i(n)) + g(n)`
  where `g(n) ∈ Θ(n^t)` for some `t`. (This is often called the "master theorem" in the literature.)
* Add the original version of the theorem with an integral instead of a sum.

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
                    _ = (fun (_ : ℕ) => ((1 : ℝ) ^ 2))     := by simp
                    _ =o[atTop] (fun (n : ℕ) => (log n)^2) :=
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
                            simp only [norm_mul, RCLike.norm_natCast, sub_left_inj,
                                       Nat.cast_eq_zero, Real.norm_of_nonneg h₁]
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
  show DifferentiableAt ℝ (fun z => 1 / log z) x
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
  show deriv (fun z => 1 / log z) x = -x⁻¹ / (log x ^ 2)
  rw [deriv_div] <;> aesop

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
        filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_sub] <;> aesop
    _ =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) := by
        filter_upwards [eventually_gt_atTop 1] with x hx
        simp [deriv_smoothingFn hx, neg_div]

lemma eventually_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := calc
  deriv (fun x => 1 + ε x) =ᶠ[atTop] deriv ε := by
          filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_add] <;> aesop
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
          filter_upwards [eventually_gt_atTop 1] with x hx
          simp [deriv_smoothingFn hx]

lemma isLittleO_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =o[atTop] fun (x : ℝ) => x⁻¹ := calc
  deriv (fun x => 1 - ε x) =ᶠ[atTop] fun z => -(deriv ε z) := by
          filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_sub] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := by rw [isLittleO_neg_left]; exact isLittleO_deriv_smoothingFn

lemma isLittleO_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =o[atTop] fun (x : ℝ) => x⁻¹ := calc
  deriv (fun x => 1 + ε x) =ᶠ[atTop] fun z => deriv ε z := by
          filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_add] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := isLittleO_deriv_smoothingFn

lemma eventually_one_add_smoothingFn_pos : ∀ᶠ (n : ℕ) in atTop, 0 < 1 + ε n := by
  have h₁ := isLittleO_smoothingFn_one
  rw [isLittleO_iff] at h₁
  refine Eventually.natCast_atTop (p := fun n => 0 < 1 + ε n) ?_
  filter_upwards [h₁ (by norm_num : (0 : ℝ) < 1/2), eventually_gt_atTop 1] with x _ hx'
  have : 0 < log x := Real.log_pos hx'
  show 0 < 1 + 1 / log x
  positivity

include R in
lemma eventually_one_add_smoothingFn_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < 1 + ε (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually (f := r i) eventually_one_add_smoothingFn_pos

lemma eventually_one_add_smoothingFn_nonneg : ∀ᶠ (n : ℕ) in atTop, 0 ≤ 1 + ε n := by
  filter_upwards [eventually_one_add_smoothingFn_pos] with n hn; exact le_of_lt hn

lemma strictAntiOn_smoothingFn : StrictAntiOn ε (Set.Ioi 1) := by
  show StrictAntiOn (fun x => 1 / log x) (Set.Ioi 1)
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
    (fun (n : ℕ) => ε (b i * n) - ε n) ~[atTop] fun n => -log (b i) / (log n)^2 := by
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
      _ = (fun (n : ℕ) => -log (b i) / (log n)^2) := by ext; congr 1; rw [← pow_two]

lemma isTheta_smoothingFn_sub_self (i : α) :
    (fun (n : ℕ) => ε (b i * n) - ε n) =Θ[atTop] fun n => 1 / (log n)^2 := by
  calc (fun (n : ℕ) => ε (b i * n) - ε n) =Θ[atTop] fun n => (-log (b i)) / (log n)^2 := by
                  exact (R.isEquivalent_smoothingFn_sub_self i).isTheta
    _ = fun (n : ℕ) => (-log (b i)) * 1 / (log n)^2 := by simp only [mul_one]
    _ = fun (n : ℕ) => -log (b i) * (1 / (log n)^2) := by simp_rw [← mul_div_assoc]
    _ =Θ[atTop] fun (n : ℕ) => 1 / (log n)^2 := by
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
  n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p + 1)

lemma sumTransform_def {p : ℝ} {g : ℝ → ℝ} {n₀ n : ℕ} :
    sumTransform p g n₀ n = n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p + 1) := rfl


variable (g) (a) (b)
/-- The asymptotic bound satisfied by an Akra-Bazzi recurrence, namely
`n^p (1 + ∑_{u < n} g(u) / u^(p+1))`. -/
noncomputable def asympBound (n : ℕ) : ℝ := n ^ p a b + sumTransform (p a b) g 0 n

lemma asympBound_def {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b + sumTransform (p a b) g 0 n := rfl

variable {g} {a} {b}

lemma asympBound_def' {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b * (1 + (∑ u ∈ range n, g u / u ^ (p a b + 1))) := by
  simp [asympBound_def, sumTransform, mul_add, mul_one, Finset.sum_Ico_eq_sum_range]

section
include R

lemma asympBound_pos (n : ℕ) (hn : 0 < n) : 0 < asympBound g a b n := by
  calc 0 < (n : ℝ) ^ p a b * (1 + 0) := by aesop (add safe Real.rpow_pos_of_pos)
       _ ≤ asympBound g a b n := by
                    simp only [asympBound_def']
                    gcongr n^p a b * (1 + ?_)
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

/-!
#### Technical lemmas

The next several lemmas are technical lemmas leading up to `rpow_p_mul_one_sub_smoothingFn_le` and
`rpow_p_mul_one_add_smoothingFn_ge`, which are key steps in the main proof.
-/

lemma eventually_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    deriv (fun z => z ^ p * (1 - ε z))
      =ᶠ[atTop] fun z => p * z ^ (p-1) * (1 - ε z) + z ^ (p-1) / (log z ^ 2) := calc
  deriv (fun x => x ^ p * (1 - ε x))
    =ᶠ[atTop] fun x => deriv (· ^ p) x * (1 - ε x) + x ^ p * deriv (1 - ε ·) x := by
            filter_upwards [eventually_gt_atTop 1] with x hx
            rw [deriv_mul]
            · exact differentiableAt_rpow_const_of_ne _ (by positivity)
            · exact differentiableAt_one_sub_smoothingFn hx
  _ =ᶠ[atTop] fun x => p * x ^ (p-1) * (1 - ε x) + x ^ p * (x⁻¹ / (log x ^ 2)) := by
            filter_upwards [eventually_gt_atTop 1, eventually_deriv_one_sub_smoothingFn]
              with x hx hderiv
            rw [hderiv, Real.deriv_rpow_const (Or.inl <| by positivity)]
  _ =ᶠ[atTop] fun x => p * x ^ (p-1) * (1 - ε x) + x ^ (p-1) / (log x ^ 2) := by
            filter_upwards [eventually_gt_atTop 0] with x hx
            rw [mul_div, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity), sub_eq_add_neg]

lemma eventually_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    deriv (fun z => z ^ p * (1 + ε z))
      =ᶠ[atTop] fun z => p * z ^ (p-1) * (1 + ε z) - z ^ (p-1) / (log z ^ 2) := calc
  deriv (fun x => x ^ p * (1 + ε x))
    =ᶠ[atTop] fun x => deriv (· ^ p) x * (1 + ε x) + x ^ p * deriv (1 + ε ·) x := by
            filter_upwards [eventually_gt_atTop 1] with x hx
            rw [deriv_mul]
            · exact differentiableAt_rpow_const_of_ne _ (by positivity)
            · exact differentiableAt_one_add_smoothingFn hx
  _ =ᶠ[atTop] fun x => p * x ^ (p-1) * (1 + ε x) - x ^ p * (x⁻¹ / (log x ^ 2)) := by
            filter_upwards [eventually_gt_atTop 1, eventually_deriv_one_add_smoothingFn]
              with x hx hderiv
            simp [hderiv, Real.deriv_rpow_const (Or.inl <| by positivity), neg_div, sub_eq_add_neg]
  _ =ᶠ[atTop] fun x => p * x ^ (p-1) * (1 + ε x) - x ^ (p-1) / (log x ^ 2) := by
            filter_upwards [eventually_gt_atTop 0] with x hx
            simp [mul_div, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity), sub_eq_add_neg]

lemma isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    deriv (fun z => z ^ p * (1 - ε z)) ~[atTop] fun z => p * z ^ (p-1) := calc
  deriv (fun z => z ^ p * (1 - ε z))
    =ᶠ[atTop] fun z => p * z ^ (p-1) * (1 - ε z) + z^(p-1) / (log z ^ 2) :=
        eventually_deriv_rpow_p_mul_one_sub_smoothingFn p
  _ ~[atTop] fun z => p * z ^ (p-1) := by
        refine IsEquivalent.add_isLittleO ?one ?two
        case one => calc
          (fun z => p * z ^ (p-1) * (1 - ε z)) ~[atTop] fun z => p * z ^ (p-1) * 1 :=
                IsEquivalent.mul IsEquivalent.refl isEquivalent_one_sub_smoothingFn_one
          _ = fun z => p * z ^ (p-1) := by ext; ring
        case two => calc
          (fun z => z ^ (p-1) / (log z ^ 2)) =o[atTop] fun z => z ^ (p-1) / 1 := by
                      simp_rw [div_eq_mul_inv]
                      refine IsBigO.mul_isLittleO (isBigO_refl _ _)
                        (IsLittleO.inv_rev ?_ (by simp))
                      rw [isLittleO_const_left]
                      refine Or.inr <| Tendsto.comp tendsto_norm_atTop_atTop ?_
                      exact Tendsto.comp (g := fun z => z ^ 2)
                        (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
          _ = fun z => z ^ (p-1) := by ext; simp
          _ =Θ[atTop] fun z => p * z ^ (p-1) := by
                      exact IsTheta.const_mul_right hp <| isTheta_refl _ _

lemma isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    deriv (fun z => z ^ p * (1 + ε z)) ~[atTop] fun z => p * z ^ (p-1) := calc
  deriv (fun z => z ^ p * (1 + ε z))
    =ᶠ[atTop] fun z => p * z ^ (p-1) * (1 + ε z) - z ^ (p-1) / (log z ^ 2) :=
        eventually_deriv_rpow_p_mul_one_add_smoothingFn p
  _ ~[atTop] fun z => p * z ^ (p-1) := by
        refine IsEquivalent.add_isLittleO ?one ?two
        case one => calc
          (fun z => p * z ^ (p-1) * (1 + ε z)) ~[atTop] fun z => p * z ^ (p-1) * 1 :=
                IsEquivalent.mul IsEquivalent.refl isEquivalent_one_add_smoothingFn_one
          _ = fun z => p * z ^ (p-1) := by ext; ring
        case two => calc
          (fun z => -(z ^ (p-1) / (log z ^ 2))) =o[atTop] fun z => z ^ (p-1) / 1 := by
                      simp_rw [isLittleO_neg_left, div_eq_mul_inv]
                      refine IsBigO.mul_isLittleO (isBigO_refl _ _)
                        (IsLittleO.inv_rev ?_ (by simp))
                      rw [isLittleO_const_left]
                      refine Or.inr <| Tendsto.comp tendsto_norm_atTop_atTop ?_
                      exact Tendsto.comp (g := fun z => z ^ 2)
                        (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
          _ = fun z => z ^ (p-1) := by ext; simp
          _ =Θ[atTop] fun z => p * z ^ (p-1) := by
                      exact IsTheta.const_mul_right hp <| isTheta_refl _ _

lemma isTheta_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖) =Θ[atTop] fun z => z ^ (p-1) := by
  refine IsTheta.norm_left ?_
  calc (fun x => deriv (fun z => z ^ p * (1 - ε z)) x) =Θ[atTop] fun z => p * z ^ (p-1) :=
            (isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn hp).isTheta
    _ =Θ[atTop] fun z => z ^ (p-1) :=
            IsTheta.const_mul_left hp <| isTheta_refl _ _

lemma isTheta_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖) =Θ[atTop] fun z => z ^ (p-1) := by
  refine IsTheta.norm_left ?_
  calc (fun x => deriv (fun z => z ^ p * (1 + ε z)) x) =Θ[atTop] fun z => p * z ^ (p-1) :=
            (isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn hp).isTheta
    _ =Θ[atTop] fun z => z ^ (p-1) :=
            IsTheta.const_mul_left hp <| isTheta_refl _ _

lemma growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    GrowsPolynomially fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖ := by
  cases eq_or_ne p 0 with
  | inl hp => -- p = 0
    have h₁ : (fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖)
        =ᶠ[atTop] fun z => z⁻¹ / (log z ^ 2) := by
      filter_upwards [eventually_deriv_one_sub_smoothingFn, eventually_gt_atTop 1] with x hx hx_pos
      have : 0 ≤ x⁻¹ / (log x ^ 2) := by
        have hlog : 0 < log x := Real.log_pos hx_pos
        positivity
      simp only [hp, Real.rpow_zero, one_mul, differentiableAt_const, hx, Real.norm_of_nonneg this]
    refine GrowsPolynomially.congr_of_eventuallyEq h₁ ?_
    refine GrowsPolynomially.div (GrowsPolynomially.inv growsPolynomially_id)
      (GrowsPolynomially.pow 2 growsPolynomially_log ?_)
    filter_upwards [eventually_ge_atTop 1] with _ hx
    exact log_nonneg hx
  | inr hp => -- p ≠ 0
    refine GrowsPolynomially.of_isTheta (growsPolynomially_rpow (p-1))
      (isTheta_deriv_rpow_p_mul_one_sub_smoothingFn hp) ?_
    filter_upwards [eventually_gt_atTop 0] with _ _
    positivity

lemma growsPolynomially_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    GrowsPolynomially fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖ := by
  cases eq_or_ne p 0 with
  | inl hp => -- p = 0
    have h₁ : (fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖)
        =ᶠ[atTop] fun z => z⁻¹ / (log z ^ 2) := by
      filter_upwards [eventually_deriv_one_add_smoothingFn, eventually_gt_atTop 1] with x hx hx_pos
      have : 0 ≤ x⁻¹ / (log x ^ 2) := by
        have hlog : 0 < log x := Real.log_pos hx_pos
        positivity
      simp only [neg_div, norm_neg, hp, Real.rpow_zero,
        one_mul, differentiableAt_const, hx, Real.norm_of_nonneg this]
    refine GrowsPolynomially.congr_of_eventuallyEq h₁ ?_
    refine GrowsPolynomially.div (GrowsPolynomially.inv growsPolynomially_id)
      (GrowsPolynomially.pow 2 growsPolynomially_log ?_)
    filter_upwards [eventually_ge_atTop 1] with x hx
    exact log_nonneg hx
  | inr hp => -- p ≠ 0
    refine GrowsPolynomially.of_isTheta (growsPolynomially_rpow (p-1))
      (isTheta_deriv_rpow_p_mul_one_add_smoothingFn hp) ?_
    filter_upwards [eventually_gt_atTop 0] with _ _
    positivity

include R

lemma isBigO_apply_r_sub_b (q : ℝ → ℝ) (hq_diff : DifferentiableOn ℝ q (Set.Ioi 1))
    (hq_poly : GrowsPolynomially fun x => ‖deriv q x‖) (i : α) :
    (fun n => q (r i n) - q (b i * n)) =O[atTop] fun n => (deriv q n) * (r i n - b i * n) := by
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := by have := R.b_pos (min_bi b); positivity
  have hb_lt_one : b' < 1 := calc
    b (min_bi b) / 2 < b (min_bi b) := by exact div_two_lt_of_pos (R.b_pos (min_bi b))
                   _ < 1 := R.b_lt_one (min_bi b)
  have hb : b' ∈ Set.Ioo 0 1 := ⟨hb_pos, hb_lt_one⟩
  have hb' : ∀ i, b' ≤ b i := fun i => calc
    b (min_bi b) / 2 ≤ b i / 2 := by gcongr; aesop
               _ ≤ b i := by exact le_of_lt <| div_two_lt_of_pos (R.b_pos i)
  obtain ⟨c₁, _, c₂, _, hq_poly⟩ := hq_poly b' hb
  rw [isBigO_iff]
  refine ⟨c₂, ?_⟩
  have h_tendsto : Tendsto (fun x => b' * x) atTop atTop :=
    Tendsto.const_mul_atTop hb_pos tendsto_id
  filter_upwards [hq_poly.natCast_atTop, R.eventually_bi_mul_le_r, eventually_ge_atTop R.n₀,
                  eventually_gt_atTop 0, (h_tendsto.eventually_gt_atTop 1).natCast_atTop] with
    n hn h_bi_le_r h_ge_n₀ h_n_pos h_bn
  rw [norm_mul, ← mul_assoc]
  refine Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (b'*n) n) (fun z hz => ?diff) (fun z hz => (hn z hz).2)
    (convex_Icc _ _) ?mem_Icc <| ⟨h_bi_le_r i, by exact_mod_cast (le_of_lt (R.r_lt_n i n h_ge_n₀))⟩
  case diff =>
    refine hq_diff.differentiableAt (Ioi_mem_nhds ?_)
    calc 1 < b' * n := by exact h_bn
         _ ≤ z := hz.1
  case mem_Icc =>
    refine ⟨by gcongr; exact hb' i, ?_⟩
    calc b i * n ≤ 1 * n := by gcongr; exact le_of_lt <| R.b_lt_one i
                 _ = n := by simp

lemma rpow_p_mul_one_sub_smoothingFn_le :
    ∀ᶠ (n : ℕ) in atTop, ∀ i, (r i n) ^ (p a b) * (1 - ε (r i n))
      ≤ (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n) := by
  rw [Filter.eventually_all]
  intro i
  let q : ℝ → ℝ := fun x => x ^ (p a b) * (1 - ε x)
  have h_diff_q : DifferentiableOn ℝ q (Set.Ioi 1) := by
    refine DifferentiableOn.mul
      (DifferentiableOn.mono (differentiableOn_rpow_const _) fun z hz => ?_)
        differentiableOn_one_sub_smoothingFn
    rw [Set.mem_compl_singleton_iff]
    rw [Set.mem_Ioi] at hz
    exact ne_of_gt <| zero_lt_one.trans hz
  have h_deriv_q : deriv q =O[atTop] fun x => x ^ ((p a b) - 1) := calc
    deriv q = deriv fun x => (fun z => z ^ (p a b)) x * (fun z => 1 - ε z) x := by rfl
          _ =ᶠ[atTop] fun x => deriv (fun z => z ^ (p a b)) x * (1 - ε x) +
                  x ^ (p a b) * deriv (fun z => 1 - ε z) x := by
              filter_upwards [eventually_ne_atTop 0, eventually_gt_atTop 1] with x hx hx'
              rw [deriv_mul] <;> aesop
          _ =O[atTop] fun x => x ^ ((p a b) - 1) := by
              refine IsBigO.add ?left ?right
              case left => calc
                (fun x => deriv (fun z => z ^ (p a b)) x * (1 - ε x))
                    =O[atTop] fun x => x ^ ((p a b) - 1) * (1 - ε x) := by
                      exact IsBigO.mul (isBigO_deriv_rpow_const_atTop (p a b)) (isBigO_refl _ _)
                  _ =O[atTop] fun x => x ^ ((p a b) - 1) * 1 := by
                      refine IsBigO.mul (isBigO_refl _ _)
                        isEquivalent_one_sub_smoothingFn_one.isBigO
                  _ = fun x => x ^ ((p a b) - 1) := by ext; rw [mul_one]
              case right => calc
                (fun x => x ^ (p a b) * deriv (fun z => 1 - ε z) x)
                    =O[atTop] (fun x => x ^ (p a b) * x⁻¹) := by
                      exact IsBigO.mul (isBigO_refl _ _) isLittleO_deriv_one_sub_smoothingFn.isBigO
                  _ =ᶠ[atTop] fun x => x ^ ((p a b) - 1) := by
                      filter_upwards [eventually_gt_atTop 0] with x hx
                      rw [← Real.rpow_neg_one, ← Real.rpow_add hx, ← sub_eq_add_neg]
  have h_main_norm : (fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖)
      ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ := by
    refine IsLittleO.eventuallyLE ?_
    calc
      (fun (n : ℕ) => q (r i n) - q (b i * n))
          =O[atTop] fun n => (deriv q n) * (r i n - b i * n) := by
              exact R.isBigO_apply_r_sub_b q h_diff_q
                (growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p a b)) i
        _ =o[atTop] fun n => (deriv q n) * (n / log n ^ 2) := by
              exact IsBigO.mul_isLittleO (isBigO_refl _ _) (R.dist_r_b i)
        _ =O[atTop] fun n => n^((p a b) - 1) * (n / log n ^ 2) := by
              exact IsBigO.mul (IsBigO.natCast_atTop h_deriv_q) (isBigO_refl _ _)
        _ =ᶠ[atTop] fun n => n^(p a b) / (log n) ^ 2 := by
              filter_upwards [eventually_ne_atTop 0] with n hn
              have hn' : (n : ℝ) ≠ 0 := by positivity
              simp [← mul_div_assoc, ← Real.rpow_add_one hn']
        _ = fun (n : ℕ) => (n : ℝ) ^ (p a b) * (1 / (log n)^2) := by
              simp_rw [mul_div, mul_one]
        _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (1 / (log n)^2) := by
              refine IsTheta.symm ?_
              simp_rw [mul_assoc]
              refine IsTheta.const_mul_left ?_ (isTheta_refl _ _)
              have := R.b_pos i; positivity
        _ =Θ[atTop] fun (n : ℕ) => (b i)^(p a b) * n^(p a b) * (ε (b i * n) - ε n) := by
              exact IsTheta.symm <| IsTheta.mul (isTheta_refl _ _)
                <| R.isTheta_smoothingFn_sub_self i
  have h_main : (fun (n : ℕ) => q (r i n) - q (b i * n))
      ≤ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
    calc (fun (n : ℕ) => q (r i n) - q (b i * n))
           ≤ᶠ[atTop] fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖ := by
                filter_upwards with _; exact le_norm_self _
         _ ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ :=
                h_main_norm
         _ =ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
                filter_upwards [eventually_gt_atTop ⌈(b i)⁻¹⌉₊, eventually_gt_atTop 1] with n hn hn'
                refine norm_of_nonneg ?_
                have h₁ := R.b_pos i
                have h₂ : 0 ≤ ε (b i * n) - ε n := by
                  refine sub_nonneg_of_le <|
                    (strictAntiOn_smoothingFn.le_iff_le ?n_gt_one ?bn_gt_one).mpr ?le
                  case n_gt_one =>
                    rwa [Set.mem_Ioi, Nat.one_lt_cast]
                  case bn_gt_one =>
                    calc 1 = b i * (b i)⁻¹ := by rw [mul_inv_cancel₀ (by positivity)]
                        _ ≤ b i * ⌈(b i)⁻¹⌉₊ := by gcongr; exact Nat.le_ceil _
                        _ < b i * n := by gcongr
                  case le => calc b i * n ≤ 1 * n := by have := R.b_lt_one i; gcongr
                                          _ = n := by rw [one_mul]
                positivity
  filter_upwards [h_main] with n hn
  have h₁ : q (b i * n) + (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)
      = (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n) := by
    have := R.b_pos i
    simp only [q, mul_rpow (by positivity : (0 : ℝ) ≤ b i) (by positivity : (0 : ℝ) ≤ n)]
    ring
  show q (r i n) ≤ (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n)
  rw [← h₁, ← sub_le_iff_le_add']
  exact hn

lemma rpow_p_mul_one_add_smoothingFn_ge :
    ∀ᶠ (n : ℕ) in atTop, ∀ i, (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
      ≤ (r i n) ^ (p a b) * (1 + ε (r i n)) := by
  rw [Filter.eventually_all]
  intro i
  let q : ℝ → ℝ := fun x => x ^ (p a b) * (1 + ε x)
  have h_diff_q : DifferentiableOn ℝ q (Set.Ioi 1) := by
    refine DifferentiableOn.mul
        (DifferentiableOn.mono (differentiableOn_rpow_const _) fun z hz => ?_)
        differentiableOn_one_add_smoothingFn
    rw [Set.mem_compl_singleton_iff]
    rw [Set.mem_Ioi] at hz
    exact ne_of_gt <| zero_lt_one.trans hz
  have h_deriv_q : deriv q =O[atTop] fun x => x ^ ((p a b) - 1) := calc
    deriv q = deriv fun x => (fun z => z ^ (p a b)) x * (fun z => 1 + ε z) x := by rfl
          _ =ᶠ[atTop] fun x => deriv (fun z => z ^ (p a b)) x * (1 + ε x)
              + x ^ (p a b) * deriv (fun z => 1 + ε z) x := by
                filter_upwards [eventually_ne_atTop 0, eventually_gt_atTop 1] with x hx hx'
                rw [deriv_mul] <;> aesop
          _ =O[atTop] fun x => x ^ ((p a b) - 1) := by
                refine IsBigO.add ?left ?right
                case left => calc
                  (fun x => deriv (fun z => z ^ (p a b)) x * (1 + ε x))
                      =O[atTop] fun x => x ^ ((p a b) - 1) * (1 + ε x) := by
                        exact IsBigO.mul (isBigO_deriv_rpow_const_atTop (p a b)) (isBigO_refl _ _)
                    _ =O[atTop] fun x => x ^ ((p a b) - 1) * 1 :=
                        IsBigO.mul (isBigO_refl _ _) isEquivalent_one_add_smoothingFn_one.isBigO
                    _ = fun x => x ^ ((p a b) - 1) := by ext; rw [mul_one]
                case right => calc
                  (fun x => x ^ (p a b) * deriv (fun z => 1 + ε z) x)
                      =O[atTop] (fun x => x ^ (p a b) * x⁻¹) := by
                        exact IsBigO.mul (isBigO_refl _ _)
                          isLittleO_deriv_one_add_smoothingFn.isBigO
                    _ =ᶠ[atTop] fun x => x ^ ((p a b) - 1) := by
                        filter_upwards [eventually_gt_atTop 0] with x hx
                        rw [← Real.rpow_neg_one, ← Real.rpow_add hx, ← sub_eq_add_neg]
  have h_main_norm : (fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖)
      ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ := by
    refine IsLittleO.eventuallyLE ?_
    calc
      (fun (n : ℕ) => q (r i n) - q (b i * n))
          =O[atTop] fun n => (deriv q n) * (r i n - b i * n) := by
            exact R.isBigO_apply_r_sub_b q h_diff_q
              (growsPolynomially_deriv_rpow_p_mul_one_add_smoothingFn (p a b)) i
        _ =o[atTop] fun n => (deriv q n) * (n / log n ^ 2) := by
            exact IsBigO.mul_isLittleO (isBigO_refl _ _) (R.dist_r_b i)
        _ =O[atTop] fun n => n ^ ((p a b) - 1) * (n / log n ^ 2) := by
            exact IsBigO.mul (IsBigO.natCast_atTop h_deriv_q) (isBigO_refl _ _)
        _ =ᶠ[atTop] fun n => n ^ (p a b) / (log n) ^ 2 := by
            filter_upwards [eventually_ne_atTop 0] with n hn
            have hn' : (n : ℝ) ≠ 0 := by positivity
            simp [← mul_div_assoc, ← Real.rpow_add_one hn']
        _ = fun (n : ℕ) => (n : ℝ) ^ (p a b) * (1 / (log n) ^ 2) := by simp_rw [mul_div, mul_one]
        _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (1 / (log n) ^ 2) := by
            refine IsTheta.symm ?_
            simp_rw [mul_assoc]
            refine IsTheta.const_mul_left ?_ (isTheta_refl _ _)
            have := R.b_pos i; positivity
        _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
            exact IsTheta.symm <| IsTheta.mul (isTheta_refl _ _)
                  <| R.isTheta_smoothingFn_sub_self i
  have h_main : (fun (n : ℕ) => q (b i * n) - q (r i n))
      ≤ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
    calc (fun (n : ℕ) => q (b i * n) - q (r i n))
           ≤ᶠ[atTop] fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖ := by
              filter_upwards with _; rw [norm_sub_rev]; exact le_norm_self _
         _ ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ :=
              h_main_norm
         _ =ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
              filter_upwards [eventually_gt_atTop ⌈(b i)⁻¹⌉₊, eventually_gt_atTop 1] with n hn hn'
              refine norm_of_nonneg ?_
              have h₁ := R.b_pos i
              have h₂ : 0 ≤ ε (b i * n) - ε n := by
                refine sub_nonneg_of_le <|
                  (strictAntiOn_smoothingFn.le_iff_le ?n_gt_one ?bn_gt_one).mpr ?le
                case n_gt_one =>
                  show 1 < (n : ℝ)
                  rw [Nat.one_lt_cast]
                  exact hn'
                case bn_gt_one =>
                  calc 1 = b i * (b i)⁻¹ := by rw [mul_inv_cancel₀ (by positivity)]
                      _ ≤ b i * ⌈(b i)⁻¹⌉₊ := by gcongr; exact Nat.le_ceil _
                      _ < b i * n := by gcongr
                case le => calc b i * n ≤ 1 * n := by have := R.b_lt_one i; gcongr
                                        _ = n := by rw [one_mul]
              positivity
  filter_upwards [h_main] with n hn
  have h₁ : q (b i * n) - (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)
      = (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n) := by
    have := R.b_pos i
    simp only [q, mul_rpow (by positivity : (0 : ℝ) ≤ b i) (by positivity : (0 : ℝ) ≤ n)]
    ring
  show (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n) ≤ q (r i n)
  rw [← h₁, sub_le_iff_le_add', ← sub_le_iff_le_add]
  exact hn

/-!
#### Main proof

This final section proves the Akra-Bazzi theorem.
-/

lemma base_nonempty {n : ℕ} (hn : 0 < n) : (Finset.Ico (⌊b (min_bi b) / 2 * n⌋₊) n).Nonempty := by
  let b' := b (min_bi b)
  have hb_pos : 0 < b' := R.b_pos _
  simp_rw [Finset.nonempty_Ico]
  exact_mod_cast calc ⌊b' / 2 * n⌋₊ ≤ b' / 2 * n := by exact Nat.floor_le (by positivity)
                                 _ < 1 / 2 * n   := by gcongr; exact R.b_lt_one (min_bi b)
                                 _ ≤ 1 * n       := by gcongr; norm_num
                                 _ = n           := by simp

/-- The main proof of the upper bound part of the Akra-Bazzi theorem. The factor
`1 - ε n` does not change the asymptotic order, but is needed for the induction step to go
through. -/
lemma T_isBigO_smoothingFn_mul_asympBound :
    T =O[atTop] (fun n => (1 - ε n) * asympBound g a b n) := by
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := R.bi_min_div_two_pos
  rw [isBigO_atTop_iff_eventually_exists]
  obtain ⟨c₁, hc₁, h_sumTransform_aux⟩ := R.eventually_atTop_sumTransform_ge
  filter_upwards [eventually_ge_atTop R.n₀,       -- n₀_ge_Rn₀
      eventually_forall_ge_atTop.mpr eventually_one_sub_smoothingFn_pos,    -- h_smoothing_pos
      eventually_forall_ge_atTop.mpr
        <| eventually_one_sub_smoothingFn_gt_const (1/2) (by norm_num),    -- h_smoothing_gt_half
      eventually_forall_ge_atTop.mpr R.eventually_asympBound_pos,            -- h_asympBound_pos
      eventually_forall_ge_atTop.mpr R.eventually_asympBound_r_pos,          -- h_asympBound_r_pos
      (tendsto_nat_floor_mul_atTop b' hb_pos).eventually_forall_ge_atTop
        R.eventually_asympBound_pos,   -- h_asympBound_floor
      eventually_gt_atTop 0,                                                -- n₀_pos
      eventually_forall_ge_atTop.mpr R.eventually_one_sub_smoothingFn_r_pos,  -- h_smoothing_r_pos
      eventually_forall_ge_atTop.mpr R.rpow_p_mul_one_sub_smoothingFn_le,    -- bound1
      (tendsto_nat_floor_mul_atTop b' hb_pos).eventually_forall_ge_atTop
        eventually_one_sub_smoothingFn_pos,   -- h_smoothingFn_floor
      eventually_forall_ge_atTop.mpr h_sumTransform_aux,                     -- h_sumTransform
      eventually_forall_ge_atTop.mpr R.eventually_bi_mul_le_r]               -- h_bi_le_r
    with n₀ n₀_ge_Rn₀ h_smoothing_pos h_smoothing_gt_half
      h_asympBound_pos h_asympBound_r_pos h_asympBound_floor n₀_pos h_smoothing_r_pos
      bound1 h_smoothingFn_floor h_sumTransform h_bi_le_r
  -- Max of the ratio `T(n) / asympBound(n)` over the base case `n ∈ [b * n₀, n₀)`
  have h_base_nonempty := R.base_nonempty n₀_pos
  let base_max : ℝ :=
    (Finset.Ico (⌊b' * n₀⌋₊) n₀).sup' h_base_nonempty
      fun n => T n / ((1 - ε n) * asympBound g a b n)
  -- The big-O constant we are aiming for: max of the base case ratio and what we need to
  -- cancel out the `g(n)` term in the calculation below
  set C := max (2 * c₁⁻¹) base_max with hC
  refine ⟨C, fun n hn => ?_⟩
  -- Base case: statement is true for `b' * n₀ ≤ n < n₀`
  have h_base : ∀ n ∈ Finset.Ico (⌊b' * n₀⌋₊) n₀, T n ≤ C * ((1 - ε n) * asympBound g a b n) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have htmp1 : 0 < 1 - ε n := h_smoothingFn_floor n hn.1
    have htmp2 : 0 < asympBound g a b n := h_asympBound_floor n hn.1
    rw [← _root_.div_le_iff₀ (by positivity)]
    rw [← Finset.mem_Ico] at hn
    calc T n / ((1 - ε ↑n) * asympBound g a b n)
           ≤ (Finset.Ico (⌊b' * n₀⌋₊) n₀).sup' h_base_nonempty
                (fun z => T z / ((1 - ε z) * asympBound g a b z)) :=
                  Finset.le_sup'_of_le _ (b := n) hn le_rfl
         _ ≤ C := le_max_right _ _
  have h_asympBound_pos' : 0 < asympBound g a b n := h_asympBound_pos n hn
  have h_one_sub_smoothingFn_pos' : 0 < 1 - ε n := h_smoothing_pos n hn
  rw [Real.norm_of_nonneg (R.T_nonneg n), Real.norm_of_nonneg (by positivity)]
  -- We now prove all other cases by induction
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    have b_mul_n₀_le_ri i : ⌊b' * ↑n₀⌋₊ ≤ r i n := by
      exact_mod_cast calc ⌊b' * (n₀ : ℝ)⌋₊ ≤ b' * n₀ := Nat.floor_le <| by positivity
                                  _ ≤ b' * n         := by gcongr
                                  _ ≤ r i n          := h_bi_le_r n hn i
    have g_pos : 0 ≤ g n := R.g_nonneg n (by positivity)
    calc
      T n = (∑ i, a i * T (r i n)) + g n := by exact R.h_rec n <| n₀_ge_Rn₀.trans hn
        _ ≤ (∑ i, a i * (C * ((1 - ε (r i n)) * asympBound g a b (r i n)))) + g n := by
            -- Apply the induction hypothesis, or use the base case depending on how large n is
            gcongr (∑ i, a i * ?_) + g n with i _
            · exact le_of_lt <| R.a_pos _
            · if ri_lt_n₀ : r i n < n₀ then
                exact h_base _ <| by
                  simp_all only [gt_iff_lt, Nat.ofNat_pos, div_pos_iff_of_pos_right,
                    eventually_atTop, sub_pos, one_div, mem_Ico, and_imp,
                    forall_true_left, mem_univ, and_self, b', C, base_max]
              else
                push_neg at ri_lt_n₀
                exact h_ind (r i n) (R.r_lt_n _ _ (n₀_ge_Rn₀.trans hn)) ri_lt_n₀
                  (h_asympBound_r_pos _ hn _) (h_smoothing_r_pos n hn i)
        _ = (∑ i, a i * (C * ((1 - ε (r i n)) * ((r i n) ^ (p a b)
                * (1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1))))))) + g n := by
            simp_rw [asympBound_def']
        _ = (∑ i, C * a i * ((r i n) ^ (p a b) * (1 - ε (r i n))
                * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n := by
            congr; ext; ring
        _ ≤ (∑ i, C * a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 - ε n)
                * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n := by
            gcongr (∑ i, C * a i * (?_
                * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n with i
            · have := R.a_pos i
              positivity
            · refine add_nonneg zero_le_one <| Finset.sum_nonneg fun j _ => ?_
              rw [div_nonneg_iff]
              exact Or.inl ⟨R.g_nonneg j (by positivity), by positivity⟩
            · exact bound1 n hn i
        _ = (∑ i, C * a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 - ε n)
                * ((1 + ((∑ u ∈ range n, g u / u ^ ((p a b) + 1))
                - (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))) + g n := by
            congr; ext i; congr
            refine eq_sub_of_add_eq ?_
            rw [add_comm]
            exact add_eq_of_eq_sub <| Finset.sum_Ico_eq_sub _
              <| le_of_lt <| R.r_lt_n i n <| n₀_ge_Rn₀.trans hn
        _ = (∑ i, C * a i * ((b i) ^ (p a b) * (1 - ε n) * ((n ^ (p a b)
                * (1 + (∑ u ∈ range n, g u / u ^ ((p a b) + 1)))
                - n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))
                + g n := by
            congr; ext; ring
        _ = (∑ i, C * a i * ((b i) ^ (p a b) * (1 - ε n)
                * ((asympBound g a b n - sumTransform (p a b) g (r i n) n)))) + g n := by
            simp_rw [asympBound_def', sumTransform_def]
        _ ≤ (∑ i, C * a i * ((b i) ^ (p a b) * (1 - ε n)
                * ((asympBound g a b n - c₁ * g n)))) + g n := by
            gcongr with i
            · have := R.a_pos i
              positivity
            · have := R.b_pos i
              positivity
            · exact h_sumTransform n hn i
        _ = (∑ i, C * (1 - ε n) * ((asympBound g a b n - c₁ * g n))
                * (a i * (b i) ^ (p a b))) + g n := by
            congr; ext; ring
        _ = C * (1 - ε n) * (asympBound g a b n - c₁ * g n) + g n := by
            rw [← Finset.mul_sum, R.sumCoeffsExp_p_eq_one, mul_one]
        _ = C * (1 - ε n) * asympBound g a b n + (1 - C * c₁ * (1 - ε n)) * g n := by ring
        _ ≤ C * (1 - ε n) * asympBound g a b n + 0 := by
            gcongr
            refine mul_nonpos_of_nonpos_of_nonneg ?_ g_pos
            rw [sub_nonpos]
            calc 1 ≤ 2 * (c₁⁻¹ * c₁) * (1/2) := by
                    rw [inv_mul_cancel₀ (by positivity : c₁ ≠ 0)]; norm_num
                 _ = (2 * c₁⁻¹) * c₁ * (1/2) := by ring
                 _ ≤ C * c₁ * (1 - ε n) := by gcongr
                                              · rw [hC]; exact le_max_left _ _
                                              · exact le_of_lt <| h_smoothing_gt_half n hn
        _ = C * ((1 - ε n) * asympBound g a b n) := by ring

/-- The main proof of the lower bound part of the Akra-Bazzi theorem. The factor
`1 + ε n` does not change the asymptotic order, but is needed for the induction step to go
through. -/
lemma smoothingFn_mul_asympBound_isBigO_T :
    (fun (n : ℕ) => (1 + ε n) * asympBound g a b n) =O[atTop] T := by
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := R.bi_min_div_two_pos
  rw [isBigO_atTop_iff_eventually_exists_pos]
  obtain ⟨c₁, hc₁, h_sumTransform_aux⟩ := R.eventually_atTop_sumTransform_le
  filter_upwards [eventually_ge_atTop R.n₀,                                 -- n₀_ge_Rn₀
      (tendsto_nat_floor_mul_atTop b' hb_pos).eventually_gt_atTop 0,        -- h_b_floor
      eventually_forall_ge_atTop.mpr eventually_one_add_smoothingFn_pos,    -- h_smoothing_pos
      (tendsto_nat_floor_mul_atTop b' hb_pos).eventually_forall_ge_atTop
        eventually_one_add_smoothingFn_pos,                                 -- h_smoothing_pos'
      eventually_forall_ge_atTop.mpr R.eventually_asympBound_pos,            -- h_asympBound_pos
      eventually_forall_ge_atTop.mpr R.eventually_asympBound_r_pos,          -- h_asympBound_r_pos
      (tendsto_nat_floor_mul_atTop b' hb_pos).eventually_forall_ge_atTop
        R.eventually_asympBound_pos,                                         -- h_asympBound_floor
      eventually_gt_atTop 0,                                                -- n₀_pos
      eventually_forall_ge_atTop.mpr R.eventually_one_add_smoothingFn_r_pos,  -- h_smoothing_r_pos
      eventually_forall_ge_atTop.mpr R.rpow_p_mul_one_add_smoothingFn_ge,   -- bound2
      (tendsto_nat_floor_mul_atTop b' hb_pos).eventually_forall_ge_atTop
        eventually_one_add_smoothingFn_pos,                                 -- h_smoothingFn_floor
      eventually_forall_ge_atTop.mpr h_sumTransform_aux,                    -- h_sumTransform
      eventually_forall_ge_atTop.mpr R.eventually_bi_mul_le_r,              -- h_bi_le_r
      eventually_forall_ge_atTop.mpr (eventually_ge_atTop ⌈exp 1⌉₊)]        -- h_exp
    with n₀ n₀_ge_Rn₀ h_b_floor h_smoothing_pos h_smoothing_pos' h_asympBound_pos h_asympBound_r_pos
      h_asympBound_floor n₀_pos h_smoothing_r_pos bound2 h_smoothingFn_floor h_sumTransform
      h_bi_le_r h_exp
  have h_base_nonempty := R.base_nonempty n₀_pos
  -- Min of the ratio T(n) / asympBound(n) over the base case n ∈ [b * n₀, n₀)
  set base_min : ℝ :=
    (Finset.Ico (⌊b' * n₀⌋₊) n₀).inf' h_base_nonempty
      (fun n => T n / ((1 + ε n) * asympBound g a b n)) with base_min_def
  -- The big-O constant we are aiming for: min of the base case ratio and what we need to cancel
  -- out the g(n) term in the calculation below
  let C := min (2 * c₁)⁻¹ base_min
  have hC_pos : 0 < C := by
    refine lt_min (by positivity) ?_
    obtain ⟨m, hm_mem, hm⟩ :=
      Finset.exists_mem_eq_inf' h_base_nonempty (fun n => T n / ((1 + ε n) * asympBound g a b n))
    calc 0 < T m / ((1 + ε m) * asympBound g a b m) := by
              have H₁ : 0 < T m := by exact R.T_pos _
              have H₂ : 0 < 1 + ε m := by rw [Finset.mem_Ico] at hm_mem
                                          exact h_smoothing_pos' m hm_mem.1
              have H₃ : 0 < asympBound g a b m := by
                refine R.asympBound_pos m ?_
                calc 0 < ⌊b' * n₀⌋₊ := by exact h_b_floor
                     _ ≤ m := by rw [Finset.mem_Ico] at hm_mem; exact hm_mem.1
              positivity
         _ = base_min := by rw [base_min_def, hm]
  refine ⟨C, hC_pos, fun n hn => ?_⟩
  -- Base case: statement is true for `b' * n₀ ≤ n < n₀`
  have h_base : ∀ n ∈ Finset.Ico (⌊b' * n₀⌋₊) n₀, C * ((1 + ε n) * asympBound g a b n) ≤ T n := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have htmp1 : 0 < 1 + ε n := h_smoothingFn_floor n hn.1
    have htmp2 : 0 < asympBound g a b n := h_asympBound_floor n hn.1
    rw [← _root_.le_div_iff₀ (by positivity)]
    rw [← Finset.mem_Ico] at hn
    calc T n / ((1 + ε ↑n) * asympBound g a b n)
           ≥ (Finset.Ico (⌊b' * n₀⌋₊) n₀).inf' h_base_nonempty
                  fun z => T z / ((1 + ε z) * asympBound g a b z) :=
                    Finset.inf'_le_of_le _ (b := n) hn <| le_refl _
         _ ≥ C := min_le_right _ _
  have h_asympBound_pos' : 0 < asympBound g a b n := h_asympBound_pos n hn
  have h_one_sub_smoothingFn_pos' : 0 < 1 + ε n := h_smoothing_pos n hn
  rw [Real.norm_of_nonneg (R.T_nonneg n), Real.norm_of_nonneg (by positivity)]
  -- We now prove all other cases by induction
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    have b_mul_n₀_le_ri i : ⌊b' * ↑n₀⌋₊ ≤ r i n := by
      exact_mod_cast calc ⌊b' * ↑n₀⌋₊ ≤ b' * n₀ := Nat.floor_le <| by positivity
                                  _ ≤ b' * n := by gcongr
                                  _ ≤ r i n := h_bi_le_r n hn i
    have g_pos : 0 ≤ g n := R.g_nonneg n (by positivity)
    calc
      T n = (∑ i, a i * T (r i n)) + g n := by exact R.h_rec n <| n₀_ge_Rn₀.trans hn
        _ ≥ (∑ i, a i * (C * ((1 + ε (r i n)) * asympBound g a b (r i n)))) + g n := by
            -- Apply the induction hypothesis, or use the base case depending on how large `n` is
              gcongr (∑ i, a i * ?_) + g n with i _
              · exact le_of_lt <| R.a_pos _
              · cases lt_or_ge (r i n) n₀ with
                | inl ri_lt_n₀ => exact h_base _ <| Finset.mem_Ico.mpr ⟨b_mul_n₀_le_ri i, ri_lt_n₀⟩
                | inr n₀_le_ri =>
                  exact h_ind (r i n) (R.r_lt_n _ _ (n₀_ge_Rn₀.trans hn)) n₀_le_ri
                    (h_asympBound_r_pos _ hn _) (h_smoothing_r_pos n hn i)
        _ = (∑ i, a i * (C * ((1 + ε (r i n)) * ((r i n) ^ (p a b)
                  * (1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1))))))) + g n := by
              simp_rw [asympBound_def']
        _ = (∑ i, C * a i * ((r i n)^(p a b) * (1 + ε (r i n))
                  * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n := by
              congr; ext; ring
        _ ≥ (∑ i, C * a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
                  * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n := by
              gcongr (∑ i, C * a i * (?_ *
                  ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + g n with i
              · have := R.a_pos i
                positivity
              · refine add_nonneg zero_le_one <| Finset.sum_nonneg fun j _ => ?_
                rw [div_nonneg_iff]
                exact Or.inl ⟨R.g_nonneg j (by positivity), by positivity⟩
              · exact bound2 n hn i
        _ = (∑ i, C * a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
                  * ((1 + ((∑ u ∈ range n, g u / u ^ ((p a b) + 1))
                  - (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))) + g n := by
              congr; ext i; congr
              refine eq_sub_of_add_eq ?_
              rw [add_comm]
              exact add_eq_of_eq_sub <| Finset.sum_Ico_eq_sub _
                <| le_of_lt <| R.r_lt_n i n <| n₀_ge_Rn₀.trans hn
        _ = (∑ i, C * a i * ((b i) ^ (p a b) * (1 + ε n)
                  * ((n ^ (p a b) * (1 + (∑ u ∈ range n, g u / u ^ ((p a b) + 1)))
                  - n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))
                  + g n := by
              congr; ext; ring
        _ = (∑ i, C * a i * ((b i) ^ (p a b) * (1 + ε n)
                  * ((asympBound g a b n - sumTransform (p a b) g (r i n) n)))) + g n := by
              simp_rw [asympBound_def', sumTransform_def]
        _ ≥ (∑ i, C * a i * ((b i) ^ (p a b) * (1 + ε n)
                  * ((asympBound g a b n - c₁ * g n)))) + g n := by
              gcongr with i
              · have := R.a_pos i
                positivity
              · have := R.b_pos i
                positivity
              · exact h_sumTransform n hn i
        _ = (∑ i, C * (1 + ε n) * ((asympBound g a b n - c₁ * g n))
                  * (a i * (b i) ^ (p a b))) + g n := by congr; ext; ring
        _ = C * (1 + ε n) * (asympBound g a b n - c₁ * g n) + g n := by
              rw [← Finset.mul_sum, R.sumCoeffsExp_p_eq_one, mul_one]
        _ = C * (1 + ε n) * asympBound g a b n + (1 - C * c₁ * (1 + ε n)) * g n := by ring
        _ ≥ C * (1 + ε n) * asympBound g a b n + 0 := by
              gcongr
              refine mul_nonneg ?_ g_pos
              rw [sub_nonneg]
              calc C * c₁ * (1 + ε n) ≤ C * c₁ * 2 := by
                        gcongr
                        refine one_add_smoothingFn_le_two ?_
                        calc exp 1 ≤ ⌈exp 1⌉₊ := by exact Nat.le_ceil _
                                 _ ≤ n := by exact_mod_cast h_exp n hn
                    _ = C * (2 * c₁) := by ring
                    _ ≤ (2 * c₁)⁻¹ * (2 * c₁) := by gcongr; exact min_le_left _ _
                    _ = c₁⁻¹ * c₁ := by ring
                    _ = 1 := inv_mul_cancel₀ (by positivity)
        _ = C * ((1 + ε n) * asympBound g a b n) := by ring

/-- The **Akra-Bazzi theorem**: `T ∈ O(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
theorem isBigO_asympBound : T =O[atTop] asympBound g a b := by
  calc T =O[atTop] (fun n => (1 - ε n) * asympBound g a b n) := by
              exact R.T_isBigO_smoothingFn_mul_asympBound
         _ =O[atTop] (fun n => 1 * asympBound g a b n) := by
              refine IsBigO.mul (isBigO_const_of_tendsto (y := 1) ?_ one_ne_zero)
                (isBigO_refl _ _)
              rw [← Function.comp_def (fun n => 1 - ε n) Nat.cast]
              exact Tendsto.comp isEquivalent_one_sub_smoothingFn_one.tendsto_const
                tendsto_natCast_atTop_atTop
         _ = asympBound g a b := by simp

/-- The **Akra-Bazzi theorem**: `T ∈ Ω(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
theorem isBigO_symm_asympBound : asympBound g a b =O[atTop] T := by
  calc asympBound g a b = (fun n => 1 * asympBound g a b n) := by simp
                 _ ~[atTop] (fun n => (1 + ε n) * asympBound g a b n) := by
                            refine IsEquivalent.mul (IsEquivalent.symm ?_) IsEquivalent.refl
                            rw [Function.const_def, isEquivalent_const_iff_tendsto one_ne_zero,
                              ← Function.comp_def (fun n => 1 + ε n) Nat.cast]
                            exact Tendsto.comp isEquivalent_one_add_smoothingFn_one.tendsto_const
                              tendsto_natCast_atTop_atTop
                 _ =O[atTop] T := R.smoothingFn_mul_asympBound_isBigO_T

/-- The **Akra-Bazzi theorem**: `T ∈ Θ(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
theorem isTheta_asympBound : T =Θ[atTop] asympBound g a b :=
  ⟨R.isBigO_asympBound, R.isBigO_symm_asympBound⟩

end AkraBazziRecurrence
