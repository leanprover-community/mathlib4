/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Computability.AkraBazzi.SumTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Divide-and-conquer recurrences and the Akra-Bazzi theorem

A divide-and-conquer recurrence is a function `T : ℕ → ℝ` that satisfies a recurrence relation of
the form `T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)` for sufficiently large `n`, where `r_i(n)` is
a function such that `‖r_i(n) - b_i n‖ ∈ o(n / (log n)^2)` for every `i`, the coefficients `a_i`
are positive, and the coefficients `b_i` are real numbers in `(0, 1)`. (This assumption can be
relaxed to `O(n / (log n)^(1+ε))`, for some `ε > 0`; we leave this as future work.) These
recurrences arise mainly in the analysis of divide-and-conquer algorithms such as mergesort or
Strassen's algorithm for matrix multiplication. This class of algorithms works by dividing an
instance of the problem of size `n`, into `k` smaller instances, where the `i`-th instance is of
size roughly `b_i n`, and calling itself recursively on those smaller instances. `T(n)` then
represents the running time of the algorithm, and `g(n)` represents the running time required to
divide the instance and process the answers produced by the recursive calls. Since virtually all
such algorithms produce instances that are only approximately of size `b_i n` (they must round up
or down, at the very least), we allow the instance sizes to be given by a function `r_i(n)` that
approximates `b_i n`.

The Akra-Bazzi theorem gives the asymptotic order of such a recurrence: it states that
`T(n) ∈ Θ(n^p (1 + ∑_{u=0}^{n-1} g(n) / u^{p+1}))`,
where `p` is the unique real number such that `∑ a_i b_i^p = 1`.

## Main definitions and results

* `isTheta_asympBound`: The main result stating that
  `T(n) ∈ Θ(n^p (1 + ∑_{u=0}^{n-1} g(n) / u^{p+1}))`

## Implementation

Note that the original version of the Akra–Bazzi theorem uses an integral rather than the sum in
the above expression, and first considers the `T : ℝ → ℝ` case before moving on to `ℕ → ℝ`. We
prove the version with a sum here, as it is simpler and more relevant for algorithms.

## TODO

* Relax the assumption described in the introduction from `o(n / (log n)^2)` to
  `O(n / (log n)^(1+ε))`, for some `ε > 0`.
* Specialize this theorem to the very common case where the recurrence is of the form
  `T(n) = ℓT(r_i(n)) + g(n)`
  where `g(n) ∈ Θ(n^t)` for some `t`. (This is often called the "master theorem" in the literature.)
* Add the original version of the theorem with an integral instead of a sum.

## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

@[expose] public section

open Finset Real Filter Asymptotics
open scoped Topology

namespace AkraBazziRecurrence

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)


local notation "ε" => smoothingFn


/-!
### Technical lemmas

The next several lemmas are technical results leading up to `rpow_p_mul_one_sub_smoothingFn_le` and
`rpow_p_mul_one_add_smoothingFn_ge`, which are key steps in the main proof.
-/

lemma eventually_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    deriv (fun z => z ^ p * (1 - ε z))
      =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 - ε z) + z ^ (p - 1) / (log z ^ 2) :=
  calc deriv (fun z => z ^ p * (1 - ε z))
  _ =ᶠ[atTop] fun x => deriv (· ^ p) x * (1 - ε x) + x ^ p * deriv (1 - ε ·) x := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [deriv_fun_mul]
    · exact differentiableAt_rpow_const_of_ne _ (by positivity)
    · exact differentiableAt_one_sub_smoothingFn hx
  _ =ᶠ[atTop] fun x => p * x ^ (p - 1) * (1 - ε x) + x ^ p * (x⁻¹ / (log x ^ 2)) := by
    filter_upwards [eventually_gt_atTop 1, eventually_deriv_one_sub_smoothingFn]
      with x hx hderiv
    rw [hderiv, Real.deriv_rpow_const]
  _ =ᶠ[atTop] fun x => p * x ^ (p - 1) * (1 - ε x) + x ^ (p - 1) / (log x ^ 2) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [mul_div, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity), sub_eq_add_neg]

lemma eventually_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    deriv (fun z => z ^ p * (1 + ε z))
      =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 + ε z) - z ^ (p - 1) / (log z ^ 2) :=
  calc deriv (fun x => x ^ p * (1 + ε x))
    _ =ᶠ[atTop] fun x => deriv (· ^ p) x * (1 + ε x) + x ^ p * deriv (1 + ε ·) x := by
      filter_upwards [eventually_gt_atTop 1] with x hx
      rw [deriv_fun_mul]
      · exact differentiableAt_rpow_const_of_ne _ (by positivity)
      · exact differentiableAt_one_add_smoothingFn hx
    _ =ᶠ[atTop] fun x => p * x ^ (p - 1) * (1 + ε x) - x ^ p * (x⁻¹ / (log x ^ 2)) := by
      filter_upwards [eventually_gt_atTop 1, eventually_deriv_one_add_smoothingFn]
        with x hx hderiv
      simp [hderiv, Real.deriv_rpow_const, neg_div, sub_eq_add_neg]
    _ =ᶠ[atTop] fun x => p * x ^ (p - 1) * (1 + ε x) - x ^ (p - 1) / (log x ^ 2) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp [mul_div, ← Real.rpow_neg_one, ← Real.rpow_add (by positivity), sub_eq_add_neg]

lemma isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    deriv (fun z => z ^ p * (1 - ε z)) ~[atTop] fun z => p * z ^ (p - 1) :=
  calc deriv (fun z => z ^ p * (1 - ε z))
    _ =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 - ε z) + z ^ (p - 1) / (log z ^ 2) :=
      eventually_deriv_rpow_p_mul_one_sub_smoothingFn p
    _ ~[atTop] fun z => p * z ^ (p - 1) := by
      refine IsEquivalent.add_isLittleO ?one ?two
      case one => calc
        (fun z => p * z ^ (p - 1) * (1 - ε z)) ~[atTop] fun z => p * z ^ (p - 1) * 1 :=
              IsEquivalent.mul IsEquivalent.refl isEquivalent_one_sub_smoothingFn_one
        _ = fun z => p * z ^ (p - 1) := by ext; ring
      case two => calc
        (fun z => z ^ (p - 1) / (log z ^ 2)) =o[atTop] fun z => z ^ (p - 1) / 1 := by
          simp_rw [div_eq_mul_inv]
          refine IsBigO.mul_isLittleO (isBigO_refl _ _)
            (IsLittleO.inv_rev ?_ (by simp))
          rw [isLittleO_const_left]
          refine Or.inr <| Tendsto.comp tendsto_norm_atTop_atTop ?_
          exact Tendsto.comp (g := fun z => z ^ 2)
            (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
        _ = fun z => z ^ (p - 1) := by ext; simp
        _ =Θ[atTop] fun z => p * z ^ (p - 1) := IsTheta.const_mul_right hp <| isTheta_refl _ _

lemma isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    deriv (fun z => z ^ p * (1 + ε z)) ~[atTop] fun z => p * z ^ (p - 1) :=
  calc deriv (fun z => z ^ p * (1 + ε z))
    _ =ᶠ[atTop] fun z => p * z ^ (p - 1) * (1 + ε z) - z ^ (p - 1) / (log z ^ 2) :=
      eventually_deriv_rpow_p_mul_one_add_smoothingFn p
    _ ~[atTop] fun z => p * z ^ (p - 1) := by
      refine IsEquivalent.add_isLittleO ?one ?two
      case one => calc
        (fun z => p * z ^ (p - 1) * (1 + ε z)) ~[atTop] fun z => p * z ^ (p - 1) * 1 :=
              IsEquivalent.mul IsEquivalent.refl isEquivalent_one_add_smoothingFn_one
        _ = fun z => p * z ^ (p - 1) := by ext; ring
      case two => calc
        (fun z => -(z ^ (p - 1) / (log z ^ 2))) =o[atTop] fun z => z ^ (p - 1) / 1 := by
            simp_rw [isLittleO_neg_left, div_eq_mul_inv]
            refine IsBigO.mul_isLittleO (isBigO_refl _ _)
              (IsLittleO.inv_rev ?_ (by simp))
            rw [isLittleO_const_left]
            refine Or.inr <| Tendsto.comp tendsto_norm_atTop_atTop ?_
            exact Tendsto.comp (g := fun z => z ^ 2)
              (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
        _ = fun z => z ^ (p - 1) := by ext; simp
        _ =Θ[atTop] fun z => p * z ^ (p - 1) := IsTheta.const_mul_right hp <| isTheta_refl _ _

lemma isTheta_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖) =Θ[atTop] fun z => z ^ (p - 1) := by
  refine IsTheta.norm_left ?_
  calc (fun x => deriv (fun z => z ^ p * (1 - ε z)) x) =Θ[atTop] fun z => p * z ^ (p - 1) :=
        (isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn hp).isTheta
    _ =Θ[atTop] fun z => z ^ (p - 1) := IsTheta.const_mul_left hp <| isTheta_refl _ _

lemma isTheta_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x => ‖deriv (fun z => z ^ p * (1 + ε z)) x‖) =Θ[atTop] fun z => z ^ (p - 1) := by
  refine IsTheta.norm_left ?_
  calc (fun x => deriv (fun z => z ^ p * (1 + ε z)) x) =Θ[atTop] fun z => p * z ^ (p - 1) :=
      (isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn hp).isTheta
    _ =Θ[atTop] fun z => z ^ (p - 1) := IsTheta.const_mul_left hp <| isTheta_refl _ _

lemma growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    GrowsPolynomially fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖ := by
  cases eq_or_ne p 0 with
  | inl hp => -- p = 0
    have h₁ : (fun x => ‖deriv (fun z => z ^ p * (1 - ε z)) x‖)
        =ᶠ[atTop] fun z => z⁻¹ / (log z ^ 2) := by
      filter_upwards [eventually_deriv_one_sub_smoothingFn, eventually_gt_atTop 1] with x hx hx_pos
      have : 0 ≤ x⁻¹ / (log x ^ 2) := by positivity
      simp only [hp, Real.rpow_zero, one_mul, hx, Real.norm_of_nonneg this]
    refine GrowsPolynomially.congr_of_eventuallyEq h₁ ?_
    refine GrowsPolynomially.div (GrowsPolynomially.inv growsPolynomially_id)
      (GrowsPolynomially.pow 2 growsPolynomially_log ?_)
    filter_upwards [eventually_ge_atTop 1] with _ hx using log_nonneg hx
  | inr hp => -- p ≠ 0
    refine GrowsPolynomially.of_isTheta (growsPolynomially_rpow (p - 1))
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
      have : 0 ≤ x⁻¹ / (log x ^ 2) := by positivity
      simp only [neg_div, norm_neg, hp, Real.rpow_zero,
        one_mul, hx, Real.norm_of_nonneg this]
    refine GrowsPolynomially.congr_of_eventuallyEq h₁ ?_
    refine GrowsPolynomially.div (GrowsPolynomially.inv growsPolynomially_id)
      (GrowsPolynomially.pow 2 growsPolynomially_log ?_)
    filter_upwards [eventually_ge_atTop 1] with x hx using log_nonneg hx
  | inr hp => -- p ≠ 0
    refine GrowsPolynomially.of_isTheta (growsPolynomially_rpow (p - 1))
      (isTheta_deriv_rpow_p_mul_one_add_smoothingFn hp) ?_
    filter_upwards [eventually_gt_atTop 0] with _ _
    positivity

include R

lemma isBigO_apply_r_sub_b (q : ℝ → ℝ) (hq_diff : DifferentiableOn ℝ q (Set.Ioi 1))
    (hq_poly : GrowsPolynomially fun x => ‖deriv q x‖) (i : α) :
    (fun n => q (r i n) - q (b i * n)) =O[atTop] fun n => (deriv q n) * (r i n - b i * n) := by
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := by have := R.b_pos (min_bi b); positivity
  have hb_lt_one : b' < 1 := calc b (min_bi b) / 2
    _ < b (min_bi b) := div_two_lt_of_pos (R.b_pos (min_bi b))
    _ < 1 := R.b_lt_one (min_bi b)
  have hb : b' ∈ Set.Ioo 0 1 := ⟨hb_pos, hb_lt_one⟩
  have hb' (i) : b' ≤ b i := calc b (min_bi b) / 2
    _ ≤ b i / 2 := by gcongr; aesop
    _ ≤ b i := le_of_lt <| div_two_lt_of_pos (R.b_pos i)
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
    (s := Set.Icc (b' * n) n) (fun z hz => ?diff) (fun z hz => (hn z hz).2)
    (convex_Icc _ _) ?mem_Icc <| ⟨h_bi_le_r i, by exact_mod_cast (le_of_lt (R.r_lt_n i n h_ge_n₀))⟩
  case diff =>
    refine hq_diff.differentiableAt (Ioi_mem_nhds ?_)
    calc 1 < b' * n := h_bn
         _ ≤ z := hz.1
  case mem_Icc =>
    refine ⟨by gcongr; exact hb' i, ?_⟩
    calc b i * n ≤ 1 * n := by gcongr; exact le_of_lt <| R.b_lt_one i
                 _ = n := by simp

set_option backward.isDefEq.respectTransparency false in
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
  have h_deriv_q : deriv q =O[atTop] fun x => x ^ ((p a b) - 1) := calc deriv q
    _ = deriv fun x => (fun z => z ^ (p a b)) x * (fun z => 1 - ε z) x := by rfl
    _ =ᶠ[atTop] fun x => deriv (fun z => z ^ (p a b)) x * (1 - ε x) +
          x ^ (p a b) * deriv (fun z => 1 - ε z) x := by
      filter_upwards [eventually_ne_atTop 0, eventually_gt_atTop 1] with x hx hx'
      rw [deriv_fun_mul] <;> aesop
    _ =O[atTop] fun x => x ^ ((p a b) - 1) := by
      refine IsBigO.add ?left ?right
      case left => calc (fun x => deriv (fun z => z ^ (p a b)) x * (1 - ε x))
        _ =O[atTop] fun x => x ^ ((p a b) - 1) * (1 - ε x) :=
          IsBigO.mul (isBigO_deriv_rpow_const_atTop (p a b)) (isBigO_refl _ _)
        _ =O[atTop] fun x => x ^ ((p a b) - 1) * 1 :=
          IsBigO.mul (isBigO_refl _ _) isEquivalent_one_sub_smoothingFn_one.isBigO
        _ = fun x => x ^ ((p a b) - 1) := by ext; rw [mul_one]
      case right => calc (fun x => x ^ (p a b) * deriv (fun z => 1 - ε z) x)
        _ =O[atTop] (fun x => x ^ (p a b) * x⁻¹) :=
          IsBigO.mul (isBigO_refl _ _) isLittleO_deriv_one_sub_smoothingFn.isBigO
        _ =ᶠ[atTop] fun x => x ^ ((p a b) - 1) := by
          filter_upwards [eventually_gt_atTop 0] with x hx
          rw [← Real.rpow_neg_one, ← Real.rpow_add hx, ← sub_eq_add_neg]
  have h_main_norm : (fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖)
      ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ := by
    refine IsLittleO.eventuallyLE ?_
    calc (fun (n : ℕ) => q (r i n) - q (b i * n))
      _ =O[atTop] fun n => (deriv q n) * (r i n - b i * n) :=
        R.isBigO_apply_r_sub_b q h_diff_q
          (growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p a b)) i
      _ =o[atTop] fun n => (deriv q n) * (n / log n ^ 2) :=
        IsBigO.mul_isLittleO (isBigO_refl _ _) (R.dist_r_b i)
      _ =O[atTop] fun n => n ^ ((p a b) - 1) * (n / log n ^ 2) :=
        IsBigO.mul (IsBigO.natCast_atTop h_deriv_q) (isBigO_refl _ _)
      _ =ᶠ[atTop] fun n => n ^ (p a b) / (log n) ^ 2 := by
        filter_upwards [eventually_ne_atTop 0] with n hn
        have hn' : (n : ℝ) ≠ 0 := by positivity
        simp [← mul_div_assoc, ← Real.rpow_add_one hn']
      _ = fun (n : ℕ) => (n : ℝ) ^ (p a b) * (1 / (log n) ^ 2) := by
        simp_rw [mul_div, mul_one]
      _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (1 / (log n) ^ 2) := by
        refine IsTheta.symm ?_
        simp_rw [mul_assoc]
        refine IsTheta.const_mul_left ?_ (isTheta_refl _ _)
        have := R.b_pos i; positivity
      _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) :=
        IsTheta.symm <| IsTheta.mul (isTheta_refl _ _) <| R.isTheta_smoothingFn_sub_self i
  have h_main : (fun (n : ℕ) => q (r i n) - q (b i * n))
      ≤ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
    calc (fun (n : ℕ) => q (r i n) - q (b i * n))
      _ ≤ᶠ[atTop] fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖ := by
        filter_upwards with _ using le_norm_self _
      _ ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ :=
        h_main_norm
      _ =ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
        filter_upwards [eventually_gt_atTop ⌈(b i)⁻¹⌉₊, eventually_gt_atTop 1] with n hn hn'
        refine norm_of_nonneg ?_
        have h₁ := R.b_pos i
        have h₂ : 0 ≤ ε (b i * n) - ε n := by
          refine sub_nonneg_of_le <|
            (strictAntiOn_smoothingFn.le_iff_ge ?n_gt_one ?bn_gt_one).mpr ?le
          case n_gt_one => rwa [Set.mem_Ioi, Nat.one_lt_cast]
          case bn_gt_one =>
            calc 1 = b i * (b i)⁻¹ := by rw [mul_inv_cancel₀ (by positivity)]
              _ ≤ b i * ⌈(b i)⁻¹⌉₊ := by gcongr; exact Nat.le_ceil _
              _ < b i * n := by gcongr
          case le => calc b i * n
            _ ≤ 1 * n := by have := R.b_lt_one i; gcongr
            _ = n := by rw [one_mul]
        positivity
  filter_upwards [h_main] with n hn
  have h₁ : q (b i * n) + (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)
      = (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n) := by
    have := R.b_pos i
    simp only [q, mul_rpow (by positivity : (0 : ℝ) ≤ b i) (by positivity : (0 : ℝ) ≤ n)]
    ring
  change q (r i n) ≤ (b i) ^ (p a b) * n ^ (p a b) * (1 - ε n)
  rw [← h₁, ← sub_le_iff_le_add']
  exact hn

set_option backward.isDefEq.respectTransparency false in
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
  have h_deriv_q : deriv q =O[atTop] fun x => x ^ ((p a b) - 1) :=
    calc deriv q
      _ = deriv fun x => (fun z => z ^ (p a b)) x * (fun z => 1 + ε z) x := by rfl
      _ =ᶠ[atTop] fun x => deriv (fun z => z ^ (p a b)) x * (1 + ε x)
          + x ^ (p a b) * deriv (fun z => 1 + ε z) x := by
        filter_upwards [eventually_ne_atTop 0, eventually_gt_atTop 1] with x hx hx'
        rw [deriv_fun_mul] <;> aesop
      _ =O[atTop] fun x => x ^ ((p a b) - 1) := by
        refine IsBigO.add ?left ?right
        case left =>
          calc (fun x => deriv (fun z => z ^ (p a b)) x * (1 + ε x))
            _ =O[atTop] fun x => x ^ ((p a b) - 1) * (1 + ε x) :=
              IsBigO.mul (isBigO_deriv_rpow_const_atTop (p a b)) (isBigO_refl _ _)
            _ =O[atTop] fun x => x ^ ((p a b) - 1) * 1 :=
              IsBigO.mul (isBigO_refl _ _) isEquivalent_one_add_smoothingFn_one.isBigO
            _ = fun x => x ^ ((p a b) - 1) := by ext; rw [mul_one]
        case right =>
          calc (fun x => x ^ (p a b) * deriv (fun z => 1 + ε z) x)
            _ =O[atTop] (fun x => x ^ (p a b) * x⁻¹) :=
              IsBigO.mul (isBigO_refl _ _) isLittleO_deriv_one_add_smoothingFn.isBigO
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
        _ =o[atTop] fun n => (deriv q n) * (n / log n ^ 2) :=
          IsBigO.mul_isLittleO (isBigO_refl _ _) (R.dist_r_b i)
        _ =O[atTop] fun n => n ^ ((p a b) - 1) * (n / log n ^ 2) :=
          IsBigO.mul (IsBigO.natCast_atTop h_deriv_q) (isBigO_refl _ _)
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
        _ =Θ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) :=
          IsTheta.symm <| IsTheta.mul (isTheta_refl _ _) <| R.isTheta_smoothingFn_sub_self i
  have h_main : (fun (n : ℕ) => q (b i * n) - q (r i n))
      ≤ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
    calc (fun (n : ℕ) => q (b i * n) - q (r i n))
      _ ≤ᶠ[atTop] fun (n : ℕ) => ‖q (r i n) - q (b i * n)‖ := by
        filter_upwards with _; rw [norm_sub_rev]; exact le_norm_self _
      _ ≤ᶠ[atTop] fun (n : ℕ) => ‖(b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)‖ :=
        h_main_norm
      _ =ᶠ[atTop] fun (n : ℕ) => (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n) := by
        filter_upwards [eventually_gt_atTop ⌈(b i)⁻¹⌉₊, eventually_gt_atTop 1] with n hn hn'
        refine norm_of_nonneg ?_
        have h₁ := R.b_pos i
        have h₂ : 0 ≤ ε (b i * n) - ε n := by
          refine sub_nonneg_of_le <|
            (strictAntiOn_smoothingFn.le_iff_ge ?n_gt_one ?bn_gt_one).mpr ?le
          case n_gt_one =>
            change 1 < (n : ℝ)
            rw [Nat.one_lt_cast]
            exact hn'
          case bn_gt_one =>
            calc 1 = b i * (b i)⁻¹ := by rw [mul_inv_cancel₀ (by positivity)]
                _ ≤ b i * ⌈(b i)⁻¹⌉₊ := by gcongr; exact Nat.le_ceil _
                _ < b i * n := by gcongr
          case le => calc b i * n
            _ ≤ 1 * n := by have := R.b_lt_one i; gcongr
            _ = n := by rw [one_mul]
        positivity
  filter_upwards [h_main] with n hn
  have h₁ : q (b i * n) - (b i) ^ (p a b) * n ^ (p a b) * (ε (b i * n) - ε n)
      = (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n) := by
    have := R.b_pos i
    simp only [q, mul_rpow (by positivity : (0 : ℝ) ≤ b i) (by positivity : (0 : ℝ) ≤ n)]
    ring
  change (b i) ^ (p a b) * n ^ (p a b) * (1 + ε n) ≤ q (r i n)
  rw [← h₁, sub_le_iff_le_add', ← sub_le_iff_le_add]
  exact hn

/-!
### Main proof

This final section proves the Akra-Bazzi theorem.
-/

/-- The main proof of the upper-bound part of the Akra-Bazzi theorem. The factor `1 - ε n` does not
change the asymptotic order, but it is needed for the induction step to go through. -/
lemma T_isBigO_smoothingFn_mul_asympBound :
    T =O[atTop] (fun n => (1 - ε n) * asympBound g a b n) := by
  refine isBigO_nat_atTop_induction_of_eventually_pos ?_ ?_ ?_
  · exact Eventually.of_forall fun h => R.T_nonneg _
  · filter_upwards [R.eventually_asympBound_pos, eventually_one_sub_smoothingFn_pos] with n hn hn₂
    positivity
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := R.bi_min_div_two_pos
  obtain ⟨c₁, hc₁, h_sumTransform_aux⟩ := R.eventually_atTop_sumTransform_ge
  filter_upwards [eventually_ge_atTop R.n₀] with n₀ n₀_ge_Rn₀
  refine ⟨2 * c₁⁻¹, ?_⟩
  filter_upwards [
    eventually_ge_atTop n₀,
    -- bound1
    R.rpow_p_mul_one_sub_smoothingFn_le,
    -- h_smoothing_pos
    eventually_one_sub_smoothingFn_pos,
    -- h_sumTransform
    h_sumTransform_aux,
    -- h_smoothing_gt_half
    eventually_one_sub_smoothingFn_gt_const (1 / 2) (by norm_num),
    -- h_bi_le_r
    R.eventually_bi_mul_le_r,
    -- n₀_div_le_n
    eventually_ge_atTop ⌈n₀ / b'⌉₊]
      with n hn bound1 h_smoothing_pos h_sumTransform h_smoothing_gt_half h_bi_le_r n₀_div_le_n
  --have n₀_le_bn : n₀ ≤ b' * n := by
  --  sorry
  have n₀_le_r : ∀ i, n₀ ≤ r i n := by
    intro i
    exact_mod_cast
      calc n₀ ≤ b' * n := by
                have : (n₀ : ℝ) / b' ≤ n := by
                  exact_mod_cast calc
                    (n₀ : ℝ) / b' ≤ ⌈n₀ / b'⌉₊ := Nat.le_ceil (↑n₀ / b')
                    _ ≤ n := by exact_mod_cast n₀_div_le_n
                rwa [div_le_iff₀, mul_comm] at this
                grind only
        _ ≤ r i n := by grind
  have r_le_n : ∀ i, r i n < n := by grind [AkraBazziRecurrence]
  intro C hC h_ind
  have C_pos : 0 ≤ C := by grind [inv_pos]
  have g_pos : 0 ≤ g n := R.g_nonneg n (by positivity)
  calc T n
    _ = (∑ i, a i * T (r i n)) + g n := R.h_rec n (by grind)
    _ ≤ (∑ i, a i * (C * ((1 - ε (r i n)) * asympBound g a b (r i n)))) + g n := by
      -- Apply the induction hypothesis
      gcongr (∑ i, a i * ?_) + g n with i _
      · exact le_of_lt <| R.a_pos _
      · exact h_ind (r i n) (by grind)
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
      · positivity [R.a_pos i]
      · refine add_nonneg zero_le_one <| Finset.sum_nonneg fun j _ => ?_
        rw [div_nonneg_iff]
        exact Or.inl ⟨R.g_nonneg j (by positivity), by positivity⟩
      · grind
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
      · positivity [R.a_pos i]
      · positivity [R.b_pos i]
      · exact h_sumTransform i
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
      calc 1
        _ ≤ 2 * (c₁⁻¹ * c₁) * (1 / 2) := by
          rw [inv_mul_cancel₀ (by positivity : c₁ ≠ 0)]; norm_num
        _ = (2 * c₁⁻¹) * c₁ * (1 / 2) := by ring
        _ ≤ C * c₁ * (1 - ε n) := by gcongr
    _ = C * ((1 - ε n) * asympBound g a b n) := by ring

/-- The main proof of the lower-bound part of the Akra-Bazzi theorem. The factor `1 + ε n` does not
change the asymptotic order, but it is needed for the induction step to go through. -/
lemma smoothingFn_mul_asympBound_isBigO_T :
    (fun (n : ℕ) => (1 + ε n) * asympBound g a b n) =O[atTop] T := by
  refine isBigO_nat_atTop_induction_of_eventually_pos ?_ ?_ ?_
  · filter_upwards [R.eventually_asympBound_pos, eventually_one_add_smoothingFn_pos] with n hn hn₂
    positivity
  · exact Eventually.of_forall fun h => R.T_pos _
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := R.bi_min_div_two_pos
  obtain ⟨c₁, hc₁, h_sumTransform_aux⟩ := R.eventually_atTop_sumTransform_le
  filter_upwards [eventually_ge_atTop R.n₀] with n₀ n₀_ge_Rn₀
  refine ⟨2 * c₁, ?_⟩
  filter_upwards [
    eventually_ge_atTop n₀,
    -- bound2
    R.rpow_p_mul_one_add_smoothingFn_ge,
    -- h_smoothing_pos
    eventually_one_add_smoothingFn_pos,
    -- h_sumTransform
    h_sumTransform_aux,
    -- h_smoothing_gt_half
    eventually_one_sub_smoothingFn_gt_const (1 / 2) (by norm_num),
    -- h_bi_le_r
    R.eventually_bi_mul_le_r,
    -- n₀_div_le_n
    eventually_ge_atTop ⌈n₀ / b'⌉₊,
    -- h_exp
    eventually_ge_atTop ⌈exp 1⌉₊]
      with n hn bound2 h_smoothing_pos h_sumTransform h_smoothing_gt_half h_bi_le_r n₀_div_le_n
        h_exp
  have n₀_le_r : ∀ i, n₀ ≤ r i n := by
    intro i
    exact_mod_cast
      calc n₀ ≤ b' * n := by
                have : (n₀ : ℝ) / b' ≤ n := by
                  exact_mod_cast calc
                    (n₀ : ℝ) / b' ≤ ⌈n₀ / b'⌉₊ := Nat.le_ceil (↑n₀ / b')
                    _ ≤ n := by exact_mod_cast n₀_div_le_n
                rwa [div_le_iff₀, mul_comm] at this
                grind only
        _ ≤ r i n := by grind
  have r_le_n : ∀ i, r i n < n := by grind [AkraBazziRecurrence]
  intro C hC h_ind
  have C_pos : 0 ≤ C := by grind [inv_pos]
  have g_pos : 0 ≤ g n := R.g_nonneg n (by positivity)
  calc C * T n
    _ = C * ((∑ i, a i * T (r i n)) + g n) := by grind [AkraBazziRecurrence]
    _ = (∑ i, a i * (C * T (r i n))) + C * g n := by rw [mul_add, mul_sum]; grind
    _ ≥ (∑ i, a i * ((1 + ε (r i n)) * asympBound g a b (r i n))) + C * g n := by
      gcongr (∑ i, a i * ?_) + C * g n with i _
      · exact le_of_lt <| R.a_pos _
      · exact h_ind (r i n) (by grind)
    _ = (∑ i, a i * ((1 + ε (r i n)) * ((r i n) ^ (p a b)
          * (1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + C * g n := by
      simp_rw [asympBound_def']
    _ = (∑ i, a i * ((r i n) ^ (p a b) * (1 + ε (r i n))
              * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + C * g n := by
      congr; ext; ring
    _ ≥ (∑ i, a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
              * ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + C * g n := by
      gcongr (∑ i, a i * (?_ *
          ((1 + (∑ u ∈ range (r i n), g u / u ^ ((p a b) + 1)))))) + C * g n with i
      · positivity [R.a_pos i]
      · refine add_nonneg zero_le_one <| Finset.sum_nonneg fun j _ => ?_
        rw [div_nonneg_iff]
        exact Or.inl ⟨R.g_nonneg j (by positivity), by positivity⟩
      · exact bound2 i
    _ = (∑ i, a i * ((b i) ^ (p a b) * n ^ (p a b) * (1 + ε n)
              * ((1 + ((∑ u ∈ range n, g u / u ^ ((p a b) + 1))
              - (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))) + C * g n := by
      congr; ext i; congr
      refine eq_sub_of_add_eq ?_
      rw [add_comm]
      exact add_eq_of_eq_sub <| Finset.sum_Ico_eq_sub _
        <| le_of_lt <| R.r_lt_n i n <| n₀_ge_Rn₀.trans hn
    _ = (∑ i, a i * ((b i) ^ (p a b) * (1 + ε n)
              * ((n ^ (p a b) * (1 + (∑ u ∈ range n, g u / u ^ ((p a b) + 1)))
              - n ^ (p a b) * (∑ u ∈ Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1))))))
              + C * g n := by
      congr; ext; ring
    _ = (∑ i, a i * ((b i) ^ (p a b) * (1 + ε n)
              * ((asympBound g a b n - sumTransform (p a b) g (r i n) n)))) + C * g n := by
      simp_rw [asympBound_def', sumTransform_def]
    _ ≥ (∑ i, a i * ((b i) ^ (p a b) * (1 + ε n)
              * ((asympBound g a b n - c₁ * g n)))) + C * g n := by
      gcongr with i
      · positivity [R.a_pos i]
      · positivity [R.b_pos i]
      · exact h_sumTransform i
    _ = (∑ i, (1 + ε n) * ((asympBound g a b n - c₁ * g n))
              * (a i * (b i) ^ (p a b))) + C * g n := by grind only
    _ = (1 + ε n) * (asympBound g a b n - c₁ * g n) + C * g n := by
          rw [← Finset.mul_sum, R.sumCoeffsExp_p_eq_one, mul_one]
    _ = (1 + ε n) * asympBound g a b n + (C - c₁ * (1 + ε n)) * g n := by ring
    _ ≥ (1 + ε n) * asympBound g a b n + 0 := by
      gcongr
      refine mul_nonneg ?_ g_pos
      rw [sub_nonneg]
      calc c₁ * (1 + ε n)
        _ ≤ c₁ * 2 := by
          gcongr
          refine one_add_smoothingFn_le_two ?_
          calc exp 1 ≤ ⌈exp 1⌉₊ := by exact Nat.le_ceil _
                    _ ≤ n := by exact_mod_cast h_exp
        _ = (2 * c₁) := by ring
        _ ≤ C := hC
    _ = ((1 + ε n) * asympBound g a b n) := by ring

/-- The **Akra-Bazzi theorem**: `T ∈ O(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
theorem isBigO_asympBound : T =O[atTop] asympBound g a b := by
  calc T
    _ =O[atTop] (fun n => (1 - ε n) * asympBound g a b n) := by
      exact R.T_isBigO_smoothingFn_mul_asympBound
    _ =O[atTop] (fun n => 1 * asympBound g a b n) := by
      refine IsBigO.mul (isBigO_const_of_tendsto (y := 1) ?_ one_ne_zero) (isBigO_refl _ _)
      rw [← Function.comp_def (fun n => 1 - ε n) Nat.cast]
      exact Tendsto.comp isEquivalent_one_sub_smoothingFn_one.tendsto_const
        tendsto_natCast_atTop_atTop
    _ = asympBound g a b := by simp

/-- The **Akra-Bazzi theorem**: `T ∈ Ω(n^p (1 + ∑_u^n g(u) / u^{p+1}))` -/
theorem isBigO_symm_asympBound : asympBound g a b =O[atTop] T := by
  calc asympBound g a b
    _ = (fun n => 1 * asympBound g a b n) := by simp
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
