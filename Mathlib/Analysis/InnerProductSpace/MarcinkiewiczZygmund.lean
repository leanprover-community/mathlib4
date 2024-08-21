/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Positivity.Finset

/-!
# The Marcinkiewicz-Zygmund inequality

This file proves the Marcinkiewicz-Zygmund inequality. This is the statement that, for a random
variable `f` valued in a real inner product space, the $$L^p$$-norm of the sum of `n` samples of `f`
is bounded by the $$L^p$$-norm of `f` up to some multiplicative constant.

## TODO

* We currently only prove the inequality for `p = 2 * m` an even natural number. The general `p`
  case can be obtained from this specific one by nesting of Lp norms.
* We currently only prove the case of a uniformly distributed discrete random variable. This needs
  to be generalised! (and when it is, this file should move out of the `Algebra.Discrete`) folder.
-/

open Finset Fintype Nat Real
variable {α : Type*} {n : Type*} [Fintype n] {A : Finset α} {m : ℕ}

private lemma step_seven {f : α → ℝ} {a b : n → α} :
    m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2 : ℝ) ^ m ≤
      m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m := by
  rw [← mul_pow, ← mul_pow, ← mul_pow, mul_assoc, mul_sum _ _ (2 : ℝ)]
  gcongr
  exact add_sq_le.trans_eq (by simp)

private lemma step_eight {f : α → ℝ} {a b : n → α} :
    m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2) : ℝ) ^ m ≤
      m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) := by
  rw [pow_add, ← mul_assoc _ _ (2 ^ _), mul_assoc _ (2 ^ (m - 1)), sum_add_distrib]
  gcongr
  exact add_pow_le (by positivity) (by positivity) m

variable [DecidableEq n]

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : n ↦ s

private lemma step_one (hA : A.Nonempty) (f : α → ℝ) (a : n → α)
    (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤
      (∑ b in A ^^ n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / A.card ^ card n := by
  let B := A ^^ n
  calc
    |∑ i, f (a i)| ^ (m + 1)
      = |∑ i, (f (a i) - (∑ b in B, f (b i)) / B.card)| ^ (m + 1) := by
      simp only [hf, sub_zero, zero_div]
    _ = |(∑ b in B, ∑ i, (f (a i) - f (b i))) / B.card| ^ (m + 1) := by
      simp [sum_comm (s := B), ← sum_div, ← mul_sum, sub_div, B, hA.ne_empty]
    _ = |∑ b in B, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / B.card ^ (m + 1) := by
      rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b in B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / B.card ^ (m + 1) := by
      gcongr; exact abs_sum_le_sum_abs _ _
    _ = (∑ b in B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / B.card ^ m / B.card := by
      rw [div_div, ← pow_succ]
    _ ≤ (∑ b in B, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / B.card := by
      gcongr; exact pow_sum_div_card_le_sum_pow _ _ fun _ _ ↦ abs_nonneg _
    _ = _ := by simp [B]

private lemma step_one' (hA : A.Nonempty) (f : α → ℝ) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) (m : ℕ)
    (a : n → α) :
    |∑ i, f (a i)| ^ m ≤ (∑ b in A ^^ n, |∑ i, (f (a i) - f (b i))| ^ m) / A.card ^ card n := by
  cases m
  · simp [hA.ne_empty]
  exact step_one hA f a hf

private lemma step_two_aux (A : Finset α) (f : α → ℝ) (ε : n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ)^^n) (g : (n → ℝ) → ℝ) :
    ∑ a in A ^^ n, ∑ b in A ^^ n, g (ε * (f ∘ a - f ∘ b)) =
      ∑ a in A ^^ n, ∑ b in A ^^ n, g (f ∘ a - f ∘ b) := by
  rw [← sum_product', ← sum_product']
  let swapper (xy : (n → α) × (n → α)) : (n → α) × (n → α) :=
    (fun i ↦ if ε i = 1 then xy.1 i else xy.2 i, fun i ↦ if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper a ∈ (A ^^ n) ×ˢ (A ^^ n) := by
    simp only [mem_product, and_imp, mem_piFinset, ← forall_and]
    intro a h i
    split_ifs
    · exact h i
    · exact (h i).symm
  have h₂ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper (swapper a) = a := fun a _ ↦ by
    ext <;> simp only <;> split_ifs <;> rfl
  refine sum_nbij' swapper swapper h₁ h₁ h₂ h₂ ?_
  · rintro ⟨a, b⟩ _
    congr with i : 1
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
    simp only [mem_piFinset, mem_insert, mem_singleton] at hε
    split_ifs with h
    · simp [h]
    rw [(hε i).resolve_right h]
    ring

private lemma step_two (f : α → ℝ) :
    ∑ a in A ^^ n, ∑ b in A ^^ n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      2⁻¹ ^ card n * ∑ ε in ({-1, 1} : Finset ℝ)^^n,
        ∑ a in A ^^ n, ∑ b in A ^^ n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) := by
  let B := A ^^ n
  have : ∀ ε ∈ ({-1, 1} : Finset ℝ)^^n,
    ∑ a in B, ∑ b in B, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a in B, ∑ b in B, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    fun ε hε ↦ step_two_aux A f _ hε fun z : n → ℝ ↦ univ.sum z ^ (2 * m)
  rw [Finset.sum_congr rfl this, sum_const, card_piFinset, card_pair, prod_const, card_univ,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_two, inv_pow, inv_mul_cancel_left₀]
  · positivity
  · norm_num

private lemma step_three (f : α → ℝ) :
    ∑ ε in ({-1, 1} : Finset ℝ)^^n,
      ∑ a in A ^^ n, ∑ b in A ^^ n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a in A ^^ n, ∑ b in A ^^ n, ∑ k in piAntidiag univ (2 * m),
          (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
            ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t := by
  simp only [@sum_comm _ _ (n → ℝ) _ _ (A ^^ n), ← Complex.abs_pow, sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun a _ ↦ ?_
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (n → ℝ), ← mul_sum, ← sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc, mul_right_comm]

private lemma step_four {k : n → ℕ} :
    ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t = 2 ^ card n * ite (∀ i, Even (k i)) 1 0 := by
  norm_num [sum_prod_piFinset _ fun i ↦ (· ^ k i), neg_one_pow_eq_ite, ite_add,
    Fintype.prod_ite_zero]

private lemma step_six {f : α → ℝ} {a b : n → α} :
    ∑ k : n → ℕ in piAntidiag univ m,
        (multinomial univ fun a ↦ 2 * k a : ℝ) * ∏ i, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2) ^ m := by
  simp only [sum_pow_eq_sum_piAntidiag, mul_sum, ← mul_assoc, pow_mul]
  gcongr with k hk
  rw [mem_piAntidiag] at hk
  exact mod_cast multinomial_two_mul_le_mul_multinomial.trans (by rw [hk.1])

private lemma end_step {f : α → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a in A ^^ n, ∑ b in A ^^ n, ∑ k in piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / A.card ^ card n
        ≤ (4 * m) ^ m * ∑ a in A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  let B := A ^^ n
  calc
    (∑ a in B, ∑ b in B, ∑ k : n → ℕ in piAntidiag univ m,
      (multinomial univ fun i ↦ 2 * k i : ℝ) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) /
        A.card ^ card n
    _ ≤ (∑ a in B, ∑ b in B, m ^ m * 2 ^ (m + (m - 1)) *
          ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) / A.card ^ card n := by
      gcongr; exact step_six.trans <| step_seven.trans step_eight
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← mul_add, ← two_mul, card_piFinset, prod_const, card_univ, Nat.cast_pow,
        mul_div_cancel_left₀ _ (by positivity), ← mul_assoc, mul_assoc _ _ 2, mul_comm 4, mul_pow,
        ← pow_succ, add_assoc, Nat.sub_add_cancel hm, ← two_mul, pow_mul]
      norm_num

namespace Real

/-- The **Marcinkiewicz-Zygmund inequality** for real-valued functions, with a slightly better
constant than `Real.marcinkiewicz_zygmund`. -/
theorem marcinkiewicz_zygmund' (m : ℕ) (f : α → ℝ) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    ∑ a in A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * ∑ a in A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  obtain rfl | hA := A.eq_empty_or_nonempty
  · cases isEmpty_or_nonempty n <;> cases m <;> simp
  let B := A ^^ n
  calc
    ∑ a in B, (∑ i, f (a i)) ^ (2 * m)
      ≤ ∑ a in A ^^ n, (∑ b in B, |∑ i, (f (a i) - f (b i))| ^ (2 * m)) / A.card ^ card n := by
      gcongr; simpa [pow_mul, sq_abs] using step_one' hA f hf (2 * m) _
    _ ≤ _ := ?_
  rw [← sum_div]
  simp only [pow_mul, sq_abs]
  simp only [← pow_mul]
  rw [step_two, step_three, mul_comm, inv_pow, ← div_eq_mul_inv, div_div]
  simp only [step_four, mul_ite, mul_zero, mul_one, ← sum_filter, ← sum_mul]
  rw [mul_comm, mul_div_mul_left _ _ (by positivity)]
  simpa only [even_iff_two_dvd, ← map_nsmul_piAntidiag_univ _ two_ne_zero, sum_map,
    Function.Embedding.coeFn_mk] using end_step hm' hA

/-- The **Marcinkiewicz-Zygmund inequality** for real-valued functions, with a slightly easier to
bound constant than `Real.marcinkiewicz_zygmund'`.

Note that `InnerProductSpace.marcinkiewicz_zygmund` and `RCLike.marcinkiewicz_zygmund` are other
versions that works for more general target spaces, at the expense of a slightly worse constant. -/
theorem marcinkiewicz_zygmund (hm : m ≠ 0) (f : α → ℝ) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    ∑ a in A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * card n ^ (m - 1) * ∑ a in A ^^ n, ∑ i, f (a i) ^ (2 * m) := by
  obtain _ | m := m
  · simp at hm
  obtain hn | hn := isEmpty_or_nonempty n
  · simp
  calc
    ∑ a in A ^^ n, (∑ i, f (a i)) ^ (2 * (m + 1))
      ≤ (4 * ↑(m + 1)) ^ (m + 1) * ∑ a in A ^^ n, (∑ i, f (a i) ^ 2) ^ (m + 1) :=
      marcinkiewicz_zygmund' _ f hf
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * (∑ a in A ^^ n, card n ^ m * ∑ i, f (a i) ^ (2 * (m + 1))) := ?_
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * card n ^ m * ∑ a in A ^^ n, ∑ i, f (a i) ^ (2 * (m + 1)) := by
      simp_rw [mul_assoc, mul_sum]; rfl
  gcongr with a
  rw [← div_le_iff' (by positivity)]
  have := Real.pow_sum_div_card_le_sum_pow (f := fun i ↦ f (a i) ^ 2) univ m fun i _ ↦ by positivity
  simpa only [Finset.card_fin, pow_mul] using this

end Real

namespace InnerProductSpace
variable {𝕜 : Type*} [NormedAddCommGroup 𝕜] [InnerProductSpace ℝ 𝕜] [FiniteDimensional ℝ 𝕜]

open FiniteDimensional in
/-- The **Marcinkiewicz-Zygmund inequality** for functions valued in a real inner product space. -/
lemma marcinkiewicz_zygmund (hm : m ≠ 0) (f : α → 𝕜) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    ∑ a in A ^^ n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (4 * finrank ℝ 𝕜 * m) ^ m * card n ^ (m - 1) * ∑ a in A ^^ n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  obtain ht | ht := Nat.eq_zero_or_pos (finrank ℝ 𝕜)
  · rw [FiniteDimensional.finrank_zero_iff] at ht
    have : 2 * m ≠ 0 := by positivity
    simp [norm_of_subsingleton, zero_pow this]
  let b := stdOrthonormalBasis ℝ 𝕜; clear_value b
  set B := A ^^ n
  simp only [pow_mul, ← b.repr.norm_map, PiLp.norm_sq_eq_of_L2, map_sum, norm_eq_abs, sq_abs,
    Fintype.sum_apply (γ := n)]
  set T := Fin (finrank ℝ 𝕜)
  calc
    ∑ a in B, (∑ t : T, (∑ i, b.repr (f (a i)) t) ^ 2) ^ m
      = ∑ a in B, card T ^ (m - 1)
          * ((∑ t : T, (∑ i, b.repr (f (a i)) t) ^ 2) ^ m / card T ^ (m - 1)) := by
      congr! with a
      have : 0 < card T := by simpa [T] using ht
      field_simp
    _ ≤ ∑ a in B, card T ^ (m - 1) * (∑ t : T, ((∑ i, b.repr (f (a i)) t) ^ 2) ^ m) := by
      gcongr with a
      convert pow_sum_div_card_le_sum_pow (s := Finset.univ) (n := m - 1) ?_
      · rw [sub_one_add_one hm]
      · rw [sub_one_add_one hm]
      · intros; positivity
    _ = card T ^ (m - 1) * (∑ t : T, ∑ a in B, (∑ i, b.repr (f (a i)) t) ^ (2 * m)) := by
      simp only [← sum_add_distrib, mul_sum, pow_mul]
      rw [sum_comm]
    _ ≤ card T ^ (m - 1) * (∑ t : T, (4 * m) ^ m * card n ^ (m - 1) *
          ∑ a in B, ∑ i, b.repr (f (a i)) t ^ (2 * m)) := by
      gcongr with t
      apply Real.marcinkiewicz_zygmund hm (f := fun x ↦ b.repr (f x) t)
      intro i
      rw [← Finset.sum_apply, ← map_sum (g := b.repr), hf, map_zero, PiLp.zero_apply]
    _ = card T ^ (m - 1) * ((4 * m) ^ m * card n ^ (m - 1) *
          ∑ a in B, ∑ i, ∑ t : T, (b.repr (f (a i)) t ^ (2 * m))) := by
      simp only [Finset.mul_sum, sum_comm (γ := T)]
    _ ≤ card T ^ (m - 1) * ((4 * m) ^ m * card n ^ (m - 1) *
          ∑ a in B, ∑ i, ∑ t' : T, (∑ t : T, b.repr (f (a i)) t ^ 2) ^ m) := by
      simp_rw [pow_mul]
      gcongr with a _ i _ t' ht'
      apply single_le_sum (s := Finset.univ) (f := fun t ↦ (b.repr (f (a i)) t) ^ 2) ?_ ht'
      intros
      positivity
    _ = card T ^ (m - 1) * ((4 * m) ^ m * card n ^ (m - 1) *
          ∑ a in B, ∑ i, card T * (∑ t : T, b.repr (f (a i)) t ^ 2) ^ m) := by simp
    _ = (4 * card T * m) ^ m * (card n) ^ (m - 1) *
        ∑ a in B, ∑ i, (∑ t : T, b.repr (f (a i)) t ^ 2) ^ m := by
      simp_rw [← mul_sum, ← mul_assoc]
      congrm ?_ * _
      nth_rw 3 6 [← sub_one_add_one hm]
      ring
    _ = _ := by simp [T]

end InnerProductSpace

namespace RCLike
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **Marcinkiewicz-Zygmund inequality** for real- or complex-valued functions. -/
lemma marcinkiewicz_zygmund (hm : m ≠ 0) (f : α → 𝕜) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    ∑ a in A ^^ n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * card n ^ (m - 1) * ∑ a in A ^^ n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  let _ : InnerProductSpace ℝ 𝕜 := RCLike.innerProductSpaceReal
  refine le_trans (InnerProductSpace.marcinkiewicz_zygmund hm f hf) ?_
  gcongr
  norm_cast
  linarith [RCLike.finrank_le_two 𝕜]

end RCLike
