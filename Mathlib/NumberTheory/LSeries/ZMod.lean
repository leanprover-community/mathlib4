/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# L-series of functions on `ZMod N`

We show that if `N` is a positive integer and `Φ : ZMod N → ℂ`, then the L-series of `Φ` has
analytic continuation (away from a pole at `s = 1` if `∑ j, Φ j ≠ 0`). Assuming `Φ` is either
even or odd, we define completed L-series and show analytic continuation of these too.

These results are most useful when `Φ` is a Dirichlet character, but the results are valid without
assuming this much stronger condition.

All definitions and theorems are in the `ZMod` namespace.

## Main definitions

* `LFunction Φ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction Φ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction Φ s * gammaFactor Φ s` where `gammaFactor Φ s` is the archimedean Gamma-factor.

(Note that if `Φ` is not even, then `completedLFunction Φ s` is the L-function of the odd part of
`Φ`, even if `Φ` isn't itself odd. This is an implementation detail and should not be relied on.)

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction Φ s = completedLFunction Φ s / gammaFactor Φ s`, unless `s = 0` and `Φ 0 ≠ 0`.
* `differentiable_completedLFunction`: if `∑ j, Φ j = 0` and `Φ 0 = 0` then `completedLFunction Φ s`
  is differentiable everywhere.
* `differentiable_LFunction`: if `∑ j, Φ j = 0` is nontrivial then `LFunction Φ s` is differentiable
  everywhere.
-/

open HurwitzZeta Complex ZMod Finset Classical

open scoped Real

section LemmasToBeRehomed

/-- Equivalence between `ℕ` and `ZMod N × ℕ`, sending `n` to `(n mod N, n / N)`. -/
def Nat.residueClassesEquiv (N : ℕ) [NeZero N] : ℕ ≃ ZMod N × ℕ where
  toFun n := (↑n, n / N)
  invFun p := p.1.val + N * p.2
  left_inv n := by simpa only [val_natCast] using Nat.mod_add_div n N
  right_inv p := by
    ext1
    · simp only [add_comm p.1.val, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero, zero_mul,
        natCast_val, cast_id', id_eq, zero_add]
    · simp only [add_comm p.1.val, Nat.mul_add_div (NeZero.pos _),
        (Nat.div_eq_zero_iff <| (NeZero.pos _)).2 p.1.val_lt, add_zero]

/-- If `f` is a summable function on `ℕ`, and `0 < N`, then we may compute `∑' n : ℕ, f n` by
summing each residue class mod `N` separately. -/
lemma Nat.sumByResidueClasses {f : ℕ → ℂ} (hf : Summable f) (N : ℕ) [NeZero N] :
    ∑' n, f n = ∑ j : ZMod N, ∑' m, f (j.val + N * m) := by
  rw [← (residueClassesEquiv N).symm.tsum_eq f, tsum_prod, tsum_fintype, residueClassesEquiv,
    Equiv.coe_fn_symm_mk]
  exact hf.comp_injective (residueClassesEquiv N).symm.injective

/-- A function is even if it satisfis `f (-x) = f x` for all `x`. -/
protected def Function.Even {R R' : Type*} [Neg R] (f : R → R') : Prop := ∀ (x : R), f (-x) = f x

/-- A function is odd if it satisfis `f (-x) = -f x` for all `x`. -/
protected def Function.Odd {R R' : Type*} [Neg R] [Neg R'] (f : R → R') : Prop :=
  ∀ (x : R), f (-x) = -(f x)

end LemmasToBeRehomed

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- If `Φ` is a periodic function, then the L-series of `Φ` converges for `1 < re s`. -/
lemma LSeriesSummable_of_one_lt_re (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LSeriesSummable (Φ ·) s := by
  let c := max' _ <| univ_nonempty.image (Complex.abs ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ ↦ le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, Φ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries Φ`: they agree in the convergence range, but
`LSeries Φ s` is defined to be `0` if `re s ≤ 1`.
 -/
noncomputable def LFunction (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s

/-- The L-function of a function on `ZMod 1` is a scalar multiple of the Riemann zeta function. -/
lemma LFunction_mod_one (Φ : ZMod 1 → ℂ) (s : ℂ) :
    LFunction Φ s = Φ 1 * riemannZeta s := by
  simp only [LFunction, Nat.cast_one, one_cpow, univ_unique, sum_singleton, one_mul]
  change Φ 1 * hurwitzZeta (toAddCircle 0) s = _
  rw [map_zero, hurwitzZeta_zero]

open scoped LSeries.notation in
/-- For `1 < re s` the congruence L-function agrees with the sum of the Dirichlet series. -/
lemma LFunction_eq_LSeries (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LFunction Φ s = LSeries ↗Φ s := by
  rw [LFunction, LSeries, mul_sum, Nat.sumByResidueClasses (LSeriesSummable_of_one_lt_re Φ hs) N]
  refine sum_congr (by rfl) (fun j _ ↦ ?_) -- choose some `j ∈ ZMod N`
  have ha : (j.val / N : ℝ) ∈ Set.Icc 0 1 := ⟨by positivity, by
    rw [div_le_one (Nat.cast_pos.mpr <| NeZero.pos _), Nat.cast_le]
    exact (val_lt _).le⟩
  rw [toAddCircle_apply, ← (hasSum_hurwitzZeta_of_one_lt_re ha hs).tsum_eq, ← mul_assoc,
    ← tsum_mul_left]
  congr 1 with m
  have aux0 : (m : ℂ) + ↑(j.val / N : ℝ) = ↑((j.val + N * m) / N : ℝ) := by
    push_cast
    rw [add_div, mul_div_cancel_left₀ _ (NeZero.ne _), add_comm]
  have aux1 : (0 : ℝ) ≤ j.val + N * m := by positivity
  have aux2 : (0 : ℝ) ≤ (↑N)⁻¹ := by positivity
  have aux3 : arg (N : ℂ) ≠ π := by simpa only [natCast_arg] using Real.pi_pos.ne
  have aux4 : ((N : ℂ) ^ s)⁻¹ ≠ 0 := by
    simp only [ne_eq, inv_eq_zero, cpow_eq_zero_iff, NeZero.ne, false_and, not_false_eq_true]
  rw [aux0, div_eq_mul_inv _ (N : ℝ), ofReal_mul, mul_cpow_ofReal_nonneg aux1 aux2, ← div_div,
    ofReal_inv, ofReal_natCast, cpow_neg, inv_cpow _ _ aux3, ← mul_div_assoc, mul_assoc,
    mul_div_cancel_left₀ _ aux4, mul_one_div, ← Nat.cast_mul, ← Nat.cast_add, ofReal_natCast,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), Nat.cast_add (R := ZMod _), Nat.cast_mul,
    CharP.cast_eq_zero (R := ZMod N) (p := N), zero_mul, add_zero]
  simp only [Nat.cast_add, natCast_val, Nat.cast_mul, cast_id', id_eq]

private lemma differentiable_Npow : Differentiable ℂ (fun (s : ℂ) ↦ (N : ℂ) ^ (-s)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl <| NeZero.ne _)

lemma differentiableAt_LFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt ℂ (LFunction Φ) s := by
  apply (differentiable_Npow s).mul
  rcases ne_or_eq s 1 with hs' | rfl
  · exact .sum fun j _ ↦ (differentiableAt_hurwitzZeta _ hs').const_mul _
  · have := DifferentiableAt.sum (u := univ) fun j _ ↦
      (differentiableAt_hurwitzZeta_sub_one_div (toAddCircle j)).const_mul (Φ j)
    simpa only [mul_sub, sum_sub_distrib, ← sum_mul, hs.neg_resolve_left rfl, zero_mul, sub_zero]

lemma differentiable_LFunction_of_sum_zero {Φ : ZMod N → ℂ} (hΦ : ∑ j, Φ j = 0) :
    Differentiable ℂ (LFunction Φ) :=
  fun s ↦ differentiableAt_LFunction Φ s (Or.inr hΦ)

section signed

variable {Φ : ZMod N → ℂ} (hΦ : Φ.Even ∨ Φ.Odd)

/-- If `Φ` is either even or odd, we can write `LFunction Φ s` using signed Hurwitz zeta functions.
Useful for comparison with `completedLFunction Φ s`. -/
lemma LFunction_def_signed (s : ℂ) :
    LFunction Φ s =
      if Φ.Even then N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s
      else N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s := by
  simp only [LFunction, ← mul_ite, hurwitzZeta, mul_add, sum_add_distrib]
  rw [← mul_add]
  congr 1
  by_cases h : Φ.Even
  · simp only [h, ↓reduceIte, add_right_eq_self, ← _root_.neg_eq_self_iff, ← sum_neg_distrib]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, h i, map_neg, hurwitzZetaOdd_neg, mul_neg]
  · simp only [h, ↓reduceIte, add_left_eq_self, ← _root_.neg_eq_self_iff, ← sum_neg_distrib]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, map_neg, hurwitzZetaEven_neg, (show Φ.Odd by tauto) i, neg_mul]

variable (Φ) in
/-- The completed L-function of a function mod `N`.

This is well-defined for all `Φ`, but is uninteresting unless `Φ` is either even or odd. -/
noncomputable def completedLFunction (s : ℂ) : ℂ :=
  if Φ.Even then N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven (toAddCircle j) s
  else N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

/--
The L-function a function mod 1 is a scalar multiple of the completed Riemann zeta function.
-/
lemma completedLFunction_mod_one {Φ : ZMod 1 → ℂ} (s : ℂ) :
    completedLFunction Φ s = Φ 1 * completedRiemannZeta s := by
  have : Φ.Even := fun j ↦ congr_arg Φ <| (Unique.eq_default (-j)).trans (Unique.eq_default j).symm
  simp [completedLFunction, this]
  change Φ 1 * completedHurwitzZetaEven (toAddCircle 0) s = _
  rw [map_zero, completedHurwitzZetaEven_zero]

variable (Φ) in
/--
The completed L-function of a function mod `N` is differentiable, with the following
exceptions: at `s = 1` if `∑ j, Φ j ≠ 0`; and at `s = 0` if `Φ 0 ≠ 0`.

Note `Φ` and `s` are explicit argument: we will always be able to infer one or other of them from
the hypotheses, but it's not clear which!
-/
lemma differentiableAt_completedLFunction (s : ℂ) (hs₀ : s ≠ 0 ∨ Φ 0 = 0)
    (hs₁ : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt ℂ (completedLFunction Φ) s := by
  unfold completedLFunction
  by_cases h : Φ.Even <;>
  simp only [h, reduceIte] <;>
  refine differentiable_Npow.differentiableAt.mul ?_
  · -- If `Φ` is even, then `completedLFunction Φ` is defined as a sum of terms which are all
    -- differentiable away from s = 0 and s = 1; but these cases need special handling.
    rcases ne_or_eq s 1 with hs₁' | rfl
    · refine .sum fun i _ ↦ ?_
      rcases ne_or_eq s 0 with hs₀' | rfl
      · -- Case s ∉ {0, 1} : all terms in sum are differentiable.
        exact (differentiableAt_completedHurwitzZetaEven _ (Or.inl hs₀') hs₁').const_mul _
      · -- Case s = 0 : all terms are differentiable except the one for `i = 0`, and this term is
        -- zero since `Φ 0 = 0`.
        replace hs₀ : Φ 0 = 0 := hs₀.neg_resolve_left rfl
        rcases ne_or_eq i 0 with hi | rfl
        · refine (differentiableAt_completedHurwitzZetaEven _ (Or.inr ?_) hs₁').const_mul _
          rwa [ne_eq, toAddCircle_eq_zero]
        · simp only [hs₀, map_zero, zero_mul, differentiableAt_const]
    · -- Case `s = 1` : each term in the sum is a differentiable function minus `Φ i / (s - 1)`. We
      -- re-group the sum accordingly, and then use the fact that `∑ i, Φ i = 0`.
      simp only [completedHurwitzZetaEven_eq, mul_sub, sum_sub_distrib]
      refine .sub (.sub (.sum fun i _ ↦ ?_) (.sum fun i _ ↦ ?_)) ?_
      · exact (differentiable_completedHurwitzZetaEven₀ _).differentiableAt.const_mul _
      · refine ((differentiableAt_const _).div differentiableAt_id ?_).const_mul _
        exact one_ne_zero
      · simp only [← sum_mul, hs₁.neg_resolve_left rfl, zero_mul,
          differentiableAt_const]
  · -- Easy case (Φ odd)
    exact .sum (fun i _ ↦ (differentiable_completedHurwitzZetaOdd _ _).const_mul _)

/-- Special case of `differentiableAt_completedLFunction` asserting differentiability everywhere
under suitable hypotheses. -/
lemma differentiable_completedLFunction (hΦ : Φ 0 = 0) (hΦ' : ∑ j, Φ j = 0) :
    Differentiable ℂ (completedLFunction Φ) :=
  fun s ↦ differentiableAt_completedLFunction Φ s (Or.inr hΦ) (Or.inr hΦ')

/-- The Archimedean Gamma factor: `Gammaℝ s` if `Φ` is even, and `Gammaℝ (s + 1)` otherwise. -/
noncomputable def gammaFactor (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
   if Φ.Even then Gammaℝ s else Gammaℝ (s + 1)

/-- Relation between the completed L-function and the usual one. We state it this way around so
it holds at the poles of the gamma factor as well. -/
lemma LFunction_eq_completed_div_gammaFactor (s : ℂ) (hs : s ≠ 0 ∨ Φ 0 = 0) :
    LFunction Φ s = completedLFunction Φ s / gammaFactor Φ s := by
  rw [LFunction_def_signed hΦ, completedLFunction, gammaFactor]
  split_ifs with h
  · -- `Φ` even
    simp only [mul_div_assoc, sum_div]
    congr 2 with i
    rcases ne_or_eq i 0 with hi | rfl
    · rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inl (hi ∘ toAddCircle_eq_zero.mp))]
    · rcases hs with hs | hΦ'
      · rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs)]
      · simp only [hΦ', map_zero, zero_mul]
  · -- `Φ` not even
    simp only [hurwitzZetaOdd, mul_div_assoc, sum_div]

/-- The L-function of an even function vanishes at negative even integers. -/
lemma LFunction_neg_two_mul_nat_add_one (hΦ : Φ.Even) (n : ℕ) :
    LFunction Φ (-2 * (n + 1)) = 0 := by
  simp only [LFunction_def_signed (Or.inl hΦ), hΦ, ↓reduceIte,
    hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero, sum_const_zero]

/-- The L-function of an odd function vanishes at negative odd integers. -/
lemma LFunction_neg_two_mul_nat_sub_one (hΦ : Φ.Odd) (n : ℕ) :
    LFunction Φ (-2 * n - 1) = 0 := by
  by_cases hΦ' : Φ.Even
  · -- silly case: `Φ` is both even and odd, so it's zero
    have : Φ = 0 := funext fun j ↦ by rw [Pi.zero_apply, ← eq_neg_self_iff, ← hΦ j, hΦ' j]
    simp [LFunction, this]
  · simp only [LFunction_def_signed (Or.inr hΦ), hΦ', ↓reduceIte,
      hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero, sum_const_zero]

end signed

end ZMod
