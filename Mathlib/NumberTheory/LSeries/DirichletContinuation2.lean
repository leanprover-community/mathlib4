/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Analytic continuation of Dirichlet L-functions

We show that if `χ` is a Dirichlet character `ZMod N → ℂ`, for a positive integer `N`, then the
L-series of `χ` has meromorphic continuation (away from a pole at `s = 1` if `χ` is trivial).

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction χ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction χ s * gammaFactor χ s` where `gammaFactor χ s` is the archimedean Gamma-factor.

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `LFunction_eq_completed_div_gammaFactor`: we have
  `LFunction χ s = completedLFunction χ s / gammaFactor χ s`, unless `s = 0` and `χ` is the trivial
  character modulo 1.
* `differentiable_completedLFunction`: if `χ` is nontrivial then `completedLFunction χ s` is
  differentiable everywhere.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
-/

open HurwitzZeta Complex ZMod Finset Classical

open scoped Real

namespace DirichletContinuationOld

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

end LemmasToBeRehomed

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, χ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries χ`: they agree in the convergence range, but
`LSeries χ s` is defined to be `0` if `re s ≤ 1`.
 -/
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, χ j * hurwitzZeta (toAddCircle j) s

/-- The L-function of the (unique) Dirichlet character mod 1 is the trivial character. -/
lemma LFunction_mod_one {χ : DirichletCharacter ℂ 1} :
    LFunction χ = riemannZeta := by
  ext s
  simp only [LFunction, PNat.val_ofNat, Nat.cast_one, one_cpow, univ_unique, sum_singleton, one_mul]
  change χ 1 * hurwitzZeta (toAddCircle 0) s = _
  rw [map_one, one_mul, map_zero, hurwitzZeta_zero]

open scoped LSeries.notation in
/-- For `1 < re s` the congruence L-function agrees with the sum of the Dirichlet series. -/
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s = LSeries ↗χ s := by
  rw [LFunction, LSeries, mul_sum, Nat.sumByResidueClasses (χ.LSeriesSummable_of_one_lt_re hs) N]
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

/-- Alternate version of the definition of `LFunction χ s` using signed Hurwitz zeta functions.
Useful for comparison with `completedLFunction χ s`. -/
lemma LFunction_def_signed (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LFunction χ s =
      if χ.Even then N ^ (-s) * ∑ j : ZMod N, χ j * hurwitzZetaEven (toAddCircle j) s
        else N ^ (-s) * ∑ j : ZMod N, χ j * hurwitzZetaOdd (toAddCircle j) s := by
  simp only [LFunction, ← mul_ite, hurwitzZeta, mul_add, sum_add_distrib]
  rw [← mul_add]
  congr 1
  rcases χ.even_or_odd with h | h
  · simp only [h, ↓reduceIte, add_right_eq_self, ← neg_eq_self ℂ, ← sum_neg_distrib]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, map_neg, hurwitzZetaOdd_neg, mul_neg]
    rw [← neg_one_mul i, map_mul, h, one_mul]
  · simp only [h.not_even, ↓reduceIte, add_left_eq_self, ← neg_eq_self ℂ, ← sum_neg_distrib]
    refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
    simp only [Equiv.neg_apply, map_neg, hurwitzZetaEven_neg, mul_neg]
    rw [← neg_one_mul i, map_mul, h, neg_mul, neg_mul, one_mul]

/-- The completed L-function of a Dirichlet character. -/
noncomputable def completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  if χ.Even then N ^ (-s) * ∑ j : ZMod N, χ j * completedHurwitzZetaEven (toAddCircle j) s
  else N ^ (-s) * ∑ j : ZMod N, χ j * completedHurwitzZetaOdd (toAddCircle j) s

/--
The L-function of the (unique) Dirichlet character mod 1 is the completed Riemann zeta function.
-/
lemma completedLFunction_mod_one {χ : DirichletCharacter ℂ (1 : ℕ+)} :
    completedLFunction χ = completedRiemannZeta := by
  have : χ.Even := χ.map_one -- this works (!)
  ext s
  simp only [completedLFunction, PNat.val_ofNat, Nat.cast_one, one_cpow, univ_unique, sum_singleton,
    one_mul, ↓reduceIte, this]
  change χ 1 * completedHurwitzZetaEven (toAddCircle 0) s = _
  rw [map_one, one_mul, map_zero, completedHurwitzZetaEven_zero]

/--
The completed L-function of a Dirichlet character is differentiable, with the following
exceptions: at `s = 1` if `χ` is the trivial character (to any modulus); and at `s = 0` if the
modulus is 1. This result is best possible.

Note both `χ` and `s` are explicit arguments: we will always be able to infer one or other
of them from the hypotheses, but it's not clear which!
-/
lemma differentiableAt_completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ N ≠ 1) (hs₁ : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (completedLFunction χ) s := by
  unfold completedLFunction
  have aux1 : Differentiable ℂ (fun (s : ℂ) ↦ (N : ℂ) ^ (-s)) :=
    Differentiable.const_cpow (by fun_prop) (Or.inl <| NeZero.ne _)
  have aux2 (hχ : χ ≠ 1) : N ≠ 1 := (hχ <| χ.level_one' ·)
  by_cases h : χ.Even <;>
  simp only [h, reduceIte] <;>
  refine aux1.differentiableAt.mul ?_
  · -- If `χ` is even, then `completedLFunction χ` is defined as a sum of terms which are all
    -- differentiable away from s = 0 and s = 1; but these cases need special handling.
    rcases ne_or_eq s 1 with hs₁' | rfl
    · refine .sum fun i _ ↦ ?_
      rcases ne_or_eq s 0 with hs₀' | rfl
      · -- Case s ≠ 0, 1 : all terms in sum are differentiable.
        exact (differentiableAt_completedHurwitzZetaEven _ (Or.inl hs₀') hs₁').const_mul _
      · -- Case s = 0 : all terms are differentiable except the one for `i = 0`. Since we are
        -- assuming `N ≠ 1`, the coefficient of the `i = 0` term (which is `χ 0`) vanishes.
        replace hs₀ : N ≠ 1 := by tauto
        rcases ne_or_eq i 0 with hi | rfl
        · refine (differentiableAt_completedHurwitzZetaEven _ (Or.inr ?_) hs₁').const_mul _
          rwa [ne_eq, toAddCircle_eq_zero]
        · simp only [χ.map_zero' hs₀, map_zero, zero_mul, differentiableAt_const]
    · -- Case `s = 1` : each term in the sum is a differentiable function minus `χ i / (s - 1)`. We
      -- re-group the sum accordingly, and then use the fact that `∑ i, χ i = 0`.
      simp only [completedHurwitzZetaEven_eq, mul_sub, sum_sub_distrib]
      refine .sub (.sub (.sum fun i _ ↦ ?_) (.sum fun i _ ↦ ?_)) ?_
      · exact (differentiable_completedHurwitzZetaEven₀ _).differentiableAt.const_mul _
      · refine ((differentiableAt_const _).div differentiableAt_id ?_).const_mul _
        exact one_ne_zero
      · simp only [← sum_mul, χ.sum_eq_zero_of_ne_one (by tauto), zero_mul,
          differentiableAt_const]
  · -- Easy case (χ odd)
    exact .sum (fun i _ ↦ (differentiable_completedHurwitzZetaOdd _ _).const_mul _)

/-- The completed L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (completedLFunction χ) := by
  refine fun s ↦ differentiableAt_completedLFunction _ _ (Or.inr ?_) (Or.inr hχ)
  exact hχ ∘ χ.level_one'

/-- The Archimedean Gamma factor for a Dirichlet character: `Gammaℝ s` if `χ` is even, and
`Gammaℝ (s + 1)` otherwise. -/
noncomputable def gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
   if χ.Even then Gammaℝ s else Gammaℝ (s + 1)

/-- Relation between the completed L-function and the usual one. We state it this way around so
it holds at the poles of the gamma factor as well. -/
lemma LFunction_eq_completed_div_gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : s ≠ 0 ∨ N ≠ 1) :
    LFunction χ s = completedLFunction χ s / gammaFactor χ s := by
  rw [LFunction_def_signed, completedLFunction, gammaFactor]
  split_ifs with h
  · -- `χ` even
    simp only [mul_div_assoc, sum_div]
    congr 2 with i
    rcases ne_or_eq i 0 with hi | rfl
    · rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inl (hi ∘ toAddCircle_eq_zero.mp))]
    · rcases hs with hs | hN
      · rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs)]
      simp only [χ.map_zero' hN, map_zero, zero_mul]
  · -- `χ` odd
    simp only [hurwitzZetaOdd, mul_div_assoc, sum_div]

/--
The L-function of a Dirichlet character is differentiable, except at `s = 1` if the character is
trivial. This result is best possible.

Note both `χ` and `s` are explicit arguments: we will always be able to infer one or other
of them from the hypotheses, but it's not clear which!
-/
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  rcases eq_or_ne s 1 with rfl | hs'
  · have : N ≠ 1 :=
      fun h ↦ ((show χ ≠ 1 by tauto) <| χ.level_one' h)
    simp only [funext fun s ↦ LFunction_eq_completed_div_gammaFactor χ s (Or.inr this)]
    refine (differentiable_completedLFunction (by tauto) _).mul ?_
    simp only [gammaFactor]
    split_ifs
    · exact differentiable_Gammaℝ_inv _
    · apply differentiable_Gammaℝ_inv.comp (f := fun s ↦ s + 1) (by fun_prop)
  · refine ((differentiable_neg _).const_cpow (Or.inl <| NeZero.ne _)).mul ?_
    exact .sum fun _ _ ↦ (differentiableAt_hurwitzZeta _ hs').const_mul _

/-- The L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (differentiableAt_LFunction _ · <| Or.inr hχ)

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (n : ℕ) :
    LFunction χ (-2 * (n + 1)) = 0 := by
  simp only [LFunction_def_signed, hχ, ↓reduceIte, hurwitzZetaEven_neg_two_mul_nat_add_one,
    mul_zero, sum_const_zero]

/-- The L-function of an odd Dirichlet character vanishes at negative odd integers. -/
lemma Odd.LFunction_neg_two_mul_nat_sub_one {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (n : ℕ) :
    LFunction χ (-2 * n - 1) = 0 := by
  simp only [LFunction_def_signed, hχ.not_even, ↓reduceIte, hurwitzZetaOdd_neg_two_mul_nat_sub_one,
    mul_zero, sum_const_zero]

end DirichletCharacter

end DirichletContinuationOld
