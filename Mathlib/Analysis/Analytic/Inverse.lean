/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.analytic.inverse
! leanprover-community/mathlib commit 284fdd2962e67d2932fa3a79ce19fcf92d38e228
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Analytic.Composition
import Mathbin.Tactic.Congrm

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
we prove that they coincide and study their properties (notably convergence).

## Main statements

* `p.left_inv i`: the formal left inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.right_inv i`: the formal right inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.left_inv_comp` says that `p.left_inv i` is indeed a left inverse to `p` when `p₁ = i`.
* `p.right_inv_comp` says that `p.right_inv i` is indeed a right inverse to `p` when `p₁ = i`.
* `p.left_inv_eq_right_inv`: the two inverses coincide.
* `p.radius_right_inv_pos_of_radius_pos`: if a power series has a positive radius of convergence,
  then so does its inverse.

-/


open scoped BigOperators Classical Topology

open Finset Filter

namespace FormalMultilinearSeries

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-! ### The left inverse of a formal multilinear series -/


/-- The left inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `(left_inv p i) ∘ p = id`. For this, the linear term
`p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. We adjust the definition so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def leftInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => 0
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
  | n + 2 =>
    -∑ c : { c : Composition (n + 2) // c.length < n + 2 },
        have : (c : Composition (n + 2)).length < n + 2 := c.2
        (left_inv (c : Composition (n + 2)).length).compAlongComposition
          (p.compContinuousLinearMap i.symm) c
#align formal_multilinear_series.left_inv FormalMultilinearSeries.leftInv

@[simp]
theorem leftInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.left_inv i 0 = 0 := by rw [left_inv]
#align formal_multilinear_series.left_inv_coeff_zero FormalMultilinearSeries.leftInv_coeff_zero

@[simp]
theorem leftInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.left_inv i 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm := by rw [left_inv]
#align formal_multilinear_series.left_inv_coeff_one FormalMultilinearSeries.leftInv_coeff_one

/-- The left inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
theorem leftInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.removeZero.left_inv i = p.left_inv i := by
  ext1 n
  induction' n using Nat.strongRec' with n IH
  cases n; · simp
  -- if one replaces `simp` with `refl`, the proof times out in the kernel.
  cases n;
  · simp
  -- TODO: why?
  simp only [left_inv, neg_inj]
  refine' Finset.sum_congr rfl fun c cuniv => _
  rcases c with ⟨c, hc⟩
  ext v
  dsimp
  simp [IH _ hc]
#align formal_multilinear_series.left_inv_remove_zero FormalMultilinearSeries.leftInv_removeZero

/-- The left inverse to a formal multilinear series is indeed a left inverse, provided its linear
term is invertible. -/
theorem leftInv_comp (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) : (leftInv p i).comp p = id 𝕜 E :=
  by
  ext (n v)
  cases n
  ·
    simp only [left_inv, ContinuousMultilinearMap.zero_apply, id_apply_ne_one, Ne.def,
      not_false_iff, zero_ne_one, comp_coeff_zero']
  cases n
  ·
    simp only [left_inv, comp_coeff_one, h, id_apply_one, ContinuousLinearEquiv.coe_apply,
      ContinuousLinearEquiv.symm_apply_apply, continuousMultilinearCurryFin1_symm_apply]
  have A :
    (Finset.univ : Finset (Composition (n + 2))) =
      {c | Composition.length c < n + 2}.toFinset ∪ {Composition.ones (n + 2)} :=
    by
    refine' subset.antisymm (fun c hc => _) (subset_univ _)
    by_cases h : c.length < n + 2
    · simp [h]
    · simp [Composition.eq_ones_iff_le_length.2 (not_lt.1 h)]
  have B :
    Disjoint ({c | Composition.length c < n + 2} : Set (Composition (n + 2))).toFinset
      {Composition.ones (n + 2)} :=
    by simp
  have C :
    ((p.left_inv i (Composition.ones (n + 2)).length)
        fun j : Fin (Composition.ones n.succ.succ).length =>
        p 1 fun k => v ((Fin.castLE (Composition.length_le _)) j)) =
      p.left_inv i (n + 2) fun j : Fin (n + 2) => p 1 fun k => v j :=
    by
    apply FormalMultilinearSeries.congr _ (Composition.ones_length _) fun j hj1 hj2 => _
    exact FormalMultilinearSeries.congr _ rfl fun k hk1 hk2 => by congr
  have D :
    (p.left_inv i (n + 2) fun j : Fin (n + 2) => p 1 fun k => v j) =
      -∑ c : Composition (n + 2) in {c : Composition (n + 2) | c.length < n + 2}.toFinset,
          (p.left_inv i c.length) (p.apply_composition c v) :=
    by
    simp only [left_inv, ContinuousMultilinearMap.neg_apply, neg_inj,
      ContinuousMultilinearMap.sum_apply]
    convert
      (sum_to_finset_eq_subtype (fun c : Composition (n + 2) => c.length < n + 2)
              fun c : Composition (n + 2) =>
              (ContinuousMultilinearMap.compAlongComposition (p.comp_continuous_linear_map ↑i.symm)
                  c (p.left_inv i c.length))
                fun j : Fin (n + 2) => p 1 fun k : Fin 1 => v j).symm.trans
        _
    simp only [comp_continuous_linear_map_apply_composition,
      ContinuousMultilinearMap.compAlongComposition_apply]
    congr
    ext c
    congr
    ext k
    simp [h]
  simp [FormalMultilinearSeries.comp, show n + 2 ≠ 1 by decide, A, Finset.sum_union B,
    apply_composition_ones, C, D, -Set.toFinset_setOf]
#align formal_multilinear_series.left_inv_comp FormalMultilinearSeries.leftInv_comp

/-! ### The right inverse of a formal multilinear series -/


/-- The right inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `p ∘ (right_inv p i) = id`. For this, the linear
term `p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `p ∘ q` is `∑ pₖ (q_{j₁}, ..., q_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `p₁ (qₙ)`. We adjust the definition of `qₙ` so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => 0
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
  | n + 2 =>
    let q : FormalMultilinearSeries 𝕜 F E := fun k => if h : k < n + 2 then right_inv k else 0
    -(i.symm : F →L[𝕜] E).compContinuousMultilinearMap ((p.comp q) (n + 2))
#align formal_multilinear_series.right_inv FormalMultilinearSeries.rightInv

@[simp]
theorem rightInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.right_inv i 0 = 0 := by rw [right_inv]
#align formal_multilinear_series.right_inv_coeff_zero FormalMultilinearSeries.rightInv_coeff_zero

@[simp]
theorem rightInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.right_inv i 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm := by rw [right_inv]
#align formal_multilinear_series.right_inv_coeff_one FormalMultilinearSeries.rightInv_coeff_one

/-- The right inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
theorem rightInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.removeZero.right_inv i = p.right_inv i :=
  by
  ext1 n
  induction' n using Nat.strongRec' with n IH
  rcases n with (_ | _ | n)
  · simp only [right_inv_coeff_zero]
  · simp only [right_inv_coeff_one]
  simp only [right_inv, neg_inj]
  rw [remove_zero_comp_of_pos _ _ (add_pos_of_nonneg_of_pos n.zero_le zero_lt_two)]
  congr 2 with k
  by_cases hk : k < n + 2 <;> simp [hk, IH]
#align formal_multilinear_series.right_inv_remove_zero FormalMultilinearSeries.rightInv_removeZero

theorem comp_right_inv_aux1 {n : ℕ} (hn : 0 < n) (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 F E) (v : Fin n → F) :
    p.comp q n v =
      ∑ c : Composition n in {c : Composition n | 1 < c.length}.toFinset,
          p c.length (q.applyComposition c v) +
        p 1 fun i => q n v :=
  by
  have A :
    (Finset.univ : Finset (Composition n)) =
      {c | 1 < Composition.length c}.toFinset ∪ {Composition.single n hn} :=
    by
    refine' subset.antisymm (fun c hc => _) (subset_univ _)
    by_cases h : 1 < c.length
    · simp [h]
    · have : c.length = 1 := by refine' (eq_iff_le_not_lt.2 ⟨_, h⟩).symm;
        exact c.length_pos_of_pos hn
      rw [← Composition.eq_single_iff_length hn] at this 
      simp [this]
  have B :
    Disjoint ({c | 1 < Composition.length c} : Set (Composition n)).toFinset
      {Composition.single n hn} :=
    by simp
  have C :
    p (Composition.single n hn).length (q.apply_composition (Composition.single n hn) v) =
      p 1 fun i : Fin 1 => q n v :=
    by
    apply p.congr (Composition.single_length hn) fun j hj1 hj2 => _
    simp [apply_composition_single]
  simp [FormalMultilinearSeries.comp, A, Finset.sum_union B, C, -Set.toFinset_setOf]
#align formal_multilinear_series.comp_right_inv_aux1 FormalMultilinearSeries.comp_right_inv_aux1

theorem comp_rightInv_aux2 (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (n : ℕ)
    (v : Fin (n + 2) → F) :
    ∑ c : Composition (n + 2) in {c : Composition (n + 2) | 1 < c.length}.toFinset,
        p c.length (applyComposition (fun k : ℕ => ite (k < n + 2) (p.right_inv i k) 0) c v) =
      ∑ c : Composition (n + 2) in {c : Composition (n + 2) | 1 < c.length}.toFinset,
        p c.length ((p.right_inv i).applyComposition c v) :=
  by
  have N : 0 < n + 2 := by decide
  refine' sum_congr rfl fun c hc => p.congr rfl fun j hj1 hj2 => _
  have : ∀ k, c.blocks_fun k < n + 2 :=
    by
    simp only [Set.mem_toFinset, Set.mem_setOf_eq] at hc 
    simp [← Composition.ne_single_iff N, Composition.eq_single_iff_length, ne_of_gt hc]
  simp [apply_composition, this]
#align formal_multilinear_series.comp_right_inv_aux2 FormalMultilinearSeries.comp_rightInv_aux2

/-- The right inverse to a formal multilinear series is indeed a right inverse, provided its linear
term is invertible and its constant term vanishes. -/
theorem comp_rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) (h0 : p 0 = 0) :
    p.comp (rightInv p i) = id 𝕜 F := by
  ext (n v)
  cases n
  ·
    simp only [h0, ContinuousMultilinearMap.zero_apply, id_apply_ne_one, Ne.def, not_false_iff,
      zero_ne_one, comp_coeff_zero']
  cases n
  ·
    simp only [comp_coeff_one, h, right_inv, ContinuousLinearEquiv.apply_symm_apply, id_apply_one,
      ContinuousLinearEquiv.coe_apply, continuousMultilinearCurryFin1_symm_apply]
  have N : 0 < n + 2 := by decide
  simp [comp_right_inv_aux1 N, h, right_inv, lt_irrefl n, show n + 2 ≠ 1 by decide, ←
    sub_eq_add_neg, sub_eq_zero, comp_right_inv_aux2, -Set.toFinset_setOf]
#align formal_multilinear_series.comp_right_inv FormalMultilinearSeries.comp_rightInv

theorem rightInv_coeff (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (n : ℕ) (hn : 2 ≤ n) :
    p.right_inv i n =
      -(i.symm : F →L[𝕜] E).compContinuousMultilinearMap
          (∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition n)),
            p.compAlongComposition (p.right_inv i) c) :=
  by
  cases n; · exact False.elim (zero_lt_two.not_le hn)
  cases n; · exact False.elim (one_lt_two.not_le hn)
  simp only [right_inv, neg_inj]
  congr 1
  ext v
  have N : 0 < n + 2 := by decide
  have : ((p 1) fun i : Fin 1 => 0) = 0 := ContinuousMultilinearMap.map_zero _
  simp [comp_right_inv_aux1 N, lt_irrefl n, this, comp_right_inv_aux2, -Set.toFinset_setOf]
#align formal_multilinear_series.right_inv_coeff FormalMultilinearSeries.rightInv_coeff

/-! ### Coincidence of the left and the right inverse -/


private theorem left_inv_eq_right_inv_aux (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) (h0 : p 0 = 0) :
    leftInv p i = rightInv p i :=
  calc
    leftInv p i = (leftInv p i).comp (id 𝕜 F) := by simp
    _ = (leftInv p i).comp (p.comp (rightInv p i)) := by rw [comp_right_inv p i h h0]
    _ = ((leftInv p i).comp p).comp (rightInv p i) := by rw [comp_assoc]
    _ = (id 𝕜 E).comp (rightInv p i) := by rw [left_inv_comp p i h]
    _ = rightInv p i := by simp

/-- The left inverse and the right inverse of a formal multilinear series coincide. This is not at
all obvious from their definition, but it follows from uniqueness of inverses (which comes from the
fact that composition is associative on formal multilinear series). -/
theorem leftInv_eq_rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) : leftInv p i = rightInv p i :=
  calc
    leftInv p i = leftInv p.removeZero i := by rw [left_inv_remove_zero]
    _ = rightInv p.removeZero i := by apply left_inv_eq_right_inv_aux <;> simp [h]
    _ = rightInv p i := by rw [right_inv_remove_zero]
#align formal_multilinear_series.left_inv_eq_right_inv FormalMultilinearSeries.leftInv_eq_rightInv

/-!
### Convergence of the inverse of a power series

Assume that `p` is a convergent multilinear series, and let `q` be its (left or right) inverse.
Using the left-inverse formula gives
$$
q_n = - (p_1)^{-n} \sum_{k=0}^{n-1} \sum_{i_1 + \dotsc + i_k = n} q_k (p_{i_1}, \dotsc, p_{i_k}).
$$
Assume for simplicity that we are in dimension `1` and `p₁ = 1`. In the formula for `qₙ`, the term
`q_{n-1}` appears with a multiplicity of `n-1` (choosing the index `i_j` for which `i_j = 2` while
all the other indices are equal to `1`), which indicates that `qₙ` might grow like `n!`. This is
bad for summability properties.

It turns out that the right-inverse formula is better behaved, and should instead be used for this
kind of estimate. It reads
$$
q_n = - (p_1)^{-1} \sum_{k=2}^n \sum_{i_1 + \dotsc + i_k = n} p_k (q_{i_1}, \dotsc, q_{i_k}).
$$
Here, `q_{n-1}` can only appear in the term with `k = 2`, and it only appears twice, so there is
hope this formula can lead to an at most geometric behavior.

Let `Qₙ = ‖qₙ‖`. Bounding `‖pₖ‖` with `C r^k` gives an inequality
$$
Q_n ≤ C' \sum_{k=2}^n r^k \sum_{i_1 + \dotsc + i_k = n} Q_{i_1} \dotsm Q_{i_k}.
$$

This formula is not enough to prove by naive induction on `n` a bound of the form `Qₙ ≤ D R^n`.
However, assuming that the inequality above were an equality, one could get a formula for the
generating series of the `Qₙ`:

$$
\begin{align}
Q(z) & := \sum Q_n z^n = Q_1 z + C' \sum_{2 \leq k \leq n} \sum_{i_1 + \dotsc + i_k = n}
  (r z^{i_1} Q_{i_1}) \dotsm (r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (\sum_{i_1 \geq 1} r z^{i_1} Q_{i_1})
  \dotsm (\sum_{i_k \geq 1} r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (r Q(z))^k
= Q_1 z + C' (r Q(z))^2 / (1 - r Q(z)).
\end{align}
$$

One can solve this formula explicitly. The solution is analytic in a neighborhood of `0` in `ℂ`,
hence its coefficients grow at most geometrically (by a contour integral argument), and therefore
the original `Qₙ`, which are bounded by these ones, are also at most geometric.

This classical argument is not really satisfactory, as it requires an a priori bound on a complex
analytic function. Another option would be to compute explicitly its terms (with binomial
coefficients) to obtain an explicit geometric bound, but this would be very painful.

Instead, we will use the above intuition, but in a slightly different form, with finite sums and an
induction. I learnt this trick in [pöschel2017siegelsternberg]. Let
$S_n = \sum_{k=1}^n Q_k a^k$ (where `a` is a positive real parameter to be chosen suitably small).
The above computation but with finite sums shows that

$$
S_n \leq Q_1 a + C' \sum_{k=2}^n (r S_{n-1})^k.
$$

In particular, $S_n \leq Q_1 a + C' (r S_{n-1})^2 / (1- r S_{n-1})$.
Assume that $S_{n-1} \leq K a$, where `K > Q₁` is fixed and `a` is small enough so that
`r K a ≤ 1/2` (to control the denominator). Then this equation gives a bound
$S_n \leq Q_1 a + 2 C' r^2 K^2 a^2$.
If `a` is small enough, this is bounded by `K a` as the second term is quadratic in `a`, and
therefore negligible.

By induction, we deduce `Sₙ ≤ K a` for all `n`, which gives in particular the fact that `aⁿ Qₙ`
remains bounded.
-/


/-- First technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in a general abstract setup. -/
theorem radius_right_inv_pos_of_radius_pos_aux1 (n : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) :
    ∑ k in Ico 2 (n + 1),
        a ^ k *
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, p (c.blocksFun j) ≤
      ∑ j in Ico 2 (n + 1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j :=
  calc
    ∑ k in Ico 2 (n + 1),
          a ^ k *
            ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
              r ^ c.length * ∏ j, p (c.blocksFun j) =
        ∑ k in Ico 2 (n + 1),
          ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            ∏ j, r * (a ^ c.blocksFun j * p (c.blocksFun j)) :=
      by
      simp_rw [mul_sum]
      apply sum_congr rfl fun k hk => _
      apply sum_congr rfl fun c hc => _
      rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, Composition.sum_blocksFun,
        prod_const, card_fin]
      ring
    _ ≤
        ∑ d in compPartialSumTarget 2 (n + 1) n,
          ∏ j : Fin d.2.length, r * (a ^ d.2.blocksFun j * p (d.2.blocksFun j)) :=
      by
      rw [sum_sigma']
      refine'
        sum_le_sum_of_subset_of_nonneg _ fun x hx1 hx2 =>
          prod_nonneg fun j hj => mul_nonneg hr (mul_nonneg (pow_nonneg ha _) (hp _))
      rintro ⟨k, c⟩ hd
      simp only [Set.mem_toFinset, mem_Ico, mem_sigma, Set.mem_setOf_eq] at hd 
      simp only [mem_comp_partial_sum_target_iff]
      refine' ⟨hd.2, c.length_le.trans_lt hd.1.2, fun j => _⟩
      have : c ≠ Composition.single k (zero_lt_two.trans_le hd.1.1) := by
        simp [Composition.eq_single_iff_length, ne_of_gt hd.2]
      rw [Composition.ne_single_iff] at this 
      exact (this j).trans_le (nat.lt_succ_iff.mp hd.1.2)
    _ = ∑ e in compPartialSumSource 2 (n + 1) n, ∏ j : Fin e.1, r * (a ^ e.2 j * p (e.2 j)) :=
      by
      symm
      apply comp_change_of_variables_sum
      rintro ⟨k, blocks_fun⟩ H
      have K : (comp_change_of_variables 2 (n + 1) n ⟨k, blocks_fun⟩ H).snd.length = k := by simp
      congr 2 <;> try rw [K]
      rw [Fin.heq_fun_iff K.symm]
      intro j
      rw [comp_change_of_variables_blocks_fun]
    _ = ∑ j in Ico 2 (n + 1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j :=
      by
      rw [comp_partial_sum_source, ←
        sum_sigma' (Ico 2 (n + 1))
          (fun k : ℕ => (Fintype.piFinset fun i : Fin k => Ico 1 n : Finset (Fin k → ℕ))) fun n e =>
          ∏ j : Fin n, r * (a ^ e j * p (e j))]
      apply sum_congr rfl fun j hj => _
      simp only [← @MultilinearMap.mkPiAlgebra_apply ℝ (Fin j) _ ℝ]
      simp only [←
        MultilinearMap.map_sum_finset (MultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ) fun k (m : ℕ) =>
          r * (a ^ m * p m)]
      simp only [MultilinearMap.mkPiAlgebra_apply]
      dsimp
      simp [prod_const, ← mul_sum, mul_pow]
#align formal_multilinear_series.radius_right_inv_pos_of_radius_pos_aux1 FormalMultilinearSeries.radius_right_inv_pos_of_radius_pos_aux1

/-- Second technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in the specific setup we are interesting in, by reducing to the general bound in
`radius_right_inv_pos_of_radius_pos_aux1`. -/
theorem radius_rightInv_pos_of_radius_pos_aux2 {n : ℕ} (hn : 2 ≤ n + 1)
    (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) {r a C : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hp : ∀ n, ‖p n‖ ≤ C * r ^ n) :
    ∑ k in Ico 1 (n + 1), a ^ k * ‖p.right_inv i k‖ ≤
      ‖(i.symm : F →L[𝕜] E)‖ * a +
        ‖(i.symm : F →L[𝕜] E)‖ * C *
          ∑ k in Ico 2 (n + 1), (r * ∑ j in Ico 1 n, a ^ j * ‖p.right_inv i j‖) ^ k :=
  let I := ‖(i.symm : F →L[𝕜] E)‖
  calc
    ∑ k in Ico 1 (n + 1), a ^ k * ‖p.right_inv i k‖ =
        a * I + ∑ k in Ico 2 (n + 1), a ^ k * ‖p.right_inv i k‖ :=
      by
      simp only [LinearIsometryEquiv.norm_map, pow_one, right_inv_coeff_one, Nat.Ico_succ_singleton,
        sum_singleton, ← sum_Ico_consecutive _ one_le_two hn]
    _ =
        a * I +
          ∑ k in Ico 2 (n + 1),
            a ^ k *
              ‖(i.symm : F →L[𝕜] E).compContinuousMultilinearMap
                  (∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                    p.compAlongComposition (p.right_inv i) c)‖ :=
      by
      congr 1
      apply sum_congr rfl fun j hj => _
      rw [right_inv_coeff _ _ _ (mem_Ico.1 hj).1, norm_neg]
    _ ≤
        a * ‖(i.symm : F →L[𝕜] E)‖ +
          ∑ k in Ico 2 (n + 1),
            a ^ k *
              (I *
                ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                  C * r ^ c.length * ∏ j, ‖p.right_inv i (c.blocksFun j)‖) :=
      by
      apply_rules [add_le_add, le_refl, sum_le_sum fun j hj => _, mul_le_mul_of_nonneg_left,
        pow_nonneg, ha]
      apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (norm_sum_le _ _).trans
      apply sum_le_sum fun c hc => _
      apply (comp_along_composition_norm _ _ _).trans
      apply mul_le_mul_of_nonneg_right (hp _)
      exact prod_nonneg fun j hj => norm_nonneg _
    _ =
        I * a +
          I * C *
            ∑ k in Ico 2 (n + 1),
              a ^ k *
                ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                  r ^ c.length * ∏ j, ‖p.right_inv i (c.blocksFun j)‖ :=
      by
      simp_rw [mul_assoc C, ← mul_sum, ← mul_assoc, mul_comm _ ‖↑i.symm‖, mul_assoc, ← mul_sum, ←
        mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum]
      ring
    _ ≤ I * a + I * C * ∑ k in Ico 2 (n + 1), (r * ∑ j in Ico 1 n, a ^ j * ‖p.right_inv i j‖) ^ k :=
      by
      apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, norm_nonneg, hC, mul_nonneg]
      simp_rw [mul_pow]
      apply
        radius_right_inv_pos_of_radius_pos_aux1 n (fun k => ‖p.right_inv i k‖)
          (fun k => norm_nonneg _) hr ha
#align formal_multilinear_series.radius_right_inv_pos_of_radius_pos_aux2 FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos_aux2

/-- If a a formal multilinear series has a positive radius of convergence, then its right inverse
also has a positive radius of convergence. -/
theorem radius_rightInv_pos_of_radius_pos (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
    (hp : 0 < p.radius) : 0 < (p.right_inv i).radius :=
  by
  obtain ⟨C, r, Cpos, rpos, ple⟩ :
    ∃ (C r : _) (hC : 0 < C) (hr : 0 < r), ∀ n : ℕ, ‖p n‖ ≤ C * r ^ n :=
    le_mul_pow_of_radius_pos p hp
  let I := ‖(i.symm : F →L[𝕜] E)‖
  -- choose `a` small enough to make sure that `∑_{k ≤ n} aᵏ Qₖ` will be controllable by
  -- induction
  obtain ⟨a, apos, ha1, ha2⟩ :
    ∃ (a : _) (apos : 0 < a), 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a ≤ 1 ∧ r * (I + 1) * a ≤ 1 / 2 :=
    by
    have :
      tendsto (fun a => 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) (𝓝 0)
        (𝓝 (2 * I * C * r ^ 2 * (I + 1) ^ 2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have A : ∀ᶠ a in 𝓝 0, 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a < 1 := by
      apply (tendsto_order.1 this).2; simp [zero_lt_one]
    have : tendsto (fun a => r * (I + 1) * a) (𝓝 0) (𝓝 (r * (I + 1) * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have B : ∀ᶠ a in 𝓝 0, r * (I + 1) * a < 1 / 2 := by apply (tendsto_order.1 this).2;
      simp [zero_lt_one]
    have C : ∀ᶠ a in 𝓝[>] (0 : ℝ), (0 : ℝ) < a := by
      filter_upwards [self_mem_nhdsWithin] with _ ha using ha
    rcases(C.and ((A.and B).filter_mono inf_le_left)).exists with ⟨a, ha⟩
    exact ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩
  -- check by induction that the partial sums are suitably bounded, using the choice of `a` and the
  -- inductive control from Lemma `radius_right_inv_pos_of_radius_pos_aux2`.
  let S n := ∑ k in Ico 1 n, a ^ k * ‖p.right_inv i k‖
  have IRec : ∀ n, 1 ≤ n → S n ≤ (I + 1) * a :=
    by
    apply Nat.le_induction
    · simp only [S]
      rw [Ico_eq_empty_of_le (le_refl 1), sum_empty]
      exact mul_nonneg (add_nonneg (norm_nonneg _) zero_le_one) apos.le
    · intro n one_le_n hn
      have In : 2 ≤ n + 1 := by linarith
      have Snonneg : 0 ≤ S n :=
        sum_nonneg fun x hx => mul_nonneg (pow_nonneg apos.le _) (norm_nonneg _)
      have rSn : r * S n ≤ 1 / 2 :=
        calc
          r * S n ≤ r * ((I + 1) * a) := mul_le_mul_of_nonneg_left hn rpos.le
          _ ≤ 1 / 2 := by rwa [← mul_assoc]
      calc
        S (n + 1) ≤ I * a + I * C * ∑ k in Ico 2 (n + 1), (r * S n) ^ k :=
          radius_right_inv_pos_of_radius_pos_aux2 In p i rpos.le apos.le Cpos.le ple
        _ = I * a + I * C * (((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n)) := by
          rw [geom_sum_Ico' _ In]; exact ne_of_lt (rSn.trans_lt (by norm_num))
        _ ≤ I * a + I * C * ((r * S n) ^ 2 / (1 / 2)) :=
          by
          apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, mul_nonneg, norm_nonneg,
            Cpos.le]
          refine' div_le_div (sq_nonneg _) _ (by norm_num) (by linarith)
          simp only [sub_le_self_iff]
          apply pow_nonneg (mul_nonneg rpos.le Snonneg)
        _ = I * a + 2 * I * C * (r * S n) ^ 2 := by ring
        _ ≤ I * a + 2 * I * C * (r * ((I + 1) * a)) ^ 2 := by
          apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, mul_nonneg, norm_nonneg,
            Cpos.le, zero_le_two, pow_le_pow_of_le_left, rpos.le]
        _ = (I + 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) * a := by ring
        _ ≤ (I + 1) * a := by apply_rules [mul_le_mul_of_nonneg_right, apos.le, add_le_add, le_refl]
  -- conclude that all coefficients satisfy `aⁿ Qₙ ≤ (I + 1) a`.
  let a' : NNReal := ⟨a, apos.le⟩
  suffices H : (a' : ENNReal) ≤ (p.right_inv i).radius
  · apply lt_of_lt_of_le _ H; exact_mod_cast apos
  apply le_radius_of_bound _ ((I + 1) * a) fun n => _
  by_cases hn : n = 0
  · have : ‖p.right_inv i n‖ = ‖p.right_inv i 0‖ := by congr <;> try rw [hn]
    simp only [this, norm_zero, MulZeroClass.zero_mul, right_inv_coeff_zero]
    apply_rules [mul_nonneg, add_nonneg, norm_nonneg, zero_le_one, apos.le]
  · have one_le_n : 1 ≤ n := bot_lt_iff_ne_bot.2 hn
    calc
      ‖p.right_inv i n‖ * ↑a' ^ n = a ^ n * ‖p.right_inv i n‖ := mul_comm _ _
      _ ≤ ∑ k in Ico 1 (n + 1), a ^ k * ‖p.right_inv i k‖ :=
        (haveI : ∀ k ∈ Ico 1 (n + 1), 0 ≤ a ^ k * ‖p.right_inv i k‖ := fun k hk =>
          mul_nonneg (pow_nonneg apos.le _) (norm_nonneg _)
        single_le_sum this (by simp [one_le_n]))
      _ ≤ (I + 1) * a := IRec (n + 1) (by decide)
#align formal_multilinear_series.radius_right_inv_pos_of_radius_pos FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos

end FormalMultilinearSeries

