/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
public import Mathlib.Analysis.Calculus.VectorField

/-!
# Evaluation of the derivative of differential forms on vector fields

In this file we prove the following formula and its corollaries.
If `ω` is a differentiable `k`-form and `V i` are `k + 1` differentiable vector fields, then

$$
  dω(V_0(x), \dots, V_n(x)) = \sum_{i=0}^k (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_k(x)\big)\right)(V_i(x)) +
    \sum_{0 \le i < j\le k} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x), V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big),
$$
where $[V_i, V_j]$ is the commutator of the vector fields $V_i$ and $V_j$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

There is no convenient way to write the second term in Lean for `k = 0`,
so we only state this theorem for `k = n + 1`,
see `extDerivWithin_apply_vectorField` and `extDeriv_apply_vectorField`.

In this case, we write the second term as a sum over `i j : Fin (n + 1)`, `i ≤ j`,
where the indexes `(i, j)` in our sum correspond to `(i, j + 1)`
(formally, `(Fin.castSucc i, Fin.succ j)`) in the formula above.
For this reason, we have `-` before the sum in our formal statement.
-/

public section

open Filter ContinuousAlternatingMap Finset VectorField
open scoped Topology

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n m k : ℕ} {r : WithTop ℕ∞}
  {s t : Set E} {x : E}

/--
If `ω` is a differentiable `(n + 1)`-form and `V i` are `n + 2` differentiable vector fields, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)) -
      \sum_{0 \le i \le j\le n} (-1)^{i + j}
        ω\big(x; [V_i, V_{j + 1}](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_{j + 1}(x)}, …, V_k(x)\big),
$$

where $[V_i, V_{j + 1}]$ is the commutator of the vector fields $V_i$ and $V_{j + 1}$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

In informal texts, this formula is usually written as

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)) -
      \sum_{0 \le i < j\le n + 1} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big).
$$

In the sum from our formalization,
each index `(i, j)` corresponds to the index `(Fin.castSucc i, Fin.succ j)`
in the sum used in informal texts.

For this reason, `i + j` in our sum has the opposite parity compared to informal texts,
which changes the sign before the sum from `+` to `-`.
-/
theorem extDerivWithin_apply_vectorField
    {ω : E → E [⋀^Fin (n + 1)]→L[𝕜] F} {V : Fin (n + 2) → E → E}
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hV : ∀ i, DifferentiableWithinAt 𝕜 (V i) s x)
    (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin ω s x (V · x) =
      (∑ i, (-1) ^ i.val • fderivWithin 𝕜 (fun x ↦ ω x (i.removeNth (V · x))) s x (V i x)) -
        ∑ i : Fin (n + 1), ∑ j ≥ i,
          (-1) ^ (i + j : ℕ) •
            ω x (Matrix.vecCons (lieBracketWithin 𝕜 (V i.castSucc) (V j.succ) s x)
              (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  have H₀ (i : Fin (n + 2)) (j : Fin (n + 1)) :
      DifferentiableWithinAt 𝕜 (fun y ↦ i.removeNth (V · y) j) s x := hV ..
  symm
  simp only [extDerivWithin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply,
    fderivWithin_continuousAlternatingMap_apply_apply hω (H₀ _) hsx, *,
    smul_add, sum_add_distrib, add_sub_assoc, add_eq_left, sub_eq_zero, smul_sum]
  rw [Fin.sum_sum_eq_sum_triangle_add]
  refine Fintype.sum_congr _ _ fun i ↦ sum_congr rfl fun j hj ↦ ?_
  rw [mem_Ici] at hj
  simp only [← Fin.insertNth_removeNth, map_insertNth]
  rw [Fin.removeNth_removeNth_eq_swap]
  have H₁ : i.castSucc.succAbove j = j.succ := by simp [Fin.succAbove_of_le_castSucc, hj]
  have H₂ : j.predAbove i.castSucc = i := by simp [Fin.predAbove_of_le_castSucc, hj]
  have H₃ : j.succ.succAbove i = i.castSucc := by simp [Fin.succAbove_of_castSucc_lt, hj]
  simp +unfoldPartialApp [pow_add, lieBracketWithin, mul_smul, smul_comm ((-1) ^ (j : ℕ)), smul_sub,
      ← sub_eq_add_neg, H₁, H₂, H₃, Fin.removeNth]

/--
If `ω` is a differentiable `(n + 1)`-form and `V i` are `n + 2` differentiable vector fields, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)) -
      \sum_{0 \le i \le j\le n} (-1)^{i + j}
        ω\big(x; [V_i, V_{j + 1}](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_{j + 1}(x)}, …, V_k(x)\big),
$$

where $[V_i, V_{j + 1}]$ is the commutator of the vector fields $V_i$ and $V_{j + 1}$.
As usual, $\widehat{V_i(x)}$ means that this item is removed from the sequence.

In informal texts, this formula is usually written as

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) =
    \sum_{i=0}^{n + 1} (-1)^i •
      D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)) -
      \sum_{0 \le i < j\le n + 1} (-1)^{i + j}
        ω\big(x; [V_i, V_j](x),
          V_0(x), …, \widehat{V_i(x)}, …, \widehat{V_j(x)}, …, V_k(x)\big).
$$

In the sum from our formalization,
each index `(i, j)` corresponds to the index `(Fin.castSucc i, Fin.succ j)`
in the sum used in informal texts.

For this reason, `i + j` in our sum has the opposite parity compared to informal texts,
which changes the sign before the sum from `+` to `-`.
-/
theorem extDeriv_apply_vectorField {ω : E → E [⋀^Fin (n + 1)]→L[𝕜] F} {V : Fin (n + 2) → E → E}
    (hω : DifferentiableAt 𝕜 ω x) (hV : ∀ i, DifferentiableAt 𝕜 (V i) x) :
    extDeriv ω x (V · x) =
      (∑ i, (-1) ^ i.val • fderiv 𝕜 (fun x ↦ ω x (i.removeNth (V · x))) x (V i x)) -
        ∑ i : Fin (n + 1), ∑ j ≥ i,
          (-1) ^ (i + j : ℕ) •
            ω x (Matrix.vecCons (lieBracket 𝕜 (V i.castSucc) (V j.succ) x)
              (j.removeNth <| i.castSucc.removeNth (V · x))) := by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← fderivWithin_univ,
    ← lieBracketWithin_univ] at *
  exact extDerivWithin_apply_vectorField hω hV (by simp)

/-- Let `ω` be a differentiable `n`-form and `V i` be `n + 1` differentiable vector fields.
If `V i` pairwise commute at `x`, i.e., $[V_i, V_j](x) = 0$ for all `i ≠ j`, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) = \sum_{i=0}^{n + 1} (-1)^i •
    D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)).
$$
-/
theorem extDerivWithin_apply_vectorField_of_pairwise_commute
    {ω : E → E [⋀^Fin n]→L[𝕜] F} {V : Fin (n + 1) → E → E}
    (hω : DifferentiableWithinAt 𝕜 ω s x) (hV : ∀ i, DifferentiableWithinAt 𝕜 (V i) s x)
    (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hcomm : Pairwise fun i j ↦ lieBracketWithin 𝕜 (V i) (V j) s x = 0) :
    extDerivWithin ω s x (V · x) =
      (∑ i, (-1) ^ i.val • fderivWithin 𝕜 (fun x ↦ ω x (i.removeNth (V · x))) s x (V i x)) := by
  cases n with
  | zero =>
    simp [extDerivWithin_apply, fderivWithin_continuousAlternatingMap_apply_const_apply,
      fderivWithin_continuousAlternatingMap_apply_apply, *]
  | succ n =>
    rw [extDerivWithin_apply_vectorField hω hV hsx, sub_eq_self]
    refine Fintype.sum_eq_zero _ fun i ↦ sum_eq_zero fun j hj ↦ ?_
    rw [hcomm (ne_of_lt <| by simpa using hj), (ω x).map_coord_zero 0] <;>
      simp

/-- Let `ω` be a differentiable `n`-form and `V i` be `n + 1` differentiable vector fields.
If `V i` pairwise commute at `x`, i.e., $[V_i, V_j](x) = 0$ for all `i ≠ j`, then

$$
  dω(V_0(x), \dots, V_{n + 1}(x)) = \sum_{i=0}^{n + 1} (-1)^i •
    D_x\left(ω\big(x; V_0(x), \dots, \widehat{V_i(x)}, \dots, V_{n + 1}(x)\big)\right)(V_i(x)).
$$
-/
theorem extDeriv_apply_vectorField_of_pairwise_commute
    {ω : E → E [⋀^Fin n]→L[𝕜] F} {V : Fin (n + 1) → E → E}
    (hω : DifferentiableAt 𝕜 ω x) (hV : ∀ i, DifferentiableAt 𝕜 (V i) x)
    (hcomm : Pairwise fun i j ↦ lieBracket 𝕜 (V i) (V j) x = 0) :
    extDeriv ω x (V · x) =
      (∑ i, (-1) ^ i.val • fderiv 𝕜 (fun x ↦ ω x (i.removeNth (V · x))) x (V i x)) := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ, ← extDerivWithin_univ,
    ← fderivWithin_univ] at *
  exact extDerivWithin_apply_vectorField_of_pairwise_commute hω hV (by simp) hcomm
