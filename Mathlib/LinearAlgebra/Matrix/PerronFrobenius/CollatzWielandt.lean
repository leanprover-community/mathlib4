/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
public import Mathlib.LinearAlgebra.Matrix.PerronFrobenius.Aux
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Collatz–Wielandt function for matrices

The Collatz–Wielandt formula and its use to define and bound the Perron root of a non-negative
matrix.

## Main definitions

* `collatzWielandtFn`: minimum positive entry ratio `(Ax)ᵢ / xᵢ`.
* `r_x`, `minRatio`, `maxRatio`: infimum/supremum ratio formulations (Berman & Plemmons).
* `perronRoot`, `perronRoot'`: Collatz–Wielandt sup/inf characterizations of the Perron root.
* `perronRoot_alt`: supremum of `collatzWielandtFn` over non-zero non-negative vectors.
* `r`: supremum of `collatzWielandtFn` over `P_set`.

## Main results

* `upperSemicontinuousOn` and `exists_maximizer`: the Collatz–Wielandt function attains its
  maximum on the standard simplex, via `UpperSemicontinuousOn.exists_isMaxOn`.
* `eq_perron_root_of_positive_eigenvector`: a positive eigenpair determines the Perron root.
* `le_of_subinvariant`: sub-invariance yields a Collatz–Wielandt lower bound.

## Implementation notes

Seneta uses row vectors; this development uses column vectors and `Matrix.mulVec`.

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

Collatz–Wielandt, Perron root, non-negative matrix
-/

@[expose] public section

namespace Matrix

section PerronFrobenius
open scoped Classical
variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

open LinearMap Set Filter Topology Finset IsCompact Quiver Matrix

open scoped Convex Pointwise

/-- The Collatz-Wielandt function, `r(x)` in Seneta's notation.
For a non-zero, non-negative vector `x`, this is `min_{i | xᵢ > 0} (Ax)ᵢ / xᵢ`.
Seneta uses row vectors `x'T`; we use column vectors `Ax`. The logic is identical. -/
noncomputable def collatzWielandtFn (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  let supp := {i | 0 < x i}.toFinset
  if h : supp.Nonempty then
    supp.inf' h fun i ↦ (A *ᵥ x) i / x i
  else 0

/-- The Collatz-Wielandt function `r_x` for a positive vector `x` (Berman & Plemmons, p. 30).
Defined for strictly positive vectors to avoid division by zero. -/
noncomputable def r_x (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  ⨅ i, (A.mulVec x i) / (x i)

noncomputable abbrev mulVec_continuousLinearMap (A : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  (Matrix.mulVecLin A).toContinuousLinearMap

namespace CollatzWielandt

/-- `r_x` is continuous on the set of strictly positive vectors. -/
lemma r_x_continuousOn_pos [Nonempty n] (A : Matrix n n ℝ) :
    ContinuousOn (r_x A) {x : n → ℝ | ∀ i, 0 < x i} := by
  refine continuousOn_iInf (fun i ↦ ContinuousOn.div
    (((continuous_apply i).comp (mulVec_continuousLinearMap A).continuous).continuousOn)
    ((continuous_apply i).continuousOn) (fun x hx ↦ (hx i).ne.symm))

/-- *The Collatz-Wielandt function is upper-semicontinuous*.
Seneta relies on this fact (p.15, Appendix C) to use the Extreme Value Theorem.
`r(x)` is a minimum of functions `fᵢ(x) = (Ax)ᵢ / xᵢ`. Each `fᵢ` is continuous where `xᵢ > 0`.
The minimum of continuous functions is upper-semicontinuous.
[Giaquinta-Modica, Definition 6.21, Exercise 6.28, pp: 235, 236] -/
theorem upperSemicontinuousOn [Nonempty n] (A : Matrix n n ℝ) :
    UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) := by
  have Hsup_nonempt : ∀ x ∈ stdSimplex ℝ n, ({i | 0 < x i}.toFinset).Nonempty := by
    intro x hx
    obtain ⟨i, hi_pos⟩ := exists_pos_of_sum_one_of_nonneg hx.2 hx.1
    refine ⟨i, by grind⟩
  intro x₀ hx₀ c hc
  have fn_eq : collatzWielandtFn A x₀ =
      {i | 0 < x₀ i}.toFinset.inf' (Hsup_nonempt x₀ hx₀) (fun i ↦ (A *ᵥ x₀) i / x₀ i) := by
    rw [collatzWielandtFn, dif_pos (Hsup_nonempt x₀ hx₀)]
  let U := {y : n → ℝ | ∀ i ∈ {i | 0 < x₀ i}.toFinset, 0 < y i}
  have U_open : IsOpen U := by
    have h_eq : U = ⋂ i ∈ {i | 0 < x₀ i}.toFinset, {y | 0 < y i} := by aesop
    rw [h_eq]
    apply isOpen_biInter_finset
    intro i _
    exact isOpen_lt continuous_const (continuous_apply i)
  let f := fun y ↦ {i | 0 < x₀ i}.toFinset.inf' (Hsup_nonempt x₀ hx₀) fun i ↦ (A *ᵥ y) i / y i
  have f_cont : ContinuousOn f U := by
    refine continuousOn_finset_inf' (Hsup_nonempt x₀ hx₀) (fun i hi ↦ ?_)
    refine (ContinuousOn.div ?_ (continuous_apply i).continuousOn fun y hy ↦ ne_of_gt (hy i hi))
    · simpa using
        ((continuous_apply i).comp (mulVec_continuousLinearMap A).continuous).continuousOn
  have f_ge : ∀ y ∈ U ∩ stdSimplex ℝ n, collatzWielandtFn A y ≤ f y := by
    intro y hy
    have fn_y : collatzWielandtFn A y =
        {i | 0 < y i}.toFinset.inf' (Hsup_nonempt y hy.2) fun i ↦ (A *ᵥ y) i / y i := by
      rw [collatzWielandtFn, dif_pos (Hsup_nonempt y hy.2)]
    have supp_subset : {i | 0 < x₀ i}.toFinset ⊆ {i | 0 < y i}.toFinset := by grind
    rw [fn_y]
    apply finset_inf'_mono_subset supp_subset
  rw [fn_eq] at hc
  have cont_at : ContinuousAt f x₀ := f_cont.continuousAt (IsOpen.mem_nhds U_open (by grind))
  have lt_eventually : ∀ᶠ y in 𝓝 x₀, f y < c := Filter.Tendsto.eventually_lt_const hc cont_at
  obtain ⟨V, V_open, x₀_in_V, hV⟩ := eventually_to_open lt_eventually
  let W := V ∩ U ∩ stdSimplex ℝ n
  have VU_nhds : V ∩ U ∈ 𝓝 x₀ := (IsOpen.inter V_open U_open).mem_nhds (⟨x₀_in_V, by grind⟩)
  have W_nhdsWithin : W ∈ 𝓝[stdSimplex ℝ n] x₀ :=
    (mem_nhdsWithin_iff_exists_mem_nhds_inter).2 <| ⟨V ∩ U, VU_nhds, by simp [W]⟩
  have h_final : ∀ y ∈ W, collatzWielandtFn A y < c := by
    rintro y ⟨⟨hyV, hyU⟩, hyS⟩
    exact lt_of_le_of_lt (f_ge y ⟨hyU, hyS⟩) (hV y hyV)
  exact Filter.mem_of_superset W_nhdsWithin (fun y hy ↦ h_final y hy)

-- The set of vectors we are optimizing over.
def P_set := {x : n → ℝ | (∀ i, 0 ≤ x i) ∧ x ≠ 0}

/-- Supremum of `collatzWielandtFn` over non-zero non-negative vectors. -/
noncomputable def r (A : Matrix n n ℝ) [Fintype n] := ⨆ x ∈ P_set, collatzWielandtFn A x

/-- The Collatz-Wielandt function attains its maximum on the standard simplex.
    [Giaquinta-Modica, Theorem 6.24 (dual), p: 235] -/
theorem exists_maximizer [Nonempty n] (A : Matrix n n ℝ) :
    ∃ v ∈ stdSimplex ℝ n, IsMaxOn (collatzWielandtFn A) (stdSimplex ℝ n) v :=
  (upperSemicontinuousOn A).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary n)⟩ (isCompact_stdSimplex ℝ n)

lemma eq_iInf_of_nonempty (A : Matrix n n ℝ) (v : n → ℝ) (h : {i | 0 < v i}.toFinset.Nonempty) :
    collatzWielandtFn A v = ⨅ i : {i | 0 < v i}, (A *ᵥ v) i / v i := by
  rw [collatzWielandtFn, dif_pos h, inf'_eq_ciInf h]
  refine Function.Surjective.iInf_congr (by aesop) (fun b ↦ by aesop) (by simp)

/-- If r ≤ 0 and r is the infimum of non-negative ratios, then r = 0. -/
lemma val_eq_zero_of_nonpos (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (S : Set n) (hS_def : S = {i | 0 < v i})
    (hS_nonempty : S.Nonempty) (r : ℝ) (hr_def : r = collatzWielandtFn A v) (hr_nonpos : r ≤ 0) :
    r = 0 := by
  refine le_antisymm hr_nonpos ?_
  rw [hr_def, collatzWielandtFn, dif_pos (by rwa [Set.toFinset_nonempty_iff, ← hS_def])]
  apply le_inf'
  intro j hj
  rw [Set.mem_toFinset] at hj
  exact div_nonneg (mulVec_nonneg hA_nonneg hv_nonneg j) hj.le

/-- Each ratio is at least the Collatz–Wielandt value. -/
lemma le_ratio (_ : ∀ i j, 0 ≤ A i j) {v : n → ℝ} (_ : ∀ i, 0 ≤ v i)
    (S : Set n) (hS_def : S = {i | 0 < v i}) (_ : S.Nonempty)
    (i : n) (_ : i ∈ S) : collatzWielandtFn A v ≤ (A *ᵥ v) i / v i := by
  rw [collatzWielandtFn, dif_pos (by rwa [Set.toFinset_nonempty_iff, ← hS_def])]
  exact inf'_le _ (by rwa [Set.mem_toFinset, ← hS_def])

/-- For any non-negative, non-zero vector `v`, the Collatz-Wielandt value `r` satisfies
    `r • v ≤ A *ᵥ v`. This is the fundamental inequality derived from the definition of
    the Collatz-Wielandt function. -/
lemma le_mulVec (hA_nonneg : ∀ i j, 0 ≤ A i j) {v : n → ℝ}
    (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne_zero : v ≠ 0) :
    (collatzWielandtFn A v) • v ≤ A *ᵥ v := by
  let r := collatzWielandtFn A v
  have hS_nonempty : ({i | 0 < v i}).Nonempty := exists_pos_of_ne_zero hv_nonneg hv_ne_zero
  intro i
  by_cases hi_supp : v i > 0
  · have h_le_div : r ≤ (A *ᵥ v) i / v i :=
      le_ratio hA_nonneg hv_nonneg {i | 0 < v i} rfl hS_nonempty i hi_supp
    exact (le_div_iff₀ hi_supp).mp h_le_div
  · have h_vi_zero : v i = 0 := by linarith [hv_nonneg i, not_lt.mp hi_supp]
    simp only [Pi.smul_apply, smul_eq_mul, h_vi_zero, mul_zero]
    exact mulVec_nonneg hA_nonneg hv_nonneg i

/-- If the Collatz-Wielandt value `r` is non-positive, there must be some `i` in the support of `v`
    where the ratio, and thus `(A * v) i`, is zero. -/
lemma exists_mulVec_eq_zero_on_support_of_nonpos (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {v : n → ℝ} (hv_nonneg : ∀ i, 0 ≤ v i) (h_supp_nonempty : {i | 0 < v i}.toFinset.Nonempty)
    (h_r_nonpos : collatzWielandtFn A v ≤ 0) : ∃ i ∈ {i | 0 < v i}.toFinset, (A *ᵥ v) i = 0 := by
  have r_nonneg : 0 ≤ collatzWielandtFn A v := by
    rw [collatzWielandtFn, dif_pos h_supp_nonempty]
    apply le_inf'
    intro i hi
    exact div_nonneg (mulVec_nonneg hA_nonneg hv_nonneg i) (le_of_lt <| by simpa using hi)
  have r_eq_zero : collatzWielandtFn A v = 0 := le_antisymm h_r_nonpos r_nonneg
  rw [collatzWielandtFn, dif_pos h_supp_nonempty] at r_eq_zero
  obtain ⟨b, hb_mem, hb_eq⟩ := exists_mem_eq_inf' h_supp_nonempty fun i => (A *ᵥ v) i / v i
  grind

lemma le_any_ratio (A : Matrix n n ℝ) {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_ne_zero : x ≠ 0) (i : n) (hi_pos : 0 < x i) :
    collatzWielandtFn A x ≤ (A *ᵥ x) i / x i := by
  dsimp [collatzWielandtFn]
  have h_supp_nonempty : ({k | 0 < x k}.toFinset).Nonempty := by
    obtain ⟨j, hj⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne_zero
    exact ⟨j, Set.mem_toFinset.mpr hj⟩
  rw [dif_pos h_supp_nonempty]
  apply inf'_le
  rw [Set.mem_toFinset]
  exact hi_pos

/-- The set of values from the Collatz-Wielandt function is bounded above by the maximum row sum of A. -/
lemma bddAbove [Nonempty n] (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    BddAbove (collatzWielandtFn A '' {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}) := by
  use univ.sup' univ_nonempty (fun i ↦ ∑ j, A i j)
  rintro y ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
  obtain ⟨m, _, h_max_eq⟩ := exists_mem_eq_sup' univ_nonempty x
  have h_xm_pos : 0 < x m := by
    obtain ⟨j, hj⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne_zero
    rw [← h_max_eq]
    exact lt_of_lt_of_le hj (le_sup' x (mem_univ j))
  have h_ratio_le : (A *ᵥ x) m / x m ≤ univ.sup' univ_nonempty (fun k ↦ ∑ l, A k l) := by
    rw [mulVec_apply, div_le_iff h_xm_pos]
    calc _ ≤ ∑ j, A m j * x m := ?_
         _ = (∑ j, A m j) * x m := ?_
         _ ≤ (univ.sup' univ_nonempty (fun k ↦ ∑ l, A k l)) * x m := ?_
    · apply sum_le_sum; intro j _
      exact mul_le_mul_of_nonneg_left
        (by rw [← h_max_eq]; exact le_sup' x (mem_univ j)) (hA_nonneg m j)
    · rw [sum_mul]
    · apply mul_le_mul_of_nonneg_right
        (le_sup' (fun k ↦ ∑ l, A k l) (mem_univ m)) (le_of_lt h_xm_pos)
  exact le_trans (le_any_ratio A hx_nonneg hx_ne_zero m h_xm_pos) h_ratio_le

/-- The set of values from the Collatz-Wielandt function is non-empty. -/
lemma set_nonempty [Nonempty n] : (collatzWielandtFn A '' {x | (∀ i, 0 ≤ x i) ∧ x ≠ 0}).Nonempty := by
  let P_set := {x : n → ℝ | (∀ i, 0 ≤ x i) ∧ x ≠ 0}
  let x_ones : n → ℝ := fun _ ↦ 1
  have h_x_ones_in_set : x_ones ∈ P_set := by
    refine ⟨fun i ↦ by aesop, fun h_zero ↦ ?_⟩
    · have h_contra : (1 : ℝ) = 0 := by
        have := congrArg (fun f ↦ f (Classical.arbitrary n)) h_zero
        simp [x_ones] at this
      exact one_ne_zero h_contra
  exact ⟨collatzWielandtFn A x_ones, ⟨x_ones, h_x_ones_in_set, rfl⟩⟩

lemma smul [Nonempty n] {c : ℝ} (hc : 0 < c) (_ : ∀ i j, 0 ≤ A i j)
    {x : n → ℝ} (hx_nonneg : ∀ i, 0 ≤ x i) (hx_ne : x ≠ 0) :
    collatzWielandtFn A (c • x) = collatzWielandtFn A x := by
  dsimp [collatzWielandtFn]
  let S := {i | 0 < x i}.toFinset
  obtain ⟨i₀, hi₀⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne
  have hS_nonempty : S.Nonempty := ⟨i₀, by simp [S, hi₀]⟩
  have h_supp_eq : {i | 0 < (c • x) i}.toFinset = S := by
    ext i
    simp [S, smul_eq_mul, mul_pos_iff_of_pos_left hc]
  rw [dif_pos (h_supp_eq.symm ▸ hS_nonempty), dif_pos hS_nonempty]
  refine inf'_congr (Eq.symm h_supp_eq ▸ hS_nonempty) h_supp_eq ?_
  intro i hi
  simp only [mulVec_smul, smul_eq_mul, Pi.smul_apply]
  rw [mul_div_mul_left _ _ (ne_of_gt hc)]

/-- Minimum ratio `(Ax)_i / x_i` for a positive vector `x`. -/
noncomputable def minRatio (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  ⨅ i, (A.mulVec x i) / x i

/-- Maximum ratio `(Ax)_i / x_i` for a positive vector `x`. -/
noncomputable def maxRatio (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  ⨆ i, (A.mulVec x i) / x i

/-- Collatz–Wielandt Perron root as a supremum of infima over positive vectors. -/
noncomputable def perronRoot (A : Matrix n n ℝ) : ℝ :=
  ⨆ (x : n → ℝ) (_ : ∀ i, 0 < x i), minRatio A x

/-- Collatz–Wielandt Perron root as an infimum of suprema over positive vectors. -/
noncomputable def perronRoot' (A : Matrix n n ℝ) : ℝ :=
  ⨅ (x : n → ℝ) (_ : ∀ i, 0 < x i), maxRatio A x

/-- The Perron root, as the supremum of the Collatz-Wielandt function (see Seneta). -/
noncomputable def perronRoot_alt (A : Matrix n n ℝ) : ℝ :=
  sSup (collatzWielandtFn A '' P_set)

lemma minRatio_le_maxRatio (A : Matrix n n ℝ) (x : n → ℝ) :
    minRatio A x ≤ maxRatio A x := by
  cases isEmpty_or_nonempty n with
  | inl h =>
    simp [minRatio, maxRatio]
  | inr h =>
    simpa [minRatio, maxRatio] using
      (ciInf_le_ciSup (f := fun i : n ↦ (A.mulVec x i) / x i)
        (Set.finite_range _).bddBelow (Set.finite_range _).bddAbove)

lemma min_max_sets_nonempty [Nonempty n] (A : Matrix n n ℝ) :
    ({r | ∃ x : n → ℝ, (∀ i, 0 < x i) ∧ r = minRatio A x}.Nonempty) ∧
      ({r | ∃ x : n → ℝ, (∀ i, 0 < x i) ∧ r = maxRatio A x}.Nonempty) := by
  refine ⟨?_, ?_⟩ <;>
    refine ⟨_, ⟨fun _ => (1 : ℝ), ⟨?_, rfl⟩⟩⟩ <;>
    intro i <;> simp

lemma forall_exists_min_le_max [Nonempty n] (A : Matrix n n ℝ) :
    ∀ r ∈ {r | ∃ x : n → ℝ, (∀ i, 0 < x i) ∧ r = minRatio A x},
      ∃ s ∈ {s | ∃ y : n → ℝ, (∀ i, 0 < y i) ∧ s = maxRatio A y}, r ≤ s := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨maxRatio A x, ⟨x, hx, rfl⟩, minRatio_le_maxRatio A x⟩

theorem eq_eigenvalue_of_positive_eigenvector [Nonempty n] {A : Matrix n n ℝ}
    {r : ℝ} {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    collatzWielandtFn A v = r := by
  have h_supp_nonempty : ({i | 0 < v i}.toFinset).Nonempty := by aesop
  rw [collatzWielandtFn, dif_pos h_supp_nonempty]
  apply inf'_eq_of_forall_le_of_exists_le h_supp_nonempty
  · intro i _
    have hratio : (A *ᵥ v) i / v i = r := by
      simpa [Pi.smul_apply, smul_eq_mul, (hv_pos i).ne'] using
        congrArg (fun t => t i / v i) h_eig
    simp [hratio]
  · refine ⟨h_supp_nonempty.choose, ⟨h_supp_nonempty.choose_spec, ?_⟩⟩
    have : (A *ᵥ v) h_supp_nonempty.choose =
      (r • v) h_supp_nonempty.choose := by rw [h_eig]
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [this, mul_div_cancel_pos_right rfl (hv_pos (Exists.choose h_supp_nonempty))]

lemma bddAbove_image_P_set [Nonempty n] (A : Matrix n n ℝ)
    (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    BddAbove (collatzWielandtFn A '' P_set) :=
  bddAbove (A := A) hA_nonneg

/-- Any eigenvalue with a strictly positive eigenvector is ≤ the Perron root. -/

theorem eigenvalue_le_perron_root_of_positive_eigenvector [Nonempty n] {r : ℝ} {v : n → ℝ}
    (hA_nonneg : ∀ i j, 0 ≤ A i j) (_ : 0 < r) (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    r ≤ perronRoot_alt A := by
  have h_le : collatzWielandtFn A v ≤ perronRoot_alt A :=
    le_csSup (bddAbove_image_P_set A hA_nonneg) (Set.mem_image_of_mem _
      ⟨fun i ↦ (hv_pos i).le, fun h ↦ (hv_pos (Classical.arbitrary n)).ne' (congr_fun h _)⟩)
  rw [← (eq_eigenvalue_of_positive_eigenvector hv_pos h_eig).symm] at h_le
  exact h_le

/-- A left eigenvector of the matrix is a right eigenvector of its transpose -/
lemma left_eigenvector_of_transpose {r : ℝ} {u : n → ℝ} (hu_left : u ᵥ* A = r • u) :
    Aᵀ *ᵥ u = r • u := by
  rwa [← vecMul_eq_mulVec_transpose]

/-- For a left eigenvector, the Collatz–Wielandt value of any non-negative vector is ≤ the eigenvalue. -/
lemma le_eigenvalue_of_left_eigenvector (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {r : ℝ} (_ : 0 < r) {u : n → ℝ} (hu_pos : ∀ i, 0 < u i) (h_eig : u ᵥ* A = r • u)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0) :
    collatzWielandtFn A w ≤ r := by
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i ↦ (hu_pos i).le
  have h_right : u ⬝ᵥ (A *ᵥ w) = r * (u ⬝ᵥ w) := by
    calc u ⬝ᵥ (A *ᵥ w) = (u ᵥ* A) ⬝ᵥ w := dotProduct_mulVec u A w
         _ = r * (u ⬝ᵥ w) := by simp [h_eig, smul_eq_mul]
  refine le_of_mul_le_mul_right ?_
    (dotProduct_pos_of_pos_of_nonneg_ne_zero hu_pos hw_nonneg hw_ne_zero)
  · have h_intermediate : u ⬝ᵥ ((collatzWielandtFn A w) • w) ≤ u ⬝ᵥ (A *ᵥ w) := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        ((CollatzWielandt.le_mulVec hA_nonneg hw_nonneg hw_ne_zero) i) (hu_nonneg i)
    simpa [dotProduct_smul, smul_eq_mul, h_right] using h_intermediate

/-- If v is an eigenvector of A with eigenvalue r (i.e., A *ᵥ v = r • v),
    this lemma provides the relation in the form needed for rewriting. -/
lemma mulVec_eq_smul_of_eigenvector {n : Type*} [Fintype n]    {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ} (h_eig : A *ᵥ v = r • v) :
    r • v = A *ᵥ v := Eq.symm h_eig

/--
If `u` is a strictly positive left eigenvector of `A` for eigenvalue `r > 0`,
then the Perron root of `A` is less than or equal to `r`.
That is, `perronRoot_alt A ≤ r`.
-/
lemma perron_root_le_eigenvalue_of_left_eigenvector [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (hr_pos : 0 < r) {u : n → ℝ} (hu_pos : ∀ i, 0 < u i)
    (h_eig : u ᵥ* A = r • u) : perronRoot_alt A ≤ r := by
  apply csSup_le (CollatzWielandt.set_nonempty)
  · rintro _ ⟨w, ⟨hw_nonneg, hw_ne_zero⟩, rfl⟩
    exact CollatzWielandt.le_eigenvalue_of_left_eigenvector hA_nonneg hr_pos
      hu_pos h_eig hw_nonneg hw_ne_zero

/--
An intermediate algebraic result for the Perron-Frobenius theorem.
If `v` is a right eigenvector of `A` for eigenvalue `r`, then for any vector `w`,
the dot product `v ⬝ᵥ (A *ᵥ w)` is equal to `r * (v ⬝ᵥ w)`.
-/
lemma dotProduct_mulVec_eq_eigenvalue_mul_dotProduct {r : ℝ} {v w : n → ℝ}
    (h_eig : Aᵀ *ᵥ v = r • v) : v ⬝ᵥ (A *ᵥ w) = r * (v ⬝ᵥ w) := by
  rw [dotProduct_mulVec v A w, vecMul_eq_mulVec_transpose A v, h_eig]
  exact dotProduct_smul_left r v w

/--
If `v` is a strictly positive right eigenvector of `A` with eigenvalue `r`, then the vector
of all ones is a right eigenvector of the similarity-transformed matrix `B = D⁻¹AD`
(where `D` is `diagonal v`) with the same eigenvalue `r`.
-/
lemma ones_eigenvector_of_similarity_transform {r : ℝ} {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    (diagonal (v⁻¹) * A * diagonal v) *ᵥ (fun _ ↦ 1) = fun _ ↦ r := by
  let ones := fun _ : n ↦ (1 : ℝ)
  rw [← mulVec_mulVec, ← mulVec_mulVec, diagonal_mulVec_ones v, h_eig]
  rw [mulVec_smul, diagonal_inv_mulVec_self (fun i ↦ (hv_pos i).ne')]
  aesop

/--
If `v` is a strictly positive right eigenvector of `A` with eigenvalue `r`, then the
similarity-transformed matrix `B = D⁻¹AD` (where `D` is `diagonal v`) has row sums equal to `r`.
-/
lemma row_sum_of_similarity_transformed_matrix [Nonempty n] {A : Matrix n n ℝ}
    {r : ℝ} {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
  ∀ i, ∑ j, (diagonal (v⁻¹) * A * diagonal v) i j = r := fun i ↦ by
  simpa [mulVec_apply, mul_one] using (congrArg (fun f => f i)
    (ones_eigenvector_of_similarity_transform (A := A) hv_pos h_eig))

/--
If a non-negative vector `x` satisfies `c • x ≤ B *ᵥ x` for a non-negative matrix `B`
whose row sums are all equal to `r`, then `c ≤ r`.
-/
lemma le_of_max_le_row_sum [Nonempty n] {B : Matrix n n ℝ} {x : n → ℝ} {c r : ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (h_B_row_sum : ∀ i, ∑ j, B i j = r) (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_ne_zero : x ≠ 0) (h_le_Bx : c • x ≤ B *ᵥ x) :
  c ≤ r := by
  obtain ⟨m, -, hm⟩ := exists_mem_eq_sup' (s := univ) univ_nonempty x
  have hcx : c * x m ≤ (B *ᵥ x) m := by
    simpa [Pi.smul_apply, smul_eq_mul] using (h_le_Bx m)
  have hBx : (B *ᵥ x) m ≤ r * x m := by
    calc (B *ᵥ x) m = ∑ j, B m j * x j := by simp [mulVec_apply]
     _ ≤ ∑ j, B m j * x m := ?_
     _ = (∑ j, B m j) * x m := ?_
     _ = r * x m := ?_
    · refine sum_le_sum (fun j _ => ?_)
      exact mul_le_mul_of_nonneg_left (by
        simpa [hm] using (le_sup' (s := univ) (f := x) (mem_univ j))) (hB_nonneg m j)
    · simp [sum_mul]
    · simp [h_B_row_sum m]
  refine le_of_mul_le_mul_right (hcx.trans hBx) ?_
  · refine (exists_pos_of_ne_zero hx_nonneg hx_ne_zero).elim (fun i hi ↦ lt_of_lt_of_le hi (by
      simpa [hm] using (le_sup' (s := univ) (f := x) (mem_univ i))))
/--
For any non-negative vector `w`, its Collatz–Wielandt value is bounded above by a
positive eigenvalue `r` that has a strictly positive *right* eigenvector `v`.
-/
theorem le_eigenvalue_of_right_eigenvector [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j)
    {r : ℝ} (_ : 0 < r) {v : n → ℝ} (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0) :
    collatzWielandtFn A w ≤ r := by
  let D := Matrix.diagonal v
  let D_inv := Matrix.diagonal (v⁻¹)
  let B := D_inv * A * D
  have hB_nonneg : ∀ i j, 0 ≤ B i j := fun i j ↦ by
    simpa [B, D, D_inv, Matrix.mul_apply, mul_assoc, diagonal, mul_assoc] using
      mul_nonneg (mul_nonneg (inv_nonneg.2 (hv_pos i).le) (hA_nonneg i j)) (hv_pos j).le
  have h_B_row_sum := row_sum_of_similarity_transformed_matrix hv_pos h_eig
  let x := D_inv *ᵥ w
  have hx_ne_zero : x ≠ 0 := by
    intro hx
    apply hw_ne_zero
    have h_w_eq_Dx : w = D *ᵥ x := by
      ext i;simp [x, D, D_inv, mulVec_diagonal, (hv_pos i).ne']
    calc
      w = D *ᵥ x := h_w_eq_Dx
      _ = 0 := by simp [hx]
  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    unfold x D_inv
    rw [mulVec_diagonal]
    exact mul_nonneg (inv_nonneg.mpr (hv_pos i).le) (hw_nonneg i)
  have h_le_Bx : (collatzWielandtFn A w) • x ≤ B *ᵥ x := by
    have h_le_mulVec := CollatzWielandt.le_mulVec hA_nonneg hw_nonneg hw_ne_zero
    have h1 : (collatzWielandtFn A w) • x = D_inv *ᵥ ((collatzWielandtFn A w) • w) := by
      ext i; simp [x, D_inv, mulVec_diagonal, Pi.smul_apply]
      grind
    have h_w_eq_Dx : w = D *ᵥ x := by ext i; simp [x, D, D_inv, mulVec_diagonal, (hv_pos i).ne']
    rw [h1]
    have h_Dinv_nonneg : ∀ i j, 0 ≤ D_inv i j := by
      intro i j
      by_cases h : i = j <;>
      simp [D_inv, h, inv_nonneg, (hv_pos _).le]
    intro i
    have h_mulVec_mono :
      (D_inv *ᵥ ((collatzWielandtFn A w) • w)) i ≤ (D_inv *ᵥ (A *ᵥ w)) i := by
      simpa [mulVec_apply] using (sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (h_le_mulVec j) (h_Dinv_nonneg i j))
    calc _ ≤ (D_inv *ᵥ (A *ᵥ w)) i := h_mulVec_mono
         _ = (D_inv *ᵥ (A *ᵥ (D *ᵥ x))) i := by rw [h_w_eq_Dx]
         _ = ((D_inv * A * D) *ᵥ x) i := by rw [← mulVec_mulVec, ← mulVec_mulVec]
  exact le_of_max_le_row_sum hB_nonneg h_B_row_sum hx_nonneg hx_ne_zero h_le_Bx

/- Any positive eigenvalue `r` with a strictly positive right eigenvector `v` is an
upper bound for the range of the Collatz-Wielandt function.
-/
theorem eigenvalue_is_ub_of_positive_eigenvector [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) {r : ℝ} (hr_pos : 0 < r) {v : n → ℝ}
    (hv_pos : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) : perronRoot_alt A ≤ r := by
  refine csSup_le (CollatzWielandt.set_nonempty (A := A)) (fun y hy ↦ ?_)
  obtain ⟨w, ⟨hw_nonneg, hw_ne_zero⟩, rfl⟩ := hy
  exact (CollatzWielandt.le_eigenvalue_of_right_eigenvector (A := A)
    hA_nonneg hr_pos hv_pos h_eig hw_nonneg hw_ne_zero)

open CollatzWielandt

theorem eq_perron_root_of_positive_eigenvector [Nonempty n] {r : ℝ}
    {v : n → ℝ} (hA_nonneg : ∀ i j, 0 ≤ A i j) (hv_pos : ∀ i, 0 < v i) (hr_pos : 0 < r)
    (h_eig : A *ᵥ v = r • v) : r = CollatzWielandt.perronRoot_alt (A := A) :=
  le_antisymm
    (eigenvalue_le_perron_root_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig)
    (eigenvalue_is_ub_of_positive_eigenvector hA_nonneg hr_pos hv_pos h_eig)

lemma perronRoot'_le_maxRatio_of_min_ge_perronRoot' {x : n → ℝ}
    (hr : perronRoot' A ≤ minRatio A x) : perronRoot' A ≤ maxRatio A x :=
  hr.trans (minRatio_le_maxRatio A x)

lemma maximizer_satisfies_le_mulVec [Nonempty n] (A : Matrix n n ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    let r := perronRoot_alt A
    ∃ v ∈ stdSimplex ℝ n, r • v ≤ A *ᵥ v := by
  let r := perronRoot_alt A
  obtain ⟨v, v_in_simplex, v_is_max⟩ := exists_maximizer (A := A)
  have v_ne_zero : v ≠ 0 := fun hv ↦ by
    refine (zero_ne_one : (0 : ℝ) ≠ (1 : ℝ)) ?_
    simpa [hv] using (v_in_simplex.2 : (∑ i, v i) = (1 : ℝ))
  have r_eq : (perronRoot_alt A) = collatzWielandtFn A v := by
    apply le_antisymm
    · -- `perronRoot_alt A ≤ collatzWielandtFn A v`
      apply csSup_le set_nonempty
      rintro _ ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
      set s : ℝ := ∑ i, x i with hs
      have s_pos : 0 < s := by
        obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hx_nonneg hx_ne_zero
        simpa [hs] using
          (sum_pos' (fun j _ ↦ hx_nonneg j) ⟨i, mem_univ _, hi⟩)
      set x' : n → ℝ := s⁻¹ • x with hx'
      have hx'_in_simplex : x' ∈ stdSimplex ℝ n := by
        refine ⟨fun i ↦ ?_, ?_⟩
        · simpa [hx'] using (mul_nonneg (inv_nonneg.2 s_pos.le) (hx_nonneg i))
        · simp only [hx', Pi.smul_apply, smul_eq_mul, ← mul_sum, ← hs]
          field_simp [ne_of_gt s_pos]
      have h_scale : collatzWielandtFn A x = collatzWielandtFn A x' := by
        simpa [hx'] using
          (smul (A := A) (x := x) (c := s⁻¹) (inv_pos.2 s_pos)
          hA_nonneg hx_nonneg hx_ne_zero).symm
      simpa [h_scale] using v_is_max hx'_in_simplex
    · -- `collatzWielandtFn A v ≤ perronRoot_alt A`
      apply le_csSup (bddAbove_image_P_set A hA_nonneg)
       (Set.mem_image_of_mem _ ⟨v_in_simplex.1, v_ne_zero⟩)
  refine ⟨v, v_in_simplex, ?_⟩
  simpa [r, r_eq] using
    (le_mulVec (A := A) hA_nonneg v_in_simplex.1 v_ne_zero)

/--
The conditional supremum of a non-empty, bounded above set of
non-negative numbers is non-negative.
-/
lemma csSup_nonneg {s : Set ℝ} (hs_nonempty : s.Nonempty) (hs_bdd : BddAbove s)
    (hs_nonneg : ∀ x ∈ s, 0 ≤ x) : 0 ≤ sSup s := by
  obtain ⟨y, hy⟩ := hs_nonempty
  exact (hs_nonneg y hy).trans (le_csSup hs_bdd hy)

/-- The Perron root of a non-negative matrix is non-negative. -/
lemma perronRoot_nonneg [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    0 ≤ perronRoot_alt A := by
  refine csSup_nonneg (CollatzWielandt.set_nonempty (A := A))
    (CollatzWielandt.bddAbove (A := A) hA_nonneg) (fun _  ↦ ?_)
  rintro ⟨x, ⟨hx_nonneg, hx_ne_zero⟩, rfl⟩
  by_cases hsupp : ({i | 0 < x i}.toFinset).Nonempty
  · rw [collatzWielandtFn, dif_pos hsupp]
    apply le_inf'
    intro i hi
    obtain hxpos : 0 < x i := by simpa [Set.mem_toFinset] using hi
    refine div_nonneg (mulVec_nonneg (A := A) hA_nonneg hx_nonneg i) hxpos.le
  · simp [collatzWielandtFn]; aesop

/--
If an inequality lambda•w ≤ A•w holds for a non-negative non-zero vector w,
then lambda is bounded by the Collatz-Wielandt function value for w.
This is the property that the Collatz-Wielandt function gives
the maximum lambda satisfying such an inequality.
-/
theorem le_of_subinvariant (_ : ∀ i j, 0 ≤ A i j)
    {w : n → ℝ} (hw_nonneg : ∀ i, 0 ≤ w i) (hw_ne_zero : w ≠ 0)
    {lambda : ℝ} (h_sub : lambda • w ≤ A *ᵥ w) :
    lambda ≤ collatzWielandtFn A w := by
  obtain ⟨i, hi⟩ := exists_pos_of_ne_zero hw_nonneg hw_ne_zero
  let S := {j | 0 < w j}.toFinset
  have hS_nonempty : S.Nonempty := ⟨i, by simp [S]; exact hi⟩
  rw [collatzWielandtFn, dif_pos hS_nonempty]
  apply le_inf'
  intro j hj
  have h_j : lambda * w j ≤ (A *ᵥ w) j := by aesop
  have hw_j_pos : 0 < w j := by simpa [S] using hj
  exact (le_div_iff₀ hw_j_pos).mpr (h_sub j)

end CollatzWielandt

end PerronFrobenius

end Matrix
