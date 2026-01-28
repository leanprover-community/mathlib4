/-
Copyright (c) 2025 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Schauder bases in normed spaces

This file defines Schauder bases in a normed space and develops their basic theory.

## Main definitions

* `SchauderBasis 𝕜 X e`: A structure representing a Schauder basis for a normed space `X`
  over a field `𝕜`, where `e : ℕ → X` is the sequence of basis vectors.
  It includes:
  - `coord`: The sequence of coordinate functionals (elements of the dual space).
  - `ortho`: The biorthogonality condition $f_i(e_j) = \delta_{ij}$.
  - `basis_expansion`: The requirement that for every $x \in X$, the series
    $\sum_{n=0}^\infty f_n(x)e_n$ converges to $x$.

* `SchauderBasis.proj b n`: The $n$-th canonical projection $P_n: X \to X$ associated
  with the basis `b`, defined as $P_n(x) = \sum_{i < n} f_i(x)e_i$.

* `SchauderBasis.basisConstant`: The supremum of the norms of the canonical projections
  (often called the "basis constant").

## Main results

* `SchauderBasis.linearIndependent`: A Schauder basis is linearly independent.
* `SchauderBasis.proj_tendsto_id`: The canonical projections $P_n$ converge pointwise
  to the identity operator.
* `SchauderBasis.proj_uniform_bound`: In a Banach space, the canonical projections
  are uniformly bounded (a consequence of the Banach-Steinhaus Theorem).
* `SchauderBasis.basis_of_canonical_projections`: A criterion to construct a Schauder
  basis from a sequence of projections satisfying certain rank, composition, and
  convergence properties.

## Notation

The file uses the `SummationFilter.conditional ℕ` to handle the convergence of the
infinite sum, which corresponds to the convergence of partial sums.

## Bibliography

Based on Chapter 1. from Albiac, F., & Kalton, N. J. (2016). Topics in Banach Space Theory.
-/

@[expose] public section

noncomputable section

open Filter Topology LinearMap Set ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A Schauder basis is a sequence (e n) of vectors in X such that there exists a sequence of
    continuous linear functionals (f n) (the coordinate functionals) satisfying:
    1) f i (e j) = δ_{ij}
    2) for every x : X, the series ∑_{n=0}^∞ f n (x) e n converges to x.

    In other words, every vector in X can be uniquely represented as a convergent series of basis
    vectors, with coefficients given by the coordinate functionals. -/
structure SchauderBasis (𝕜 : Type*) {X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) where
  /-- Coordinate functionals -/
  coord : ℕ → StrongDual 𝕜 X
  /-- Biorthogonality -/
  ortho : ∀ i j, coord i (e j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i
  /-- Convergence of partial sums -/
  basis_expansion : ∀ x : X, HasSum (fun i ↦ (coord i) x • e i) x (SummationFilter.conditional ℕ)

namespace SchauderBasis

variable {e : ℕ → X} (b : SchauderBasis 𝕜 e)

/-- The basis vectors are linearly independent. -/
theorem linearIndependent (h : SchauderBasis 𝕜 e) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have hsum : ∑ i ∈ l.support, l i • e i = 0 := hl
  -- Apply the i-th coordinate functional to the linear combination
  have happ : h.coord i (∑ j ∈ l.support, l j • e j) = 0 := by rw [hsum, map_zero]
  rw [map_sum] at happ
  simp_rw [ContinuousLinearMap.map_smul] at happ
  rw [Finset.sum_eq_single i, h.ortho i i] at happ
  · simpa using happ
  · intro j _ hji; rw [h.ortho i j, Pi.single_apply, if_neg hji.symm, smul_eq_mul, mul_zero]
  · intro hi; simp only [Finsupp.notMem_support_iff.mp hi, smul_eq_mul, zero_mul]

/-- A canonical projection P_n associated to a Schauder basis given by coordinate functionals f_i:
    P_n x = ∑_{i < n} f_i(x) e_i -/
def proj (n : ℕ) : X →L[𝕜] X := ∑ i ∈ Finset.range n, (b.coord i).smulRight (e i)

/-- The canonical projection at 0 is the zero map. -/
@[simp]
theorem proj_zero : b.proj 0 = 0 := by
  simp only [proj, Finset.range_zero, Finset.sum_empty]

/-- The action of the canonical projection on a vector x. -/
@[simp]
theorem proj_apply (n : ℕ) (x : X) : b.proj n x = ∑ i ∈ Finset.range n, b.coord i x • e i := by
  simp only [proj, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

/-- The action of the canonical projection on a basis element e i. -/
@[simp]
theorem proj_basis_element (n i : ℕ) : b.proj n (e i) = if i < n then e i else 0 := by
  rw [proj_apply]
  by_cases hin : i < n
  · rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hin)]
    · simp only [b.ortho, Pi.single_apply, ↓reduceIte, one_smul, if_pos hin]
    · intro j _ hji; rw [b.ortho j i, Pi.single_apply, if_neg hji, zero_smul]
  rw [if_neg hin, Finset.sum_eq_zero]
  intro j hj
  push_neg at hin
  rw [b.ortho j i, Pi.single_apply, if_neg , zero_smul]
  exact (Finset.mem_range.mp hj).trans_le hin |>.ne

/-- The range of the canonical projection is the span of the first n basis elements. -/
theorem range_proj (n : ℕ) : LinearMap.range (b.proj n).toLinearMap =
    Submodule.span 𝕜 (Set.range (fun i : Fin n => e i)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, proj_apply b]
    apply Submodule.sum_mem
    intros i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    use e i
    rw [ContinuousLinearMap.coe_coe, proj_basis_element , if_pos i.is_lt]

/-- The dimension of the range of the canonical projection `P n` is `n`. -/
theorem dim_range_proj (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (b.proj n).toLinearMap) = n := by
  rw [range_proj, finrank_span_eq_card]
  · exact Fintype.card_fin n
  · exact b.linearIndependent.comp (fun (i : Fin n) => (i : ℕ)) Fin.val_injective

/-- The canonical projections converge pointwise to the identity map. -/
theorem proj_tendsto_id (x : X) : Tendsto (fun n ↦ b.proj n x) atTop (𝓝 x) := by
  simp only [proj_apply]
  have := b.basis_expansion x
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range] at this
  exact this

/-- Composition of canonical projections: `proj n (proj m x) = proj (min n m) x`. -/
theorem proj_comp (n m : ℕ) (x : X) : b.proj n (b.proj m x) = b.proj (min n m) x := by
  simp only [proj_apply, map_sum, map_smul]
  -- Now LHS is ∑ j < m, c_j • ∑ i < n, (coord i)(e_j) • e_i
  -- Use biorthogonality to simplify (coord i)(e_j)
  have h_ortho : ∀ i j, (b.coord i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [b.ortho i j, Pi.single_apply]
  simp_rw [h_ortho]
  -- Now inner sum is ∑ i < n, (if i = j then 1 else 0) • e_i = if j < n then e_j else 0
  simp only [ite_smul, one_smul, zero_smul]
  simp_rw [Finset.sum_ite_eq', Finset.mem_range]
  -- Now LHS is ∑ j < m, c_j • (if j < n then e_j else 0)
  simp only [smul_ite, smul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, and_comm]
  exact Nat.lt_min.symm

/-- The canonical projections are uniformly bounded (Banach-Steinhaus). -/
theorem proj_uniform_bound [CompleteSpace X] : ∃ C : ℝ, ∀ n : ℕ, ‖b.proj n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  let f: ℕ → X := fun n => b.proj n x
  have : ∃ M : ℝ, ∀ x ∈ Set.range f, ‖x‖ ≤ M :=
      isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto f (proj_tendsto_id b x ))
  rcases this with ⟨M, hM⟩
  rw [Set.forall_mem_range] at hM
  use M

/-- The basis constant is the supremum of the norms of the canonical projections. -/
def basisConstant : ℝ≥0∞ := ⨆ n, (‖b.proj n‖₊ : ℝ≥0∞)

-- /-- The basis constant is finite. -/
theorem basisConstant_lt_top_for_complete [CompleteSpace X] : b.basisConstant < ⊤ := by
  rw [basisConstant, ENNReal.iSup_coe_lt_top, bddAbove_iff_exists_ge (0 : NNReal)]
  obtain ⟨C, hC⟩ := b.proj_uniform_bound
  have hCpos : 0 ≤ C := by simpa [proj_zero] using hC 0
  use C.toNNReal
  constructor
  · exact zero_le _
  · rintro _ ⟨n, rfl⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal C hCpos, coe_nnnorm]
    exact hC n

/-- The norm of any projection is bounded by the basis constant (as a real number). -/
theorem norm_proj_le_basisConstant (n : ℕ) : (‖b.proj n‖₊ : ℝ≥0∞) ≤ b.basisConstant := by
  rw [basisConstant]
  exact le_iSup (fun i ↦ (‖b.proj i‖₊ : ℝ≥0∞)) n

/-- `Q_n = P_{n+1} - P_n`. -/
def Q (P : ℕ → X →L[𝕜] X) (n : ℕ) : X →L[𝕜] X := P (n + 1) - P n

/-- The sum of Q i over i < n equals P n. -/
@[simp]
lemma Q_sum (P : ℕ → X →L[𝕜] X) (h0 : P 0 = 0) (n : ℕ) : ∑ i ∈ Finset.range n, Q P i = P n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, Q]; abel

/-- The operators `Q i` are orthogonal projections. -/
lemma Q_ortho {P : ℕ → X →L[𝕜] X} (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (i j : ℕ) (x : X) : (Q P i) (Q P j x) = (Pi.single j (Q P j x) : ℕ → X) i := by
  simp only [Pi.single_apply, Q, ContinuousLinearMap.sub_apply, map_sub, hcomp,
    Nat.add_min_add_right]
  split_ifs with h
  · rw [h, min_self, min_eq_right (Nat.le_succ j), Nat.min_eq_left (Nat.le_succ j)]
    abel
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left_of_lt h', min_eq_left (Nat.succ_le_of_lt h'),
        min_eq_left_of_lt (Nat.lt_succ_of_lt h')]
      abel
    · rw [min_eq_right_of_lt h', min_eq_right (Nat.succ_le_of_lt h'),
        min_eq_right_of_lt (Nat.lt_succ_of_lt h')]
      abel

/-- The rank of `Q n` is `1`. -/
lemma Q_rank_one {P : ℕ → X →L[𝕜] X}
    (h0 : P 0 = 0)
    (hrank : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x) (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (Q P n).toLinearMap) = 1 := by
  let Q := Q P
  let U := LinearMap.range (Q n).toLinearMap
  let V := LinearMap.range (P n).toLinearMap
  have h_range_Pn_succ : LinearMap.range (P (n + 1)).toLinearMap = U ⊔ V := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩; rw [ContinuousLinearMap.coe_coe, ← sub_add_cancel (P (n + 1) y) (P n y)]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    · rw [sup_le_iff]
      have hV (y : X) : P n y ∈ LinearMap.range (P (n + 1)).toLinearMap := by
        use P n y
        rw [ContinuousLinearMap.coe_coe, hcomp (n + 1) n y, min_eq_right (Nat.le_succ n)]
      constructor
      · rintro x ⟨y, rfl⟩
        apply Submodule.sub_mem _ (LinearMap.mem_range_self _ _)
        dsimp only [ContinuousLinearMap.coe_coe]
        exact hV y
      · rintro x ⟨y, rfl⟩
        exact hV y
  have h_disjoint : U ⊓ V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    dsimp only [ContinuousLinearMap.coe_coe] at *
    have : Q n (P n z) = 0 := by
      simp_rw [Q, SchauderBasis.Q, ContinuousLinearMap.sub_apply, hcomp,
        min_eq_right (Nat.le_succ n), min_self, sub_self]
    rw [← hz, ← this, hz, Q_ortho hcomp, Pi.single_apply, if_pos rfl]
  have h_fin_Pn (n : ℕ) : FiniteDimensional 𝕜 (LinearMap.range (P n).toLinearMap) := by
    by_cases hn : n = 0
    · rw [hn]
      apply FiniteDimensional.of_rank_eq_zero
      apply Submodule.rank_eq_zero.mpr
      exact LinearMap.range_eq_bot.mpr (by simp only [h0, ContinuousLinearMap.coe_zero])
    apply FiniteDimensional.of_finrank_pos
    rw [hrank n]
    exact Nat.pos_of_ne_zero hn
  have : FiniteDimensional 𝕜 U := by
    have : U ≤ LinearMap.range (P (n+1)).toLinearMap := by
      simp only [U, Q, SchauderBasis.Q]
      intro x ⟨y, hy⟩
      rw [← hy]
      apply Submodule.sub_mem _ (LinearMap.mem_range_self _ _)
      use P n y
      dsimp only [ContinuousLinearMap.coe_coe]
      rw [hcomp (n+1) n y, min_eq_right (Nat.le_succ n)]
    exact Submodule.finiteDimensional_of_le this
  have : FiniteDimensional 𝕜 V := by simp only [V]; exact h_fin_Pn n
  have := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [h_disjoint, finrank_bot, add_zero, ← h_range_Pn_succ, hrank, hrank, Nat.add_comm] at this
  exact Nat.add_right_cancel this.symm

/-- Constructs a Schauder basis from a sequence of projections. -/
def basis_of_canonical_projections {P : ℕ → X →L[𝕜] X} {e : ℕ → X} (h0 : P 0 = 0)
    (hdim : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n).toLinearMap) = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (hlim : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x))
    (he_in_range : ∀ n, e n ∈ LinearMap.range (Q P n).toLinearMap) (he_ne : ∀ n, e n ≠ 0) :
    SchauderBasis 𝕜 e :=
  let Q := Q P
  have hrankQ := Q_rank_one h0 hdim hcomp
  have h_range_eq_span (n : ℕ) : LinearMap.range (Q n).toLinearMap = Submodule.span 𝕜 {e n} := by
    symm
    have : FiniteDimensional 𝕜 ↥(LinearMap.range (Q n).toLinearMap) := by
      apply FiniteDimensional.of_finrank_pos
      rw [hrankQ n]
      exact Nat.succ_pos 0
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact he_in_range n
    · rw [hrankQ n, finrank_span_singleton (he_ne n)]
  let f_fun : ℕ → X → 𝕜 := fun n x =>
    Classical.choose (Submodule.mem_span_singleton.mp (by
      rw [← h_range_eq_span]
      exact LinearMap.mem_range_self (Q n).toLinearMap x))
  have hQf (n : ℕ) (x : X) : Q n x = f_fun n x • e n :=
    (Classical.choose_spec (Submodule.mem_span_singleton.mp (by
      rw [← h_range_eq_span]
      exact LinearMap.mem_range_self (Q n).toLinearMap x))).symm
  let f (n : ℕ) : StrongDual 𝕜 X := LinearMap.mkContinuous (IsLinearMap.mk' (f_fun n) (by
    constructor
    · intro x y; apply smul_left_injective 𝕜 (he_ne n); dsimp only [smul_eq_mul];
      rw [← hQf, map_add, add_smul, hQf, hQf]
    · intro c x; apply smul_left_injective 𝕜 (he_ne n);dsimp  only [smul_eq_mul];
      rw [← hQf, map_smul, mul_smul, hQf]
    )) (‖Q n‖ / ‖e n‖) (by
      intro x; rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (he_ne n))]
      calc ‖f_fun n x‖ * ‖e n‖ = ‖f_fun n x • e n‖ := (norm_smul _ _).symm
        _ = ‖Q n x‖ := by rw [hQf]
        _ ≤ ‖Q n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _)
  have ortho : ∀ i j, f i (e j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
    intro i j
    apply smul_left_injective 𝕜 (he_ne i)
    dsimp only [smul_eq_mul]
    simp only [mkContinuous_apply, IsLinearMap.mk'_apply, Pi.single_apply, ite_smul, one_smul,
      zero_smul, f]
    have : Q i (e j) = (Pi.single j (e j) : ℕ → X) i := by
      obtain ⟨x, hx⟩ := he_in_range j
      rw [ContinuousLinearMap.coe_coe] at hx
      rw [← hx, Q_ortho hcomp i j x]
    rw [← hQf, this, Pi.single_apply]
    split_ifs with hij
    · subst hij; simp only
    · simp only
  have lim (x : X) : HasSum (fun i ↦ (f i) x • e i) x (SummationFilter.conditional ℕ) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
    apply Tendsto.congr _ (hlim x)
    intro n
    simp_rw [f]
    dsimp only [mkContinuous_apply, IsLinearMap.mk'_apply]
    simp_rw [← hQf, Q]
    simp only [← Q_sum P h0 n, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  SchauderBasis.mk f ortho lim

end SchauderBasis
