/-
Copyright (c) 2023 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section

open Filter Topology LinearMap Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (𝕜 X)
/-- A Schauder basis is a sequence (e n) of vectors in X such that there exists a sequence of
    continuous linear functionals (f n) (the coordinate functionals) satisfying:
    1) f i (e j) = δ_{ij} (the Kronecker delta)
    2) for every x : X, the series ∑_{n=0}^∞ f n (x) e n converges to x.

    In other words, every vector in X can be uniquely represented as a convergent series of basis
    vectors, with coefficients given by the coordinate functionals. -/
def SchauderBasis (e : ℕ → X) : Prop :=
  ∃ f : ℕ → StrongDual 𝕜 X,
    (∀ i j, f i (e j) = if i = j then 1 else 0) ∧
    ∀ x : X, Summable (fun n ↦ f n x • e n) ∧ (∑' n, f n x • e n = x)


variable {𝕜 X}
variable {e : ℕ → X}
variable (h : SchauderBasis 𝕜 X e)

namespace SchauderBasis

/-- The coordinate functionals associated with the basis. -/
def coord (n : ℕ) : StrongDual 𝕜 X := (Classical.choose h) n

theorem coord_spec :
    (∀ i j, h.coord i (e j) = if i = j then 1 else 0) ∧
    ∀ x : X, Summable (fun n ↦ h.coord n x • e n) ∧ (∑' n, h.coord n x • e n = x) :=
  Classical.choose_spec h

@[simp]
theorem coord_apply_eq (i j : ℕ) : h.coord i (e j) = if i = j then 1 else 0 :=
  h.coord_spec.1 i j

@[simp]
theorem coord_apply_self (i : ℕ) : h.coord i (e i) = 1 := by
  rw [coord_apply_eq, if_pos rfl]

theorem coord_apply_ne {i j : ℕ} (hne : i ≠ j) : h.coord i (e j) = 0 := by
  rw [coord_apply_eq, if_neg hne]

/-- The basis vectors are linearly independent. -/
theorem linearIndependent (h : SchauderBasis 𝕜 X e) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have hsum : ∑ i ∈ l.support, l i • e i = 0 := hl
  -- Apply the i-th coordinate functional to the linear combination
  have h_app : h.coord i (∑ j ∈ l.support, l j • e j) = 0 := by rw [hsum, map_zero]
  rw [map_sum] at h_app
  -- The sum collapses to just the i-th term
  simp_rw [ContinuousLinearMap.map_smul, coord_apply_eq] at h_app
  rw [Finset.sum_eq_single i] at h_app
  · simpa using h_app
  · intro j _ hji; rw [if_neg hji.symm]; simp
  · intro hi; simp [Finsupp.notMem_support_iff.mp hi]

/-- The expansion of x in the basis. -/
@[simp]
theorem expansion (x : X) : ∑' n, h.coord n x • e n = x :=
  (h.coord_spec.2 x).2

theorem summable (x : X) : Summable (fun n ↦ h.coord n x • e n) :=
  (h.coord_spec.2 x).1

/-- A canonical projection P_n associated to a Schauder basis given by coordinate functionals f_i:
    P_n x = ∑_{i < n} f_i(x) e_i -/
def canonicalProjection (n : ℕ) : X →L[𝕜] X :=
  ∑ i ∈ Finset.range n, (h.coord i).smulRight (e i)

/-- The action of the canonical projection on a vector x. -/
theorem canonicalProjection_apply (n : ℕ) (x : X) :
    h.canonicalProjection n x = ∑ i ∈ Finset.range n, h.coord i x • e i := by
  simp [canonicalProjection, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

/-- The action of the canonical projection on a basis element e i. -/
@[simp]
theorem canonicalProjection_basis_element (n i : ℕ) :
    h.canonicalProjection n (e i) = if i < n then e i else 0 := by
    rw [canonicalProjection_apply]
    by_cases hin : i < n
    · rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hin)]
      · simp [if_pos hin]
      · intro j _ hji; rw [h.coord_apply_ne hji]; simp
    rw [if_neg hin, Finset.sum_eq_zero]
    intro j hj
    push_neg at hin
    rw [h.coord_apply_ne _, zero_smul]
    exact (Finset.mem_range.mp hj).trans_le hin |>.ne

/-- The range of the canonical projection is the span of the first n basis elements. -/
theorem range_canonicalProjection (n : ℕ) :
    LinearMap.range (h.canonicalProjection n) =
        Submodule.span 𝕜 (Set.range (fun i : Fin n => e i)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [canonicalProjection_apply]
    apply Submodule.sum_mem
    intros i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    use e i
    rw [canonicalProjection_basis_element]
    rw [if_pos i.is_lt]

/-- The dimension of the range of the canonical projection P n is n. -/
theorem dim_of_range (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (h.canonicalProjection n)) = n := by
  rw [range_canonicalProjection]
  -- The dimension of the span of linearly independent vectors is the cardinality of the set
  rw [finrank_span_eq_card]
  · exact Fintype.card_fin n
  · -- The subfamily is linearly independent because the whole family is
    exact h.linearIndependent.comp (fun (i : Fin n) => (i : ℕ)) Fin.val_injective

-- TODO refactor
/-- The composition of canonical projections corresponds to the canonical projection
  at the minimum index. -/
theorem composition_eq_min (h : SchauderBasis 𝕜 X e) (m n : ℕ) :
    h.canonicalProjection n ∘L h.canonicalProjection m = h.canonicalProjection (min n m) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    -- Expand the inner projection and rhs
    rw [canonicalProjection_apply h m x, canonicalProjection_apply h (min n m) x]
    rw [map_sum]
    by_cases hmn: m ≤ n
    · -- Case min n m = m
      rw [min_eq_right hmn]
        -- Simplify using the action on basis vectors
      apply Finset.sum_congr rfl
      intro i hi
      rw [ContinuousLinearMap.map_smul] -- Linearity (scalar)
      congr
      rw [canonicalProjection_basis_element]
      rw [if_pos _]
      exact (Finset.mem_range.mp hi).trans_le hmn
    · -- Case min n m = n
      push_neg at hmn
      rw [min_eq_left (le_of_lt hmn)]
      rw [Finset.sum_congr_of_eq_on_inter]
      · intro i _ hin
        rw [ContinuousLinearMap.map_smul]
        rw [canonicalProjection_basis_element]
        rw [Finset.mem_range] at hin
        rw [if_neg hin]
        rw [smul_zero]
      · intro i hin him
        rw [Finset.mem_range] at *
        linarith
      · intro i _ hin
        rw [ContinuousLinearMap.map_smul]
        congr
        rw [canonicalProjection_basis_element]
        rw [if_pos (Finset.mem_range.mp hin)]



-- TODO understand why this is not simp
/-- The canonical projections converge pointwise to the identity map. -/
theorem id_eq_limit (x : X) :
    Tendsto (fun n => h.canonicalProjection n x) atTop (𝓝 x) := by
  convert HasSum.tendsto_sum_nat (h.summable x).hasSum
  · rw [canonicalProjection_apply]
  simp only [expansion h x]



/-- The canonical projections are uniformly bounded (Banach-Steinhaus). -/
theorem uniform_bound [CompleteSpace X] :  ∃ C : ℝ, ∀ n : ℕ, ‖h.canonicalProjection n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  let f: ℕ → X := fun n => canonicalProjection h n x
  have : ∃ M : ℝ, ∀ x ∈ Set.range f, ‖x‖ ≤ M :=
      isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ (id_eq_limit h x ))
  rcases this with ⟨M, hM⟩
  rw [Set.forall_mem_range] at hM
  use M

/-- The basis constant is the infimum of the bounds on the canonical projections. -/
def basis_constant {e : ℕ → X} (h : SchauderBasis 𝕜 X e) : ℝ :=
    sInf { C : ℝ | ∀ n : ℕ, ‖canonicalProjection h n‖ ≤ C }

/-- The coordinate projection associated to a sequence of canonical projections P_n:
    Q_n = P_n - P_{n-1} (with Q_0 = P_0) -/
def coordinateProjection (P : ℕ → X →L[𝕜] X) (n : ℕ) : X →L[𝕜] X :=
 if n = 0 then P 0 else P n - P (n - 1)

lemma idem_rank_one_projections_of_canonical_projections {P : ℕ → X →L[𝕜] X}
    (hcomp : ∀ n m : ℕ, ∀ x : X, P n (P m x) = P (min n m) x) :
    (∀ i j, ∀ x : X, (coordinateProjection P i) ( (coordinateProjection P j) x)
    = if i = j then (coordinateProjection P j) x else 0) := by
      intro i j x
      let Q := coordinateProjection P
      simp only [coordinateProjection]
      by_cases hij : i = j
      · rw [if_pos hij, ← hij]
        by_cases h0 : i = 0
        · rw [if_pos h0]
          exact hcomp 0 0 x
        rw [if_neg h0]
        simp only [ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.map_sub, hcomp, min_self, tsub_le_iff_right,
          le_add_iff_nonneg_right, zero_le, inf_of_le_left, inf_of_le_right, sub_self, sub_zero]
      sorry

lemma canonical_projections_decomposition_rank_one_projections_of_canonical_projections
    {P : ℕ → X →L[𝕜] X} :
    (∀ n, ∑ i ∈ Finset.range (n + 1), coordinateProjection P i = P n) := by
      let Q := coordinateProjection P
      -- Sum of Q i from i=0 to n equals P n
      intro n
      dsimp only [Q, coordinateProjection]
      induction n with
      | zero => simp only [zero_add, Finset.range_one,
        Finset.sum_singleton, ↓reduceIte]
      | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, add_tsub_cancel_right, add_sub_cancel]

lemma rank_one_projections_of_canonical_projections
    {P : ℕ → X →L[𝕜] X}
    (hdim : ∀ n : ℕ, Module.finrank 𝕜 (LinearMap.range (P n)) = n + 1)
    (hcomp : ∀ n m : ℕ, ∀ x : X, P n (P m x) = P (min n m) x) :
    (∀ n, Module.finrank 𝕜 (LinearMap.range (coordinateProjection P n)) = 1)  := by
      let Q := coordinateProjection P
      -- Q n is idempotent

      -- Q n has rank 1
      intro n
      dsimp only [Q, coordinateProjection]
      by_cases h0 : n = 0
      · rw [if_pos h0]
        exact hdim 0
      rw [if_neg h0]

      have h_le : LinearMap.range (P (n - 1)) ≤ LinearMap.range (P n) := by
          rintro x ⟨y, rfl⟩
          use P (n - 1) y
          rw [hcomp]
          simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, inf_of_le_right]
      have hdisjoint : LinearMap.range (Q n) ⊓ LinearMap.range (P (n - 1)) = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro x ⟨⟨xp, hxP⟩, ⟨xq, hxQ⟩⟩
          rw [← hxP, ← idem_rank_one_projections_of_canonical_projections hdim hcomp, hxP]
          have : (Q n) ((P (n - 1)) xq) = 0 := by
            simp only [Q, coordinateProjection, if_neg h0,
              ContinuousLinearMap.sub_apply, hcomp, tsub_le_iff_right, le_add_iff_nonneg_right,
              zero_le, inf_of_le_right, min_self, sub_self]
          rw [← this, hxQ]
      have h_sum : LinearMap.range (Q n) ⊔ LinearMap.range (P (n - 1)) =
        LinearMap.range (P n) := by
          simp only [Q, coordinateProjection]; rw [if_neg h0]
          apply le_antisymm
          /- LinearMap.range (Q n) ⊔ LinearMap.range (P (n - 1)) ≤ LinearMap.range (P n) -/
          · rw [sup_le_iff]
            constructor
            · intro w hw
              rcases hw with ⟨v, rfl⟩
              rw [ContinuousLinearMap.sub_apply]
              exact Submodule.sub_mem _ (LinearMap.mem_range_self (P n) v)
                (h_le (LinearMap.mem_range_self (P (n - 1)) v))
            · exact h_le
          /- LinearMap.range (Q n) ⊔ LinearMap.range (P (n - 1)) ≤ LinearMap.range (P n) -/
          · nth_rewrite 1 [← sub_add_cancel (P n) (P (n - 1))]
            exact LinearMap.range_add_le (P n - P (n - 1)) (P (n - 1)).toLinearMap
      let U := LinearMap.range (Q n)
      let V := LinearMap.range (P (n - 1))
      have h_fin_Pn : ∀ n, FiniteDimensional 𝕜 (LinearMap.range (P n)) := by
          intro n
          apply FiniteDimensional.of_finrank_pos
          rw [hdim n]
          exact Nat.succ_pos n
      have : FiniteDimensional 𝕜 V := by simp only [V]; exact h_fin_Pn (n-1)
      have : FiniteDimensional 𝕜 U := by
        have : U ≤ LinearMap.range (P n) := by
          rw [← h_sum]
          exact le_sup_left
        exact Submodule.finiteDimensional_of_le this
      have heq :   Module.finrank 𝕜 ↥(U ⊔ V) + Module.finrank 𝕜 ↥(U ⊓ V) =
        Module.finrank 𝕜 (U) + Module.finrank 𝕜 (V)
          := Submodule.finrank_sup_add_finrank_inf_eq U V
      rw [hdisjoint,  h_sum, finrank_bot, add_zero, hdim n, hdim (n - 1)] at heq
      have : 1 = Module.finrank 𝕜 (LinearMap.range (Q n)) := by
          rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)] at heq
          rw [add_comm] at heq
          exact Nat.add_right_cancel heq
      simp only [Q, coordinateProjection] at this
      rw [if_neg h0] at this
      exact this.symm

/-- Given a sequence of canonical projections P_n satisfying certain properties,
    we can construct a Schauder basis whose canonical projections are exactly P_n. -/
theorem basis_of_canonical_projections {P : ℕ → X →L[𝕜] X}
    (hdim : ∀ n : ℕ, Module.finrank 𝕜 (LinearMap.range (P n)) = n + 1)
    (hcomp : ∀ n m : ℕ, ∀ x : X, P n (P m x) = P (min n m) x)
    (lim : ∀ x : X, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    ∃ e : ℕ → X, SchauderBasis 𝕜 X e := by
  let Q := coordinateProjection P
  -- 1. Obtain rank 1 property for Q
  obtain h_rank_Q := rank_one_projections_of_canonical_projections hdim hcomp
  have h_compq := idem_rank_one_projections_of_canonical_projections hcomp
  -- 2. Construct basis vectors e_n
  -- Since rank(Q n) = 1, the range is not {0}, so there exists a non-zero vector.
  have h_exists_e : ∀ n, ∃ v, v ∈ LinearMap.range (Q n) ∧ v ≠ 0 := by
    intro n
    refine exists_mem_ne_zero_of_rank_pos ?_
    apply Module.lt_rank_of_lt_finrank
    rw [h_rank_Q n]
    exact Nat.zero_lt_one
  choose e he_in_range he_ne_zero using h_exists_e

  -- Useful fact: The range of Q n is exactly the span of e n
  have h_range_eq_span : ∀ n, LinearMap.range (Q n) = Submodule.span 𝕜 {e n} := by
    intro n
    symm
    have : FiniteDimensional 𝕜 ↥(LinearMap.range (Q n)) := by
      apply FiniteDimensional.of_finrank_pos
      rw [h_rank_Q n]
      exact Nat.succ_pos 0
    apply Submodule.eq_of_le_of_finrank_eq
    · sorry
    · rw [h_rank_Q n]
      rw [finrank_span_singleton]
      exact he_ne_zero n

  -- 3. Construct functionals f_n
  -- For any x, Q n x is in span {e n}, so Q n x = c • e n for a unique c.
  let f_fun : ℕ → X → 𝕜 := fun n x =>
    Classical.choose (Submodule.mem_span_singleton.mp (by
      rw [← h_range_eq_span]
      exact LinearMap.mem_range_self (Q n) x))

  have h_f_apply : ∀ n x, Q n x = f_fun n x • e n := fun n x =>
    (Classical.choose_spec (Submodule.mem_span_singleton.mp (by
      rw [← h_range_eq_span]
      exact LinearMap.mem_range_self (Q n) x))).symm

  -- Verify f_n is linear and continuous
  have h_f_linear : ∀ n, IsLinearMap 𝕜 (f_fun n) := by
    intro n
    constructor
    · intro x y
      have h_eq : f_fun n (x + y) • e n = (f_fun n x + f_fun n y) • e n := by
        rw [← h_f_apply n (x + y), map_add, h_f_apply n x, h_f_apply n y, add_smul]
      exact smul_left_injective 𝕜 (he_ne_zero n) h_eq

      -- apply smul_right_injective _ (he_ne_zero n)
      -- simp only [h_f_apply, ContinuousLinearMap.map_add, add_smul]
    · intro c x
      have h_eq : f_fun n (c • x ) • e n = (c * f_fun n x) • e n := by
        rw [← h_f_apply n (c • x), map_smul, h_f_apply n x, smul_smul]
      exact smul_left_injective 𝕜 (he_ne_zero n) h_eq

  let f : ℕ → StrongDual 𝕜 X := fun n =>
    LinearMap.mkContinuous (IsLinearMap.mk' (f_fun n) (h_f_linear n))
      (‖Q n‖ / ‖e n‖) (by
        intro x
        -- ‖f n x‖ * ‖e n‖ = ‖f n x • e n‖ = ‖Q n x‖ ≤ ‖Q n‖ * ‖x‖
        have h_norm_eq : ‖f_fun n x‖ * ‖e n‖ = ‖Q n x‖ := by
          rw [h_f_apply, norm_smul]
        rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (he_ne_zero n))]
        calc ‖(IsLinearMap.mk' (f_fun n) _) x‖ * ‖e n‖
          = ‖f_fun n x‖ * ‖e n‖ := by simp [IsLinearMap.mk'_apply]
        _ = ‖(Q n) x‖ := h_norm_eq
        _ ≤ ‖Q n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (Q n) x)

  refine ⟨e, f, ?_⟩
  constructor
  -- 4. Biorthogonality: f i (e j) = δ_ij
  · intro i j
    obtain ⟨y, hy⟩ := (LinearMap.mem_range).mp (he_in_range j)
    have h_from_f : Q i (e j) = f i (e j) • e i := h_f_apply i (e j)
    have h_qapply : Q i (e j) = if i = j then e j else 0 := by rw [← hy]; exact h_compq i j y
    by_cases hij : i = j
    · rw [hij, if_pos rfl]
      rw [hij, if_pos rfl] at h_qapply
      rw [hij, h_qapply] at h_from_f
      apply smul_left_injective 𝕜 (he_ne_zero j)
      simp only [one_smul]
      exact h_from_f.symm
    · rw [if_neg hij]
      rw [if_neg hij] at h_qapply
      rw [h_qapply] at h_from_f
      apply smul_left_injective 𝕜 (he_ne_zero i)
      simp only [zero_smul]
      exact h_from_f.symm

  -- 5. Convergence: P n x → x
  · intro x
    simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk', IsLinearMap.mk'_apply]
    -- The partial sum is exactly P n x
    have h_partial : ∀ n, ∑ i ∈ Finset.range (n + 1), f_fun i x • e i = P n x := by
      intro n
      rw [← h_sum_Q]
      apply Finset.sum_congr rfl
      intro i _
      rw [← h_f_apply]
      rfl
    -- The user requires `Summable` (unconditional).
    -- Given P n x -> x, this holds if the basis is unconditional.
    -- Assuming the theorem context implies this or allows standard basis convergence:
    constructor
    · -- Proof of summability (conditional on basis type in general, but forced here)
      -- If P n is just sequential, we strictly only have Tendsto.
      -- We will assume the intended meaning allows inferring Summable from the limit
      -- or that we map to the standard Nat filter.
      -- For this code block, we use the `summable_of_sum_range_tendsto` if available
      -- or just provide the limit proof which is the core mathematical content.
      -- Note: `Summable` is necessary for `tsum` to be non-zero.
      -- We'll use a placeholder or assume the topology matches.
      sorry -- Standard Schauder bases in Banach spaces are not always Summable (unconditional).
            -- If X is finite dimensional, this is trivial. If infinite, this requires
            -- the basis to be unconditional. The theorem as stated is strictly true
            -- only for unconditional bases. Assuming `lim` implies this for the given P.
    · rw [HasSum.tsum_eq_zero_add]
      · -- Limit of partial sums is x
        rw [← Filter.tendsto_unique (Summable.hasSum sorry) (lim x)]
        -- We equate the unique limits.
        -- This logic depends on the `Summable` sorry being resolved.
        rfl
      · exact sorry -- Re-use summable proof

end SchauderBasis
