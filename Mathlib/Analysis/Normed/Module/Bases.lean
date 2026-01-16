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


variable [CompleteSpace X]
/-- The canonical projections are uniformly bounded (Banach-Steinhaus). -/
theorem uniform_bound : ∃ C : ℝ, ∀ n : ℕ, ‖h.canonicalProjection n‖ ≤ C := by
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

/-- Construct a Schauder basis from a sequence of canonical projections satisfying natural
    properties. -/
theorem basis_of_canonical_projections {P : ℕ → X →L[𝕜] X}
    (hdim : ∀ n : ℕ, Module.finrank 𝕜 (LinearMap.range (P n)) = n + 1)
    (hcomp : ∀ n m : ℕ, P n ∘ P m = P (min n m))
    (lim : ∀ x : X, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    ∃ e : ℕ → X, SchauderBasis 𝕜 X e := by
        -- Define the difference operator Q_n mapping to the n-th coordinate space
        let Q : ℕ → X →L[𝕜] X := fun n ↦
            if h : n = 0 then P 0 else P n - P (n - 1)

        -- Q sums to P
        have h_sum : ∀ n, ∑ i ∈ Finset.range (n + 1), Q i = P n := by
            intro n
            induction' n with n ih
            · simp [Q]
            · rw [Finset.sum_range_succ, ih]; dsimp [Q]; simp

        -- Q n has rank 1
        have h_dim_Q : ∀ n, Module.finrank 𝕜 (LinearMap.range (Q n)) = 1 := by
            intro n
            by_cases h0 : n = 0
            · simp [Q]
              rw [if_pos h0]
              exact hdim 0
            simp [Q]
            rw [if_neg h0]
            have h_le : LinearMap.range (P (n - 1)) ≤ LinearMap.range (P n) := by
                intro x hx
                obtain ⟨y, rfl⟩ := hx
                use P (n - 1) y
                have : n - 1 ≤ n := Nat.sub_le n 1
                calc
                  P n (P (n - 1) y) = (P n ∘ P (n - 1)) y := rfl
                  _ = (P (n - 1)) y  := by rw [hcomp n (n - 1), min_eq_right this]
            have hx : LinearMap.range (Q n) ⊓ LinearMap.range (P (n - 1)) = ⊥ := by
                rw [Submodule.eq_bot_iff]
                sorry
            have h_sum : LinearMap.range (Q n) ⊔ LinearMap.range (P (n - 1)) = LinearMap.range (P n) := by
                sorry
            let U := LinearMap.range (Q n)
            let V := LinearMap.range (P (n - 1))
            have : FiniteDimensional 𝕜 U := by sorry
            have : FiniteDimensional 𝕜 V := by sorry
            have hy :   Module.finrank 𝕜 ↥(U ⊔ V) + Module.finrank 𝕜 ↥(U ⊓ V) =  Module.finrank 𝕜 (U) + Module.finrank 𝕜 (V)
                := Submodule.finrank_sup_add_finrank_inf_eq U V

            rw [hx,  h_sum, finrank_bot, add_zero, hdim n, hdim (n - 1)] at hy
            have : 1 = Module.finrank 𝕜 (LinearMap.range (Q n)) := by
                rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)] at hy
                rw [add_comm] at hy
                exact Nat.add_right_cancel hy


            exact this




                -- apply le_antisymm
                -- ·   rintro z ⟨x, rfl⟩
                --     simp [Q]
                --     rw [if_neg h0]
                --     have hz : P (n - 1) (P n x) = P (n - 1) x := by
                --         rw [hcomp n (n - 1), min_eq_right (Nat.sub_le n 1)]
                --     simp [hz]
                --     apply Submodule.mem_inf.mpr
                --     constructor
                --     · use P n x
                --     · simp [hz]
                -- · rintro z ⟨y, hy⟩
                --   rw [hy]
                --   simp [Q]
                --   by_cases h0 : n = 0
                --   · rw [if_pos h0]
                --     use y
                --   · rw [if_neg h0]
                --     use y
                --     simp


        sorry



end SchauderBasis
