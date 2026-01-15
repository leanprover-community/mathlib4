/-
Copyright (c) 2023 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

@[expose] public section

noncomputable section

universe u

open Filter Topology LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable (𝕜 X)
-- TODO use (.) functions instead of fun => when possible


/-- A Schauder basis is a sequence (e n) such that every element x of the space can be uniquely
represented as a convergent series x = ∑' n, a n • e n for some coefficients a n in the field 𝕜. -/
def SchauderBasis (e : ℕ → X) : Prop :=
  ∃ f : ℕ → StrongDual 𝕜 X,
    (∀ i j, f i (e j) = if i = j then 1 else 0) ∧
    ∀ x : X, Summable (fun n ↦ f n x • e n) ∧ (∑' n, f n x • e n = x)

variable {𝕜 X}
variable {e : ℕ → X}

namespace SchauderBasis

def coord {e : ℕ → X}
    (h : SchauderBasis 𝕜 X e) : ℕ → StrongDual 𝕜 X := Classical.choose h

theorem coord_apply_eq (h : SchauderBasis 𝕜 X e) (i j : ℕ) :
    h.coord i (e j) = if i = j then 1 else 0 :=
  (Classical.choose_spec h).1 i j

theorem coord_apply_self (h : SchauderBasis 𝕜 X e) (i : ℕ) : h.coord i (e i) = 1 := by
  rw [coord_apply_eq, if_pos rfl]

theorem coord_apply_ne (h : SchauderBasis 𝕜 X e) {i j : ℕ} (hne : i ≠ j) : h.coord i (e j) = 0 := by
  rw [coord_apply_eq, if_neg hne]

/-- The basis vectors are linearly independent. -/
theorem linearIndependent (h : SchauderBasis 𝕜 X e) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff]
  intros l hl
  ext k
  have hsum : ∑ i ∈ l.support, l i • e i = 0 := hl
  have h_app : h.coord k (∑ i ∈ l.support, l i • e i) = 0 := by
    rw [hsum, map_zero]
  rw [map_sum, Finset.sum_eq_single k] at h_app
  · simpa [coord_apply_self] using h_app
  · intros j _ hji
    have : (h.coord k) (l j • e j) = l j • (h.coord k (e j)) := by
        rw [ContinuousLinearMap.map_smul]
    simp [this, coord_apply_ne h hji.symm]
  · intro hi_notin_supp
    have : l k = 0 := Finsupp.notMem_support_iff.mp hi_notin_supp
    simp [this]


def coeff {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) : ℕ → 𝕜 :=
    fun n => coord h n x

theorem coeff_summable {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) :
        Summable (fun n => coeff h x n • e n) := ((Classical.choose_spec h).2 x).1

/-- The representation of x. -/
def repr (h : SchauderBasis 𝕜 X e) (x : X) : X := ∑' n, h.coord n x • e n

@[simp]
theorem repr_eq_self (h : SchauderBasis 𝕜 X e) (x : X) : h.repr x = x :=
  ((Classical.choose_spec h).2 x).2

theorem summable (h : SchauderBasis 𝕜 X e) (x : X) : Summable (fun n ↦ h.coord n x • e n) :=
  ((Classical.choose_spec h).2 x).1

/-- A canonical projection P_n associated to a Schauder basis.
    P_n x = ∑_{i < n} f_i(x) e_i -/
def CanonicalProjection (h : SchauderBasis 𝕜 X e) (n : ℕ) : X →L[𝕜] X :=
  ∑ i ∈ Finset.range n, (h.coord i).smulRight (e i)

theorem CanonicalProjection_apply (h : SchauderBasis 𝕜 X e) (n : ℕ) (x : X) :
    h.CanonicalProjection n x = ∑ i ∈ Finset.range n, h.coord i x • e i := by
  simp [CanonicalProjection, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]


namespace CanonicalProjections

theorem canonical_projection_on_basis_element
    (h : SchauderBasis 𝕜 X e) (n i : ℕ) :
    (CanonicalProjection h n) (e i) = if i < n then e i else 0 := by
    let bf := coord h
    have : (CanonicalProjection h n) (e i) = ∑ j ∈ Finset.range n, bf j (e i) • e j := by
        rw [CanonicalProjection]; simp [bf]
    rw [this]
    have hsum: (∑ j ∈ Finset.range n, bf j (e i) • e j) =
        ∑ j ∈ Finset.range n, (if j = i then (1 : 𝕜) else 0) • e j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [coord_apply_eq h j i]
    rw [hsum]
    simp [Finset.sum_ite_eq']


theorem dim_of_range (h : SchauderBasis 𝕜 X e) (n : ℕ) :
    Module.finrank 𝕜 (range (CanonicalProjection h n)) = n := by
    have einrange: ∀ i, i < n → e i ∈ range (CanonicalProjection h n) := by
        intro i hi
        let bf := coord h
         -- TODO make it a lemma
        have z: (Finset.range n).filter (fun j => j = i) = {i} := by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            constructor
            · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, rfl⟩
            · intro _ hm; exact (Finset.mem_filter.mp hm).2
        have : (CanonicalProjection h n) (e i) = e i := by
            rw [canonical_projection_on_basis_element h n i]
            simp [hi]
        exact ⟨e i, this⟩
    have range_eq_span : range (CanonicalProjection h n) = Submodule.span 𝕜 { e i | i < n } := by
        apply le_antisymm
        · -- range ⊆ span
          intro x ⟨y, hy⟩
          rw [← hy, CanonicalProjection]
          simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
          apply Submodule.sum_mem
          intro i hi
          apply Submodule.smul_mem
          apply Submodule.subset_span
          simp only [Finset.mem_range] at hi
          exact ⟨i, hi, rfl⟩
        · -- span ⊆ range
          apply Submodule.span_le.mpr
          intro x ⟨i, hi, hx⟩
          rw [← hx]
          exact einrange i hi
    rw [range_eq_span]
    have li : LinearIndependent 𝕜 (fun (i : Fin n) => e i) := by
      apply LinearIndependent.comp h.linearIndependent
      intro i j hij
      exact Fin.ext hij
    have span_eq : Submodule.span 𝕜 (Set.range (fun (i : Fin n) => e i)) =
                   Submodule.span 𝕜 { e i | i < n } := by
      congr 1
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · intro ⟨i, hi⟩
        exact ⟨i.val, i.isLt, hi⟩
      · intro ⟨i, hi, hx⟩
        exact ⟨⟨i, hi⟩, hx⟩
    rw [← span_eq, ← li.finrank_span_eq_card, Fintype.card_fin]
    exact this


theorem composition_eq_min (h : SchauderBasis 𝕜 X e) (m n : ℕ) :
    CanonicalProjection h n ∘ CanonicalProjection h m = CanonicalProjection h (min n m) := by
    ext x
    let bf := coord h
    have hinner: ∀ i j : ℕ, (bf i (bf j x • e j)) • e i = if i = j then (bf j x) • e i else 0 := by
        intro i j; rw [ContinuousLinearMap.map_smul, coord_apply_eq h i j]; simp
    calc
        (CanonicalProjection h n ∘ CanonicalProjection h m) x
            = CanonicalProjection h n (CanonicalProjection h m x) := by simp
        _ = ∑ i ∈ Finset.range n, bf i (CanonicalProjection h m x) • e i := by
            rw [CanonicalProjection]; simp [bf]
        _ = ∑ i ∈ Finset.range n, bf i (∑ j ∈ Finset.range m, bf j x • e j) • e i := by
            rw [CanonicalProjection]; simp [bf]
        _ = ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range m, (bf i (bf j x • e j))) • e i :=
            Finset.sum_congr rfl (fun j hj => by apply congrArg ( · • e j ); rw [map_sum])
        _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, (bf i (bf j x • e j)) • e i :=
            Finset.sum_congr rfl (fun j hj => Finset.sum_smul )
        _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, if i = j then (bf j x) • e i else 0 :=
            Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun i hi => hinner j i))
        _ = ∑ i ∈ Finset.range (min n m), (bf i x) • e i := by
            by_cases hnm: n ≤ m
            · rw [min_eq_left hnm]
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_ite_eq_of_mem
              simp only [Finset.mem_range] at *
              exact lt_of_lt_of_le hi hnm
            · push_neg at hnm
              rw [min_eq_right (le_of_lt hnm)]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_ite_eq_of_mem'
              simp only [Finset.mem_range] at *
              exact hj.trans hnm
        _ = CanonicalProjection h (min n m) x := by rw [CanonicalProjection]; simp [bf]

theorem id_eq_limit (h : SchauderBasis 𝕜 X e) (x : X) :
    Tendsto (fun n => CanonicalProjection h n x) atTop (𝓝 x) := by
    let bf := coord h
    have tndto : Tendsto (fun n => (∑ i ∈ Finset.range n, coeff h x i • e i))
        atTop (𝓝 (∑' n, bf n x • e n)) := HasSum.tendsto_sum_nat (coeff_summable h x).hasSum
    have r: ∑' (n : ℕ), (bf n) x • e n = x := by
        nth_rw 2 [<-repr_self h x]
        dsimp [repr, coeff]
    rw [r] at tndto
    have p: ∀ n, ∑ i ∈ Finset.range n, h.coeff x i • e i = (h.CanonicalProjection n) x := by
        dsimp [CanonicalProjection, coeff]
        simp
    exact Filter.Tendsto.congr p tndto

variable [CompleteSpace X]
-- todo clean up proof
theorem uniform_bound (h : SchauderBasis 𝕜 X e) :
    ∃ C : ℝ, ∀ n : ℕ, ‖CanonicalProjection h n‖ ≤ C := by
    exact banach_steinhaus (by
        intro x
        let f: ℕ → X := fun n => CanonicalProjection h n x
        have : Bornology.IsBounded (Set.range f) := by
           exact Metric.isBounded_range_of_tendsto _ (id_eq_limit h x )
        have : ∃ M : ℝ, ∀ x ∈ Set.range f, ‖x‖ ≤ M :=
            isBounded_iff_forall_norm_le.mp  this
        rcases this with ⟨M, hM⟩
        use M
        rintro n
        specialize hM (CanonicalProjection h n x) (Set.mem_range_self n)
        exact hM )


def basis_constant {e : ℕ → X} (h : SchauderBasis 𝕜 X e) : ℝ :=
    sInf { C : ℝ | ∀ n : ℕ, ‖CanonicalProjections h n‖ ≤ C }


theorem basis_of_canonical_projections {P : ℕ → X →L[𝕜] X}
    (hdim : ∀ n : ℕ, Module.finrank 𝕜 (range (P n)) = n + 1)
    (hcomp : ∀ m n : ℕ, P n ∘ P m = P (min n m))
    (lim : ∀ x : X, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    ∃ e : ℕ → X, SchauderBasis 𝕜 X e := by
        let V: ℕ → Submodule 𝕜 X := fun n => range (P (n+1)) ⊓ ker (P n)
        let a: (n : ℕ) → V n := sorry
        let e: ℕ → X := fun n => a n
        use e

        -- define functionals from rank one operators
        let b: (n : ℕ) → {f: StrongDual 𝕜 X | ∀ x:X, f x • e n = (P (n+1) - P n) x}:= fun n =>
            match n with
            | 0 => sorry
            | n + 1 => sorry
        let bf: ℕ → StrongDual 𝕜 X := fun n => b n
        use bf
        have a: ∀ n, (bf n) (e n) = 1 ∧ ∀ (m : ℕ), m ≠ n → (bf n) (e m) = 0 := sorry
        have b: ∀ (x : X), (Summable fun n ↦ (bf n) x • e n) ∧
            ∑' (n : ℕ), (bf n) x • e n = x := sorry

        exact ⟨ a, b ⟩


         -- let e : {e: ℕ → X | } :=
        --     fun n => by
        --     match n with
        --     -- there is some magic happening when reinterpreting v as elem in X
        --     | 0 => let v := Classical.choose (finrank_eq_one_iff'.mp (hdim 0)); use v
        --     | n + 1 =>
        --         let U := range (P n)
        --         let V := range (P (n+1))
        --         have : U ≤ V := sorry
        --         have : ¬U ≤ V := sorry
        --         have : ∃ v ∈ V, v ∉ U := sorry
        --         exact Classical.choose this

end CanonicalProjections

end SchauderBasis
