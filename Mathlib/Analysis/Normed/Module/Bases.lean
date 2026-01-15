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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

-- TODO use (.) functions instead of fun => when possible

variable (𝕜 X) in
/-- A Schauder basis is a sequence (e n) such that every element x of the space can be uniquely
represented as a convergent series x = ∑' n, a n • e n for some coefficients a n in the field 𝕜. -/
def SchauderBasis (e : ℕ → X) : Prop :=
    ( ∃ f : ℕ → StrongDual 𝕜 X,
        (∀ n : ℕ, (f n (e n) = 1 ∧ (∀ m ≠ n, f n (e m) = 0))) ∧
        ∀ x : X, Summable (fun n => f n x • e n) ∧
        (∑' n, f n x • e n = x) )

namespace SchauderBasis

def biorthogonal_functionals {e : ℕ → X}
    (h : SchauderBasis 𝕜 X e) : ℕ → StrongDual 𝕜 X := Classical.choose h

omit [IsRCLikeNormedField 𝕜]
theorem biorthogonal_property {e : ℕ → X}
    (h : SchauderBasis 𝕜 X e) :
    ∀ n : ℕ, (biorthogonal_functionals h n (e n) = 1 ∧
        ∀ m ≠ n, biorthogonal_functionals h n (e m) = 0) :=
    (Classical.choose_spec h).1

omit [IsRCLikeNormedField 𝕜]
theorem linear_independent {e : ℕ → X} (h : SchauderBasis 𝕜 X e) :
  LinearIndependent 𝕜 e := by
    apply linearIndependent_iff.mpr
    rintro s hsum
    have hsum : ∑ n ∈ s.support, s n • e n = 0 := hsum
    apply Finsupp.support_eq_empty.mp
    by_contra hnonempty
    push_neg at hnonempty
    let n := Classical.choose hnonempty
    have hn: n ∈ s.support := Classical.choose_spec hnonempty
    have : s n ≠ 0 := Finsupp.mem_support_iff.mp hn
    let f := biorthogonal_functionals h n
    -- have fem: ∀ m, m ≠ n → f (e m) = 0 := fun m hm => ((Classical.choose_spec h).1 n).2 m hm
    have fsm0: ∀ m ∈ {m ∈ s.support | m ≠ n}, f (s m • e m) = 0 := by
        intro m hm
        calc
            f (s m • e m) = s m • f (e m) := by rw [ContinuousLinearMap.map_smul]
            _ = s m * f (e m) := by rw [smul_eq_mul]
            _ = s m * 0 := by rw
                [((biorthogonal_property h) n).2 m (by rw [Finset.mem_filter] at hm; exact hm.2)]
            _ = 0 := by rw [mul_zero]
    let ssuppn := s.support.filter (fun m => m = n)
    let ssuppnn := s.support.filter (fun m => m ≠ n)
    have fmsum0 : f (∑ m ∈ ssuppnn, s m • e m) = 0 := by
        calc
            f (∑ m ∈ ssuppnn, s m • e m) = ∑ m ∈ ssuppnn, f (s m • e m) := by rw [map_sum]
            _ = ∑ m ∈ ssuppnn, 0 := by exact Finset.sum_congr rfl fsm0
            _ = 0 := by rw [Finset.sum_const_zero]
    -- TODO make it a lemma
    have z: ssuppn = {n} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        constructor
        · exact Finset.mem_filter.mpr ⟨hn, rfl⟩
        · intro _ hm; exact (Finset.mem_filter.mp hm).2

    have : s n = 0 := by
        calc
            s n = s n * 1 := by rw [mul_one]
            _ = s n * f (e n) := by rw [((biorthogonal_property h) n).1]
            _ = s n • f (e n) := by rw [smul_eq_mul]
            _ = f (s n • e n) := by rw [<-map_smul]
            _ = f (∑ m ∈ {n}, s m • e m) := by rw [Finset.sum_singleton]
            _ = f (∑ m ∈ ssuppn, s m • e m) :=
                congrArg f (Finset.sum_congr z.symm fun _ _ => rfl)
            _ = f (∑ m ∈ ssuppn, s m • e m) + 0 := by rw [add_zero]
            _ = f (∑ m ∈ ssuppn, s m • e m) + f (∑ m ∈ ssuppnn, s m • e m) := by rw [fmsum0]
            _ = f ((∑ m ∈ ssuppn, s m • e m) + (∑ m ∈ ssuppnn, s m • e m)) := by
                rw [ContinuousLinearMap.map_add]
            _ = f (∑ m ∈ s.support, s m • e m) :=
                congrArg f (by rw [Finset.sum_filter_add_sum_filter_not])
            _ = f 0 := by rw [hsum]
            _ = 0 := ContinuousLinearMap.map_zero f
    contradiction

def coeff {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) : ℕ → 𝕜 :=
    fun n => biorthogonal_functionals h n x

theorem coeff_summable {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) :
        Summable (fun n => coeff h x n • e n) := ((Classical.choose_spec h).2 x).1

def repr {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) : X :=
    ∑' n, (coeff h x n) • e n

omit [IsRCLikeNormedField 𝕜]
@[simp]
theorem repr_self {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) :
    repr h x = x := by
    dsimp [repr, coeff]
    exact ((Classical.choose_spec h).2 x).2



/-- A canonical projection associated to a Schauder basis. -/
def CanonicalProjections {e : ℕ → X} (h : SchauderBasis 𝕜 X e) : ℕ → X →L[𝕜] X := by
    intro n
    -- TODO add lemma for constructing continuous linear maps from eval functionals smul vectors
    let hi: ℕ → X →L[𝕜] X := by
        intro i
        let linear_map: X →ₗ[𝕜] X :=
            { toFun := fun x => (biorthogonal_functionals h i x) • e i
              map_add' := by
                intros x y
                have : biorthogonal_functionals h i (x + y) =
                    biorthogonal_functionals h i x + biorthogonal_functionals h i y :=
                    LinearMap.map_add (biorthogonal_functionals h i).toLinearMap x y
                rw [this, add_smul]
              map_smul' := by
                intros c x
                dsimp -- ? why is dsimp needed here
                have : biorthogonal_functionals h i (c • x) =
                    c * biorthogonal_functionals h i x :=
                    LinearMap.map_smul (biorthogonal_functionals h i).toLinearMap c x
                rw [this, mul_smul]
                }
        exact LinearMap.mkContinuous
          linear_map
          (‖(biorthogonal_functionals h i)‖ * ‖e i‖)
          (by
            intro x
            calc
              ‖linear_map x‖ = ‖(biorthogonal_functionals h i x) • e i‖ := rfl
              _ = ‖biorthogonal_functionals h i x‖ * ‖e i‖ := norm_smul _ _
              _ ≤ ‖(biorthogonal_functionals h i)‖ * ‖x‖ * ‖e i‖ := by
                apply mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ x) (norm_nonneg _)
              _ = ‖(biorthogonal_functionals h i)‖ * ‖e i‖ * ‖x‖ := by ring)

    exact (Finset.range n).sum (fun i => hi i)

namespace CanonicalProjections

theorem bf_eval {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (i j : ℕ) :
    biorthogonal_functionals h i (e j) = if i = j then (1 : 𝕜) else 0 := by
    by_cases hij: i = j
    · rw [hij]
      simp only
      exact ((biorthogonal_property h) j).1
    · rw [if_neg hij]; push_neg at hij
      exact ((biorthogonal_property h) i).2 j hij.symm

theorem canonical_projection_on_basis_element {e : ℕ → X}
    (h : SchauderBasis 𝕜 X e) (n i : ℕ) :
    (CanonicalProjections h n) (e i) = if i < n then e i else 0 := by
    let bf := biorthogonal_functionals h
    have : (CanonicalProjections h n) (e i) = ∑ j ∈ Finset.range n, bf j (e i) • e j := by
        rw [CanonicalProjections]; simp [bf]
    rw [this]
    have hsum: (∑ j ∈ Finset.range n, bf j (e i) • e j) =
        ∑ j ∈ Finset.range n, (if j = i then (1 : 𝕜) else 0) • e j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [bf_eval h j i]
    rw [hsum]
    simp [Finset.sum_ite_eq']


theorem dim_of_range {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (n : ℕ) :
    Module.finrank 𝕜 (range (CanonicalProjections h n)) = n := by
    have einrange: ∀ i, i < n → e i ∈ range (CanonicalProjections h n) := by
        intro i hi
        let bf := biorthogonal_functionals h
         -- TODO make it a lemma
        have z: (Finset.range n).filter (fun j => j = i) = {i} := by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            constructor
            · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, rfl⟩
            · intro _ hm; exact (Finset.mem_filter.mp hm).2
        have : (CanonicalProjections h n) (e i) = e i := by
            rw [canonical_projection_on_basis_element h n i]
            simp [hi]
        exact ⟨e i, this⟩
    have basisofrange: range (CanonicalProjections h n) ≃ₗ[𝕜]
        Submodule.span 𝕜 ({ e i | i < n }) := by  sorry
    rw [LinearEquiv.finrank_eq basisofrange]
    have : Module.finrank 𝕜 (Submodule.span 𝕜 ({ e i | i < n })) = n := by sorry
    exact this


theorem composition_eq_min {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (m n : ℕ) :
    CanonicalProjections h n ∘ CanonicalProjections h m = CanonicalProjections h (min n m) := by
    ext x
    let bf := biorthogonal_functionals h
    have hinner: ∀ i j : ℕ, (bf i (bf j x • e j)) • e i = if i = j then (bf j x) • e i else 0 := by
        intro i j
        rw [ContinuousLinearMap.map_smul]
        by_cases hij : i = j
        · rw [hij]; rw [bf_eval h j j]; simp
        · rw [bf_eval h i j]; simp
    calc
        (CanonicalProjections h n ∘ CanonicalProjections h m) x
            = CanonicalProjections h n (CanonicalProjections h m x) := by simp
        _ = ∑ i ∈ Finset.range n, bf i (CanonicalProjections h m x) • e i := by
            rw [CanonicalProjections]; simp [bf]
        _ = ∑ i ∈ Finset.range n, bf i (∑ j ∈ Finset.range m, bf j x • e j) • e i := by
            rw [CanonicalProjections]; simp [bf]
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
        _ = CanonicalProjections h (min n m) x := by rw [CanonicalProjections]; simp [bf]

theorem id_eq_limit {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) :
    Tendsto (fun n => CanonicalProjections h n x) atTop (𝓝 x) := by
    let bf := biorthogonal_functionals h
    have tndto : Tendsto (fun n => (∑ i ∈ Finset.range n, coeff h x i • e i))
        atTop (𝓝 (∑' n, bf n x • e n)) := HasSum.tendsto_sum_nat (coeff_summable h x).hasSum
    have r: ∑' (n : ℕ), (bf n) x • e n = x := by
        nth_rw 2 [<-repr_self h x]
        dsimp [repr, coeff]
    rw [r] at tndto
    have p: ∀ n, ∑ i ∈ Finset.range n, h.coeff x i • e i = (h.CanonicalProjections n) x := by
        dsimp [CanonicalProjections, coeff]
        simp
    exact Filter.Tendsto.congr p tndto

variable [CompleteSpace X]
-- todo clean up proof
theorem uniform_bound {e : ℕ → X} (h : SchauderBasis 𝕜 X e) :
    ∃ C : ℝ, ∀ n : ℕ, ‖CanonicalProjections h n‖ ≤ C := by
    exact banach_steinhaus (by
        intro x
        let f: ℕ → X := fun n => CanonicalProjections h n x
        have : Bornology.IsBounded (Set.range f) := by
           exact Metric.isBounded_range_of_tendsto _ (id_eq_limit h x )
        have : ∃ M : ℝ, ∀ x ∈ Set.range f, ‖x‖ ≤ M :=
            isBounded_iff_forall_norm_le.mp  this
        rcases this with ⟨M, hM⟩
        use M
        rintro n
        specialize hM (CanonicalProjections h n x) (Set.mem_range_self n)
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
