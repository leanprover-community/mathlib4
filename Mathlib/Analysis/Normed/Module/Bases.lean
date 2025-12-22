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
theorem linear_independent {e : ℕ → X} (h : SchauderBasis 𝕜 X e) :
  LinearIndependent 𝕜 e := by
    apply linearIndependent_iff.mpr
    rintro s hsum
    have hsum : ∑ n ∈ s.support, s n • e n = 0 := hsum
    apply Finsupp.support_eq_empty.mp
    by_contra hnonempty
    push_neg at hnonempty
    let n := Classical.choose hnonempty
    have : s n ≠ 0 := Finsupp.mem_support_iff.mp (Classical.choose_spec hnonempty)
    let f := biorthogonal_functionals h n
    have fen: f (e n) = 1 := by exact ((Classical.choose_spec h).1 n).1
    have fem: ∀ m, m ≠ n → f (e m) = 0 := fun m hm => ((Classical.choose_spec h).1 n).2 m hm
    have fsm0: ∀ m ∈ {m ∈ s.support | m ≠ n}, f (s m • e m) = 0 := by
        intro m hm
        calc
            f (s m • e m) = s m • f (e m) := by rw [ContinuousLinearMap.map_smul]
            _ = s m * f (e m) := by rw [smul_eq_mul]
            _ = s m * 0 := by rw [fem m (by rw [Finset.mem_filter] at hm; exact hm.2)]
            _ = 0 := by rw [mul_zero]
    let ssuppn := s.support.filter (fun m => m = n)
    let ssuppnn := s.support.filter (fun m => m ≠ n)
    have fmsum0 : f (∑ m ∈ ssuppnn, s m • e m) = 0 := by
        calc
            f (∑ m ∈ ssuppnn, s m • e m) = ∑ m ∈ ssuppnn, f (s m • e m) := by rw [map_sum]
            _ = ∑ m ∈ ssuppnn, 0 := by exact Finset.sum_congr rfl fsm0
            _ = 0 := by rw [Finset.sum_const_zero]
    have z: {n} = ssuppn := by -- TODO use Set.setOf_eq_eq_singleton
        ext m
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro h
          have : m ∈ s.support := by
                rw [h]
                exact Classical.choose_spec hnonempty
          exact ⟨this, h⟩
        · intro h
          exact h.2
    have : s n = 0 := by
        calc
            s n = s n * 1 := by rw [mul_one]
            _ = s n * f (e n) := by rw [fen]
            _ = s n • f (e n) := by rw [smul_eq_mul]
            _ = f (s n • e n) := by rw [<-map_smul]
            _ = f (∑ m ∈ {n}, s m • e m) := by rw [Finset.sum_singleton]
            _ = f (∑ m ∈ ssuppn, s m • e m) :=
                congrArg f (Finset.sum_congr z fun _ _ => rfl)
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

variable [CompleteSpace X]

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
    exact ∑ i : Finset.range n, hi i

namespace CanonicalProjections

theorem dim_of_range {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (n : ℕ) :
    Module.finrank 𝕜 (range (CanonicalProjections h n)) = n := by
    have einrange: ∀ i, i < n → e i ∈ range (CanonicalProjections h n) := by
        intro i hi
        let bf := biorthogonal_functionals h
        have : CanonicalProjections h n (e i) = e i := by
            have : i ∈ Finset.range n := by sorry
            calc
              CanonicalProjections h n (e i) = ∑ j : Finset.range n, (bf j (e i)) • e j :=   by sorry
              _ =  ∑ j : Finset.range n, if j = i then 1 • e j else 0 • e j := by sorry
              _ = 1 • e i := by sorry
              _ = e i := by rw [one_smul]

        exact ⟨e i, this⟩
    have basisofrange: range (CanonicalProjections h n) ≃ₗ[𝕜] Submodule.span 𝕜 ({ e i | i < n }) := by  sorry
    rw [LinearEquiv.finrank_eq basisofrange]
    have : Module.finrank 𝕜 (Submodule.span 𝕜 ({ e i | i < n })) = n := by sorry
    exact this

theorem composition_eq_min {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (m n : ℕ) :
    CanonicalProjections h n ∘ CanonicalProjections h m = CanonicalProjections h (min n m) := by
    ext x
    dsimp [CanonicalProjections]
    have bf := biorthogonal_functionals h
    calc
        (CanonicalProjections h n ∘ CanonicalProjections h m) x
            = CanonicalProjections h n (∑ i ∈ Finset.range m, (bf i x) • e i) := by sorry
        _ = ∑ j ∈ Finset.range n, bf j (∑ i ∈ Finset.range m, (bf i x) • e i) • e j := by sorry
        _ = ∑ j ∈ Finset.range n, (if j < m then (bf j x) else 0) • e j := by sorry
        _ = ∑ j ∈ Finset.range (min n m), (bf j x) • e j := by sorry
        _ = CanonicalProjections h (min n m) x := by sorry

theorem id_eq_limit {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) :
    Tendsto (fun n => CanonicalProjections h n x) atTop (𝓝 x) := by

    let bf := biorthogonal_functionals h
    have tndto : Tendsto (fun n => (∑ i ∈ Finset.range n, coeff h x i • e i))
        atTop (𝓝 (∑' n, bf n x • e n)) := HasSum.tendsto_sum_nat (coeff_summable h x).hasSum
    have r: ∑' (n : ℕ), (bf n) x • e n = x := by
        nth_rw 2 [<-repr_self h x]
        dsimp [repr, coeff]
    rw [r] at tndto
    have p: ∀ n, ∑ i ∈ Finset.range n, h.coeff x i • e i = (h.CanonicalProjections n) x := by sorry
    exact Filter.Tendsto.congr p tndto

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

omit [CompleteSpace X]
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
