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
        (∀ n : ℕ, f n (e n) = 1 ∧ ∀ m ≠ n, f n (e m) = 0) ∧
        ∀ x : X, Summable (fun n => f n x • e n) ∧
        (∑' n, f n x • e n = x) )

namespace SchauderBasis

def biorthogonal_functionals {e : ℕ → X}
    (h : SchauderBasis 𝕜 X e) : ℕ → StrongDual 𝕜 X := Classical.choose h

def coeff {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) : ℕ → 𝕜 :=
    fun n => biorthogonal_functionals h n x

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
    sorry

theorem composition_eq_min {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (m n : ℕ) :
    CanonicalProjections h n ∘ CanonicalProjections h m = CanonicalProjections h (min n m) := by
    sorry

theorem id_eq_limit {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) :
    Tendsto (fun n => CanonicalProjections h n x) atTop (𝓝 x) := by
    sorry

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
    (hdim : ∀ n : ℕ, Module.finrank 𝕜 (range (P n)) = n)
    (hcomp : ∀ m n : ℕ, P n ∘ P m = P (min n m))
    (lim : ∀ x : X, Tendsto (fun n => P n x) atTop (𝓝 x))
    {e : ℕ → X}(he1: e 1 ∈ range (P 1)) (hek : ∀ k : ℕ , e k ∈ range ( P k) ⊓ (ker (P (k - 1)))) :
    SchauderBasis 𝕜 X e := by
    sorry

end CanonicalProjections





variable (𝕜 X) in
/-- A basic sequence is a sequence (e n) such that e is a Schauder basis for
    the closedlinear span of (e n). -/
def BasicSequence (e : ℕ → X) : Prop :=
    SchauderBasis 𝕜
    (Submodule.topologicalClosure (Submodule.span 𝕜 (Set.range e)))
    (fun n => ⟨e n, by
        apply Submodule.closure_subset_topologicalClosure_span
        apply subset_closure
        exact Set.mem_range_self n⟩)

namespace BasicSequence

theorem grunblum_criterion {e : ℕ → X} (K : ℝ) (hC : 1 < K)
    (h : ∀ n : ℕ, ∀ m : ℕ, m ≤ n → ∀ a : ℕ → 𝕜,
        ‖∑ i ∈ Finset.range m, a i • e i‖ ≤ K * ‖∑ i ∈ Finset.range n, a i • e i‖) :
    BasicSequence 𝕜 X e := by
    sorry

theorem basic_sequence_of_infinite_dim : ¬FiniteDimensional 𝕜 X →
    ∃ e : ℕ → X, BasicSequence 𝕜 X e := by
    sorry

lemma exists_perpendicular_vector (S : Set (WeakDual 𝕜 X)) (h0w : 0 ∈ closure S)
    (h0ns : 0 ∉ closure (WeakDual.toStrongDual '' S)) :
     ∃ x : X, ∀ f ∈ S, f.toLinearMap x = 0 := by
    sorry



end BasicSequence

end SchauderBasis
