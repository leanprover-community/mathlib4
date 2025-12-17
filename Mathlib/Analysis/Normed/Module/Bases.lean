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

@[expose] public section

noncomputable section

universe u


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]


variable (𝕜 X) in
/-- A Schauder basis is a sequence (e n) such that every element x of the space can be uniquely
represented as a convergent series x = ∑' n, a n • e n for some coefficients a n in the field 𝕜. -/
def SchauderBasis (e : ℕ → X) : Prop :=
    (∀ x : X, ∃! a : ℕ → 𝕜, Summable (fun n => a n • e n)  ∧ ∑' n, a n • e n = x)

namespace SchauderBasis

def coeff {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) : ℕ → 𝕜 :=
    (Classical.choose (h x))

def repr {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) : X :=
    ∑' n, (coeff h x n) • e n

omit [IsRCLikeNormedField 𝕜]
@[simp]
theorem repr_self {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) :
    repr h x = x := (Classical.choose_spec (h x)).1.2

theorem summable_coeff {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) :
    Summable (fun n => (coeff h x n) • e n) := (Classical.choose_spec (h x)).1.1

omit [IsRCLikeNormedField 𝕜]
@[simp]
theorem coeff_unique {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x : X) (a : ℕ → 𝕜)
    (hax : Summable (fun n => a n • e n) ∧ ∑' n, a n • e n = x) : a = coeff h x :=
    (Classical.choose_spec (h x)).2 a hax

theorem coeff_eq_zero_of_zero {e : ℕ → X} (h : SchauderBasis 𝕜 X e) :
    coeff h (0 : X) = 0 := by
    have szero : Summable (fun n => (0 : 𝕜) • e n) := by
        simp [summable_zero]
    have : ∑' n, (0 : 𝕜) • e n = (0 : X) := by
        simp [tsum_zero]
    rw [coeff_unique h (0 : X) 0 ⟨szero, this⟩]

theorem coeff_add {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (x y : X) :
    coeff h (x + y) = coeff h x + coeff h y := by
    let a: ℕ → 𝕜 := coeff h x
    let b: ℕ → 𝕜 := coeff h y
    have apbsum : Summable (fun n => (a n + b n) • e n) := by
        rw [summable_congr fun n => by rw [add_smul (a n) (b n) (e n)]]
        exact Summable.add (summable_coeff h x) (summable_coeff h y)
    have : ∑' n, (a n + b n) • e n = x + y := by
        calc
            ∑' n, (a n + b n) • e n = ∑' n, (a n • e n + b n • e n) :=
                tsum_congr fun n => by simp only [add_smul]
            _ = ∑' n, a n • e n + ∑' n, b n • e n := Summable.tsum_add ?_ ?_
            _ = repr h x + repr h y := by dsimp [repr]
            _ = x + y := by rw [repr_self h x, repr_self h y]
        · exact summable_coeff h x
        · exact summable_coeff h y
    apply Eq.symm
    exact coeff_unique h (x + y) (fun n => a n + b n) ⟨apbsum, this⟩

theorem coeff_smul {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (c : 𝕜) (x : X) :
    coeff h (c • x) = fun n => c * coeff h x n := by
    let a: ℕ → 𝕜 := coeff h x
    have casum : Summable (fun n => (c * a n) • e n) := by
        rw [summable_congr fun n => by rw [mul_smul c (a n) (e n)]]
        exact Summable.const_smul c (summable_coeff h x)
    have : ∑' n, (c * a n) • e n = c • x := by
        calc
            ∑' n, (c * a n) • e n = ∑' n, c • (a n • e n) := tsum_congr fun n => by
                simp only [smul_smul]
            _ = c • ∑' n, (a n • e n) := by
                rw [Summable.tsum_const_smul]
                exact summable_coeff h x
            _ = c • repr h x := by dsimp [repr]
            _ = c • x := by rw [repr_self h x]
    apply Eq.symm
    rw [coeff_unique h (c • x) (fun n => c * a n) ⟨casum, this⟩]


/-- A canonical projection associated to a Schauder basis. -/
def CanonicalProjections {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (P : ℕ → X →L[𝕜] X) : Prop  :=
    (∀ n : ℕ, ∀ x: X, (P n x = ∑ i ∈ Finset.range n, (coeff h x i) • e i))

namespace CanonicalProjections

open Filter Topology LinearMap

theorem dim_of_range {e : ℕ → X} (h : SchauderBasis 𝕜 X e) {P : ℕ → X →L[𝕜] X}
(hp : CanonicalProjections h P) (n : ℕ) : Module.finrank 𝕜 (range (P n)) = n := by
    sorry

theorem composition_eq_min {e : ℕ → X} (h : SchauderBasis 𝕜 X e) (m n : ℕ)
    {P : ℕ → X →L[𝕜] X} (hp : CanonicalProjections h P) :
     P n ∘ P m = P (min n m) := by
    sorry

theorem id_eq_limit {e : ℕ → X} (h : SchauderBasis 𝕜 X e)
    {P : ℕ → X →L[𝕜] X} (hp : CanonicalProjections h P) (x : X):
    Tendsto (fun n => P n x) atTop (𝓝 x) := by
    sorry

theorem basis_of_canonical_projections (P : ℕ → X →L[𝕜] X)
    (hdim : ∀ n : ℕ, Module.finrank 𝕜 (LinearMap.range (P n)) = n)
    (hcomp : ∀ m n : ℕ, P n ∘ P m = P (min n m))
    (lim : ∀ x : X, Tendsto (fun n => P n x) atTop (𝓝 x))
    (e : ℕ → X)
    (he1: e 1 ∈ range (P 1)) (hek : ∀ k : ℕ , e k ∈ range ( P k) ⊓ (ker (P (k - 1))))
    :
    SchauderBasis 𝕜 X e := by
    sorry


end CanonicalProjections

end SchauderBasis
