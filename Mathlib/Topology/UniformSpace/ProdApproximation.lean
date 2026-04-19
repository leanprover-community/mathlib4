/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Separation.DisjointCover

/-!
# Uniform approximation by products

We show that if `X, Y` are compact Hausdorff spaces with `X` profinite, then any continuous function
on `X × Y` valued in a ring (with a uniform structure) can be uniformly approximated by finite
sums of functions of the form `f x * g y`.
-/

public section

open UniformSpace

open scoped Uniformity

namespace ContinuousMap

variable {X Y R V : Type*}
  [TopologicalSpace X] [TotallyDisconnectedSpace X] [T2Space X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y]
  [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] {S : Set (V × V)}

/-- A continuous function on `X × Y`, taking values in an `R`-module with a uniform structure,
can be uniformly approximated by sums of functions of the form `(x, y) ↦ f x • g y`.

Note that no continuity properties are assumed either for multiplication on `R`, or for the scalar
multiplication of `R` on `V`. -/
lemma exists_finite_sum_smul_approximation_of_mem_uniformity [TopologicalSpace R]
    [MonoidWithZero R] [MulActionWithZero R V] (f : C(X × Y, V)) (hS : S ∈ 𝓤 V) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, V)),
    ∀ x y, (f (x, y), ∑ i, g i x • h i y) ∈ S := by
  have hS' : {(f, g) | ∀ y, (f y, g y) ∈ S} ∈ 𝓤 C(Y, V) :=
    (mem_compactConvergence_entourage_iff _).mpr
      ⟨_, _, isCompact_univ, hS, by simp only [Set.mem_univ, true_implies, subset_refl]⟩
  obtain ⟨n, U, v, hv⟩ := exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal
    f.curry (nhdsSet_diagonal_le_uniformity hS')
  refine ⟨n, fun i ↦ ⟨_, (U i).isClopen.continuous_indicator <| continuous_const (y := 1)⟩,
    v, fun x y ↦ ?_⟩
  convert hv x y using 2
  simp only [sum_apply]
  congr 1 with i
  by_cases hi : x ∈ U i <;> simp [hi]

/-- A continuous function on `X × Y`, taking values in a ring `R` equipped with a uniformity
compatible with addition, can be uniformly approximated by sums of functions of the form
`(x, y) ↦ f x * g y`.

Note that no assumption is needed relating the multiplication on `R` to the uniformity. -/
lemma exists_finite_sum_mul_approximation_of_mem_uniformity [Ring R] [UniformSpace R]
    [IsUniformAddGroup R] (f : C(X × Y, R)) {S : Set (R × R)} (hS : S ∈ 𝓤 R) :
    ∃ (n : ℕ) (g : Fin n → C(X, R)) (h : Fin n → C(Y, R)),
    ∀ x y, (f (x, y), ∑ i, g i x * h i y) ∈ S :=
  exists_finite_sum_smul_approximation_of_mem_uniformity f hS

section prodMul

open scoped TensorProduct

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The natural bilinear map sending `f, g` to the function `(x, y) ↦ f x * g y` on `X × Y`. -/
def prodMul : C(X, R) →ₗ[R] C(Y, R) →ₗ[R] C(X × Y, R) :=
  LinearMap.mk₂ R (fun f g ↦ (f.comp .fst) * (g.comp .snd))
    (fun f f' g ↦ by ext; simp [add_mul])
    (fun r f g ↦ by ext; simp)
    (fun f g g' ↦ by ext; simp [mul_add])
    (fun r f g ↦ by ext; simp)

@[simp] lemma prodMul_apply (f : C(X, R)) (g : C(Y, R)) (p : X × Y) :
    f.prodMul g p  = f p.1 * g p.2 :=
  (rfl)

lemma prodMul_def (f : C(X, R)) (g : C(Y, R)) :
    f.prodMul g  = f.comp .fst * g.comp .snd :=
  (rfl)

/-- Tensor product version of `ContinuousMap.prodMul`. -/
@[expose] def tensorHom : C(X, R) ⊗[R] C(Y, R) →ₗ[R] C(X × Y, R) :=
  TensorProduct.lift prodMul

lemma denseRange_tensorHom [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace X] :
    DenseRange (tensorHom : C(X, R) ⊗[R] C(Y, R) → C(X × Y, R)) := by
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  intro f
  simp_rw [mem_closure_iff, Set.nonempty_def]
  intro U hUo hUf
  have := mem_nhds_uniformity_iff_right.mp (hUo.mem_nhds hUf)
  obtain ⟨J, hJu, hJ'⟩ := (hasBasis_compactConvergenceUniformity_of_compact).mem_iff.mp this
  obtain ⟨n, g, h, hgh⟩ := exists_finite_sum_mul_approximation_of_mem_uniformity f hJu
  have hG := Set.mem_of_subset_of_mem hJ' (a := (f, tensorHom <| ∑ i, g i ⊗ₜ h i))
  simp only [Prod.forall, Set.mem_setOf_eq, forall_const] at hG
  simpa using ⟨_, hG <| by simpa [tensorHom] using hgh⟩

end prodMul

end ContinuousMap
