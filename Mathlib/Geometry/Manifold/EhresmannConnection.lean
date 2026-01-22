/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorField.Pullback

open scoped Manifold
open Bundle
open FiberBundle
open IsManifold
open scoped ModelWithCorners

variable {E_base : Type*} [NormedAddCommGroup E_base] [NormedSpace ℝ E_base]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E_base H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (n : WithTop ℕ∞)
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
variable [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
variable [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]

/-- The vertical subspace at a point `v` in the total space of a fiber bundle is the kernel
of the differential of the projection map. It consists of tangent vectors that are tangent to
the fiber through `v`. -/
public noncomputable def verticalSubspace (v : TotalSpace F V) :
    Submodule ℝ (TangentSpace (I.prod 𝓘(ℝ, F)) v) :=
  LinearMap.ker
    ((mfderiv (I.prod 𝓘(ℝ, F)) I TotalSpace.proj v).toLinearMap)

section EhresmannConnection

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*}
variable [TopologicalSpace (TotalSpace F E)]
variable [(b : M) → TopologicalSpace (E b)]
variable [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
variable [FiberBundle F E]
variable {n : ℕ}
variable {IM : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) M}
variable [IsManifold IM ⊤ M]
variable [ChartedSpace M (TotalSpace F E)]
variable [IsManifold (IM.prod 𝓘(ℝ, F)) ⊤ (TotalSpace F E)]

/-- An Ehresmann connection on a fiber bundle `E → M` is a smooth choice of horizontal subspace
at each point of the total space, complementary to the vertical subspace. The horizontal subspace
provides a notion of "horizontal lift" and allows parallel transport along curves in the base.

The connection is specified by:
- `horizontal e`: the horizontal subspace at each point `e` in the total space
- `complement`: the horizontal and vertical subspaces span the entire tangent space
- `disjoint`: the horizontal and vertical subspaces intersect trivially
- `smooth`: the horizontal distribution is smooth, given locally by a smooth frame of vector fields
-/
public
structure EhresmannConnection where
  horizontal : (e : TotalSpace F E) → Submodule ℝ (TangentSpace (IM.prod 𝓘(ℝ, F)) e)
  complement : ∀ e : TotalSpace F E,
    horizontal e ⊔ verticalSubspace e = ⊤
  disjoint : ∀ e : TotalSpace F E,
    horizontal e ⊓ verticalSubspace e = ⊥
  smooth : ∀ e₀ : TotalSpace F E, ∃ (U : Set (TotalSpace F E)) (d : ℕ)
    (X : Fin d → (e : TotalSpace F E) → TangentSpace (IM.prod 𝓘(ℝ, F)) e),
    e₀ ∈ U ∧
    IsLocalFrameOn (IM.prod 𝓘(ℝ, F)) (EuclideanSpace ℝ (Fin n) × F) ⊤ X U ∧
    (∀ e ∈ U, horizontal e = Submodule.span ℝ (Set.range (fun i => X i e)))

end EhresmannConnection
