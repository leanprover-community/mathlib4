import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorField.Pullback

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

noncomputable def verticalSubspace (v : TotalSpace F V) :
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
