import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.MemFG

open TensorProduct FreeAddMonoid

universe u v

variable {R : Type u} [CommSemiring R] {S : Semiring S} [Algebra R S]
  {M N : Type*}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]


namespace Algebra.TensorProduct

open Submodule

theorem mem_map_subtype_of_exists_rTensor_FG (t : S ⊗[R] M) :
    ∃ S₀, Subalgebra.FG S₀ ∧ ∃ t₀ : S₀ ⊗[R] M,
      t = LinearMap.rTensor M (Subalgebra.val S₀).toLinearMap t₀ := by
  obtain ⟨P, hP, Q, _, ⟨t, rfl⟩⟩ := TensorProduct.mem_map_subtype_of_exists_FG t
  obtain ⟨s, hs⟩ := hP
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P ≤ Subalgebra.toSubmodule (Algebra.adjoin R (s : Set S)) := by
    simp only [← hs, span_le, coe_toSubmodule]
    exact Algebra.subset_adjoin
  use TensorProduct.map (Submodule.inclusion this) (Submodule.subtype Q) t
  simp only [LinearMap.rTensor]
  apply congr_fun
  change _ = (TensorProduct.map _ _) ∘ (TensorProduct.map _ _)
  rw [← LinearMap.coe_comp, ← TensorProduct.map_comp]
  apply congr_arg₂ _ rfl
  apply congr_arg₂ _ rfl
  simp only [LinearMap.id_comp]
