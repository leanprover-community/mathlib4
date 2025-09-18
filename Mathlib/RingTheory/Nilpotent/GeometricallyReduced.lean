/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Henselian

/-!
# Geometrically reduced algebras

In this file we introduce geometrically reduced algebras.
For a field `k`, we say that a `k`-algebra `A` is geometrically reduced (`IsGeometricallyReduced`)
if the tensor product `AlgebraicClosure k ⊗[k] A` is reduced.

## Main results
- `IsReduced.tensor_of_flat_of_forall_fg`: if `R` is a commutative semiring and `A` and `C` are
  `R`-algebras, such that `C ⊗[R] B` is reduced for all finitely generated `R` subalgebras `B` of
  `A`, then `C ⊗[R] A` is reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent.

-/

open TensorProduct

noncomputable section
variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The `k`-algebra `A` is geometrically reduced iff its base change to `AlgebraicClosure k` is
  reduced -/
@[mk_iff]
class IsGeometricallyReduced (k A : Type*) [Field k] [Ring A] [Algebra k A] : Prop where
  reduced_algebraicClosure_tensor : IsReduced ((AlgebraicClosure k) ⊗[k] A)

attribute [instance] IsGeometricallyReduced.reduced_algebraicClosure_tensor

instance (k A K : Type*) [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsGeometricallyReduced k A] : IsReduced (K ⊗[k] A) :=
  isReduced_of_injective
    (Algebra.TensorProduct.map ((IsAlgClosed.lift : K →ₐ[k] AlgebraicClosure k)) 1)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _))

lemma isGeometricallyReduced_of_injective {B : Type*} [Ring B] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A :=
  ⟨isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)⟩

variable (k) in
theorem isReduced_of_isGeometricallyReduced [IsGeometricallyReduced k A] : IsReduced A :=
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] (AlgebraicClosure k) ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective <| FaithfulSMul.algebraMap_injective _ _)

-- If all finitely generated subalgebras of A are geometrically reduced, then A is geometrically
-- reduced. The result is in https://stacks.math.columbia.edu/tag/030T
@[stacks 030T]
theorem IsReduced.tensor_of_flat_of_forall_fg {R C A : Type*}
    [CommSemiring R] [CommSemiring C] [Semiring A] [Algebra R A] [Algebra R C] [Module.Flat R C]
    (h : ∀ B : Subalgebra R A, B.FG → IsReduced (C ⊗[R] B)) :
    IsReduced (C ⊗[R] A) := by
  by_contra h_contra
  obtain ⟨x, hx⟩ := exists_isNilpotent_of_not_isReduced h_contra
  obtain ⟨D, hD⟩ := exists_fg_and_mem_baseChange x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id C C ) D.val) := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    exact (AlgHom.injective_codRestrict D.val D Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  obtain ⟨z, rfl⟩ := hD.2
  have h_notReduced : ¬IsReduced (C ⊗[R] D) := by
    simp_rw [isReduced_iff, not_forall]
    exact ⟨z, (IsNilpotent.map_iff h_inj).mp hx.right, (by simpa [·] using hx.1)⟩
  tauto
