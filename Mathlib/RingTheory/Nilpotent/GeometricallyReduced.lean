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
if the tensor product `A ⊗[k] AlgebraicClosure k` is reduced.

## Main results
- `FlatBaseChangeIsReduced.of_FG`: if `k` is a commutative ring and `A` and `C` are `k`-algebras,
  such that `C ⊗[k] B` is reduced for all finitely generated `k` subalgebras `B` of `A`, then
  `C ⊗[k] A` is reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent.

-/

open TensorProduct

noncomputable section
variable {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A]

/-- The `k`-algebra `A` is geometrically reduced iff its base change to `AlgebraicClosure k` is
  reduced -/
@[mk_iff]
class IsGeometricallyReduced (k : Type*) (A : Type*) [Field k] [Ring A] [Algebra k A] : Prop where
  reduced_algebraicClosure_tensor : IsReduced ((AlgebraicClosure k) ⊗[k] A)

attribute [instance] IsGeometricallyReduced.reduced_algebraicClosure_tensor

instance (k : Type*) (A : Type*) [Field k] [Ring A] [Algebra k A] (K : Type) [Field K] [Algebra k K]
    [IsAlgClosure k K] [IsGeometricallyReduced k A] : IsReduced (K ⊗[k] A) :=
  isReduced_of_injective
    (Algebra.TensorProduct.map
      ((↑(IsAlgClosure.equiv k K (AlgebraicClosure k)) : K →ₐ[k] AlgebraicClosure k)) 1)
    (Module.Flat.rTensor_preserves_injective_linearMap _
      <| EquivLike.injective (IsAlgClosure.equiv k K (AlgebraicClosure k)))

lemma isGeometricallyReduced_of_injective {B : Type*} [Ring B] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A :=
  ⟨isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)⟩

theorem isReduced_of_isGeometricallyReduced [IsGeometricallyReduced k A] : IsReduced A :=
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] (AlgebraicClosure k) ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective <| FaithfulSMul.algebraMap_injective _ _)

-- If all finitely generated subalgebras of A are geometrically reduced, then A is geometrically
-- reduced. The result is in https://stacks.math.columbia.edu/tag/030T
theorem FlatBaseChangeIsReduced.of_FG {k : Type*} {A : Type*} {C : Type*} [CommRing A]
    [CommRing C] [CommRing k] [Algebra k A] [Algebra k C] [Module.Flat k C]
    (h : ∀ B : Subalgebra k A, B.FG → IsReduced (C ⊗[k] B)) :
    IsReduced (C ⊗[k] A) := by
  by_contra h_contra
  obtain ⟨x, hx⟩ := exists_isNilpotent_of_not_isReduced h_contra
  obtain ⟨D, hD⟩ := exists_fg_and_mem_baseChange x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id C C ) D.val) := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    exact (AlgHom.injective_codRestrict D.val D Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  rw [Subalgebra.baseChange, AlgHom.mem_range] at hD
  obtain ⟨z, hz⟩ := hD.2
  have h_notReduced : ¬IsReduced (C ⊗[k] D) := by
    rw [isReduced_iff, not_forall]
    use z
    rw [← hz] at hx
    refine not_imp_of_and_not ⟨(IsNilpotent.map_iff h_inj).mp hx.right, ?_⟩
    by_contra h_contra
    rw [h_contra] at hx
    tauto
  tauto
