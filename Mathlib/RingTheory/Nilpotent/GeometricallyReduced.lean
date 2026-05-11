/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Geometrically reduced algebras

In this file we introduce geometrically reduced algebras.
For a commutative ring `R` and `R`-algebra `A`, we say that `A` is geometrically reduced
(`IsGeometricallyReduced`) if for every prime ideal `p` of `R`, the base change of `A`
to an algebraic closure of `κ(p)` is reduced.
In the case of `R = k` a field, this is equivalent to `AlgebraicClosure k ⊗[k] A` being reduced.

## Main results
- `IsGeometricallyReduced.of_forall_fg`: for a field `k` and a commutative `k`-algebra `A`, if all
  finitely generated subalgebras `B` of `A` are geometrically reduced, then `A` is geometrically
  reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent (see TODO).

## TODO
- Prove that if `A` is a geometrically reduced `R`-algebra, then for every `R`-algebra `K` that is
  a field, the tensor product `K ⊗[R] A` is reduced. (@Thmoas-Guan)

-/

public section

open TensorProduct

noncomputable section

namespace Algebra

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- An `R`-algebra `A` is geometrically reduced iff for every prime ideal `p` of R`
  the base change to `AlgebraicClosure p.ResidueField` is reduced. -/
@[mk_iff]
class IsGeometricallyReduced (R A : Type*) [CommRing R] [Ring A] [Algebra R A] : Prop where
  isReduced_algebraicClosure_residueField_tensorProduct (p : Ideal R) [p.IsPrime] :
  IsReduced (AlgebraicClosure p.ResidueField ⊗[R] A)

attribute [instance] IsGeometricallyReduced.isReduced_algebraicClosure_residueField_tensorProduct

section Field

lemma isGeometricallyReduced_field_iff (k A : Type*) [Field k] [Ring A] [Algebra k A] :
    IsGeometricallyReduced k A ↔ IsReduced (AlgebraicClosure k ⊗[k] A) := by
  let e (p : Ideal k) [p.IsPrime] : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure p.ResidueField :=
    have := p.AlgEquivResidueFieldOfField.isAlgebraic
    IsAlgClosure.equiv k _ _
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ⟨fun p hp ↦ ?_⟩⟩
  · exact isReduced_of_injective _ (Algebra.TensorProduct.congr (e ⊥) AlgEquiv.refl).injective
  · exact isReduced_of_injective _ (Algebra.TensorProduct.congr (e p).symm AlgEquiv.refl).injective

instance (k A K : Type*) [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsGeometricallyReduced k A] : IsReduced (K ⊗[k] A) := by
  have := (isGeometricallyReduced_field_iff k A).mp ‹_›
  exact isReduced_of_injective
    (Algebra.TensorProduct.map ((IsAlgClosed.lift : K →ₐ[k] AlgebraicClosure k)) 1)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _))

lemma IsGeometricallyReduced.of_injective {B : Type*} [Ring B] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A := by
  have := (isGeometricallyReduced_field_iff k B).mp ‹_›
  rw [isGeometricallyReduced_field_iff]
  exact isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)

variable (k) in
theorem isReduced_of_isGeometricallyReduced [IsGeometricallyReduced k A] : IsReduced A :=
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] (AlgebraicClosure k) ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective <| FaithfulSMul.algebraMap_injective _ _)

/-- If all finitely generated subalgebras of `A` are geometrically reduced, then `A` is
  geometrically reduced. -/
@[stacks 030T]
theorem IsGeometricallyReduced.of_forall_fg
    (h : ∀ B : Subalgebra k A, B.FG → IsGeometricallyReduced k B) :
    IsGeometricallyReduced k A := by
  simp_rw [isGeometricallyReduced_field_iff] at h ⊢
  exact IsReduced.tensorProduct_of_flat_of_forall_fg h

end Field

end Algebra
