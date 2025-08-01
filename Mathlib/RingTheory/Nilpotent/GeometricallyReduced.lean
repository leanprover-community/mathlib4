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
- `all_FG_geometricallyReduced_isGeometricallyReduced`: if `k` is a commutative ring and `A` and `C`
  are `k`-algebras, such that `C ⊗[k] B` is reduced for all finitely generated `k` subalgebras `B`
  of `A`, then `C ⊗[k] A` is reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent.

-/

open TensorProduct

noncomputable section
variable {k : Type} {A : Type} [Field k] [Ring A] [Algebra k A]

/-- The k-algebra A is geometrically reduced iff its basechange to AlgebraicClosure k is reduced -/
@[mk_iff]
class IsGeometricallyReduced (k : Type) (A : Type) [Field k] [Ring A] [Algebra k A] : Prop where
  reduced_algebraicClosure_tensor : IsReduced ((AlgebraicClosure k) ⊗[k] A)
attribute [instance] IsGeometricallyReduced.reduced_algebraicClosure_tensor


lemma geometricallyReduced_indep_of_algebraicClosure (k : Type) (A : Type) [Field k] [Ring A]
    [Algebra k A] (K : Type) [Field K] [Algebra k K] [IsAlgClosure k K]
    (h : IsGeometricallyReduced k A) : IsReduced (K ⊗[k] A) :=
  isReduced_of_injective
    (Algebra.TensorProduct.map
      ((↑(IsAlgClosure.equiv k K (AlgebraicClosure k)) : K →ₐ[k] AlgebraicClosure k)) 1)
    (Module.Flat.rTensor_preserves_injective_linearMap _
      <| EquivLike.injective (IsAlgClosure.equiv k K (AlgebraicClosure k)))

lemma isGeometricallyReduced_of_injective {B : Type} [Ring B] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A :=
  ⟨isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)⟩


theorem isGeometricallyReduced_isReduced [IsGeometricallyReduced k A] : IsReduced A :=
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] (AlgebraicClosure k) ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective <| FaithfulSMul.algebraMap_injective _ _)

lemma notReduced_has_nilpotent {R : Type} [Zero R] [Pow R ℕ] (h : ¬IsReduced R) :
    ∃ x : R, x ≠ 0 ∧ IsNilpotent x := by
  by_contra h_contra
  simp only [ne_eq, not_exists, not_and] at h_contra
  simp only [isReduced_iff, not_forall] at h
  obtain ⟨x, ⟨hNil, hx⟩⟩ := h
  tauto

/-- Given a subalgebra C of a k-algebra A, and a k-algebra B, the basechange of C to a subalgebra
of A ⊗[k] B -/
def subAlgebra.baseChange {A k : Type} [CommRing k] [Ring A] [Algebra k A] (B : Type) [CommRing B]
    [Algebra k B] (C : Subalgebra k A) : Subalgebra B (B ⊗[k] A) :=
  AlgHom.range (Algebra.TensorProduct.map (AlgHom.id B B) C.val)

lemma FGsubalgebra_baseChange_of_element {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (x : A ⊗[k] B) :
    ∃ C : Subalgebra k B, C.FG ∧ x ∈ subAlgebra.baseChange A C := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  classical
  refine ⟨Algebra.adjoin k (S.image fun j ↦ j.2), ?_, ?_⟩
  · exact Subalgebra.fg_adjoin_finset _
  · exact hS ▸ Subalgebra.sum_mem _ fun s hs ↦ ⟨s.1 ⊗ₜ[k] ⟨s.2, Algebra.subset_adjoin
      (Finset.mem_image_of_mem _ hs)⟩, rfl⟩

-- If all finitely generated subalgebras of A are geometrically reduced, then A is geometrically
-- reduced. The result is in https://stacks.math.columbia.edu/tag/030T
theorem all_FG_flatBaseChangeReduced_imp_baseChangeReduced {k A C : Type} [CommRing A] [CommRing C]
    [CommRing k] [Algebra k A] [Algebra k C] [Module.Flat k C]
    (h : ∀ B : Subalgebra k A, B.FG → IsReduced (C ⊗[k] B)) :
    IsReduced (C ⊗[k] A) := by
  by_contra h_contra
  obtain ⟨x, hx⟩ := notReduced_has_nilpotent h_contra
  obtain ⟨D, hD⟩ := FGsubalgebra_baseChange_of_element x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id C C ) D.val) := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    exact (AlgHom.injective_codRestrict D.val D Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  rw [subAlgebra.baseChange, AlgHom.mem_range] at hD
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
