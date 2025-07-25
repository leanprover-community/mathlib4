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
- `all_FG_geometricallyReduced_isGeometricallyReduced`: if all finitely generated subalgebras of `A`
  are geometrically reduced, then `A` is geometrically reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent.

-/

open TensorProduct

noncomputable section
variable (k : Type) (A : Type) [Field k] [CommRing A] [Algebra k A]
variable (B : Type) [CommRing B] [Algebra k B]


/-- The k-algebra A is geometrically reduced iff its basechange to AlgebraicClosure k is reduced -/
@[mk_iff]
class IsGeometricallyReduced : Prop where
  baseChangeReduced : IsReduced ((AlgebraicClosure k) ⊗[k] A)

theorem IsGeometricallyReduced_imp_baseChange_by_closure_Reduced (h : IsGeometricallyReduced k A) :
    IsReduced ((AlgebraicClosure k) ⊗[k] A) := by
    exact h.baseChangeReduced

lemma isGeometricallyReduced_of_injective (B : Type) [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A := by
  have hfK : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure k) (AlgebraicClosure k)) f) := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    exact hf
  expose_names
  rw [isGeometricallyReduced_iff] at *
  exact isReduced_of_injective (Algebra.TensorProduct.map 1 f) hfK


theorem isGeometricallyReduced_isReduced [IsGeometricallyReduced k A] : IsReduced A := by
  -- We prove this by providing an injection A →ₐ[k] A ⊗[k] AlgebraicClosure k and then
  -- applying isReduced_of_injective
  let f : A →ₐ[k] (AlgebraicClosure k) ⊗[k] A := Algebra.TensorProduct.includeRight
  expose_names
  rw [isGeometricallyReduced_iff] at inst_3
  have hf : Function.Injective f := by
    apply Algebra.TensorProduct.includeRight_injective
    exact FaithfulSMul.algebraMap_injective k (AlgebraicClosure k)
  exact isReduced_of_injective f hf

lemma notReduced_has_nilpotent {R : Type} [Zero R] [Pow R ℕ] (h : ¬IsReduced R) :
    ∃ x : R, x ≠ 0 ∧ IsNilpotent x := by
  by_contra h_contra
  simp only [ne_eq, not_exists, not_and] at h_contra
  simp only [isReduced_iff, not_forall] at h
  obtain ⟨x, ⟨hNil, hx⟩⟩ := h
  tauto

/-- Given a subalgebra C of a k-algebra A, and a k-algebra B, the basechange of C to a subalgebra
of A ⊗[k] B -/
def subAlgebraBaseChange (C : Subalgebra k A) : Subalgebra B (B ⊗[k] A) :=
  AlgHom.range (Algebra.TensorProduct.map (AlgHom.id B B) C.val)

lemma FGsubalgebra_baseChange_of_element (x : A ⊗[k] B) :
    ∃ C : Subalgebra k B , C.FG ∧ x ∈ subAlgebraBaseChange k B A C := by
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  let S1 := Set.image (fun j ↦ j.2) S.toSet
  let C := Algebra.adjoin k S1
  use C
  constructor
  · rw [Subalgebra.fg_def]
    use S1
    refine ⟨?_, rfl⟩
    exact Set.Finite.image (fun j ↦ j.2) (Finset.finite_toSet S)
  · rw [hS]
    refine Subalgebra.sum_mem _ ?_
    intro s hs
    have hCS : ∀ i ∈ S, i.2 ∈ C := by
      intro i hi
      apply SetLike.mem_of_subset
      · apply Algebra.subset_adjoin
      · use i
        exact ⟨hi, rfl⟩
    use s.1 ⊗ₜ[k] ⟨s.2, hCS s hs⟩
    rfl

-- If all finitely generated subalgebras of A are geometrically reduced, then A is geometrically
-- reduced. The result is in https://stacks.math.columbia.edu/tag/030T
theorem all_FG_geometricallyReduced_isGeometricallyReduced
    (h : ∀ B : Subalgebra k A, B.FG → IsGeometricallyReduced k B) :
    IsGeometricallyReduced k A := by
  by_contra h_contra
  rw [isGeometricallyReduced_iff] at *
  apply notReduced_has_nilpotent at h_contra
  obtain ⟨x, hx⟩ := h_contra
  obtain ⟨C, hC⟩ := FGsubalgebra_baseChange_of_element _ _ _ x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id (AlgebraicClosure k) (AlgebraicClosure k) ) C.val) := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    exact (AlgHom.injective_codRestrict C.val C Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
  have hy : ∃ y : ((AlgebraicClosure k) ⊗[k] C), y ≠ 0 ∧ IsNilpotent y := by
    rw [subAlgebraBaseChange, AlgHom.mem_range] at hC
    obtain ⟨z, hz⟩ := hC.2
    use z
    rw [← hz] at hx
    constructor
    · by_contra h_contra
      rw [h_contra] at hx
      tauto
    · exact (IsNilpotent.map_iff h_inj).mp hx.right
  obtain ⟨y, hy⟩ := hy
  have h_notReduced : ¬IsGeometricallyReduced k C := by
    rw [isGeometricallyReduced_iff, isReduced_iff, not_forall]
    use y
    tauto
  tauto
