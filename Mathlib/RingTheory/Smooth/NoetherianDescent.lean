/-
Copyright (c) 2025 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Smooth.Basic

/-!
# Smooth algebras have smooth, Noetherian representatives

In this file, we show if `S` is a smooth `R`-algebra, there exists a `ℤ`-subalgebra of finite type
`R₀` such that `S ≃ₐ R ⊗[R₀] S₀` where `S₀` is a model.f `
-/

universe u

open TensorProduct MvPolynomial

namespace Algebra.Smooth

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable (R S) in
/-- (Implementation detail): If `S` is an `R`-algebra with presentation `P`
and section `σ` of the projection `R[Xᵢ] ⧸ I^2 → S`, then a
`DescentAux` structure contains the data necessary to reconstruct `σ`. -/
private structure DescentAux where
  P : Presentation R S
  σ : S →ₐ[R] MvPolynomial P.vars R ⧸ P.ker ^ 2
  h : P.vars → MvPolynomial P.vars R
  p : P.rels → MvPolynomial P.rels (MvPolynomial P.vars R)
  hphom : ∀ (j : P.rels), (p j).IsHomogeneous 2
  hp : ∀ (j : P.rels), (eval P.relation) (p j) = (aeval h) (P.relation j)
  q : P.vars → MvPolynomial P.rels P.Ring
  hqhom : ∀ (i : P.vars), (q i).IsHomogeneous 1
  hq : ∀ (i : P.vars), (eval P.relation) (q i) = h i - X i

namespace DescentAux

variable (A : DescentAux R S)

/-- (Implementation detail): The finite type `ℤ`-algebra. -/
private def R₀ (A : DescentAux R S) : Type u :=
  Algebra.adjoin A.P.Core
    ((⋃ i, (A.h i).coeffs) ∪
      (⋃ i, ⋃ x ∈ (A.q i).coeffs, x.coeffs) ∪
      (⋃ i, ⋃ x ∈ (A.p i).coeffs, x.coeffs) : Set R)

private instance : CommRing A.R₀ := inferInstanceAs <| CommRing (Algebra.adjoin _ _)
instance : Algebra A.R₀ R := inferInstanceAs <| Algebra (Algebra.adjoin _ _) R
private instance : Algebra A.R₀ S := inferInstanceAs <| Algebra (Algebra.adjoin _ _) S
private instance : IsScalarTower A.R₀ R S :=
  inferInstanceAs <| IsScalarTower (Algebra.adjoin _ _) _ _
private instance : FaithfulSMul A.R₀ R := inferInstanceAs <| FaithfulSMul (Algebra.adjoin _ _) _

private instance [A.P.IsFinite] : Algebra.FiniteType ℤ A.R₀ := by
  dsimp only [R₀]
  refine Algebra.FiniteType.trans (S := A.P.Core) inferInstance <| .adjoin_of_finite ?_
  refine Set.Finite.union (Set.Finite.union ?_ ?_) ?_
  · refine Set.finite_iUnion fun i ↦ Finset.finite_toSet _
  · refine Set.finite_iUnion fun i ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi ↦ Finset.finite_toSet _)
  · refine Set.finite_iUnion fun i ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi ↦ Finset.finite_toSet _)

private instance isCore_coreOfSection : A.P.IsCore A.R₀ := by dsimp [R₀]; infer_instance

set_option quotPrecheck false
local notation "f₀" => Ideal.Quotient.mkₐ A.R₀ (Ideal.span <| .range <| A.P.coreRelation A.R₀)

private lemma subset_range_algebraMap :
    ((⋃ i, (A.h i).coeffs) ∪
      (⋃ i, ⋃ x ∈ (A.q i).coeffs, x.coeffs) ∪
      (⋃ i, ⋃ x ∈ (A.p i).coeffs, x.coeffs) : Set R) ⊆ Set.range ⇑(algebraMap A.R₀ R) := by
  simp only [R₀, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]

private lemma coeffs_h_subset (i) : ((A.h i).coeffs : Set R) ⊆ Set.range ⇑(algebraMap A.R₀ R) := by
  trans ⋃ i, ↑(A.h i).coeffs
  · exact Set.subset_iUnion_of_subset i subset_rfl
  · exact subset_trans (subset_trans Set.subset_union_left Set.subset_union_left)
      A.subset_range_algebraMap

private lemma coeffs_p_subset (i) :
    ((A.p i).coeffs : Set _) ⊆ .range (MvPolynomial.map (σ := A.P.vars) (algebraMap A.R₀ R)) := by
  intro p hp
  refine MvPolynomial.mem_range_map_of_coeffs_subset (subset_trans ?_ A.subset_range_algebraMap)
  refine subset_trans ?_ Set.subset_union_right
  exact Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset p hp subset_rfl)

private lemma coeffs_q_subset (i) :
    ((A.q i).coeffs : Set _) ⊆ .range (MvPolynomial.map (σ := A.P.vars) (algebraMap A.R₀ R)) := by
  intro q hq
  refine MvPolynomial.mem_range_map_of_coeffs_subset (subset_trans ?_ A.subset_range_algebraMap)
  refine subset_trans ?_ Set.subset_union_left
  refine subset_trans ?_ Set.subset_union_right
  exact Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset q hq subset_rfl)

private noncomputable def σ₀ :
    A.P.CoreModel A.R₀ →ₐ[A.R₀] MvPolynomial A.P.vars A.R₀ ⧸ (RingHom.ker f₀ ^ 2) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ _ _).comp <| aeval fun i ↦
      ((A.h i).preimage (A.coeffs_h_subset i))) <| by
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [← AlgHom.comap_ker, Ideal.Quotient.mkₐ_ker, Ideal.coe_comap,
      Set.mem_preimage, SetLike.mem_coe]
    have hinj : Function.Injective (MvPolynomial.map (σ := A.P.vars) (algebraMap A.R₀ R)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective A.R₀ R)
    rw [Ideal.mem_span_pow_iff]
    refine ⟨(A.p i).preimage (A.coeffs_p_subset i), .of_map hinj ?_, hinj ?_⟩
    · rw [map_preimage]
      exact A.hphom i
    · simp_rw [map_eval, Function.comp_def, Presentation.map_coreRelation, map_preimage,
        A.hp, MvPolynomial.map_aeval]
      simp [MvPolynomial.eval₂_map_comp_C, Presentation.map_coreRelation, aeval_def]

private lemma kerSquareLift_comp_σ₀ :
    (AlgHom.kerSquareLift f₀).comp A.σ₀ = .id A.R₀ (Presentation.CoreModel A.R₀) := by
  have hf₀ : Function.Surjective f₀ := Ideal.Quotient.mk_surjective
  rw [← AlgHom.cancel_right hf₀]
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  suffices h : ∃ p, p.IsHomogeneous 1 ∧ (eval (Presentation.coreRelation A.R₀)) p =
      preimage (A.coeffs_h_subset i) - X i by
    simpa [σ₀, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_iff]
  have hinj : Function.Injective (MvPolynomial.map (σ := A.P.vars) (algebraMap A.R₀ R)) :=
    map_injective _ (FaithfulSMul.algebraMap_injective A.R₀ R)
  refine ⟨(A.q i).preimage (A.coeffs_q_subset i), .of_map hinj ?_, hinj ?_⟩
  · rw [map_preimage]
    exact A.hqhom i
  · simp [MvPolynomial.map_eval, map_preimage, Function.comp_def, Presentation.map_coreRelation, hq]

end DescentAux

/-- If `S` is a smooth `R`-algebra, there exists a `ℤ`-subalgebra of finite type `R₀` such that
`S ≃ₐ R ⊗[R₀] S₀` where `S₀` is a model. -/
@[stacks 00TP]
theorem exists_finiteType [Smooth R S] :
    ∃ (R₀ : Type u) (S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : Algebra R₀ R) (_ : Algebra R₀ S₀),
      FiniteType ℤ R₀ ∧ Smooth R₀ S₀ ∧ Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) := by
  let P := Presentation.ofFinitePresentation R S
  let f : MvPolynomial P.vars R →ₐ[R] S := aeval P.val
  have hkerf : RingHom.ker f = Ideal.span (.range P.relation) := P.span_range_relation_eq_ker.symm
  obtain ⟨(σ : S →ₐ[R] MvPolynomial P.vars R ⧸ RingHom.ker f ^ 2), hsig⟩ :=
    (FormallySmooth.iff_split_surjection f P.algebraMap_surjective).mp inferInstance
  have (i : P.vars) := Ideal.Quotient.mk_surjective (σ <| P.val i)
  choose h hh using this
  have hdiag : (Ideal.Quotient.mkₐ _ _).comp (aeval h) = σ.comp (aeval P.val) :=
    algHom_ext (by simp [hh])
  have (j : P.rels) : Ideal.Quotient.mk (RingHom.ker f ^ 2) (aeval h (P.relation j)) = 0 := by
    suffices ho : σ (aeval P.val (P.relation j)) = 0 by
      convert ho
      exact congr($hdiag _)
    simp
  simp_rw [Ideal.Quotient.eq_zero_iff_mem, hkerf, Ideal.mem_span_pow_iff] at this
  choose p homog hp using this
  have (i : P.vars) : h i - X i ∈ Ideal.span (.range P.relation) := by
    simpa [P.span_range_relation_eq_ker, sub_eq_zero, ← hh i] using congr($hsig (P.val i))
  simp_rw [Ideal.mem_span_iff] at this
  choose q hqhom hq using this
  let A : DescentAux R S :=
    { P := P, σ := σ, p := p, h := h, hphom := homog, hp := hp, q := q, hqhom := hqhom, hq := hq }
  have : P.IsCore A.R₀ := A.isCore_coreOfSection
  exact ⟨A.R₀, P.CoreModel A.R₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨.of_split _ A.σ₀ A.kerSquareLift_comp_σ₀, inferInstance⟩,
    ⟨(P.tensorCoreModelEquiv A.R₀).symm⟩⟩

end Algebra.Smooth
