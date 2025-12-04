/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Smooth algebras have Noetherian models

In this file, we show if `S` is a smooth `R`-algebra, there exists a `ℤ`-subalgebra of finite type
`R₀` and a smooth `R₀`-algebra `S₀` such that `S ≃ₐ R ⊗[R₀] S₀`.
-/

universe u

open TensorProduct MvPolynomial

namespace Algebra.Smooth

variable {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (R S) in
/-- (Implementation detail): If `S` is an `R`-algebra with presentation `P`
and section `σ` of the projection `R[Xᵢ] ⧸ I^2 → S`, then a
`DescentAux` structure contains the data necessary to reconstruct `σ`. -/
structure DescentAux where
  vars : Type
  rels : Type
  P : Presentation R S vars rels
  σ : S →ₐ[R] MvPolynomial vars R ⧸ P.ker ^ 2
  h : vars → MvPolynomial vars R
  p : rels → MvPolynomial rels (MvPolynomial vars R)
  hphom : ∀ (j : rels), (p j).IsHomogeneous 2
  hp : ∀ (j : rels), (eval P.relation) (p j) = (aeval h) (P.relation j)
  q : vars → MvPolynomial rels P.Ring
  hqhom : ∀ (i : vars), (q i).IsHomogeneous 1
  hq : ∀ (i : vars), (eval P.relation) (q i) = h i - X i

namespace DescentAux

variable (A : DescentAux R S)

/-- (Implementation detail): The finite type `ℤ`-algebra. -/
def R₀ (A : DescentAux R S) : Type _ :=
  Algebra.adjoin A.P.Core
    ((⋃ i, (A.h i).coeffs) ∪
      (⋃ i, ⋃ x ∈ (A.q i).coeffs, x.coeffs) ∪
      (⋃ i, ⋃ x ∈ (A.p i).coeffs, x.coeffs) : Set R)

instance : CommRing A.R₀ := inferInstanceAs <| CommRing (Algebra.adjoin _ _)
instance algebra : Algebra A.R₀ R := inferInstanceAs <| Algebra (Algebra.adjoin _ _) R
instance : Algebra A.R₀ S := inferInstanceAs <| Algebra (Algebra.adjoin _ _) S
instance : IsScalarTower A.R₀ R S :=
  inferInstanceAs <| IsScalarTower (Algebra.adjoin _ _) _ _
instance : FaithfulSMul A.R₀ R := inferInstanceAs <| FaithfulSMul (Algebra.adjoin _ _) _

instance [Finite A.vars] [Finite A.rels] : Algebra.FiniteType ℤ A.R₀ := by
  dsimp only [R₀]
  refine Algebra.FiniteType.trans (S := A.P.Core) inferInstance <| .adjoin_of_finite ?_
  refine Set.Finite.union (Set.Finite.union ?_ ?_) ?_
  · refine Set.finite_iUnion fun i ↦ Finset.finite_toSet _
  · refine Set.finite_iUnion fun i ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi ↦ Finset.finite_toSet _)
  · refine Set.finite_iUnion fun i ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi ↦ Finset.finite_toSet _)

instance hasCoeffs : A.P.HasCoeffs A.R₀ := by dsimp [R₀]; infer_instance

set_option quotPrecheck false in
local notation "f₀" =>
  Ideal.Quotient.mkₐ A.R₀ (Ideal.span <| .range <| A.P.relationOfHasCoeffs A.R₀)

lemma subset_range_algebraMap :
    ((⋃ i, (A.h i).coeffs) ∪
      (⋃ i, ⋃ x ∈ (A.q i).coeffs, x.coeffs) ∪
      (⋃ i, ⋃ x ∈ (A.p i).coeffs, x.coeffs) : Set R) ⊆ Set.range ⇑(algebraMap A.R₀ R) := by
  simp only [R₀, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]

lemma coeffs_h_subset (i) : ↑(A.h i).coeffs ⊆ Set.range ⇑(algebraMap A.R₀ R) := by
  trans ⋃ i, ↑(A.h i).coeffs
  · exact Set.subset_iUnion_of_subset i subset_rfl
  · exact subset_trans (subset_trans Set.subset_union_left Set.subset_union_left)
      A.subset_range_algebraMap

lemma coeffs_p_subset (i) :
    ↑(A.p i).coeffs ⊆ Set.range (MvPolynomial.map (σ := A.vars) (algebraMap A.R₀ R)) := by
  intro p hp
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  refine subset_trans ?_ A.subset_range_algebraMap
  refine subset_trans ?_ Set.subset_union_right
  exact Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset p hp subset_rfl)

lemma coeffs_q_subset (i) :
    ↑(A.q i).coeffs ⊆ Set.range (MvPolynomial.map (σ := A.vars) (algebraMap A.R₀ R)) := by
  intro q hq
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  refine subset_trans ?_ A.subset_range_algebraMap
  refine subset_trans ?_ Set.subset_union_left
  refine subset_trans ?_ Set.subset_union_right
  exact Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset q hq subset_rfl)

lemma exists_kerSquareLift_comp_eq_id :
    ∃ (σ₀ : A.P.ModelOfHasCoeffs A.R₀ →ₐ[A.R₀] MvPolynomial A.vars A.R₀ ⧸ (RingHom.ker f₀ ^ 2)),
      (AlgHom.kerSquareLift f₀).comp σ₀ = .id A.R₀ (Presentation.ModelOfHasCoeffs A.R₀) := by
  choose p hp using fun i ↦ (A.h i).mem_range_map_iff_coeffs_subset.mpr (A.coeffs_h_subset i)
  refine ⟨?_, ?_⟩
  · refine Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ _ _).comp <| aeval p) ?_
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [← AlgHom.comap_ker, Ideal.coe_comap, Set.mem_preimage, SetLike.mem_coe]
    rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker,
      ← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
    have hinj : Function.Injective (MvPolynomial.map (σ := A.vars) (algebraMap A.R₀ R)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective A.R₀ R)
    rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
    obtain ⟨q, hq⟩ := (A.p i).mem_range_map_iff_coeffs_subset.mpr (A.coeffs_p_subset i)
    refine ⟨q, .of_map hinj ?_, hinj ?_⟩
    · rw [hq]
      exact A.hphom i
    · simp_rw [map_eval, Function.comp_def, Presentation.map_relationOfHasCoeffs,
        hq, A.hp, MvPolynomial.map_aeval, hp]
      simp [MvPolynomial.eval₂_map_comp_C, Presentation.map_relationOfHasCoeffs, aeval_def]
  · have hf₀ : Function.Surjective f₀ := Ideal.Quotient.mk_surjective
    rw [← AlgHom.cancel_right hf₀]
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    suffices h : ∃ p', p'.IsHomogeneous 1 ∧ (eval (A.P.relationOfHasCoeffs A.R₀)) p' =
        p i - X i by
      -- Reducible def-eq issues caused by `RingHom.ker f.toRingHom` discrepancies
      -- Can be fixed after #25138.
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa [Ideal.mem_span_iff_exists_isHomogeneous, hp]
    have hinj : Function.Injective (MvPolynomial.map (σ := A.vars) (algebraMap A.R₀ R)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective A.R₀ R)
    obtain ⟨t, ht⟩ := (A.q i).mem_range_map_iff_coeffs_subset.mpr (A.coeffs_q_subset i)
    refine ⟨t, .of_map hinj ?_, hinj ?_⟩
    · rw [ht]
      exact A.hqhom i
    · simp [MvPolynomial.map_eval, Function.comp_def,
        Presentation.map_relationOfHasCoeffs, ht, hq, hp]

end DescentAux

/-- If `S` is a smooth `R`-algebra, there exists a `ℤ`-subalgebra of finite type
`R₀` and a smooth `R₀`-algebra `S₀` such that `S ≃ₐ R ⊗[R₀] S₀`. -/
@[stacks 00TP]
public theorem exists_finiteType [Smooth R S] :
    ∃ (R₀ : Type u) (S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : Algebra R₀ R) (_ : Algebra R₀ S₀),
      FiniteType ℤ R₀ ∧ Smooth R₀ S₀ ∧ Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) := by
  let P := Presentation.ofFinitePresentation R S
  let f : P.Ring →ₐ[R] S := IsScalarTower.toAlgHom _ _ _
  have hkerf : RingHom.ker f = Ideal.span (.range P.relation) :=
    P.span_range_relation_eq_ker.symm
  obtain ⟨(σ : S →ₐ[R] MvPolynomial _ R ⧸ RingHom.ker f ^ 2), hsig⟩ :=
    (FormallySmooth.iff_split_surjection f P.algebraMap_surjective).mp inferInstance
  have (i : _) := Ideal.Quotient.mk_surjective (σ <| P.val i)
  choose h hh using this
  have hdiag : (Ideal.Quotient.mkₐ _ _).comp (aeval h) = σ.comp (aeval P.val) :=
    algHom_ext (by simp [hh])
  have (j : _) : Ideal.Quotient.mk (RingHom.ker f ^ 2) (aeval h (P.relation j)) = 0 := by
    suffices ho : σ (aeval P.val (P.relation j)) = 0 by
      convert ho
      exact congr($hdiag _)
    simp
  simp_rw [Ideal.Quotient.eq_zero_iff_mem, hkerf,
    Ideal.mem_span_pow_iff_exists_isHomogeneous] at this
  choose p homog hp using this
  have hsig (i : _) : f (h i) = P.val i := by
    rw [← AlgHom.kerSquareLift_mk]
    -- Reducible def-eq issues caused by `RingHom.ker f.toRingHom` discrepancies
    -- Can be fixed after #25138.
    exact hh i ▸ congr($hsig (P.val i))
  have (i : Fin (Presentation.ofFinitePresentationVars R S)) :
      h i - X i ∈ Ideal.span (.range P.relation) := by
    simpa [P.span_range_relation_eq_ker, sub_eq_zero, f] using hsig i
  simp_rw [Ideal.mem_span_iff_exists_isHomogeneous] at this
  choose q hqhom hq using this
  let A : DescentAux R S :=
    { vars := _, rels := _, P := P, σ := σ, p := p, h := h, hphom := homog, hp := hp,
      q := q, hqhom := hqhom, hq := hq }
  have : P.HasCoeffs A.R₀ := A.hasCoeffs
  obtain ⟨σ₀, hσ₀⟩ := A.exists_kerSquareLift_comp_eq_id
  exact ⟨A.R₀, P.ModelOfHasCoeffs A.R₀, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨.of_split _ σ₀ hσ₀, inferInstance⟩, ⟨(P.tensorModelOfHasCoeffsEquiv A.R₀).symm⟩⟩

end Algebra.Smooth
