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

variable {R : Type*} [CommRing R]
variable {A : Type u} {B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra A B]

variable (A B) in
/-- (Implementation detail): If `S` is an `R`-algebra with presentation `P`
and section `σ` of the projection `R[Xᵢ] ⧸ I^2 → S`, then a
`DescentAux` structure contains the data necessary to reconstruct `σ`. -/
structure DescentAux where
  vars : Type
  rels : Type
  P : Presentation A B vars rels
  σ : B →ₐ[A] MvPolynomial vars A ⧸ P.ker ^ 2
  h : vars → MvPolynomial vars A
  p : rels → MvPolynomial rels (MvPolynomial vars A)
  hphom : ∀ (j : rels), (p j).IsHomogeneous 2
  hp : ∀ (j : rels), (eval P.relation) (p j) = (aeval h) (P.relation j)
  q : vars → MvPolynomial rels P.Ring
  hqhom : ∀ (i : vars), (q i).IsHomogeneous 1
  hq : ∀ (i : vars), (eval P.relation) (q i) = h i - X i

namespace DescentAux

variable (D : DescentAux A B)

variable (R)

/-- (Implementation detail): The finite type `ℤ`-algebra. -/
def subalgebra (D : DescentAux A B) : Subalgebra R A :=
  Algebra.adjoin R
    (D.P.coeffs ∪
      ((⋃ i, (D.h i).coeffs) ∪
       (⋃ i, ⋃ x ∈ (D.q i).coeffs, x.coeffs) ∪
       (⋃ i, ⋃ x ∈ (D.p i).coeffs, x.coeffs)) : Set A)

instance : CommRing (D.subalgebra R) := inferInstanceAs <| CommRing (Algebra.adjoin _ _)
instance algebra₀ : Algebra R (D.subalgebra R) := inferInstanceAs <| Algebra R (Algebra.adjoin _ _)
instance algebra₁ : Algebra (D.subalgebra R) A := inferInstanceAs <| Algebra (Algebra.adjoin _ _) A
instance algebra₂ : Algebra (D.subalgebra R) B := inferInstanceAs <| Algebra (Algebra.adjoin _ _) B
instance : IsScalarTower (D.subalgebra R) A B :=
  inferInstanceAs <| IsScalarTower (Algebra.adjoin _ _) _ _
instance : FaithfulSMul (D.subalgebra R) A := inferInstanceAs <| FaithfulSMul (Algebra.adjoin _ _) _

instance [Finite D.vars] [Finite D.rels] : Algebra.FiniteType R (D.subalgebra R) := by
  dsimp only [subalgebra]
  refine Algebra.FiniteType.trans (S := R) inferInstance <| .adjoin_of_finite ?_
  refine .union ?_ (.union (.union ?_ ?_) ?_)
  · exact Presentation.finite_coeffs
  · refine Set.finite_iUnion fun i ↦ Finset.finite_toSet _
  · refine Set.finite_iUnion fun i ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi ↦ Finset.finite_toSet _)
  · refine Set.finite_iUnion fun i ↦ ?_
    exact Set.Finite.biUnion (Finset.finite_toSet _) (fun i hi ↦ Finset.finite_toSet _)

instance hasCoeffs : D.P.HasCoeffs (D.subalgebra R) where
  coeffs_subset_range := by
    grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]

set_option quotPrecheck false in
local notation "f₀" =>
  Ideal.Quotient.mkₐ (D.subalgebra R)
    (Ideal.span <| .range <| D.P.relationOfHasCoeffs (D.subalgebra R))

lemma coeffs_h_subset (i) : ↑(D.h i).coeffs ⊆ Set.range ⇑(algebraMap (D.subalgebra R) A) := by
  have : ((D.h i).coeffs : Set _) ⊆ ⋃ i, ((D.h i).coeffs : Set A) :=
    Set.subset_iUnion_of_subset i subset_rfl
  grind [subalgebra, Subalgebra.setRange_algebraMap, Algebra.subset_adjoin]

lemma coeffs_p_subset (i) :
    ↑(D.p i).coeffs ⊆
      Set.range (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) := by
  intro p hp
  have : (p.coeffs : Set A) ⊆ ⋃ i, ⋃ x ∈ (D.p i).coeffs, ↑x.coeffs :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset p hp subset_rfl)
  grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra, Subalgebra.setRange_algebraMap,
    Algebra.subset_adjoin]

lemma coeffs_q_subset (i) :
    ↑(D.q i).coeffs ⊆
      Set.range (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) := by
  intro q hq
  have : (q.coeffs : Set A) ⊆ ⋃ i, ⋃ x ∈ (D.q i).coeffs, ↑(coeffs x) :=
    Set.subset_iUnion_of_subset i (Set.subset_iUnion₂_of_subset q hq subset_rfl)
  grind [MvPolynomial.mem_range_map_iff_coeffs_subset, subalgebra, Subalgebra.setRange_algebraMap,
    Algebra.subset_adjoin]

lemma exists_kerSquareLift_comp_eq_id :
    ∃ (σ₀ : D.P.ModelOfHasCoeffs (D.subalgebra R) →ₐ[D.subalgebra R]
        MvPolynomial D.vars (D.subalgebra R) ⧸ (RingHom.ker f₀ ^ 2)),
      (AlgHom.kerSquareLift f₀).comp σ₀ =
        .id (D.subalgebra R) (Presentation.ModelOfHasCoeffs (D.subalgebra R)) := by
  choose p hp using fun i ↦ (D.h i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_h_subset R i)
  refine ⟨?_, ?_⟩
  · refine Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ _ _).comp <| aeval p) ?_
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
    intro i
    simp only [← AlgHom.comap_ker, Ideal.coe_comap, Set.mem_preimage, SetLike.mem_coe]
    rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker,
      ← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
    obtain ⟨q, hq⟩ := (D.p i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_p_subset R i)
    refine ⟨q, .of_map hinj ?_, hinj ?_⟩
    · rw [hq]
      exact D.hphom i
    · simp_rw [map_eval, Function.comp_def, Presentation.map_relationOfHasCoeffs,
        hq, D.hp, MvPolynomial.map_aeval, hp]
      simp [MvPolynomial.eval₂_map_comp_C, Presentation.map_relationOfHasCoeffs, aeval_def]
  · have hf₀ : Function.Surjective f₀ := Ideal.Quotient.mk_surjective
    rw [← AlgHom.cancel_right hf₀]
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    suffices h : ∃ p', p'.IsHomogeneous 1 ∧ (eval (D.P.relationOfHasCoeffs (D.subalgebra R))) p' =
        p i - X i by
      -- Reducible def-eq issues caused by `RingHom.ker f.toRingHom` discrepancies
      -- Can be fixed after #25138.
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa [Ideal.mem_span_iff_exists_isHomogeneous, hp]
    have hinj : Function.Injective
        (MvPolynomial.map (σ := D.vars) (algebraMap (D.subalgebra R) A)) :=
      map_injective _ (FaithfulSMul.algebraMap_injective (D.subalgebra R) A)
    obtain ⟨t, ht⟩ := (D.q i).mem_range_map_iff_coeffs_subset.mpr (D.coeffs_q_subset R i)
    refine ⟨t, .of_map hinj ?_, hinj ?_⟩
    · rw [ht]
      exact D.hqhom i
    · simp [MvPolynomial.map_eval, Function.comp_def,
        Presentation.map_relationOfHasCoeffs, ht, hq, hp]

end DescentAux

variable (R A B)

/--
Let `A` be an `R`-algebra. If `B` is a smooth `A`-algebra, there exists an
`R`-subalgebra of finite type `A₀` of `A` and a smooth `A₀`-algebra `B₀` such that
`B ≃ₐ A ⊗[A₀] B₀`.
See `Algebra.Smooth.exists_finiteType` for a version in terms of `Function.Injective`.
-/
public theorem exists_subalgebra_finiteType [Smooth A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      FiniteType R A₀ ∧ Smooth A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  let P := Presentation.ofFinitePresentation A B
  let f : P.Ring →ₐ[A] B := IsScalarTower.toAlgHom _ _ _
  have hkerf : RingHom.ker f = Ideal.span (.range P.relation) :=
    P.span_range_relation_eq_ker.symm
  obtain ⟨(σ : B →ₐ[A] MvPolynomial _ A ⧸ RingHom.ker f ^ 2), hsig⟩ :=
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
  have (i : Fin (Presentation.ofFinitePresentationVars A B)) :
      h i - X i ∈ Ideal.span (.range P.relation) := by
    simpa [P.span_range_relation_eq_ker, sub_eq_zero, f] using hsig i
  simp_rw [Ideal.mem_span_iff_exists_isHomogeneous] at this
  choose q hqhom hq using this
  let D : DescentAux A B :=
    { vars := _, rels := _, P := P, σ := σ, p := p, h := h, hphom := homog, hp := hp,
      q := q, hqhom := hqhom, hq := hq }
  have : P.HasCoeffs (D.subalgebra R) := D.hasCoeffs R
  obtain ⟨σ₀, hσ₀⟩ := D.exists_kerSquareLift_comp_eq_id R
  exact ⟨D.subalgebra R, P.ModelOfHasCoeffs (D.subalgebra R), inferInstance, inferInstance,
    inferInstance, ⟨.of_split _ σ₀ hσ₀, inferInstance⟩,
    ⟨(P.tensorModelOfHasCoeffsEquiv (D.subalgebra R)).symm⟩⟩

/--
Let `A` be an `R`-algebra. If `B` is a smooth `A`-algebra, there exists an
`R`-algebra of finite type `A₀` and a smooth `A₀`-algebra `B₀` such that `B ≃ₐ A ⊗[A₀] B₀`
with `A₀ → A` injective.
See `Algebra.Smooth.exists_subalgebra_finiteType` for a version in terms of `Subalgebra`.
-/
@[stacks 00TP]
public theorem exists_finiteType [Smooth A B] :
    ∃ (A₀ : Type u) (B₀ : Type u) (_ : CommRing A₀) (_ : CommRing B₀)
      (_ : Algebra R A₀) (_ : Algebra A₀ A) (_ : Algebra A₀ B₀),
      Function.Injective (algebraMap A₀ A) ∧ FiniteType R A₀ ∧ Smooth A₀ B₀ ∧
      Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  obtain ⟨A₀, B₀, _, _, _, _, _⟩ := exists_subalgebra_finiteType R A B
  use A₀, B₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Subtype.val_injective, inferInstance, inferInstance

end Algebra.Smooth
