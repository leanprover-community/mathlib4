/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.Tactic.Algebraize

/-!
# Standard smooth ring homomorphisms

In this file we define standard smooth ring homomorphisms and show their
meta properties.

## Main definitions

- `RingHom.IsStandardSmooth`: A ring homomorphism `R →+* S` is standard smooth if `S` is standard
  smooth as `R`-algebra.
- `RingHom.IsStandardSmoothOfRelativeDimension n`: A ring homomorphism `R →+* S` is standard
  smooth of relative dimension `n` if `S` is standard smooth of relative dimension `n` as
  `R`-algebra.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section
universe t t' w w' u v

variable (n m : ℕ)

open TensorProduct

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism `R →+* S` is standard smooth if `S` is standard smooth as `R`-algebra. -/
@[algebraize RingHom.IsStandardSmooth.toAlgebra]
def IsStandardSmooth (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmooth _ _ _ _ f.toAlgebra

lemma isStandardSmooth_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardSmooth ↔ Algebra.IsStandardSmooth R S := by
  rw [RingHom.IsStandardSmooth, toAlgebra_algebraMap]

/-- Helper lemma for the `algebraize` tactic -/
lemma IsStandardSmooth.toAlgebra {f : R →+* S} (hf : IsStandardSmooth f) :
    @Algebra.IsStandardSmooth R S _ _ f.toAlgebra := hf

/-- A ring homomorphism `R →+* S` is standard smooth of relative dimension `n` if
`S` is standard smooth of relative dimension `n` as `R`-algebra. -/
@[algebraize RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra]
def IsStandardSmoothOfRelativeDimension (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmoothOfRelativeDimension n _ _ _ _ f.toAlgebra

lemma isStandardSmoothOfRelativeDimension_algebraMap [Algebra R S] :
    (algebraMap R S).IsStandardSmoothOfRelativeDimension n ↔
      Algebra.IsStandardSmoothOfRelativeDimension n R S := by
  rw [RingHom.IsStandardSmoothOfRelativeDimension, toAlgebra_algebraMap]

/-- Helper lemma for the `algebraize` tactic -/
lemma IsStandardSmoothOfRelativeDimension.toAlgebra {f : R →+* S}
    (hf : IsStandardSmoothOfRelativeDimension n f) :
    @Algebra.IsStandardSmoothOfRelativeDimension n R S _ _ f.toAlgebra := hf

lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth (f : R →+* S)
    (hf : IsStandardSmoothOfRelativeDimension n f) :
    IsStandardSmooth f := by
  algebraize [f]
  exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

variable {n m}

variable (R) in
lemma IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension 0 (RingHom.id R) :=
  Algebra.IsStandardSmoothOfRelativeDimension.id R

lemma IsStandardSmoothOfRelativeDimension.equiv (e : R ≃+* S) :
    IsStandardSmoothOfRelativeDimension 0 (e : R →+* S) := by
  algebraize [e.toRingHom]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective

variable {T : Type*} [CommRing T]

lemma IsStandardSmooth.comp {g : S →+* T} {f : R →+* S}
    (hg : IsStandardSmooth g) (hf : IsStandardSmooth f) :
    IsStandardSmooth (g.comp f) := by
  rw [IsStandardSmooth]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmooth.trans R S T

lemma IsStandardSmoothOfRelativeDimension.comp {g : S →+* T} {f : R →+* S}
    (hg : IsStandardSmoothOfRelativeDimension n g)
    (hf : IsStandardSmoothOfRelativeDimension m f) :
    IsStandardSmoothOfRelativeDimension (n + m) (g.comp f) := by
  rw [IsStandardSmoothOfRelativeDimension]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans m n R S T

lemma isStandardSmooth_stableUnderComposition :
    StableUnderComposition @IsStandardSmooth :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma isStandardSmooth_respectsIso : RespectsIso @IsStandardSmooth := by
  apply isStandardSmooth_stableUnderComposition.respectsIso
  introv
  exact (IsStandardSmoothOfRelativeDimension.equiv e).isStandardSmooth

lemma isStandardSmoothOfRelativeDimension_respectsIso :
    RespectsIso (@IsStandardSmoothOfRelativeDimension n) where
  left {R S T _ _ _} f e hf := by
    rw [← zero_add n]
    exact (IsStandardSmoothOfRelativeDimension.equiv e).comp hf
  right {R S T _ _ _} f e hf := by
    rw [← add_zero n]
    exact hf.comp (IsStandardSmoothOfRelativeDimension.equiv e)

lemma isStandardSmooth_isStableUnderBaseChange :
    IsStableUnderBaseChange @IsStandardSmooth := by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmooth_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmooth R T := by
      rw [RingHom.IsStandardSmooth] at h; convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmooth S (S ⊗[R] T) by
      rw [RingHom.IsStandardSmooth]; convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

variable (n)

lemma isStandardSmoothOfRelativeDimension_isStableUnderBaseChange :
    IsStableUnderBaseChange (@IsStandardSmoothOfRelativeDimension n) := by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmoothOfRelativeDimension_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
      rw [RingHom.IsStandardSmoothOfRelativeDimension] at h
      convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmoothOfRelativeDimension n S (S ⊗[R] T) by
      rw [RingHom.IsStandardSmoothOfRelativeDimension]
      convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

lemma IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway {Rᵣ : Type*} [CommRing Rᵣ]
    [Algebra R Rᵣ] (r : R) [IsLocalization.Away r Rᵣ] :
    IsStandardSmoothOfRelativeDimension 0 (algebraMap R Rᵣ) := by
  have : (algebraMap R Rᵣ).toAlgebra = ‹Algebra R Rᵣ› := by
    ext
    rw [Algebra.smul_def]
    rfl
  rw [IsStandardSmoothOfRelativeDimension, this]
  exact Algebra.IsStandardSmoothOfRelativeDimension.localization_away r

lemma isStandardSmooth_localizationPreserves : LocalizationPreserves IsStandardSmooth :=
  isStandardSmooth_isStableUnderBaseChange.localizationPreserves

lemma isStandardSmoothOfRelativeDimension_localizationPreserves :
    LocalizationPreserves (IsStandardSmoothOfRelativeDimension n) :=
  (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n).localizationPreserves

lemma isStandardSmooth_holdsForLocalizationAway :
    HoldsForLocalizationAway IsStandardSmooth := by
  introv R h
  exact (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r).isStandardSmooth

lemma isStandardSmoothOfRelativeDimension_holdsForLocalizationAway :
    HoldsForLocalizationAway (IsStandardSmoothOfRelativeDimension 0) := by
  introv R h
  exact IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r

lemma isStandardSmooth_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway IsStandardSmooth :=
  isStandardSmooth_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    isStandardSmooth_holdsForLocalizationAway

lemma isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway (IsStandardSmoothOfRelativeDimension n) where
  left R S _ _ _ _ _ r _ _ hf :=
    have : (algebraMap R S).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
    add_zero n ▸ IsStandardSmoothOfRelativeDimension.comp hf this
  right _ S T _ _ _ _ s _ _ hf :=
    have : (algebraMap S T).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway s
    zero_add n ▸ IsStandardSmoothOfRelativeDimension.comp this hf

variable (R S) in
/-- Every standard smooth homomorphism `R → S` factors into `R -> R[X₁,...,Xₙ] → S`
where `n` is the relative dimension and `R[X₁,...,Xₙ] → S` is etale. -/
theorem _root_.Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ g : MvPolynomial (Fin n) R →ₐ[R] S, g.Etale := by
  classical
  let := Fintype.ofFinite
  obtain ⟨ι, σ, _, _, P, e⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (R := R) (S := S) (n := n)
  let e₀ : σ ⊕ Fin n ≃ ι := ((Equiv.ofInjective _ P.map_inj).sumCongr
      (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, Set.ncard_compl,
        Set.ncard_range_of_injective P.map_inj, ← e, Algebra.Presentation.dimension])).symm).trans
      (Equiv.Set.sumCompl _)
  let e : MvPolynomial σ (MvPolynomial (Fin n) R) ≃ₐ[R] P.Ring :=
    (MvPolynomial.sumAlgEquiv R _ _).symm.trans (MvPolynomial.renameEquiv _ e₀)
  let φ := e.toAlgHom.comp (IsScalarTower.toAlgHom _ (MvPolynomial (Fin n) R) _)
  algebraize [φ.toRingHom, (algebraMap P.Ring S).comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower R (MvPolynomial (Fin n) R) S := .to₁₂₄ _ _ P.Ring _
  refine ⟨IsScalarTower.toAlgHom _ _ _, ?_⟩
  have H : (MvPolynomial.aeval fun x ↦ (algebraMap P.Ring S) (e (MvPolynomial.X x))).toRingHom =
      (algebraMap P.Ring S).comp e.toRingHom := by
    ext
    · simp [e, IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) S]
    · simp [e, @RingHom.algebraMap_toAlgebra (MvPolynomial (Fin n) R) S, φ]
    · simp [e]
  let P' : Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { toGenerators := .ofSurjective (algebraMap _ _ <| e <| .X ·) <| by
      convert P.algebraMap_surjective.comp e.surjective
      exact congr($H)
    relation := e.symm ∘ P.relation
    span_range_relation_eq_ker := by
      rw [Set.range_comp, ← AlgEquiv.coe_ringEquiv e.symm, AlgEquiv.symm_toRingEquiv,
        ← Ideal.map_span, P.span_range_relation_eq_ker, Ideal.map_symm]
      exact congr(RingHom.ker $H).symm
    map := _
    map_inj := Function.injective_id }
  let P' : Algebra.SubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { __ := P'
    jacobian_isUnit := by
      convert P.jacobian_isUnit using 1
      simp_rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, map_det]
      congr 1
      ext i j
      trans algebraMap P.Ring S (e ((e.symm (P.relation j)).pderiv i))
      · simpa [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, P',
          Algebra.Generators.ofSurjective] using congr($H _)
      suffices e ((e.symm (P.relation j)).pderiv i) = (P.relation j).pderiv (P.map i) by
        simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, this]
      simp [e, MvPolynomial.pderiv_sumToIter, ← MvPolynomial.pderiv_rename e₀.injective,
        show e₀ (Sum.inl i) = P.map i from rfl] }
  exact etale_algebraMap.mpr (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    ⟨_, _, _, inferInstance, P', by simp [Algebra.Presentation.dimension]⟩)

/-- Every standard smooth homomorphism `R → S` factors into `R -> R[X₁,...,Xₙ] → S`
where `n` is the relative dimension and `R[X₁,...,Xₙ] → S` is etale. -/
theorem IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    {f : R →+* S} {n : ℕ} (hf : f.IsStandardSmoothOfRelativeDimension n) :
    ∃ g : MvPolynomial (Fin n) R →+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  classical
  algebraize [f]
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R S
  exact ⟨_, g.comp_algebraMap, hg⟩

theorem IsStandardSmooth.exists_etale_mvPolynomial
    {f : R →+* S} (hf : f.IsStandardSmooth) :
    ∃ n, ∃ g : MvPolynomial (Fin n) R →+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
  let := f.toAlgebra
  exact ⟨_, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    ⟨_, _, _, ‹_›, P, rfl⟩⟩

end RingHom
