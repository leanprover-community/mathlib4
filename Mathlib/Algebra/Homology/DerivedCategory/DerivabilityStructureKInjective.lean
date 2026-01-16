/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# The K-injective derivability structure

-/

@[expose] public section

universe w

open CategoryTheory Abelian Limits ZeroObject

variable {C : Type*} [Category C] [Abelian C]

namespace CategoryTheory.Abelian

open HomologicalComplex in
lemma quasiIso_f_iff_of_shortExact {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    QuasiIso S.f ↔ S.X₃.Acyclic := by
  refine ⟨fun _ n ↦ ?_, fun h ↦ ⟨fun n ↦ ?_⟩⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    refine (hS.homology_exact₃ n (n + 1) (by simp)).isZero_X₂ ?_ ?_
    · rw [← cancel_epi (homologyMap S.f n), comp_zero, ← homologyMap_comp,
        S.zero, homologyMap_zero]
    · simp [← cancel_mono (homologyMap S.f (n + 1))]
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have := (hS.homology_exact₂ n).epi_f (by
      apply IsZero.eq_of_tgt
      simpa [← exactAt_iff_isZero_homology] using h n)
    have := (hS.homology_exact₁ (n - 1) n (by simp)).mono_g (by
      apply IsZero.eq_of_src
      simpa [← exactAt_iff_isZero_homology] using h (n -1))
    exact Balanced.isIso_of_mono_of_epi _

instance : (MorphismProperty.monomorphisms C).IsStableUnderCobaseChange := by
  apply MorphismProperty.IsStableUnderCobaseChange.mk'
  intro _ _ _ _ _ _ h
  simp only [MorphismProperty.monomorphisms.iff] at h ⊢
  infer_instance

instance :
    (HomologicalComplex.quasiIso C (.up ℤ) ⊓
      (MorphismProperty.monomorphisms _)).IsStableUnderCobaseChange where
  of_isPushout {K₁ K₂ L₁ L₂ t l b r} sq h := by
    have : Mono t := h.2
    have : Mono b := (MorphismProperty.monomorphisms _).of_isPushout sq h.2
    refine ⟨?_, by simpa⟩
    have hK : (ShortComplex.mk t (cokernel.π t) (by simp)).ShortExact :=
      { exact := ShortComplex.exact_cokernel t }
    have hL : (ShortComplex.mk b (cokernel.π b) (by simp)).ShortExact :=
      { exact := ShortComplex.exact_cokernel b }
    let e : cokernel t ≅ cokernel b :=
      { hom := cokernel.map _ _ l r sq.w.symm
        inv := cokernel.desc _ (sq.desc 0 (cokernel.π t) (by simp)) (by simp)
        hom_inv_id := coequalizer.hom_ext (by simp)
        inv_hom_id := coequalizer.hom_ext (by apply sq.hom_ext <;> simp ) }
    replace hK := quasiIso_f_iff_of_shortExact hK
    replace hL := quasiIso_f_iff_of_shortExact hL
    dsimp at hK hL
    simp only [HomologicalComplex.mem_quasiIso_iff]
    rw [hL]
    exact HomologicalComplex.Acyclic.of_iso (by simpa [← hK] using h.1) e

instance {K₁ K₂ L₁ : CochainComplex C ℤ} (f : K₁ ⟶ K₂) (i : K₁ ⟶ L₁) [Mono i] [QuasiIso i] :
    QuasiIso (pushout.inl f i) :=
  (MorphismProperty.of_isPushout
    (P := (HomologicalComplex.quasiIso C (.up ℤ) ⊓
      (MorphismProperty.monomorphisms _))) (IsPushout.of_hasPushout f i)
        ⟨by simpa, by simpa⟩).1

variable (C) in
class HasKInjectiveResolutions : Prop where
  exists_isKInjective (K : CochainComplex C ℤ) :
    ∃ (L : CochainComplex C ℤ) (_ : L.IsKInjective) (i : K ⟶ L), Mono i ∧ QuasiIso i

end CategoryTheory.Abelian

namespace CochainComplex

variable [HasKInjectiveResolutions C]

variable (C) in
abbrev KInjectives :=
  ObjectProperty.FullSubcategory (fun (K : CochainComplex C ℤ) ↦ K.IsKInjective)

namespace KInjectives

abbrev mk (K : CochainComplex C ℤ) [K.IsKInjective] : KInjectives C := ⟨K, inferInstance⟩

abbrev ι : KInjectives C ⥤ CochainComplex C ℤ := ObjectProperty.ι _

variable (C) in
def quasiIso : MorphismProperty (KInjectives C) :=
  (HomologicalComplex.quasiIso C (.up ℤ)).inverseImage ι

variable (C) in
@[simps]
def localizerMorphism :
    LocalizerMorphism (KInjectives.quasiIso C) (HomologicalComplex.quasiIso C (.up ℤ)) where
  functor := ι
  map := by rfl

instance (K : CochainComplex C ℤ) :
    IsConnected ((localizerMorphism C).RightResolution K) := by
  obtain ⟨L, _, i, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective K
  let R : (localizerMorphism C).RightResolution K := { X₁ := .mk L, w := i, hw := by simpa }
  have : Nonempty ((localizerMorphism C).RightResolution K) := ⟨R⟩
  have : ∀ R', ∃ R'', Nonempty (R ⟶ R'') ∧ Nonempty (R' ⟶ R'') := by
    intro R'
    obtain ⟨M, _, j, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective (pushout R'.w i)
    have : QuasiIso R'.w := R'.hw
    refine ⟨{ X₁ := .mk M, w := R'.w ≫ pushout.inl R'.w i ≫ j, hw := ?_ }, ⟨?_⟩, ⟨?_⟩⟩
    · dsimp
      simp only [HomologicalComplex.mem_quasiIso_iff]
      infer_instance
    · exact
        { f := ObjectProperty.homMk (pushout.inr R'.w i ≫ j)
          comm := by simp [pushout.condition_assoc, R] }
    · exact { f := ObjectProperty.homMk (pushout.inl R'.w i ≫ j) }
  refine zigzag_isConnected (fun R₁ R₂ ↦ ?_)
  obtain ⟨R₁', ⟨f₁⟩, ⟨g₁⟩⟩ := this R₁
  obtain ⟨R₂', ⟨f₂⟩, ⟨g₂⟩⟩ := this R₂
  exact (Zigzag.of_hom g₁).trans ((Zigzag.of_inv f₁).trans
    ((Zigzag.of_hom f₂).trans (Zigzag.of_inv g₂)))

instance : (localizerMorphism C).arrow.HasRightResolutions := by
  intro f
  obtain ⟨K₁, K₂, f, rfl⟩ := Arrow.mk_surjective f
  obtain ⟨L₁, _, i₁, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective K₁
  have : QuasiIso (pushout.inl f i₁) := inferInstance
  obtain ⟨M, _, j, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective (pushout f i₁)
  refine ⟨{
    X₁ := Arrow.mk (X := .mk L₁) (Y := .mk M) (ObjectProperty.homMk (pushout.inr f i₁ ≫ j))
    w := Arrow.homMk i₁ (pushout.inl f i₁ ≫ j) (by simp [pushout.condition_assoc])
    hw := ⟨by simpa, by
      dsimp
      simp only [HomologicalComplex.mem_quasiIso_iff]
      infer_instance⟩
  }⟩

/-instance : (localizerMorphism C).IsLocalizedEquivalence := by
  sorry

instance : (localizerMorphism C).IsRightDerivabilityStructure :=
  .mk' _-/

end KInjectives

end CochainComplex
