/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Monomorphisms
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.OfQuotient

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

variable (C) in
abbrev KInjectives :=
  ObjectProperty.FullSubcategory (fun (K : CochainComplex C ℤ) ↦ K.IsKInjective)

namespace KInjectives

abbrev mk (K : CochainComplex C ℤ) [K.IsKInjective] : KInjectives C := ⟨K, inferInstance⟩

lemma mk_surjective (X : KInjectives C) :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsKInjective),
      X = mk K :=
  ⟨X.obj, X.property, rfl⟩

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

variable [HasKInjectiveResolutions C]

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

end KInjectives

end CochainComplex

namespace HomotopyCategory

variable (C) in
abbrev KInjectives :=
  (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal.FullSubcategory

namespace KInjectives

abbrev mk (K : CochainComplex C ℤ) [K.IsKInjective] :
    KInjectives C :=
  ⟨(HomotopyCategory.quotient _ _).obj K, by
    rwa [← CochainComplex.isKInjective_iff_rightOrthogonal]⟩

lemma mk_surjective (X : KInjectives C) :
    ∃ (K : CochainComplex C ℤ) (_ : K.IsKInjective),
      X = mk K := by
  obtain ⟨X, hX⟩ := X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [← CochainComplex.isKInjective_iff_rightOrthogonal] at hX
  exact ⟨K, inferInstance, rfl⟩

def ι : KInjectives C ⥤ HomotopyCategory C (.up ℤ) :=
  ObjectProperty.ι _

section

variable [HasDerivedCategory C]

def Qh : KInjectives C ⥤ DerivedCategory C :=
  ι ⋙ DerivedCategory.Qh

instance : (Qh (C := C)).Full where
  map_surjective {K L} f := by
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    obtain ⟨f, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient _ _).obj K) L).2 f
    exact ⟨ObjectProperty.homMk f, rfl⟩

instance : (Qh (C := C)).Faithful where
  map_injective {K L f g} h := by
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    ext
    exact (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient _ _).obj K) L).1 h

variable [HasKInjectiveResolutions C]

instance : (Qh (C := C)).EssSurj where
  mem_essImage X := by
    obtain ⟨K, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := DerivedCategory.Qh) X
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨L, _, j, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective K
    have := Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient _ _).map j)
        (by simpa [quotient_map_mem_quasiIso_iff])
    exact ⟨mk L,
      ⟨(asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map j))).symm ≪≫ e⟩⟩

instance : (Qh (C := C)).IsEquivalence where

instance : Qh.IsLocalization (.isomorphisms (KInjectives C)) := by
  let l : LocalizerMorphism (.isomorphisms (KInjectives C))
      (HomotopyCategory.quasiIso C (.up ℤ)) :=
    { functor := ι
      map := by
        intro K L f (hf : IsIso f)
        simp only [MorphismProperty.inverseImage_iff, quasiIso]
        infer_instance }
  have : CatCommSq l.functor (𝟭 (KInjectives C)) DerivedCategory.Qh Qh :=
    ⟨(Functor.leftUnitor _).symm⟩
  have : l.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.mk' l (𝟭 _) (DerivedCategory.Qh) Qh
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    l DerivedCategory.Qh

end

end KInjectives

end HomotopyCategory

namespace CochainComplex

namespace KInjectives

def toHomotopyCategory : KInjectives C ⥤ HomotopyCategory.KInjectives C :=
  ObjectProperty.lift _ (KInjectives.ι ⋙ HomotopyCategory.quotient _ _) (fun K ↦ by
    simpa [← CochainComplex.isKInjective_iff_rightOrthogonal] using K.property)

@[simp]
lemma toHomotopyCategory_obj (K : CochainComplex C ℤ) [K.IsKInjective] :
    toHomotopyCategory.obj (mk K) = HomotopyCategory.KInjectives.mk K := rfl

instance : (toHomotopyCategory (C := C)).Full where
  map_surjective {K L} f:= by
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    exact ⟨ObjectProperty.homMk f, rfl⟩

instance : (toHomotopyCategory (C := C)).EssSurj where
  mem_essImage X := by
    obtain ⟨K, _, rfl⟩ := X.mk_surjective
    exact ⟨mk K, ⟨Iso.refl _⟩⟩

lemma isIso_toHomotopyCategory_map_iff {K L : KInjectives C} (f : K ⟶ L) :
    IsIso (toHomotopyCategory.map f) ↔ QuasiIso f.hom := by
  have := HasDerivedCategory.standard C
  rw [← isIso_iff_of_reflects_iso _ HomotopyCategory.KInjectives.Qh]
  obtain ⟨K, _, rfl⟩ := K.mk_surjective
  obtain ⟨L, _, rfl⟩ := L.mk_surjective
  obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
  exact DerivedCategory.isIso_Q_map_iff_quasiIso C f

instance (K : CochainComplex C ℤ) [K.IsKInjective] :
    CochainComplex.IsKInjective (HomologicalComplex.cylinder K) := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  refine ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished _) ?_ ?_
  · dsimp
    rwa [← CochainComplex.isKInjective_iff_rightOrthogonal]
  · dsimp
    rw [← CochainComplex.isKInjective_iff_rightOrthogonal]
    infer_instance

variable [HasKInjectiveResolutions C]

instance : toHomotopyCategory.IsLocalization (KInjectives.quasiIso C) := by
  refine Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _ ?_ ?_
  · intro K L f hf
    rwa [isIso_toHomotopyCategory_map_iff]
  · intro K L f₀ f₁ h
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    dsimp at f₀ f₁ h
    let H : Homotopy f₀ f₁ :=
      HomotopyCategory.homotopyOfEq _ _ (HomotopyCategory.KInjectives.ι.congr_map h)
    refine ⟨mk (HomologicalComplex.cylinder K),
      ObjectProperty.homMk (HomologicalComplex.cylinder.ι₀ K),
      ObjectProperty.homMk (HomologicalComplex.cylinder.ι₁ K),
      ObjectProperty.homMk (HomologicalComplex.cylinder.π K), ?_,
      by cat_disch, by cat_disch,
      ObjectProperty.homMk (HomologicalComplex.cylinder.desc f₀ f₁ H),
      by cat_disch, by cat_disch⟩
    · exact (HomologicalComplex.cylinder.homotopyEquiv K
        (fun n ↦ ⟨n - 1, by simp⟩)).quasiIso_hom

instance [HasDerivedCategory C] :
    (ι ⋙ DerivedCategory.Q).IsLocalization (quasiIso C) := by
  change (toHomotopyCategory ⋙ (HomotopyCategory.KInjectives.Qh (C := C))).IsLocalization _
  refine Functor.IsLocalization.comp toHomotopyCategory
    (HomotopyCategory.KInjectives.Qh) (W₂ := .isomorphisms _) _ _ ?_ le_rfl ?_
  · intro K L f hf
    have : IsIso (toHomotopyCategory.map f) := by rwa [isIso_toHomotopyCategory_map_iff]
    dsimp
    infer_instance
  · intro K L f hf
    obtain ⟨K, _, rfl⟩ := K.mk_surjective
    obtain ⟨L, _, rfl⟩ := L.mk_surjective
    obtain ⟨f, rfl⟩ := ObjectProperty.homMk_surjective f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    refine ⟨mk K, mk L, ObjectProperty.homMk f, ?_, ⟨Iso.refl _⟩⟩
    have : IsIso ((HomotopyCategory.quotient _ _).map f) := by
      simp only [MorphismProperty.isomorphisms.iff] at hf
      exact (Functor.mapIso HomotopyCategory.KInjectives.ι (@asIso _ _ _ _ _ hf)).isIso_hom
    have : QuasiIso f := by
      rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
      exact
      (DerivedCategory.Qh.mapIso
        (asIso ((HomotopyCategory.quotient _ _).map f))).isIso_hom
    simpa [quasiIso]

instance [HasDerivedCategory C] :
    ((localizerMorphism C).functor ⋙ DerivedCategory.Q).IsLocalization (quasiIso C) := by
  dsimp
  infer_instance

instance : (localizerMorphism C).IsLocalizedEquivalence := by
  have := HasDerivedCategory.standard C
  exact .of_isLocalization_of_isLocalization _ (DerivedCategory.Q)

instance : (localizerMorphism C).IsRightDerivabilityStructure :=
  .mk' _

end KInjectives

end CochainComplex
