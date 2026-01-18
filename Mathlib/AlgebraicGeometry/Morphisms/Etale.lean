/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!

# Étale morphisms

A morphism of schemes `f : X ⟶ Y` is étale if it is smooth of relative dimension zero. We
also define the category of schemes étale over `X`.

-/

@[expose] public section

universe t u

universe u₂ u₁ v₂ v₁

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

/-- A morphism of schemes is étale if it is smooth of relative dimension zero. -/
abbrev IsEtale {X Y : Scheme.{u}} (f : X ⟶ Y) := IsSmoothOfRelativeDimension 0 f

namespace IsEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance [IsEtale f] : IsSmooth f :=
  IsSmoothOfRelativeDimension.isSmooth 0 f

instance : IsStableUnderBaseChange @IsEtale :=
  isSmoothOfRelativeDimension_isStableUnderBaseChange 0

open RingHom in
instance (priority := 900) [IsEtale f] : FormallyUnramified f where
  formallyUnramified_of_affine_subset U V e := by
    have : Locally (IsStandardSmoothOfRelativeDimension 0) (f.appLE (↑U) (↑V) e).hom :=
      HasRingHomProperty.appLE (P := @IsSmoothOfRelativeDimension 0) _ inferInstance ..
    have : Locally RingHom.FormallyUnramified (f.appLE U V e).hom := by
      apply locally_of_locally _ this
      intro R S _ _ f hf
      algebraize [f]
      rw [RingHom.FormallyUnramified]
      have : Algebra.IsStandardSmoothOfRelativeDimension 0 R S := hf
      infer_instance
    rwa [← RingHom.locally_iff_of_localizationSpanTarget
      FormallyUnramified.respectsIso FormallyUnramified.ofLocalizationSpanTarget]

instance : MorphismProperty.HasOfPostcompProperty
    @IsEtale (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
  exact inferInstanceAs <| IsEtale (pullback.diagonal f)

/-- If `f ≫ g` is étale and `g` unramified, then `f` is étale. -/
lemma of_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [IsEtale (f ≫ g)] [LocallyOfFiniteType g]
    [FormallyUnramified g] : IsEtale f :=
  of_postcomp _ (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) f g ⟨‹_›, ‹_›⟩ ‹_›

instance : MorphismProperty.HasOfPostcompProperty @IsEtale @IsEtale := by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @IsEtale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance

noncomputable
def _root_.AlgebraicGeometry.Scheme.stalkMapIsoOfIsPullback {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    [IsOpenImmersion g] (p : P) (x : X := fst p) (hx : fst p = x := by cat_disch) :
    Arrow.mk (f.stalkMap x) ≅ Arrow.mk (snd.stalkMap p) :=
  haveI : IsOpenImmersion fst := MorphismProperty.of_isPullback h.flip ‹_›
  Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [← hx, ← Scheme.Hom.comp_apply, h.w]; simp) ≪≫
      asIso (g.stalkMap (snd p)))
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by rw [hx]) ≪≫
      asIso (fst.stalkMap p))
    (by
      subst hx
      simp [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp,
        Scheme.Hom.stalkMap_congr_hom _ _ h.w])

lemma _root_.RingHom.FormallyEtale.comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S} {g : S →+* T} (hf : f.FormallyEtale)
    (hg : g.FormallyEtale) :
    (g.comp f).FormallyEtale := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.comp R S T

lemma _root_.RingHom.FormallyEtale.of_comp {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {f : R →+* S} {g : S →+* T} (hf : f.FormallyUnramified)
    (h : (g.comp f).FormallyEtale) :
    g.FormallyEtale := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.of_restrictScalars (R := R)

lemma _root_.RingHom.FormallyEtale.isLocalizationMap {R : Type*} [CommRing R] {M : Submonoid R}
    {S : Type*} [CommRing S] [Algebra R S] {P : Type*} [CommRing P] [IsLocalization M S]
    {T : Submonoid P} (Q : Type*) [CommRing Q] [Algebra P Q] [IsLocalization T Q]
    {g : R →+* P} (hy : M ≤ Submonoid.comap g T)
    (hg : g.FormallyEtale) :
    (IsLocalization.map (S := S) Q g hy).FormallyEtale := by
  refine .of_comp (f := algebraMap R S) ?_ ?_
  · rw [RingHom.formallyUnramified_algebraMap]
    exact .of_isLocalization M
  · simp only [IsLocalization.map_comp]
    refine .comp hg ?_
    rw [RingHom.formallyEtale_algebraMap]
    exact .of_isLocalization T

@[simp]
lemma _root_.RingHom.quotientKerEquivOfSurjective_symm_apply
    {R S : Type*} [Ring R] [Semiring S] {f : R →+* S} (hf : Function.Surjective f) (x : R) :
    (RingHom.quotientKerEquivOfSurjective hf).symm (f x) = Ideal.Quotient.mk _ x := by
  apply (RingHom.quotientKerEquivOfSurjective hf).injective
  simp

lemma _root_.RingHom.quotientKerEquivOfSurjective_symm_comp
    {R S : Type*} [Ring R] [Semiring S] {f : R →+* S} (hf : Function.Surjective f) :
    (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom.comp f = Ideal.Quotient.mk _ := by
  ext; simp

lemma _root_.RingHom.exists_comp_evalRingHom_eq_of_isDomain {ι : Type*} [Finite ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] {S : Type*} [CommRing S] [IsDomain S] (f : (∀ i, R i) →+* S) :
    ∃ (i : ι) (g : R i →+* S), f = g.comp (Pi.evalRingHom R i) := by
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨_, RingHom.ker_isPrime f⟩
  use i
  have := congr($(hq).asIdeal)
  dsimp only [PrimeSpectrum.comap_asIdeal] at this
  let g' : (∀ i, R i) ⧸ (RingHom.ker (Pi.evalRingHom R i)) →+* S :=
    Ideal.Quotient.lift _ f <| by
      simp_rw [← RingHom.mem_ker, ← SetLike.le_def, ← this, RingHom.ker]
      exact Ideal.comap_mono (by simp)
  use g'.comp (RingHom.quotientKerEquivOfSurjective
      (RingHom.surjective (Pi.evalRingHom R i))).symm.toRingHom
  ext x
  dsimp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  simp [g']

lemma  _root_.AlgebraicGeometry.LocallyOfFiniteType.residueFieldMap [LocallyOfFiniteType f]
    (x : X) : (f.residueFieldMap x).hom.EssFiniteType :=
  RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap _ _)

instance [LocallyOfFiniteType f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.EssFiniteType (Y.residueField (f.base x)) (X.residueField x) := by
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [← RingHom.essFiniteType_algebraMap]
  exact AlgebraicGeometry.LocallyOfFiniteType.residueFieldMap _ _

instance [IsEtale f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) := by
  infer_instance

end IsEtale

namespace Scheme

/-- The category `Etale X` is the category of schemes étale over `X`. -/
def Etale (X : Scheme.{u}) : Type _ := MorphismProperty.Over @IsEtale ⊤ X

variable (X : Scheme.{u})

instance : Category X.Etale :=
  inferInstanceAs <| Category (MorphismProperty.Over @IsEtale ⊤ X)

/-- The forgetful functor from schemes étale over `X` to schemes over `X`. -/
def Etale.forget : X.Etale ⥤ Over X :=
  MorphismProperty.Over.forget @IsEtale ⊤ X

/-- The forgetful functor from schemes étale over `X` to schemes over `X` is fully faithful. -/
def Etale.forgetFullyFaithful : (Etale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

instance : (Etale.forget X).Full :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Full
instance : (Etale.forget X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Faithful

instance : HasPullbacks X.Etale := by
  unfold Etale
  infer_instance

end Scheme

end AlgebraicGeometry
