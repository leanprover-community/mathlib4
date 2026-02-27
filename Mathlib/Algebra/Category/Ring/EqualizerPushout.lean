/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Equalizer of inclusions to pushout in `CommRingCat`

Given a map `f : R ⟶ S` in `CommRingCat`, we prove that the equalizer of the two maps
`pushout.inl : S ⟶ pushout f f` and `pushout.inr : S ⟶ pushout f f` is canonically isomorphic
to `R` when `R ⟶ S` is a faithfully flat ring map.

Note that, under `CommRingCat.pushoutCoconeIsColimit`, the two maps `inl` and `inr` above can be
described as `s ↦ s ⊗ₜ[R] 1` and `s ↦ 1 ⊗ₜ[R] s`, respectively.
-/

@[expose] public section

open CategoryTheory Limits

namespace CommRingCat

universe u

namespace Equalizer

section CodRestrictEqLocusPushoutCocone

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical ring map from `R` to the explicit equalizer of
`includeLeft : S ⟶ S ⊗[R] S` and `includeRight : S ⟶ S ⊗[R] S`. -/
def codRestrictEqLocusPushoutCocone :
    R →+* (equalizerFork (pushoutCocone R S S).inl (pushoutCocone R S S).inr).pt :=
  RingHom.codRestrict (algebraMap R S)
    ((pushoutCocone R S S).inl.hom.eqLocus (pushoutCocone R S S).inr.hom) (by simp)

/-- Injectivity of `algebraMap R S` implies `codRestrictEqLocusPushoutCocone f` is injective. -/
lemma codRestrictEqLocusPushoutCocone.inj_of_inj (hf : Function.Injective (algebraMap R S)) :
    Function.Injective (codRestrictEqLocusPushoutCocone R S) :=
  RingHom.injective_codRestrict.mpr hf

/-- `Algebra.IsEffective R S` implies `codRestrictEqLocusPushoutCocone` is surjective. -/
lemma codRestrictEqLocusPushoutCocone.surj_of_isEffective (hf : Algebra.IsEffective R S) :
    Function.Surjective (codRestrictEqLocusPushoutCocone (R := R) (S := S)) := by
  intro s
  have := Set.mem_range.mp <|
    Algebra.IsEffective.eqLocus_includeLeft_includeRight hf ▸ SetLike.mem_coe.mpr s.property
  use this.choose
  apply Subtype.ext
  erw [RingHom.codRestrict_apply, this.choose_spec]

/-- Faithfully flat `algebraMap R S` implies `codRestrictEqLocusPushoutCocone` is bijective. -/
lemma codRestrictEqLocusPushoutCocone.bij_of_faithfullyFlat (hf : (algebraMap R S).FaithfullyFlat) :
    Function.Bijective (codRestrictEqLocusPushoutCocone R S) := by
  constructor
  · exact codRestrictEqLocusPushoutCocone.inj_of_inj _ _ (RingHom.FaithfullyFlat.injective hf)
  · haveI : Module.FaithfullyFlat R S := (RingHom.faithfullyFlat_algebraMap_iff).mp hf
    exact codRestrictEqLocusPushoutCocone.surj_of_isEffective _ _
      (Algebra.IsEffective.of_faithfullyFlat R S)

end CodRestrictEqLocusPushoutCocone

section Fork

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then the fork
```
        S ---inl---> pushout f f
R --f-->
        S ---inr---> pushout f f
```
is an equalizer diagram.
See `isLimitForkPushoutCoconeSelfOfFaithfullyFlat` for the pushoutCocone version. -/
noncomputable def isLimitForkPushoutSelfOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsLimit (Fork.ofι f pushout.condition) := by
  algebraize [f.hom]
  let fork : Fork (pushoutCocone R S S).inl (pushoutCocone R S S).inr :=
    Fork.ofι (ofHom (algebraMap R S)) (by rw [(PushoutCocone.condition _)])
  let isPushout : IsPushout (ofHom (algebraMap R S)) (ofHom (algebraMap R S))
      (pushoutCocone R S S).inl (pushoutCocone R S S).inr :=
    ⟨⟨PushoutCocone.condition (pushoutCocone R S S)⟩, ⟨pushoutCoconeIsColimit R S S⟩⟩
  let isLimit : IsLimit fork :=
    (Fork.isLimitEquivOfIsos _
      (equalizerFork (pushoutCocone R S S).inl (pushoutCocone R S S).inr) (Iso.refl _) (Iso.refl _)
      (RingEquiv.toCommRingCatIso <|
        RingEquiv.ofBijective _ (codRestrictEqLocusPushoutCocone.bij_of_faithfullyFlat R S hf))
      (by cat_disch) (by cat_disch) (by cat_disch)).symm
    (equalizerForkIsLimit (pushoutCocone R S S).inl (pushoutCocone R S S).inr)
  exact Fork.isLimitEquivOfIsos fork (Fork.ofι f pushout.condition) (Iso.refl _)
    (IsPushout.isoPushout isPushout) (Iso.refl _) (IsPushout.inl_isoPushout_hom isPushout).symm
    (IsPushout.inr_isoPushout_hom isPushout).symm rfl isLimit

/-- A regular monomorphism structure on a map `f : R ⟶ S` in `CommRingCat` with
faithfully flat `f.hom : R ⟶ S`. -/
noncomputable def regularMonoOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) :
    RegularMono f where
  Z := pushout f f
  left := pushout.inl f f
  right := pushout.inr f f
  w := pushout.condition
  isLimit := isLimitForkPushoutSelfOfFaithfullyFlat f hf

end Fork

end Equalizer

namespace Opposite

variable {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R)

/-- For a map `f : S ⟶ R` in `CommRingCatᵒᵖ` with faithfully flat `f.unop : R.unop ⟶ S.unop`,
the cofork
```
pullback f f ---fst---> S
                          --f--> R
pullback f f ---snd---> S
```
is a coequalizer diagram. -/
noncomputable def isColimitOfπPullbackOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) :
    IsColimit (Cofork.ofπ f pullback.condition) :=
  Cofork.isColimitCoforkPushoutEquivIsColimitForkUnopPullback.symm
    (Equalizer.isLimitForkPushoutSelfOfFaithfullyFlat _ hf)

/-- A regular epimorphism structure on a map `f : S ⟶ R` in `CommRingCatᵒᵖ` with
faithfully flat `f.unop.hom : R.unop ⟶ S.unop`. -/
noncomputable def regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := isColimitOfπPullbackOfFaithfullyFlat f hf

/-- Any map `f : S ⟶ R` in `CommRingCatᵒᵖ` with faithfully flat `f.unop.hom : R.unop ⟶ S.unop` is
an effective epimorphism. -/
lemma effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : EffectiveEpi f :=
  RegularEpi.effectiveEpi (regularEpiOfFaithfullyFlat f hf)

end Opposite

end CommRingCat
