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

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/--
The explicit cocone of form
```
R ---------f---------> S
|                      |
f                  includeLeft
|                      |
v                      v
S ----includeRight-->S ⊗[R] S
```
for a map `f : R ⟶ S` in `CommRingCat`.
-/
def pushoutCoconeSelf : PushoutCocone f f := by
  algebraize [f.hom]
  exact CommRingCat.pushoutCocone R S S

/--
The explicit fork
```
        S ---includeLeft---> S ⊗[R] S
R --f-->
        S ---includeRight--> S ⊗[R] S
```
for a map `f : R ⟶ S` in `CommRingCat`.
-/
def forkPushoutCoconeSelf : Fork (pushoutCoconeSelf f).inl (pushoutCoconeSelf f).inr := by
  algebraize [f.hom]
  apply Fork.ofι f
  apply CommRingCat.hom_ext
  apply RingHom.coe_inj
  ext
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul _

/-- For a map `R ⟶ S` in `CommRingCat`, it asserts that the pair of maps `f : R → S` and
`Algebra.TensorProduct.includeLeftSubRight : S → S ⊗[R] S` form an exact pair. -/
def IsEffective : Prop := by
  algebraize [f.hom]
  exact Algebra.IsEffective R S

namespace Equalizer

section CodRestrictEqLocusPushoutCocone

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The canonical ring map from `R` to the (explicit) equalizer of `includeLeft : S ⟶ S ⊗[R] S` and
`includeRight : S ⟶ S ⊗[R] S`. -/
noncomputable def codRestrictEqLocusPushoutCocone :
    R →+* (equalizerFork (pushoutCoconeSelf f).inl (pushoutCoconeSelf f).inr).pt := by
  algebraize [f.hom]
  exact RingHom.codRestrict (algebraMap R S)
    ((CommRingCat.pushoutCocone R S S).inl.hom.eqLocus (CommRingCat.pushoutCocone R S S).inr.hom)
      (fun _ ↦ by simp [RingHom.eqLocus, Algebra.TensorProduct.tmul_one_eq_one_tmul])

/-- If `f : R ⟶ S` is an injective map in `CommRingCat`, then `codRestrictEqLocusPushoutCocone f` is
injective. -/
lemma codRestrictEqLocusPushoutCocone.inj_of_inj (hf : Function.Injective f.hom) :
    Function.Injective (codRestrictEqLocusPushoutCocone f) :=
  RingHom.injective_codRestrict.mpr hf

/-- If `IsEffective f` is true for a map `f : R ⟶ S` in `CommRingCat`, then
`codRestrictEqLocusPushoutCocone f` is surjective. -/
lemma codRestrictEqLocusPushoutCocone.surj_of_isEffective (hf : IsEffective f) :
    Function.Surjective (codRestrictEqLocusPushoutCocone f) := by
  intro s
  algebraize [f.hom]
  have := Set.mem_range.mp <|
    Algebra.eqLocus_includeLeft_includeRight_of_isEffective hf ▸ SetLike.mem_coe.mpr s.property
  use this.choose
  apply Subtype.ext
  erw [RingHom.codRestrict_apply, this.choose_spec]

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then
`codRestrictEqLocusPushoutCocone f` is bijective. -/
lemma codRestrictEqLocusPushoutCocone.bij_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    Function.Bijective (codRestrictEqLocusPushoutCocone f) := by
  constructor
  · exact codRestrictEqLocusPushoutCocone.inj_of_inj _ (RingHom.FaithfullyFlat.injective hf)
  · algebraize [f.hom]
    exact codRestrictEqLocusPushoutCocone.surj_of_isEffective _
      (Algebra.isEffective_of_faithfullyFlat _ _)

end CodRestrictEqLocusPushoutCocone

section Fork

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then `forkPushoutCoconeSelf` is
an equalizer diagram.
See `isLimitForkPushoutSelfOfFaithfullyFlat` for the pushout version. -/
noncomputable def isLimitForkPushoutCoconeSelfOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsLimit (forkPushoutCoconeSelf f) :=
  (Fork.isLimitEquivOfIsos _ (equalizerFork _ _) (Iso.refl _) (Iso.refl _) (RingEquiv.ofBijective _
    (codRestrictEqLocusPushoutCocone.bij_of_faithfullyFlat _ hf)).toCommRingCatIso
      (by simp) (by simp) (by cat_disch)).symm (CommRingCat.equalizerForkIsLimit _ _)

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
  let : IsPushout _ _ _ _ :=
    ⟨⟨PushoutCocone.condition (pushoutCocone R S S)⟩, ⟨pushoutCoconeIsColimit R S S⟩⟩
  exact Fork.isLimitEquivOfIsos _ _ (Iso.refl _) (IsPushout.isoPushout this) (Iso.refl _)
    (IsPushout.inl_isoPushout_hom this).symm (IsPushout.inr_isoPushout_hom this).symm rfl
      (isLimitForkPushoutCoconeSelfOfFaithfullyFlat f hf)

/-- A regular monomorphism structure on a map `f : R ⟶ S` in `CommRingCat` with
faithfully flat `f.hom : R ⟶ S`. -/
noncomputable def regularMonoOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) : RegularMono f where
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
