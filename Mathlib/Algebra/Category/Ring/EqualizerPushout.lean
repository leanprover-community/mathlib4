/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Equalizer of inclusions to pushout in `CommRingCat`

Given a map `f : R ⟶ S` in `CommRingCat`, we prove that the equalizer of the two maps
`pushout.inl : S ⟶ pushout f f` and `pushout.inr : S ⟶ pushout f f` is canonically isomorphic
to `R` when `R ⟶ S` is a faithfully flat ring map.

Note that, under `CommRingCat.pushoutCoconeIsColimit`, the two maps `inl` and `inr` above can be
described as `s ↦ s ⊗ₜ[R] 1` and `s ↦ 1 ⊗ₜ[R] s`, respectively.
-/

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
def ExactIncludeLeftSubRight : Prop := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.ExactIncludeLeftSubRight R S

namespace Equalizer

section ToEqualizerPushoutCoconeSelf

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The canonical ring map from `R` to the explicit equalizer of `includeLeft : S ⟶ S ⊗[R] S` and
`includeRight : S ⟶ S ⊗[R] S`. -/
noncomputable def toEqualizerPushoutCoconeSelf :
    R →+* (equalizerFork (pushoutCoconeSelf f).inl (pushoutCoconeSelf f).inr).pt := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocusOfInclusion R S

/-- If `f : R ⟶ S` is an injective map in `CommRingCat`, then `toEqualizerPushoutCoconeSelf f` is
injective. -/
lemma toEqualizerPushoutCoconeSelf_inj_of_inj (hf : Function.Injective f.hom) :
    Function.Injective (toEqualizerPushoutCoconeSelf f) := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocusOfInclusion_injective _ _ hf

/-- If `ExactIncludeLeftSubRight f` is true for a map `f : R ⟶ S` in `CommRingCat`, then
`toEqualizerPushoutCoconeSelf f` is surjective. -/
lemma toEqualizerPushoutCoconeSelf_surj_of_exactIncludeLeftSubRight
    (hf : ExactIncludeLeftSubRight f) : Function.Surjective (toEqualizerPushoutCoconeSelf f) := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocusOfInclusion_surjective _ _ hf

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then `toEqualizerPushoutCoconeSelf f`
is bijective. -/
lemma toEqualizerPushoutCoconeSelf_bij_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    Function.Bijective (toEqualizerPushoutCoconeSelf f) := by
  constructor
  · exact toEqualizerPushoutCoconeSelf_inj_of_inj _ (RingHom.FaithfullyFlat.injective hf)
  · algebraize [f.hom]
    exact toEqualizerPushoutCoconeSelf_surj_of_exactIncludeLeftSubRight _
      (Algebra.TensorProduct.exactIncludeLeftSubRight_of_faithfullyFlat _ _)

end ToEqualizerPushoutCoconeSelf

section Fork

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then `forkPushoutCoconeSelf` is
an equalizer diagram.
See `isLimitForkPushoutSelfOfFaithfullyFlat` for the pushout version. -/
noncomputable def isLimitforkPushoutCoconeSelfOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsLimit (forkPushoutCoconeSelf f) :=
  (Fork.isLimitEquivOfIsos _ (equalizerFork _ _) (Iso.refl _) (Iso.refl _) (RingEquiv.ofBijective _
    (toEqualizerPushoutCoconeSelf_bij_of_faithfullyFlat _ hf)).toCommRingCatIso (by simp) (by simp)
      rfl).symm (CommRingCat.equalizerForkIsLimit _ _)

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then the fork
```
        S ---inl---> pushout f f
R --f-->
        S ---inr---> pushout f f
```
is an equalizer diagram.
See `isLimitforkPushoutCoconeSelfOfFaithfullyFlat` for the pushoutCocone version. -/
noncomputable def isLimitForkPushoutSelfOfFaithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsLimit (Fork.ofι f pushout.condition) := by
  algebraize [f.hom]
  let : IsPushout _ _ _ _ :=
    ⟨⟨PushoutCocone.condition (pushoutCocone R S S)⟩, ⟨pushoutCoconeIsColimit R S S⟩⟩
  exact Fork.isLimitEquivOfIsos _ _ (Iso.refl _) (IsPushout.isoPushout this) (Iso.refl _)
    (IsPushout.inl_isoPushout_hom this).symm (IsPushout.inr_isoPushout_hom this).symm rfl
      (isLimitforkPushoutCoconeSelfOfFaithfullyFlat f hf)

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
faithfully flat `f.unop : R.unop ⟶ S.unop`. -/
noncomputable def regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := isColimitOfπPullbackOfFaithfullyFlat f hf

/-- Any map `f : S ⟶ R` in `CommRingCatᵒᵖ` with faithfully flat `f.unop : R.unop ⟶ S.unop` is
an effective epimorphism. -/
lemma effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : EffectiveEpi f := by
  let := regularEpiOfFaithfullyFlat f hf
  infer_instance

end Opposite

end CommRingCat
