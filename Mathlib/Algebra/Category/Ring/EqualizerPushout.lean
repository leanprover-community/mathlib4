/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Equalizer of inclusions to pushout in `CommRingCat`

Given a map `f : R ⟶ S` in `CommRingCat`, we prove that the equalizer of the two maps
`pushout.inl : S ⟶ pushout f f` and `pushout.inr : S ⟶ pushout f f` is canonically isomorphic
to `R` when `R ⟶ S` is a faithfully flat ring map.

Note that, under `CommRingCat.pushoutCoconeIsColimit`, the two maps `inl` and `inr` above can be
written as `s ↦ s ⊗ₜ[R] 1` and `s ↦ 1 ⊗ₜ[R] s`, respectively.
-/

open CategoryTheory Limits TensorProduct

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
def pushoutCoconeSelf : PushoutCocone f f :=
  @CommRingCat.pushoutCocone _ _ _ _ _ _ f.hom.toAlgebra f.hom.toAlgebra

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

namespace Equalizer

section toEqualizer

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The canonical ring map from `R` to the explicit equalizer of `includeLeft : S ⟶ S ⊗[R] S` and
`includeRight : S ⟶ S ⊗[R] S`. -/
noncomputable def toEqualizer :
    R →+* (equalizerFork (pushoutCoconeSelf f).inl (pushoutCoconeSelf f).inr).pt := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocusOfInclusion R S

/-- If `f : R ⟶ S` is an injective map in `CommRingCat`, then `toEqualizer f` is injective. -/
lemma toEqualizer.inj_of_inj (hf : Function.Injective f.hom) :
    Function.Injective (toEqualizer f) := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocusOfInclusion_injective R S hf

/-- If `f : R ⟶ S` is a map in `CommRingCat` such that the pair of `algebraMap : R → S` and
`includeLeft - includeRight : S → S ⊗[R] S` is exact, then `toEqualizer f` is surjective. -/
lemma toEqualizer.surj_of_exactLeftMinusRight
    (hf : @Algebra.TensorProduct.Exact.IncludeLeftSubRight R S _ _ f.hom.toAlgebra) :
    Function.Surjective (toEqualizer f) := by
  algebraize [f.hom]
  exact Algebra.TensorProduct.toEqLocusOfInclusion_surjective R S hf

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then `toEqualizer f` is bijective. -/
lemma toEqualizer.bij_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    Function.Bijective (toEqualizer f) := by
  constructor
  · exact toEqualizer.inj_of_inj _ (RingHom.FaithfullyFlat.injective hf)
  · algebraize [f.hom]
    exact toEqualizer.surj_of_exactLeftMinusRight _
      (Algebra.TensorProduct.Exact.includeLeftSubRight_of_faithfullyFlat R S)

end toEqualizer

section Fork

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then `forkPushoutCoconeSelf` is
an equalizer diagram. See `isLimitForkPushoutSelf` for the pushout version. -/
noncomputable def isLimitforkPushoutCoconeSelf (hf : f.hom.FaithfullyFlat) :
    IsLimit (forkPushoutCoconeSelf f) := by
  refine (Fork.isLimitEquivOfIsos _
    (equalizerFork (pushoutCoconeSelf f).inl (pushoutCoconeSelf f).inr)
    (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp) ?_).symm ?_
  · exact (RingEquiv.ofBijective _ (toEqualizer.bij_of_faithfullyFlat _ hf)).toCommRingCatIso
  · rfl
  · exact CommRingCat.equalizerForkIsLimit _ _

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then the fork
```
        S ---inl---> pushout f f
R --f-->
        S ---inr---> pushout f f
```
an equalizer diagram. See `isLimitforkPushoutCoconeSelf` for the pushoutCocone version. -/
noncomputable def isLimitForkPushoutSelf (hf : f.hom.FaithfullyFlat) :
    IsLimit (Fork.ofι f pushout.condition) := by
  algebraize [f.hom]
  let : IsPushout _ _ _ _ :=
    ⟨⟨PushoutCocone.condition (pushoutCocone R S S)⟩, ⟨pushoutCoconeIsColimit R S S⟩⟩
  exact Fork.isLimitEquivOfIsos _ _
    (Iso.refl _) (IsPushout.isoPushout this) (Iso.refl _)
      (IsPushout.inl_isoPushout_hom this).symm (IsPushout.inr_isoPushout_hom this).symm
        rfl (isLimitforkPushoutCoconeSelf f hf)

end Fork

end Equalizer

end CommRingCat
