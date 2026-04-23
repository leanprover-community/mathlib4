/-
Copyright (c) 2025 Yong-Gyu Choi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yong-Gyu Choi
-/
module

public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.Algebraize
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Equalizer of inclusions to pushouts in `CommRingCat`

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

section Fork

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- If `f : R ⟶ S` is a faithfully flat map in `CommRingCat`, then the fork
```
        S ---inl---> pushout f f
R --f-->
        S ---inr---> pushout f f
```
is an equalizer diagram. -/
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
      (RingEquiv.toCommRingCatIso <| RingEquiv.ofBijective _
        (Algebra.codRestrictEqLocusPushoutCocone.bijective_of_faithfullyFlat R S))
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

/-- Any map `f : R ⟶ S` in `CommRingCat` with faithfully flat `f.hom : R ⟶ S` is a regular
monomorphism. -/
lemma isRegularMono_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsRegularMono f :=
  isRegularMono_of_regularMono (regularMonoOfFaithfullyFlat f hf)

end Fork

namespace Opposite

variable {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R)

/-- A regular epimorphism structure on a map `f : S ⟶ R` in `CommRingCatᵒᵖ` with
faithfully flat `f.unop.hom : R.unop ⟶ S.unop`. -/
lemma regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) :
    IsRegularEpi f :=
  (isRegularEpi_op_iff_isRegularMono _).mpr (isRegularMono_of_faithfullyFlat _ hf)

/-- Any map `f : S ⟶ R` in `CommRingCatᵒᵖ` with faithfully flat `f.unop.hom : R.unop ⟶ S.unop` is
an effective epimorphism. -/
lemma effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : EffectiveEpi f :=
  (isRegularEpi_iff_effectiveEpi _).mp (regularEpiOfFaithfullyFlat _ hf)

end Opposite

end CommRingCat
