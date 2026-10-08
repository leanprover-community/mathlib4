/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Subobject

import Mathlib.Algebra.Homology.ShortComplex.Pullback
import Mathlib.CategoryTheory.Abelian.Subobject

/-!
# Orthogonals are closed under extensions, and Dickson's theorem

In a preadditive balanced category, we show that both `P.leftOrthogonal` and `P.rightOrthogonal`
are closed under extensions, using the kernel and cokernel supplied by a short exact sequence.

In a well-powered abelian category with coproducts, we show in
`ObjectProperty.leftOrthogonal_rightOrthogonal_eq_self` that a property `P` which is closed under
quotients, extensions, and coproducts satisfies `P.rightOrthogonal.leftOrthogonal = P`. This is the
hard direction of [S. E. Dickson][dickson1966]'s characterisation of torsion classes. The easy
direction is assembled from the closure instances in
`Mathlib/CategoryTheory/ObjectProperty/OrthogonalLimits.lean`.

## References

* [S. E. Dickson, *A torsion theory for Abelian categories*][dickson1966]
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

/-! Closure under extensions uses the kernel and cokernel supplied by a short exact sequence, so
these two instances are stated for preadditive balanced categories. -/

section Extensions

variable [Preadditive C] [Balanced C]

/-- The left orthogonal of a property of objects is closed under extensions. -/
instance (P : ObjectProperty C) : P.leftOrthogonal.IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ Z k hZ := by
    obtain ⟨l, hfac⟩ := Cofork.IsColimit.desc' hS.gIsCokernel k (by simpa using h₁ _ hZ)
    simp [← hfac, h₃ l hZ]

/-- The right orthogonal of a property of objects is closed under extensions. -/
instance (P : ObjectProperty C) : P.rightOrthogonal.IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ Z k hZ := by
    obtain ⟨l, hfac⟩ := Fork.IsLimit.lift' hS.fIsKernel k (by simpa using h₃ _ hZ)
    simp [← hfac, h₁ l hZ]

end Extensions

/-! The hard direction of Dickson's theorem: in a well-powered abelian category with coproducts,
a property `P` closed under quotients, extensions, and coproducts is recovered as the left
orthogonal of its right orthogonal. -/

section Abelian

variable [Abelian C]

open Abelian

/-- In a well-powered abelian category with coproducts, if `P` is closed under quotients,
extensions, and coproducts, then for any `X`, the cokernel of the arrow of the largest
`P`-subobject of `X` satisfies `P.rightOrthogonal`. -/
lemma rightOrthogonal_cokernel_sSup (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] (X : C) :
    P.rightOrthogonal (cokernel (Subobject.sSup {A : Subobject X | P (A : C)}).arrow) := by
  rw [ObjectProperty.rightOrthogonal_iff]
  intro Z f hZ
  let A : Subobject X := Subobject.sSup {A : Subobject X | P (A : C)}
  -- `B` is the image of `f`, viewed as a subobject of the cokernel.
  let B : Subobject (cokernel A.arrow) := Subobject.mk (Abelian.image.ι f)
  have hB : P (B : C) := P.prop_of_iso (Subobject.underlyingIso (Abelian.image.ι f)).symm
    (P.prop_of_epi (Abelian.factorThruImage f) hZ)
  -- The pullback `A'` of `B` along the cokernel projection is an extension of `B` by `A`,
  -- so it satisfies `P` and is therefore contained in `A`.
  let A' : Subobject X := (Subobject.pullback (cokernel.π A.arrow)).obj B
  have hS : (ShortComplex.mk _ _ (cokernel.condition A.arrow)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  have hA' : P (A' : C) :=
    P.prop_of_iso ((Subobject.isPullback (cokernel.π A.arrow) B).isoIsPullback _ _
      (IsPullback.of_hasPullback _ _)).symm
      (P.prop_X₂_of_shortExact (hS.pull B.arrow) (P.prop_subobjectSSup _ fun _ hA ↦ hA) hB)
  have hle : A' ≤ A := Subobject.le_sSup _ _ hA'
  -- Hence the projection of `A'` onto `B` vanishes, so `B`, and with it the image of `f`,
  -- is zero.
  have hzero : A'.arrow ≫ cokernel.π A.arrow = 0 := by
    rw [← Subobject.ofLE_arrow hle, Category.assoc, cokernel.condition, comp_zero]
  have hπ : Subobject.pullbackπ (cokernel.π A.arrow) B = 0 := by
    rw [← cancel_mono B.arrow, (Subobject.isPullback (cokernel.π A.arrow) B).w, hzero, zero_comp]
  have himf : IsZero (Abelian.image f) :=
    IsZero.of_iso (IsZero.of_epi_eq_zero (Subobject.pullbackπ (cokernel.π A.arrow) B) hπ)
      (Subobject.underlyingIso (Abelian.image.ι f)).symm
  simp [← Abelian.image.fac f, IsZero.eq_zero_of_src himf]

/-- In a well-powered abelian category with coproducts, if `P` is closed under quotients,
extensions, and coproducts, then `P.rightOrthogonal.leftOrthogonal ≤ P`. Together with
`ObjectProperty.le_leftOrthogonal_rightOrthogonal`, this gives the equality
`ObjectProperty.leftOrthogonal_rightOrthogonal_eq_self`. -/
lemma leftOrthogonal_rightOrthogonal_le (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    P.rightOrthogonal.leftOrthogonal ≤ P :=
  fun X hX ↦
    let A : Subobject X := Subobject.sSup {A : Subobject X | P (A : C)}
    haveI : Epi A.arrow :=
      Preadditive.epi_of_cokernel_zero (hX (cokernel.π _) (rightOrthogonal_cokernel_sSup P X))
    P.prop_of_epi A.arrow (P.prop_subobjectSSup _ fun _ hA ↦ hA)

/-- In a well-powered abelian category with coproducts, if `P` is closed under quotients,
extensions, and coproducts, then `P.rightOrthogonal.leftOrthogonal = P`. This is the hard
direction of [S. E. Dickson][dickson1966]'s characterisation of torsion classes, see
`CategoryTheory.Abelian.isTorsionClass_iff`. -/
theorem leftOrthogonal_rightOrthogonal_eq_self (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    P.rightOrthogonal.leftOrthogonal = P :=
  le_antisymm P.leftOrthogonal_rightOrthogonal_le P.le_leftOrthogonal_rightOrthogonal

end Abelian

end ObjectProperty

end CategoryTheory
