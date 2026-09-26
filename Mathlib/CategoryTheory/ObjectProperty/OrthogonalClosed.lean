/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Subobject
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Closure properties of orthogonals

Let `P` be a property of objects in a category with zero morphisms. We show that the left
orthogonal `P.leftOrthogonal` is closed under quotients and under colimits of any shape, and,
dually, that the right orthogonal `P.rightOrthogonal` is closed under subobjects and under
limits of any shape. When the category is moreover preadditive and balanced, so that a short
exact sequence exhibits its first map as a kernel and its second map as a cokernel, both
orthogonals are also closed under extensions.

These are registered as instances of `IsClosedUnderQuotients`, `IsClosedUnderColimitsOfShape`,
`IsClosedUnderSubobjects`, `IsClosedUnderLimitsOfShape` and `IsClosedUnderExtensions`.
Together they form the easy direction of [S. E. Dickson][dickson1966]'s characterisation of
torsion classes, see `CategoryTheory.Abelian.isTorsionClass_iff`.

Conversely, in a well-powered abelian category with coproducts, we show in
`ObjectProperty.leftOrthogonal_rightOrthogonal_eq_self` that a property `P` which is closed under
quotients, extensions, and coproducts satisfies `P.rightOrthogonal.leftOrthogonal = P`. This is the
hard direction of Dickson's theorem.

## References

* [S. E. Dickson, *A torsion theory for Abelian categories*][dickson1966]
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/-- The left orthogonal of a property of objects is closed under quotients. -/
instance (P : ObjectProperty C) : P.leftOrthogonal.IsClosedUnderQuotients where
  prop_of_epi f _ hX := (P.leftOrthogonal_iff _).mpr
    fun _ g hZ ↦ zero_of_epi_comp f (hX (f ≫ g) hZ)

/-- The left orthogonal of a property of objects is closed under colimits of any shape. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isColimit.hom_ext
    intro j
    simp only [comp_zero]
    exact hX.prop_diag_obj j (hX.ι.app j ≫ f) hY

/-- The right orthogonal of a property of objects is closed under subobjects. -/
instance (P : ObjectProperty C) : P.rightOrthogonal.IsClosedUnderSubobjects where
  prop_of_mono i _ hY := (P.rightOrthogonal_iff _).mpr
    fun _ f hX ↦ zero_of_comp_mono i (hY (f ≫ i) hX)

/-- The right orthogonal of a property of objects is closed under limits of any shape. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    P.rightOrthogonal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isLimit.hom_ext
    intro j
    simp only [zero_comp]
    exact hX.prop_diag_obj j (f ≫ hX.π.app j) hY

end HasZeroMorphisms

/-! Closure under extensions uses the kernel and cokernel supplied by a short exact sequence, so
these two instances are stated for preadditive balanced categories. -/

section Extensions

variable [Preadditive C] [Balanced C]

/-- The left orthogonal of a property of objects is closed under extensions. -/
instance (P : ObjectProperty C) : P.leftOrthogonal.IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro s hs hX₁ hX₃ Z k hZ
    let t : CokernelCofork s.f := CokernelCofork.ofπ k (hX₁ (s.f ≫ k) hZ)
    let l : s.X₃ ⟶ Z := hs.gIsCokernel.desc t
    have hl : l = 0 := hX₃ l hZ
    have hfac : s.g ≫ l = k := hs.gIsCokernel.fac t WalkingParallelPair.one
    simp [← hfac, hl]

/-- The right orthogonal of a property of objects is closed under extensions. -/
instance (P : ObjectProperty C) : P.rightOrthogonal.IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro s hs hX₁ hX₃ Z k hZ
    let t : KernelFork s.g := KernelFork.ofι k (hX₃ (k ≫ s.g) hZ)
    let l : Z ⟶ s.X₁ := hs.fIsKernel.lift t
    have hl : l = 0 := hX₁ l hZ
    have hfac : l ≫ s.f = k := hs.fIsKernel.fac t WalkingParallelPair.zero
    simp [← hfac, hl]

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
  have hA' : P (A' : C) :=
    P.prop_X₂_of_shortExact (shortExact_shortComplexPullbackπCokernelπ B)
      (P.prop_sSup _ fun _ hA ↦ hA) hB
  have hle : A' ≤ A := Subobject.le_sSup _ _ hA'
  -- Hence the projection of `A'` onto `B` vanishes, so `B`, and with it the image of `f`,
  -- is zero.
  have hzero : A'.arrow ≫ cokernel.π A.arrow = 0 := by
    rw [← Subobject.ofLE_arrow hle, Category.assoc, cokernel.condition, comp_zero]
  have hπ : Subobject.pullbackπ (cokernel.π A.arrow) B = 0 := by
    apply (cancel_mono B.arrow).mp
    rw [(Subobject.isPullback (cokernel.π A.arrow) B).toCommSq.w, hzero, zero_comp]
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
    P.prop_of_epi A.arrow (P.prop_sSup _ fun _ hA ↦ hA)

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
