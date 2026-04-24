/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Properties of `P.Under ⊤ R` for `R : CommRingCat`

In this file we translate ring theoretic properties of a property of ring homomorphisms
`P` in properties of the category `P.Under ⊤ R`.

## Main results

- `CommRingCat.Under.hasFiniteLimits`: If `P` is stable under finite products and equalizers,
  `P.Under ⊤ R` has finite limits.
-/

@[expose] public section

universe u

open CategoryTheory Limits

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

open MorphismProperty

lemma RingHom.HasFiniteProducts.isClosedUnderLimitsOfShape (hQi : RespectsIso Q)
    (hQp : HasFiniteProducts Q) (R : CommRingCat.{u}) :
    (toMorphismProperty Q).underObj (X := R).IsClosedUnderFiniteProducts := by
  refine .of_isClosedUnderLimitsOfShape fun (J : Type u) _ ↦ ⟨fun A ⟨pres, hpres⟩ ↦ ?_⟩
  let e : A ≅ CommRingCat.mkUnder R (Π i, pres.diag.obj ⟨i⟩) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.isoOfNatIso (Discrete.natIso fun i ↦ eqToIso <| by simp) ≪≫
      limit.isoLimitCone ⟨CommRingCat.Under.piFan <| fun i ↦ (pres.diag.obj ⟨i⟩),
        CommRingCat.Under.piFanIsLimit <| fun i ↦ (pres.diag.obj ⟨i⟩)⟩
  have : (toMorphismProperty Q).RespectsIso := toMorphismProperty_respectsIso_iff.mp hQi
  rw [underObj_iff, ← Under.w e.inv, (toMorphismProperty Q).cancel_right_of_respectsIso]
  exact hQp _ fun i ↦ hpres _

lemma RingHom.HasEqualizers.isClosedUnderLimitsOfShape (hQi : RespectsIso Q)
    (hQe : HasEqualizers Q) (R : CommRingCat.{u}) :
    (toMorphismProperty Q).underObj (X := R).IsClosedUnderLimitsOfShape WalkingParallelPair := by
  refine ⟨fun A ⟨pres, hpres⟩ ↦ ?_⟩
  let e : A ≅
      CommRingCat.mkUnder R
        (AlgHom.equalizer (R := R)
          (CommRingCat.toAlgHom (pres.diag.map .left))
          (CommRingCat.toAlgHom (pres.diag.map .right))) :=
    (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
      HasLimit.isoOfNatIso (diagramIsoParallelPair _) ≪≫ limit.isoLimitCone
        ⟨CommRingCat.Under.equalizerFork (pres.diag.map .left) (pres.diag.map .right),
          CommRingCat.Under.equalizerForkIsLimit
            (pres.diag.map .left) (pres.diag.map .right)⟩
  have : (toMorphismProperty Q).RespectsIso := toMorphismProperty_respectsIso_iff.mp hQi
  rw [underObj_iff, ← Under.w e.inv, (toMorphismProperty Q).cancel_right_of_respectsIso]
  exact hQe _ _ (hpres .zero) (hpres .one)

/-- If `Q` is stable under finite products, the inclusion from the subcategory of `Under R` defined
by `Q` creates finite products. -/
@[implicit_reducible]
noncomputable def RingHom.HasFiniteProducts.createsFiniteProductsForget
    (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q) (R : CommRingCat.{u}) :
    CreatesFiniteProducts (MorphismProperty.Under.forget (toMorphismProperty Q) ⊤ R) := by
  refine .mk' _ fun (J : Type u) _ ↦ ?_
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  have := hQp.isClosedUnderLimitsOfShape hQi R
  exact inferInstanceAs <| (toMorphismProperty Q).underObj.IsClosedUnderLimitsOfShape _

lemma RingHom.HasFiniteProducts.hasFiniteProducts (hQi : RespectsIso Q) (hQp : HasFiniteProducts Q)
    (R : CommRingCat.{u}) :
    Limits.HasFiniteProducts ((RingHom.toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun n ↦ ⟨fun D ↦ ?_⟩⟩
  have := hQp.createsFiniteProductsForget hQi R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

/-- If `Q` is stable under equalizers, the inclusion from the subcategory of `Under R` defined
by `Q` creates equalizers. -/
@[implicit_reducible]
noncomputable def RingHom.HasEqualizers.createsLimitsWalkingParallelPair (hQi : RespectsIso Q)
    (hQe : HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesLimitsOfShape WalkingParallelPair
      (MorphismProperty.Under.forget (toMorphismProperty Q) ⊤ R) := by
  apply +allowSynthFailures Comma.forgetCreatesLimitsOfShapeOfClosed
  exact hQe.isClosedUnderLimitsOfShape hQi _

lemma RingHom.HasEqualizers.hasEqualizers (hQi : RespectsIso Q) (hQe : HasEqualizers Q)
    (R : CommRingCat.{u}) :
    Limits.HasEqualizers ((toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun D ↦ ?_⟩
  have := hQe.createsLimitsWalkingParallelPair hQi R
  exact hasLimit_of_created D (Under.forget _ _ R)

namespace CommRingCat

/-- If `Q` is stable under finite products and equalizers, the inclusion from the subcategory of
`Under R` defined by `Q` creates finite limits. -/
@[implicit_reducible]
noncomputable def Under.createsFiniteLimitsForget (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) :=
  letI := hQp.createsFiniteProductsForget hQi
  letI := hQe.createsLimitsWalkingParallelPair hQi
  createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts _

lemma Under.hasFiniteLimits (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    HasFiniteLimits ((RingHom.toMorphismProperty Q).Under ⊤ R) :=
  have := hQp.hasFiniteProducts hQi
  have := hQe.hasEqualizers hQi
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end CommRingCat
