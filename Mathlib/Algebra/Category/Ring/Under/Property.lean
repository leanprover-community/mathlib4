/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Properties of `P.Under ⊤ R` for `R : CommRingCat`

In this file we show properties of the category of commutative rings under `R` where
the structure map satisfies some property `P`.

## Main results

- ``

-/

universe u

open CategoryTheory Limits

namespace RingHom

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- A property of ring homomorphisms `Q` is said to have equalizers, if the equalizer of algebra
maps between algebras satisfiying `Q` also satisfies `Q`. -/
def HasEqualizers (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S →ₐ[R] T), Q (algebraMap R S) → Q (algebraMap R T) →
      Q (algebraMap R (AlgHom.equalizer f g))

/-- A property of ring homomorphisms `Q` is said to have finite products, if a finite product of
algebras satisfiying `Q` also satisfies `Q`. -/
def HasFiniteProducts (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)],
    (∀ i, Q (algebraMap R (S i))) → Q (algebraMap R (Π i, S i))

--lemma HasFiniteProducts.of_finite (h : HasFiniteProducts Q) {R : Type u} [CommRing R] {ι : Type u}
--    [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
--    (H : ∀ i, Q (algebraMap R (S i))) :
--    Q (algebraMap R (Π i, S i)) := by
--  sorry

end RingHom

namespace CommRingCat

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

open MorphismProperty

variable (J : Type) [SmallCategory J] [FinCategory J]

set_option backward.isDefEq.respectTransparency false in
@[implicit_reducible]
noncomputable def Under.createsFiniteProductsForget (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (R : CommRingCat.{u}) :
    CreatesFiniteProducts (MorphismProperty.Under.forget (RingHom.toMorphismProperty Q) ⊤ R) := by
  refine .mk' _ fun (J : Type u) _ ↦ ?_
  have : (commaObj (Functor.fromPUnit R) (𝟭 _)
      (RingHom.toMorphismProperty Q)).IsClosedUnderLimitsOfShape (Discrete J) := by
    constructor
    intro (A : Under R) ⟨(pres : LimitPresentation _ A), hpres⟩
    let e : A ≅ CommRingCat.mkUnder R (Π i, pres.diag.obj ⟨i⟩) :=
      (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
        HasLimit.isoOfNatIso (Discrete.natIso fun i ↦ eqToIso <| by simp) ≪≫
        limit.isoLimitCone ⟨CommRingCat.Under.piFan <| fun i ↦ (pres.diag.obj ⟨i⟩),
          CommRingCat.Under.piFanIsLimit <| fun i ↦ (pres.diag.obj ⟨i⟩)⟩
    simp only [commaObj_iff, Functor.const_obj_obj, Functor.id_obj, ← Under.w e.inv]
    have : (RingHom.toMorphismProperty Q).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp hQi
    rw [MorphismProperty.cancel_right_of_respectsIso (P := RingHom.toMorphismProperty Q)]
    exact hQp _ fun i ↦ hpres _
  apply +allowSynthFailures (Comma.forgetCreatesLimitsOfShapeOfClosed _)

lemma Under.hasFiniteProducts (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (R : CommRingCat.{u}) :
    HasFiniteProducts ((RingHom.toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun n ↦ ⟨fun D ↦ ?_⟩⟩
  have := CommRingCat.Under.createsFiniteProductsForget hQi hQp R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

set_option backward.isDefEq.respectTransparency false in
@[implicit_reducible]
noncomputable
def Under.createsEqualizersForget (hQi : RingHom.RespectsIso Q)
    (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesLimitsOfShape WalkingParallelPair
      (MorphismProperty.Under.forget (RingHom.toMorphismProperty Q) ⊤ R) := by
  have :
      (commaObj (Functor.fromPUnit R) (𝟭 _)
        (RingHom.toMorphismProperty Q)).IsClosedUnderLimitsOfShape
      WalkingParallelPair := by
    constructor
    intro (A : Under R) ⟨(pres : LimitPresentation _ A), hpres⟩
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
    have := Under.w e.inv
    simp only [commaObj_iff, Functor.const_obj_obj, Functor.id_obj]
    rw [← this]
    have : (RingHom.toMorphismProperty Q).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp hQi
    rw [MorphismProperty.cancel_right_of_respectsIso (P := RingHom.toMorphismProperty Q)]
    exact hQe _ _ (hpres .zero) (hpres .one)
  apply Comma.forgetCreatesLimitsOfShapeOfClosed

@[implicit_reducible]
noncomputable
def Under.createsFiniteLimitsForget (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) := by
  have := CommRingCat.Under.createsFiniteProductsForget hQi hQp
  have := CommRingCat.Under.createsEqualizersForget hQi hQe
  apply createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts

lemma Under.hasEqualizers (hQi : RingHom.RespectsIso Q)
    (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    HasEqualizers ((RingHom.toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun D ↦ ?_⟩
  have := CommRingCat.Under.createsEqualizersForget hQi hQe R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

lemma Under.hasFiniteLimits (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    HasFiniteLimits ((RingHom.toMorphismProperty Q).Under ⊤ R) :=
  have := CommRingCat.Under.hasFiniteProducts hQi hQp
  have := CommRingCat.Under.hasEqualizers hQi hQe
  hasFiniteLimits_of_hasEqualizers_and_finite_products

set_option backward.isDefEq.respectTransparency false in
lemma Under.property_limit_of_hasFiniteProducts_of_hasEqualizers
    (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q)
    {R : CommRingCat.{u}} (D : J ⥤ Under R) (h : ∀ j, Q (D.obj j).hom.hom) :
    Q (limit D).hom.hom := by
  have := CommRingCat.Under.hasFiniteLimits hQi hQp hQe
  let D' : J ⥤ (RingHom.toMorphismProperty Q).Under ⊤ R :=
    MorphismProperty.Comma.lift D h (by simp) (by simp)
  let A := limit D'
  have : CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) :=
    CommRingCat.Under.createsFiniteLimitsForget hQi hQp hQe R
  let e : (Under.forget _ _ R).obj A ≅ limit D :=
    preservesLimitIso (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) D'
  have := CategoryTheory.Under.w e.hom
  rw [← this, CommRingCat.hom_comp, hQi.cancel_right_isIso]
  exact A.prop

end CommRingCat
