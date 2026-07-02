/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Properties of `P.Under ⊤ R` for `R : CommRingCat`

In this file we translate ring theoretic properties of a property of ring homomorphisms
`P` in properties of the category `P.Under ⊤ R`.

## Main results

- `CommRingCat.Under.hasFiniteLimits`: If `P` is stable under finite products and equalizers,
  `P.Under ⊤ R` has finite limits.
- `RingHom.HasStableEqualizers.preservesFiniteLimits_pushout`: If `P` has stable equalizers,
  base change along arbitrary morphisms preserve finite limits.
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
@[instance_reducible]
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

lemma RingHom.HasFiniteProducts.preservesFiniteProducts_pushout (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) [(toMorphismProperty Q).IsStableUnderCobaseChange]
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteProducts (Under.pushout (toMorphismProperty Q) ⊤ f) := by
  have := hQp.createsFiniteProductsForget hQi R
  refine ⟨fun n ↦ ⟨fun {K} ↦ ?_⟩⟩
  have : PreservesLimit K (Under.pushout (toMorphismProperty Q) ⊤ f ⋙
        Under.forget (toMorphismProperty Q) ⊤ S) := by
    rw [preservesLimit_iff_of_natIso _ (Under.pushoutCompForgetIso _)]
    infer_instance
  exact preservesLimit_of_reflects_of_preserves _ (MorphismProperty.Under.forget _ ⊤ S)

/-- If `Q` is stable under equalizers, the inclusion from the subcategory of `Under R` defined
by `Q` creates equalizers. -/
@[instance_reducible]
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
@[instance_reducible]
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

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

open RingHom

variable {P}

set_option backward.defeqAttrib.useBackward true in
lemma CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective
    {R S : CommRingCat.{u}} [Algebra R S] {A B : Under R} {f g : A ⟶ B} :
    PreservesLimit (parallelPair f g) (tensorProd R S) ↔
      Function.Bijective ((toAlgHom f).tensorEqualizer R S (toAlgHom g)) := by
  let c : Fork f g := Under.equalizerFork f g
  let hc : IsLimit c := Under.equalizerForkIsLimit f g
  let ι : R.mkUnder (AlgHom.equalizer (toAlgHom f) (toAlgHom g)) ⟶ A :=
    (AlgHom.equalizer (toAlgHom f) (toAlgHom g)).val.toUnder
  let h' := (R.tensorProd S).map ι
  have w' : h' ≫ (tensorProd R S).map f = h' ≫ (tensorProd R S).map g := by
    simpa using! congr((R.tensorProd S).map $(CommRingCat.Under.equalizer_comp f g))
  let e : IsLimit ((R.tensorProd S).mapCone c) ≃ IsLimit (Fork.ofι h' w') :=
    isLimitMapConeForkEquiv (tensorProd R S) (Under.equalizer_comp f g)
  rw [preservesLimit_iff_isLimit_mapCone hc, e.nonempty_congr,
    (Under.equalizerForkIsLimit _ _).nonempty_isLimit_iff_isIso_lift]
  have heq : (Under.equalizerForkIsLimit _ _).lift (Fork.ofι h' w') =
      (AlgHom.tensorEqualizer S S (toAlgHom f) (toAlgHom g)).toUnder ≫
        Under.homMk (CommRingCat.ofHom (.id _)) := by
    refine Fork.IsLimit.hom_ext (Under.equalizerForkIsLimit _ _) ?_
    rw [Fork.IsLimit.lift_ι]
    ext : 2
    dsimp
    ext x <;> rfl
  rw [heq, ← isIso_iff_of_reflects_iso _ (CategoryTheory.Under.forget S),
    ConcreteCategory.isIso_iff_bijective]
  rfl

lemma RingHom.HasStableEqualizers.preservesLimit_parallelPair_tensorProd
    (hPse : HasStableEqualizers P) {R S : CommRingCat.{u}} [Algebra R S]
    {A B : Under R} (f g : A ⟶ B) (hA : P A.hom.hom) (hB : P B.hom.hom) :
    PreservesLimit (parallelPair f g) (CommRingCat.tensorProd R S) := by
  rw [CommRingCat.preservesLimit_parallelPair_tensorProd_iff_tensorEqualizer_bijective]
  exact hPse _ _ hA hB

lemma RingHom.HasStableEqualizers.preservesEqualizers_pushout (hPi : RespectsIso P)
    (hPe : HasEqualizers P) (hPse : HasStableEqualizers P)
    [(toMorphismProperty P).IsStableUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (Under.pushout (toMorphismProperty P) ⊤ f) := by
  refine ⟨fun {K} ↦ ?_⟩
  have := hPe.createsLimitsWalkingParallelPair hPi R
  algebraize [f.hom]
  have : PreservesLimit (K ⋙ Under.forget (toMorphismProperty P) ⊤ R)
      (CategoryTheory.Under.pushout f) := by
    rw [← CommRingCat.ofHom_hom f,
      ← preservesLimit_iff_of_natIso _ (CommRingCat.tensorProdIsoPushout R S),
      ← preservesLimit_iff_of_iso_diagram _ (diagramIsoParallelPair _).symm]
    exact hPse.preservesLimit_parallelPair_tensorProd _ _ ((K.obj _).prop) ((K.obj _).prop)
  have : PreservesLimit K (Under.pushout (toMorphismProperty P) ⊤ f ⋙
        Under.forget (toMorphismProperty P) ⊤ S) := by
    rw [preservesLimit_iff_of_natIso _ (Under.pushoutCompForgetIso _)]
    infer_instance
  exact preservesLimit_of_reflects_of_preserves _ (Under.forget _ ⊤ S)

/-- If `P` is a property of ring homs that is stable under finite products and
equalizers, and the latter are preserved by arbitrary base change,
pushout along any ring homomorphism preserves finite limits. -/
lemma RingHom.HasStableEqualizers.preservesFiniteLimits_pushout (hPi : RingHom.RespectsIso P)
    (hPp : HasFiniteProducts P) (hPe : HasEqualizers P) (hPse : HasStableEqualizers P)
    [(toMorphismProperty P).IsStableUnderCobaseChange] {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteLimits (Under.pushout (toMorphismProperty P) ⊤ f) :=
  have := hPp.preservesFiniteProducts_pushout hPi f
  have := hPse.preservesEqualizers_pushout hPi hPe f
  have := CommRingCat.Under.hasFiniteLimits hPi hPp hPe
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _
