-- `Mathlib/AlgebraicGeometry/Morphisms/ValuativeCriterion
import Mathlib.ValuativeCriterion.Proper
import Mathlib.ValuativeCriterion.Immersion
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.ValuativeCriterion.ValuationRing
import Mathlib.ValuativeCriterion.ResidueField
import Mathlib.ValuativeCriterion.Lemmas

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

structure ValuativeCommSq {X Y : Scheme.{u}} (f : X ⟶ Y) where
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [valuationRing : ValuationRing R]
  K : Type u
  [field : Field K]
  [algebra : Algebra R K]
  [isFractionRing : IsFractionRing R K]
  (i₁ : Spec (.of K) ⟶ X)
  (i₂ : Spec (.of R) ⟶ Y)
  (commSq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap R K))) f i₂)

namespace ValuativeCommSq

attribute [instance] commRing domain valuationRing field algebra isFractionRing

end ValuativeCommSq

def ValuativeCriterion.Existence : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, S.commSq.HasLift

def ValuativeCriterion.Uniqueness : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, Subsingleton S.commSq.LiftStruct

def ValuativeCriterion : MorphismProperty Scheme :=
  fun _ _ f ↦ ∀ S : ValuativeCommSq f, Nonempty (Unique (S.commSq.LiftStruct))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

namespace Existence

/--
Uses `exists_factor_valuationRing` and `Scheme.fromSpecResidueField`.

https://stacks.math.columbia.edu/tag/01KE
-/
lemma specializingMap (H : ValuativeCriterion.Existence f) :
    SpecializingMap f.1.base := by
      intro x' y h
      let y' := f.val.base x'
      let ι_stalk_y := Y.fromSpecStalk y

      let stalk_y_to_residue_x' : Y.stalk (y) ⟶ (X.residueField x') :=
        (Y.presheaf.stalkSpecializes h) ≫ (PresheafedSpace.stalkMap f.1 x') ≫ (X.toResidueField x')

      let f₁ := Spec.map stalk_y_to_residue_x'
      let f₂ := X.fromSpecResidueField x'

      have comm₁ : f₁ ≫ ι_stalk_y = f₂ ≫ f := by
        simp_all only [Spec.map_comp, Category.assoc, f₁, y', stalk_y_to_residue_x', ι_stalk_y, f₂]
        rw [@Scheme.stalkSpecializes_fromSpecStalk]
        rw [@Scheme.stalkMap_fromSpecStalk]
        rfl

      let A := (exists_factor_valuationRing stalk_y_to_residue_x').choose
      let hA := (exists_factor_valuationRing stalk_y_to_residue_x').choose_spec.choose
      let stalk_y_to_A_is_local := (exists_factor_valuationRing stalk_y_to_residue_x').choose_spec.choose_spec

      let A_to_residue_x' := CommRingCat.ofHom A.subtype
      let stalk_y_to_A := CommRingCat.ofHom <| stalk_y_to_residue_x'.codRestrict _ hA

      have obivious : stalk_y_to_A ≫ A_to_residue_x' = stalk_y_to_residue_x' := rfl

      have comm₂ : f₁ = Spec.map A_to_residue_x' ≫ Spec.map stalk_y_to_A := by
        rw [← @Spec.map_comp]
        simp_all only [f₁]

      have w : f₂ ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫
            Spec.map stalk_y_to_A ≫ Y.fromSpecStalk y := by
        rw [← comm₁, comm₂]
        simp_all only [Spec.map_comp, Category.assoc, CommRingCat.coe_comp_of, RingHom.coe_comp, Function.comp_apply,
          f₁, stalk_y_to_residue_x', ι_stalk_y, f₂, stalk_y_to_A, A_to_residue_x', A]
        rfl

      let commSq : ValuativeCommSq f := {
        R := A
        commRing := inferInstance
        domain := inferInstance
        valuationRing := inferInstance
        K := X.residueField x'
        field := inferInstance
        algebra := Algebra.ofSubring A.toSubring
        isFractionRing := ValuationSubring.instIsFractionRingSubtypeMem A
        i₁ := f₂
        i₂ := Spec.map stalk_y_to_A ≫ Y.fromSpecStalk y
        commSq := ⟨w⟩
      }

      let l := Classical.choice (H commSq).exists_lift
      let x := l.l.val.base <| LocalRing.closedPoint A

      have hx' : x' ⤳ x := by
        have x'_eq_f₂_cls_pt : f₂.val.base (LocalRing.closedPoint <| X.residueField x') = x' :=
          Scheme.fromSpecResidueField_apply x' (LocalRing.closedPoint (Scheme.residueField x'))

        have that : (Spec.map A_to_residue_x').val.base (LocalRing.closedPoint <| X.residueField x')
            ⤳ LocalRing.closedPoint A := by
          have : LocalRing (CommRingCat.of A) := ValuationSubring.localRing A
          apply LocalRing.specializes_closedPoint

        rw [← x'_eq_f₂_cls_pt]
        simp only [x]

        have : f₂.val.base = (Spec.map (CommRingCat.ofHom (algebraMap commSq.R commSq.K)) ≫ l.l).val.base := by rw [l.fac_left]
        rw [this]
        exact
          schemePreservesSpec (Spec (CommRingCat.of ↥A)) X l.l (LocalRing.closedPoint ↥A)
            ((Spec.map (CommRingCat.ofHom (algebraMap commSq.R commSq.K))).val.base
              (LocalRing.closedPoint ↑(Scheme.residueField x')))
                that

      have hx : f.val.base x = y := by
        simp only [x]
        rw [← @Scheme.comp_val_base_apply]
        rw [l.fac_right]
        simp only [Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply]
        have :
            (Spec.map stalk_y_to_A).val.base (LocalRing.closedPoint A) =
              LocalRing.closedPoint (Y.stalk y) := by
          have : LocalRing <| CommRingCat.of (Y.stalk y) := LocallyRingedSpace.stalkLocal Y.toLocallyRingedSpace y
          have : LocalRing <| CommRingCat.of A := ValuationSubring.localRing A
          have : IsLocalRingHom stalk_y_to_A := stalk_y_to_A_is_local
          apply LocalRing.comap_closedPoint
        change (Y.fromSpecStalk y).val.base ((Spec.map stalk_y_to_A).val.base (LocalRing.closedPoint A)) = y
        rw [this]
        exact Y.fromSpecStalk_closedPoint

      use x
      exact ⟨hx', hx⟩

/--
Uses `bijective_rangeRestrict_comp_of_valuationRing` and `stalkClosedPointTo`

https://stacks.math.columbia.edu/tag/01KE first half
-/
lemma of_specializingMap
    (H : (MorphismProperty.topologically @SpecializingMap).universally f) :
    ValuativeCriterion.Existence f := sorry

/-- by def -/
lemma stableUnderBaseChange :
    ValuativeCriterion.Existence.StableUnderBaseChange := sorry

/-- by the three lemmas above -/
lemma eq :
    ValuativeCriterion.Existence = (MorphismProperty.topologically @SpecializingMap).universally :=
  sorry

/-- by `ValuativeCriterion.Existence.eq` and `universallyClosed_iff_specializingMap`. -/
lemma _root_.AlgebraicGeometry.universallyClosed_of_valuativeCriterion [QuasiCompact f]
    (hf : ValuativeCriterion.Existence f) : UniversallyClosed f := sorry

/-- by `ValuativeCriterion.Existence.eq` and `universallyClosed_eq_universallySpecializing`. -/
lemma _root_.AlgebraicGeometry.universallyClosed_eq_valuativeCriterion :
    @UniversallyClosed = ValuativeCriterion.Existence ⊓ @QuasiCompact := sorry

end Existence

section Uniqueness

/--
Needs `IsImmersion (pullback.diagonal f)`, `IsClosedImmersion.of_isImmersion`,
`universallyClosed_of_valuativeCriterion`.

https://stacks.math.columbia.edu/tag/01L0
-/
lemma isSeparated_of_valuativeCriterion [QuasiSeparated f]
    (hf : ValuativeCriterion.Uniqueness f) : IsSeparated f := sorry

/--
https://stacks.math.columbia.edu/tag/01KZ
-/
lemma IsSeparated.valuativeCriterion [IsSeparated f] :
    ValuativeCriterion.Uniqueness f := by
  intros S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  ext
  dsimp at *
  have h := hl₁'.trans hl₂'.symm
  let Z := pullback (pullback.diagonal f) (pullback.lift l₁ l₂ h)
  let g : Z ⟶ Spec (.of S.R) := pullback.snd _ _
  have : IsClosedImmersion g := sorry -- by `IsClosedImmersion.isStableUnderBaseChange`
  have : IsAffine Z := sorry -- by `IsClosedImmersion g` and `IsClosedImmersion.iff_of_isAffine`
  suffices IsIso g by
    sorry -- by category theory
  suffices Function.Bijective (g.app ⊤) by
    sorry -- by `isIso_iff_of_isAffine`
  constructor
  · let l : Spec (.of S.K) ⟶ Z := sorry
    have hg : l ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) := sorry
    sorry -- Γ of rhs of hg is injective.
  · sorry -- by `IsClosedImmersion g` and `IsClosedImmersion.iff_of_isAffine`

-- by lemmas above
lemma IsSeparated_eq_valuativeCriterion :
    @IsSeparated = ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated := sorry

end Uniqueness

-- by definition
lemma valuativeCriterion_eq :
    ValuativeCriterion = ValuativeCriterion.Existence ⊓ ValuativeCriterion.Uniqueness := sorry

-- by lemmas above and `isProper_eq`
lemma proper_eq_ValuativeCriterion :
    @IsProper = ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType := sorry

end AlgebraicGeometry
