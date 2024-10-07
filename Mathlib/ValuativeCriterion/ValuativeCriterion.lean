-- `Mathlib/AlgebraicGeometry/Morphisms/ValuativeCriterion
import Mathlib.ValuativeCriterion.Proper
import Mathlib.ValuativeCriterion.Immersion
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.ValuativeCriterion.ValuationRing
import Mathlib.ValuativeCriterion.ResidueField
import Mathlib.ValuativeCriterion.Lemmas
import Mathlib.ValuativeCriterion.UniversallyClosed
set_option maxHeartbeats 0

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

  let stalk_y_to_residue_x' : Y.presheaf.stalk y ⟶ (X.residueField x') :=
    (Y.presheaf.stalkSpecializes h) ≫ (f.stalkMap x') ≫ (X.toResidueField x')

  let f₁ := Spec.map stalk_y_to_residue_x'
  let f₂ := X.fromSpecResidueField x'

  have comm₁ : f₁ ≫ ι_stalk_y = f₂ ≫ f := by
    simp_all only [Spec.map_comp, Category.assoc, f₁, y', stalk_y_to_residue_x', ι_stalk_y, f₂]
    rw [@Scheme.stalkSpecializes_fromSpecStalk]
    rw [@Scheme.stalkMap_fromSpecStalk]
    rfl

  let A := (exists_factor_valuationRing stalk_y_to_residue_x').choose
  let hA := (exists_factor_valuationRing stalk_y_to_residue_x').choose_spec.choose
  let stalk_y_to_A_is_local :=
    (exists_factor_valuationRing stalk_y_to_residue_x').choose_spec.choose_spec

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
    simp_all only [Spec.map_comp, Category.assoc, CommRingCat.coe_comp_of, RingHom.coe_comp,
      Function.comp_apply,
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

    have : f₂.val.base =
        (Spec.map (CommRingCat.ofHom (algebraMap commSq.R commSq.K)) ≫ l.l).val.base := by
      rw [l.fac_left]
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
          LocalRing.closedPoint (Y.presheaf.stalk y) := by
      have : LocalRing <| CommRingCat.of (Y.presheaf.stalk y) :=
        Y.toLocallyRingedSpace.localRing y
      have : LocalRing <| CommRingCat.of A := ValuationSubring.localRing A
      have : IsLocalRingHom stalk_y_to_A := stalk_y_to_A_is_local
      apply LocalRing.comap_closedPoint
    change (Y.fromSpecStalk y).val.base
      ((Spec.map stalk_y_to_A).val.base (LocalRing.closedPoint A)) = y
    rw [this]
    exact Y.fromSpecStalk_closedPoint

  use x
  exact ⟨hx', hx⟩

/--
Uses `bijective_rangeRestrict_comp_of_valuationRing` and `stalkClosedPointTo`

https://stacks.math.columbia.edu/tag/01KE first half
-/
lemma of_specializingMap
    (H : (AlgebraicGeometry.topologically @SpecializingMap).universally f) :
      ValuativeCriterion.Existence f := by
  intro c
  rcases c with
    @⟨R, commRing, domain, valuationRing, K, field, algebra, isFractionRing, i₁, i₂, commSq⟩
  letI : IsDomain (CommRingCat.of R) := domain
  letI : ValuationRing (CommRingCat.of R) := valuationRing
  letI : LocalRing (CommRingCat.of R) := ValuationRing.localRing (CommRingCat.of R)
  have H' := H (pullback.snd i₂ f) i₂ (pullback.fst i₂ f) (IsPullback.of_hasPullback i₂ f)

  let lft := pullback.lift (Spec.map <| CommRingCat.ofHom <| algebraMap R K) i₁ commSq.w.symm

  let XR := pullback i₂ f
  let XR_to_Spec_R := pullback.fst i₂ f
  let XR_to_X := pullback.snd i₂ f
  let Spec_K_to_Spec_R := Spec.map <| CommRingCat.ofHom <| algebraMap R K

  have comm₁ := pullback.lift_fst Spec_K_to_Spec_R i₁ commSq.w.symm
  have comm₂ := pullback.lift_snd Spec_K_to_Spec_R i₁ commSq.w.symm

  let x' := lft.val.base <| LocalRing.closedPoint K
  let y' := (pullback.fst i₂ f).val.base x'
  let y := LocalRing.closedPoint R
  have y'_spec_to_y : y' ⤳ y := by apply LocalRing.specializes_closedPoint

  let x := (H' y'_spec_to_y).choose
  have ⟨hx', hx⟩ := (H' y'_spec_to_y).choose_spec
  change x' ⤳ x at hx'

  let image_x := (pullback.fst i₂ f).val.base x
  letI h_image_x : IsClosedPoint image_x := ⟨hx⟩

  let R_y_to_XR_x := XR_to_Spec_R.stalkMap x
  let XR_x_to_XR_x' := TopCat.Presheaf.stalkSpecializes XR.presheaf hx'
  let XR_x'_to_K := Scheme.stalkClosedPointTo lft

  let R_to_K := CommRingCat.ofHom <| algebraMap R K
  let XR_x_to_K := XR_x_to_XR_x' ≫ XR_x'_to_K
  let R_y_to_R_x' := stalk_cls_pt_to image_x
  let R_x'_to_R := stalkClosedPointIso <| CommRingCat.of R
  let R_to_XR_x :=
    R_x'_to_R.inv
      ≫ R_y_to_R_x'
        ≫ R_y_to_XR_x
  let comp := R_to_XR_x ≫ XR_x_to_K

  have comm : R_to_K = comp := by
    apply Spec.map_inj.mp
    simp only [
      Category.assoc, Spec.map_comp,
      comp, R_to_XR_x, XR_x_to_K,
      R_y_to_XR_x, R_y_to_R_x', R_x'_to_R]

    have : Spec.map (stalk_cls_pt_to image_x) ≫
        Spec.map (stalkClosedPointIso (CommRingCat.of R)).inv
          = Spec.map (stalkClosedPointIso' image_x).inv := by
      rw [← Spec.map_comp]
      apply Spec.map_inj.mpr
      rfl
    rw [this]
    rw [stalkClosedPointIso_fromSpecStalk']
    have : Spec.map (XR_to_Spec_R.stalkMap x)
        ≫ (Spec (CommRingCat.of (CommRingCat.of R))).fromSpecStalk image_x
          = XR.fromSpecStalk x
            ≫ XR_to_Spec_R :=
      Scheme.stalkMap_fromSpecStalk XR_to_Spec_R
    rw [this]
    have := Scheme.stalkSpecializes_fromSpecStalk hx'
    rw [reassoc_of% this]
    have : Spec.map R_to_K = lft ≫ XR_to_Spec_R := comm₁.symm
    rw [this]
    have : lft = Spec.map (Scheme.stalkClosedPointTo lft) ≫ XR.fromSpecStalk _ :=
        (Scheme.Spec_stalkClosedPointTo_fromSpecStalk lft).symm
    rw [this]
    simp only [CommRingCat.coe_of, Category.assoc]

  let R_in_K := LocalSubring.range R_to_K
  let R_in_K_via_comp := LocalSubring.range comp
  let R_in_K_as_val := val_subriing_from_val_ring R K
  let XR_x_in_K := LocalSubring.range XR_x_to_K

  haveI : IsLocalRingHom R_y_to_XR_x :=
    inferInstanceAs <| IsLocalRingHom (LocallyRingedSpace.Hom.stalkMap _ _)
  letI R_to_XR_x_is_local : IsLocalRingHom R_to_XR_x :=
    CommRingCat.isLocalRingHom_comp (stalkClosedPointIso (CommRingCat.of R)).inv
      (((Spec (CommRingCat.of R)).presheaf.stalkCongr (congrArg nhds hx)).inv ≫ R_y_to_XR_x)

  have R_leq_XR_x : R_in_K_via_comp ≤ XR_x_in_K := by apply domination_preserved_by_range

  have R_as_val_eq_R : R_in_K = R_in_K_as_val.toLocalSubring := by
    rw [val_subriing_from_val_ring_eq_local_subring_inclusion]
    rfl

  have R_in_K_eq_R_in_K_via_comp : R_in_K = R_in_K_via_comp := congrArg LocalSubring.range comm

  have R_as_val_leq_XR_x : R_in_K_as_val.toLocalSubring ≤ XR_x_in_K := by
    rwa [← R_as_val_eq_R, R_in_K_eq_R_in_K_via_comp]

  have R_as_val_eq_XR_x : R_in_K_as_val.toLocalSubring = XR_x_in_K :=
    val_ring_is_max R_in_K_as_val XR_x_in_K R_as_val_leq_XR_x

  have R_eq_XR_x_in_K : R_in_K = XR_x_in_K := by
    rw [← R_as_val_eq_XR_x, R_as_val_eq_R]

  let XR_x_to_R := CommRingCat.ofHom <|
    map_to_injective_range
      (NoZeroSMulDivisors.algebraMap_injective R K)
        (congrArg Subtype.val R_eq_XR_x_in_K)

  let Spec_R_to_XR := (Spec.map XR_x_to_R) ≫ XR.fromSpecStalk x
  have that : XR_x_to_R ≫ R_to_K = XR_x_to_K :=
    map_to_injective_range_comm
      (NoZeroSMulDivisors.algebraMap_injective R K)
        (congrArg Subtype.val R_eq_XR_x_in_K)
  have sec : Spec_K_to_Spec_R ≫ Spec.map XR_x_to_R = Spec.map XR_x_to_K := by
    calc
      _ = Spec.map (XR_x_to_R ≫ R_to_K) := (Spec.map_comp XR_x_to_R R_to_K).symm
      _ = Spec.map XR_x_to_K := congrArg Spec.map that

  have that' := map_to_injective_range_retract
    (NoZeroSMulDivisors.algebraMap_injective R K)
      (congrArg Subtype.val R_eq_XR_x_in_K)
        R_to_XR_x
          comm
  have : R_to_XR_x ≫ XR_x_to_R = 𝟙 _ := that'
  have : Spec.map (R_to_XR_x ≫ XR_x_to_R) = 𝟙 _ := by
    rw [this]
    exact Spec.map_id (CommRingCat.of R)
  have : Spec.map XR_x_to_R ≫ Spec.map R_to_XR_x = 𝟙 _ := by
    rw [← this]
    exact Eq.symm (Spec.map_comp R_to_XR_x XR_x_to_R)
  have sec' : Spec_R_to_XR ≫ XR_to_Spec_R = 𝟙 _ := by
    simp only [Spec_R_to_XR, XR_to_Spec_R]
    have t : (XR.fromSpecStalk x) ≫ pullback.fst i₂ f = Spec.map R_to_XR_x := by
      simp only [R_to_XR_x, R_x'_to_R, R_y_to_R_x', R_y_to_XR_x, Spec.map_comp, Category.assoc]
      have : Spec.map (stalk_cls_pt_to image_x) ≫
          Spec.map (stalkClosedPointIso (CommRingCat.of R)).inv =
            Spec.map (stalkClosedPointIso' image_x).inv := by
        rw [← Spec.map_comp]
        rw [stalkClosedPointIso']
      rw [this]
      rw [stalkClosedPointIso_fromSpecStalk']
      rw [← Scheme.stalkMap_fromSpecStalk]
      rfl
    rw [← this]
    rw [← t]
    rfl

  let l := Spec_R_to_XR ≫ XR_to_X
  have fac_left : Spec_K_to_Spec_R ≫ l = i₁ := by
    simp only [l, Spec_R_to_XR,XR_x_to_R, Category.assoc]
    change Spec_K_to_Spec_R ≫ Spec.map XR_x_to_R ≫ XR.fromSpecStalk x ≫ XR_to_X = i₁
    rw [reassoc_of% sec]
    rw [← comm₂]
    simp only [XR_to_X]
    have : Spec.map XR_x_to_K ≫ XR.fromSpecStalk x = lft := by
      simp only [XR_x_to_K]
      simp only [Spec.map_comp, Category.assoc, XR_x_to_XR_x', XR_x'_to_K]
      rw [Scheme.stalkSpecializes_fromSpecStalk]
      apply Scheme.Spec_stalkClosedPointTo_fromSpecStalk
    rw [reassoc_of% this]
  have fac_right : l ≫ f = i₂ := by
    calc
      _ = Spec_R_to_XR ≫ XR_to_X ≫ f := rfl
      _ = Spec_R_to_XR ≫ XR_to_Spec_R ≫ i₂ :=
        congrArg (CategoryStruct.comp Spec_R_to_XR) pullback.condition.symm
      _ = (Spec_R_to_XR ≫ XR_to_Spec_R) ≫ i₂ := rfl
      _ = i₂ := by simp only [sec', Category.id_comp]

  exact ⟨⟨⟨l, fac_left, fac_right⟩⟩⟩

/-- by def -/
lemma stableUnderBaseChange :
    ValuativeCriterion.Existence.StableUnderBaseChange := by
  intros Y' X X' Y  Y'_to_Y f X'_to_X f' hP hf commSq

  -- let Spec_K_to_X' := commSq.i₁
  -- let Spec_R_to_Y' := commSq.i₂

  let commSq' : ValuativeCommSq f := {
    R := commSq.R
    commRing := by infer_instance
    domain := by infer_instance
    valuationRing := by infer_instance
    K := commSq.K
    field := by infer_instance
    algebra := by infer_instance
    isFractionRing := by infer_instance
    i₁ := commSq.i₁ ≫ X'_to_X
    i₂ := commSq.i₂ ≫ Y'_to_Y
    commSq := {
      w := by
        simp only [Category.assoc]
        rw [hP.w]
        rw [reassoc_of% commSq.commSq.w]
    }
  }

  let lift := (hf commSq').exists_lift.some
  have lift_comm₁ := lift.fac_left
  have lift_comm₂ := lift.fac_right

  have comm₁ : lift.l ≫ f = commSq.i₂ ≫ Y'_to_Y := by
    simp_all only [commSq', lift]

  let l := hP.lift lift.l commSq.i₂ comm₁
  have fac_left :
      Spec.map (CommRingCat.ofHom (algebraMap commSq.R commSq.K)) ≫ l = commSq.i₁ := by
    apply hP.hom_ext
    · aesop
    · simp only [Category.assoc]
      rw [hP.lift_snd]
      rw [commSq.commSq.w]
  have fac_right : l ≫ f' = commSq.i₂ := hP.lift_snd _ _ _

  exact ⟨⟨⟨l, fac_left, fac_right⟩⟩⟩

/-- by the three lemmas above -/
lemma eq : ValuativeCriterion.Existence =
    (AlgebraicGeometry.topologically @SpecializingMap).universally := by
  ext
  constructor
  · intro _
    apply MorphismProperty.universally_mono
    · apply specializingMap
    · rwa [MorphismProperty.StableUnderBaseChange.universally_eq stableUnderBaseChange]
  · apply of_specializingMap

/-- by `ValuativeCriterion.Existence.eq` and `universallyClosed_iff_specializingMap`. -/
lemma _root_.AlgebraicGeometry.universallyClosed_of_valuativeCriterion [QuasiCompact f]
    (hf : ValuativeCriterion.Existence f) : UniversallyClosed f := by
  rw [eq] at hf
  apply (AlgebraicGeometry.universallyClosed_iff_specializingMap f).mpr
  exact hf

/-- by `ValuativeCriterion.Existence.eq` and `universallyClosed_eq_universallySpecializing`. -/
lemma _root_.AlgebraicGeometry.universallyClosed_eq_valuativeCriterion :
    @UniversallyClosed = ValuativeCriterion.Existence ⊓ @QuasiCompact := by
  ext X Y f
  constructor
  · intro hf
    have h₁ : ValuativeCriterion.Existence f := by
      apply of_specializingMap
      rwa [← AlgebraicGeometry.universallyClosed_iff_specializingMap]
    have h₂ : QuasiCompact f := by infer_instance
    exact ⟨h₁, h₂⟩
  · intro ⟨h₁, h₂⟩
    rw [AlgebraicGeometry.universallyClosed_eq_universallySpecializing]
    have : (topologically @SpecializingMap).universally f := by
      rwa [eq] at h₁
    exact ⟨this, h₂⟩

end Existence

section Uniqueness

/--
Needs `IsImmersion (pullback.diagonal f)`, `IsClosedImmersion.of_isImmersion`,
`universallyClosed_of_valuativeCriterion`.

https://stacks.math.columbia.edu/tag/01L0
-/
lemma isSeparated_of_valuativeCriterion [QuasiSeparated f]
    (hf : ValuativeCriterion.Uniqueness f) : IsSeparated f where
  diagonal_isClosedImmersion := by
    suffices h : ValuativeCriterion.Existence (pullback.diagonal f) by
      have : QuasiCompact (pullback.diagonal f) :=
        AlgebraicGeometry.QuasiSeparated.diagonalQuasiCompact
      apply IsClosedImmersion.of_isImmersion
      apply IsClosedMap.isClosed_range
      apply (topologically @IsClosedMap).universally_le
      exact (universallyClosed_of_valuativeCriterion (pullback.diagonal f) h).out
    intro S
    have hc : CommSq S.i₁ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
        f (S.i₂ ≫ pullback.fst f f ≫ f) := ⟨by simp [← S.commSq.w_assoc]⟩
    let S' : ValuativeCommSq f := ⟨S.R, S.K, S.i₁, S.i₂ ≫ pullback.fst f f ≫ f, hc⟩
    have : Subsingleton S'.commSq.LiftStruct := hf S'
    let S'l₁ : S'.commSq.LiftStruct := ⟨S.i₂ ≫ pullback.fst f f,
      by simp [← S.commSq.w_assoc], by simp⟩
    let S'l₂ : S'.commSq.LiftStruct := ⟨S.i₂ ≫ pullback.snd f f,
      by simp [← S.commSq.w_assoc], by simp [pullback.condition]⟩
    have h₁₂ : S'l₁ = S'l₂ := Subsingleton.elim _ _
    constructor
    constructor
    refine ⟨S.i₂ ≫ pullback.fst _ _, ?_, ?_⟩
    · simp [← S.commSq.w_assoc]
    · simp
      apply IsPullback.hom_ext (IsPullback.of_hasPullback _ _)
      · simp
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        exact congrArg CommSq.LiftStruct.l h₁₂

/--
https://stacks.math.columbia.edu/tag/01KZ
-/
lemma IsSeparated.valuativeCriterion [IsSeparated f] :
    ValuativeCriterion.Uniqueness f := by
  intros S
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  ext : 1
  dsimp at *
  have h := hl₁'.trans hl₂'.symm
  let Z := pullback (pullback.diagonal f) (pullback.lift l₁ l₂ h)
  let g : Z ⟶ Spec (.of S.R) := pullback.snd _ _
  have : IsClosedImmersion g := IsClosedImmersion.isStableUnderBaseChange.snd _ _ inferInstance
  have hZ : IsAffine Z := by
    rw [IsClosedImmersion.iff_of_isAffine] at this
    exact this.left
  suffices IsIso g by
    rw [← cancel_epi g]
    conv_lhs => rw [← pullback.lift_fst l₁ l₂ h, ← pullback.condition_assoc]
    conv_rhs => rw [← pullback.lift_snd l₁ l₂ h, ← pullback.condition_assoc]
    simp
  suffices h : Function.Bijective (g.app ⊤) by
    rw [isIso_iff_of_isAffine]
    exact ⟨hZ, h⟩
  constructor
  · let l : Spec (.of S.K) ⟶ Z := by
      apply pullback.lift S.i₁ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
      apply IsPullback.hom_ext (IsPullback.of_hasPullback _ _)
      simpa using hl₁.symm
      simpa using hl₂.symm
    have hg : l ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) :=
      pullback.lift_snd _ _ _
    have : Function.Injective ((l ≫ g).app ⊤) := by
      rw [hg]
      let e := Scheme.arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom <| algebraMap S.R S.K)
      let P : MorphismProperty CommRingCat :=
        RingHom.toMorphismProperty <| fun f ↦ Function.Injective f
      have : (RingHom.toMorphismProperty <| fun f ↦ Function.Injective f).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.injective_respectsIso
      show P _
      rw [← MorphismProperty.arrow_mk_iso_iff (P := P) e]
      exact NoZeroSMulDivisors.algebraMap_injective S.R S.K
    rw [Scheme.comp_app _ _] at this
    exact Function.Injective.of_comp this
  · rw [IsClosedImmersion.iff_of_isAffine] at this
    exact this.right

-- by lemmas above
lemma IsSeparated_eq_valuativeCriterion :
    @IsSeparated = ValuativeCriterion.Uniqueness ⊓ @QuasiSeparated := by
  ext X Y f
  constructor
  · intro hf
    exact ⟨IsSeparated.valuativeCriterion f, inferInstance⟩
  · intro ⟨hu, _⟩
    exact isSeparated_of_valuativeCriterion f hu

end Uniqueness

-- by definition
lemma valuativeCriterion_eq :
    ValuativeCriterion = ValuativeCriterion.Existence ⊓ ValuativeCriterion.Uniqueness := by
  ext X Y f
  constructor
  · intro hf
    refine ⟨fun S ↦ ?_, fun S ↦ ?_⟩
    · obtain ⟨(u : Unique (S.commSq.LiftStruct))⟩ := hf S
      exact CommSq.HasLift.mk' default
    · obtain ⟨(u : Unique (S.commSq.LiftStruct))⟩ := hf S
      infer_instance
  · intro ⟨he, hu⟩ S
    rw [unique_iff_subsingleton_and_nonempty]
    exact ⟨hu S, (he S).1⟩

-- by lemmas above and `isProper_eq`
lemma proper_eq_ValuativeCriterion :
    @IsProper = ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType := by
  rw [isProper_eq, IsSeparated_eq_valuativeCriterion, valuativeCriterion_eq,
    universallyClosed_eq_valuativeCriterion]
  rw [← inf_assoc]
  ext X Y f
  constructor
  · intro ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
    exact ⟨⟨⟨⟨h2, h0⟩, h3⟩, h1⟩, h4⟩
  · intro ⟨⟨⟨⟨h2, h0⟩, h3⟩, h1⟩, h4⟩
    exact ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩

end AlgebraicGeometry
