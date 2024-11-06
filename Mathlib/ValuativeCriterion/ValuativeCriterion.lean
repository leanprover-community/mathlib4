-- `Mathlib/AlgebraicGeometry/Morphisms/ValuativeCriterion
import Mathlib.ValuativeCriterion.Immersion
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.ValuativeCriterion.ValuationRing
import Mathlib.ValuativeCriterion.Lemmas
import Mathlib.ValuativeCriterion.UniversallyClosed

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

open LocalRing in
/--
Uses `exists_factor_valuationRing` and `Scheme.fromSpecResidueField`.

https://stacks.math.columbia.edu/tag/01KE
-/
lemma specializingMap (H : ValuativeCriterion.Existence f) :
    SpecializingMap f.1.base := by
  intro x' y h
  let stalk_y_to_residue_x' : Y.presheaf.stalk y ⟶ X.residueField x' :=
    Y.presheaf.stalkSpecializes h ≫ f.stalkMap x' ≫ X.residue x'
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing stalk_y_to_residue_x'
  let stalk_y_to_A : Y.presheaf.stalk y ⟶ .of A :=
    CommRingCat.ofHom (stalk_y_to_residue_x'.codRestrict _ hA)
  have w : X.fromSpecResidueField x' ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A (X.residueField x'))) ≫
        Spec.map stalk_y_to_A ≫ Y.fromSpecStalk y := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.Spec_map_stalkMap_fromSpecStalk,
      ← Scheme.Spec_map_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨l, hl₁, hl₂⟩ := (H { R := A, K := X.residueField x', commSq := ⟨w⟩ }).exists_lift
  dsimp only at hl₁ hl₂
  refine ⟨l.base (closedPoint A), ?_, ?_⟩
  · simp_rw [← Scheme.fromSpecResidueField_apply x' (closedPoint (X.residueField x')), ← hl₁]
    exact (specializes_closedPoint _).map l.base.2
  · rw [← Scheme.comp_base_apply, hl₂]
    simp only [Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply]
    have : (Spec.map stalk_y_to_A).base (closedPoint A) = closedPoint (Y.presheaf.stalk y) :=
      comap_closedPoint (S := A) (stalk_y_to_residue_x'.codRestrict A.toSubring hA)
    rw [this, Y.fromSpecStalk_closedPoint]

open LocalRing in
/--
Uses `bijective_rangeRestrict_comp_of_valuationRing` and `stalkClosedPointTo`

https://stacks.math.columbia.edu/tag/01KE first half
-/
lemma of_specializingMap (H : (topologically @SpecializingMap).universally f) :
    ValuativeCriterion.Existence f := by
  rintro ⟨R, K, i₁, i₂, ⟨w⟩⟩
  haveI : IsDomain (CommRingCat.of R) := ‹_›
  haveI : ValuationRing (CommRingCat.of R) := ‹_›
  letI : Field (CommRingCat.of K) := ‹_›
  replace H := H (pullback.snd i₂ f) i₂ (pullback.fst i₂ f) (.of_hasPullback i₂ f)
  let lft := pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R K))) i₁ w.symm
  obtain ⟨x, h₁, h₂⟩ := @H (lft.base (closedPoint _)) _ (specializes_closedPoint (R := R) _)
  let e : CommRingCat.of R ≅ (Spec (.of R)).presheaf.stalk ((pullback.fst i₂ f).base x) :=
    (stalkClosedPointIso (.of R)).symm ≪≫
      (Spec (.of R)).presheaf.stalkCongr (.of_eq h₂.symm)
  let α := e.hom ≫ (pullback.fst i₂ f).stalkMap x
  have : IsLocalHom α := inferInstance
  let β := (pullback i₂ f).presheaf.stalkSpecializes h₁ ≫ Scheme.stalkClosedPointTo lft
  have hαβ : α ≫ β = CommRingCat.ofHom (algebraMap R K) := by
    simp only [CommRingCat.coe_of, Iso.trans_hom, Iso.symm_hom, TopCat.Presheaf.stalkCongr_hom,
      Category.assoc, α, e, β, stalkClosedPointIso_inv, StructureSheaf.toStalk]
    show (Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).presheaf.germ _ _ _ ≫ _ = _
    simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.stalkMap_germ_assoc,
      TopologicalSpace.Opens.map_top]
    erw [Scheme.germ_stalkClosedPointTo lft ⊤ trivial,
      ← Scheme.comp_app_assoc lft (pullback.fst i₂ f)]
    rw [pullback.lift_fst]
    simp
  have hbij := (bijective_rangeRestrict_comp_of_valuationRing (R := R) (K := K) α β hαβ)
  let φ : (pullback i₂ f).presheaf.stalk x ⟶ CommRingCat.of R :=
    (RingEquiv.ofBijective _ hbij).symm.toRingHom.comp β.rangeRestrict
  have hαφ : α ≫ φ = 𝟙 _ := by ext x; exact (RingEquiv.ofBijective _ hbij).symm_apply_apply x
  have hαφ' : (pullback.fst i₂ f).stalkMap x ≫ φ = e.inv := by
    rw [← cancel_epi e.hom, ← Category.assoc, hαφ, e.hom_inv_id]
  have hφβ : φ ≫ CommRingCat.ofHom (algebraMap R K) = β :=
    hαβ ▸ RingHom.ext fun x ↦ congr_arg Subtype.val
      ((RingEquiv.ofBijective _ hbij).apply_symm_apply (β.rangeRestrict x))
  refine ⟨⟨⟨Spec.map ((pullback.snd i₂ f).stalkMap x ≫ φ) ≫ X.fromSpecStalk _, ?_, ?_⟩⟩⟩
  · simp only [← Spec.map_comp_assoc, Category.assoc, hφβ]
    simp [β, Scheme.Spec_map_stalkSpecializes_fromSpecStalk_assoc, -CommRingCat.coe_of,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc, lft]
  · simp only [Spec.map_comp, Category.assoc, Scheme.Spec_map_stalkMap_fromSpecStalk,
      ← pullback.condition]
    rw [← Scheme.Spec_map_stalkMap_fromSpecStalk_assoc, ← Spec.map_comp_assoc, hαφ']
    simp only [Iso.trans_inv, TopCat.Presheaf.stalkCongr_inv, Iso.symm_inv, Spec.map_comp,
      Category.assoc, Scheme.Spec_map_stalkSpecializes_fromSpecStalk_assoc, e]
    rw [← Spec_stalkClosedPointIso, ← Spec.map_comp_assoc,
      Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- by def -/
lemma stableUnderBaseChange :
    ValuativeCriterion.Existence.StableUnderBaseChange := by
  intros Y' X X' Y  Y'_to_Y f X'_to_X f' hP hf commSq

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
    · simpa [l]
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
      apply IsClosedImmersion.of_isPreimmersion
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
  have : IsClosedImmersion g := IsClosedImmersion.stableUnderBaseChange.snd _ _ inferInstance
  have hZ : IsAffine Z := by
    rw [@HasAffineProperty.iff_of_isAffine @IsClosedImmersion] at this
    exact this.left
  suffices IsIso g by
    rw [← cancel_epi g]
    conv_lhs => rw [← pullback.lift_fst l₁ l₂ h, ← pullback.condition_assoc]
    conv_rhs => rw [← pullback.lift_snd l₁ l₂ h, ← pullback.condition_assoc]
    simp
  suffices h : Function.Bijective (g.app ⊤) by
    refine (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr ?_
    exact ⟨hZ, (ConcreteCategory.isIso_iff_bijective _).mpr h⟩
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
      let e := arrowIsoΓSpecOfIsAffine (CommRingCat.ofHom <| algebraMap S.R S.K)
      let P : MorphismProperty CommRingCat :=
        RingHom.toMorphismProperty <| fun f ↦ Function.Injective f
      have : (RingHom.toMorphismProperty <| fun f ↦ Function.Injective f).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.injective_respectsIso
      show P _
      rw [← MorphismProperty.arrow_mk_iso_iff (P := P) e]
      exact NoZeroSMulDivisors.algebraMap_injective S.R S.K
    rw [Scheme.comp_app _ _] at this
    exact Function.Injective.of_comp this
  · rw [@HasAffineProperty.iff_of_isAffine @IsClosedImmersion] at this
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
