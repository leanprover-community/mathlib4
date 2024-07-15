-- `Mathlib/AlgebraicGeometry/Morphisms/ValuativeCriterion
import Mathlib.ValuativeCriterion.Proper
import Mathlib.ValuativeCriterion.Immersion
import Mathlib.RingTheory.Valuation.ValuationRing

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
    SpecializingMap f.1.base := sorry

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
