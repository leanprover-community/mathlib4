/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape

/-!
# (Co)limits in subcategories of comma categories defined by morphism properties

-/

namespace CategoryTheory

open Limits MorphismProperty.Comma

variable {T : Type*} [Category T] (P : MorphismProperty T)

namespace MorphismProperty.Comma

variable {A B J : Type*} [Category A] [Category B] [Category J] {L : A ⥤ T} {R : B ⥤ T}
variable (D : J ⥤ P.Comma L R ⊤ ⊤)

/-- If `P` is closed under limits of shape `J` in `Comma L R`, then when `D` has
a limit in `Comma L R`, the forgetful functor creates this limit. -/
noncomputable def forgetCreatesLimitOfClosed
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J]
    [HasLimit (D ⋙ forget L R P ⊤ ⊤)] :
    CreatesLimit D (forget L R P ⊤ ⊤) :=
  createsLimitOfFullyFaithfulOfIso
    (⟨limit (D ⋙ forget L R P ⊤ ⊤),
      ObjectProperty.prop_limit (P.commaObj L R) _
        fun j ↦ (D.obj j).prop⟩) (Iso.refl _)

/-- If `Comma L R` has limits of shape `J` and `Comma L R` is closed under limits of shape
`J`, then `forget L R P ⊤ ⊤` creates limits of shape `J`. -/
noncomputable def forgetCreatesLimitsOfShapeOfClosed [HasLimitsOfShape J (Comma L R)]
    [ObjectProperty.IsClosedUnderLimitsOfShape (P.commaObj L R) J] :
    CreatesLimitsOfShape J (forget L R P ⊤ ⊤) where
  CreatesLimit := forgetCreatesLimitOfClosed _ _

lemma hasLimit_of_closedUnderLimitsOfShape
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J]
    [HasLimit (D ⋙ forget L R P ⊤ ⊤)] :
    HasLimit D :=
  haveI : CreatesLimit D (forget L R P ⊤ ⊤) := forgetCreatesLimitOfClosed _ D
  hasLimit_of_created D (forget L R P ⊤ ⊤)

instance hasLimitsOfShape_of_closedUnderLimitsOfShape [HasLimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J] :
    HasLimitsOfShape J (P.Comma L R ⊤ ⊤) where
  has_limit _ := hasLimit_of_closedUnderLimitsOfShape _ _

/-- If `P` is closed under colimits of shape `J` in `Comma L R`, then when `D` has
a colimit in `Comma L R`, the forgetful functor creates this colimit. -/
noncomputable def forgetCreatesColimitOfClosed
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J]
    [HasColimit (D ⋙ forget L R P ⊤ ⊤)] :
    CreatesColimit D (forget L R P ⊤ ⊤) :=
  createsColimitOfFullyFaithfulOfIso
    (⟨colimit (D ⋙ forget L R P ⊤ ⊤),
      (P.commaObj L R).prop_colimit _ (fun j ↦ (D.obj j).prop)⟩) (Iso.refl _)

variable (J) in
/-- If `Comma L R` has colimits of shape `J` and `Comma L R` is closed under colimits of shape
`J`, then `forget L R P ⊤ ⊤` creates colimits of shape `J`. -/
noncomputable def forgetCreatesColimitsOfShapeOfClosed [HasColimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J] :
    CreatesColimitsOfShape J (forget L R P ⊤ ⊤) where
  CreatesColimit := forgetCreatesColimitOfClosed _ _

lemma hasColimit_of_closedUnderColimitsOfShape
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J]
    [HasColimit (D ⋙ forget L R P ⊤ ⊤)] :
    HasColimit D :=
  haveI : CreatesColimit D (forget L R P ⊤ ⊤) := forgetCreatesColimitOfClosed _ D
  hasColimit_of_created D (forget L R P ⊤ ⊤)

instance hasColimitsOfShape_of_closedUnderColimitsOfShape [HasColimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J] :
    HasColimitsOfShape J (P.Comma L R ⊤ ⊤) where
  has_colimit _ := hasColimit_of_closedUnderColimitsOfShape _ _

end MorphismProperty.Comma

section

variable {A : Type*} [Category A] {L : A ⥤ T}

instance CostructuredArrow.closedUnderLimitsOfShape_discrete_empty [L.Faithful] [L.Full] {Y : A}
    [P.ContainsIdentities] [P.RespectsIso] :
    (P.costructuredArrowObj L (X := L.obj Y)).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    let e : X ≅ CostructuredArrow.mk (𝟙 (L.obj Y)) :=
      p.isLimit.conePointUniqueUpToIso ((IsLimit.postcomposeInvEquiv
        (Functor.emptyExt _ _) _).2 CostructuredArrow.mkIdTerminal)
    rw [MorphismProperty.costructuredArrowObj_iff,
      P.costructuredArrow_iso_iff e]
    simpa using P.id_mem (L.obj Y)

end

section

variable {X : T}

instance Over.closedUnderLimitsOfShape_discrete_empty [P.ContainsIdentities] [P.RespectsIso] :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) :=
  CostructuredArrow.closedUnderLimitsOfShape_discrete_empty P

instance [P.RespectsIso] [P.ContainsIdentities] :
    (MorphismProperty.commaObj (𝟭 T) (Functor.fromPUnit.{0} X) P).IsClosedUnderLimitsOfShape
      (Discrete PEmpty.{1}) :=
  Over.closedUnderLimitsOfShape_discrete_empty _

/-- Let `P` be stable under composition and base change. If `P` satisfies cancellation on the right,
the subcategory of `Over X` defined by `P` is closed under pullbacks.

Without the cancellation property, this does not in general. Consider for example
`P = Function.Surjective` on `Type`. -/
instance Over.closedUnderLimitsOfShape_pullback [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    have ip := p.π.app .left
    have h := IsPullback.of_isLimit_cone <|
        Limits.isLimitOfPreserves (CategoryTheory.Over.forget X) p.isLimit
    dsimp at h
    rw [MorphismProperty.overObj_iff,
      show Y.hom = (p.π.app .left).left ≫ (p.diag.obj .left).hom by simp]
    apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (p.prop_diag_obj _)
    exact P.of_postcomp _ (p.diag.obj WalkingCospan.one).hom (p.prop_diag_obj .one)
      (by simpa using p.prop_diag_obj .right)

instance [HasPullbacks T] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (MorphismProperty.commaObj (𝟭 T) (Functor.fromPUnit.{0} X) P).IsClosedUnderLimitsOfShape
      WalkingCospan :=
  Over.closedUnderLimitsOfShape_pullback _

end

namespace MorphismProperty.Over

variable (X : T)

noncomputable instance [P.ContainsIdentities] [P.RespectsIso] :
    CreatesLimitsOfShape (Discrete PEmpty.{1}) (Over.forget P ⊤ X) :=
  haveI : HasLimitsOfShape (Discrete PEmpty.{1}) (Comma (𝟭 T) (Functor.fromPUnit X)) := by
    change HasLimitsOfShape _ (Over X)
    infer_instance
  forgetCreatesLimitsOfShapeOfClosed _

variable {X} in
instance [P.ContainsIdentities] (Y : P.Over ⊤ X) :
    Unique (Y ⟶ Over.mk ⊤ (𝟙 X) (P.id_mem X)) where
  default := Over.homMk Y.hom
  uniq a := by
    ext
    · simp only [mk_left, homMk_hom, Over.homMk_left]
      rw [← Over.w a]
      simp only [mk_left, Functor.const_obj_obj, mk_hom, Category.comp_id]

/-- `X ⟶ X` is the terminal object of `P.Over ⊤ X`. -/
def mkIdTerminal [P.ContainsIdentities] :
    IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) :=
  IsTerminal.ofUnique _

instance [P.ContainsIdentities] : HasTerminal (P.Over ⊤ X) :=
  let h : IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) := Over.mkIdTerminal P X
  h.hasTerminal

/-- If `P` is stable under composition, base change and satisfies post-cancellation,
`Over.forget P ⊤ X` creates pullbacks. -/
noncomputable instance createsLimitsOfShape_walkingCospan [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    CreatesLimitsOfShape WalkingCospan (Over.forget P ⊤ X) :=
  haveI : HasLimitsOfShape WalkingCospan (Comma (𝟭 T) (Functor.fromPUnit X)) :=
    inferInstanceAs <| HasLimitsOfShape WalkingCospan (Over X)
  forgetCreatesLimitsOfShapeOfClosed P

/-- If `P` is stable under composition, base change and satisfies post-cancellation,
`P.Over ⊤ X` has pullbacks -/
instance (priority := 900) hasPullbacks [HasPullbacks T] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] : HasPullbacks (P.Over ⊤ X) :=
  haveI : HasLimitsOfShape WalkingCospan (Comma (𝟭 T) (Functor.fromPUnit X)) :=
    inferInstanceAs <| HasLimitsOfShape WalkingCospan (Over X)
  hasLimitsOfShape_of_closedUnderLimitsOfShape P

end MorphismProperty.Over

end CategoryTheory
