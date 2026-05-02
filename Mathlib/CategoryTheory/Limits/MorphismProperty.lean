/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# (Co)limits in subcategories of comma categories defined by morphism properties

-/

@[expose] public section

namespace CategoryTheory

open Limits MorphismProperty.Comma

variable {T : Type*} [Category* T] (P : MorphismProperty T)

namespace MorphismProperty.Comma

variable {A B J : Type*} [Category* A] [Category* B] [Category* J] {L : A ⥤ T} {R : B ⥤ T}
variable (D : J ⥤ P.Comma L R ⊤ ⊤)

/-- If `P` is closed under limits of shape `J` in `Comma L R`, then when `D` has
a limit in `Comma L R`, the forgetful functor creates this limit. -/
@[implicit_reducible]
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
@[implicit_reducible]
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
@[implicit_reducible]
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
@[implicit_reducible]
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

section CostructuredArrow

variable {A : Type*} [Category* A] {L : A ⥤ T}

instance CostructuredArrow.closedUnderLimitsOfShape_discrete_empty [L.Faithful] [L.Full] {Y : A}
    [P.ContainsIdentities] [P.RespectsIso] :
    (P.costructuredArrowObj L (X := L.obj Y)).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) where
  limitsOfShape_le := by
    rintro X p
    letI t : IsTerminal X := (ObjectProperty.limitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ CostructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso CostructuredArrow.mkIdTerminal
    simpa [MorphismProperty.costructuredArrowObj_iff,
      P.costructuredArrow_iso_iff e] using P.id_mem (L.obj Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma CostructuredArrow.isClosedUnderColimitsOfShape {J : Type*} [Category* J]
    {P : MorphismProperty T} [P.RespectsIso] [PreservesColimitsOfShape J L] [HasColimitsOfShape J A]
    (c : ∀ (D : J ⥤ T) [HasColimit D], Cocone D)
    (hc : ∀ (D : J ⥤ T) [HasColimit D], IsColimit (c D))
    (H : ∀ (D : J ⥤ T) [HasColimit D] {X : T} (s : D ⟶ (Functor.const J).obj X),
      (∀ j, P (s.app j)) → P ((hc D).desc (Cocone.mk X s))) (X : T) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le Y := by
    intro ⟨d⟩
    let hd : IsColimit ((CategoryTheory.CostructuredArrow.proj L X ⋙ L).mapCocone d.cocone) :=
      isColimitOfPreserves _ d.isColimit
    have heq : Y.hom = hd.desc { pt := X, ι := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j ↦ ?_
      simp only [Functor.const_obj_obj, IsColimit.fac]
      simp
    rw [P.costructuredArrowObj_iff, heq, ← hd.coconePointUniqueUpToIso_hom_desc (hc _),
      P.cancel_left_of_respectsIso]
    exact H _ _ d.prop_diag_obj

lemma CostructuredArrow.closedUnderLimitsOfShape_walkingCospan [HasPullbacks A] [HasPullbacks T]
    [PreservesLimitsOfShape WalkingCospan L] (X : T)
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    [P.HasOfPostcompProperty P] :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨pres, hpres⟩
    have h : IsPullback (L.map (pres.π.app .left).left) (L.map (pres.π.app .right).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inl).left)
          (L.map (pres.diag.map WalkingCospan.Hom.inr).left) :=
      IsPullback.of_isLimit_cone <| isLimitOfPreserves
        (CategoryTheory.CostructuredArrow.toOver L X ⋙ CategoryTheory.Over.forget X) pres.isLimit
    rw [MorphismProperty.costructuredArrowObj_iff]
    rw [show Y.hom = L.map (pres.π.app .left).left ≫ (pres.diag.obj .left).hom by simp]
    apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (hpres _)
    exact P.of_postcomp _ (pres.diag.obj WalkingCospan.one).hom (hpres .one)
      (by simpa using hpres .right)

namespace MorphismProperty.CostructuredArrow

variable (X : T) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
  [P.HasOfPostcompProperty P] [HasPullbacks A] [HasPullbacks T]
  [PreservesLimitsOfShape WalkingCospan L]

noncomputable instance createsLimitsOfShape_walkingCospan :
    CreatesLimitsOfShape WalkingCospan (CostructuredArrow.forget P ⊤ L X) := by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

instance hasPullbacks : HasPullbacks (P.CostructuredArrow ⊤ L X) := by
  apply +allowSynthFailures hasLimitsOfShape_of_closedUnderLimitsOfShape
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

instance : PreservesLimitsOfShape WalkingCospan (CostructuredArrow.toOver P L X) :=
  have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P L X ⋙ Over.forget P ⊤ X) :=
    inferInstanceAs <| PreservesLimitsOfShape WalkingCospan <|
      CostructuredArrow.forget P ⊤ L X ⋙ CategoryTheory.CostructuredArrow.toOver L X
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end MorphismProperty.CostructuredArrow

end CostructuredArrow

section

variable {A : Type*} [Category* A] {L : A ⥤ T}

instance StructuredArrow.closedUnderColimitsOfShape_discrete_empty [L.Faithful] [L.Full] {Y : A}
    [P.ContainsIdentities] [P.RespectsIso] :
    (P.structuredArrowObj L (X := L.obj Y)).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) where
  colimitsOfShape_le := by
    rintro X p
    letI t : IsInitial X := (ObjectProperty.colimitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ StructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso StructuredArrow.mkIdInitial
    simpa [MorphismProperty.structuredArrowObj_iff,
      P.structuredArrow_iso_iff e] using P.id_mem (L.obj Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma StructuredArrow.isClosedUnderLimitsOfShape {J : Type*} [Category* J]
    {P : MorphismProperty T} [P.RespectsIso] [PreservesLimitsOfShape J L] [HasLimitsOfShape J A]
    (c : ∀ (D : J ⥤ T) [HasLimit D], Cone D)
    (hc : ∀ (D : J ⥤ T) [HasLimit D], IsLimit (c D))
    (H : ∀ (D : J ⥤ T) [HasLimit D] {X : T} (s : (Functor.const J).obj X ⟶ D),
      (∀ j, P (s.app j)) → P ((hc D).lift (Cone.mk X s))) (X : T) :
    (P.structuredArrowObj L (X := X)).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le Y := by
    intro ⟨d⟩
    let hd : IsLimit ((CategoryTheory.StructuredArrow.proj X L ⋙ L).mapCone d.cone) :=
      isLimitOfPreserves _ d.isLimit
    have heq : Y.hom = hd.lift { pt := X, π := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j ↦ ?_
      simp only [IsLimit.fac]
      simp
    rw [P.structuredArrowObj_iff, heq, ← (hc _).lift_comp_conePointUniqueUpToIso_hom hd,
      P.cancel_right_of_respectsIso]
    exact H _ _ d.prop_diag_obj

end

section

variable {X : T}

instance Over.closedUnderLimitsOfShape_discrete_empty [P.ContainsIdentities] [P.RespectsIso] :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) :=
  CostructuredArrow.closedUnderLimitsOfShape_discrete_empty P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `P` be stable under composition and base change. If `P` satisfies cancellation on the right,
the subcategory of `Over X` defined by `P` is closed under pullbacks.

Without the cancellation property, this does not in general. Consider for example
`P = Function.Surjective` on `Type`. -/
instance Over.closedUnderLimitsOfShape_pullback [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape WalkingCospan :=
  CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

end

section

variable {X : T}

instance Under.closedUnderColimitsOfShape_discrete_empty [P.ContainsIdentities] [P.RespectsIso] :
    (P.underObj (X := X)).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) :=
  StructuredArrow.closedUnderColimitsOfShape_discrete_empty (L := 𝟭 _) P

/-- Let `P` be stable under composition and cobase change. If `P` satisfies cancellation on the
left, the subcategory of `Under X` defined by `P` is closed under pushouts. -/
instance Under.closedUnderColimitsOfShape_pushout [HasPushouts T]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] :
    (P.underObj (X := X)).IsClosedUnderColimitsOfShape WalkingSpan := by
  rw [ObjectProperty.isClosedUnderColimitsOfShape_iff_op, ←
    ObjectProperty.isClosedUnderLimitsOfShape_inverseImage_iff _ _ (Over.opEquivOpUnder _),
    MorphismProperty.inverseImage_op_underObj,
    ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivalence _ walkingSpanOpEquiv]
  infer_instance

end

namespace MorphismProperty.Over

variable (X : T)

noncomputable instance [P.ContainsIdentities] [P.RespectsIso] :
    CreatesLimitsOfShape (Discrete PEmpty.{1}) (Over.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape _ (Over X))
  · apply Over.closedUnderLimitsOfShape_discrete_empty _

set_option backward.defeqAttrib.useBackward true in
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
  CostructuredArrow.createsLimitsOfShape_walkingCospan _ _

/-- If `P` is stable under composition, base change and satisfies post-cancellation,
`P.Over ⊤ X` has pullbacks -/
instance (priority := 900) hasPullbacks [HasPullbacks T] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] : HasPullbacks (P.Over ⊤ X) :=
  CostructuredArrow.hasPullbacks _ _

variable [HasPullbacks T] [P.IsStableUnderComposition] [P.ContainsIdentities]
  [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]

noncomputable instance : CreatesFiniteLimits (Over.forget P ⊤ X) :=
  createsFiniteLimitsOfCreatesTerminalAndPullbacks _

instance [HasFiniteWidePullbacks T] : HasFiniteLimits (P.Over ⊤ X) :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Over.forget P ⊤ X)

instance : PreservesFiniteLimits (Over.forget P ⊤ X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (Over.forget P ⊤ X)

instance {X Y : T} (f : X ⟶ Y) : PreservesFiniteLimits (pullback P ⊤ f) where
  preservesFiniteLimits J _ _ := by
    have : PreservesLimitsOfShape J
        (MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _) :=
      inferInstanceAs <| PreservesLimitsOfShape J <|
        Over.forget _ _ _ ⋙ CategoryTheory.Over.pullback f
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (MorphismProperty.Over.pullback P ⊤ f) (MorphismProperty.Over.forget _ _ _)

end MorphismProperty.Over

namespace MorphismProperty.Under

variable (X : T)

noncomputable instance [P.ContainsIdentities] [P.RespectsIso] :
    CreatesColimitsOfShape (Discrete PEmpty.{1}) (Under.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape _ (Under X))
  · apply Under.closedUnderColimitsOfShape_discrete_empty _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {X} in
instance [P.ContainsIdentities] (Y : P.Under ⊤ X) :
    Unique (Under.mk ⊤ (𝟙 X) (P.id_mem X) ⟶ Y) where
  default := Under.homMk Y.hom (by simp)
  uniq a := by ext; simp [← Under.w a]

/-- `X ⟶ X` is the initial object of `P.Under ⊤ X`. -/
def mkIdInitial [P.ContainsIdentities] :
    IsInitial (Under.mk ⊤ (𝟙 X) (P.id_mem X)) :=
  .ofUnique _

instance [P.ContainsIdentities] : HasInitial (P.Under ⊤ X) :=
  (Under.mkIdInitial P X).hasInitial

/-- If `P` is stable under composition, cobase change and satisfies pre-cancellation,
`Under.forget P ⊤ X` creates pushouts. -/
noncomputable instance [HasPushouts T]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] :
    CreatesColimitsOfShape WalkingSpan (Under.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape WalkingSpan (Under X))
  · apply Under.closedUnderColimitsOfShape_pushout

/-- If `P` is stable under composition, cobase change and satisfies pre-cancellation,
`P.Under ⊤ X` has pushouts. -/
instance (priority := 900) [HasPushouts T] [P.IsStableUnderComposition]
    [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] : HasPushouts (P.Under ⊤ X) := by
  apply +allowSynthFailures hasColimitsOfShape_of_closedUnderColimitsOfShape
  · exact inferInstanceAs (HasColimitsOfShape WalkingSpan (Under X))
  · apply Under.closedUnderColimitsOfShape_pushout

variable [HasPushouts T] [P.IsStableUnderComposition] [P.ContainsIdentities]
  [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P]

noncomputable instance : CreatesFiniteColimits (Under.forget P ⊤ X) :=
  createsFiniteColimitsOfCreatesInitialAndPushouts _

instance [HasFiniteWidePushouts T] : HasFiniteColimits (P.Under ⊤ X) :=
  hasFiniteColimits_of_hasColimits_of_createsFiniteColimits (Under.forget P ⊤ X)

instance : PreservesFiniteColimits (Under.forget P ⊤ X) :=
  preservesFiniteColimits_of_preservesInitial_and_pushouts (Under.forget P ⊤ X)

end MorphismProperty.Under

end CategoryTheory
