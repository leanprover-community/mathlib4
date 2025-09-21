/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Constructing binary product from pullbacks and terminal object.

The product is the pullback over the terminal objects. In particular, if a category
has pullbacks and a terminal object, then it has binary products.

We also provide the dual.
-/


universe v v' u u'

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

/-- If a span is the pullback span over the terminal object, then it is a binary product. -/
def isBinaryProductOfIsTerminalIsPullback (F : Discrete WalkingPair ⥤ C) (c : Cone F) {X : C}
    (hX : IsTerminal X) (f : F.obj ⟨WalkingPair.left⟩ ⟶ X) (g : F.obj ⟨WalkingPair.right⟩ ⟶ X)
    (hc : IsLimit
      (PullbackCone.mk (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩ :) <|
        hX.hom_ext (_ ≫ f) (_ ≫ g))) : IsLimit c where
  lift s :=
    hc.lift
      (PullbackCone.mk (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingCospan.left) (hc.fac _ WalkingCospan.right)
  uniq s m J := by
    let c' :=
      PullbackCone.mk (m ≫ c.π.app ⟨WalkingPair.left⟩) (m ≫ c.π.app ⟨WalkingPair.right⟩ :)
        (hX.hom_ext (_ ≫ f) (_ ≫ g))
    dsimp; rw [← J, ← J]
    apply hc.hom_ext
    rintro (_ | (_ | _)) <;> simp only [PullbackCone.mk_π_app]
    exacts [(Category.assoc _ _ _).symm.trans (hc.fac_assoc c' WalkingCospan.left f).symm,
      (hc.fac c' WalkingCospan.left).symm, (hc.fac c' WalkingCospan.right).symm]

/-- The pullback over the terminal object is the product -/
def isProductOfIsTerminalIsPullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z)
    (H₂ : IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsLimit (BinaryFan.mk h k) := by
  apply isBinaryProductOfIsTerminalIsPullback _ _ H₁
  exact H₂

/-- The product is the pullback over the terminal object. -/
def isPullbackOfIsTerminalIsProduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z) (H₂ : IsLimit (BinaryFan.mk h k)) :
    IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply PullbackCone.isLimitAux'
  intro s
  use H₂.lift (BinaryFan.mk s.fst s.snd)
  use H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩
  use H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.right⟩
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩).symm
  · exact h₂.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.right⟩).symm

/-- Any category with pullbacks and a terminal object has a limit cone for each walking pair. -/
noncomputable def limitConeOfTerminalAndPullbacks [HasTerminal C] [HasPullbacks C]
    (F : Discrete WalkingPair ⥤ C) : LimitCone F where
  cone :=
    { pt :=
        pullback (terminal.from (F.obj ⟨WalkingPair.left⟩))
          (terminal.from (F.obj ⟨WalkingPair.right⟩))
      π :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pullback.fst _ _) (pullback.snd _ _) }
  isLimit :=
    isBinaryProductOfIsTerminalIsPullback F _ terminalIsTerminal _ _ (pullbackIsPullback _ _)

variable (C) in
-- This is not an instance, as it is not always how one wants to construct binary products!
/-- Any category with pullbacks and terminal object has binary products. -/
theorem hasBinaryProducts_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasBinaryProducts C :=
  { has_limit := fun F => HasLimit.mk (limitConeOfTerminalAndPullbacks F) }

/-- A functor that preserves terminal objects and pullbacks preserves binary products. -/
lemma preservesBinaryProducts_of_preservesTerminal_and_pullbacks [HasTerminal C]
    [HasPullbacks C] [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]
    [PreservesLimitsOfShape WalkingCospan F] : PreservesLimitsOfShape (Discrete WalkingPair) F :=
  ⟨fun {K} =>
    preservesLimit_of_preserves_limit_cone (limitConeOfTerminalAndPullbacks K).2
      (by
        apply
          isBinaryProductOfIsTerminalIsPullback _ _ (isLimitOfHasTerminalOfPreservesLimit F)
        apply isLimitOfHasPullbackOfPreservesLimit)⟩

/-- In a category with a terminal object and pullbacks,
a product of objects `X` and `Y` is isomorphic to a pullback. -/
noncomputable def prodIsoPullback [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y) :=
  limit.isoLimitCone (limitConeOfTerminalAndPullbacks _)

@[reassoc (attr := simp)]
lemma prodIsoPullback_hom_fst [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullback.fst _ _ = prod.fst :=
  limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]
lemma prodIsoPullback_hom_snd [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullback.snd _ _ = prod.snd :=
  limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

@[reassoc (attr := simp)]
lemma prodIsoPullback_inv_fst [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.fst = pullback.fst _ _ :=
  limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]
lemma prodIsoPullback_inv_snd [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.snd = pullback.snd _ _ :=
  limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

/-- If a cospan is the pushout cospan under the initial object, then it is a binary coproduct. -/
def isBinaryCoproductOfIsInitialIsPushout (F : Discrete WalkingPair ⥤ C) (c : Cocone F) {X : C}
    (hX : IsInitial X) (f : X ⟶ F.obj ⟨WalkingPair.left⟩) (g : X ⟶ F.obj ⟨WalkingPair.right⟩)
    (hc :
      IsColimit
        (PushoutCocone.mk (c.ι.app ⟨WalkingPair.left⟩) (c.ι.app ⟨WalkingPair.right⟩ :) <|
          hX.hom_ext (f ≫ _) (g ≫ _))) :
    IsColimit c where
  desc s :=
    hc.desc
      (PushoutCocone.mk (s.ι.app ⟨WalkingPair.left⟩) (s.ι.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingSpan.left) (hc.fac _ WalkingSpan.right)
  uniq s m J := by
    let c' :=
      PushoutCocone.mk (c.ι.app ⟨WalkingPair.left⟩ ≫ m) (c.ι.app ⟨WalkingPair.right⟩ ≫ m)
        (hX.hom_ext (f ≫ _) (g ≫ _))
    dsimp; rw [← J, ← J]
    apply hc.hom_ext
    rintro (_ | (_ | _)) <;>
      simp only [PushoutCocone.mk_ι_app, Category.assoc]
    on_goal 1 => congr 1
    exacts [(hc.fac c' WalkingSpan.left).symm, (hc.fac c' WalkingSpan.left).symm,
      (hc.fac c' WalkingSpan.right).symm]

/-- The pushout under the initial object is the coproduct -/
def isCoproductOfIsInitialIsPushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsInitial W)
    (H₂ : IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsColimit (BinaryCofan.mk f g) := by
  apply isBinaryCoproductOfIsInitialIsPushout _ _ H₁
  exact H₂

/-- The coproduct is the pushout under the initial object. -/
def isPushoutOfIsInitialIsCoproduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsInitial W) (H₂ : IsColimit (BinaryCofan.mk f g)) :
    IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply PushoutCocone.isColimitAux'
  intro s
  use H₂.desc (BinaryCofan.mk s.inl s.inr)
  use H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.left⟩
  use H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.right⟩
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.left⟩).symm
  · exact h₂.trans (H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.right⟩).symm

/-- Any category with pushouts and an initial object has a colimit cocone for each walking pair. -/
noncomputable def colimitCoconeOfInitialAndPushouts [HasInitial C] [HasPushouts C]
    (F : Discrete WalkingPair ⥤ C) : ColimitCocone F where
  cocone :=
    { pt := pushout (initial.to (F.obj ⟨WalkingPair.left⟩)) (initial.to (F.obj ⟨WalkingPair.right⟩))
      ι :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pushout.inl _ _) (pushout.inr _ _) }
  isColimit := isBinaryCoproductOfIsInitialIsPushout F _ initialIsInitial _ _ (pushoutIsPushout _ _)

variable (C) in
-- This is not an instance, as it is not always how one wants to construct binary coproducts!
/-- Any category with pushouts and initial object has binary coproducts. -/
theorem hasBinaryCoproducts_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => HasColimit.mk (colimitCoconeOfInitialAndPushouts F) }

/-- A functor that preserves initial objects and pushouts preserves binary coproducts. -/
lemma preservesBinaryCoproducts_of_preservesInitial_and_pushouts [HasInitial C]
    [HasPushouts C] [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]
    [PreservesColimitsOfShape WalkingSpan F] : PreservesColimitsOfShape (Discrete WalkingPair) F :=
  ⟨fun {K} =>
    preservesColimit_of_preserves_colimit_cocone (colimitCoconeOfInitialAndPushouts K).2 (by
      apply
        isBinaryCoproductOfIsInitialIsPushout _ _
          (isColimitOfHasInitialOfPreservesColimit F)
      apply isColimitOfHasPushoutOfPreservesColimit)⟩

/-- In a category with an initial object and pushouts,
a coproduct of objects `X` and `Y` is isomorphic to a pushout. -/
noncomputable def coprodIsoPushout [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : X ⨿ Y ≅ pushout (initial.to X) (initial.to Y) :=
  colimit.isoColimitCocone (colimitCoconeOfInitialAndPushouts _)

@[reassoc (attr := simp)]
lemma inl_coprodIsoPushout_hom [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : coprod.inl ≫ (coprodIsoPushout X Y).hom = pushout.inl _ _ :=
  colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]
lemma inr_coprodIsoPushout_hom [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : coprod.inr ≫ (coprodIsoPushout X Y).hom = pushout.inr _ _ :=
  colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]
lemma inl_coprodIsoPushout_inv [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : pushout.inl _ _ ≫ (coprodIsoPushout X Y).inv = coprod.inl :=
  colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.left⟩

@[reassoc (attr := simp)]
lemma inr_coprodIsoPushout_inv [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : pushout.inr _ _ ≫ (coprodIsoPushout X Y).inv = coprod.inr :=
  colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.right⟩
