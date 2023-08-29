/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

#align_import category_theory.limits.constructions.binary_products from "leanprover-community/mathlib"@"3424a5932a77dcec2c177ce7d805acace6149299"

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
      (PullbackCone.mk (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩ : _) <|
        hX.hom_ext (_ ≫ f) (_ ≫ g))) : IsLimit c where
  lift s :=
    hc.lift
      (PullbackCone.mk (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac s j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingCospan.left) (hc.fac _ WalkingCospan.right)
  uniq s m J := by
    let c' :=
      PullbackCone.mk (m ≫ c.π.app ⟨WalkingPair.left⟩) (m ≫ c.π.app ⟨WalkingPair.right⟩ : _)
        (hX.hom_ext (_ ≫ f) (_ ≫ g))
    dsimp; rw [← J, ← J]
    -- ⊢ m = IsLimit.lift hc (PullbackCone.mk (NatTrans.app s.π { as := WalkingPair.l …
           -- ⊢ m = IsLimit.lift hc (PullbackCone.mk (m ≫ NatTrans.app c.π { as := WalkingPa …
    apply hc.hom_ext
    -- ⊢ ∀ (j : WalkingCospan), m ≫ NatTrans.app (PullbackCone.mk (NatTrans.app c.π { …
    rintro (_ | (_ | _)) <;> simp only [PullbackCone.mk_π_app_one, PullbackCone.mk_π_app]
                             -- ⊢ m ≫ NatTrans.app c.π { as := WalkingPair.left } ≫ f = IsLimit.lift hc (Pullb …
                             -- ⊢ m ≫ NatTrans.app c.π { as := WalkingPair.left } = IsLimit.lift hc (PullbackC …
                             -- ⊢ m ≫ NatTrans.app c.π { as := WalkingPair.right } = IsLimit.lift hc (Pullback …
    exacts [(Category.assoc _ _ _).symm.trans (hc.fac_assoc c' WalkingCospan.left f).symm,
      (hc.fac c' WalkingCospan.left).symm, (hc.fac c' WalkingCospan.right).symm]
#align is_binary_product_of_is_terminal_is_pullback isBinaryProductOfIsTerminalIsPullback

/-- The pullback over the terminal object is the product -/
def isProductOfIsTerminalIsPullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z)
    (H₂ : IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsLimit (BinaryFan.mk h k) := by
  apply isBinaryProductOfIsTerminalIsPullback _ _ H₁
  exact H₂
  -- 🎉 no goals
#align is_product_of_is_terminal_is_pullback isProductOfIsTerminalIsPullback

/-- The product is the pullback over the terminal object. -/
def isPullbackOfIsTerminalIsProduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z) (H₂ : IsLimit (BinaryFan.mk h k)) :
    IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply PullbackCone.isLimitAux'
  -- ⊢ (s : PullbackCone f g) → { l // l ≫ PullbackCone.fst (PullbackCone.mk h k (_ …
  intro s
  -- ⊢ { l // l ≫ PullbackCone.fst (PullbackCone.mk h k (_ : h ≫ f = k ≫ g)) = Pull …
  use H₂.lift (BinaryFan.mk s.fst s.snd)
  -- ⊢ IsLimit.lift H₂ (BinaryFan.mk (PullbackCone.fst s) (PullbackCone.snd s)) ≫ P …
  use H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩
  -- ⊢ IsLimit.lift H₂ (BinaryFan.mk (PullbackCone.fst s) (PullbackCone.snd s)) ≫ P …
  use H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.right⟩
  -- ⊢ ∀ {m : s.pt ⟶ (PullbackCone.mk h k (_ : h ≫ f = k ≫ g)).pt}, m ≫ PullbackCon …
  intro m h₁ h₂
  -- ⊢ m = IsLimit.lift H₂ (BinaryFan.mk (PullbackCone.fst s) (PullbackCone.snd s))
  apply H₂.hom_ext
  -- ⊢ ∀ (j : Discrete WalkingPair), m ≫ NatTrans.app (BinaryFan.mk h k).π j = IsLi …
  rintro ⟨⟨⟩⟩
  -- ⊢ m ≫ NatTrans.app (BinaryFan.mk h k).π { as := WalkingPair.left } = IsLimit.l …
  · exact h₁.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩).symm
    -- 🎉 no goals
  · exact h₂.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.right⟩).symm
    -- 🎉 no goals
#align is_pullback_of_is_terminal_is_product isPullbackOfIsTerminalIsProduct

/-- Any category with pullbacks and a terminal object has a limit cone for each walking pair. -/
noncomputable def limitConeOfTerminalAndPullbacks [HasTerminal C] [HasPullbacks C]
    (F : Discrete WalkingPair ⥤ C) : LimitCone F
    where
  cone :=
    { pt :=
        pullback (terminal.from (F.obj ⟨WalkingPair.left⟩))
          (terminal.from (F.obj ⟨WalkingPair.right⟩))
      π :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x pullback.fst pullback.snd }
  isLimit :=
    isBinaryProductOfIsTerminalIsPullback F _ terminalIsTerminal _ _ (pullbackIsPullback _ _)
#align limit_cone_of_terminal_and_pullbacks limitConeOfTerminalAndPullbacks

variable (C)

-- This is not an instance, as it is not always how one wants to construct binary products!
/-- Any category with pullbacks and terminal object has binary products. -/
theorem hasBinaryProducts_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasBinaryProducts C :=
  { has_limit := fun F => HasLimit.mk (limitConeOfTerminalAndPullbacks F) }
#align has_binary_products_of_has_terminal_and_pullbacks hasBinaryProducts_of_hasTerminal_and_pullbacks

variable {C}

/-- A functor that preserves terminal objects and pullbacks preserves binary products. -/
noncomputable def preservesBinaryProductsOfPreservesTerminalAndPullbacks [HasTerminal C]
    [HasPullbacks C] [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]
    [PreservesLimitsOfShape WalkingCospan F] : PreservesLimitsOfShape (Discrete WalkingPair) F :=
  ⟨fun {K} =>
    preservesLimitOfPreservesLimitCone (limitConeOfTerminalAndPullbacks K).2
      (by
        apply
          isBinaryProductOfIsTerminalIsPullback _ _ (isLimitOfHasTerminalOfPreservesLimit F)
        apply isLimitOfHasPullbackOfPreservesLimit)⟩
        -- 🎉 no goals
#align preserves_binary_products_of_preserves_terminal_and_pullbacks preservesBinaryProductsOfPreservesTerminalAndPullbacks

/-- In a category with a terminal object and pullbacks,
a product of objects `X` and `Y` is isomorphic to a pullback. -/
noncomputable def prodIsoPullback [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y) :=
  limit.isoLimitCone (limitConeOfTerminalAndPullbacks _)
#align prod_iso_pullback prodIsoPullback

/-- If a cospan is the pushout cospan under the initial object, then it is a binary coproduct. -/
def isBinaryCoproductOfIsInitialIsPushout (F : Discrete WalkingPair ⥤ C) (c : Cocone F) {X : C}
    (hX : IsInitial X) (f : X ⟶ F.obj ⟨WalkingPair.left⟩) (g : X ⟶ F.obj ⟨WalkingPair.right⟩)
    (hc :
      IsColimit
        (PushoutCocone.mk (c.ι.app ⟨WalkingPair.left⟩) (c.ι.app ⟨WalkingPair.right⟩ : _) <|
          hX.hom_ext (f ≫ _) (g ≫ _))) :
    IsColimit c
    where
  desc s :=
    hc.desc
      (PushoutCocone.mk (s.ι.app ⟨WalkingPair.left⟩) (s.ι.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac s j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingSpan.left) (hc.fac _ WalkingSpan.right)
  uniq s m J := by
    let c' :=
      PushoutCocone.mk (c.ι.app ⟨WalkingPair.left⟩ ≫ m) (c.ι.app ⟨WalkingPair.right⟩ ≫ m)
        (hX.hom_ext (f ≫ _) (g ≫ _))
    dsimp; rw [← J, ← J]
    -- ⊢ m = IsColimit.desc hc (PushoutCocone.mk (NatTrans.app s.ι { as := WalkingPai …
           -- ⊢ m = IsColimit.desc hc (PushoutCocone.mk (NatTrans.app c.ι { as := WalkingPai …
    apply hc.hom_ext
    -- ⊢ ∀ (j : WalkingSpan), NatTrans.app (PushoutCocone.mk (NatTrans.app c.ι { as : …
    rintro (_ | (_ | _)) <;>
      simp only [PushoutCocone.mk_ι_app_zero, PushoutCocone.mk_ι_app, Category.assoc]
      -- ⊢ f ≫ NatTrans.app c.ι { as := WalkingPair.left } ≫ m = f ≫ NatTrans.app c.ι { …
      -- ⊢ NatTrans.app c.ι { as := WalkingPair.left } ≫ m = NatTrans.app c.ι { as := W …
      -- ⊢ NatTrans.app c.ι { as := WalkingPair.right } ≫ m = NatTrans.app c.ι { as :=  …
    congr 1
    exacts [(hc.fac c' WalkingSpan.left).symm, (hc.fac c' WalkingSpan.left).symm,
      (hc.fac c' WalkingSpan.right).symm]
#align is_binary_coproduct_of_is_initial_is_pushout isBinaryCoproductOfIsInitialIsPushout

/-- The pushout under the initial object is the coproduct -/
def isCoproductOfIsInitialIsPushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsInitial W)
    (H₂ : IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsColimit (BinaryCofan.mk f g) := by
  apply isBinaryCoproductOfIsInitialIsPushout _ _ H₁
  exact H₂
  -- 🎉 no goals
#align is_coproduct_of_is_initial_is_pushout isCoproductOfIsInitialIsPushout

/-- The coproduct is the pushout under the initial object. -/
def isPushoutOfIsInitialIsCoproduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsInitial W) (H₂ : IsColimit (BinaryCofan.mk f g)) :
    IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply PushoutCocone.isColimitAux'
  -- ⊢ (s : PushoutCocone h k) → { l // PushoutCocone.inl (PushoutCocone.mk f g (_  …
  intro s
  -- ⊢ { l // PushoutCocone.inl (PushoutCocone.mk f g (_ : h ≫ f = k ≫ g)) ≫ l = Pu …
  use H₂.desc (BinaryCofan.mk s.inl s.inr)
  -- ⊢ PushoutCocone.inl (PushoutCocone.mk f g (_ : h ≫ f = k ≫ g)) ≫ IsColimit.des …
  use H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.left⟩
  -- ⊢ PushoutCocone.inr (PushoutCocone.mk f g (_ : h ≫ f = k ≫ g)) ≫ IsColimit.des …
  use H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.right⟩
  -- ⊢ ∀ {m : (PushoutCocone.mk f g (_ : h ≫ f = k ≫ g)).pt ⟶ s.pt}, PushoutCocone. …
  intro m h₁ h₂
  -- ⊢ m = IsColimit.desc H₂ (BinaryCofan.mk (PushoutCocone.inl s) (PushoutCocone.i …
  apply H₂.hom_ext
  -- ⊢ ∀ (j : Discrete WalkingPair), NatTrans.app (BinaryCofan.mk f g).ι j ≫ m = Na …
  rintro ⟨⟨⟩⟩
  -- ⊢ NatTrans.app (BinaryCofan.mk f g).ι { as := WalkingPair.left } ≫ m = NatTran …
  · exact h₁.trans (H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.left⟩).symm
    -- 🎉 no goals
  · exact h₂.trans (H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.right⟩).symm
    -- 🎉 no goals
#align is_pushout_of_is_initial_is_coproduct isPushoutOfIsInitialIsCoproduct

/-- Any category with pushouts and an initial object has a colimit cocone for each walking pair. -/
noncomputable def colimitCoconeOfInitialAndPushouts [HasInitial C] [HasPushouts C]
    (F : Discrete WalkingPair ⥤ C) : ColimitCocone F where
  cocone :=
    { pt := pushout (initial.to (F.obj ⟨WalkingPair.left⟩)) (initial.to (F.obj ⟨WalkingPair.right⟩))
      ι :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x pushout.inl pushout.inr }
  isColimit := isBinaryCoproductOfIsInitialIsPushout F _ initialIsInitial _ _ (pushoutIsPushout _ _)
#align colimit_cocone_of_initial_and_pushouts colimitCoconeOfInitialAndPushouts

variable (C)

-- This is not an instance, as it is not always how one wants to construct binary coproducts!
/-- Any category with pushouts and initial object has binary coproducts. -/
theorem hasBinaryCoproducts_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => HasColimit.mk (colimitCoconeOfInitialAndPushouts F) }
#align has_binary_coproducts_of_has_initial_and_pushouts hasBinaryCoproducts_of_hasInitial_and_pushouts

variable {C}

/-- A functor that preserves initial objects and pushouts preserves binary coproducts. -/
noncomputable def preservesBinaryCoproductsOfPreservesInitialAndPushouts [HasInitial C]
    [HasPushouts C] [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]
    [PreservesColimitsOfShape WalkingSpan F] : PreservesColimitsOfShape (Discrete WalkingPair) F :=
  ⟨fun {K} =>
    preservesColimitOfPreservesColimitCocone (colimitCoconeOfInitialAndPushouts K).2 (by
      apply
        isBinaryCoproductOfIsInitialIsPushout _ _
          (isColimitOfHasInitialOfPreservesColimit F)
      apply isColimitOfHasPushoutOfPreservesColimit)⟩
      -- 🎉 no goals
#align preserves_binary_coproducts_of_preserves_initial_and_pushouts preservesBinaryCoproductsOfPreservesInitialAndPushouts

/-- In a category with an initial object and pushouts,
a coproduct of objects `X` and `Y` is isomorphic to a pushout. -/
noncomputable def coprodIsoPushout [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : X ⨿ Y ≅ pushout (initial.to X) (initial.to Y) :=
  colimit.isoColimitCocone (colimitCoconeOfInitialAndPushouts _)
#align coprod_iso_pushout coprodIsoPushout
