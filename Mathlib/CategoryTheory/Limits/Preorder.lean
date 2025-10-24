/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Joël Riou, Fernando Chu
-/

import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Order.Bounds.Defs

/-!
# (Co)limits in a preorder category

We provide basic results about (co)limits in the associated category of a preordered type.
- We show that a functor `F` has a (co)limit iff it has a greatest lower bound (least upper bound).
- We show maximal (minimal) elements correspond to terminal (initial) objects.
- We show that (co)products correspond to infima (suprema).

-/

universe v u u'

open CategoryTheory Limits

namespace Preorder

variable {C : Type u}

section

variable [Preorder C]
variable {J : Type u'} [Category.{v} J]
variable (F : J ⥤ C)

/-- The cone associated to a lower bound of a functor. -/
def coneOfLowerBound {x : C} (h : x ∈ lowerBounds (Set.range F.obj)) : Cone F where
  pt := x
  π := { app i := homOfLE (h (Set.mem_range_self _)) }

/-- The point of a cone is a lower bound. -/
lemma conePt_mem_lowerBounds (c : Cone F) : c.pt ∈ lowerBounds (Set.range F.obj) := by
  intro x ⟨i, p⟩; rw [← p]; exact (c.π.app i).le

/-- If a cone is a limit, its point is a glb. -/
lemma isGLB_of_isLimit {c : Cone F} (h : IsLimit c) : IsGLB (Set.range F.obj) c.pt :=
  ⟨(conePt_mem_lowerBounds F c), fun _ k ↦ (h.lift (coneOfLowerBound F k)).le⟩

/-- If the point of cone is a glb, the cone is a limi.t -/
def isLimitOfIsGLB (c : Cone F) (h : IsGLB (Set.range F.obj) c.pt) : IsLimit c where
  lift d := (h.2 (conePt_mem_lowerBounds F d)).hom

/-- A functor has a limit iff there exists a glb. -/
lemma hasLimit_iff_hasGLB : HasLimit F ↔ ∃ x, IsGLB (Set.range F.obj) x := by
  constructor <;> intro h
  · let limitCone := getLimitCone F
    exact ⟨limitCone.cone.pt, isGLB_of_isLimit F limitCone.isLimit⟩
  · obtain ⟨l, isGLB⟩ := h
    exact ⟨⟨⟨coneOfLowerBound F isGLB.1, isLimitOfIsGLB F _ isGLB⟩⟩⟩

/-- The cocone associated to an upper bound of a functor -/
def coconePt_mem_upperBounds {x : C} (h : x ∈ upperBounds (Set.range F.obj)) : Cocone F where
  pt := x
  ι := { app i := homOfLE (h (Set.mem_range_self _)) }

/-- The point of a cocone is an upper bound. -/
lemma upperBoundOfCocone (c : Cocone F) : c.pt ∈ upperBounds (Set.range F.obj) := by
  intro x ⟨i, p⟩; rw [← p]; exact (c.ι.app i).le

/-- If a cocone is a colimit, its point is a lub. -/
lemma isLUB_of_isColimit {c : Cocone F} (h : IsColimit c) : IsLUB (Set.range F.obj) c.pt :=
  ⟨(upperBoundOfCocone F c), fun _ k ↦ (h.desc (coconePt_mem_upperBounds F k)).le⟩

/-- If the point of cocone is a lub, the cocone is a .colimit -/
def isColimitOfIsLUB (c : Cocone F) (h : IsLUB (Set.range F.obj) c.pt) : IsColimit c where
  desc d := (h.2 (upperBoundOfCocone F d)).hom

/-- A functor has a colimit iff there exists a lub. -/
lemma hasColimit_iff_hasLUB :
    HasColimit F ↔ ∃ x, IsLUB (Set.range F.obj) x := by
  constructor <;> intro h
  · let limitCocone := getColimitCocone F
    exact ⟨limitCocone.cocone.pt, isLUB_of_isColimit F limitCocone.isColimit⟩
  · obtain ⟨l, isLUB⟩ := h
    exact ⟨⟨⟨coconePt_mem_upperBounds F isLUB.1, isColimitOfIsLUB F _ isLUB⟩⟩⟩

end

noncomputable section

variable [Preorder C]

/-- A terminal object in a preorder `C` is top element for `C`. -/
def _root_.CategoryTheory.Limits.IsTerminal.orderTop {X : C} (t : IsTerminal X) : OrderTop C where
  top := X
  le_top Y := leOfHom (t.from Y)

/-- A preorder with a terminal object has a greatest element. -/
def orderTopOfHasTerminal [HasTerminal C] : OrderTop C := IsTerminal.orderTop terminalIsTerminal

/-- If `C` is a preorder with top, then `⊤` is a terminal object. -/
def isTerminalTop [OrderTop C] : IsTerminal (⊤ : C) := IsTerminal.ofUnique _

instance (priority := low) [OrderTop C] : HasTerminal C := hasTerminal_of_unique ⊤

/-- An initial object in a preorder `C` is bottom element for `C`. -/
def _root_.CategoryTheory.Limits.IsInitial.orderBot {X : C} (t : IsInitial X) : OrderBot C where
  bot := X
  bot_le Y := leOfHom (t.to Y)

/-- A preorder with an initial object has a least element. -/
def orderBotOfHasInitial [HasInitial C] : OrderBot C := IsInitial.orderBot initialIsInitial

/-- If `C` is a preorder with bot, then `⊥` is an initial object. -/
def isInitialBot [OrderBot C] : IsInitial (⊥ : C) := IsInitial.ofUnique _

instance (priority := low) [OrderBot C] : HasInitial C := hasInitial_of_unique ⊥

end

noncomputable section

variable [PartialOrder C]

/--
A family of limiting binary fans on a partial order induces an inf-semilattice structure on it.
-/
def semilatticeInfOfIsLimitBinaryFan
    (c : ∀ (X Y : C), BinaryFan X Y) (h : (X Y : C) → IsLimit (c X Y)) : SemilatticeInf C where
  inf X Y := (c X Y).pt
  inf_le_left X Y := leOfHom (c X Y).fst
  inf_le_right X Y := leOfHom (c X Y).snd
  le_inf _ _ _ le_fst le_snd := leOfHom <| (h _ _).lift (BinaryFan.mk le_fst.hom le_snd.hom)

variable (C) in
/-- If a partial order has binary products, then it is a inf-semilattice -/
def semilatticeInfOfHasBinaryProducts [HasBinaryProducts C] : SemilatticeInf C :=
  semilatticeInfOfIsLimitBinaryFan
    (fun _ _ ↦ BinaryFan.mk prod.fst prod.snd) (fun X Y ↦ prodIsProd X Y)

/--
A family of colimiting binary cofans on a partial order induces a sup-semilattice structure on it.
-/
def semilatticeSupOfIsColimitBinaryCofan
    (c : ∀ (X Y : C), BinaryCofan X Y) (h : (X Y : C) → IsColimit (c X Y)) : SemilatticeSup C where
  sup X Y := (c X Y).pt
  le_sup_left X Y := leOfHom (c X Y).inl
  le_sup_right X Y := leOfHom (c X Y).inr
  sup_le _ _ _ le_inl le_inr := leOfHom <| (h _ _).desc (BinaryCofan.mk le_inl.hom le_inr.hom)

variable (C) in
/-- If a partial order has binary coproducts, then it is a sup-semilattice -/
def semilatticeSupOfHasBinaryCoproducts [HasBinaryCoproducts C] : SemilatticeSup C :=
  semilatticeSupOfIsColimitBinaryCofan
    (fun _ _ ↦ BinaryCofan.mk coprod.inl coprod.inr) (fun X Y ↦ coprodIsCoprod X Y)

end

section

/-- The infimum of two elements in a preordered type is a binary product in
the category associated to this preorder. -/
def isLimitBinaryFan [SemilatticeInf C] (X Y : C) :
    IsLimit (BinaryFan.mk (P := X ⊓ Y) (homOfLE inf_le_left) (homOfLE inf_le_right)) :=
  BinaryFan.isLimitMk (fun s ↦ homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

instance (priority := low) [SemilatticeInf C] : HasBinaryProducts C where
  has_limit F := by
    have : HasLimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isLimitBinaryFan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasLimit_of_iso (diagramIsoPair F).symm

/-- The supremum of two elements in a preordered type is a binary coproduct
in the category associated to this preorder. -/
def isColimitBinaryCofan [SemilatticeSup C] (X Y : C) :
    IsColimit (BinaryCofan.mk (P := X ⊔ Y) (homOfLE le_sup_left) (homOfLE le_sup_right)) :=
  BinaryCofan.isColimitMk (fun s ↦ homOfLE (sup_le (leOfHom s.inl) (leOfHom s.inr)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

instance (priority := low) [SemilatticeSup C] : HasBinaryCoproducts C where
  has_colimit F := by
    have : HasColimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isColimitBinaryCofan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasColimit_of_iso (diagramIsoPair F)

end

end Preorder
