/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Stability under coproducts from pushouts and transfinite compositions

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

namespace MorphismProperty

variable {J : Type w} [LinearOrder J]

variable {X Y : J → C} (f : ∀ j, X j ⟶ Y j)

namespace transfiniteCompositionOfShapeSigmaMap

open Classical in
def obj (_ : ∀ j, X j ⟶ Y j) (i j : J) : C :=
  if i ≤ j then X j else Y j

def objIso₁ (i j : J) (hij : i ≤ j) : obj f i j ≅ X j :=
  eqToIso (dif_pos hij)

def objIso₂ (i j : J) (hij : j < i) : obj f i j ≅ Y j :=
  eqToIso (dif_neg (by simpa using hij))

def map (i₁ i₂ : J) (h : i₁ ≤ i₂) (j : J) :
    obj f i₁ j ⟶ obj f i₂ j :=
  if hi₂ : i₂ ≤ j then
    (objIso₁ f i₁ j (by lia)).hom ≫ (objIso₁ f i₂ j hi₂).inv
  else
    if hi₁ : i₁ ≤ j then
      (objIso₁ f i₁ j hi₁).hom ≫ f j ≫ (objIso₂ f i₂ j (by lia)).inv
    else
      (objIso₂ f i₁ j (by lia)).hom ≫ (objIso₂ f i₂ j (by lia)).inv

lemma map_eq_of_le₂ (i₁ i₂ : J) (h : i₁ ≤ i₂) (j : J) (hi₂ : i₂ ≤ j) :
    map f i₁ i₂ h j = (objIso₁ f i₁ j (by lia)).hom ≫ (objIso₁ f i₂ j hi₂).inv := by
  grind [map]

@[simp]
lemma map_refl (i j : J) :
    map f i i (by rfl) j = 𝟙 _ := by
  grind [map]

@[reassoc (attr := simp)]
lemma map_trans (i₁ i₂ i₃ : J) (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (j : J) :
    map f i₁ i₂ hi₁₂ j ≫ map f i₂ i₃ hi₂₃ j = map f i₁ i₃ (hi₁₂.trans hi₂₃) j := by
  grind [map]

open Classical in
def objι (i j : J) :
    obj f i j ⟶ Y j :=
  if hi : i ≤ j then
    (objIso₁ f i j hi).hom ≫ f j
  else
    (objIso₂ f i j (by lia)).hom

@[reassoc (attr := simp)]
lemma objIso₁_inv_objι (i j : J) (hi : i ≤ j) :
    (objIso₁ f i j hi).inv ≫ objι f i j = f j:= by
  grind [objι]

@[reassoc (attr := simp)]
lemma map_objι (i₁ i₂ : J) (hi : i₁ ≤ i₂) (j : J) :
    map f i₁ i₂ hi j ≫ objι f i₂ j = objι f i₁ j := by
  grind [map, objι]

@[reassoc (attr := simp)]
lemma objIso₂_inv_map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (j : J) (hi₁ : j < i₁) :
    (objIso₂ f i₁ j hi₁).inv ≫ map f i₁ i₂ hi j = (objIso₂ f i₂ j (by lia)).inv := by
  grind [map]

@[simps]
def diagramFunctor :
    J ⥤ Discrete J ⥤ C where
  obj i := Discrete.functor (obj f i)
  map {i₁ i₂} g := Discrete.natTrans (fun ⟨j⟩ ↦ map f i₁ i₂ (leOfHom g) j)

abbrev columnFunctor (j : J) : J ⥤ C := (diagramFunctor f).flip.obj (.mk j)

instance (j : J) [OrderBot J] [SuccOrder J] :
    (columnFunctor f j).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    by_cases h : m ≤ j
    · exact ⟨{
        desc s := (objIso₁ f m j h).hom ≫ (objIso₁ f ⊥ j bot_le).inv ≫
          s.ι.app ⟨⊥, Order.IsSuccLimit.bot_lt hm⟩
        fac s k := by
          rw [← s.w (show ⟨⊥, Order.IsSuccLimit.bot_lt hm⟩ ⟶ k from homOfLE bot_le)]
          dsimp
          grind [map]
        uniq s l hl := by
          simp [← hl ⟨⊥, Order.IsSuccLimit.bot_lt hm⟩, map_eq_of_le₂ f _ _ bot_le j h]
      }⟩
    · simp only [not_le] at h
      exact ⟨{
        desc s := (objIso₂ f m j h).hom ≫
            (objIso₂ f _ _ (Order.lt_succ_of_not_isMax (not_isMax_iff.2 ⟨_, h⟩))).inv ≫
            s.ι.app ⟨Order.succ j, hm.succ_lt_iff.2 h⟩
        fac s k := by
          dsimp
          by_cases hk : Order.succ j ≤ k
          · rw [← s.w (show ⟨Order.succ j, hm.succ_lt_iff.2 h⟩ ⟶ k from homOfLE hk)]
            dsimp
            grind [map]
          · simp only [not_le] at hk
            rw [← s.w (show k ⟶ ⟨Order.succ j, hm.succ_lt_iff.2 h⟩ from homOfLE hk.le)]
            dsimp
            grind [map]
        uniq s l hl := by simp [← hl ⟨Order.succ j, hm.succ_lt_iff.2 h⟩]
      }⟩

variable [HasCoproductsOfShape J C] in
noncomputable def isoBot [OrderBot J] : ∐ (obj f ⊥) ≅ ∐ X :=
  Sigma.mapIso (fun j ↦ objIso₁ f ⊥ j bot_le)

@[simps]
def cocone : Cocone (diagramFunctor f) where
  pt := Discrete.functor Y
  ι.app i := Discrete.natTrans (fun ⟨j⟩ ↦ objι f i j)

def isColimitCocone [SuccOrder J] [NoMaxOrder J] :
    IsColimit (cocone f) :=
  evaluationJointlyReflectsColimits _ (fun ⟨j⟩ ↦
    { desc s := (objIso₂ f (Order.succ j) j (Order.lt_succ j)).inv ≫
        s.ι.app (Order.succ j)
      fac s i := by
        dsimp
        by_cases hij : i ≤ Order.succ j
        · rw [← s.w (homOfLE hij)]
          dsimp
          grind [map, objι]
        · simp only [not_le] at hij
          have : ¬ i ≤ j := by
            simp only [not_le]
            exact lt_of_le_of_lt (Order.le_succ j) hij
          rw [← s.w (homOfLE hij.le)]
          simp [objι, map, dif_neg this]
      uniq s l hl := by
        dsimp
        rw [← hl]
        dsimp
        grind [objι] })

variable [HasCoproductsOfShape J C] [SuccOrder J] [NoMaxOrder J]

instance [OrderBot J] : (diagramFunctor f).IsWellOrderContinuous where
  nonempty_isColimit m hm :=
    ⟨evaluationJointlyReflectsColimits _
      (fun ⟨j⟩ ↦ (columnFunctor f j).isColimitOfIsWellOrderContinuous m hm)⟩

instance [OrderBot J] : (diagramFunctor f ⋙ colim).IsWellOrderContinuous where
  nonempty_isColimit m hm :=
    ⟨isColimitOfPreserves colim
      ((diagramFunctor f).isColimitOfIsWellOrderContinuous m hm)⟩

open Classical in
lemma isPushout (i : J) :
    IsPushout ((objIso₁ f i i le_rfl).inv ≫ Sigma.ι _ i) (f i)
      (colimMap ((diagramFunctor f).map (homOfLE (Order.le_succ i))))
      ((objIso₂ f (Order.succ i) i (Order.lt_succ i)).inv ≫ Sigma.ι _ i) where
  w := by simp [map]
  isColimit' := ⟨by
    let φ (s : PushoutCocone ((objIso₁ f i i le_rfl).inv ≫ Sigma.ι (obj f i) i) (f i))
        (j : J) :
        obj f (Order.succ i) j ⟶ s.pt :=
      if hij : i < j then
          (objIso₁ f (Order.succ i) j (Order.succ_le_of_lt hij)).hom ≫
            (objIso₁ f i j hij.le).inv ≫ Sigma.ι _ j ≫ s.inl
      else
        if hij : j < i then
          (objIso₂ f (Order.succ i) j (Order.lt_succ_of_le hij.le)).hom ≫
            (objIso₂ f i j hij).inv ≫ Sigma.ι _ j ≫ s.inl
        else
          haveI hij : i = j := by lia
          (objIso₂ f (Order.succ i) j (by simp [hij])).hom ≫
            eqToHom (by rw [hij]) ≫ s.inr
    have hφ₁ (s) :
        (objIso₂ f _ _ (Order.lt_succ i)).inv ≫ φ s i = s.inr := by simp [φ]
    have hφ₂ (s) (j : J) :
        map f _ _ (Order.le_succ i) j ≫ φ s j = Sigma.ι (obj f i) j ≫ s.inl := by
      dsimp [φ]
      split_ifs with h₁ h₂
      · simp [map, dif_pos h₁]
      · simp [map, dif_neg h₁, dif_neg (show ¬ i ≤ j by lia)]
      · obtain rfl : i = j := by lia
        have := s.condition
        rw [Category.assoc] at this
        simp [← cancel_epi (objIso₁ f i i le_rfl).inv, this, map]
    refine PushoutCocone.IsColimit.mk _ (fun s ↦ Sigma.desc (φ s))
      (fun s ↦ by ext; simp [hφ₂]) (fun s ↦ by simp [hφ₁])
      (fun s l hl₁ hl₂ ↦ Sigma.hom_ext _ _ (fun j ↦ ?_))
    dsimp
    rw [Sigma.ι_desc]
    by_cases hij : i = j
    · subst hij
      rw [Category.assoc] at hl₂
      rw [← cancel_epi ((objIso₂ f (Order.succ i) i (Order.lt_succ i)).inv), hl₂, hφ₁]
    · replace hl₁ := Sigma.ι _ j ≫= hl₁
      dsimp at hl₁
      rw [Sigma.ι_map_assoc, ← hφ₂] at hl₁
      have : IsIso (map f _ _ (Order.le_succ i) j) := by
        dsimp [map]
        split_ifs
        · infer_instance
        · lia
        · infer_instance
      rwa [← cancel_epi (map f _ _ (Order.le_succ i) j)]⟩

end transfiniteCompositionOfShapeSigmaMap

section

variable [HasCoproductsOfShape J C] [OrderBot J] [SuccOrder J] [WellFoundedLT J] [NoMaxOrder J]

open transfiniteCompositionOfShapeSigmaMap in
noncomputable def transfiniteCompositionOfShapeSigmaMap :
    TransfiniteCompositionOfShape (MorphismProperty.ofHoms f).pushouts J
      (Limits.Sigma.map f) where
  F := diagramFunctor f ⋙ colim
  isoBot := isoBot f
  incl := { app i := colim.map ((cocone f).ι.app i) }
  isColimit := isColimitOfPreserves colim (isColimitCocone f)
  map_mem i hi := MorphismProperty.pushouts_mk _ (isPushout f i) ⟨i⟩
  fac := by dsimp [isoBot]; cat_disch

instance [W.IsStableUnderTransfiniteCompositionOfShape J]
    [W.IsStableUnderCobaseChange] :
    W.IsStableUnderCoproductsOfShape J :=
  IsStableUnderCoproductsOfShape.mk _ _ (fun X Y _ _ f hf ↦ by
    refine transfiniteCompositionsOfShape_le _ _ _
      ((transfiniteCompositionOfShapeSigmaMap f).ofLE ?_).mem
    simp only [pushouts_le_iff]
    rintro _ _ _ ⟨j⟩
    exact hf j)

end

/-instance [HasCoproducts.{w} C] [IsStableUnderTransfiniteComposition.{w} W]
    [W.IsStableUnderCobaseChange] : W.IsStableUnderCoproductsOfShape J := by
  by_cases hJ : Finite J
  · sorry
  · let κ := Cardinal.mk J
    have hκ : Cardinal.aleph0 ≤ κ := by
      simpa only [κ, ← Cardinal.infinite_iff, ← not_finite_iff_infinite]
    let e : Discrete J ≌ Discrete κ.ord.ToType := by
      apply Discrete.equivalence
      sorry
    have : W.IsStableUnderColimitsOfShape (Discrete κ.ord.ToType) := by
      have := Cardinal.noMaxOrder hκ
      have : OrderBot κ.ord.ToType :=
        Cardinal.toTypeOrderBot (by
          rintro h
          exact Cardinal.aleph0_ne_zero (by rwa [h, nonpos_iff_eq_zero] at hκ))
      infer_instance
    exact IsStableUnderColimitsOfShape.of_equivalence e.symm-/

end MorphismProperty

end CategoryTheory
