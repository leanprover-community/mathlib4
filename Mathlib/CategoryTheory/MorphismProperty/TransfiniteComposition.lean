/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder
import Mathlib.Order.Shrink
import Mathlib.Logic.UnivLE

/-!
# Classes of morphisms that are stable under transfinite composition

Given a well ordered type `J`, `W : MorphismProperty C` and
a morphism `f : X ⟶ Y`, we define a structure `W.TransfiniteCompositionOfShape J f`
which expresses that `f` is a transfinite composition of morphisms in `J`.
This structures extends `CategoryTheory.TransfiniteCompositionOfShape` which was
defined in the file `CategoryTheory.Limits.Shape.Preorder.TransfiniteCompositionOfShape`.
We use this structure in order to define the class of morphisms
`W.transfiniteCompositionsOfShape J : MorphismProperty C`, and the type class
`W.IsStableUnderTransfiniteCompositionOfShape J`.
In particular, if `J := ℕ`, we obtain `W.IsStableUnderInfiniteComposition`,

Finally, we introduce the class `W.IsStableUnderTransfiniteComposition`
which says that `W.IsStableUnderTransfiniteCompositionOfShape J`
holds for any well ordered type `J` in a certain universe `u`.

-/

universe w w' v v' u u'

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

variable {J : Type w} [PartialOrder J]

/-- Given a functor `F : J ⥤ C` and `m : J`, this is the induced
functor `Set.Iio j ⥤ C`. -/
@[simps!]
def restrictionLT (F : J ⥤ C) (j : J) : Set.Iio j ⥤ C :=
  Monotone.functor (f := fun k ↦ k.1) (fun _ _ ↦ id) ⋙ F

/-- Given a functor `F : J ⥤ C` and `m : J`, this is the cocone with point `F.obj m`
for the restriction of `F` to `Set.Iio m`. -/
@[simps]
def coconeLT (F : J ⥤ C) (m : J) :
    Cocone (F.restrictionLT m) where
  pt := F.obj m
  ι :=
    { app := fun ⟨i, hi⟩ ↦ F.map (homOfLE hi.le)
      naturality := fun ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ f ↦ by
        dsimp
        rw [← F.map_comp, comp_id]
        rfl }

/-- Given a functor `F : J ⥤ C` and `j : J`, this is the induced
functor `Set.Iic j ⥤ C`. -/
abbrev restrictionLE (F : J ⥤ C) (j : J) : Set.Iic j ⥤ C :=
  (Set.initialSegIic j).monotone.functor ⋙ F

/-- Given a functor `F : J ⥤ C` and `j : J`, this is the (colimit) cocone
with point `F.obj j` for the restriction of `F` to `Set.Iic m`. -/
@[simps!]
def coconeLE (F : J ⥤ C) (j : J) :
    Cocone (F.restrictionLE j) where
  pt := F.obj j
  ι :=
    { app x := F.map (homOfLE x.2)
      naturality _ _ f := by
        dsimp
        simp only [homOfLE_leOfHom, ← Functor.map_comp, comp_id]
        rfl }

/-- The colimit of `F.coconeLE j` is `F.obj j`. -/
def isColimitCoconeLE (F : J ⥤ C) (j : J) :
    IsColimit (F.coconeLE j) where
  desc s := s.ι.app ⟨j, by simp⟩
  fac s k := by
    simpa only [Functor.const_obj_obj, Functor.const_obj_map, comp_id]
      using s.ι.naturality (homOfLE k.2 : k ⟶ ⟨j, by simp⟩)
  uniq s m hm := by simp [← hm]

end Functor

namespace MorphismProperty

variable (W : MorphismProperty C)

section

variable (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {J' : Type w'} [LinearOrder J'] [SuccOrder J'] [OrderBot J'] [WellFoundedLT J']

/-- Structure expressing that a morpshism `f : X ⟶ Y` in a category `C`
is a transfinite composition of shape `J` of morphisms in `W : MorphismProperty C`. -/
structure TransfiniteCompositionOfShape {X Y : C} (f : X ⟶ Y) extends
    CategoryTheory.TransfiniteCompositionOfShape J f where
  map_mem (j : J) (hj : ¬IsMax j) : W (F.map (homOfLE (Order.le_succ j)))

namespace TransfiniteCompositionOfShape

section

variable {W J} {X Y : C} {f : X ⟶ Y} (h : W.TransfiniteCompositionOfShape J f)

/-- If `f` and `f'` are two isomorphic morphisms and `f` is a transfinite composition
of morphisms in `W : MorphismProperty C`, then so is `f'`. -/
@[simps toTransfiniteCompositionOfShape]
def ofArrowIso {X' Y' : C}
    {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    W.TransfiniteCompositionOfShape J f' where
  __ := h.toTransfiniteCompositionOfShape.ofArrowIso e
  map_mem := h.map_mem

/-- If `W ≤ W'`, then transfinite compositions of shape `J` of morphisms in `W`
are also transfinite composition of shape `J` of morphisms in `W'`. -/
@[simps toTransfiniteCompositionOfShape]
def ofLE {W' : MorphismProperty C} (hW : W ≤ W') :
    W'.TransfiniteCompositionOfShape J f where
  __ := h.toTransfiniteCompositionOfShape
  map_mem j hj := hW _ (h.map_mem j hj)

/-- If `f` is a transfinite composition of shape `J` of morphisms in `W`,
then it is also a transfinite composition of shape `J'` of morphisms in `W` if `J' ≃o J`. -/
def ofOrderIso {J' : Type w'} [LinearOrder J'] [OrderBot J']
    [SuccOrder J'] [WellFoundedLT J'] (e : J' ≃o J) :
    W.TransfiniteCompositionOfShape J' f where
  __ := h.toTransfiniteCompositionOfShape.ofOrderIso e
  map_mem j hj := by
    have := h.map_mem (e j) (by simpa only [e.isMax_apply])
    rw [← W.arrow_mk_mem_toSet_iff] at this ⊢
    have eq : Arrow.mk (homOfLE (e.monotone (Order.le_succ j))) =
      Arrow.mk (homOfLE (Order.le_succ (e j))) :=
        Arrow.ext rfl (e.map_succ j) rfl
    replace eq := congr_arg h.F.mapArrow.obj eq
    convert this using 1

end

/-- If `F : ComposableArrows C n` and all maps `F.obj i.castSucc ⟶ F.obj i.succ`
are in `W`, then `F.hom : F.left ⟶ F.right` is a transfinite composition of
shape `Fin (n + 1)` of morphisms in `W`. -/
@[simps!]
def ofComposableArrows {n : ℕ} (F : ComposableArrows C n)
    (hF : ∀ (i : Fin n), W (F.map (homOfLE i.castSucc_le_succ))) :
    W.TransfiniteCompositionOfShape (Fin (n + 1)) F.hom where
  toTransfiniteCompositionOfShape := .ofComposableArrows F
  map_mem j hj := by
    obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
    · replace hF := hF j
      rw [← W.arrow_mk_mem_toSet_iff] at hF ⊢
      have eq : Arrow.mk (homOfLE (Order.le_succ j.castSucc)) =
        Arrow.mk (homOfLE j.castSucc_le_succ) :=
          Arrow.ext rfl j.orderSucc_castSucc rfl
      replace eq := congr_arg F.mapArrow.obj eq
      convert hF using 1
    · rw [isMax_iff_eq_top] at hj
      exact (hj rfl).elim

/-- The identity of any object is a transfinite composition of shape `Fin 1`. -/
def id (X : C) : W.TransfiniteCompositionOfShape (Fin 1) (𝟙 X) :=
  ofComposableArrows W (.mk₀ X) (by simp)

variable {W}

/-- If `f : X ⟶ Y` satisfies `W f`, then `f` is a transfinite composition of shape `Fin 2`
of morphisms in `W`. -/
def ofMem {X Y : C} (f : X ⟶ Y) (hf : W f) :
    W.TransfiniteCompositionOfShape (Fin 2) f :=
  ofComposableArrows W (.mk₁ f) (fun i ↦ by fin_cases i; assumption)

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` satisfy `W f` and `W g`, then `f ≫ g` is a
transfinite composition of shape `Fin 3` of morphisms in `W`. -/
def ofComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) :
    W.TransfiniteCompositionOfShape (Fin 3) (f ≫ g) :=
  ofComposableArrows W (.mk₂ f g) (fun i ↦ by fin_cases i <;> assumption)

end TransfiniteCompositionOfShape

/-- Given `W : MorphismProperty C` and a well-ordered type `J`, this is
the class of morphisms that are transfinite composition of shape `J`
of morphisms in `W`. -/
def transfiniteCompositionsOfShape : MorphismProperty C :=
  fun _ _ f ↦ Nonempty (W.TransfiniteCompositionOfShape J f)

lemma monotone_transfiniteCompositionsOfShape :
    Monotone (transfiniteCompositionsOfShape (C := C) (J := J)) := by
  rintro _ _ h _ _ _ ⟨t⟩
  exact ⟨t.ofLE h⟩

variable {J} in
lemma transfiniteCompositionsOfShape_eq_of_orderIso (e : J ≃o J') :
    W.transfiniteCompositionsOfShape J =
      W.transfiniteCompositionsOfShape J' := by
  ext _ _ f
  exact ⟨fun ⟨h⟩ ↦ ⟨h.ofOrderIso e.symm⟩, fun ⟨h⟩ ↦ ⟨h.ofOrderIso e⟩⟩

instance : RespectsIso (W.transfiniteCompositionsOfShape J) :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e ⟨h⟩ ↦ ⟨h.ofArrowIso e⟩)

variable {W J} in
lemma TransfiniteCompositionOfShape.mem {X Y : C} (f : X ⟶ Y)
    (h : W.TransfiniteCompositionOfShape J f) :
    W.transfiniteCompositionsOfShape J f := ⟨h⟩

-- to be moved
instance (ι : Type*) [Preorder ι] [OrderBot ι] (j : ι) :
    OrderBot (Set.Iic j) where
  bot := ⟨⊥, bot_le⟩
  bot_le _ := bot_le

variable {J} in
lemma transfiniteCompositionsOfShape_map_bot_le
    (F : J ⥤ C) [F.IsWellOrderContinuous] (j : J)
    (hF : ∀ (i : J) (_ : i < j), W (F.map (homOfLE (Order.le_succ i)))) :
    W.transfiniteCompositionsOfShape (Set.Iic j) (F.map (homOfLE bot_le : ⊥ ⟶ j)) := by
  sorry
  /-
  refine ⟨_, fun ⟨i, hi⟩ hi' ↦ ?_, _, F.isColimitCoconeLE j⟩
  dsimp [Monotone.functor]
  have := Set.Iic.succ_coe _ hi'
  dsimp at this
  have := hF i (by
    simp only [not_isMax_iff, Subtype.exists, Subtype.mk_lt_mk, Set.mem_Iic, exists_prop] at hi'
    obtain ⟨k, hk⟩ := hi'
    exact lt_of_lt_of_le hk.2 hk.1)
  convert this-/

lemma transfiniteCompositionsOfShape_map_of_preserves (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    {X Y : C} (f : X ⟶ Y) {P : MorphismProperty D}
    [PreservesColimitsOfShape J G]
    (h : (P.inverseImage G).transfiniteCompositionsOfShape J f) :
    P.transfiniteCompositionsOfShape J (G.map f) := by
  sorry
  /-
  obtain ⟨F, hF, c, hc⟩  := h
  exact ⟨F ⋙ G, hF, _, isColimitOfPreserves G hc⟩-/

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite compositions
of shape `J` if for any well-order-continuous functor `F : J ⥤ C` such that
`F.obj j ⟶ F.obj (Order.succ j)` is in `W`, then `F.obj ⊥ ⟶ c.pt` is in `W`
for any colimit cocone `c : Cocone F`. -/
@[mk_iff]
class IsStableUnderTransfiniteCompositionOfShape : Prop where
  le : W.transfiniteCompositionsOfShape J ≤ W

lemma transfiniteCompositionsOfShape_le
    [W.IsStableUnderTransfiniteCompositionOfShape J] :
    W.transfiniteCompositionsOfShape J ≤ W :=
  IsStableUnderTransfiniteCompositionOfShape.le

variable {J} in
lemma isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso (e : J ≃o J') :
    W.IsStableUnderTransfiniteCompositionOfShape J ↔
      W.IsStableUnderTransfiniteCompositionOfShape J' := by
  simp only [isStableUnderTransfiniteCompositionOfShape_iff,
    W.transfiniteCompositionsOfShape_eq_of_orderIso e]

end

/-- A class of morphisms `W : MorphismProperty C` is stable under infinite composition
if for any functor `F : ℕ ⥤ C` such that `F.obj n ⟶ F.obj (n + 1)` is in `W` for any `n : ℕ`,
the map `F.obj 0 ⟶ c.pt` is in `W` for any colimit cocone `c : Cocone F`. -/
abbrev IsStableUnderInfiniteComposition : Prop :=
  W.IsStableUnderTransfiniteCompositionOfShape ℕ

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite composition
if it is multiplicative and stable under transfinite composition of any shape
(in a certain universe). -/
class IsStableUnderTransfiniteComposition : Prop where
  isStableUnderTransfiniteCompositionOfShape
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.IsStableUnderTransfiniteCompositionOfShape J

namespace IsStableUnderTransfiniteComposition

attribute [instance] isStableUnderTransfiniteCompositionOfShape

protected instance isomorphisms :
    (isomorphisms C).IsStableUnderTransfiniteComposition where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := ⟨by
    sorry /-
    rintro _ _ _ ⟨F, hF, c, hc⟩
    suffices ∀ (j : J), IsIso (F.map ((homOfLE bot_le) : ⊥ ⟶ j)) from
      Functor.IsEventuallyConstantFrom.isIso_ι_of_isColimit (fun j f ↦ this j) hc
    intro j
    induction j using SuccOrder.limitRecOn with
    | hm _ h =>
        obtain rfl := h.eq_bot
        dsimp
        infer_instance
    | hs j hj h =>
        have : IsIso _ := hF j hj
        rw [← homOfLE_comp bot_le (Order.le_succ j), F.map_comp]
        infer_instance
    | hl j hj h =>
        letI : OrderBot (Set.Iio j) :=
          { bot := ⟨⊥, Order.IsSuccLimit.bot_lt hj ⟩
            bot_le j := bot_le }
        simpa using Functor.IsEventuallyConstantFrom.isIso_ι_of_isColimit (i₀ := ⊥)
          (fun i _ ↦ h i.1 i.2) (F.isColimitOfIsWellOrderContinuous j hj)-/ ⟩

variable [IsStableUnderTransfiniteComposition.{w'} W]

lemma shrink [UnivLE.{w, w'}] :
    IsStableUnderTransfiniteComposition.{w} W where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    rw [isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso W
      (orderIsoShrink.{w'} J)]
    infer_instance

lemma shrink₀ : IsStableUnderTransfiniteComposition.{0} W := shrink.{0, w'} W

attribute [local instance] shrink₀

instance : W.IsMultiplicative where
  id_mem X :=
    transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.id W X).mem
  comp_mem f g hf hg :=
    transfiniteCompositionsOfShape_le _ _ _
      (TransfiniteCompositionOfShape.ofComp f g hf hg).mem

end IsStableUnderTransfiniteComposition

/-- The class of transfinite compositions (for arbitrary well-ordered types `J : Type w`)
of a class of morphisms `W`. -/
@[pp_with_univ]
def transfiniteCompositions : MorphismProperty C :=
  ⨆ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
    (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J

lemma transfiniteCompositions_iff {X Y : C} (f : X ⟶ Y) :
    transfiniteCompositions.{w} W f ↔
      ∃ (J : Type w) (_ : LinearOrder J) (_ : SuccOrder J) (_ : OrderBot J)
        (_ : WellFoundedLT J), W.transfiniteCompositionsOfShape J f := by
  simp only [transfiniteCompositions, iSup_iff]

lemma transfiniteCompositionsOfShape_le_transfiniteCompositions
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.transfiniteCompositionsOfShape J ≤ transfiniteCompositions.{w} W := by
  intro A B f hf
  rw [transfiniteCompositions_iff]
  exact ⟨_, _, _, _, _, hf⟩

end MorphismProperty

end CategoryTheory
