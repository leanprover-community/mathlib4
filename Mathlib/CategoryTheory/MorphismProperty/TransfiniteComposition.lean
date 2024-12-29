/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.Limit
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Classes of morphisms that are stable under transfinite composition

Let `F : J ⥤ C` be a functor from a well ordered type `J`. We say that `F`
is well-order-continuous (`F.IsWellOrderContinuous`), if for any `m : J`
which satisfies `hm : Order.IsSuccLimit m`, `F.obj m` identifies
to the colimit of the `F.obj j` for `j < m`.

Given `W : MorphismProperty C`, we say that
`W.IsStableUnderTransfiniteCompositionOfShape J` if for any
colimit cocone `c` for a well-order-continuous functor `F : J ⥤ C`
such that `F.obj j ⟶ F.obj (Order.succ j)` belongs to `W`, we can
conclude that `c.ι.app ⊥ : F.obj ⊥ ⟶ c.pt` belongs to `W`. The
morphisms of this form `c.ι.app ⊥` for any `F` and `c` are
part of the morphism property `W.transfiniteCompositionsOfShape J`.
The condition of being stable by transfinite composition of shape `J`
is actually phrased as `W.transfiniteCompositionsOfShape J ≤ W`.

In particular, if `J := ℕ`, we define `W.IsStableUnderInfiniteComposition`,
which means that if `F : ℕ ⥤ C` is such that `F.obj n ⟶ F.obj (n + 1)`
belongs to `W`, then `F.obj 0 ⟶ c.pt` belongs to `W`
for any colimit cocone `c : Cocone F`.

Finally, we define the class `W.IsStableUnderTransfiniteComposition`
which says that `W.IsStableUnderTransfiniteCompositionOfShape J`
holds for any well ordered type `J` in a certain universe `u`.
(We also require that `W` is multiplicative.)

-/

universe w v v' v'' u u' u''

instance {α : Type u} [Preorder α] {j : α} :
    OrderTop (Set.Iic j) where
  top := ⟨j, by simp⟩
  le_top i := i.2

lemma Set.Iic.not_isMin_coe {α : Type u} [Preorder α] {j : α}
    {k : Set.Iic j} (hk : ¬ IsMin k) :
    ¬ IsMin k.1 :=
   fun h ↦ hk (fun _ ha' ↦ h ha')

lemma Set.Iic.not_isMax_coe {α : Type u} [Preorder α] {j : α}
    {k : Set.Iic j} (hk : ¬ IsMax k) :
    ¬ IsMax k.1 :=
   fun h ↦ hk (fun _ ha' ↦ h ha')

variable {α : Type u} [LinearOrder α] [SuccOrder α] (j : α)

lemma Set.Iic.succ_coe {α : Type u} [LinearOrder α] [SuccOrder α] {j : α}
    (k : Set.Iic j) (hk : ¬ IsMax k) :
    Order.succ k = Order.succ k.1 :=
  coe_succ_of_mem (by
    rw [mem_Iic, Order.succ_le_iff_of_not_isMax (not_isMax_coe hk)]
    by_contra!
    obtain ⟨k, hk⟩ := k
    simp only [not_isMax_iff, Subtype.exists, Subtype.mk_lt_mk, mem_Iic, exists_prop] at hk
    obtain ⟨i, hi⟩ := hk
    have := lt_of_le_of_lt (hi.1.trans this) hi.2
    simp at this)

lemma Set.Iic.isSuccPrelimit_coe {α : Type u} [Preorder α] {j : α}
    {k : Set.Iic j} (hk : Order.IsSuccPrelimit k) :
    Order.IsSuccPrelimit k.1 :=
  fun a ha ↦ hk ⟨a, ha.1.le.trans k.2⟩ ⟨ha.1, fun ⟨_, _⟩ hb' ↦ ha.2 hb'⟩

lemma Set.Iic.isSuccLimit_coe {α : Type u} [Preorder α] {j : α}
    {k : Set.Iic j} (hk : Order.IsSuccLimit k) :
    Order.IsSuccLimit k.1 :=
  ⟨not_isMin_coe hk.1, isSuccPrelimit_coe hk.2⟩

/-- Given an element `j` in a preordered type `α`, and `k : Set.Iic j`,
this is the order isomorphism between `Set.Iio k` and `Set.Iio k.1`. -/
@[simps]
def Set.Iic.iioOrderIso {α : Type u} [Preorder α] {j : α}
    (k : Set.Iic j) :
    Set.Iio k ≃o Set.Iio k.1 where
  toFun := fun ⟨⟨x, _⟩, hx'⟩ ↦ ⟨x, hx'⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨⟨x, hx.le.trans k.2⟩, hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by rfl

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

variable {J : Type w} [Preorder J]

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
@[simps!]
def restrictionLE (F : J ⥤ C) (j : J) : Set.Iic j ⥤ C :=
  Monotone.functor (f := fun k ↦ k.1) (fun _ _ ↦ id) ⋙ F

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

/-- A functor `F : J ⥤ C` is well-order-continuous if for any limit element `m : J`,
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`. -/
class IsWellOrderContinuous (F : J ⥤ C) : Prop where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :
    Nonempty (IsColimit (F.coconeLT m))

/-- If `F : J ⥤ C` is well-order-continuous and `m : J` is a limit element, then
the cocone `F.coconeLT m` is colimit, i.e. `F.obj m` identifies to the colimit
of the `F.obj j` for `j < m`. -/
noncomputable def isColimitOfIsWellOrderContinuous (F : J ⥤ C) [F.IsWellOrderContinuous]
    (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit (F.coconeLT m) := (IsWellOrderContinuous.nonempty_isColimit m hm).some

instance (F : ℕ ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit m hm := by simp at hm

lemma isWellOrderContinuous_of_iso {F G : J ⥤ C} (e : F ≅ G) [F.IsWellOrderContinuous] :
    G.IsWellOrderContinuous where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :=
    ⟨(IsColimit.precomposeHomEquiv (isoWhiskerLeft _ e) _).1
      (IsColimit.ofIsoColimit (F.isColimitOfIsWellOrderContinuous m hm)
        (Cocones.ext (e.app _)))⟩

instance {J : Type w} [Preorder J]
    (F : J ⥤ C) [F.IsWellOrderContinuous] (j : J) :
    (F.restrictionLE j).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨
    IsColimit.ofWhiskerEquivalence (Set.Iic.iioOrderIso m).equivalence.symm
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Iic.isSuccLimit_coe hm))⟩

end Functor

namespace Limits

variable (J : Type w) [Preorder J]

/-- A functor `G : C ⥤ D` satisfies `PreservesWellOrderContinuousOfShape J G`
if for any limit element `j` in the preordered type `J`, the functor `G`
preserves colimits of shape `Set.Iio j`. -/
class PreservesWellOrderContinuousOfShape (G : C ⥤ D) : Prop where
  preservesColimitsOfShape (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G := by infer_instance

variable {J} in
lemma preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G :=
  PreservesWellOrderContinuousOfShape.preservesColimitsOfShape j hj

instance (F : J ⥤ C) (G : C ⥤ D) [F.IsWellOrderContinuous]
    [PreservesWellOrderContinuousOfShape J G] :
    (F ⋙ G).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G j hj
    exact isColimitOfPreserves G (F.isColimitOfIsWellOrderContinuous j hj)⟩

instance {E : Type u''} [Category.{v''} E] (G₁ : C ⥤ D) (G₂ : D ⥤ E)
    [PreservesWellOrderContinuousOfShape J G₁]
    [PreservesWellOrderContinuousOfShape J G₂] :
    PreservesWellOrderContinuousOfShape J (G₁ ⋙ G₂) where
  preservesColimitsOfShape j hj := by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G₁ j hj
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G₂ j hj
    infer_instance

end Limits

namespace MorphismProperty

variable (W : MorphismProperty C)

section

variable (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J]

/-- Given `W : MorphismProperty C` and a well-ordered type `J`, we say
that a morphism in `C` is a transfinite composition of morphisms in `W`
of shape `J` if it is of the form `c.ι.app ⊥ : F.obj ⊥ ⟶ c.pt`
where `c` is a colimit cocone for a well-order-continuous functor
`F : J ⥤ C` such that for any non-maximal `j : J`, the map
`F.map j ⟶ F.map (Order.succ j)` is in `W`. -/
inductive transfiniteCompositionsOfShape [WellFoundedLT J] : MorphismProperty C
  | mk (F : J ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (j : J) (_ : ¬IsMax j), W (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : transfiniteCompositionsOfShape (c.ι.app ⊥)

variable [WellFoundedLT J]

lemma monotone_transfiniteCompositionsOfShape :
    Monotone (transfiniteCompositionsOfShape (C := C) (J := J)) := by
  rintro _ _ h _ _ _ ⟨F, hF, c, hc⟩
  exact ⟨F, fun j hj ↦ h _ (hF j hj), c, hc⟩

instance [W.RespectsIso] : RespectsIso (W.transfiniteCompositionsOfShape J) where
  precomp := by
    rintro X' X Y i (_ : IsIso i) _ ⟨F, hF, c, hc⟩
    let F' := F.copyObj (fun j ↦ if j = ⊥ then X' else F.obj j)
      (fun j ↦ if hj : j = ⊥ then
          eqToIso (by rw [hj]) ≪≫ (asIso i).symm ≪≫ eqToIso (if_pos hj).symm
        else eqToIso (if_neg hj).symm)
    let e : F ≅ F' := F.isoCopyObj _ _
    have := Functor.isWellOrderContinuous_of_iso e
    let c' : Cocone F' := (Cocones.precompose e.inv).obj c
    have : W.transfiniteCompositionsOfShape J (c'.ι.app ⊥) := by
      constructor
      · intro j hj
        exact (arrow_mk_iso_iff _ (((Functor.mapArrowFunctor _ _).mapIso e).app
          (Arrow.mk (homOfLE (Order.le_succ j))))).1 (hF j hj)
      · exact (IsColimit.precomposeInvEquiv e c).2 hc
    exact MorphismProperty.of_eq _ this (if_pos rfl) rfl (by simp [c', e])
  postcomp := by
    rintro _ _ _ i (_ : IsIso i) _ ⟨F, hF, c, hc⟩
    exact ⟨_, hF, { ι := c.ι ≫ (Functor.const _).map i },
      IsColimit.ofIsoColimit hc (Cocones.ext (asIso i))⟩

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
  refine ⟨_, fun ⟨i, hi⟩ hi' ↦ ?_, _, F.isColimitCoconeLE j⟩
  dsimp [Monotone.functor]
  have := Set.Iic.succ_coe _ hi'
  dsimp at this
  have := hF i (by
    simp only [not_isMax_iff, Subtype.exists, Subtype.mk_lt_mk, Set.mem_Iic, exists_prop] at hi'
    obtain ⟨k, hk⟩ := hi'
    exact lt_of_lt_of_le hk.2 hk.1)
  convert this

lemma transfiniteCompositionsOfShape_map_of_preserves (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    {X Y : C} (f : X ⟶ Y) {P : MorphismProperty D}
    [PreservesColimitsOfShape J G]
    (h : (P.inverseImage G).transfiniteCompositionsOfShape J f) :
    P.transfiniteCompositionsOfShape J (G.map f) := by
  obtain ⟨F, hF, c, hc⟩  := h
  exact ⟨F ⋙ G, hF, _, isColimitOfPreserves G hc⟩

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite compositions
of shape `J` if for any well-order-continuous functor `F : J ⥤ C` such that
`F.obj j ⟶ F.obj (Order.succ j)` is in `W`, then `F.obj ⊥ ⟶ c.pt` is in `W`
for any colimit cocone `c : Cocone F`. -/
@[mk_iff]
class IsStableUnderTransfiniteCompositionOfShape : Prop where
  le : W.transfiniteCompositionsOfShape J ≤ W


lemma transfiniteCompositionsOfShape_le [W.IsStableUnderTransfiniteCompositionOfShape J] :
    W.transfiniteCompositionsOfShape J ≤ W :=
  IsStableUnderTransfiniteCompositionOfShape.le

variable {J} in
lemma mem_of_transfinite_composition [W.IsStableUnderTransfiniteCompositionOfShape J]
    {F : J ⥤ C} [F.IsWellOrderContinuous]
    (hF : ∀ (j : J) (_ : ¬IsMax j), W (F.map (homOfLE (Order.le_succ j))))
    {c : Cocone F} (hc : IsColimit c) : W (c.ι.app ⊥) :=
  W.transfiniteCompositionsOfShape_le J _ (by constructor <;> assumption)

end

/-- A class of morphisms `W : MorphismProperty C` is stable under infinite composition
if for any functor `F : ℕ ⥤ C` such that `F.obj n ⟶ F.obj (n + 1)` is in `W` for any `n : ℕ`,
the map `F.obj 0 ⟶ c.pt` is in `W` for any colimit cocone `c : Cocone F`. -/
abbrev IsStableUnderInfiniteComposition : Prop :=
  W.IsStableUnderTransfiniteCompositionOfShape ℕ

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite composition
if it is multiplicative and stable under transfinite composition of any shape
(in a certain universe). -/
class IsStableUnderTransfiniteComposition extends W.IsMultiplicative : Prop where
  isStableUnderTransfiniteCompositionOfShape
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.IsStableUnderTransfiniteCompositionOfShape J

namespace IsStableUnderTransfiniteComposition

attribute [instance] isStableUnderTransfiniteCompositionOfShape

protected instance isomorphisms :
    (isomorphisms C).IsStableUnderTransfiniteComposition where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := ⟨by
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
          (fun i _ ↦ h i.1 i.2) (F.isColimitOfIsWellOrderContinuous j hj) ⟩

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
