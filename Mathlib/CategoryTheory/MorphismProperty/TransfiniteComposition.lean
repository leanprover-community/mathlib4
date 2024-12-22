/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.LatticeIntervals
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.MorphismProperty.Composition

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

universe w w' v v' u u'

lemma Subtype.monotone_val {α : Type u} [Preorder α] (p : α → Prop) :
    Monotone (Subtype.val : Subtype p → _) := fun _ _ h ↦ h

lemma Set.monotone_coe {α : Type u} [Preorder α] (S : Set α) :
    Monotone (fun (x : S) ↦ x.1) := by
  apply Subtype.monotone_val

lemma Set.not_isMin_coe {α : Type u} [Preorder α] {S : Set α} (k : S)
    (hk : ¬ IsMin k) : ¬ IsMin k.1 := by
  simp only [not_isMin_iff, Subtype.exists] at hk ⊢
  obtain ⟨a, _, ha⟩ := hk
  exact ⟨a, ha⟩

lemma Set.not_isMax_coe {α : Type u} [Preorder α] {S : Set α} (k : S)
    (hk : ¬ IsMax k) : ¬ IsMax k.1 := by
  simp only [not_isMax_iff, Subtype.exists] at hk ⊢
  obtain ⟨a, _, ha⟩ := hk
  exact ⟨a, ha⟩

lemma Set.Iic.not_isMin_coe {α : Type u} [Preorder α] {j : α}
    {k : Set.Iic j} (hk : ¬ IsMin k) :
    ¬ IsMin k.1 :=
   fun h ↦ hk (fun _ ha' ↦ h ha')

lemma Set.Iic.isSuccPrelimit_coe {α : Type u} [Preorder α] {j : α}
    {k : Set.Iic j} (hk : Order.IsSuccPrelimit k) :
    Order.IsSuccPrelimit k.1 :=
  fun a ha ↦ hk ⟨a, ha.1.le.trans k.2⟩ ⟨ha.1, fun ⟨_, _⟩ hb' ↦ ha.2 hb'⟩

lemma Set.Iic.isSuccLimit_coe {α : Type u} [Preorder α] {j : α}
    {k : Set.Iic j} (hk : Order.IsSuccLimit k) :
    Order.IsSuccLimit k.1 :=
  ⟨not_isMin_coe hk.1, isSuccPrelimit_coe hk.2⟩

lemma Set.Ici.not_isMin_coe {α : Type u} [Preorder α] {j : α}
    {k : Set.Ici j} (hk : ¬ IsMin k) :
    ¬ IsMin k.1 :=
   fun h ↦ hk (fun _ ha' ↦ h ha')

lemma Set.Ici.isSuccLimit_coe {α : Type u} [LinearOrder α] {j : α}
    {k : Set.Ici j} (hk : Order.IsSuccLimit k) :
    Order.IsSuccLimit k.1 :=
  ⟨not_isMin_coe hk.1, fun a ⟨h₁, h₂⟩ ↦ by
    refine hk.2 ⟨a, ?_⟩ ⟨h₁, fun b hb' ↦ h₂ hb'⟩
    · simp only [mem_Ici]
      by_contra!
      apply hk.1
      obtain rfl : k = ⟨j, by simp⟩ :=
        le_antisymm (by simpa using h₂ this) k.2
      rw [isMin_iff_eq_bot]
      rfl⟩

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

instance (α : Type u) [Preorder α] [OrderBot α] (a : α) : OrderBot (Set.Iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le _ := bot_le

lemma Set.Iic.succ_eq {α : Type u} [PartialOrder α] [SuccOrder α] {j : α}
    (k : Set.Iic j) (hk : ¬ IsMax k) :
    Order.succ k = Order.succ k.1 :=
  coe_succ_of_mem (by
    obtain ⟨k, hk'⟩ := k
    simp only [mem_Iic] at hk' ⊢
    rw [Order.succ_le_iff_of_not_isMax
      (fun hk' ↦ hk (fun ⟨a, ha⟩ hka ↦ by exact hk' hka))]
    obtain _ | rfl := hk'.lt_or_eq
    · assumption
    · exfalso
      exact hk (fun x _ ↦ x.2))

lemma Set.Ici.succ_eq {α : Type u} [PartialOrder α] [SuccOrder α] {j : α}
    (k : Set.Ici j) :
    Order.succ k = Order.succ k.1 :=
  coe_succ_of_mem (k.2.trans (Order.le_succ k.1))

def Set.Icc.orderIso {α : Type u} [Preorder α] {j j' : α} (h : j ≤ j') :
    Set.Icc j j' ≃o Set.Iic (⟨j', h⟩ : Set.Ici j) where
  toFun := fun ⟨a, h⟩ ↦ ⟨⟨a, h.1⟩, h.2⟩
  invFun := fun ⟨⟨a, h₁⟩, h₂⟩ ↦ ⟨a, h₁, h₂⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

section

variable {α : Type u} [Preorder α]

def Set.coeIci {S : Set α} (m : S) (x : Set.Iio m) : Set.Iio m.1 :=
  ⟨_, x.2⟩

lemma Set.monotone_coeIci {S : Set α} (m : S) :
    Monotone (Set.coeIci m) := fun _ _ h ↦ h

end

section

variable {α β : Type*} [Preorder α] [Preorder β] (e : α ≃o β)

lemma OrderIso.map_isSuccPrelimit (i : α) (hi : Order.IsSuccPrelimit i) :
    Order.IsSuccPrelimit (e i) := by
  intro b
  obtain ⟨j, rfl⟩ := e.surjective b
  simp only [apply_covBy_apply_iff]
  apply hi

@[simp]
lemma OrderIso.isSuccPrelimit_apply (i : α) :
    Order.IsSuccPrelimit (e i) ↔ Order.IsSuccPrelimit i :=
  ⟨fun h ↦ by simpa using e.symm.map_isSuccPrelimit _ h,
    fun h ↦ e.map_isSuccPrelimit i h⟩

lemma OrderIso.map_isSuccLimit (i : α) (hi : Order.IsSuccLimit i) :
    Order.IsSuccLimit (e i) := by
  simpa only [Order.IsSuccLimit, isMin_apply, isSuccPrelimit_apply] using hi

def OrderIso.setIio (j : α) :
    Set.Iio j ≃o Set.Iio (e j) where
  toFun := fun ⟨k, hk⟩ ↦ ⟨e k, by simpa using hk⟩
  invFun := fun ⟨k, hk⟩ ↦ ⟨e.symm k, by simpa using e.symm.strictMono hk⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_rel_iff' {k l} := e.map_rel_iff (a := k.1) (b := l.1)

end

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

/-- The colimit of `F.cocone j` is `F.obj j`. -/
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

instance [PartialOrder J] [SuccOrder J] (F : J ⥤ C) [F.IsWellOrderContinuous] (j : J) :
    (F.restrictionLE j).IsWellOrderContinuous where
  nonempty_isColimit m hm :=
    ⟨IsColimit.ofWhiskerEquivalence (Set.Iic.iioOrderIso m).equivalence.symm
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Iic.isSuccLimit_coe hm))⟩

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

variable {J}

instance (F : J ⥤ C) (G : C ⥤ D) [F.IsWellOrderContinuous]
    [PreservesWellOrderContinuousOfShape J G] :
    (F ⋙ G).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    have := preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape G j hj
    exact isColimitOfPreserves G (F.isColimitOfIsWellOrderContinuous j hj)⟩

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

lemma monotone_transfiniteCompositionsOfShape {W₁ W₂ : MorphismProperty C} (h : W₁ ≤ W₂)
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W₁.transfiniteCompositionsOfShape J ≤ W₂.transfiniteCompositionsOfShape J := by
  rintro _ _ _ ⟨F, hF, c, hc⟩
  exact ⟨F, fun j hj ↦ h _ (hF j hj), c, hc⟩

variable [WellFoundedLT J]

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

section

variable {J} {J' : Type w'} [LinearOrder J'] [SuccOrder J']
  [OrderBot J'] [WellFoundedLT J']

instance (e : J ≃o J') (F : J' ⥤ C) [F.IsWellOrderContinuous] :
    (e.equivalence.functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨(F.isColimitOfIsWellOrderContinuous (e j)
    (e.map_isSuccLimit j hj)).whiskerEquivalence (e.setIio j).equivalence⟩

instance (e : J ≃o J') (F : J ⥤ C) [F.IsWellOrderContinuous] :
    (e.equivalence.inverse ⋙ F).IsWellOrderContinuous :=
  inferInstanceAs (e.symm.equivalence.functor ⋙ F).IsWellOrderContinuous

variable [W.RespectsIso]

lemma transfiniteCompositionsOfShape_le_of_orderIso (e : J ≃o J') :
    W.transfiniteCompositionsOfShape J ≤ W.transfiniteCompositionsOfShape J' := by
  rintro _ _ _ ⟨F, hF, c, hc⟩
  let F' : J' ⥤ C := e.equivalence.inverse ⋙ F
  let c' := c.whisker e.equivalence.inverse
  have hc' : IsColimit c' := IsColimit.whiskerEquivalence hc e.symm.equivalence
  have : W.transfiniteCompositionsOfShape J' (c'.ι.app ⊥) := by
    refine ⟨_, fun j hj ↦ ?_, _, hc'⟩
    refine (W.arrow_mk_iso_iff ?_).1
      (hF (e.symm j) (by simpa only [← OrderIso.isMax_apply e.symm] using hj))
    have e : Arrow.mk (homOfLE (Order.le_succ (e.symm j))) ≅
      (e.equivalence.inverse.mapArrow.obj
        (Arrow.mk (homOfLE (Order.le_succ j)))) :=
          Arrow.isoMk (Iso.refl _) (eqToIso (e.symm.map_succ j).symm)
    exact F.mapArrow.mapIso e
  have e : Arrow.mk (c'.ι.app ⊥) ≅ Arrow.mk (c.ι.app ⊥) :=
    Arrow.isoMk (eqToIso (by dsimp; rw [e.symm.map_bot])) (Iso.refl _) (by
      dsimp [c']
      rw [← c.w (eqToHom e.symm.map_bot), eqToHom_map, assoc, comp_id])
  exact ((W.transfiniteCompositionsOfShape J').arrow_iso_iff e).1 this

lemma transfiniteCompositionsOfShape_eq_of_orderIso (e : J ≃o J') :
    W.transfiniteCompositionsOfShape J = W.transfiniteCompositionsOfShape J' :=
  le_antisymm (W.transfiniteCompositionsOfShape_le_of_orderIso e)
    (W.transfiniteCompositionsOfShape_le_of_orderIso e.symm)

lemma isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso (e : J ≃o J') :
    W.IsStableUnderTransfiniteCompositionOfShape J ↔
      W.IsStableUnderTransfiniteCompositionOfShape J' := by
  simp only [isStableUnderTransfiniteCompositionOfShape_iff,
    W.transfiniteCompositionsOfShape_eq_of_orderIso e]

end

variable [W.IsStableUnderTransfiniteCompositionOfShape J]

lemma mem_map_from_bot_of_transfinite_composition
    {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {F : J ⥤ C} [F.IsWellOrderContinuous]
    (hF : ∀ (j : J) (_ : ¬IsMax j), W (F.map (homOfLE (Order.le_succ j))))
    (j : J) [W.IsStableUnderTransfiniteCompositionOfShape (Set.Iic j)] :
    W (F.map (homOfLE (bot_le : ⊥ ≤ j))) := by
  refine W.mem_of_transfinite_composition (fun ⟨k, hk⟩ hk' ↦ ?_)
    (F.isColimitCoconeLE j)
  rw [← W.inverseImage_iff]
  exact (W.inverseImage _).of_eq (hF k (fun h ↦ hk' (fun ⟨a, ha⟩ ha' ↦ h ha'))) rfl
    ((Set.Iic.succ_eq _ hk').symm) rfl

instance (F : J ⥤ C) (j : J) [F.IsWellOrderContinuous] :
    ((Set.Ici j).monotone_coe.functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    have : (Set.monotone_coeIci m).functor.Final := by
      obtain ⟨m, hm'⟩ := m
      apply Functor.final_of_exists_of_isFiltered
      · rintro ⟨a, ha⟩
        have h₁ : j < m := by
          by_contra!
          obtain rfl : m = j := le_antisymm this hm'
          have := hm.1
          simp only [isMin_iff_eq_bot] at this
          exact this rfl
        have h₂ := hm.2 ⟨max a j, le_max_right a j⟩
        rw [not_covBy_iff (by exact sup_lt_iff.2 ⟨ha, h₁⟩)] at h₂
        obtain ⟨⟨b, hb₁⟩, hb₂, hb₃⟩ := h₂
        exact ⟨⟨⟨b, hb₁⟩, hb₃⟩, ⟨homOfLE ((le_max_left a j).trans hb₂.le)⟩⟩
      · rintro a b f g
        exact ⟨b, 𝟙 _, rfl⟩
    exact (Functor.Final.isColimitWhiskerEquiv (F := (Set.monotone_coeIci m).functor) _).2
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Ici.isSuccLimit_coe hm))⟩

lemma mem_map_of_transfinite_composition [W.RespectsIso]
    {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {F : J ⥤ C} [F.IsWellOrderContinuous]
    (hF : ∀ (j : J) (_ : ¬IsMax j), W (F.map (homOfLE (Order.le_succ j))))
    {j j' : J} (φ : j ⟶ j')
    [letI : Fact (j ≤ j') := ⟨leOfHom φ⟩;
      W.IsStableUnderTransfiniteCompositionOfShape (Set.Icc j j')] :
    W (F.map φ) := by
  have : Fact (j ≤ j') := ⟨leOfHom φ⟩
  have hF' (j : J) (hj : ¬IsMax j) (k : J) (hk : k = Order.succ j) :
      W (F.map (homOfLE (by rw [hk]; exact Order.le_succ j) : j ⟶ k)) := by
    subst hk
    exact hF j hj
  let j'' : Set.Ici j := ⟨j', leOfHom φ⟩
  have : W.IsStableUnderTransfiniteCompositionOfShape (Set.Iic j'') := by
    rwa [← W.isStableUnderTransfiniteCompositionOfShape_iff_of_orderIso
      (Set.Icc.orderIso (leOfHom φ))]
  exact mem_map_from_bot_of_transfinite_composition W
    (F := (Set.Ici j).monotone_coe.functor ⋙ F)
    (fun k hk ↦ hF' k (Set.not_isMax_coe k hk) _ (Set.Ici.succ_eq k)) j''

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

end IsStableUnderTransfiniteComposition

end MorphismProperty

end CategoryTheory
