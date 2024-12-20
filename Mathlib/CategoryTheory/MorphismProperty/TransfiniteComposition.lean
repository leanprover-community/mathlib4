/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.Limit
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
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
such that `F.obj i ⟶ F.obj (Order.succ i)` belongs to `W`, we can
conclude that `c.ι.app ⊥ : F.obj ⊥ ⟶ c.pt` belongs to `W`.

In particular, if `J := ℕ`, we define `W.IsStableUnderInfiniteComposition`,
which means that if `F : ℕ ⥤ C` is such that `F.obj n ⟶ F.obj (n + 1)`
belongs to `W`, then `F.obj 0 ⟶ c.pt` belongs to `W`
for any colimit cocone `c : Cocone F`.

Finally, we define the class `W.IsStableUnderTransfiniteComposition`
which says that `W.IsStableUnderTransfiniteCompositionOfShape J`
holds for any well ordered type `J` in a certain universe `u`.
(We also require that `W` is multiplicative.)

-/

universe u

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

lemma Set.Iic.not_isMin_coe {α : Type u} [PartialOrder α] [SuccOrder α] {j : α}
    {k : Set.Iic j} (hk : ¬ IsMin k) :
    ¬ IsMin k.1 :=
   fun h ↦ hk (fun _ ha' ↦ h ha')

lemma Set.Iic.isSuccPrelimit_coe {α : Type u} [PartialOrder α] [SuccOrder α] {j : α}
    {k : Set.Iic j} (hk : Order.IsSuccPrelimit k) :
    Order.IsSuccPrelimit k.1 :=
  fun a ha ↦ hk ⟨a, ha.1.le.trans k.2⟩ ⟨ha.1, fun ⟨_, _⟩ hb' ↦ ha.2 hb'⟩

lemma Set.Iic.isSuccLimit_coe {α : Type u} [PartialOrder α] [SuccOrder α] {j : α}
    {k : Set.Iic j} (hk : Order.IsSuccLimit k) :
    Order.IsSuccLimit k.1 :=
  ⟨not_isMin_coe hk.1, isSuccPrelimit_coe hk.2⟩

@[simps]
def Set.Iic.iioOrderIso {α : Type u} [PartialOrder α] [SuccOrder α] {j : α}
    (k : Set.Iic j) :
    Set.Iio k ≃o Set.Iio k.1 where
  toFun := fun ⟨⟨x, _⟩, hx'⟩ ↦ ⟨x, hx'⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨⟨x, hx.le.trans k.2⟩, hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by rfl


namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type*} [Category C] {J : Type u} [Preorder J]

lemma map_comp_eqToHom_eq_map_of_preorder (F : J ⥤ C)
    {a b c : J} (f : a ⟶ b) (g : a ⟶ c) (h : b = c) :
    F.map f ≫ eqToHom (by rw [h]) = F.map g := by
  subst h
  simp only [eqToHom_refl, comp_id]
  congr
  apply Subsingleton.elim

/-- Given a functor `F : J ⥤ C` and `m : J`, this is the cocone with point `F.obj m`
for the restriction of `F` to `Set.Iio m`. -/
@[simps]
def coconeLT (F : J ⥤ C) (m : J) :
    Cocone ((OrderHom.Subtype.val (· ∈ Set.Iio m)).monotone.functor ⋙ F) where
  pt := F.obj m
  ι :=
    { app := fun ⟨i, hi⟩ ↦ F.map (homOfLE hi.le)
      naturality := fun ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ f ↦ by
        dsimp
        rw [← F.map_comp, comp_id]
        rfl }

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

@[simps!]
def restrictionLE (F : J ⥤ C) (j : J) : Set.Iic j ⥤ C :=
  Monotone.functor (f := fun k ↦ k.1) (fun _ _ ↦ id) ⋙ F

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

def isColimitCoconeLE (F : J ⥤ C) (j : J) :
    IsColimit (F.coconeLE j) where
  desc s := s.ι.app ⟨j, by simp⟩
  fac s k := by
    simpa only [Functor.const_obj_obj, Functor.const_obj_map, comp_id]
      using s.ι.naturality (homOfLE k.2 : k ⟶ ⟨j, by simp⟩)
  uniq s m hm := by simp [← hm]

instance {J : Type u} [PartialOrder J] [SuccOrder J] (F : J ⥤ C) [F.IsWellOrderContinuous] (j : J) :
    (F.restrictionLE j).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨
    IsColimit.ofWhiskerEquivalence (Set.Iic.iioOrderIso m).equivalence.symm
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Iic.isSuccLimit_coe hm))⟩

end Functor

namespace MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C)

lemma of_eq {X Y : C} {f : X ⟶ Y} (hf : W f) {X' Y' : C} (f' : X' ⟶ Y')
    (hX : X = X') (hY : Y = Y') (hf' : f' = eqToHom hX.symm ≫ f ≫ eqToHom hY) :
    W f' := by
  subst hX hY
  obtain rfl : f' = f := by simpa using hf'
  exact hf

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite composition
of shape `J` if for any well-order-continuous functor `F : J ⥤ C` such that
`F.obj i ⟶ F.obj (Order.succ i)` is in `W`, then `F.obj ⊥ ⟶ c.pt` is in `W`
for any colimit cocone `c : Cocone F`. -/
class IsStableUnderTransfiniteCompositionOfShape
    (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] : Prop where
  mem (F : J ⥤ C) [F.IsWellOrderContinuous]
    (hF : ∀ (j : J) (_ : ¬IsMax j), W (F.map (homOfLE (Order.le_succ j))))
    (c : Cocone F) (hc : IsColimit c) : W (c.ι.app ⊥)

/-- A class of morphisms `W : MorphismProperty C` is stable under infinite composition
if for any functor `F : ℕ ⥤ C` such that `F.obj n ⟶ F.obj (n + 1)` is in `W` for any `n : ℕ`,
the map `F.obj 0 ⟶ c.pt` is in `W` for any colimit cocone `c : Cocone F`. -/
abbrev IsStableUnderInfiniteComposition : Prop :=
  W.IsStableUnderTransfiniteCompositionOfShape ℕ

lemma mem_of_transfinite_composition
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    [W.IsStableUnderTransfiniteCompositionOfShape J]
    {F : J ⥤ C} [F.IsWellOrderContinuous]
    (hF : ∀ (j : J) (_ : ¬IsMax j), W (F.map (homOfLE (Order.le_succ j))))
    {c : Cocone F} (hc : IsColimit c) : W (c.ι.app ⊥) :=
  IsStableUnderTransfiniteCompositionOfShape.mem F hF c hc

lemma mem_map_of_transfinite_composition
    {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    {F : J ⥤ C} [F.IsWellOrderContinuous]
    (hF : ∀ (j : J) (_ : ¬IsMax j), W (F.map (homOfLE (Order.le_succ j))))
    (j : J) [W.IsStableUnderTransfiniteCompositionOfShape (Set.Iic j)] :
    W (F.map (homOfLE (bot_le : ⊥ ≤ j))) := by
  refine W.mem_of_transfinite_composition (fun ⟨k, hk⟩ hk' ↦ ?_)
    (F.isColimitCoconeLE j)
  refine W.of_eq (hF k (fun h ↦ hk' (fun ⟨a, ha⟩ ha' ↦ h ha'))) _ rfl ?_ ?_
  · dsimp
    simp only [Functor.comp_obj, Monotone.functor_obj, Set.Iic.succ_eq _ hk']
  · dsimp
    rw [id_comp]
    exact (Functor.map_comp_eqToHom_eq_map_of_preorder _ _ _ (Set.Iic.succ_eq _ hk').symm).symm

/-- A class of morphisms `W : MorphismProperty C` is stable under transfinite composition
if it is multiplicative and stable under transfinite composition of any shape
(in a certain universe). -/
class IsStableUnderTransfiniteComposition extends W.IsMultiplicative : Prop where
  isStableUnderTransfiniteCompositionOfShape
    (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    W.IsStableUnderTransfiniteCompositionOfShape J

attribute [instance] IsStableUnderTransfiniteComposition.isStableUnderTransfiniteCompositionOfShape

end MorphismProperty

end CategoryTheory
