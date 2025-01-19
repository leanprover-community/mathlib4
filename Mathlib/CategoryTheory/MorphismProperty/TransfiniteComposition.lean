/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

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

universe w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

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
class IsStableUnderTransfiniteCompositionOfShape : Prop where
  le : W.transfiniteCompositionsOfShape J ≤ W

variable [W.IsStableUnderTransfiniteCompositionOfShape J]

lemma transfiniteCompositionsOfShape_le  :
    W.transfiniteCompositionsOfShape J ≤ W :=
  IsStableUnderTransfiniteCompositionOfShape.le

variable {J} in
lemma mem_of_transfinite_composition {F : J ⥤ C} [F.IsWellOrderContinuous]
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

end IsStableUnderTransfiniteComposition

end MorphismProperty

end CategoryTheory
