/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.SuccPred.Limit
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Category.Preorder

/-
# Continuity of functors from well ordered types

Let `F : J ⥤ C` be functor from a well ordered type `J`.
We introduce the typeclass `F.IsWellOrderContinuous`
to say that if `m` is a limit element, then `F.obj m`
is the colimit of the `F.obj j` for `j < m`.

## TODO
* use the API for initial segments in order to generalize some
definitions in this file
* given a morphism `f` in `C`, introduce a structure
`TransfiniteCompositionOfShape J f` which contains the data
of a continuous functor `F : J ⥤ C` and an identification
of `f` to the map from `F.obj ⊥` to the colimit of `F`
* redefine `MorphismProperty.transfiniteCompositionsOfShape`
in terms of this structure `TransfiniteCompositionOfShape`

-/

universe w v u

namespace CategoryTheory.Functor

open Category Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Preorder J]

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

end CategoryTheory.Functor
