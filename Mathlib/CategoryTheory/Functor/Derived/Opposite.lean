/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Opposite
import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Left and right derived functors and opposite categories
-/

namespace CategoryTheory

namespace Functor

variable {C D H : Type*} [Category C] [Category D] [Category H]


section

variable
  (F' : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : L ⋙ F' ⟶ F) (β : F ⟶ L ⋙ F')
  (W : MorphismProperty C) [L.IsLocalization W]

lemma isLeftDerivedFunctor_iff_op :
    F'.IsLeftDerivedFunctor α W ↔
      F'.op.IsRightDerivedFunctor (F := F.op) (L := L.op) (NatTrans.op α) W.op := by
  rw [isLeftDerivedFunctor_iff, isRightDerivedFunctor_iff,
    isRightKanExtension_iff_op]

lemma isRightDerivedFunctor_iff_op :
    F'.IsRightDerivedFunctor β W ↔
      F'.op.IsLeftDerivedFunctor (F := F.op) (L := L.op) (NatTrans.op β) W.op := by
  rw [isLeftDerivedFunctor_iff, isRightDerivedFunctor_iff,
    isLeftKanExtension_iff_op]

instance [F'.IsLeftDerivedFunctor α W] :
    F'.op.IsRightDerivedFunctor (F := F.op) (L := L.op) (NatTrans.op α) W.op := by
  rwa [← isLeftDerivedFunctor_iff_op]

instance [F'.IsRightDerivedFunctor β W] :
    F'.op.IsLeftDerivedFunctor (F := F.op) (L := L.op) (NatTrans.op β) W.op := by
  rwa [← isRightDerivedFunctor_iff_op]

end

variable (F : C ⥤ D) (W : MorphismProperty C)

lemma hasLeftDerivedFunctor_iff_op :
    F.HasLeftDerivedFunctor W ↔ F.op.HasRightDerivedFunctor W.op := by
  constructor
  · intro h
    exact HasRightDerivedFunctor.mk' (L := W.Q.op)
      (RF := (F.totalLeftDerived W.Q W).op)
      (α := NatTrans.op (F.totalLeftDerivedCounit W.Q W))
  · intro h
    have : (F.op.totalRightDerived W.Q.op W.op).unop.IsLeftDerivedFunctor
      (NatTrans.unop (F.op.totalRightDerivedUnit W.Q.op W.op)) W := by
      rw [isLeftDerivedFunctor_iff_op]
      exact inferInstanceAs ((F.op.totalRightDerived W.Q.op W.op).IsRightDerivedFunctor
        (F.op.totalRightDerivedUnit W.Q.op W.op) W.op)
    exact HasLeftDerivedFunctor.mk' (L := W.Q)
      (LF := (F.op.totalRightDerived W.Q.op W.op).unop)
      (α := NatTrans.unop (F.op.totalRightDerivedUnit W.Q.op W.op))

lemma hasRightDerivedFunctor_iff_op :
    F.HasRightDerivedFunctor W ↔ F.op.HasLeftDerivedFunctor W.op := by
  constructor
  · intro h
    exact HasLeftDerivedFunctor.mk' (L := W.Q.op)
      (LF := (F.totalRightDerived W.Q W).op)
      (α := NatTrans.op (F.totalRightDerivedUnit W.Q W))
  · intro h
    have : (F.op.totalLeftDerived W.Q.op W.op).unop.IsRightDerivedFunctor
      (NatTrans.unop (F.op.totalLeftDerivedCounit W.Q.op W.op)) W := by
      rw [isRightDerivedFunctor_iff_op]
      exact inferInstanceAs ((F.op.totalLeftDerived W.Q.op W.op).IsLeftDerivedFunctor
        (F.op.totalLeftDerivedCounit W.Q.op W.op) W.op)
    exact HasRightDerivedFunctor.mk' (L := W.Q)
      (RF := (F.op.totalLeftDerived W.Q.op W.op).unop)
      (α := NatTrans.unop (F.op.totalLeftDerivedCounit W.Q.op W.op))

end Functor

end CategoryTheory
