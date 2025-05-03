/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Opposites of left/right Kan extensions

-/

namespace CategoryTheory

open Limits Opposite

variable {C C' D D' H H' : Type*} [Category C] [Category D] [Category H] [Category H']
  [Category D'] [Category C']

namespace Functor

section

variable {L : C ⥤ D} {F : C ⥤ H}

@[simps!]
protected def RightExtension.op (E : RightExtension L F) : LeftExtension L.op F.op :=
  LeftExtension.mk (F' := E.left.op) (NatTrans.op E.hom)

@[simps!]
protected def RightExtension.unop (E : RightExtension L.op F.op) : LeftExtension L F :=
  LeftExtension.mk (F' := E.left.unop) (NatTrans.unop E.hom)

@[simps!]
protected def LeftExtension.op (E : LeftExtension L F) : RightExtension L.op F.op :=
  RightExtension.mk (F' := E.right.op) (NatTrans.op E.hom)

@[simps!]
protected def LeftExtension.unop (E : LeftExtension L.op F.op) : RightExtension L F :=
  RightExtension.mk (F' := E.right.unop) (NatTrans.unop E.hom)

variable (L F)

set_option maxHeartbeats 400000 in
-- this is slow
@[simps]
def rightExtensionOpEquivalence :
    (RightExtension L F)ᵒᵖ ≌ LeftExtension L.op F.op where
  functor :=
    { obj E := E.unop.op
      map f := StructuredArrow.homMk (NatTrans.op f.unop.left)
        (congr_arg NatTrans.op (CostructuredArrow.w f.unop)) }
  inverse :=
    { obj E := op (E.unop)
      map f := (CostructuredArrow.homMk (NatTrans.unop f.right)
        (congr_arg NatTrans.unop (StructuredArrow.w f))).op }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option maxHeartbeats 400000 in
-- this is slow
@[simps]
def leftExtensionOpEquivalence :
    (LeftExtension L F)ᵒᵖ ≌ RightExtension L.op F.op where
  functor :=
    { obj E := E.unop.op
      map f := CostructuredArrow.homMk (NatTrans.op f.unop.right)
        (congr_arg NatTrans.op (StructuredArrow.w f.unop)) }
  inverse :=
    { obj E := op (E.unop)
      map f := (StructuredArrow.homMk (NatTrans.unop f.left)
        (congr_arg NatTrans.unop (CostructuredArrow.w f))).op }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

variable {L F}

namespace RightExtension.IsUniversal

protected noncomputable def op {E : RightExtension L F} (h : E.IsUniversal) :
    E.op.IsUniversal :=
  (initialOpOfTerminal h).isInitialObj
    ((rightExtensionOpEquivalence L F).functor)

protected noncomputable def unop {E : RightExtension L.op F.op} (h : E.IsUniversal) :
    E.unop.IsUniversal :=
  initialUnopOfTerminal
    (h.isTerminalObj (leftExtensionOpEquivalence L F).inverse)

end RightExtension.IsUniversal

namespace LeftExtension.IsUniversal

noncomputable def op {E : LeftExtension L F} (h : E.IsUniversal) :
    E.op.IsUniversal :=
  (terminalOpOfInitial h).isTerminalObj
    ((leftExtensionOpEquivalence L F).functor)

noncomputable def unop {E : LeftExtension L.op F.op} (h : E.IsUniversal) :
    E.unop.IsUniversal :=
  terminalUnopOfInitial
    (h.isInitialObj (rightExtensionOpEquivalence L F).inverse)

end LeftExtension.IsUniversal

end

variable  {F' : D ⥤ H} {L : C ⥤ D} {F : C ⥤ H}

lemma isRightKanExtension_iff_op (α : L ⋙ F' ⟶ F) :
    F'.IsRightKanExtension α ↔
      F'.op.IsLeftKanExtension (F := F.op) (L := L.op) (NatTrans.op α) :=
  ⟨fun ⟨⟨(h)⟩⟩ ↦ ⟨⟨RightExtension.IsUniversal.op h⟩⟩,
    fun ⟨⟨(h)⟩⟩ ↦ ⟨⟨LeftExtension.IsUniversal.unop h⟩⟩⟩

lemma isLeftKanExtension_iff_op (α : F ⟶ L ⋙ F') :
    F'.IsLeftKanExtension α ↔
      F'.op.IsRightKanExtension (F := F.op) (L := L.op) (NatTrans.op α) :=
  ⟨fun ⟨⟨(h)⟩⟩ ↦ ⟨⟨LeftExtension.IsUniversal.op h⟩⟩,
    fun ⟨⟨(h)⟩⟩ ↦ ⟨⟨RightExtension.IsUniversal.unop h⟩⟩⟩

instance (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α] :
    F'.op.IsLeftKanExtension (F := F.op) (L := L.op) (NatTrans.op α) := by
  rwa [← isRightKanExtension_iff_op]

instance (α : F ⟶ L ⋙ F') [F'.IsLeftKanExtension α] :
    F'.op.IsRightKanExtension (F := F.op) (L := L.op) (NatTrans.op α) := by
  rwa [← isLeftKanExtension_iff_op]

end Functor

end CategoryTheory
