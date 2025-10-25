/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Limits.Presentation

/-!
# Objects that are colimits of objects satisfying a certain property

Given a property of objects `P : ObjectProperty C` and a category `J`,
we introduce two properties of objects `P.strictColimitsOfShape J`
and `P.colimitsOfShape J`. The former contains exactly the objects
of the form `colimit F` for any functor `F : J ⥤ C` that has
a colimit and such that `F.obj j` satisfies `P` for any `j`, while
the latter contains all the objects that are isomorphic to
these "chosen" objects `colimit F`.

Under certain circumstances, the type of objects satisfying
`P.strictColimitsOfShape J` is small: the main reason this variant is
introduced is to deduce that the full subcategory of `P.colimitsOfShape J`
is essentially small.

By requiring `P.colimitsOfShape J ≤ P`, we introduce a typeclass
`P.IsClosedUnderColimitsOfShape J`.

We also show that `colimitsOfShape` in a category `C` is related
to `limitsOfShape` in the opposite category `Cᵒᵖ` and vice versa.

## TODO

* refactor `ObjectProperty.ind` by saying that it is the supremum
of `P.colimitsOfShape J` for a filtered category `J`
(generalize also to `κ`-filtered categories?)
* formalize the closure of `P` under finite colimits (which require
iterating over `ℕ`), and more generally the closure under colimits
indexed by a category whose type of arrows has a cardinality
that is bounded by a certain regular cardinal (@joelriou)

-/

universe w v'' v' u'' u' v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category C] (P : ObjectProperty C)
  (J : Type u') [Category.{v'} J]
  {J' : Type u''} [Category.{v''} J']

/-- The property of objects that are *equal* to `colimit F` for some
functor `F : J ⥤ C` where all `F.obj j` satisfy `P`. -/
inductive strictColimitsOfShape : ObjectProperty C
  | colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ j, P (F.obj j)) :
    strictColimitsOfShape (colimit F)

variable {P} in
lemma strictColimitsOfShape_monotone {Q : ObjectProperty C} (h : P ≤ Q) :
    P.strictColimitsOfShape J ≤ Q.strictColimitsOfShape J := by
  rintro _ ⟨F, hF⟩
  exact ⟨F, fun j ↦ h _ (hF j)⟩

/-- A structure expressing that `X : C` is the colimit of a functor
`diag : J ⥤ C` such that `P (diag.obj j)` holds for all `j`. -/
structure ColimitOfShape (X : C) extends ColimitPresentation J X where
  prop_diag_obj (j : J) : P (diag.obj j)

namespace ColimitOfShape

variable {P J}

/-- If `F : J ⥤ C` is a functor that has a colimit and is such that for all `j`,
`F.obj j` satisfies a property `P`, then this structure expresses that `colimit F`
is indeed a colimit of objects satisfying `P`. -/
@[simps toColimitPresentation]
noncomputable def colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ j, P (F.obj j)) :
    P.ColimitOfShape J (colimit F) where
  toColimitPresentation := .colimit F
  prop_diag_obj := hF

/-- If `X` is a colimit indexed by `J` of objects satisfying a property `P`, then
any object that is isomorphic to `X` also is. -/
@[simps toColimitPresentation]
def ofIso {X : C} (h : P.ColimitOfShape J X) {Y : C} (e : X ≅ Y) :
    P.ColimitOfShape J Y where
  toColimitPresentation := .ofIso h.toColimitPresentation e
  prop_diag_obj := h.prop_diag_obj

/-- If `X` is a colimit indexed by `J` of objects satisfying a property `P`,
it is also a colimit indexed by `J` of objects satisfying `Q` if `P ≤ Q`. -/
@[simps toColimitPresentation]
def ofLE {X : C} (h : P.ColimitOfShape J X) {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    Q.ColimitOfShape J X where
  toColimitPresentation := h.toColimitPresentation
  prop_diag_obj j := hPQ _ (h.prop_diag_obj j)

/-- Change the index category for `ObjectProperty.ColimitOfShape`. -/
@[simps toColimitPresentation]
noncomputable def reindex {X : C} (h : P.ColimitOfShape J X) (G : J' ⥤ J) [G.Final] :
    P.ColimitOfShape J' X where
  toColimitPresentation := h.toColimitPresentation.reindex G
  prop_diag_obj _ := h.prop_diag_obj _

end ColimitOfShape

/-- The property of objects that are the point of a colimit cocone for a
functor `F : J ⥤ C` where all objects `F.obj j` satisfy `P`. -/
def colimitsOfShape : ObjectProperty C :=
  fun X ↦ Nonempty (P.ColimitOfShape J X)

variable {P J} in
lemma ColimitOfShape.colimitsOfShape {X : C} (h : P.ColimitOfShape J X) :
    P.colimitsOfShape J X :=
  ⟨h⟩

lemma strictColimitsOfShape_le_colimitsOfShape :
    P.strictColimitsOfShape J ≤ P.colimitsOfShape J := by
  rintro X ⟨F, hF⟩
  exact ⟨.colimit F hF⟩

instance : (P.colimitsOfShape J).IsClosedUnderIsomorphisms where
  of_iso := by rintro _ _ e ⟨h⟩; exact ⟨h.ofIso e⟩

@[simp]
lemma isoClosure_strictColimitsOfShape :
    (P.strictColimitsOfShape J).isoClosure = P.colimitsOfShape J := by
  refine le_antisymm ?_ ?_
  · rw [isoClosure_le_iff]
    apply strictColimitsOfShape_le_colimitsOfShape
  · intro X ⟨h⟩
    have := h.hasColimit
    exact ⟨colimit h.diag, strictColimitsOfShape.colimit h.diag h.prop_diag_obj,
      ⟨h.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

variable {P} in
lemma colimitsOfShape_monotone {Q : ObjectProperty C} (hPQ : P ≤ Q) :
    P.colimitsOfShape J ≤ Q.colimitsOfShape J := by
  intro X ⟨h⟩
  exact ⟨h.ofLE hPQ⟩

@[simp]
lemma colimitsOfShape_isoClosure :
    P.isoClosure.colimitsOfShape J = P.colimitsOfShape J := by
  refine le_antisymm ?_ (colimitsOfShape_monotone _ (P.le_isoClosure))
  intro X ⟨h⟩
  choose obj h₁ h₂ using h.prop_diag_obj
  exact
   ⟨{ toColimitPresentation := h.changeDiag (h.diag.isoCopyObj obj (fun j ↦ (h₂ j).some)).symm
      prop_diag_obj := h₁ }⟩

instance [ObjectProperty.Small.{w} P] [LocallySmall.{w} C] [Small.{w} J] [LocallySmall.{w} J] :
    ObjectProperty.Small.{w} (P.strictColimitsOfShape J) := by
  refine small_of_surjective
    (f := fun (F : { F : J ⥤ P.FullSubcategory // HasColimit (F ⋙ P.ι) }) ↦
      (⟨_, letI := F.2; ⟨F.1 ⋙ P.ι, fun j ↦ (F.1.obj j).2⟩⟩)) ?_
  rintro ⟨_, ⟨F, hF⟩⟩
  exact ⟨⟨P.lift F hF, by assumption⟩, rfl⟩

/-- A property of objects satisfies `P.IsClosedUnderColimitsOfShape J` if it
is stable by colimits of shape `J`. -/
@[mk_iff]
class IsClosedUnderColimitsOfShape (P : ObjectProperty C) (J : Type u') [Category.{v'} J] where
  colimitsOfShape_le (P J) : P.colimitsOfShape J ≤ P

variable {P J} in
lemma IsClosedUnderColimitsOfShape.mk' [P.IsClosedUnderIsomorphisms]
    (h : P.strictColimitsOfShape J ≤ P) :
    P.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    conv_rhs => rw [← P.isoClosure_eq_self]
    rw [← isoClosure_strictColimitsOfShape]
    exact monotone_isoClosure h

export IsClosedUnderColimitsOfShape (colimitsOfShape_le)

section

variable {J} [P.IsClosedUnderColimitsOfShape J]

variable {P} in
lemma ColimitOfShape.prop {X : C} (h : P.ColimitOfShape J X) : P X :=
  P.colimitsOfShape_le J _ ⟨h⟩

lemma prop_of_isColimit {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ (j : J), P (F.obj j)) : P c.pt :=
  P.colimitsOfShape_le J _ ⟨{ diag := _, ι := _, isColimit := hc, prop_diag_obj := hF }⟩

lemma prop_colimit (F : J ⥤ C) [HasColimit F] (hF : ∀ (j : J), P (F.obj j)) :
    P (colimit F) :=
  P.prop_of_isColimit (colimit.isColimit F) hF

end

variable {J} in
lemma colimitsOfShape_le_of_final (G : J ⥤ J') [G.Final] :
    P.colimitsOfShape J' ≤ P.colimitsOfShape J :=
  fun _h ⟨h⟩ ↦ ⟨h.reindex G⟩

variable {J} in
lemma colimitsOfShape_congr (e : J ≌ J') :
    P.colimitsOfShape J = P.colimitsOfShape J' :=
  le_antisymm (P.colimitsOfShape_le_of_final e.inverse)
    (P.colimitsOfShape_le_of_final e.functor)

variable {J} in
lemma isClosedUnderColimitsOfShape_iff_of_equivalence (e : J ≌ J') :
    P.IsClosedUnderColimitsOfShape J ↔
      P.IsClosedUnderColimitsOfShape J' := by
  simp only [isClosedUnderColimitsOfShape_iff, P.colimitsOfShape_congr e]

variable {P J} in
lemma IsClosedUnderColimitsOfShape.of_equivalence (e : J ≌ J')
    [P.IsClosedUnderColimitsOfShape J] :
    P.IsClosedUnderColimitsOfShape J' := by
  rwa [← P.isClosedUnderColimitsOfShape_iff_of_equivalence e]

lemma colimitsOfShape_eq_unop_limitsOfShape :
    P.colimitsOfShape J = (P.op.limitsOfShape Jᵒᵖ).unop := by
  ext X
  constructor
  · rintro ⟨h⟩
    exact ⟨{
      diag := h.diag.op
      π := NatTrans.op h.ι
      isLimit := isLimitOfUnop h.isColimit
      prop_diag_obj _ := h.prop_diag_obj _
    }⟩
  · rintro ⟨h⟩
    exact ⟨{
      diag := h.diag.unop
      ι := NatTrans.unop h.π
      isColimit := isColimitOfOp h.isLimit
      prop_diag_obj _ := h.prop_diag_obj _
    }⟩

lemma limitsOfShape_eq_unop_colimitsOfShape :
    P.limitsOfShape J = (P.op.colimitsOfShape Jᵒᵖ).unop := by
  ext X
  constructor
  · rintro ⟨h⟩
    exact ⟨{
      diag := h.diag.op
      ι := NatTrans.op h.π
      isColimit := isColimitOfUnop h.isLimit
      prop_diag_obj _ := h.prop_diag_obj _
    }⟩
  · rintro ⟨h⟩
    exact ⟨{
      diag := h.diag.unop
      π := NatTrans.unop h.ι
      isLimit := isLimitOfOp h.isColimit
      prop_diag_obj _ := h.prop_diag_obj _
    }⟩

lemma limitsOfShape_op :
    P.op.limitsOfShape J = (P.colimitsOfShape Jᵒᵖ).op := by
  rw [colimitsOfShape_eq_unop_limitsOfShape, op_unop,
    P.op.limitsOfShape_congr (opOpEquivalence J)]

lemma colimitsOfShape_op :
    P.op.colimitsOfShape J = (P.limitsOfShape Jᵒᵖ).op := by
  rw [limitsOfShape_eq_unop_colimitsOfShape, op_unop,
    P.op.colimitsOfShape_congr (opOpEquivalence J)]

lemma isClosedUnderColimitsOfShape_iff_op :
    P.IsClosedUnderColimitsOfShape J ↔
      P.op.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rw [isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff,
    colimitsOfShape_eq_unop_limitsOfShape, ← op_monotone_iff, op_unop]

lemma isClosedUnderLimitsOfShape_iff_op :
    P.IsClosedUnderLimitsOfShape J ↔
      P.op.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rw [isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff,
    limitsOfShape_eq_unop_colimitsOfShape, ← op_monotone_iff, op_unop]

lemma isClosedUnderColimitsOfShape_op_iff_op :
    P.IsClosedUnderColimitsOfShape Jᵒᵖ ↔
      P.op.IsClosedUnderLimitsOfShape J := by
  rw [isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff,
    limitsOfShape_op, op_monotone_iff]

lemma isClosedUnderLimitsOfShape_op_iff_op :
    P.IsClosedUnderLimitsOfShape Jᵒᵖ ↔
      P.op.IsClosedUnderColimitsOfShape J := by
  rw [isClosedUnderColimitsOfShape_iff, isClosedUnderLimitsOfShape_iff,
    colimitsOfShape_op, op_monotone_iff]

instance [P.IsClosedUnderColimitsOfShape J] :
    P.op.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderColimitsOfShape_iff_op]

instance [P.IsClosedUnderLimitsOfShape J] :
    P.op.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderLimitsOfShape_iff_op]

instance [P.IsClosedUnderColimitsOfShape Jᵒᵖ] :
    P.op.IsClosedUnderLimitsOfShape J := by
  rwa [← isClosedUnderColimitsOfShape_op_iff_op]

instance [P.IsClosedUnderLimitsOfShape Jᵒᵖ] :
    P.op.IsClosedUnderColimitsOfShape J := by
  rwa [← isClosedUnderLimitsOfShape_op_iff_op]

section

variable (Q : ObjectProperty Cᵒᵖ)

lemma isClosedUnderColimitsOfShape_iff_unop :
    Q.IsClosedUnderColimitsOfShape J ↔
      Q.unop.IsClosedUnderLimitsOfShape Jᵒᵖ :=
  (Q.unop.isClosedUnderLimitsOfShape_op_iff_op J).symm

lemma isClosedUnderLimitsOfShape_iff_unop :
    Q.IsClosedUnderLimitsOfShape J ↔
      Q.unop.IsClosedUnderColimitsOfShape Jᵒᵖ :=
  (Q.unop.isClosedUnderColimitsOfShape_op_iff_op J).symm

lemma isClosedUnderColimitsOfShape_op_iff_unop :
    Q.IsClosedUnderColimitsOfShape Jᵒᵖ ↔
      Q.unop.IsClosedUnderLimitsOfShape J :=
  (Q.unop.isClosedUnderLimitsOfShape_iff_op J).symm

lemma isClosedUnderLimitsOfShape_op_iff_unop :
    Q.IsClosedUnderLimitsOfShape Jᵒᵖ ↔
      Q.unop.IsClosedUnderColimitsOfShape J :=
  (Q.unop.isClosedUnderColimitsOfShape_iff_op J).symm

instance [Q.IsClosedUnderColimitsOfShape J] :
    Q.unop.IsClosedUnderLimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderColimitsOfShape_iff_unop]

instance [Q.IsClosedUnderLimitsOfShape J] :
    Q.unop.IsClosedUnderColimitsOfShape Jᵒᵖ := by
  rwa [← isClosedUnderLimitsOfShape_iff_unop]

instance [Q.IsClosedUnderColimitsOfShape Jᵒᵖ] :
    Q.unop.IsClosedUnderLimitsOfShape J := by
  rwa [← isClosedUnderColimitsOfShape_op_iff_unop]

instance [Q.IsClosedUnderLimitsOfShape Jᵒᵖ] :
    Q.unop.IsClosedUnderColimitsOfShape J := by
  rwa [← isClosedUnderLimitsOfShape_op_iff_unop]

end

instance [P.IsClosedUnderColimitsOfShape WalkingParallelPair] :
    P.IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    let c : Cofork (h.r ≫ h.i) (𝟙 Y) := Cofork.ofπ h.r (by simp)
    have hc : IsColimit c :=
      Cofork.IsColimit.mk _ (fun s ↦ h.i ≫ s.π)
        (fun s ↦ by simpa using s.condition)
        (fun s m hm ↦ by dsimp [c] at hm; simp [← hm])

    exact P.prop_of_isColimit hc (by rintro (_ | _) <;> exact hY)

end ObjectProperty

namespace Limits

@[deprecated (since := "2025-09-22")] alias ClosedUnderColimitsOfShape :=
  ObjectProperty.IsClosedUnderColimitsOfShape
@[deprecated (since := "2025-09-22")] alias closedUnderColimitsOfShape_of_colimit :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk'
@[deprecated (since := "2025-09-22")] alias ClosedUnderColimitsOfShape.colimit :=
  ObjectProperty.prop_colimit

end CategoryTheory.Limits
