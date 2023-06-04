import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Limits

universe v v' u u'

namespace CategoryTheory
open CategoryTheory.Limits

noncomputable def colimit_op {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (α : C ⥤ D) [HasColimit α] [HasLimit α.op] : limit α.op ≅ Opposite.op (colimit α) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit α.op) (isLimitCoconeOp _ (colimit.isColimit α))

variable {C : Type u} [Category.{v} C]
  {I : Type v} [SmallCategory I] {J : Type v} [SmallCategory J]
  (α : I ⥤ C) (β : J ⥤ C)

-- Todo: find out if there is really nothing about this?
instance : HasLimitsOfSize.{v, v} (Cᵒᵖ ⥤ Type v)ᵒᵖ :=
  { has_limits_of_shape := fun _ => hasLimitsOfShape_op_of_hasColimitsOfShape }

-- Todo: deduce this from the Yoneda lemma in mathlib
def my_yoneda_lemma (F : Cᵒᵖ ⥤ Type v) :
  yoneda.op ⋙ yoneda.obj F ≅ F ⋙ uliftFunctor.{u} :=
sorry

-- This is perhaps the composition of two more general facts, one about flipping and composing, and
-- one about flipping and yoneda.
def flip_calc : Functor.flip (β ⋙ yoneda) ≅ coyoneda ⋙ (whiskeringLeft _ _ _).obj β :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun j => Iso.refl _) (by aesop_cat)) (by aesop_cat)

noncomputable def homs_calc : ((colimit (α ⋙ yoneda)) ⟶ colimit (β ⋙ yoneda)) ≃
   limit (α.op ⋙ coyoneda ⋙ (whiskeringLeft _ _ _).obj β ⋙ colim) := by
  change (yoneda.obj (colimit (β ⋙ yoneda))).obj (Opposite.op (colimit (α ⋙ yoneda))) ≃ _

  let t := (yoneda.obj (colimit (β ⋙ yoneda))).mapIso (colimit_op (α ⋙ yoneda))
  refine' t.toEquiv.symm.trans _

  have p := preservesLimitsOfSizeShrink.{v, max u v, v, max u v} (yoneda.obj (colimit (β ⋙ yoneda)))
  have q : HasLimitsOfSize.{v, v} (Type (max u v)) := sorry
  have z : HasLimit (Functor.op (α ⋙ yoneda) ⋙ yoneda.obj (colimit (β ⋙ yoneda))) := sorry
  let u := preservesLimitIso (yoneda.obj (colimit (β ⋙ yoneda))) (α ⋙ yoneda).op
  refine' u.toEquiv.trans _

  let t := lim.mapIso (isoWhiskerLeft α.op (my_yoneda_lemma (colimit (β ⋙ yoneda))))
  refine' t.toEquiv.trans _

  have i : PreservesLimit (α.op ⋙ colimit (β ⋙ yoneda)) uliftFunctor.{u, v} := sorry
  have i' : HasLimit ((Functor.op α ⋙ colimit (β ⋙ yoneda)) ⋙ uliftFunctor) := sorry
  let o := preservesLimitIso uliftFunctor.{u, v} (α.op ⋙ colimit (β ⋙ yoneda))
  refine' o.toEquiv.symm.trans _
  refine' Equiv.ulift.trans _

  let oo := lim.mapIso (isoWhiskerLeft α.op (colimitIsoFlipCompColim (β ⋙ yoneda)))
  refine' oo.toEquiv.trans _

  let rr := lim.mapIso (isoWhiskerLeft α.op (isoWhiskerRight (flip_calc β) colim))
  exact rr.toEquiv

end CategoryTheory
