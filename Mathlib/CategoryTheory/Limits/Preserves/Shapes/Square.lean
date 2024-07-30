/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Preservations of pullback/pushout squares

If a functor `F : C ⥤ D` preserves suitable cospans (resp. spans),
and `sq : Square C` is a pullback square (resp. a pushout square)
then so is the square`sq.map F`.

The lemma `Square.isPullback_iff_map_coyoneda_isPullback` also
shows that a square is a pullback square iff it is so after the
application of the functor `coyoneda.obj X` for all `X : Cᵒᵖ`.
Similarly, a square is a pushout square iff the opposite
square becomes a pullback square after the application of the
functor `yoneda.obj X` for all `X : C`.

-/

universe v v' u u'

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Square

variable {sq : Square C}

lemma IsPullback.map (h : sq.IsPullback) (F : C ⥤ D) [PreservesLimit (cospan sq.f₂₄ sq.f₃₄) F] :
    (sq.map F).IsPullback :=
  Square.IsPullback.mk _ (isLimitPullbackConeMapOfIsLimit F sq.fac h.isLimit)

lemma IsPushout.map (h : sq.IsPushout) (F : C ⥤ D) [PreservesColimit (span sq.f₁₂ sq.f₁₃) F] :
    (sq.map F).IsPushout :=
  Square.IsPushout.mk _ (isColimitPushoutCoconeMapOfIsColimit F sq.fac h.isColimit)

variable (sq)

lemma isPullback_iff_map_coyoneda_isPullback :
    sq.IsPullback ↔ ∀ (X : Cᵒᵖ), (sq.map (coyoneda.obj X)).IsPullback :=
  ⟨fun h _ ↦ h.map _, fun h ↦ IsPullback.mk _
    ((sq.pullbackCone.isLimitCoyonedaEquiv).symm (fun X ↦ (h X).isLimit))⟩

lemma isPushout_iff_op_map_yoneda_isPullback :
    sq.IsPushout ↔ ∀ (X : C), (sq.op.map (yoneda.obj X)).IsPullback :=
  ⟨fun h _ ↦ h.op.map _, fun h ↦ IsPushout.mk _
    ((sq.pushoutCocone.isColimitYonedaEquiv).symm
      (fun X ↦ IsLimit.ofIsoLimit (h X).isLimit (PullbackCone.ext (Iso.refl _))))⟩

end Square

end CategoryTheory
