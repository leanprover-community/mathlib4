/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Sheafification

universe v u

namespace CategoryTheory

open Limits Opposite

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)]

structure MayerVietorisSquare where
  /-- the object that is covered -/
  X : C
  /-- the first object of the covering -/
  U : C
  /-- the second object of the covering -/
  V : C
  /-- the pullback of `U` and `V` over `X` -/
  W : C
  /-- the inclusion of `U` in `X` -/
  i : U ⟶ X
  /-- the morphism from `V` to `X` -/
  j : V ⟶ X
  /-- the morphism from `W` to `U` -/
  p : W ⟶ U
  /-- the inclusion from `W` to `V` -/
  q : W ⟶ V
  fac : p ≫ i = q ≫ j
  hi : Mono i := by infer_instance
  isColimit :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsColimit (PushoutCocone.mk
      (f := F.map p) (g := F.map q) (F.map i) (F.map j) (by
        simp only [← Functor.map_comp, fac]))

variable {J}

namespace MayerVietorisSquare

variable (S : J.MayerVietorisSquare)
variable (F : Sheaf J (Type v))
  (u : F.val.obj (op S.U)) (v : F.val.obj (op S.V))
  (h : F.val.map S.p.op u = F.val.map S.q.op v)

def glue : F.val.obj (op S.X) :=
  yonedaEquiv ((sheafificationAdjunction _ _).homEquiv _ _
    (PushoutCocone.IsColimit.desc S.isColimit
      (((sheafificationAdjunction _ _).homEquiv _ _).symm (yonedaEquiv.symm u))
      (((sheafificationAdjunction _ _).homEquiv _ _).symm (yonedaEquiv.symm v)) (by
        dsimp
        apply ((sheafificationAdjunction _ _).homEquiv _ _).injective
        sorry)))

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory
