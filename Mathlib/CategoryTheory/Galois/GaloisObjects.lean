/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.Logic.Equiv.TransferInstance

/-!
# Galois objects in Galois categories

We define Galois objects in a Galois category `C` in a fibre functor independent way and show
equivalent characterisations.

## Main definitions

* `GaloisObject` : Connected object `X` of `C` such that `X / Aut X` is terminal.

## Main results

* `galois_iff_pretransitive` : A connected object `X` is Galois if and only if `Aut X`
                               acts transitively on `F.obj X` for a fibre functor `F`.

-/
universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

noncomputable instance {G : Type v} [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) FintypeCat.incl.{w} := by
  choose G' hg hf e using Finite.exists_type_zero_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShapeOfEquiv (Classical.choice e).toSingleObjEquiv.symm _

/-- A connected object `X` of `C` is Galois if the quotient `X / Aut X` is terminal. -/
class GaloisObject {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (X : C) : Prop where
  connected : ConnectedObject X
  quotientByAutTerminal : Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X)

namespace GaloisObject

attribute [instance] connected

end GaloisObject

variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FibreFunctor F]

/-- The natural action of `Aut X` on `F.obj X`. -/
instance autMulFibre (X : C) : MulAction (Aut X) (F.obj X) where
  smul σ a := F.map σ.hom a
  one_smul a := by
    show F.map (𝟙 X) a = a
    simp only [map_id, FintypeCat.id_apply]
  mul_smul g h a := by
    show F.map (h.hom ≫ g.hom) a = (F.map h.hom ≫ F.map g.hom) a
    simp only [map_comp, FintypeCat.comp_apply]

/-- For a connected object `X` of `C`, the quotient `X / Aut X` is terminal if and only if
the quotient `F.obj X / Aut X` has exactly one element. -/
noncomputable def quotientByAutTerminalEquivUniqueQuotient [GaloisCategory C]
    (X : C) [ConnectedObject X] :
    IsTerminal (colimit <| SingleObj.functor <| Aut.toEnd X) ≃
    Unique (MulAction.orbitRel.Quotient (Aut X) (F.obj X)) := by
  letI J : SingleObj (Aut X) ⥤ C := SingleObj.functor (Aut.toEnd X)
  letI e : (F ⋙ FintypeCat.incl).obj (colimit J) ≅ _ :=
    preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
    (Equiv.toIso <| SingleObj.Types.colimitEquivQuotient (J ⋙ F ⋙ FintypeCat.incl))
  apply Equiv.trans
  apply (IsTerminal.isTerminalIffObj (F ⋙ FintypeCat.incl) _).trans
    (isLimitEmptyConeEquiv _ (asEmptyCone _) (asEmptyCone _) e)
  exact Types.isTerminalEquivUnique _

lemma galois_iff_aux [GaloisCategory C] (X : C) [ConnectedObject X] :
    GaloisObject X ↔ Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X) :=
  ⟨fun h ↦ h.quotientByAutTerminal, fun h ↦ ⟨inferInstance, h⟩⟩

/-- Given a fibre functor `F` and a connected object `X` of `C`. Then `X` is Galois if and only if
the natural action of `Aut X` on `F.obj X` is transitive. -/
theorem galois_iff_pretransitive [GaloisCategory C] (X : C) [ConnectedObject X] :
    GaloisObject X ↔ MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [galois_iff_aux, Equiv.nonempty_congr <| quotientByAutTerminalEquivUniqueQuotient F X]
  exact (MulAction.pretransitive_iff_unique_quotient_of_nonempty (Aut X) (F.obj X)).symm
