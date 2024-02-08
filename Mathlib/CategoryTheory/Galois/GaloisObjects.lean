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

We define when a connected object of a Galois category `C` is Galois in a fiber functor independent
way and show equivalent characterisations.

## Main definitions

* `IsGalois` : Connected object `X` of `C` such that `X / Aut X` is terminal.

## Main results

* `galois_iff_pretransitive` : A connected object `X` is Galois if and only if `Aut X`
                               acts transitively on `F.obj X` for a fiber functor `F`.

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
class IsGalois {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (X : C)
    extends IsConnected X : Prop where
  quotientByAutTerminal : Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X)

variable {C : Type u₁} [Category.{u₂, u₁} C]

/-- The natural action of `Aut X` on `F.obj X`. -/
instance autMulFiber (F : C ⥤ FintypeCat.{w}) (X : C) : MulAction (Aut X) (F.obj X) where
  smul σ a := F.map σ.hom a
  one_smul a := by
    show F.map (𝟙 X) a = a
    simp only [map_id, FintypeCat.id_apply]
  mul_smul g h a := by
    show F.map (h.hom ≫ g.hom) a = (F.map h.hom ≫ F.map g.hom) a
    simp only [map_comp, FintypeCat.comp_apply]

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- For a connected object `X` of `C`, the quotient `X / Aut X` is terminal if and only if
the quotient `F.obj X / Aut X` has exactly one element. -/
noncomputable def quotientByAutTerminalEquivUniqueQuotient
    (X : C) [IsConnected X] :
    IsTerminal (colimit <| SingleObj.functor <| Aut.toEnd X) ≃
    Unique (MulAction.orbitRel.Quotient (Aut X) (F.obj X)) := by
  let J : SingleObj (Aut X) ⥤ C := SingleObj.functor (Aut.toEnd X)
  let e : (F ⋙ FintypeCat.incl).obj (colimit J) ≅ _ :=
    preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
    (Equiv.toIso <| SingleObj.Types.colimitEquivQuotient (J ⋙ F ⋙ FintypeCat.incl))
  apply Equiv.trans
  apply (IsTerminal.isTerminalIffObj (F ⋙ FintypeCat.incl) _).trans
    (isLimitEmptyConeEquiv _ (asEmptyCone _) (asEmptyCone _) e)
  exact Types.isTerminalEquivUnique _

lemma isGalois_iff_aux (X : C) [IsConnected X] :
    IsGalois X ↔ Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X) :=
  ⟨fun h ↦ h.quotientByAutTerminal, fun h ↦ ⟨h⟩⟩

/-- Given a fiber functor `F` and a connected object `X` of `C`. Then `X` is Galois if and only if
the natural action of `Aut X` on `F.obj X` is transitive. -/
theorem isGalois_iff_pretransitive (X : C) [IsConnected X] :
    IsGalois X ↔ MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [isGalois_iff_aux, Equiv.nonempty_congr <| quotientByAutTerminalEquivUniqueQuotient F X]
  exact (MulAction.pretransitive_iff_unique_quotient_of_nonempty (Aut X) (F.obj X)).symm

/-- If `X` is Galois, the quotient `X / Aut X` is terminal.  -/
noncomputable def isTerminalQuotientOfIsGalois (X : C) [IsGalois X] :
    IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X :=
  Nonempty.some IsGalois.quotientByAutTerminal

/-- If `X` is Galois, then the action of `Aut X` on `F.obj X` is
transitive for every fiber functor `F`. -/
instance isPretransitive_of_isGalois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [← isGalois_iff_pretransitive]
  infer_instance

end PreGaloisCategory

end CategoryTheory
