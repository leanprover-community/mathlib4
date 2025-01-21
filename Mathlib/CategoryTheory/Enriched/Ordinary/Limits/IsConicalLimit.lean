/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Riehl, Dagur Asgeirsson, Jon Eugster
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Conical limits / enriched limits
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits Opposite

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable {F : J ⥤ C} (c : Cone F)

/--
A limit cone `c` in a `V`-enriched ordinary category `C` is a *`V`-enriched limit*
(or *conical limit*) if for every `X : C`, the cone obtained by applying the coyoneda
functor `(X ⟶[V] -)` to `c` is a limit cone in `V`.
-/
structure IsConicalLimit where
  /-- A conical limit cone is a limit cone. -/
  isLimit : IsLimit c
  /--
  The cone obtained by applying the coyoneda functor `(X ⟶[V] -)` to `c` is a limit cone in `V`.
  -/
  isConicalLimit (X : C) : IsLimit <| (eCoyoneda V X).mapCone c

end CategoryTheory.Enriched
