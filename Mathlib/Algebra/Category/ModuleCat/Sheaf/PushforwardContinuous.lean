/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Pushforward of sheaves of modules

Assume that `C` and `D` are categories equipped with Grothendieck topologies.
Let `F : C ⥤ D` be a continuous functor and `R` a sheaf of rings over `D`.
In this file, we construct a pushforward functor
`SheafOfModules.{v} R ⥤ SheafOd`.

If `F : C ⥤ D` is a continuous functor, the precomposition `F.op ⋙ _` induces a functor from presheaves
over `C` to presheaves over `D`. When `R : Dᵒᵖ ⥤ RingCat`, we define the
induced functor `PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R)`
on presheaves of modules.

-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₁} [Category.{v₂} D]

namespace SheafOfModules




end SheafOfModules
