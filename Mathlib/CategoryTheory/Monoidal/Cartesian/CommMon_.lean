/-
Copyright (c) 2025 Yaël Dillies, Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Markus Himmel
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# Commutative monoids objects in cartesian monoidal categories
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits MonoidalCategory ChosenFiniteProducts

variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]

namespace CategoryTheory

attribute [local instance] Functor.monoidalOfChosenFiniteProducts
  Functor.braidedOfChosenFiniteProducts

namespace Functor
variable {F F' : C ⥤ D} [PreservesFiniteProducts F] [PreservesFiniteProducts F']

/-- Natural transformations between functors lift to monoid objects. -/
@[simps!]
noncomputable def mapCommMonNatTrans (f : F ⟶ F') : F.mapCommMon ⟶ F'.mapCommMon where
  app X := .mk (f.app _)

/-- Natural isomorphisms between functors lift to monoid objects. -/
@[simps!]
noncomputable def mapCommMonNatIso (e : F ≅ F') : F.mapCommMon ≅ F'.mapCommMon :=
  NatIso.ofComponents fun X ↦ CommMon_.mkIso (e.app _)

end Functor

open Functor

namespace Equivalence

-- FIXME: There is a diamond between `LaxBraided.id` and `Functor.braidedOfChosenFiniteProducts`
-- noncomputable def mapCommMon (e : C ≌ D) : CommMon_ C ≌ CommMon_ D where
--   functor := e.functor.mapCommMon
--   inverse := e.inverse.mapCommMon
--   unitIso := mapCommMonIdIso.symm ≪≫ mapCommMonNatIso e.unitIso ≪≫ mapCommMonCompIso
--   counitIso := mapCommMonCompIso.symm ≪≫ mapCommMonNatIso e.counitIso ≪≫ mapCommMonIdIso

end CategoryTheory.Equivalence
