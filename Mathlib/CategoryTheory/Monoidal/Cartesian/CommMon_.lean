/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
# Commutative monoids objects in cartesian monoidal categories
-/

open CategoryTheory Limits MonoidalCategory ChosenFiniteProducts

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [ChosenFiniteProducts C]
variable {D : Type u₂} [Category.{v₂} D] [ChosenFiniteProducts D]

namespace CategoryTheory
namespace Functor
variable {F F' : C ⥤ D} [F.Braided] [F'.Braided]

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

namespace Adjunction
variable {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Braided] [G.Braided]

/-- An adjunction of braided functors lifts to an adjunction of their lifts to commutative monoid
objects. -/
@[simps!] noncomputable def mapCommMon : F.mapCommMon ⊣ G.mapCommMon where
  unit := mapCommMonIdIso.inv ≫ mapCommMonNatTrans a.unit ≫ mapCommMonCompIso.hom
  counit := mapCommMonCompIso.inv ≫ mapCommMonNatTrans a.counit ≫ mapCommMonIdIso.hom

end Adjunction

namespace Equivalence

/-- An equivalence of categories lifts to an equivalence of their commutative monoid objects. -/
noncomputable def mapCommMon (e : C ≌ D) [e.functor.Braided] [e.inverse.Braided] :
    CommMon_ C ≌ CommMon_ D where
  functor := e.functor.mapCommMon
  inverse := e.inverse.mapCommMon
  unitIso := mapCommMonIdIso.symm ≪≫ mapCommMonNatIso e.unitIso ≪≫ mapCommMonCompIso
  counitIso := mapCommMonCompIso.symm ≪≫ mapCommMonNatIso e.counitIso ≪≫ mapCommMonIdIso

end CategoryTheory.Equivalence
