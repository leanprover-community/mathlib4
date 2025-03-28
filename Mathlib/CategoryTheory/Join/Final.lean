/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Join.Basic
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.IsConnected

/-!
# (Co)Finality of the inclusions in joins of category

This file records the fact that `inclLeft C D : C ⥤ C ⋆ D` is `Initial` if `C` is connected.
Dually, `inclRight : C ⥤ C ⋆ D` is `Final` if `D` is connected.

-/

namespace CategoryTheory.Join

variable (C D : Type*) [Category C] [Category D]

/-- The category of `inclLeft C D`-costructured arrows with target `right d` is equivalent to C. -/
def CostructuredArrowEquiv (d : D) : CostructuredArrow (inclLeft C D) (right d) ≌ C where
  functor := CostructuredArrow.proj (inclLeft C D) (right d)
  inverse :=
    { obj c := .mk (edge c d)
      map f := CostructuredArrow.homMk _ }
  unitIso := NatIso.ofComponents (fun _ ↦ CostructuredArrow.isoMk _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The category of `inclRight C D`-structured arrows with source `left c` is equivalent to D. -/
def StructuredArrowEquiv (c : C) : StructuredArrow (left c) (inclRight C D) ≌ D where
  functor := StructuredArrow.proj (left c) (inclRight C D)
  inverse :=
    { obj d := .mk (edge c d)
      map f := StructuredArrow.homMk _ }
  unitIso := NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance [IsConnected C] : (inclLeft C D).Initial where
  out x := match x with
    |.left _ => isConnected_of_isTerminal _ CostructuredArrow.mkIdTerminal
    |.right d => isConnected_of_equivalent (CostructuredArrowEquiv C D d).symm

instance [IsConnected D] : (inclRight C D).Final where
  out x := match x with
    |.left c => isConnected_of_equivalent (StructuredArrowEquiv C D c).symm
    |.right d => isConnected_of_isInitial (StructuredArrow (right d) (inclRight C D))
      (@StructuredArrow.mkIdInitial D _ (C ⋆ D) _ d (inclRight C D) _ _)

end CategoryTheory.Join
