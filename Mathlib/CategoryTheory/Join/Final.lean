/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Join.Basic
import Mathlib.CategoryTheory.Limits.Final

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
    |.left c => by
      let t : CostructuredArrow (inclLeft C D) (left c) := .mk (𝟙 (left c))
      sorry
      -- letI : Nonempty (CostructuredArrow (inclLeft C D) (left c)) := ⟨t⟩
      -- apply isConnected_of_zigzag
      -- intro j₁ j₂
      -- let f₁ : j₁ ⟶ t := CostructuredArrow.homMk _
      -- let f₂ : j₂ ⟶ t := CostructuredArrow.homMk _
      -- use [t, j₂]
      -- constructor
      -- · simp only [List.chain_cons, List.Chain.nil, and_true]
      --   exact ⟨Zag.of_hom f₁, Zag.symm (Zag.of_hom f₂)⟩
      -- · rfl
    |.right d => by
      exact isConnected_of_equivalent (CostructuredArrowEquiv C D d).symm
      sorry




end CategoryTheory.Join
