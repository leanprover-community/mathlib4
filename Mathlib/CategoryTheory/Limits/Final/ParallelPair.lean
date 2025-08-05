/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Final
/-!

# Conditions for `parallelPair` to be initial

In this file we give sufficient conditions on a category `C` and parallel morphisms `f g : X ⟶ Y`
in `C` so that `parallelPair f g` becomes an initial functor.

The conditions are that there is a morphism out of `X` to every object of `C` and that any two
parallel morphisms out of `X` factor through the parallel pair `f`, `g`
(`h₂ : ∀ ⦃Z : C⦄ (i j : X ⟶ Z), ∃ (a : Y ⟶ Z), i = f ≫ a ∧ j = g ≫ a`).
-/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

open WalkingParallelPair WalkingParallelPairHom CostructuredArrow

lemma parallelPair_initial_mk' {X Y : C} (f g : X ⟶ Y)
    (h₁ : ∀ Z, Nonempty (X ⟶ Z))
    (h₂ : ∀ ⦃Z : C⦄ (i j : X ⟶ Z),
      Zigzag (J := CostructuredArrow (parallelPair f g) Z)
        (mk (Y := zero) i) (mk (Y := zero) j)) :
    (parallelPair f g).Initial where
  out Z := by
    have : Nonempty (CostructuredArrow (parallelPair f g) Z) :=
      ⟨mk (Y := zero) (h₁ Z).some⟩
    have : ∀ (x : CostructuredArrow (parallelPair f g) Z), Zigzag x
      (mk (Y := zero) (h₁ Z).some) := by
        rintro ⟨(_ | _), ⟨⟩, φ⟩
        · apply h₂
        · refine Zigzag.trans ?_ (h₂ (f ≫ φ) _)
          exact Zigzag.of_inv (homMk left)
    exact zigzag_isConnected (fun x y => (this x).trans (this y).symm)

lemma parallelPair_initial_mk {X Y : C} (f g : X ⟶ Y)
    (h₁ : ∀ Z, Nonempty (X ⟶ Z))
    (h₂ : ∀ ⦃Z : C⦄ (i j : X ⟶ Z), ∃ (a : Y ⟶ Z), i = f ≫ a ∧ j = g ≫ a) :
    (parallelPair f g).Initial :=
  parallelPair_initial_mk' f g h₁ (fun Z i j => by
    obtain ⟨a, rfl, rfl⟩ := h₂ i j
    let f₁ : (mk (Y := zero) (f ≫ a) : CostructuredArrow (parallelPair f g) Z) ⟶ mk (Y := one) a :=
      homMk left
    let f₂ : (mk (Y := zero) (g ≫ a) : CostructuredArrow (parallelPair f g) Z) ⟶ mk (Y := one) a :=
      homMk right
    exact Zigzag.of_hom_inv f₁ f₂)

end Limits

end CategoryTheory
