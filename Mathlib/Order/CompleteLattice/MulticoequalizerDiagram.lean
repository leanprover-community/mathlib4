/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.CompleteLattice.Lemmas
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.CommSq
import Mathlib.Tactic.FinCases

/-!
# Multicoequalizer diagrams in complete lattices

We introduce the notion of bicartesian square (`Lattice.BicartSq`) in a lattice `T`.
This consists of elements `x₁`, `x₂`, `x₃` and `x₄` such that `x₂ ⊔ x₃ = x₄` and
`x₂ ⊓ x₃ = x₁`.

It shall be shown (TODO) that if `T := Set X`, then the image of the
associated commutative square in the category `Type _` is a bicartesian square
in a categorical sense (both pushout and pullback).

More generally, if `T` is a complete lattice, `x : T`, `u : ι → T`, `v : ι → ι → T`,
we introduce a property `MulticoequalizerDiagram x u v` which says that `x` is
the supremum of `u`, and that for all `i` and `j`, `v i j` is the minimum of `u i` and `u j`.
Again, when `T := Set X`, we shall show (TOOD) that we obtain a multicoequalizer diagram
in the category of types.

-/

universe u

open CategoryTheory Limits

namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

/-- A bicartesian square in a lattice consists of elements `x₁`, `x₂`, `x₃` and `x₄`
such that `x₂ ⊔ x₃ = x₄` and `x₂ ⊓ x₃ = x₁`. -/
structure BicartSq : Prop where
  max_eq : x₂ ⊔ x₃ = x₄
  min_eq : x₂ ⊓ x₃ = x₁

namespace BicartSq

variable {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄)

include sq

lemma le₁₂ : x₁ ≤ x₂ := by simpa only [← sq.min_eq] using inf_le_left
lemma le₁₃ : x₁ ≤ x₃ := by simpa only [← sq.min_eq] using inf_le_right
lemma le₂₄ : x₂ ≤ x₄ := by simpa only [← sq.max_eq] using le_sup_left
lemma le₃₄ : x₃ ≤ x₄ := by simpa only [← sq.max_eq] using le_sup_right

/-- The commutative square associated to a bicartesian square in a lattice. -/
lemma commSq : CommSq (homOfLE sq.le₁₂) (homOfLE sq.le₁₃)
    (homOfLE sq.le₂₄) (homOfLE sq.le₃₄) := ⟨rfl⟩

end BicartSq

end Lattice

namespace CompleteLattice

variable {T : Type u} [CompleteLattice T] {ι : Type*} (x : T) (u : ι → T) (v : ι → ι → T)

/-- A multicoequalizer diagram in a complete lattice `T` consists of families of elements
`u : ι → T`, `v : ι → ι → T`, and an element `x : T` such that `x` is the supremum of `u`,
and for any `i` and `j`, `v i j` is the minimum of `u i` and `u j`. -/
structure MulticoequalizerDiagram : Prop where
  iSup_eq : ⨆ (i : ι), u i = x
  min_eq (i j : ι) : u i ⊓ u j = v i j

namespace MulticoequalizerDiagram

variable {x u v} (d : MulticoequalizerDiagram x u v)

/-- The multispan index in the category associated to the complete lattice `T`
given by the objects `u i` and the minima `v i j = u i ⊓ u j`,
when `d : MulticoequalizerDiagram x u v`. -/
@[simps]
def multispanIndex : MultispanIndex (.prod ι) T where
  left := fun ⟨i, j⟩ ↦ v i j
  right := u
  fst (_ : ι × ι) := homOfLE (by
    dsimp
    rw [← d.min_eq]
    exact inf_le_left)
  snd (_ : ι × ι) := homOfLE (by
    dsimp
    rw [← d.min_eq]
    exact inf_le_right)

/-- The multicofork in the category associated to the complete lattice `T`
associated to `d : MulticoequalizerDiagram x u v` with `x : T`.
(In the case `T := Set X`, this multicofork becomes colimit after the application
of the obvious functor `Set X ⥤ Type _`.) -/
@[simps! pt]
def multicofork : Multicofork d.multispanIndex :=
  Multicofork.ofπ _ x (fun i ↦ homOfLE (by simpa only [← d.iSup_eq] using le_iSup u i))
    (fun _ ↦ rfl)

end MulticoequalizerDiagram

end CompleteLattice

lemma Lattice.BicartSq.multicoequalizerDiagram {T : Type u} [CompleteLattice T]
    {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄) :
    CompleteLattice.MulticoequalizerDiagram (T := T) x₄
      (fun i ↦ bif i then x₃ else x₂)
      (fun i j ↦ bif i then bif j then x₃ else x₁
        else bif j then x₁ else x₂) where
  iSup_eq := by rw [← sq.max_eq, sup_comm, sup_eq_iSup]
  min_eq i j := by fin_cases i <;> fin_cases j <;> simp [← sq.min_eq, inf_comm x₂ x₃]
