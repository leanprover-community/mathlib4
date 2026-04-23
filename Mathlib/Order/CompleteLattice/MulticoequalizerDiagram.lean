/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# Multicoequalizer diagrams in complete lattices

We introduce the notion of bi-Cartesian square (`Lattice.BicartSq`) in a lattice `T`.
This consists of elements `x₁`, `x₂`, `x₃` and `x₄` such that `x₂ ⊔ x₃ = x₄` and
`x₂ ⊓ x₃ = x₁`.

It shall be shown (TODO) that if `T := Set X`, then the image of the
associated commutative square in the category `Type _` is a bi-Cartesian square
in a categorical sense (both pushout and pullback).

More generally, if `T` is a complete lattice, `x : T`, `u : ι → T`, `v : ι → ι → T`,
we introduce a property `MulticoequalizerDiagram x u v` which says that `x` is
the supremum of `u`, and that for all `i` and `j`, `v i j` is the minimum of `u i` and `u j`.
Again, when `T := Set X`, we shall show (TODO) that we obtain a multicoequalizer diagram
in the category of types.

-/

@[expose] public section

universe u

open CategoryTheory Limits

local grind_pattern inf_le_left => a ⊓ b
local grind_pattern inf_le_right => a ⊓ b
local grind_pattern le_sup_left => a ⊔ b
local grind_pattern le_sup_right => a ⊔ b

namespace Lattice

variable {T : Type u} (x₁ x₂ x₃ x₄ : T) [Lattice T]

/-- A bi-Cartesian square in a lattice consists of elements `x₁`, `x₂`, `x₃` and `x₄`
such that `x₂ ⊔ x₃ = x₄` and `x₂ ⊓ x₃ = x₁`. -/
structure BicartSq : Prop where
  sup_eq : x₂ ⊔ x₃ = x₄
  inf_eq : x₂ ⊓ x₃ = x₁

attribute [grind cases] BicartSq

namespace BicartSq

@[deprecated (since := "2025-11-26")] alias max_eq := sup_eq
@[deprecated (since := "2025-11-26")] alias min_eq := inf_eq

variable {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄)

include sq

lemma le₁₂ : x₁ ≤ x₂ := by grind
lemma le₁₃ : x₁ ≤ x₃ := by grind
lemma le₂₄ : x₂ ≤ x₄ := by grind
lemma le₃₄ : x₃ ≤ x₄ := by grind

/-- The commutative square associated to a bi-Cartesian square in a lattice. -/
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
  eq_inf (i j : ι) : v i j = u i ⊓ u j

namespace MulticoequalizerDiagram

@[deprecated (since := "2025-11-26")] alias min_eq := eq_inf

attribute [local grind] MulticoequalizerDiagram
attribute [local grind =] MultispanShape.prod_fst MultispanShape.prod_snd

variable {x u v} (d : MulticoequalizerDiagram x u v)

/-- The multispan index in the category associated to the complete lattice `T`
given by the objects `u i` and the minima `v i j = u i ⊓ u j`,
when `d : MulticoequalizerDiagram x u v`. -/
@[simps]
def multispanIndex : MultispanIndex (.prod ι) T where
  left := fun ⟨i, j⟩ ↦ v i j
  right := u
  fst _ := homOfLE (by grind)
  snd _ := homOfLE (by grind)

/-- The multicofork in the category associated to the complete lattice `T`
associated to `d : MulticoequalizerDiagram x u v` with `x : T`.
(In the case `T := Set X`, this multicofork becomes colimit after the application
of the obvious functor `Set X ⥤ Type _`.) -/
@[simps! pt]
def multicofork : Multicofork d.multispanIndex :=
  Multicofork.ofπ _ x (fun i ↦ homOfLE (by grind [multispanIndex_right, le_iSup_iff]))
    (fun _ ↦ rfl)

end MulticoequalizerDiagram

end CompleteLattice

lemma Lattice.BicartSq.multicoequalizerDiagram {T : Type u} [CompleteLattice T]
    {x₁ x₂ x₃ x₄} (sq : BicartSq x₁ x₂ x₃ x₄) :
    CompleteLattice.MulticoequalizerDiagram (T := T) x₄
      (fun i ↦ bif i then x₃ else x₂)
      (fun i j ↦ bif i then bif j then x₃ else x₁
        else bif j then x₁ else x₂) where
  iSup_eq := by rw [← sq.sup_eq, sup_comm, sup_eq_iSup]
  eq_inf i j := by grind
