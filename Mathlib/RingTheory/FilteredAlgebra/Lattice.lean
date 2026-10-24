/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.RingTheory.FilteredAlgebra.Basic

/-!
# filtrations in a lattice setting

In this file, we show that the conventions for filtrations are well-behaved when the filtrations
takes values in a complete lattice, such as the lattice of `R`-submodules of an `R`-module, for `R`
a ring.

-/

public section

noncomputable section

universe u v w

variable {ι : Type v} {R : Type w} {A : Type u}

section

variable {ι A σ : Type*} [Preorder ι] [CompleteLattice σ] [SetLike σ A]
  (F : ι → σ) (F_lt : outParam <| ι → σ) [IsFiltration F F_lt]

lemma IsFiltration.f_lt_eq_sup (i : ι) :
    F_lt i = ⨆ j < i, F j :=
  le_antisymm_iff.mpr ⟨IsFiltration.is_sup (⨆ j < i, F j) i fun _ h ↦ le_biSup F h,
    iSup₂_le fun _ h ↦ IsFiltration.is_le h⟩

end
