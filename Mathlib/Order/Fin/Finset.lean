/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Hom.Set
import Mathlib.Data.Finset.Insert

/-!
# Order isomorphisms from Fin to finsets

We define order isomorphisms like `Fin.orderIsoTriple` from `Fin 3`
to the finset `{a, b, c}` when `a < b` and `b < c`.

-/

namespace Fin

-- move to Mathlib.Order.Hom.Basic
@[simps!]
noncomputable def OrderIso.ofUnique
    (A B : Type*) [Unique A] [Unique B] [Preorder A] [Preorder B] :
    A ≃o B where
  __ := Equiv.ofUnique A B
  map_rel_iff' {a b} := by simp

variable {α : Type*} [Preorder α] [DecidableEq α]

/-- This is the order isomorphisms from `Fin 1` to a finset `{a}`. -/
@[simps! apply]
noncomputable def orderIsoSingleton' (a : α) :
    Fin 1 ≃o ({a} : Finset α) :=
  .ofUnique _ _

/-- This is the order isomorphisms from `Fin 2` to a finset `{a, b}` when `a < b`. -/
@[simps! apply]
noncomputable def orderIsoPair (a b : α) (hab : a < b) :
    Fin 2 ≃o ({a, b} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩]
    (strictMono_vecEmpty.vecCons hab) (fun ⟨x, hx⟩ ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)

/-- This is the order isomorphisms from `Fin 3`
to a finset `{a, b, c}` when `a < b` and `b < c`. -/
@[simps! apply]
noncomputable def orderIsoTriple (a b c : α) (hab : a < b) (hbc : b < c) :
    Fin 3 ≃o ({a, b, c} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩, ⟨c, by simp⟩]
    (StrictMono.vecCons (strictMono_vecEmpty.vecCons hbc) hab) (fun ⟨x, hx⟩ ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)

end Fin
