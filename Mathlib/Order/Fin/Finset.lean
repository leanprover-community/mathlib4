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

## Future works

* Do the same for `Set` without too much duplication of code (TODO)
* Provide a definition which would take as an input an order
  isomorphism `e : Fin (n + 1) ≃o s` (with `s : Set α` (or `Finset α`)) and
  extend it to an order isomorphism `Fin (n + 2) ≃o Finset.insert i s` when `i < e 0` (TODO).

-/

namespace Fin

variable {α : Type*} [Preorder α]

/-- This is the order isomorphism from `Fin 1` to a finset `{a}`. -/
noncomputable def orderIsoSingleton (a : α) :
    Fin 1 ≃o ({a} : Finset α) :=
  OrderIso.ofUnique _ _

@[simp]
lemma orderIsoSingleton_apply (a : α) (i : Fin 1) :
    orderIsoSingleton a i = a := rfl

variable [DecidableEq α]

section

variable (a b : α) (hab : a < b)

/-- This is the order isomorphism from `Fin 2` to a finset `{a, b}` when `a < b`. -/
noncomputable def orderIsoPair :
    Fin 2 ≃o ({a, b} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩]
    (strictMono_vecEmpty.vecCons hab) (fun ⟨x, hx⟩ ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)

@[simp] lemma orderIsoPair_zero : orderIsoPair a b hab 0 = a := rfl
@[simp] lemma orderIsoPair_one : orderIsoPair a b hab 1 = b := rfl

end

section

variable (a b c : α) (hab : a < b) (hbc : b < c)

/-- This is the order isomorphism from `Fin 3`
to a finset `{a, b, c}` when `a < b` and `b < c`. -/
noncomputable def orderIsoTriple :
    Fin 3 ≃o ({a, b, c} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩, ⟨c, by simp⟩]
    (StrictMono.vecCons (strictMono_vecEmpty.vecCons hbc) hab) (fun ⟨x, hx⟩ ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)

@[simp] lemma orderIsoTriple_zero : orderIsoTriple a b c hab hbc 0 = a := rfl
@[simp] lemma orderIsoTriple_one : orderIsoTriple a b c hab hbc 1 = b := rfl
@[simp] lemma orderIsoTriple_two : orderIsoTriple a b c hab hbc 2 = c := rfl

end

end Fin
