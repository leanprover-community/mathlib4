/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.quotients
! leanprover-community/mathlib commit d78597269638367c3863d40d45108f52207e03cf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Quotient
import Mathbin.ModelTheory.Semantics

/-!
# Quotients of First-Order Structures
This file defines prestructures and quotients of first-order structures.

## Main Definitions
* If `s` is a setoid (equivalence relation) on `M`, a `first_order.language.prestructure s` is the
data for a first-order structure on `M` that will still be a structure when modded out by `s`.
* The structure `first_order.language.quotient_structure s` is the resulting structure on
`quotient s`.

-/


namespace FirstOrder

namespace Language

variable (L : Language) {M : Type _}

open FirstOrder

open Structure

/-- A prestructure is a first-order structure with a `setoid` equivalence relation on it,
  such that quotienting by that equivalence relation is still a structure. -/
class Prestructure (s : Setoid M) where
  toStructure : L.Structure M
  fun_equiv : ∀ {n} {f : L.Functions n} (x y : Fin n → M), x ≈ y → funMap f x ≈ funMap f y
  rel_equiv : ∀ {n} {r : L.Relations n} (x y : Fin n → M) (h : x ≈ y), RelMap r x = RelMap r y
#align first_order.language.prestructure FirstOrder.Language.Prestructure

variable {L} {s : Setoid M} [ps : L.Prestructure s]

instance quotientStructure : L.Structure (Quotient s)
    where
  funMap n f x :=
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice x)
  rel_map n r x :=
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice x)
#align first_order.language.quotient_structure FirstOrder.Language.quotientStructure

variable (s)

include s

theorem funMap_quotient_mk' {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    (funMap f fun i => ⟦x i⟧) = ⟦@funMap _ _ ps.toStructure _ f x⟧ :=
  by
  change
    Quotient.map (@fun_map L M ps.to_structure n f) prestructure.fun_equiv (Quotient.finChoice _) =
      _
  rw [Quotient.finChoice_eq, Quotient.map_mk]
#align first_order.language.fun_map_quotient_mk FirstOrder.Language.funMap_quotient_mk'

theorem relMap_quotient_mk' {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    (RelMap r fun i => ⟦x i⟧) ↔ @RelMap _ _ ps.toStructure _ r x :=
  by
  change
    Quotient.lift (@rel_map L M ps.to_structure n r) prestructure.rel_equiv (Quotient.finChoice _) ↔
      _
  rw [Quotient.finChoice_eq, Quotient.lift_mk]
#align first_order.language.rel_map_quotient_mk FirstOrder.Language.relMap_quotient_mk'

theorem Term.realize_quotient_mk' {β : Type _} (t : L.term β) (x : β → M) :
    (t.realize fun i => ⟦x i⟧) = ⟦@Term.realize _ _ ps.toStructure _ x t⟧ :=
  by
  induction' t with _ _ _ _ ih
  · rfl
  · simp only [ih, fun_map_quotient_mk, term.realize]
#align first_order.language.term.realize_quotient_mk FirstOrder.Language.Term.realize_quotient_mk'

end Language

end FirstOrder

