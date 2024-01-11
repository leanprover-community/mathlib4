/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Fintype.Quotient
import Mathlib.ModelTheory.Semantics

#align_import model_theory.quotients from "leanprover-community/mathlib"@"d78597269638367c3863d40d45108f52207e03cf"

/-!
# Quotients of First-Order Structures
This file defines prestructures and quotients of first-order structures.

## Main Definitions
* If `s` is a setoid (equivalence relation) on `M`, a `FirstOrder.Language.Prestructure s` is the
data for a first-order structure on `M` that will still be a structure when modded out by `s`.
* The structure `FirstOrder.Language.quotientStructure s` is the resulting structure on
`Quotient s`.

-/


namespace FirstOrder

namespace Language

variable (L : Language) {M : Type*}

open FirstOrder

open Structure

/-- A prestructure is a first-order structure with a `Setoid` equivalence relation on it,
  such that quotienting by that equivalence relation is still a structure. -/
class Prestructure (s : Setoid M) where
  toStructure : L.Structure M
  fun_equiv : ∀ {n} {f : L.Functions n} (x y : Fin n → M), x ≈ y → funMap f x ≈ funMap f y
  rel_equiv : ∀ {n} {r : L.Relations n} (x y : Fin n → M) (_ : x ≈ y), RelMap r x = RelMap r y
#align first_order.language.prestructure FirstOrder.Language.Prestructure
#align first_order.language.prestructure.to_structure FirstOrder.Language.Prestructure.toStructure
#align first_order.language.prestructure.fun_equiv FirstOrder.Language.Prestructure.fun_equiv
#align first_order.language.prestructure.rel_equiv FirstOrder.Language.Prestructure.rel_equiv

variable {L} {s : Setoid M}
variable [ps : L.Prestructure s]

instance quotientStructure : L.Structure (Quotient s) where
  funMap {n} f x :=
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice x)
  RelMap {n} r x :=
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice x)
#align first_order.language.quotient_structure FirstOrder.Language.quotientStructure

variable (s)

theorem funMap_quotient_mk' {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    (funMap f fun i => (⟦x i⟧ : Quotient s)) = ⟦@funMap _ _ ps.toStructure _ f x⟧ := by
  change
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice _) =
      _
  rw [Quotient.finChoice_eq, Quotient.map_mk]
#align first_order.language.fun_map_quotient_mk FirstOrder.Language.funMap_quotient_mk'

theorem relMap_quotient_mk' {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    (RelMap r fun i => (⟦x i⟧ : Quotient s)) ↔ @RelMap _ _ ps.toStructure _ r x := by
  change
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice _) ↔
      _
  rw [Quotient.finChoice_eq, Quotient.lift_mk]
#align first_order.language.rel_map_quotient_mk FirstOrder.Language.relMap_quotient_mk'

theorem Term.realize_quotient_mk' {β : Type*} (t : L.Term β) (x : β → M) :
    (t.realize fun i => (⟦x i⟧ : Quotient s)) = ⟦@Term.realize _ _ ps.toStructure _ x t⟧ := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp only [ih, funMap_quotient_mk', Term.realize]
#align first_order.language.term.realize_quotient_mk FirstOrder.Language.Term.realize_quotient_mk'

end Language

end FirstOrder
