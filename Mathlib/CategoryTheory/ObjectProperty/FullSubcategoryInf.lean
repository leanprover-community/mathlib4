/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

/-!
# Full subcategory on a binary infimum of object properties

In this file, we record the equivalence between `(P ⊓ Q).FullSubcategory`, and
the full of P.FullSubcategory on the inverse image of Q.

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C]

variable (P Q : ObjectProperty C)

/-- The full subcategory on `P ⊓ Q` identifies to a full subcategory of Q.FullSubcategory. -/
@[simps!, implicit_reducible]
def infEquivalence :
    (P ⊓ Q).FullSubcategory ≌ (P.inverseImage (Q.ι)).FullSubcategory where
  functor := lift _ (ιOfLE <| inf_le_right) (fun x ↦ (inf_le_left (a := P) (b := Q)) _ x.property)
  inverse := lift _ ((P.inverseImage Q.ι).ι ⋙ Q.ι) fun x ↦ by
    have := x.property
    have := x.obj.property
    simp_all
  counitIso := NatIso.ofComponents fun _ ↦ .refl _
  unitIso := NatIso.ofComponents fun _ ↦ .refl _

end CategoryTheory.ObjectProperty

