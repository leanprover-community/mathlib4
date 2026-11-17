/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.Order.Group.Nat

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Free monoids have unique products
-/

public section

assert_not_exists Cardinal Subsemiring Algebra Submodule StarModule

open Finset

/-- Any `FreeMonoid` has the `TwoUniqueProds` property. -/
instance FreeMonoid.instTwoUniqueProds {κ : Type*} : TwoUniqueProds (FreeMonoid κ) :=
  .of_mulHom ⟨Multiplicative.ofAdd ∘ (·.toList.length), by simp⟩ (fun _ _ _ _ h h' ↦ by
    simp only [FreeMonoid.ext_iff] at h ⊢
    exact List.append_inj h h'.1)

/-- Any `FreeAddMonoid` has the `TwoUniqueSums` property. -/
instance FreeAddMonoid.instTwoUniqueSums {κ : Type*} : TwoUniqueSums (FreeAddMonoid κ) :=
  .of_addHom ⟨(·.toList.length), by simp⟩ (fun _ _ _ _ h h' ↦ by
    simp only [FreeAddMonoid.ext_iff] at h ⊢
    exact List.append_inj h h'.1)
