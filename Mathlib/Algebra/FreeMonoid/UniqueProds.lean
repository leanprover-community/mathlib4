/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.UniqueProds.Basic
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Free monoids have unique products
-/

@[expose] public section

assert_not_exists Cardinal Subsemiring Algebra Submodule StarModule

open Finset

/-- Any `FreeMonoid` has the `TwoUniqueProds` property. -/
instance FreeMonoid.instTwoUniqueProds {κ : Type*} : TwoUniqueProds (FreeMonoid κ) :=
  .of_mulHom ⟨Multiplicative.ofAdd ∘ List.length, fun _ _ ↦ congr_arg _ List.length_append⟩
    (fun _ _ _ _ h h' ↦ List.append_inj h <| Equiv.injective Multiplicative.ofAdd h'.1)

/-- Any `FreeAddMonoid` has the `TwoUniqueSums` property. -/
instance FreeAddMonoid.instTwoUniqueSums {κ : Type*} : TwoUniqueSums (FreeAddMonoid κ) :=
  .of_addHom ⟨_, fun _ _ => List.length_append⟩ (fun _ _ _ _ h h' ↦ List.append_inj h h'.1)
