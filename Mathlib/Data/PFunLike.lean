/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Data.SetLike.Basic

/-!
# Typeclass `PFunLike` for a type whose elements are partial functions

This typeclass is intended to be used in a similar way to `FunLike` but each function is partial,
i.e. it is defined over a subtype. It is implemented to allow for partial homomorphisms such as
`LinearPMap` to work with the same system as classical homomorphisms do.

This typeclass is **not** intended to be used as a generalization of `FunLike`, but rather as a
parallel system. The links between partial homomorphisms and classical homomorphisms should be
implemented separately.

## Implementation notes

As it is the case with `FunLike` the type class `PFunLike` should not be extended when defining
a new typeclass for partial homomorphisms, but rather added as an assumption. Here is an example
with the class of partial morphisms which map 0 to 0:

class ZeroPHomClass (F : Type*) (M γ N : outParam Type*) [SetLike γ M] [Zero M] [Zero N]
    [ZeroMemClass γ M] [PFunLike F M γ N] where
  pmap_zero : ∀ (f : F), f 0 = 0
-/

/-- The class `PFunLike F α γ β` expresses that a term `f : F` can be seen as a function from
`domain f` to `β`, where `domain f : γ` can be seen as a subset of `α` (see `SetLike`).

This typeclass is used in the definition of the homomorphism typeclasses,
such as `ZeroPHomClass`, `MulPHomClass`, `MonoidPHomClass`...
-/
class PFunLike (F : Type*) (α γ β : outParam Type*) [SetLike γ α] where
/-- Each `f : F` has a domain which is a subset of `α`. -/
domain : F → γ
/-- A coercion which sends each `f : F` to the corresponding map `α → β`. -/
coe : Π (f : F), (domain f) → β
coe_injective : Π (f g : F), domain f = domain g →
  (∀ (x : domain f) (y : domain g), (x : α) = (y : α) → coe f x = coe g y) → f = g

attribute [coe] PFunLike.coe

namespace PFunLike

variable {F α γ β : Type*} [SetLike γ α] [PFunLike F α γ β]

instance (priority := 100) CoeFun : CoeFun F (fun f ↦ domain f → β) := ⟨coe⟩

lemma ext {f g : F} (hd : domain f = domain g)
    (h : ∀ ⦃x : domain f⦄ ⦃y : domain g⦄, (x : α) = y → f x = g y) : f = g :=
  coe_injective f g hd h

lemma ext_iff {f g : F} :
    f = g ↔ domain f = domain g ∧ ∀ ⦃x : domain f⦄ ⦃y : domain g⦄, (x : α) = y → f x = g y where
  mp h := by cases h; simp
  mpr := fun ⟨hd, h⟩ ↦ ext hd h

end PFunLike
