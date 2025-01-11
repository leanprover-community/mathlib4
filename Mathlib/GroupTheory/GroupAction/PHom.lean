/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Data.PFunLike
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Partial equivariant homomorphisms

## Main definitions

* `MulActionPSemiHomClass F φ X γ Y` states that `F` is a type of partial bundled `X → Y` homs
  which are `φ`-equivariant and whose domains are of type `γ`;
  `AddActionPSemiHomClass F φ X Y` is its additive version.
* `MulActionHomClass F M X γ Y` is an abbrev for `MulActionPSemiHomClass F id X γ Y`.
-/

/-- `MulActionPSemiHomClass F φ X γ Y` states that `F` is a type of partial bundled `X → Y` homs
  which are `φ`-equivariant and whose domains are of type `γ`. -/
class AddActionPSemiHomClass (F : Type*) {M N : outParam Type*} (φ : outParam (M → N))
    (X γ Y : outParam Type*) [SetLike γ X] [VAdd M X] [VAdd N Y] [PFunLike F X γ Y]
    [VAddMemClass γ M X] where
  pmap_vaddₛₗ : ∀ (f : F) (c : M) (x : PFunLike.domain f), f (c +ᵥ x) = φ c +ᵥ f x

export AddActionPSemiHomClass (pmap_vaddₛₗ)

/-- `AddActionPSemiHomClass F φ X γ Y` states that `F` is a type of partial bundled `X → Y` homs
  which are `φ`-equivariant and whose domains are of type `γ`. -/
@[to_additive]
class MulActionPSemiHomClass (F : Type*) {M N : outParam Type*} (φ : outParam (M → N))
    (X γ Y : outParam Type*) [SetLike γ X] [SMul M X] [SMul N Y] [PFunLike F X γ Y]
    [SMulMemClass γ M X] where
  pmap_smulₛₗ : ∀ (f : F) (c : M) (x : PFunLike.domain f), f (c • x) = φ c • f x

export MulActionPSemiHomClass (pmap_smulₛₗ)

/-- `MulActionHomClass F M X γ Y` is an abbrev for `MulActionPSemiHomClass F id X γ Y`. -/
@[to_additive "`AddActionHomClass F M X γ Y` is an abbrev for `AddActionPSemiHomClass F id X γ Y`."]
abbrev MulActionPHomClass (F : Type*) (M X γ Y : outParam Type*) [SetLike γ X]
    [SMul M X] [SMul M Y] [PFunLike F X γ Y] [SMulMemClass γ M X] :=
  MulActionPSemiHomClass F (@id M) X γ Y

@[to_additive (attr := simp)]
lemma pmap_smul {F M X γ Y : Type*} [SetLike γ X] [SMul M X] [SMul M Y] [PFunLike F X γ Y]
    [SMulMemClass γ M X] [MulActionPHomClass F M X γ Y]
    (f : F) (c : M) (x : PFunLike.domain f) : f (c • x) = c • f x := pmap_smulₛₗ f c x
