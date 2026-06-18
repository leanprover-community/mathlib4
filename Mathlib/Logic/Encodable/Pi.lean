/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Vector.Basic
public import Mathlib.Logic.Equiv.Finset

/-!
# Encodability of Pi types

This file provides instances of `Encodable` for types of vectors and (dependent) functions:

* `Encodable.List.Vector.encodable`: vectors of length `n` (represented by lists) are encodable
* `Encodable.finArrow`: vectors of length `n` (represented by `Fin`-indexed functions) are encodable
* `Encodable.fintypeArrow`, `Encodable.fintypePi`: (dependent) functions with
  finite domain and countable codomain are encodable
-/

@[expose] public section

open List (Vector)
open Nat List

namespace Encodable

variable {α : Type*}

/-- If `α` is encodable, then so is `Vector α n`. -/
instance List.Vector.encodable [Encodable α] {n} : Encodable (List.Vector α n) :=
  inferInstanceAs <| Encodable (Subtype _)

/-- If `α` is countable, then so is `Vector α n`. -/
instance List.Vector.countable [Countable α] {n} : Countable (List.Vector α n) :=
  inferInstanceAs <| Countable (Subtype _)

/-- If `α` is encodable, then so is `Fin n → α`. -/
instance finArrow [Encodable α] {n} : Encodable (Fin n → α) :=
  ofEquiv _ (Equiv.vectorEquivFin _ _).symm

instance finPi (n) (π : Fin n → Type*) [∀ i, Encodable (π i)] : Encodable (∀ i, π i) :=
  ofEquiv _ (Equiv.piEquivSubtypeSigma (Fin n) π)

-- TODO: Unify with `fintypePi` and find a better name
/-- When `α` is finite and `β` is encodable, `α → β` is encodable too. Because the encoding is not
unique, we wrap it in `Trunc` to preserve computability. -/
def fintypeArrow (α : Type*) (β : Type*) [DecidableEq α] [Fintype α] [Encodable β] :
    Trunc (Encodable (α → β)) :=
  (Fintype.truncEquivFin α).map fun f =>
    Encodable.ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr f (Equiv.refl _)

/-- When `α` is finite and all `π a` are encodable, `Π a, π a` is encodable too. Because the
encoding is not unique, we wrap it in `Trunc` to preserve computability. -/
def fintypePi (α : Type*) (π : α → Type*) [DecidableEq α] [Fintype α] [∀ a, Encodable (π a)] :
    Trunc (Encodable (∀ a, π a)) :=
  (Fintype.truncEncodable α).bind fun a =>
    (@fintypeArrow α (Σ a, π a) _ _ (@Sigma.encodable _ _ a _)).bind fun f =>
      Trunc.mk <|
        @Encodable.ofEquiv _ _ (@Subtype.encodable _ _ f _)
          (Equiv.piEquivSubtypeSigma α π)

/-- If `α` and `β` are encodable and `α` is a fintype, then `α → β` is encodable as well. -/
instance fintypeArrowOfEncodable {α β : Type*} [Encodable α] [Fintype α] [Encodable β] :
    Encodable (α → β) :=
  ofEquiv (Fin (Fintype.card α) → β) <| Equiv.arrowCongr fintypeEquivFin (Equiv.refl _)

end Encodable
