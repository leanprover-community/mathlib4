/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.RingTheory.Smooth.Pi
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!

# Formal-étaleness of finite products of rings

## Main result

- `Algebra.FormallyEtale.pi_iff`: If `I` is finite, `Π i : I, A i` is `R`-formally-étale
  if and only if each `A i` is `R`-formally-étale.

-/

@[expose] public section

namespace Algebra.FormallyEtale

variable {R : Type*} {I : Type*} (A : I → Type*)
variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]

theorem pi_iff [Finite I] :
    FormallyEtale R (Π i, A i) ↔ ∀ i, FormallyEtale R (A i) := by
  simp_rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth, forall_and]
  rw [FormallyUnramified.pi_iff A, FormallySmooth.pi_iff A]

instance [Finite I] [∀ i, FormallyEtale R (A i)] : FormallyEtale R (Π i, A i) :=
  .of_formallyUnramified_and_formallySmooth

instance [Finite I] [∀ i, Etale R (A i)] : Etale R (Π i, A i) where

end Algebra.FormallyEtale
