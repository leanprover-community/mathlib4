/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# Facts about algebras when the coefficient ring is a simple ring
-/

@[expose] public section

variable (R A : Type*) [CommRing R] [Semiring A] [Algebra R A] [IsSimpleRing R] [Nontrivial A]

instance : FaithfulSMul R A :=
  faithfulSMul_iff_algebraMap_injective R A |>.2 <| RingHom.injective _
