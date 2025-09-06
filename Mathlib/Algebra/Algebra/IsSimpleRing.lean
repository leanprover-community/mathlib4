/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Eric Wieser
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Facts about algebras when the coefficient ring is a simple ring
-/

variable (R A : Type*) [CommRing R] [Semiring A] [Algebra R A] [IsSimpleRing R] [Nontrivial A]

instance : FaithfulSMul R A :=
  faithfulSMul_iff_algebraMap_injective R A |>.2 <| RingHom.injective _
