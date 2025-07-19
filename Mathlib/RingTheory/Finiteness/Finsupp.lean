/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of finitely supported functions

-/

open Finsupp

variable {R V} [Semiring R] [AddCommMonoid V] [Module R V] {ι : Type*} [_root_.Finite ι]

instance Module.Finite.finsupp [Module.Finite R V] :
    Module.Finite R (ι →₀ V) :=
  Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R V ι).symm

variable (M : ι → Type*) [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)]

instance [∀ (i : ι), Module.Finite R (M i)] :
    Module.Finite R (Π₀ (i : ι), M i) :=
  letI : Fintype ι := Fintype.ofFinite _
  Module.Finite.equiv DFinsupp.linearEquivFunOnFintype.symm
