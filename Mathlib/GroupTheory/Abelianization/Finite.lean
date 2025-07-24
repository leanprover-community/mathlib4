/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes, Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Coset.Card

/-!
# The abelianization of a finite group is finite
-/

variable {G : Type*} [Group G]

instance [Fintype G] [DecidablePred (· ∈ commutator G)] : Fintype (Abelianization G) :=
  QuotientGroup.fintype (commutator G)

instance [Finite G] : Finite (Abelianization G) :=
  Quotient.finite _
