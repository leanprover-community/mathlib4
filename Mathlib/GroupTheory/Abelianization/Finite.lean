/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coset.Card

/-!
# The abelianization of a finite group is finite
-/

public section

variable {G : Type*} [Group G]

instance [Fintype G] [DecidablePred (· ∈ commutator G)] : Fintype (Group.Abelianization G) :=
  QuotientGroup.fintype (commutator G)

instance [Finite G] : Finite (Group.Abelianization G) :=
  Quotient.finite _
