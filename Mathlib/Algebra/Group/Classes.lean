/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Algebra.Classes

/-!
# Instances for operations in algebraic structures.

As the unbundled algebraic structures typeclasses are of somewhat dubious use at present,
we separate out the file providing instances from the main `Mathlib.Algebra.Group.Defs` file.
-/

#align_import algebra.group.defs from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

variable {G : Type*}

@[to_additive]
instance Semigroup.to_isAssociative [Semigroup G] : IsAssociative G (· * ·) :=
  ⟨mul_assoc⟩
#align semigroup.to_is_associative Semigroup.to_isAssociative
#align add_semigroup.to_is_associative AddSemigroup.to_isAssociative

@[to_additive]
instance CommMagma.to_isCommutative [CommMagma G] : IsCommutative G (· * ·) := ⟨mul_comm⟩
#align comm_semigroup.to_is_commutative CommMagma.to_isCommutative
#align add_comm_semigroup.to_is_commutative AddCommMagma.to_isCommutative
