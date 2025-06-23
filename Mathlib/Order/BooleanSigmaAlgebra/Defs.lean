/-
Copyright (c) 2025 Pierre Quinton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Quinton
-/
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Countable

/-!
# Definitions of Boolean σ-algebras

A Boolean σ-algebra is a Boolean algebra in which every countable subset `s` has a least upper bound
and a greatest lower bound, denoted below by `sSup s` and `sInf s`. This provides a natural
generalization for σ-algebras.

The theory is very comparable to the theory of complete Boolean algebras, except that suitable
countability have to be added to most statements.

To differentiate the statements between complete Boolean algebras and Boolean σ-algebras, we prefix
`sInf` and `sSup` in the statements by `σ`, giving `σsInf` and `σsSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `σsInf_le` is the same statement in Boolean σ-algebras with an additional assumption that `s`
is countable.
-/

universe u

variable {α : Type u}

/-- A Boolean σ-algebra is a `BooleanAlgebra` in which every countable subset has a supremum and an
infimum.

To differentiate the statements from the corresponding statements in `CompleteBooleanAlgebra`, we
prefix `sInf` and `sSup` by a `σ` everywhere. Most statements should hold in both worlds, usually
with additional assumptions of countability. -/
class BooleanσAlgebra (α) extends BooleanAlgebra α, SupSet α, InfSet α where
  isLUB_σsSup (s : Set α) (hs : s.Countable) : IsLUB s (sSup s)
  isGLB_σsInf (s : Set α) (hs : s.Countable) : IsGLB s (sInf s)

/-- A complete Boolean algebra is a Boolean σ-algebra. -/
instance (priority := 100) CompleteBooleanAlgebra.toBooleanσAlgebra [CompleteBooleanAlgebra α] :
    BooleanσAlgebra α where
  isLUB_σsSup (s : Set α) _ := isLUB_sSup s
  isGLB_σsInf (s : Set α) _ := isGLB_sInf s
