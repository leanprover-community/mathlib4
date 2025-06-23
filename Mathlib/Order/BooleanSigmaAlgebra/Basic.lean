/-
Copyright (c) 2025 Pierre Quinton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Quinton
-/
import Mathlib.Order.BooleanSigmaAlgebra.Defs

/-!
# Theory of Boolean σ-algebras

A Boolean σ-algebra is a Booleanalgebra in which every countable subset `s` has a least upper bound
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


