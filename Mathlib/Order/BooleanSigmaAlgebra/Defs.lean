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

A σ-complete lattice is a lattice in which every countable subset `s` has a least upper bound and a
greatest lower bound, denoted below by `sSup s` and `sInf s`. This is an intermediate type class
used to define Boolean σ-algebras.

A Boolean σ-algebra is both a Boolean algebra and a σ-complete lattice.

The theory is very comparable to the theory of complete Boolean algebras, except that suitable
countability assumptions have to be added.

To differentiate the statements between complete Boolean algebras and Boolean σ-algebras, we prefix
`sInf` and `sSup` in the statements by `σ`, giving `σsInf` and `σsSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `σsInf_le` is the same statement in Boolean σ-algebras with an additional assumption that `s`
is countable.

## Typeclasses

* `SigmaCompleteLattice`: σ-complete lattice: A lattice closed under the formation of countable
  suprema and infima.
* `BooleanSigmaAlgebra`: Boolean σ-algebra: A Boolean algebra closed under the formation of
  countable suprema and infima.
-/

variable {α : Type*}

/-- A σ-complete lattice is a `Lattice` in which every countable subset has a supremum and an
infimum.

To differentiate the statements from the corresponding statements in `CompleteLattice` or
`ConditionallyCompleteLattice`, we prefix `sInf` and `sSup` by a `σ` everywhere. Most statements
should hold in both worlds, usually with additional assumptions of countability.

Note that `sSup s` and `sInf s` are only guaranteed to be the supremum and the infifmum of `s` when
`s` is countable. If `s` is not countable and `IsLUB s a` is true, then `sSup s = a` might not hold.
-/
class SigmaCompleteLattice (α) extends Lattice α, SupSet α, InfSet α, BoundedOrder α where
  /-- Any countable set has its supremum as a least upper bound. -/
  isLUB_σsSup (s : Set α) (hs : s.Countable) : IsLUB s (sSup s)
  /-- Any countable set has its infimum as a greatest lower bound. -/
  isGLB_σsInf (s : Set α) (hs : s.Countable) : IsGLB s (sInf s)

/-- A complete lattice is a σ-complete lattice. -/
instance (priority := 100) CompleteLattice.toSigmaCompleteLattice [CompleteLattice α] :
    SigmaCompleteLattice α where
  isLUB_σsSup s _ := isLUB_sSup s
  isGLB_σsInf s _ := isGLB_sInf s

instance OrderDual.instSigmaCompleteLattice [SigmaCompleteLattice α] :
    SigmaCompleteLattice αᵒᵈ where
  isLUB_σsSup (s : Set α) hs := (SigmaCompleteLattice.isGLB_σsInf s hs).dual
  isGLB_σsInf (s : Set α) hs := (SigmaCompleteLattice.isLUB_σsSup s hs).dual

/-- A Boolean σ-algebra is a `BooleanAlgebra` and a `SigmaCompleteLattice`.

To differentiate the statements from the corresponding statements in `CompleteBooleanAlgebra`, we
prefix `sInf` and `sSup` by a `σ` everywhere. Most statements should hold in both worlds, usually
with additional assumptions of countability. -/
class BooleanSigmaAlgebra (α) extends BooleanAlgebra α, SigmaCompleteLattice α

/-- A complete Boolean algebra is a Boolean σ-algebra. -/
instance (priority := 100) CompleteBooleanAlgebra.toBooleanSigmaAlgebra [CompleteBooleanAlgebra α] :
    BooleanSigmaAlgebra α where
  isLUB_σsSup (s : Set α) _ := isLUB_sSup s
  isGLB_σsInf (s : Set α) _ := isGLB_sInf s

instance OrderDual.instBooleanSigmaAlgebra (α : Type*) [BooleanSigmaAlgebra α] :
    BooleanSigmaAlgebra αᵒᵈ where
  toBooleanAlgebra := inferInstance
  toSupSet := inferInstance
  toInfSet := inferInstance
  isLUB_σsSup (s : Set α) (hs : s.Countable) := IsGLB.dual (BooleanSigmaAlgebra.isGLB_σsInf s hs)
  isGLB_σsInf (s : Set α) (hs : s.Countable) := IsLUB.dual (BooleanSigmaAlgebra.isLUB_σsSup s hs)
