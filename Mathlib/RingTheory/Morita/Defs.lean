/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Morita Equivalence

This file defines the Morita Equivalence between (non-commutative) rings
as the equivalence between module categories defined on them.

## Reference

* [Nathan Jacobson, Basic Algebra II (2nd edition)]

## Tags

Morita Equivalence, Category Theory, Noncommutative Algebra

-/

/-- Two rings are morita-equivalent if there exists an equivalence between
  the module category defined on them.-/
class IsMoritaEquivalent
  (R S : Type*) [Ring R] [Ring S] : Prop where
out : Nonempty <| ModuleCat R ≌ ModuleCat S
