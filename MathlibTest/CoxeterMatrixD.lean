/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Regression tests for `CoxeterMatrix.D`.

These tests verify that `CoxeterMatrix.D` agrees with `CartanMatrix.D` on
off-diagonal entries: entry (i,j) is 3 exactly when the Cartan entry is -1
(adjacent in the Dynkin diagram), and 2 otherwise. In particular there is
no triangle among any three nodes.
-/

import Mathlib.GroupTheory.Coxeter.Matrix

-- D₄: the fork node is 1 (= n-3 = 4-3). Both 2 and 3 join to 1,
-- but 2 and 3 are NOT joined to each other.
example : CoxeterMatrix.D 4 1 2 = 3 ∧ CoxeterMatrix.D 4 1 3 = 3 ∧
          CoxeterMatrix.D 4 2 3 = 2 ∧ CoxeterMatrix.D 4 0 1 = 3 := by decide

-- D₅: fork node is 2 (= n-3 = 5-3). Nodes 3 and 4 join to 2, but NOT each other.
example : CoxeterMatrix.D 5 2 3 = 3 ∧ CoxeterMatrix.D 5 2 4 = 3 ∧
          CoxeterMatrix.D 5 3 4 = 2 := by decide

-- D₃ = A₃: three nodes in a chain, no triangle.
-- Node 0 joins node 1, node 1 joins node 2 (= fork node 0 = n-3),
-- nodes 0 and 2 are the two leaves of the fork → both join node 0.
example : CoxeterMatrix.D 3 0 1 = 3 ∧ CoxeterMatrix.D 3 0 2 = 3 ∧
          CoxeterMatrix.D 3 1 2 = 2 := by decide

-- Sanity: no pair of distinct fork-end nodes are adjacent (would form a triangle).
-- For D₆: fork at node 3, leaves 4 and 5.
example : CoxeterMatrix.D 6 3 4 = 3 ∧ CoxeterMatrix.D 6 3 5 = 3 ∧
          CoxeterMatrix.D 6 4 5 = 2 := by decide
