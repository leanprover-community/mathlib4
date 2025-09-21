/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/


open Filter Set

open Topology

variable {α : Type*}

set_option linter.deprecated false in
/-- A `NormedOrderedAddGroup` is an additive group that is both a `NormedAddCommGroup` and an
`OrderedAddCommGroup`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[deprecated "Use `[NormedAddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]` instead."
  (since := "2025-04-10")]
structure NormedOrderedAddGroup (α : Type*) extends
    OrderedAddCommGroup α, Norm α, MetricSpace α where
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop

set_option linter.deprecated false in
set_option linter.existingAttributeWarning false in
/-- A `NormedOrderedGroup` is a group that is both a `NormedCommGroup` and an
`OrderedCommGroup`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[to_additive,
  deprecated "Use `[NormedCommGroup α] [PartialOrder α] [IsOrderedMonoid α]` instead."
  (since := "2025-04-10")]
structure NormedOrderedGroup (α : Type*) extends OrderedCommGroup α, Norm α, MetricSpace α where
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop

set_option linter.deprecated false in
set_option linter.existingAttributeWarning false in
/-- A `NormedLinearOrderedAddGroup` is an additive group that is both a `NormedAddCommGroup`
and a `LinearOrderedAddCommGroup`. This class is necessary to avoid diamonds caused by both
classes carrying their own group structure. -/
@[deprecated "Use `[NormedAddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]` instead."
  (since := "2025-04-10")]
structure NormedLinearOrderedAddGroup (α : Type*) extends LinearOrderedAddCommGroup α, Norm α,
  MetricSpace α where
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop

set_option linter.deprecated false in
set_option linter.existingAttributeWarning false in
/-- A `NormedLinearOrderedGroup` is a group that is both a `NormedCommGroup` and a
`LinearOrderedCommGroup`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[to_additive,
  deprecated "Use `[NormedCommGroup α] [LinearOrder α] [IsOrderedMonoid α]` instead."
  (since := "2025-04-10")]
structure NormedLinearOrderedGroup (α : Type*) extends LinearOrderedCommGroup α, Norm α,
  MetricSpace α where
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop

set_option linter.deprecated false in
set_option linter.existingAttributeWarning false in
/-- A `NormedLinearOrderedField` is a field that is both a `NormedField` and a
`LinearOrderedField`. This class is necessary to avoid diamonds. -/
@[deprecated "Use `[NormedField α] [LinearOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2025-04-10")]
structure NormedLinearOrderedField (α : Type*) extends LinearOrderedField α, Norm α,
  MetricSpace α where
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop
  /-- The norm is multiplicative. -/
  norm_mul : ∀ x y : α, ‖x * y‖ = ‖x‖ * ‖y‖
