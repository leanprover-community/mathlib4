/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
In this file we provide various simp lemmas in its elementwise form via `Tactic.Elementwise`.
-/


open CategoryTheory CategoryTheory.Limits

set_option linter.existingAttributeWarning false in
attribute [elementwise (attr := simp)] Cone.w limit.lift_π limit.w
  colimit.ι_desc colimit.w kernel.lift_ι cokernel.π_desc kernel.condition cokernel.condition

attribute [elementwise] Cocone.w
