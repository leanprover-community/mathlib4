/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
In this file we provide various simp lemmas in its elementwise form via `Tactic.Elementwise`.
-/
set_option backward.defeqAttrib.useBackward true

public section


open CategoryTheory CategoryTheory.Limits

attribute [elementwise] limit.lift_π limit.w
  colimit.ι_desc colimit.w kernel.lift_ι cokernel.π_desc kernel.condition cokernel.condition

attribute [simp] limit.lift_π_apply limit.w_apply colimit.ι_desc_apply colimit.w_apply
  kernel.lift_ι_apply cokernel.π_desc_apply kernel.condition_apply cokernel.condition_apply
