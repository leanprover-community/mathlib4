/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.Notation.Support

/-!
# Support of a function composed with a scalar action

We show that the support of `x ↦ f (c⁻¹ • x)` is equal to `c • support f`.
-/


open Pointwise

open Function Set

section Group

variable {α β γ : Type*} [Group α] [MulAction α β]

theorem mulSupport_comp_inv_smul [One γ] (c : α) (f : β → γ) :
    (mulSupport fun x ↦ f (c⁻¹ • x)) = c • mulSupport f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_mulSupport]

/- Note: to_additive also automatically translates `SMul` to `VAdd`, so we give the additive version
manually. -/
theorem support_comp_inv_smul [Zero γ] (c : α) (f : β → γ) :
    (support fun x ↦ f (c⁻¹ • x)) = c • support f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_support]

end Group

section GroupWithZero

variable {α β γ : Type*} [GroupWithZero α] [MulAction α β]

theorem mulSupport_comp_inv_smul₀ [One γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
    (mulSupport fun x ↦ f (c⁻¹ • x)) = c • mulSupport f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_mulSupport]

/- Note: to_additive also automatically translates `SMul` to `VAdd`, so we give the additive version
manually. -/
theorem support_comp_inv_smul₀ [Zero γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
    (support fun x ↦ f (c⁻¹ • x)) = c • support f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_support]

end GroupWithZero
