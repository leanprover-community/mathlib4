/-
Copyright (c) 2025 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.Holder

/-!
# The `L∞` (i.e. `Lp _ ⊤`) API and pointwise multiplication

This file develops the basic results specific to `Lp R ∞ μ` when `R` is a
`NormedRing`.  The main goal is to equip `L∞` with its natural pointwise multiplicative
structure (defined a.e.) and to register the constant embedding.  This is a small,
self-contained layer intended to be imported later by files that build richer structure
(e.g. the commutative C⋆-algebra structure when `R = 𝕜`).

## Main definitions

* `instance : Mul (Lp R ⊤ μ)` – pointwise (a.e.) multiplication on `L∞`.
* `Linfty.const : R →+ Lp R ⊤ μ` – additive monoid hom sending a scalar to the corresponding
  constant `L∞` function.

## Tags

Lp, L∞

-/

namespace MeasureTheory

open ENNReal

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {R : Type*} [NormedRing R]

section Mul

noncomputable instance : Mul (Lp R ∞ μ) where
  mul f g := f • g

lemma Linfty.coeFn_mul (f g : Lp R ∞ μ) : f * g =ᵐ[μ] ⇑f * g :=
  Lp.coeFn_lpSMul f g

end Mul

section Const

/-- Note: Unlike for general Lp, this does not require `IsFiniteMeasure` instance. -/
theorem memLinfty_const (c : R) : MemLp (fun _ : α => c) ∞ μ := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases hμ : μ = 0
  · simp [hμ]
  · rw [eLpNorm_const c (ENNReal.top_ne_zero) hμ]
    simp

theorem const_mem_Linfty (c : R) :
    @AEEqFun.const α _ _ μ _ c ∈ Lp R ∞ μ :=
  (memLinfty_const c).eLpNorm_mk_lt_top

def Linfty.const : R →+ Lp R ∞ μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Linfty c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma Linfty.const_val (c : R) : (Linfty.const c).1 = AEEqFun.const (β := R) (μ := μ) α c := rfl

lemma Linfty.coeFn_const (c : R) : Linfty.const (μ := μ) c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c

end Const

end MeasureTheory
