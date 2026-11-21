/-
Copyright (c) 2026 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.RingTheory.FilteredAlgebra.Basic

import Mathlib.Algebra.Algebra.Operations

/-!
# Relations between graded rings and filtered rings

In this file, we introduce the filtered ring attached to a graded ring, when the grading is by an
ordered additive commutative monoid.

## TODO

* Define Rees algebra `⨁ i, F i` of a filtered ring (possibly generalizing away from rings)
* Define associated graded

-/

public section

noncomputable section

universe u v w

variable {ι : Type v} {R : Type w} {A : Type u}

section

variable [AddCommMonoid ι] [PartialOrder ι] [CommSemiring R]
  [Semiring A] [Algebra R A] (F : ι → Submodule R A) [SetLike.GradedMonoid F]

lemma isRingFiltration_of_graded [AddLeftMono ι] :
    IsRingFiltration (fun i ↦ ⨆ j ≤ i, F j) (fun i ↦ ⨆ j < i, F j) where
  mono _ j h := biSup_mono fun _ hk ↦ hk.trans h
  is_le {_ j} h := biSup_mono fun _ hk ↦ hk.trans_lt h
  is_sup _ _ h :=
    iSup₂_le fun k hk ↦ (le_iSup₂ (f := fun j (_ : j ≤ k) ↦ F j) k le_rfl).trans (h k hk)
  one_mem := le_iSup₂ (f := fun j (_ : j ≤ 0) ↦ F j) 0 le_rfl (SetLike.one_mem_graded F)
  mul_mem {i j} _ _ hx hy := by
    suffices (⨆ k ≤ i, F k) * (⨆ l ≤ j, F l) ≤ ⨆ m ≤ i + j, F m from
      this (Submodule.mul_mem_mul hx hy)
    simp_rw [Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
    exact fun k hk l hl ↦ le_iSup₂_of_le (k + l) (add_le_add hk hl)
      (Submodule.mul_le.mpr fun _ ha _ hb ↦ SetLike.mul_mem_graded ha hb)

end
