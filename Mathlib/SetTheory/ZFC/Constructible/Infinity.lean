/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.BasicAxioms
public import Mathlib.SetTheory.ZFC.Constructible.Ordinals

/-!
# Infinity in the constructible universe

The standard von Neumann code `omega0.toZFSet` is constructible.  Its ordinal
membership characterization immediately gives the empty element and closure
under von Neumann successor.
-/

@[expose] public section

universe u

namespace Constructible.Model

/-- The standard von Neumann omega, packaged as a constructible set. -/
noncomputable def omegaLCarrier : LCarrier.{u} :=
  ⟨Ordinal.omega0.toZFSet, omega_mem_L⟩

theorem empty_mem_omegaLCarrier :
    emptyLCarrier.1 ∈ omegaLCarrier.1 := by
  simp only [emptyLCarrier, omegaLCarrier]
  rw [← Ordinal.toZFSet_zero]
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr Ordinal.omega0_pos

/-- Every member of omega has its von Neumann successor in omega. -/
theorem successor_mem_omegaLCarrier (x : LCarrier.{u})
    (hx : x.1 ∈ omegaLCarrier.1) :
    ∃ s : LCarrier.{u}, s.1 ∈ omegaLCarrier.1 ∧
      ∀ z : LCarrier.{u}, z.1 ∈ s.1 ↔ z.1 ∈ x.1 ∨ z = x := by
  change x.1 ∈ Ordinal.omega0.toZFSet at hx
  rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨beta, hbeta, hxbeta⟩
  let s : LCarrier.{u} :=
    ⟨(Order.succ beta).toZFSet, ordinal_toZFSet_mem_L (Order.succ beta)⟩
  refine ⟨s, ?_, ?_⟩
  · exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.isSuccLimit_omega0.succ_lt hbeta)
  · intro z
    change z.1 ∈ (Order.succ beta).toZFSet ↔
      z.1 ∈ x.1 ∨ z = x
    rw [Order.succ_eq_add_one, Ordinal.toZFSet_add_one,
      ZFSet.mem_insert_iff, hxbeta]
    simp only [Subtype.ext_iff, or_comm]

/-- The usual Infinity witness in the membership structure on `L`. -/
theorem lCarrier_infinity :
    ∃ w : LCarrier.{u},
      (∃ e : LCarrier.{u}, e.1 ∈ w.1 ∧
        ∀ z : LCarrier.{u}, z.1 ∉ e.1) ∧
      ∀ x : LCarrier.{u}, x.1 ∈ w.1 ->
        ∃ s : LCarrier.{u}, s.1 ∈ w.1 ∧
          ∀ z : LCarrier.{u}, z.1 ∈ s.1 ↔ z.1 ∈ x.1 ∨ z = x := by
  refine ⟨omegaLCarrier, ⟨emptyLCarrier, empty_mem_omegaLCarrier,
    not_mem_emptyLCarrier⟩, ?_⟩
  exact successor_mem_omegaLCarrier

end Constructible.Model
