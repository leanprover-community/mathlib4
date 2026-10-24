/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# A module over a division ring is simple iff it has rank one
-/

public section

theorem isSimpleModule_iff_finrank_eq_one {R M} [DivisionRing R] [AddCommGroup M] [Module R M] :
    IsSimpleModule R M ↔ Module.finrank R M = 1 :=
  ⟨fun h ↦ have := h.nontrivial; have ⟨v, hv⟩ := exists_ne (0 : M)
    (finrank_eq_one_iff_of_nonzero' v hv).mpr (IsSimpleModule.toSpanSingleton_surjective R hv),
  (isSimpleModule_iff ..).mpr ∘ is_simple_module_of_finrank_eq_one⟩

section Quotient

variable {R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]

open Submodule
/- If a submodule has a simple quotient, then it has a complement
    of the form `R • x` for some `x ≠ 0`.-/
theorem isCompl_of_quot_isSimpleModule
    {p : Submodule R M} (h : IsSimpleModule R (M ⧸ p)) :
    ∃ x : M, x ∉ p ∧ IsCompl p (span R {x}) := by
  have := IsSimpleModule.nontrivial R (M ⧸ p)
  have ⟨y, hy⟩ := exists_ne (0 : M ⧸ p)
  obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_surjective p) y
  use x
  have xnotinp : x ∉ p:= by
    apply (Quotient.mk_eq_zero p (x:=x)).not.mp
    simpa [hx] using hy
  constructor
  · exact xnotinp
  · refine isCompl_span_singleton_of_isCoatom_of_notMem (s:=p)
      ((isSimpleModule_iff_isCoatom (m:=p)).mp h) xnotinp

end Quotient
