/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryGraph

/-!
# The bounded-section interface for the Gödel/Def bridge

The ambient graph of a composed rudimentary term may use intermediate values
outside a transitive carrier `U`.  The bridge to `DefZF U` therefore targets a
stronger certificate: an ambient `Δ₀` formula defining membership in the final
set, using only genuine members of `U` as parameters.

The substitution and generated-formula modules produce `Delta0Section` values;
`Delta0Section.mem_DefZF` is the final absoluteness step.
-/

@[expose] public section

universe u

namespace Constructible

open Delta0Formula

/--
A finite ambient `Δ₀` definition of the section of `z` over `U`.  Every entry
of `params` is a genuine member of `U`.
-/
structure Delta0Section (U z : ZFSet.{u}) where
  arity : Nat
  params : Tuple (ZFCarrier U) arity
  formula : Delta0Formula (arity + 1)
  correct : ∀ q : ZFCarrier U,
    Satisfies (fun x y : ZFSet.{u} => x ∈ y) formula
        (snoc (Delta0Formula.val params) q.1) ↔
      q.1 ∈ z

/--
For a transitive carrier, bounded absoluteness turns a `Delta0Section`
certificate into membership in the internally represented `DefZF U`.
-/
theorem Delta0Section.mem_DefZF {U z : ZFSet.{u}}
    (sec : Delta0Section U z) (hU : U.IsTransitive) (hzU : z ⊆ U) :
    z ∈ DefZF U := by
  rw [mem_DefZF_iff_exists_satisfies]
  refine ⟨hzU, sec.arity, sec.params, sec.formula.toFO, ?_⟩
  intro q
  rw [Delta0Formula.satisfies_toFO]
  have habs := Delta0Formula.satisfies_absolute hU sec.formula
    (snoc sec.params q)
  have habs' :
      Satisfies (zfCarrierMem U) sec.formula (snoc sec.params q) ↔
        Satisfies (fun x y : ZFSet.{u} => x ∈ y) sec.formula
          (snoc (Delta0Formula.val sec.params) q.1) := by
    simpa only [Delta0Formula.val_snoc] using habs
  exact (sec.correct q).symm.trans habs'.symm

namespace Godel

/-- Each primitive Gödel operation already supplies a bounded-section certificate. -/
def opDelta0Section {U x y : ZFSet.{u}} (i : Fin 9)
    (hx : x ∈ U) (hy : y ∈ U) : Delta0Section U (op i x y) where
  arity := 2
  params := ![⟨x, hx⟩, ⟨y, hy⟩]
  formula := memOpSectionFormula i
  correct := by
    intro q
    have hassign :
        snoc (Delta0Formula.val ![⟨x, hx⟩, ⟨y, hy⟩]) q.1 =
          ![x, y, q.1] := by
      funext j
      fin_cases j <;> rfl
    rw [hassign]
    exact satisfies_memOpSectionFormula i x y q.1

/-- The existing primitive-operation result factors through `Delta0Section`. -/
theorem op_mem_DefZF_viaDelta0Section {U x y : ZFSet.{u}} {i : Fin 9}
    (hU : U.IsTransitive) (hx : x ∈ U) (hy : y ∈ U)
    (hsub : op i x y ⊆ U) :
    op i x y ∈ DefZF U :=
  (opDelta0Section i hx hy).mem_DefZF hU hsub

end Godel

end Constructible
