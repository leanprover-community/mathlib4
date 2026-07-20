/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.FormulaGodel
public import Mathlib.SetTheory.ZFC.Constructible.SimpleF3F4
public import Mathlib.SetTheory.ZFC.Constructible.SimpleF6F8

/-!
# Equivalence of formula and rudimentary definability

This file proves Jensen's equivalence between first-order definable subsets of a transitive set
and the powerset-bounded closure under the nine basic Gödel operations.
-/

@[expose] public section

open Set

universe u

namespace Constructible.Godel

theorem isSimpleSetFunction_F0 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F0 (s 0) (s 1)) := by
  simpa [F0] using isSimpleSetFunction_pair.{u}

theorem isSimpleSetFunction_F1 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F1 (s 0) (s 1)) := by
  simpa [F1] using isSimpleSetFunction_sdiff.{u}

theorem isSimpleSetFunction_F5 :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => F5 (s 0) (s 1)) := by
  have h := isSimpleSetFunction_sUnion.compUnary
    (isSimpleSetFunction_projection.{u} (0 : Fin 2))
  simpa [F5] using h

theorem isSimpleSetFunction_op (i : Fin 9) :
    IsSimpleSetFunction
      (fun s : Tuple ZFSet.{u} 2 => op i (s 0) (s 1)) := by
  fin_cases i
  · simpa [op] using isSimpleSetFunction_F0.{u}
  · simpa [op] using isSimpleSetFunction_F1.{u}
  · simpa [op] using isSimpleSetFunction_F2.{u}
  · simpa [op] using isSimpleSetFunction_F3.{u}
  · simpa [op] using isSimpleSetFunction_F4.{u}
  · simpa [op] using isSimpleSetFunction_F5.{u}
  · simpa [op] using isSimpleSetFunction_F6.{u}
  · simpa [op] using isSimpleSetFunction_F7.{u}
  · simpa [op] using isSimpleSetFunction_F8.{u}

theorem godelDef_subset_DefZF {U : ZFSet.{u}}
    (hU : U.IsTransitive) :
    godelDef U ⊆ Constructible.DefZF U :=
  godelDef_subset_DefZF_of_simpleOps isSimpleSetFunction_op hU

/-- Jensen's final equivalence: formula definability over a transitive set is
exactly membership in the powerset-bounded rudimentary closure. -/
theorem DefZF_eq_godelDef {U : ZFSet.{u}} (hU : U.IsTransitive) :
    Constructible.DefZF U = godelDef U := by
  apply le_antisymm
  · exact DefZF_subset_godelDef hU
  · exact godelDef_subset_DefZF hU

end Constructible.Godel
