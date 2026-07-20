/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Separation

/-!
# Formula-defined constructible sets

This file provides the generic bridge from external descriptions to internal
constructible sets.  If all members of a `ZFSet` are constructible and, on
the domain `L`, membership in that set is expressed by one fixed first-order
formula with constructible parameters, then the set itself belongs to `L`.

The restriction of the defining equivalence to `x ∈ L` is intentional:
`Model.SatisfiesIn L` restricts quantified variables, but it does not require
the free variables in an externally supplied assignment to belong to `L`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/--
A `ZFSet` whose members are constructible and whose membership relation is
first-order definable over `L`, with constructible parameters, belongs to `L`.

The defining equivalence is only needed for candidate elements in `L`.
-/
theorem mem_L_of_formula_definition_on_L {n : Nat} {s : ZFSet.{u}}
    (phi : FOFormula (n + 1)) (params : Tuple ZFSet.{u} n)
    (hs : ∀ x ∈ s, x ∈ L) (hparams : ∀ i, params i ∈ L)
    (hdef : ∀ x, x ∈ L →
      (x ∈ s ↔ Model.SatisfiesIn L phi (snoc params x))) :
    s ∈ L := by
  rcases exists_LStage_for_members hs with ⟨alpha, halpha⟩
  rcases exists_separation phi params hparams (LStageZF_mem_L alpha) with
    ⟨t, htL, ht⟩
  have hst : s = t := by
    apply ZFSet.ext
    intro x
    rw [ht x]
    constructor
    · intro hxs
      exact ⟨halpha x hxs, (hdef x (hs x hxs)).mp hxs⟩
    · rintro ⟨hxStage, hxFormula⟩
      have hxL : x ∈ L :=
        LStageZF_subset_constructibleUniverse alpha hxStage
      exact (hdef x hxL).mpr hxFormula
  rw [hst]
  exact htL

/--
Convenience form when the formula characterizes membership for every raw
`ZFSet`, rather than merely for elements of `L`.
-/
theorem mem_L_of_formula_definition {n : Nat} {s : ZFSet.{u}}
    (phi : FOFormula (n + 1)) (params : Tuple ZFSet.{u} n)
    (hs : ∀ x ∈ s, x ∈ L) (hparams : ∀ i, params i ∈ L)
    (hdef : ∀ x,
      (x ∈ s ↔ Model.SatisfiesIn L phi (snoc params x))) :
    s ∈ L :=
  mem_L_of_formula_definition_on_L phi params hs hparams
    (fun x _hxL => hdef x)

namespace Model

/--
Subtype-semantics version of `mem_L_of_formula_definition_on_L`.

The set being constructed is still a raw `ZFSet`; the parameters, candidate
elements, and defining satisfaction statement are presented directly in the
first-order structure `LCarrier`.
-/
theorem mem_L_of_formula_definition_lCarrier {n : Nat} {s : ZFSet.{u}}
    (phi : FOFormula (n + 1)) (params : Tuple LCarrier.{u} n)
    (hs : ∀ x ∈ s, x ∈ L)
    (hdef : ∀ x : LCarrier.{u},
      (x.1 ∈ s ↔
        FOFormula.Satisfies
          (fun z w : LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc params x))) :
    s ∈ L := by
  let rawParams : Tuple ZFSet.{u} n := fun i => (params i).1
  apply mem_L_of_formula_definition_on_L phi rawParams hs
    (fun i => (params i).2)
  intro x hxL
  let xL : LCarrier.{u} := ⟨x, hxL⟩
  have hbridge := satisfies_lCarrier_iff_satisfiesIn_L phi (snoc params xL)
  have hbridgeRaw :
      FOFormula.Satisfies
          (fun z w : LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc params xL) ↔
        SatisfiesIn L phi (snoc rawParams x) := by
    simpa only [subtypeVal_snoc] using hbridge
  exact (hdef xL).trans hbridgeRaw

end Model

end ZFC

end Constructible
