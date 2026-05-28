/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Quotients by `IsZLattice`s are tori

The quotient of a finite-dimensional real normed space `E` by an `IsZLattice ℝ L` is
isomorphic, as an additive group, to a unit additive torus, with index type given by
`Module.Free.ChooseBasisIndex ℤ L`.

## Main definitions

* `IsZLattice.quotientAddEquivUnitAddTorus`: the additive equivalence
  `E ⧸ L ≃+ UnitAddTorus (Module.Free.ChooseBasisIndex ℤ L)`.

## Future work

Promoting to a `ContinuousAddEquiv` requires continuous versions of
`Submodule.Quotient.equiv` and `Submodule.quotientPi` not yet in Mathlib.
-/

@[expose] public section

namespace IsZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Finite ι] (b : Module.Basis ι ℤ L)

/-- The image of `L` under the basis-induced equivalence `E ≃ₗ[ℝ] ι → ℝ` is the standard
integer lattice in `ι → ℝ`. -/
theorem map_basis_equivFun_eq :
    Submodule.map ((b.ofZLatticeBasis ℝ).equivFun.toLinearMap.restrictScalars ℤ : E →ₗ[ℤ] ι → ℝ) L =
      Submodule.pi (Set.univ : Set ι) (fun _ : ι ↦ ℤ ∙ (1 : ℝ)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  set b' := b.ofZLatticeBasis ℝ
  rw [show L = Submodule.span ℤ (Set.range b') from (b.ofZLatticeBasis_span ℝ).symm]
  simp [Submodule.map_span, Submodule.span_range_eq_iSup, ← Submodule.iSup_map_single,
    Finsupp.single_eq_pi_single]

/-- The additive equivalence between `E ⧸ L` and the unit additive torus, using the canonical
choice of `ℤ`-basis of `L` from `Module.Free.chooseBasis`. -/
noncomputable def quotientAddEquivUnitAddTorus :
    (E ⧸ L) ≃+ UnitAddTorus (Module.Free.ChooseBasisIndex ℤ L) := by
  let b := Module.Free.chooseBasis ℤ L
  exact (Submodule.Quotient.equiv L _ ((b.ofZLatticeBasis ℝ).equivFun.restrictScalars ℤ)
        (map_basis_equivFun_eq b)).trans (Submodule.quotientPi _) |>.toAddEquiv.trans <|
      .piCongrRight fun _ ↦ QuotientAddGroup.quotientAddEquivOfEq <|
        Submodule.span_singleton_toAddSubgroup_eq_zmultiples (1 : ℝ)

end IsZLattice
