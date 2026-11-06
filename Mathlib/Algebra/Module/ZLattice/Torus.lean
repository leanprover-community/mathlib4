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
# The quotient of a real vector space by a `ℤ`-lattice is a torus

Let `E` be a finite-dimensional real normed space and `L` a `ℤ`-lattice in `E`. Then `E ⧸ L` is
isomorphic, as an additive group, to the unit additive torus indexed by
`Module.Free.ChooseBasisIndex ℤ L`.

## Main definitions

* `ZLattice.quotientAddEquivUnitAddTorus`: the additive equivalence
  `E ⧸ L ≃+ UnitAddTorus (Module.Free.ChooseBasisIndex ℤ L)` sending the class of `x` to its
  coordinates modulo `1` in the basis `Module.Free.chooseBasis ℤ L`.

## TODO

Promote `ZLattice.quotientAddEquivUnitAddTorus` to a `ContinuousAddEquiv`. This requires
continuous versions of `Submodule.Quotient.equiv` and `Submodule.quotientPi`.
-/

@[expose] public section

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

namespace Module.Basis

variable {ι : Type*} [Finite ι] (b : Basis ι ℤ L)

/-- The coordinate map `E ≃ₗ[ℝ] ι → ℝ` of the basis `b.ofZLatticeBasis ℝ` sends `L` onto the
standard integer lattice in `ι → ℝ`. -/
theorem map_equivFun_ofZLatticeBasis :
    L.map ((b.ofZLatticeBasis ℝ).equivFun.restrictScalars ℤ : E →ₗ[ℤ] ι → ℝ) =
      .pi .univ fun _ ↦ ℤ ∙ (1 : ℝ) := by
  classical
  conv_lhs => arg 2; rw [← b.ofZLatticeBasis_span ℝ]
  simp [-ofZLatticeBasis_apply, Submodule.map_span, Submodule.span_range_eq_iSup,
    ← Submodule.iSup_map_single, Finsupp.single_eq_pi_single]

end Module.Basis

namespace ZLattice

variable (L) in
/-- The additive equivalence between `E ⧸ L` and the unit additive torus, sending the class of `x`
to its coordinates modulo `1` in the basis `Module.Free.chooseBasis ℤ L`. -/
noncomputable def quotientAddEquivUnitAddTorus :
    (E ⧸ L) ≃+ UnitAddTorus (Free.ChooseBasisIndex ℤ L) :=
  let b := Free.chooseBasis ℤ L
  ((Submodule.Quotient.equiv L _ ((b.ofZLatticeBasis ℝ).equivFun.restrictScalars ℤ)
    b.map_equivFun_ofZLatticeBasis).trans (Submodule.quotientPi _)).toAddEquiv.trans <|
      .piCongrRight fun _ ↦ QuotientAddGroup.quotientAddEquivOfEq <|
        Submodule.span_singleton_toAddSubgroup_eq_zmultiples 1

@[simp]
theorem quotientAddEquivUnitAddTorus_mk (x : E) (i : Free.ChooseBasisIndex ℤ L) :
    quotientAddEquivUnitAddTorus L (Submodule.Quotient.mk x) i =
      ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ).repr x i :=
  rfl

end ZLattice
