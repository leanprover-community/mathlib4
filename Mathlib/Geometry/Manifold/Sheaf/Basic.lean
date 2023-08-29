/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Topology.Sheaves.LocalPredicate

#align_import geometry.manifold.sheaf.basic from "leanprover-community/mathlib"@"431589bce478b2229eba14b14a283250428217db"

/-! # Generic construction of a sheaf from a `LocalInvariantProp` on a manifold

This file constructs the sheaf-of-types of functions `f : M → M'` (for charted spaces `M`, `M'`)
which satisfy the lifted property `LiftProp P` associated to some locally invariant (in the sense
of `StructureGroupoid.LocalInvariantProp`) property `P` on the model spaces of `M` and `M'`. For
example, differentiability and smoothness are locally invariant properties in this sense, so this
construction can be used to construct the sheaf of differentiable functions on a manifold and the
sheaf of smooth functions on a manifold.

The mathematical work is in associating a `TopCat.LocalPredicate` to a
`StructureGroupoid.LocalInvariantProp`: that is, showing that a differential-geometric "locally
invariant" property is preserved under restriction and gluing.

## Main definitions

* `StructureGroupoid.LocalInvariantProp.localPredicate`: the `TopCat.LocalPredicate` (in the
  sheaf-theoretic sense) on functions from open subsets of `M` into `M'`, which states whether
  such functions satisfy `LiftProp P`.
* `StructureGroupoid.LocalInvariantProp.sheaf`: the sheaf-of-types of functions `f : M → M'`
  which satisfy the lifted property `LiftProp P`.
-/


open scoped Manifold Topology

open Set TopologicalSpace StructureGroupoid StructureGroupoid.LocalInvariantProp Opposite

universe u

variable {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : StructureGroupoid H} {G' : StructureGroupoid H'} {P : (H → H') → Set H → H → Prop}
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M] (M' : Type u) [TopologicalSpace M']
  [ChartedSpace H' M']

instance TopCat.of.chartedSpace : ChartedSpace H (TopCat.of M) :=
  (inferInstance : ChartedSpace H M)
set_option linter.uppercaseLean3 false in
#align Top.of.charted_space TopCat.of.chartedSpace

instance TopCat.of.hasGroupoid [HasGroupoid M G] : HasGroupoid (TopCat.of M) G :=
  (inferInstance : HasGroupoid M G)
set_option linter.uppercaseLean3 false in
#align Top.of.has_groupoid TopCat.of.hasGroupoid

/-- Let `P` be a `LocalInvariantProp` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
an induced `LocalPredicate` on the functions from `M` to `M'`, given by `LiftProp P`. -/
def StructureGroupoid.LocalInvariantProp.localPredicate (hG : LocalInvariantProp G G' P) :
    TopCat.LocalPredicate fun _ : TopCat.of M => M' where
  pred {U : Opens (TopCat.of M)} := fun f : U → M' => ChartedSpace.LiftProp P f
  res := by
    intro U V i f h x
    -- ⊢ ChartedSpace.LiftPropAt P (fun x => f ((fun x => { val := ↑x, property := (_ …
    have hUV : U ≤ V := CategoryTheory.leOfHom i
    -- ⊢ ChartedSpace.LiftPropAt P (fun x => f ((fun x => { val := ↑x, property := (_ …
    show ChartedSpace.LiftPropAt P (f ∘ Set.inclusion hUV) x
    -- ⊢ ChartedSpace.LiftPropAt P (f ∘ inclusion hUV) x
    rw [← hG.liftPropAt_iff_comp_inclusion hUV]
    -- ⊢ ChartedSpace.LiftPropAt P f (inclusion hUV x)
    apply h
    -- 🎉 no goals
  locality := by
    intro V f h x
    -- ⊢ ChartedSpace.LiftPropAt P f x
    obtain ⟨U, hxU, i, hU : ChartedSpace.LiftProp P (f ∘ i)⟩ := h x
    -- ⊢ ChartedSpace.LiftPropAt P f x
    let x' : U := ⟨x, hxU⟩
    -- ⊢ ChartedSpace.LiftPropAt P f x
    have hUV : U ≤ V := CategoryTheory.leOfHom i
    -- ⊢ ChartedSpace.LiftPropAt P f x
    have : ChartedSpace.LiftPropAt P f (inclusion hUV x') := by
      rw [hG.liftPropAt_iff_comp_inclusion hUV]
      exact hU x'
    convert this
    -- 🎉 no goals
#align structure_groupoid.local_invariant_prop.local_predicate StructureGroupoid.LocalInvariantProp.localPredicate

/-- Let `P` be a `LocalInvariantProp` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
a sheaf of types on `M` which, to each open set `U` in `M`, associates the type of bundled
functions from `U` to `M'` satisfying the lift of `P`. -/
def StructureGroupoid.LocalInvariantProp.sheaf (hG : LocalInvariantProp G G' P) :
    TopCat.Sheaf (Type u) (TopCat.of M) :=
  TopCat.subsheafToTypes (hG.localPredicate M M')
#align structure_groupoid.local_invariant_prop.sheaf StructureGroupoid.LocalInvariantProp.sheaf

instance StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun (hG : LocalInvariantProp G G' P)
    (U : (Opens (TopCat.of M))ᵒᵖ) : CoeFun ((hG.sheaf M M').val.obj U) fun _ => ↑(unop U) → M' where
  coe a := a.1
#align structure_groupoid.local_invariant_prop.sheaf_has_coe_to_fun StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun

theorem StructureGroupoid.LocalInvariantProp.section_spec (hG : LocalInvariantProp G G' P)
    (U : (Opens (TopCat.of M))ᵒᵖ) (f : (hG.sheaf M M').val.obj U) : ChartedSpace.LiftProp P f :=
  f.2
#align structure_groupoid.local_invariant_prop.section_spec StructureGroupoid.LocalInvariantProp.section_spec
