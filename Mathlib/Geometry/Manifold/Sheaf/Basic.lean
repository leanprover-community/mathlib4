/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module geometry.manifold.sheaf.basic
! leanprover-community/mathlib commit 431589bce478b2229eba14b14a283250428217db
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Topology.Sheaves.LocalPredicate

/-! # Generic construction of a sheaf from a `local_invariant_prop` on a manifold

This file constructs the sheaf-of-types of functions `f : M → M'` (for charted spaces `M`, `M'`)
which satisfy the lifted property `lift_prop P` associated to some locally invariant (in the sense
of `structure_groupoid.local_invariant_prop`) property `P` on the model spaces of `M` and `M'`. For
example, differentiability and smoothness are locally invariant properties in this sense, so this
construction can be used to construct the sheaf of differentiable functions on a manifold and the
sheaf of smooth functions on a manifold.

The mathematical work is in associating a `Top.local_predicate` to a
`structure_groupoid.local_invariant_prop`: that is, showing that a differential-geometric "locally
invariant" property is preserved under restriction and gluing.

## Main definitions

* `structure_groupoid.local_invariant_prop.local_predicate`: the `Top.local_predicate` (in the
  sheaf-theoretic sense) on functions from open subsets of `M` into `M'`, which states whether
  such functions satisfy `lift_prop P`.
* `structure_groupoid.local_invariant_prop.sheaf`: the sheaf-of-types of functions `f : M → M'`
  which satisfy the lifted property `lift_prop P`.
-/


open scoped Manifold Topology

open Set TopologicalSpace StructureGroupoid StructureGroupoid.LocalInvariantProp Opposite

universe u

variable {H : Type _} [TopologicalSpace H] {H' : Type _} [TopologicalSpace H']
  {G : StructureGroupoid H} {G' : StructureGroupoid H'} {P : (H → H') → Set H → H → Prop}
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M] (M' : Type u) [TopologicalSpace M']
  [ChartedSpace H' M']

instance TopCat.of.chartedSpace : ChartedSpace H (TopCat.of M) :=
  (inferInstance : ChartedSpace H M)
#align Top.of.charted_space TopCat.of.chartedSpace

instance TopCat.of.hasGroupoid [HasGroupoid M G] : HasGroupoid (TopCat.of M) G :=
  (inferInstance : HasGroupoid M G)
#align Top.of.has_groupoid TopCat.of.hasGroupoid

/-- Let `P` be a `local_invariant_prop` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
an induced `local_predicate` on the functions from `M` to `M'`, given by `lift_prop P`. -/
def StructureGroupoid.LocalInvariantProp.localPredicate (hG : LocalInvariantProp G G' P) :
    TopCat.LocalPredicate fun x : TopCat.of M => M' where
  pred {U : Opens (TopCat.of M)} := fun f : U → M' => LiftProp P f
  res := by
    intro U V i f h x
    have hUV : U ≤ V := CategoryTheory.leOfHom i
    show lift_prop_at P (f ∘ Set.inclusion hUV) x
    rw [← hG.lift_prop_at_iff_comp_inclusion hUV]
    apply h
  locality := by
    intro V f h x
    obtain ⟨U, hxU, i, hU : lift_prop P (f ∘ i)⟩ := h x
    let x' : U := ⟨x, hxU⟩
    have hUV : U ≤ V := CategoryTheory.leOfHom i
    have : lift_prop_at P f (inclusion hUV x') := by
      rw [hG.lift_prop_at_iff_comp_inclusion hUV]
      exact hU x'
    convert this
    ext1
    rfl
#align structure_groupoid.local_invariant_prop.local_predicate StructureGroupoid.LocalInvariantProp.localPredicate

/-- Let `P` be a `local_invariant_prop` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
a sheaf of types on `M` which, to each open set `U` in `M`, associates the type of bundled
functions from `U` to `M'` satisfying the lift of `P`. -/
def StructureGroupoid.LocalInvariantProp.sheaf (hG : LocalInvariantProp G G' P) :
    TopCat.Sheaf (Type u) (TopCat.of M) :=
  TopCat.subsheafToTypes (hG.LocalPredicateₓ M M')
#align structure_groupoid.local_invariant_prop.sheaf StructureGroupoid.LocalInvariantProp.sheaf

instance StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun (hG : LocalInvariantProp G G' P)
    (U : (Opens (TopCat.of M))ᵒᵖ) : CoeFun ((hG.Sheaf M M').val.obj U) fun _ => unop U → M'
    where coe a := a.1
#align structure_groupoid.local_invariant_prop.sheaf_has_coe_to_fun StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun

theorem StructureGroupoid.LocalInvariantProp.section_spec (hG : LocalInvariantProp G G' P)
    (U : (Opens (TopCat.of M))ᵒᵖ) (f : (hG.Sheaf M M').val.obj U) : LiftProp P f :=
  f.2
#align structure_groupoid.local_invariant_prop.section_spec StructureGroupoid.LocalInvariantProp.section_spec

