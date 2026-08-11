/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!

# Topological monoids with open units

We say that a topological monoid `M` has open units (`IsOpenUnits`) if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or fields),
complete normed rings (for example the ring `E →L[𝕜] E` of continuous linear endomorphisms of any
Banach space `E`), and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)`
(`IsOpenUnits.of_isAdic`).

A non-example is `𝔸ₖ`, because the topology on ideles is not the induced topology from adeles.

This condition is necessary and sufficient for `U(R)` to be an open subspace of `X(R)`
for all affine scheme `X` over `R` and all affine open subscheme `U ⊆ X`.
-/

public section

open Topology

/--
We say that a topological monoid `M` has open units if `Mˣ` is open in `M` and
has the subspace topology (i.e. inverse is continuous).

Typical examples include monoids with discrete topology, topological groups (or fields),
complete normed rings, and rings `R` equipped with the `I`-adic topology where `I ≤ J(R)`.
-/
@[mk_iff]
class IsOpenUnits (M : Type*) [Monoid M] [TopologicalSpace M] : Prop where
  isOpenEmbedding_unitsVal : IsOpenEmbedding (Units.val : Mˣ → M)

namespace Units

variable {M : Type*} [Monoid M] [TopologicalSpace M] [IsOpenUnits M]

lemma isOpenEmbedding_val : IsOpenEmbedding (Units.val : Mˣ → M) :=
  IsOpenUnits.isOpenEmbedding_unitsVal

lemma isOpenMap_val : IsOpenMap (Units.val : Mˣ → M) := isOpenEmbedding_val.isOpenMap

lemma isEmbedding_val : IsEmbedding (Units.val : Mˣ → M) := isOpenEmbedding_val.isEmbedding

lemma isInducing_val : IsInducing (Units.val : Mˣ → M) := isOpenEmbedding_val.isInducing

protected theorem isOpen : IsOpen { a : M | IsUnit a } :=
  isOpenEmbedding_val.isOpen_range

protected theorem nhds (a : Mˣ) : { a : M | IsUnit a } ∈ 𝓝 (a : M) :=
  IsOpen.mem_nhds Units.isOpen a.isUnit

protected theorem _root_.nonunits.isClosed : IsClosed (nonunits M) :=
  Units.isOpen.isClosed_compl

end Units

/-- In rings `R` with open units, `Ring.inverse : R → R` is continuous on the set of units. -/
lemma Ring.inverse_continuousOn {M₀ : Type*} [MonoidWithZero M₀] [TopologicalSpace M₀]
    [IsOpenUnits M₀] : ContinuousOn Ring.inverse { a : M₀ | IsUnit a} := by
  refine (Set.image_univ ▸ Units.isInducing_val.continuousOn_image_iff).2 <| continuousOn_univ.2 ?_
  simpa [Function.comp_def] using Units.continuous_coe_inv

/-- In rings `R` with open units, `Ring.inverse : R → R` is continuous at every unit `a : Rˣ`. -/
lemma Ring.inverse_continuousAt {M₀ : Type*} [MonoidWithZero M₀] [TopologicalSpace M₀]
    [IsOpenUnits M₀] (a : M₀ˣ) : ContinuousAt Ring.inverse (a : M₀) :=
  Ring.inverse_continuousOn.continuousAt (Units.nhds a)

namespace Ideal

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [IsOpenUnits R]

/-- The `Ideal.closure` of a proper ideal in ring with open units is proper. -/
theorem closure_ne_top (I : Ideal R) (hI : I ≠ ⊤) : I.closure ≠ ⊤ := by
  have h := closure_minimal (coe_subset_nonunits hI) nonunits.isClosed
  simpa only [I.closure.eq_top_iff_one, Ne] using! mt (@h 1) one_notMem_nonunits

/-- The `Ideal.closure` of a maximal ideal in a ring with open units is the ideal itself. -/
theorem IsMaximal.closure_eq {I : Ideal R} (hI : I.IsMaximal) : I.closure = I :=
  (hI.eq_of_le (I.closure_ne_top hI.ne_top) subset_closure).symm

/-- Maximal ideals in rings with open units are closed. -/
instance IsMaximal.isClosed {I : Ideal R} [hI : I.IsMaximal] : IsClosed (I : Set R) :=
  isClosed_of_closure_subset <| Eq.subset <| congr_arg ((↑) : Ideal R → Set R) hI.closure_eq

end Ideal

/-- Transport an `IsOpenUnits`-instance along an isomorphism. -/
lemma ContinuousMulEquiv.isOpenUnits {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [Monoid M] [Monoid N] (e : M ≃ₜ* N) [IsOpenUnits N] : IsOpenUnits M where
  isOpenEmbedding_unitsVal := by
    convert e.symm.isOpenEmbedding.comp <| IsOpenUnits.isOpenEmbedding_unitsVal.comp <|
      e.isOpenEmbedding.units_map (f := e.toMonoidHom)
    ext m
    exact (e.symm_apply_apply m).symm

instance (priority := 900) (M : Type*) [Monoid M] [TopologicalSpace M] [DiscreteTopology M] :
    IsOpenUnits M where
  isOpenEmbedding_unitsVal :=
    .of_continuous_injective_isOpenMap Units.continuous_val Units.val_injective
      fun _ _ ↦ isOpen_discrete _

instance (priority := 900) {M : Type*} [Group M] [TopologicalSpace M] [ContinuousInv M] :
    IsOpenUnits M where
  isOpenEmbedding_unitsVal := toUnits_homeomorph.symm.isOpenEmbedding

instance (priority := 900) {M : Type*} [GroupWithZero M]
    [TopologicalSpace M] [ContinuousInv₀ M] [T1Space M] : IsOpenUnits M where
  isOpenEmbedding_unitsVal := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    convert! (isClosed_singleton (X := M) (x := 0)).isOpen_compl
    ext
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact isUnit_iff_ne_zero
