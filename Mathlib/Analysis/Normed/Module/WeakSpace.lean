/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Normed space instances for `WeakSpace`

This file provides basic instances for `WeakSpace 𝕜 E` in the setting of normed spaces.

The file equips `WeakSpace 𝕜 E` with the norm bornology inherited from `E`, so that `IsBounded`
refers to norm boundedness. This is a pragmatic choice discussed further in the implementation
notes.

## Main definitions

* `WeakSpace.instBornology`: The norm bornology on `WeakSpace 𝕜 E`, inherited from `E`.
* `WeakSpace.seminormFamily`: The family of seminorms `fun f x ↦ ‖f x‖` generating the weak
  topology, indexed by `StrongDual 𝕜 E`.
* `WeakSpace.instT2Space`: The weak topology on a normed space over `RCLike` is Hausdorff,
  via Hahn–Banach separation.

## Main results

### Topology comparison
* `WeakSpace.norm_topology_le_weakSpace_topology`: The weak topology is coarser than the norm
  topology.

### Bornology and pointwise bounds
* `WeakSpace.isBounded_iff_isVonNBounded`: Equivalence of norm and weak boundedness for
  normed spaces over `RCLike`.

## Implementation notes

* **Bornology choice:** The `Bornology` instance on `WeakSpace 𝕜 E` is inherited from `E` via
  `inferInstanceAs` and corresponds to the norm bornology. While the natural bornology for a
  weak topology is technically the von Neumann bornology (pointwise boundedness), we use the
  norm bornology for several pragmatic reasons:
  1. **Practicality:** In the normed setting, "bounded" is almost universally synonymous with
     "norm-bounded". This allows `IsBounded` to be used directly.
  2. **Clarity:** It preserves a clear distinction between norm-boundedness (`IsBounded`) and
     topological weak boundedness (`IsVonNBounded`).
  3. **Consistency:** By the Uniform Boundedness Principle, these notions coincide whenever
     `𝕜` is `RCLike` (`isBounded_iff_isVonNBounded`). No `[CompleteSpace E]` assumption is
     needed because `banach_steinhaus` is applied to the inclusion in the double dual, whose
     domain `StrongDual 𝕜 E` is always complete when `𝕜` is `RCLike`.
-/

@[expose] public section

noncomputable section

open Bornology Topology

namespace WeakSpace

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The norm bornology on `WeakSpace 𝕜 E`, inherited from `E`. -/
instance instBornology : Bornology (WeakSpace 𝕜 E) := inferInstanceAs (Bornology E)

/-- A set in `WeakSpace 𝕜 E` is bounded iff its image in `E` is bounded. -/
@[simp]
theorem isBounded_toE_preimage {s : Set E} :
    IsBounded (⇑(toWeakSpace 𝕜 E).symm ⁻¹' s) ↔ IsBounded s :=
  Iff.rfl

/-- A set in `E` is bounded iff its image in `WeakSpace 𝕜 E` is bounded. -/
@[simp]
theorem isBounded_toWeakSpace_preimage {s : Set (WeakSpace 𝕜 E)} :
    IsBounded (⇑(toWeakSpace 𝕜 E) ⁻¹' s) ↔ IsBounded s :=
  Iff.rfl

/-- The weak topology on a normed space is coarser than the norm topology. -/
theorem norm_topology_le_weakSpace_topology :
    (UniformSpace.toTopologicalSpace : TopologicalSpace E) ≤
      (inferInstance : TopologicalSpace (WeakSpace 𝕜 E)) := by
  convert (toWeakSpaceCLM 𝕜 E).continuous.le_induced
  exact induced_id.symm

end NontriviallyNormedField

section RCLike

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The weak topology on a normed space over `RCLike` is T2 (Hausdorff). This follows from
Hahn–Banach: the continuous linear functionals separate points. -/
instance instT2Space : T2Space (WeakSpace 𝕜 E) :=
  (WeakBilin.isEmbedding (B := (topDualPairing 𝕜 E).flip) fun x y h => by
    obtain ⟨g, _, hg⟩ := exists_dual_vector'' 𝕜 (x - y)
    rw [map_sub, show g x = g y from LinearMap.ext_iff.mp h g, sub_self] at hg
    exact sub_eq_zero.mp (norm_eq_zero.mp (by exact_mod_cast hg.symm))).t2Space

set_option backward.isDefEq.respectTransparency false in
/-- By the Uniform Boundedness Principle, norm-boundedness (the default bornology)
and pointwise-boundedness (`IsVonNBounded`) coincide on the weak space of a normed space
over `RCLike`. -/
theorem isBounded_iff_isVonNBounded {s : Set (WeakSpace 𝕜 E)} :
    IsBounded s ↔ Bornology.IsVonNBounded 𝕜 s := by
  constructor
  · exact fun h => ((NormedSpace.isVonNBounded_iff (E := E) (𝕜 := 𝕜)).mpr h).of_topologicalSpace_le
      norm_topology_le_weakSpace_topology
  · intro h_vN
    have h_ptwise := (WeakSpace.withSeminorms 𝕜 E).isVonNBounded_iff_seminorm_bounded.mp h_vN
    obtain ⟨C, hC⟩ := banach_steinhaus
      (g := fun i : s ↦ NormedSpace.inclusionInDoubleDual 𝕜 E i.val) fun f ↦
      let ⟨M, _, hM⟩ := h_ptwise f
      ⟨M, fun i ↦ le_of_lt (hM i.val i.property)⟩
    suffices @IsBounded E _ s from this
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, fun x hx ↦ by
      rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x]
      exact hC ⟨x, hx⟩⟩

end RCLike

end WeakSpace
