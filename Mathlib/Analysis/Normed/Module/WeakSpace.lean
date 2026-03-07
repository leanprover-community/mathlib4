/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Normed space instances for `WeakSpace`

This file provides basic instances for `WeakSpace 𝕜 E` in the setting of normed spaces.

## Main definitions

* `WeakSpace.instBornology`: The norm bornology on `WeakSpace 𝕜 E`, inherited from `E`.
* `WeakSpace.instT2Space`: The weak topology on a normed space over `RCLike` is Hausdorff,
  via Hahn–Banach separation.
-/

@[expose] public section

noncomputable section

open Bornology Topology

namespace WeakSpace

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

variable (𝕜) [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The weak topology on a normed space over `RCLike` is T2 (Hausdorff). This follows from
Hahn–Banach: the continuous linear functionals separate points. -/
instance instT2Space : T2Space (WeakSpace 𝕜 F) :=
  (WeakBilin.isEmbedding (B := (topDualPairing 𝕜 F).flip) fun x y h => by
    obtain ⟨g, _, hg⟩ := exists_dual_vector'' 𝕜 (x - y)
    rw [map_sub, show g x = g y from LinearMap.ext_iff.mp h g, sub_self] at hg
    exact sub_eq_zero.mp (norm_eq_zero.mp (by exact_mod_cast hg.symm))).t2Space

end WeakSpace
