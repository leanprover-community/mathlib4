/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The set of Fredholm operators is open

In this file, we show that the set of Fredholm operators between two Banach spaces is open
(for the operator norm) in the space of continuous linear maps.
-/

@[expose] public noncomputable section

open Topology Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace 𝕜] [CompleteSpace E]

/-- If `T` is a Fredholm operators between two Banach spaces, then every operator `S` close
enough to `T` (in operator norm) is also Fredholm. -/
protected theorem IsFredholm.eventually
    {T : E →L[𝕜] F} (hT : T.IsFredholm) : ∀ᶠ S in 𝓝 T, S.IsFredholm := by
  obtain ⟨pkg⟩ := hT.nonempty_fredholmPackage
  have : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.isComplete.completeSpace_coe
  have := pkg.decDom.cofg_X₁
  let Φ (S : E →L[𝕜] F) : (pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₁) :=
    pkg.decCodom.proj ∘L S ∘L pkg.decDom.X₁.subtypeL
  have Φ_cont : Continuous Φ := by fun_prop
  have Φ_T_inv : (Φ T).IsInvertible := ⟨pkg.equiv, by ext; simp [Φ, pkg.eq_equiv]⟩
  have : ∀ᶠ S in 𝓝 T, (Φ S).IsInvertible := Φ_cont.tendsto T |>.eventually Φ_T_inv.eventually
  filter_upwards [this] with S Φ_S_inv
  have A : IsFredholm pkg.decDom.X₁.subtypeL :=
    pkg.decDom.X₁.isFredholm_subtypeL pkg.decDom.isTopCompl.isClosed
  have B : IsFredholm pkg.decCodom.proj := pkg.decCodom.isFredholm_proj
  rw [← A.comp_iff_left, ← B.comp_iff_right]
  exact Φ_S_inv.isFredholm

/-- The set of Fredholm operators between two Banach spaces is open (for the operator norm)
in the space of continuous linear maps. -/
theorem isOpen_setOfPred_isFredholm : IsOpen {T : E →L[𝕜] F | T.IsFredholm} :=
  isOpen_iff_mem_nhds.mpr fun _ ↦ IsFredholm.eventually

end ContinuousLinearMap
