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

## TODO

We can strengthen this statement in two ways:
- the index is continuous (i.e. locally constant) on the set of Fredholm operators (WIP)
- for any choice of a quasi-inverse `S₀` to a Fredholm operator `T₀`, there is a function
`φ : (E →L[𝕜] F) → (F →L[𝕜] E)` which is analytic on a neighborhood of `T₀`, such that `φ(T₀) = S₀`
and `φ(T)` is a quasi-inverse of `T` for every `T` in a neighborhood of `T₀`.
-/

@[expose] public noncomputable section

open Topology Submodule

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E]

/-- Let `T₀ : E → F` be a Fredholm operator between two Banach spaces, and choose a
`FredholmPackage` for `T₀`; that is, fix topological decompositions `E = E₁ ⊕ E₀` and `F = F₁ ⊕ F₀`,
where `E₀` and `F₀` are finite dimensional, and such that in these decompositions we have
$T₀ = \begin{pmatrix} α₀ & 0 \cr 0 & 0$ with `α₀` invertible.

Then, for $T = \begin{pmatrix} α & β \cr γ & δ$ close enough to `T₀` (in operator norm), we have
that `α` is invertible. -/
theorem FredholmPackage.eventually_isInvertible
    {T : E →L[𝕜] F} (pkg : T.FredholmPackage) :
    ∀ᶠ S in 𝓝 T, (pkg.decCodom.proj ∘L S ∘L pkg.decDom.X₁.subtypeL).IsInvertible := by
  have : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.isComplete.completeSpace_coe
  let Φ (S : E →L[𝕜] F) : (pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₁) :=
    pkg.decCodom.proj ∘L S ∘L pkg.decDom.X₁.subtypeL
  have Φ_cont : Continuous Φ := by fun_prop
  have Φ_T_inv : (Φ T).IsInvertible := ⟨pkg.equiv, by ext; simp [Φ, pkg.eq_equiv]⟩
  exact Φ_cont.tendsto T |>.eventually Φ_T_inv.eventually

/-- If `T₀` is a Fredholm operators between two Banach spaces, then every operator `T` close
enough to `T₀` (in operator norm) is also Fredholm. -/
protected theorem IsFredholm.eventually [CompleteSpace 𝕜]
    {T : E →L[𝕜] F} (hT : T.IsFredholm) : ∀ᶠ S in 𝓝 T, S.IsFredholm := by
  obtain ⟨pkg⟩ := hT.nonempty_fredholmPackage
  filter_upwards [pkg.eventually_isInvertible] with S h_inv
  have A : IsFredholm pkg.decDom.X₁.subtypeL :=
    have := pkg.decDom.cofg_X₁
    pkg.decDom.X₁.isFredholm_subtypeL pkg.decDom.isTopCompl.isClosed
  have B : IsFredholm pkg.decCodom.proj := pkg.decCodom.isFredholm_proj
  rw [← A.comp_iff_left, ← B.comp_iff_right]
  exact h_inv.isFredholm

/-- The set of Fredholm operators between two Banach spaces is open (for the operator norm)
in the space of continuous linear maps. -/
theorem isOpen_setOfPred_isFredholm [CompleteSpace 𝕜] : IsOpen {T : E →L[𝕜] F | T.IsFredholm} :=
  isOpen_iff_mem_nhds.mpr fun _ ↦ IsFredholm.eventually

end ContinuousLinearMap
