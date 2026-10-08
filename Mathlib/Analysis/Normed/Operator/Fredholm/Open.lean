/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The set of Fredholm operators is open, and the index is locally constant

In this file, we show two closely related results about Fredholm operators between two Banach
spaces:
* `isOpen_setOfPred_isFredholm`: the set of Fredholm operators is open
  (for the operator norm) in the space of continuous linear maps;
* `index_continuousOn_isFredholm`: the integer-valued map `T ↦ T.index` is continuous
  (i.e locally constant) on this open subset.

## TODO

With a bit more work, we could also show that, for any choice of a quasi-inverse `S₀` to a
Fredholm operator `T₀`, there is a function `φ : (E →L[𝕜] F) → (F →L[𝕜] E)` which is analytic on a
neighborhood of `T₀`, such that `φ(T₀) = S₀` and `φ(T)` is a quasi-inverse of `T` for every `T` in
a neighborhood of `T₀`.
-/

@[expose] public noncomputable section

open Topology Submodule Module LinearMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [CompleteSpace E]

/-- Let `T₀ : E → F` be a Fredholm operator between two Banach spaces, and choose a
`FredholmPackage` for `T₀`; that is, fix topological decompositions `E = E₁ ⊕ E₀` and `F = F₁ ⊕ F₀`,
where `E₀` and `F₀` are finite dimensional, and such that in these decompositions we have
$T₀ = \begin{pmatrix} α₀ & 0 \cr 0 & 0 \end{pmatrix}$ with `α₀` invertible.

Then, for $T = \begin{pmatrix} α & β \cr γ & δ \end{pmatrix}$ close enough to `T₀`
(in operator norm), we have that `α` is invertible. -/
theorem FredholmPackage.eventually_nhds_isInvertible
    {T₀ : E →L[𝕜] F} (pkg : T₀.FredholmPackage) :
    ∀ᶠ T in 𝓝 T₀, (pkg.decCodom.proj ∘L T ∘L pkg.decDom.X₁.subtypeL).IsInvertible := by
  have : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.isComplete.completeSpace_coe
  let Φ (T : E →L[𝕜] F) : (pkg.decDom.X₁ →L[𝕜] pkg.decCodom.X₁) :=
    pkg.decCodom.proj ∘L T ∘L pkg.decDom.X₁.subtypeL
  have Φ_cont : Continuous Φ := by fun_prop
  have Φ_T₀_inv : (Φ T₀).IsInvertible := ⟨pkg.equiv, by ext; simp [Φ, pkg.eq_equiv]⟩
  exact Φ_cont.tendsto T₀ |>.eventually Φ_T₀_inv.eventually_nhds

private theorem FredholmPackage.eventually_nhds_isFredholm_and_index_eq [CompleteSpace 𝕜]
    {T₀ : E →L[𝕜] F} (pkg : T₀.FredholmPackage) :
    ∀ᶠ T in 𝓝 T₀, T.IsFredholm ∧
      T.index = (finrank 𝕜 pkg.decDom.X₀ : ℤ) - finrank 𝕜 pkg.decCodom.X₀ := by
  filter_upwards [pkg.eventually_nhds_isInvertible] with T h_inv
  have A : IsFredholm pkg.decDom.X₁.subtypeL :=
    have := pkg.decDom.cofg_X₁
    pkg.decDom.X₁.isFredholm_subtypeL pkg.decDom.isTopCompl.isClosed
  have B : IsFredholm pkg.decCodom.proj := pkg.decCodom.isFredholm_proj
  have C : IsFredholm T := by
    rw [← A.comp_iff_left, ← B.comp_iff_right]
    exact h_inv.isFredholm
  refine ⟨C, ?_⟩
  have key := LinearMap.index_of_bijective h_inv.bijective
  rw [B.index_comp (C.comp A), C.index_comp A, toLinearMap_projectionOntoL, index_projectionOnto,
    toLinearMap_subtypeL, index_subtype,
    (Submodule.quotientEquivOfIsCompl _ _ pkg.decDom.isTopCompl.isCompl).finrank_eq] at key
  lia

/-- If `T₀` is a Fredholm operator between two Banach spaces, then every operator `T` close
enough to `T₀` (in operator norm) is also Fredholm. -/
protected theorem IsFredholm.eventually_nhds [CompleteSpace 𝕜]
    {T₀ : E →L[𝕜] F} (hT₀ : T₀.IsFredholm) : ∀ᶠ T in 𝓝 T₀, T.IsFredholm := by
  obtain ⟨pkg⟩ := hT₀.nonempty_fredholmPackage
  exact pkg.eventually_nhds_isFredholm_and_index_eq.mono fun T ⟨T_fred, _⟩ ↦ T_fred

/-- The set of Fredholm operators between two Banach spaces is open (for the operator norm)
in the space of continuous linear maps. -/
theorem isOpen_setOfPred_isFredholm [CompleteSpace 𝕜] : IsOpen {T : E →L[𝕜] F | T.IsFredholm} :=
  isOpen_iff_mem_nhds.mpr fun _ ↦ IsFredholm.eventually_nhds

/-- If `T₀` is a Fredholm operator between two Banach spaces, then every operator `T` close
enough to `T₀` (in operator norm) has the same index as `T₀`. -/
theorem IsFredholm.eventually_nhds_index_eq [CompleteSpace 𝕜]
    {T₀ : E →L[𝕜] F} (hT₀ : T₀.IsFredholm) : ∀ᶠ T in 𝓝 T₀, T.index = T₀.index := by
  obtain ⟨pkg⟩ := hT₀.nonempty_fredholmPackage
  rw [pkg.eventually_nhds_isFredholm_and_index_eq.self_of_nhds.2]
  exact pkg.eventually_nhds_isFredholm_and_index_eq.mono fun _ ⟨_, eq⟩ ↦ eq

/-- If `T₀` is a Fredholm operator between two Banach spaces, then the integer-valued map
`T ↦ T.index` is continuous at `T₀`. -/
theorem IsFredholm.index_continuousAt [CompleteSpace 𝕜]
    {T₀ : E →L[𝕜] F} (hT₀ : T₀.IsFredholm) :
    ContinuousAt (fun (T : E →L[𝕜] F) ↦ T.index) T₀ :=
  tendsto_const_nhds.congr' <| .symm hT₀.eventually_nhds_index_eq

/-- The integer-valued map `T ↦ T.index` is continuous (i.e locally constant)
on the set of Fredholm operators between two Banach spaces.. -/
theorem index_continuousOn_isFredholm [CompleteSpace 𝕜] :
    ContinuousOn (fun (T : E →L[𝕜] F) ↦ T.index) {T | T.IsFredholm} :=
  continuousOn_of_forall_continuousAt fun _ ↦ IsFredholm.index_continuousAt

end ContinuousLinearMap
