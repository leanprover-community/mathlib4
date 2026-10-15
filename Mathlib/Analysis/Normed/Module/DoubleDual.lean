/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Michał Świętek, Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.WeakDual

import Mathlib.Analysis.Normed.Group.Quotient

/-!
# The double dual of a normed space, and reflexive spaces

In this file we define the inclusion of a normed space into its double strong dual,
prove that it is an isometry (for `𝕜 = ℝ` or `𝕜 = ℂ`), and use the corresponding weak-topology
embedding together with Banach–Alaoglu to transfer compactness from the weak-star bidual back to
the weak topology.

We also define reflexive topological vector spaces and study reflexive normed
spaces. A topological vector space `E` over a normed field `𝕜` is reflexive
(`TopologicalSpace.IsReflexive 𝕜 E`) if the canonical map `StrongDual.inclusionInDoubleDualₗ 𝕜 E`
from `E` to its strong bidual `StrongDual 𝕜 (StrongDual 𝕜 E)`, which sends `x` to the evaluation
at `x`, is a homeomorphism.

## Main definitions

* `StrongDual.inclusionInDoubleDualₗ`: the inclusion of a topological vector space into its
  double `StrongDual`, as a linear map.
* `NormedSpace.inclusionInDoubleDual` is the inclusion of a normed space in its double
  `StrongDual`, considered as a bounded linear map.
* `NormedSpace.inclusionInDoubleDualLi` is the same map as a linear isometry (for `𝕜 = ℝ` or
  `𝕜 = ℂ`).
* `NormedSpace.inclusionInDoubleDualWeak` is the map from the weak space into the weak-star bidual,
  as a continuous linear map.
* `NormedSpace.isEmbedding_inclusionInDoubleDualWeak` shows that `inclusionInDoubleDualWeak` is
  a topological embedding.
* `NormedSpace.isCompact_closure_of_isBounded` transfers compactness from the weak-star topology
  on the bidual back to the weak topology on `X`.
* `TopologicalSpace.IsReflexive`: a topological vector space is reflexive if
  `StrongDual.inclusionInDoubleDualₗ` is a homeomorphism.

## Main results

* `NormedSpace.isReflexive_iff_surjective_inclusionInDoubleDual`: a normed space is reflexive if
  and only if the canonical map to its double dual is surjective.
* `TopologicalSpace.IsReflexive.completeSpace`: a reflexive normed space is complete.
* `TopologicalSpace.IsReflexive.submodule_of_isClosed`: a closed subspace of a reflexive normed
  space is reflexive.
* `FiniteDimensional.isReflexive`: a finite-dimensional normed space is reflexive.

Hilbert spaces are reflexive: see the file ` Mathlib/Analysis/InnerProductSpace/Reflexive.lean`.

## References

* [Conway, John B., A course in functional analysis][conway1990]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

double dual, inclusion, isometry, embedding, weak-star topology, reflexive space
-/

@[expose] public section

noncomputable section

open Topology Bornology WeakDual

universe u v

namespace StrongDual

variable (𝕜 E : Type*) [NormedField 𝕜] [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E]

/-- The inclusion from a topological vector space `E` into its strong bidual, which sends `x` to
the evaluation at `x`, as a linear map.

For a normed space, see the continuous linear map `NormedSpace.inclusionInDoubleDual`. -/
def inclusionInDoubleDualₗ : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  ContinuousLinearMap.applyₗ 𝕜 (.id 𝕜)

variable {𝕜 E} in
@[simp]
lemma inclusionInDoubleDualₗ_apply (x : E) (f : StrongDual 𝕜 E) :
    inclusionInDoubleDualₗ 𝕜 E x f = f x := rfl

end StrongDual

namespace NormedSpace

section inclusionInDoubleDual

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The inclusion of a normed space in its double (topological) strong dual, considered
as a bounded linear map. -/
def inclusionInDoubleDual : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜

@[simp]
theorem dual_def (x : E) (f : StrongDual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl

/-- `StrongDual.inclusionInDoubleDualₗ` is the linear map underlying
`NormedSpace.inclusionInDoubleDual`. -/
@[simp]
lemma toLinearMap_inclusionInDoubleDual :
    (inclusionInDoubleDual 𝕜 E).toLinearMap = StrongDual.inclusionInDoubleDualₗ 𝕜 E := rfl

theorem inclusionInDoubleDual_norm_eq :
    ‖inclusionInDoubleDual 𝕜 E‖ = ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)‖ :=
  ContinuousLinearMap.opNorm_flip _

theorem inclusionInDoubleDual_norm_le : ‖inclusionInDoubleDual 𝕜 E‖ ≤ 1 := by
  rw [inclusionInDoubleDual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

theorem double_dual_bound (x : E) : ‖(inclusionInDoubleDual 𝕜 E) x‖ ≤ ‖x‖ := by
  simpa using ContinuousLinearMap.le_of_opNorm_le _ (inclusionInDoubleDual_norm_le 𝕜 E) x

end inclusionInDoubleDual

section BidualIsometry

variable (𝕜 : Type v) [RCLike 𝕜] {E : Type u}

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The inclusion of a normed space in its double strong dual is an isometry onto its image. -/
def inclusionInDoubleDualLi : E →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' x := by
      apply le_antisymm (double_dual_bound 𝕜 E x)
      obtain ⟨g, hg⟩ := exists_dual_vector'' 𝕜 x
      grw [← (inclusionInDoubleDual 𝕜 E x).unit_le_opNorm g hg.left]
      simp [hg.right] }

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
Compare `ContinuousLinearMap.opNorm_le_bound`. -/
theorem norm_le_dual_bound (x : E) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ f : StrongDual 𝕜 E, ‖f x‖ ≤ M * ‖f‖) : ‖x‖ ≤ M := by
  rw [← (inclusionInDoubleDualLi (E := E) 𝕜).norm_map x]
  exact ContinuousLinearMap.opNorm_le_bound _ hMp hM

end Seminormed

end BidualIsometry

section Embedding

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (X : Type*) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The map from a normed space with the weak topology into the weak-star bidual, as a continuous
linear map. Built using `LinearEquiv.arrowCongr` to properly bundle the topology changes via
`toWeakSpace` and `StrongDual.toWeakDual`. -/
@[simps! -isSimp apply apply_apply]
def inclusionInDoubleDualWeak : WeakSpace 𝕜 X →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 X) where
  toLinearMap := (toWeakSpace 𝕜 X).arrowCongr StrongDual.toWeakDual
    (inclusionInDoubleDual 𝕜 X).toLinearMap
  cont := Topology.IsInducing.continuous ⟨Eq.symm induced_compose⟩

attribute [simp] inclusionInDoubleDualWeak_apply_apply

@[simp]
lemma toLinearMap_inclusionInDoubleDualWeak :
    (inclusionInDoubleDualWeak 𝕜 X).toLinearMap =
      (toWeakSpace 𝕜 X).arrowCongr StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X).toLinearMap :=
  rfl

variable (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- `inclusionInDoubleDualWeak` is a topological embedding from the weak topology to the weak-star
topology. -/
theorem isEmbedding_inclusionInDoubleDualWeak :
    IsEmbedding (inclusionInDoubleDualWeak 𝕜 X) where
  eq_induced := Eq.symm induced_compose
  injective := StrongDual.toWeakDual.injective.comp
    (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective

/-- If `S` is bounded set in `WeakSpace X` and the weak-star closure of its image under
the embedding into the weak-star double dual lies in the range of that embedding,
then `closure S` is compact in the weak topology.

This combines Banach–Alaoglu (compactness of bounded weak-star–closed sets) with the topological
embedding `inclusionInDoubleDualWeak_isEmbedding` to transfer compactness back to the weak
topology on `X`. -/
theorem isCompact_closure_of_isBounded (S : Set (WeakSpace 𝕜 X))
    (hb : IsBounded ((toWeakSpace 𝕜 X) ⁻¹' S))
    (hrange : closure (inclusionInDoubleDualWeak 𝕜 X '' S) ⊆
      Set.range (inclusionInDoubleDualWeak 𝕜 X)) :
    IsCompact (closure S) := by
  rw [(isEmbedding_inclusionInDoubleDualWeak 𝕜 X).closure_eq_preimage_closure_image]
  apply (isEmbedding_inclusionInDoubleDualWeak 𝕜 X).isCompact_preimage' _ hrange
  exact WeakDual.isCompact_of_bounded_of_closed
    (WeakDual.isBounded_closure ((inclusionInDoubleDual 𝕜 X).lipschitzWith.isBounded_image hb))
    isClosed_closure

end Embedding

end NormedSpace

/-! ### Reflexive normed spaces -/

/-- A topological vector space `E` is reflexive if the inclusion
`StrongDual.inclusionInDoubleDualₗ 𝕜 E` from `E` into its strong bidual is a homeomorphism.

This is not the algebraic notion `Module.IsReflexive`, which concerns the algebraic double dual. -/
class TopologicalSpace.IsReflexive (𝕜 E : Type*) [NormedField 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E] : Prop where
  isHomeomorph_inclusionInDoubleDualₗ : IsHomeomorph (StrongDual.inclusionInDoubleDualₗ 𝕜 E)

open Function

variable {𝕜 : Type*} [RCLike 𝕜]

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A point which does not belong to the closure of a subspace `F` is separated from `F` by a
continuous linear form which vanishes on `F`. -/
theorem Submodule.exists_strongDual_forall_apply_eq_zero_of_notMem_topologicalClosure
    (F : Submodule 𝕜 E) {y : E} (hy : y ∉ F.topologicalClosure) :
    ∃ ψ : StrongDual 𝕜 E, (∀ z ∈ F, ψ z = 0) ∧ ψ y ≠ 0 := by
  -- the image of `y` in the normed space `E ⧸ F.topologicalClosure` is not zero
  have : IsClosed (F.topologicalClosure : Set E) := F.isClosed_topologicalClosure
  have hy' : ‖F.topologicalClosure.mkQ y‖ ≠ 0 := by
    rwa [Ne, norm_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨g, -, hg⟩ := exists_dual_vector 𝕜 (F.topologicalClosure.mkQ y) hy'
  refine ⟨g.comp F.topologicalClosure.mkQL, fun z hz ↦ ?_, ?_⟩
  · simp [(Submodule.Quotient.mk_eq_zero _).2 (F.le_topologicalClosure hz)]
  · rw [ContinuousLinearMap.comp_apply, Submodule.mkQL_apply, hg]
    exact RCLike.ofReal_ne_zero.2 hy'

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open NormedSpace

/-- A normed space is reflexive if and only if the canonical map to its double dual is
surjective. -/
theorem NormedSpace.isReflexive_iff_surjective_inclusionInDoubleDual :
    TopologicalSpace.IsReflexive 𝕜 E ↔ Surjective (inclusionInDoubleDual 𝕜 E) :=
  ⟨fun hE ↦ hE.isHomeomorph_inclusionInDoubleDualₗ.surjective, fun hE ↦
    ⟨(LinearIsometryEquiv.ofSurjective (inclusionInDoubleDualLi 𝕜) hE).toHomeomorph.isHomeomorph⟩⟩

namespace TopologicalSpace.IsReflexive

variable (𝕜 E) in
/-- A reflexive normed space is complete. -/
theorem completeSpace [IsReflexive 𝕜 E] : CompleteSpace E :=
  ((inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isUniformInducing.completeSpace_congr
    (isReflexive_iff_surjective_inclusionInDoubleDual.1 ‹_›)).2 inferInstance

/-- A closed subspace of a reflexive normed space is reflexive. -/
theorem submodule_of_isClosed [IsReflexive 𝕜 E] (F : Submodule 𝕜 E) (hF : IsClosed (F : Set E)) :
    IsReflexive 𝕜 F := by
  rw [isReflexive_iff_surjective_inclusionInDoubleDual]
  intro Λ
  -- `Λ` composed with the restriction of linear forms to `F` is the evaluation at a point `y`
  obtain ⟨y, hy⟩ := isReflexive_iff_surjective_inclusionInDoubleDual.1 ‹_›
    (Λ.comp (ContinuousLinearMap.precomp 𝕜 F.subtypeL))
  have hyψ (ψ : StrongDual 𝕜 E) : ψ y = Λ (ψ.comp F.subtypeL) := by
    rw [← dual_def 𝕜 E y ψ, hy]
    rfl
  -- `y ∈ F`, since every continuous linear form which vanishes on `F` vanishes at `y`
  have hyF : y ∈ F := by
    by_contra hyF
    obtain ⟨ψ, hψF, hψy⟩ := F.exists_strongDual_forall_apply_eq_zero_of_notMem_topologicalClosure
      (hF.submodule_topologicalClosure_eq ▸ hyF)
    have hψ : ψ.comp F.subtypeL = 0 := ContinuousLinearMap.ext fun z ↦ hψF z z.2
    exact hψy (by rw [hyψ, hψ, map_zero])
  -- every continuous linear form on `F` is the restriction of a continuous linear form on `E`
  refine ⟨⟨y, hyF⟩, ContinuousLinearMap.ext fun ψ ↦ ?_⟩
  obtain ⟨ψ', hψ', -⟩ := exists_extension_norm_eq F ψ
  have hψ'_eq : ψ'.comp F.subtypeL = ψ := ContinuousLinearMap.ext hψ'
  rw [dual_def, ← hψ'_eq, ← hyψ]
  rfl

end TopologicalSpace.IsReflexive

/-- A finite-dimensional normed space is reflexive. -/
instance FiniteDimensional.isReflexive [FiniteDimensional 𝕜 E] :
    TopologicalSpace.IsReflexive 𝕜 E := by
  rw [isReflexive_iff_surjective_inclusionInDoubleDual]
  -- `inclusionInDoubleDual` is an injective linear map between spaces of the same dimension
  have h_inj : Injective (inclusionInDoubleDual 𝕜 E : E →ₗ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)) :=
    (inclusionInDoubleDualLi 𝕜 (E := E)).injective
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := 𝕜) (V := E)
    (V₂ := StrongDual 𝕜 (StrongDual 𝕜 E)) ?_).1 h_inj
  rw [← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq,
    ← LinearMap.toContinuousLinearMap.finrank_eq, Subspace.dual_finrank_eq]

/-- If the scalars `g i` and the continuous linear forms `φ i` are such that
`‖∑ i, c i * g i‖ ≤ ‖∑ i, c i • φ i‖` for all finitely supported families of scalars `c`,
then there is a point `y` of norm at most `1` such that `φ i y = g i` for all `i`. -/
theorem NormedSpace.exists_norm_le_one_forall_apply_eq
    {ι : Type*} [TopologicalSpace.IsReflexive 𝕜 E] (φ : ι → StrongDual 𝕜 E) (g : ι → 𝕜)
    (h : ∀ c : ι →₀ 𝕜, ‖Finsupp.linearCombination 𝕜 g c‖ ≤ ‖Finsupp.linearCombination 𝕜 φ c‖) :
    ∃ y : E, ‖y‖ ≤ 1 ∧ ∀ i, φ i y = g i := by
  obtain ⟨Λ, hΛ_norm, hΛ⟩ := exists_strongDual_forall_apply_eq_of_forall_norm_le _ _ h
  obtain ⟨y, rfl⟩ := isReflexive_iff_surjective_inclusionInDoubleDual.1 ‹_› Λ
  refine ⟨y, ((inclusionInDoubleDualLi 𝕜).norm_map y).symm.trans_le hΛ_norm, fun i ↦ ?_⟩
  simpa [dual_def] using hΛ (Finsupp.single i 1)

end Normed
