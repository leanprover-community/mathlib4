/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Whitney embedding theorem

In this file we prove a version of the Whitney embedding theorem: for any compact real manifold `M`,
for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.

## TODO

* Prove the weak Whitney embedding theorem: any `σ`-compact smooth `m`-dimensional manifold can be
  embedded into `ℝ^(2m+1)`. This requires a version of Sard's theorem: for a locally Lipschitz
  continuous map `f : ℝ^m → ℝ^n`, `m < n`, the range has Hausdorff dimension at most `m`, hence it
  has measure zero.

## Tags

partition of unity, smooth bump function, whitney theorem
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe uι uE uH uM

open Function Filter Module Set Topology
open scoped Manifold ContDiff

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


noncomputable section

namespace SmoothBumpCovering

/-!
### Whitney embedding theorem

In this section we prove a version of the Whitney embedding theorem: for any compact real manifold
`M`, for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.
-/

variable [T2Space M] [Fintype ι] {s : Set M} (f : SmoothBumpCovering ι I M s)

/-- Smooth embedding of `M` into `(E × ℝ) ^ ι`. -/
def embeddingPiTangent : C^∞⟮I, M; 𝓘(ℝ, ι → E × ℝ), ι → E × ℝ⟯ where
  val x i := (f i x • extChartAt I (f.c i) x, f i x)
  property :=
    contMDiff_pi_space.2 fun i =>
      ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff

@[local simp]
theorem embeddingPiTangent_coe :
    ⇑f.embeddingPiTangent = fun x i => (f i x • extChartAt I (f.c i) x, f i x) :=
  rfl

theorem embeddingPiTangent_injOn : InjOn f.embeddingPiTangent s := by
  intro x hx y _ h
  simp only [embeddingPiTangent_coe, funext_iff] at h
  obtain ⟨h₁, h₂⟩ := Prod.mk_inj.1 (h (f.ind x hx))
  rw [f.apply_ind x hx] at h₂
  rw [← h₂, f.apply_ind x hx, one_smul, one_smul] at h₁
  have := f.mem_extChartAt_source_of_eq_one h₂.symm
  exact (extChartAt I (f.c _)).injOn (f.mem_extChartAt_ind_source x hx) this h₁

theorem embeddingPiTangent_injective (f : SmoothBumpCovering ι I M) :
    Injective f.embeddingPiTangent :=
  injOn_univ.1 f.embeddingPiTangent_injOn

theorem comp_embeddingPiTangent_mfderiv (x : M) (hx : x ∈ s) :
    ((ContinuousLinearMap.fst ℝ E ℝ).comp
            (@ContinuousLinearMap.proj ℝ _ ι (fun _ => E × ℝ) _ _ (fun _ => inferInstance)
              (f.ind x hx))).comp
        (mfderiv I 𝓘(ℝ, ι → E × ℝ) f.embeddingPiTangent x) =
      mfderiv% (chartAt H (f.c (f.ind x hx))) x := by
  set L :=
    (ContinuousLinearMap.fst ℝ E ℝ).comp
      (@ContinuousLinearMap.proj ℝ _ ι (fun _ => E × ℝ) _ _ (fun _ => inferInstance) (f.ind x hx))
  have := L.hasMFDerivAt.comp x
    (f.embeddingPiTangent.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  convert hasMFDerivAt_unique this _
  refine (hasMFDerivAt_extChartAt (f.mem_chartAt_ind_source x hx)).congr_of_eventuallyEq ?_
  refine (f.eventuallyEq_one x hx).mono fun y hy => ?_
  simp only [L, embeddingPiTangent_coe, ContinuousLinearMap.coe_comp', (· ∘ ·),
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply]
  rw [hy, Pi.one_apply, one_smul]

theorem embeddingPiTangent_ker_mfderiv (x : M) (hx : x ∈ s) :
    (mfderiv I 𝓘(ℝ, ι → E × ℝ) f.embeddingPiTangent x).ker = ⊥ := by
  apply bot_unique
  rw [← (mdifferentiable_chart (f.c (f.ind x hx))).ker_mfderiv_eq_bot
      (f.mem_chartAt_ind_source x hx),
    ← comp_embeddingPiTangent_mfderiv]
  exact LinearMap.ker_le_ker_comp _ _

theorem embeddingPiTangent_injective_mfderiv (x : M) (hx : x ∈ s) :
    Injective (mfderiv I 𝓘(ℝ, ι → E × ℝ) f.embeddingPiTangent x) :=
  LinearMap.ker_eq_bot.1 (f.embeddingPiTangent_ker_mfderiv x hx)

/-- Baby version of the **Whitney weak embedding theorem**: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be immersed into the `n`-dimensional
Euclidean space. -/
theorem exists_immersion_euclidean {ι : Type*} [Finite ι] (f : SmoothBumpCovering ι I M) :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      CMDiff ∞ e ∧ Injective e ∧ ∀ x : M, Injective (mfderiv% e x) := by
  cases nonempty_fintype ι
  set F := EuclideanSpace ℝ (Fin <| finrank ℝ (ι → E × ℝ))
  letI : IsNoetherian ℝ (E × ℝ) := IsNoetherian.iff_fg.2 inferInstance
  letI : FiniteDimensional ℝ (ι → E × ℝ) := IsNoetherian.iff_fg.1 inferInstance
  set eEF : (ι → E × ℝ) ≃L[ℝ] F :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  refine ⟨_, eEF ∘ f.embeddingPiTangent,
    eEF.toDiffeomorph.contMDiff.comp f.embeddingPiTangent.contMDiff,
    eEF.injective.comp f.embeddingPiTangent_injective, fun x => ?_⟩
  rw [mfderiv_comp _ eEF.differentiableAt.mdifferentiableAt
      (f.embeddingPiTangent.contMDiff.mdifferentiableAt (by simp)),
    eEF.mfderiv_eq]
  exact eEF.injective.comp (f.embeddingPiTangent_injective_mfderiv _ trivial)

end SmoothBumpCovering

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
theorem exists_embedding_euclidean_of_compact [T2Space M] [CompactSpace M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      CMDiff ∞ e ∧ IsClosedEmbedding e ∧ ∀ x : M, Injective (mfderiv% e x) := by
  rcases SmoothBumpCovering.exists_isSubordinate I isClosed_univ fun (x : M) _ => univ_mem with
    ⟨ι, f, -⟩
  haveI := f.fintype
  rcases f.exists_immersion_euclidean with ⟨n, e, hsmooth, hinj, hinj_mfderiv⟩
  exact ⟨n, e, hsmooth, hsmooth.continuous.isClosedEmbedding hinj, hinj_mfderiv⟩
