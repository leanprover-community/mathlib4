/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation

/-! # The bundle of alternating maps between `C^n` vector bundles over the same base space is `C^n`

Here we show that the bundle of continuous alternating linear maps is a `C^n` vector bundle,
when the base field has characteristic zero.

We also show that applying a smooth family of alternating maps to smooth families of vectors gives
a smooth result, in several versions.
-/

public section

noncomputable section

open Bundle Set OpenPartialHomeomorph ContinuousAlternatingMap Pretrivialization FiberBundle

open scoped Manifold Bundle Topology

section

variable {𝕜 B F₁ F₂ M ι : Type*} {n : WithTop ℕ∞} [Fintype ι]
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

local notation "AE₁E₂" => TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun (b : B) ↦ E₁ b [⋀^ι]→L[𝕜] E₂ b)

section

theorem contMDiffOn_continuousAlternatingMapCoordChange [CharZero 𝕜]
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    CMDiff[e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)] n
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂') := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine (h₁.mono ?_).continuousAlternatingMapCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

theorem chartAt_continuousAlternatingMap (y₀ y : AE₁E₂) :
    chartAt (ModelProd HB (F₁ [⋀^ι]→L[𝕜] F₂)) y₀ y =
      (chartAt HB y₀.1 y.1, inCoordinates F₁ F₂ y₀.1 y.1 y₀.1 y.1 y.2) := by
  rw [FiberBundle.chartedSpace_chartAt, trans_apply, OpenPartialHomeomorph.prod_apply,
    Trivialization.coe_coe, OpenPartialHomeomorph.refl_apply, Function.id_def,
    trivializationAt_continuousAlternatingMap_apply]

theorem contMDiffWithinAt_continuousAlternatingMap_bundle (f : M → AE₁E₂) {s : Set M} {x₀ : M} :
    CMDiffAt[s] n f x₀ ↔
      CMDiffAt[s] n (fun x ↦ (f x).1) x₀ ∧
        CMDiffAt[s] n
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffWithinAt_totalSpace

theorem contMDiffAt_continuousAlternatingMap_bundle (f : M → AE₁E₂) {x₀ : M} :
    CMDiffAt n f x₀ ↔
      CMDiffAt n (fun x ↦ (f x).1) x₀ ∧ CMDiffAt n
        (fun x ↦ inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffAt_totalSpace

end

section

theorem mdifferentiableOn_continuousAlternatingMapCoordChange [CharZero 𝕜]
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    MDiff[e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)]
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂') := by
  apply ContMDiffOn.mdifferentiableOn _ one_ne_zero
  exact contMDiffOn_continuousAlternatingMapCoordChange

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

theorem mdifferentiableWithinAt_continuousAlternatingMap_bundle
    (f : M → AE₁E₂) {s : Set M} {x₀ : M} :
    MDiffAt[s] f x₀ ↔
      MDiffAt[s] (fun x ↦ (f x).1) x₀ ∧
        MDiffAt[s]
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableWithinAt_totalSpace IB ..

theorem mdifferentiableAt_continuousAlternatingMap_bundle (f : M → AE₁E₂) {x₀ : M} :
    MDiffAt f x₀ ↔
      MDiffAt (fun x ↦ (f x).1) x₀ ∧
        MDiffAt (fun x ↦ inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableAt_totalSpace ..

end

variable [CharZero 𝕜] [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

instance Bundle.continuousAlternatingMap.vectorPrebundle.isContMDiff :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange,
      continuousAlternatingMapCoordChange_apply⟩

instance ContMDiffVectorBundle.continuousAlternatingMap :
    ContMDiffVectorBundle n (F₁ [⋀^ι]→L[𝕜] F₂) ((fun (b : B) ↦ E₁ b [⋀^ι]→L[𝕜] E₂ b)) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end

section

/- Declare two manifolds `B₁` and `B₂` (with models `IB₁ : HB₁ → EB₁` and `IB₂ : HB₂ → EB₂`),
and two vector bundles `E₁` and `E₂` respectively over `B₁` and `B₂` (with model fibers
`F₁` and `F₂`).

Also a third manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M ι : Type*} [Fintype ι]
  {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB₁ : Type*}
  [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁] {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*}
  [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂] {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : WithTop ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M → B₁} {b₂ : M → B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) [⋀^ι]→L[𝕜] E₂ (b₂ m)} {v : ι → Π (m : M), E₁ (b₁ m)} {s : Set M}

/-- Consider `C^n` maps `v₁, ..., vᵢ : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`,
and another base map `b₂ : M → B₂`. Given alternating maps `ϕ m : E₁ (b₁ m) [⋀^ι]→L[𝕜] E₂ (b₂ m)`
depending smoothly on `m`, one can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the
resulting map is `C^n`.

Note that the smoothness of `ϕ` cannot always be stated as smoothness of a map into a manifold,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only when `b₁` and `b₂` are
globally smooth, but we want to apply this lemma with only local information. Therefore, we
formulate it using smoothness of `ϕ` read in coordinates.

Version for `ContMDiffWithinAt`. We also give a version for `ContMDiffAt`, but no version for
`ContMDiffOn` or `ContMDiff` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed without
`inCoordinates`, see `ContMDiffWithinAt.continuousAlternatingMap_bundle_apply`.
-/
lemma ContMDiffWithinAt.continuousAlternatingMap_apply_of_inCoordinates
    (hϕ : CMDiffAt[s] n
      (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ∀ i, CMDiffAt[s] n (fun m ↦ (v i m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt[s] n b₂ m₀) :
    CMDiffAt[s] n (fun m ↦ (ϕ m (fun i ↦ v i m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← contMDiffWithinAt_insert_self] at hϕ hb₂ ⊢
  replace hv : ∀ i, CMDiffAt[insert m₀ s] n (fun m ↦ (v i m : TotalSpace F₁ E₁)) m₀ := by
    intro i
    rw [contMDiffWithinAt_insert_self]
    exact hv i
  simp_rw [contMDiffWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContMDiffWithinAt.continuousAlternatingMap_apply hϕ
    (fun i ↦ (hv i).2)).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
      apply hb₂.continuousWithinAt
      apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
      exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · filter_upwards [A'] with m h'm
    rw [inCoordinates_eq_of_mem_baseSet₂ _ _ h'm]
    simp only [compContinuousLinearMap_apply, ContinuousLinearMap.compContinuousAlternatingMap_coe,
      ContinuousLinearEquiv.coe_coe, Trivialization.continuousLinearEquivAt_apply,
      Function.comp_apply]
    congr
    ext i
    exact hι.elim i
  · have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
      apply (hv i₀).1.continuousWithinAt
      apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
      exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
    filter_upwards [A, A'] with m hm h'm
    rw [inCoordinates_eq _ _ hm h'm]
    simp only [compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
      Trivialization.continuousLinearEquivAt_symm_apply,
      ContinuousLinearMap.compContinuousAlternatingMap_coe,
      Trivialization.continuousLinearEquivAt_apply, Function.comp_apply]
    congr
    ext i
    simp [*]

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another base map `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending smoothly
on `m`, one can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

Note that the smoothness of `ϕ` cannot always be stated as smoothness of a map into a manifold,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only when `b₁` and `b₂` are
globally smooth, but we want to apply this lemma with only local information. Therefore, we
formulate it using smoothness of `ϕ` read in coordinates.

Version for `ContMDiffAt`. We also give a version for `ContMDiffWithinAt`, but no version for
`ContMDiffOn` or `ContMDiff` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed without
`inCoordinates`, see `ContMDiffAt.clm_bundle_apply`.
-/
lemma ContMDiffAt.continuousAlternatingMap_apply_of_inCoordinates
    (hϕ : CMDiffAt n
      (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ∀ i, CMDiffAt n (fun m ↦ (v i m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt n b₂ m₀) :
    CMDiffAt n (fun m ↦ (ϕ m (fun i ↦ v i m) : TotalSpace F₂ E₂)) m₀ := by
  simp_rw [← contMDiffWithinAt_univ] at hϕ hv hb₂ ⊢
  exact ContMDiffWithinAt.continuousAlternatingMap_apply_of_inCoordinates hϕ hv hb₂

/-- Consider differentiable maps `v₁, ..., vᵢ : M → E₁` to a vector bundle, over a base
map `b₁ : M → B₁`, and another base map `b₂ : M → B₂`. Given alternating maps
`ϕ m : E₁ (b₁ m) [⋀^ι]→L[𝕜] E₂ (b₂ m)` depending differentiably on `m`, one can
apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is differentiable.

Note that the differentiability of `ϕ` cannot always be stated as differentiability of a map into
a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only
when `b₁` and `b₂` are globally smooth, but we want to apply this lemma with only local information.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableWithinAt`. We also give a version for `MDifferentiableAt`, but no
version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written in coordinates,
only makes sense around a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed without
`inCoordinates`, see `MDifferentiableWithinAt.continuousAlternatingMap_bundle_apply`.
-/
lemma MDifferentiableWithinAt.continuousAlternatingMap_apply_of_inCoordinates
    (hϕ : MDiffAt[s]
      (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ∀ i, MDiffAt[s] (fun m ↦ (v i m : TotalSpace F₁ E₁)) m₀) (hb₂ : MDiffAt[s] b₂ m₀) :
    MDiffAt[s] (fun m ↦ (ϕ m (fun i ↦ v i m) : TotalSpace F₂ E₂)) m₀ := by
  simp_rw [mdifferentiableWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (MDifferentiableWithinAt.continuousAlternatingMap_apply hϕ
    (fun i ↦ (hv i).2)).congr_of_eventuallyEq_insert ?_
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
      apply hb₂.insert.continuousWithinAt
      apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
      exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · filter_upwards [A'] with m h'm
    rw [inCoordinates_eq_of_mem_baseSet₂ _ _ h'm]
    simp only [compContinuousLinearMap_apply, ContinuousLinearMap.compContinuousAlternatingMap_coe,
      ContinuousLinearEquiv.coe_coe, Trivialization.continuousLinearEquivAt_apply,
      Function.comp_apply]
    congr
    ext i
    exact hι.elim i
  · have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
      apply (hv i₀).1.insert.continuousWithinAt
      apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
      exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
    filter_upwards [A, A'] with m hm h'm
    rw [inCoordinates_eq _ _ hm h'm]
    simp only [compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
      Trivialization.continuousLinearEquivAt_symm_apply,
      ContinuousLinearMap.compContinuousAlternatingMap_coe,
      Trivialization.continuousLinearEquivAt_apply, Function.comp_apply]
    congr
    ext i
    simp [*]

/-- Consider differentiable maps `v₁, ..., vᵢ : M → E₁` to a vector bundle, over a base
map `b₁ : M → B₁`, and another base map `b₂ : M → B₂`. Given alternating maps
`ϕ m : E₁ (b₁ m) [⋀^ι]→L[𝕜] E₂ (b₂ m)` depending differentiably on `m`, one can
apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is differentiable.

Note that the differentiability of `ϕ` cannot always be stated as differentiability of a map into
a manifold, as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only
when `b₁` and `b₂` are globally smooth, but we want to apply this lemma with only local information.
Therefore, we formulate it using differentiability of `ϕ` read in coordinates.

Version for `MDifferentiableAt`. We also give a version for `MDifferentiableWithinAt`, but no
version for `MDifferentiableOn` or `MDifferentiable` as our assumption, written in coordinates,
only makes sense around a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed without
`inCoordinates`, see `MDifferentiableAt.continuousAlternatingMap_bundle_apply`.
-/
lemma MDifferentiableAt.continuousAlternatingMap_apply_of_inCoordinates
    (hϕ : MDiffAt
      (fun m ↦ inCoordinates F₁ F₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ∀ i, MDiffAt (fun m ↦ (v i m : TotalSpace F₁ E₁)) m₀) (hb₂ : MDiffAt b₂ m₀) :
    MDiffAt (fun m ↦ (ϕ m (fun i ↦ v i m) : TotalSpace F₂ E₂)) m₀ := by
  simp_rw [← mdifferentiableWithinAt_univ] at hϕ hv hb₂ ⊢
  exact MDifferentiableWithinAt.continuousAlternatingMap_apply_of_inCoordinates hϕ hv hb₂

end

section

/- Declare a manifold `B` (with model `IB : HB → EB`),
and three vector bundles `E₁`, `E₂` and `E₃` over `B` (with model fibers `F₁`, `F₂` and `F₃`).

Also a second manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 B F₁ F₂ F₃ M ι : Type*} [Fintype ι] [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)]
  [∀ x, Module 𝕜 (E₃ x)] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  {b : M → B} {v : ι → Π x, E₁ (b x)} {s : Set M} {x : M}
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : Π x, (E₁ (b x) [⋀^ι]→L[𝕜] E₂ (b x))}

/-- Consider `C^n` maps `vᵢ : M → E₁` to a vector bundle, over a base map `b : M → B`, and
alternating linear maps `ϕ m : E₁ (b m) [⋀^ι]→ E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is `C^n`.

We give here a version of this statement within a set at a point. -/
lemma ContMDiffWithinAt.continuousAlternatingMap_bundle_apply
    (hϕ : CMDiffAt[s] n
      (fun m ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x [⋀^ι]→L[𝕜] E₂ x))
        (b m) (ϕ m)) x)
    (hv : ∀ i, CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) x) :
    CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) x := by
  simp only [contMDiffWithinAt_continuousAlternatingMap_bundle] at hϕ
  exact hϕ.2.continuousAlternatingMap_apply_of_inCoordinates hv hϕ.1

/-- Consider `C^n` maps `vᵢ : M → E₁` to a vector bundle, over a base map `b : M → B`, and
alternating linear maps `ϕ m : E₁ (b m) [⋀^ι]→ E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is `C^n`.

We give here a version of this statement at a point. -/
lemma ContMDiffAt.continuousAlternatingMap_bundle_apply
    (hϕ : CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x [⋀^ι]→L[𝕜] E₂ x))
        (b m) (ϕ m)) x)
    (hv : ∀ i, CMDiffAt n (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) x) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) x :=
  ContMDiffWithinAt.continuousAlternatingMap_bundle_apply hϕ hv

/-- Consider `C^n` maps `vᵢ : M → E₁` to a vector bundle, over a base map `b : M → B`, and
alternating linear maps `ϕ m : E₁ (b m) [⋀^ι]→ E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is `C^n`.

We give here a version of this statement on a set. -/
lemma ContMDiffOn.continuousAlternatingMap_bundle_apply
    (hϕ : CMDiff[s] n
      (fun m ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x [⋀^ι]→L[𝕜] E₂ x))
        (b m) (ϕ m)))
    (hv : ∀ i, CMDiff[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m))) :
    CMDiff[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) :=
  fun x hx ↦ (hϕ x hx).continuousAlternatingMap_bundle_apply (fun i ↦ hv i x hx)

/-- Consider `C^n` maps `vᵢ : M → E₁` to a vector bundle, over a base map `b : M → B`, and
alternating linear maps `ϕ m : E₁ (b m) [⋀^ι]→ E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is `C^n`. -/
lemma ContMDiff.continuousAlternatingMap_bundle_apply
    (hϕ : CMDiff n
      (fun m ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x [⋀^ι]→L[𝕜] E₂ x))
        (b m) (ϕ m)))
    (hv : ∀ i, CMDiff n (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m))) :
    CMDiff n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) :=
  fun x ↦ (hϕ x).continuousAlternatingMap_bundle_apply (fun i ↦ hv i x)

/-- Consider differentiable maps `vᵢ : M → E₁` to a vector bundle, over a base map `b : M → B`, and
alternating linear maps `ϕ m : E₁ (b m) [⋀^ι]→ E₂ (b m)` depending differentiably on `m`.
One can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is differentiable.

We give here a version of this statement within a set at a point. -/
lemma MDifferentiableWithinAt.continuousAlternatingMap_bundle_apply
    (hϕ : MDiffAt[s]
      (fun m ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x [⋀^ι]→L[𝕜] E₂ x))
        (b m) (ϕ m)) x)
    (hv : ∀ i, MDiffAt[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) x) :
    MDiffAt[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) x := by
  simp only [mdifferentiableWithinAt_continuousAlternatingMap_bundle] at hϕ
  exact hϕ.2.continuousAlternatingMap_apply_of_inCoordinates hv hϕ.1

/-- Consider differentiable maps `vᵢ : M → E₁` to a vector bundle, over a base map `b : M → B`, and
alternating linear maps `ϕ m : E₁ (b m) [⋀^ι]→ E₂ (b m)` depending differentiably on `m`.
One can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is differentiable.

We give here a version of this statement at a point. -/
lemma MDifferentiableAt.continuousAlternatingMap_bundle_apply
    (hϕ : MDiffAt
      (fun m ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x [⋀^ι]→L[𝕜] E₂ x))
        (b m) (ϕ m)) x)
    (hv : ∀ i, MDiffAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m)) x) :
    MDiffAt (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) x :=
  MDifferentiableWithinAt.continuousAlternatingMap_bundle_apply hϕ hv

/-- Consider differentiable maps `vᵢ : M → E₁` to a vector bundle, over a base map `b : M → B`, and
alternating linear maps `ϕ m : E₁ (b m) [⋀^ι]→ E₂ (b m)` depending differentiably on `m`.
One can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is differentiable.

We give here a version of this statement on a set. -/
lemma MDifferentiableOn.continuousAlternatingMap_bundle_apply
    (hϕ : MDiff[s]
      (fun m ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x [⋀^ι]→L[𝕜] E₂ x))
        (b m) (ϕ m)))
    (hv : ∀ i, MDiff[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m))) :
    MDiff[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) :=
  fun x hx ↦ (hϕ x hx).continuousAlternatingMap_bundle_apply (fun i ↦ hv i x hx)

/-- Consider differentiable maps `vᵢ : M → E₁` to a vector bundle, over a base map `b : M → B`, and
alternating linear maps `ϕ m : E₁ (b m) [⋀^ι]→ E₂ (b m)` depending differentiably on `m`.
One can apply `ϕ m` to `(v₁ m, ..., vᵢ m)`, and the resulting map is differentiable. -/
lemma MDifferentiable.continuousAlternatingMap_bundle_apply
    (hϕ : MDiff
      (fun m ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x [⋀^ι]→L[𝕜] E₂ x))
        (b m) (ϕ m)))
    (hv : ∀ i, MDiff (fun m ↦ TotalSpace.mk' F₁ (b m) (v i m))) :
    MDiff (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (fun i ↦ v i m))) :=
  fun x ↦ (hϕ x).continuousAlternatingMap_bundle_apply (fun i ↦ hv i x)

end
