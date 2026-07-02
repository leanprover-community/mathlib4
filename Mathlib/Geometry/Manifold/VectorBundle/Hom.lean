/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Homs of `C^n` vector bundles over the same base space

Here we show that the bundle of continuous linear maps is a `C^n` vector bundle. We also show
that applying a smooth family of linear maps to a smooth family of vectors gives a smooth
result, in several versions.

Note that we only do this for bundles of linear maps, not for bundles of arbitrary semilinear maps.
Indeed, semilinear maps are typically not smooth. For instance, complex conjugation is not
`ℂ`-differentiable.
-/

public section

section -- By John McCarthy
open Bundle Set OpenPartialHomeomorph ContinuousLinearMap Pretrivialization
open scoped Manifold Bundle Topology
variable {𝕜 B F₁ : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)]
  [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]


lemma Bundle.Trivialization.ContMDiffAt_symm {k}
    [IsManifold IB k B]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    (e : Bundle.Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B))
    [MemTrivializationAtlas e] {x : B} (hx : x ∈ e.baseSet) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁)) k
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁) m (Trivialization.symmL 𝕜 e m)) x := by
  have hx' : x ∈ (trivializationAt F₁ E₁ x).baseSet := mem_baseSet_trivializationAt F₁ E₁ x
  refine contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, ?_⟩
  apply (contMDiffAt_coordChangeL hx hx').congr_of_eventuallyEq
  filter_upwards [(e.open_baseSet.inter (trivializationAt F₁ E₁ x).open_baseSet).mem_nhds
    ⟨hx, hx'⟩] with b hb
  ext v
  change ((trivializationAt F₁ E₁ x).continuousLinearMapAt 𝕜 b)
      ((e.symmL 𝕜 b) ((Bundle.Trivial.trivialization B F₁).symmL 𝕜 b v)) =
    (e.coordChangeL 𝕜 (trivializationAt F₁ E₁ x) b) v
  simp [e.symmL_apply hb.1, continuousLinearMapAt_apply_of_mem 𝕜 _ hb.2,
    coordChangeL_apply' e _ hb, e.mk_symm hb.1]
end

/-- Composition of a function followed by a dependent function. -/
@[inline, reducible]
def Function.dcomp' {α β : Sort*} {γ : β → Sort*} (f : (y : β) → γ y)
    (g : α → β) := fun x => f (g x)

@[inherit_doc] infixr:80 " ∘'' " => Function.dcomp'

noncomputable section

open Bundle Set OpenPartialHomeomorph ContinuousLinearMap Pretrivialization

open scoped Manifold Bundle Topology

section

variable {𝕜 B F₁ F₂ M : Type*} {n : WithTop ℕ∞}
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

local notation "LE₁E₂" => TotalSpace (F₁ →L[𝕜] F₂) (fun (b : B) ↦ E₁ b →L[𝕜] E₂ b)

section

theorem contMDiffOn_continuousLinearMapCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    CMDiff[e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)] n
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂') := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

set_option backward.isDefEq.respectTransparency false in
theorem hom_chart (y₀ y : LE₁E₂) :
    chartAt (ModelProd HB (F₁ →L[𝕜] F₂)) y₀ y =
      (chartAt HB y₀.1 y.1, inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2) := by
  rw [FiberBundle.chartedSpace_chartAt, trans_apply, OpenPartialHomeomorph.prod_apply,
    Trivialization.coe_coe, OpenPartialHomeomorph.refl_apply, Function.id_def,
    hom_trivializationAt_apply]

theorem contMDiffWithinAt_hom_bundle (f : M → LE₁E₂) {s : Set M} {x₀ : M} :
    CMDiffAt[s] n f x₀ ↔
      CMDiffAt[s] n (fun x ↦ (f x).1) x₀ ∧
        CMDiffAt[s] n
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffWithinAt_totalSpace

theorem contMDiffAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
    CMDiffAt n f x₀ ↔
      CMDiffAt n (fun x ↦ (f x).1) x₀ ∧ CMDiffAt n
        (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffAt_totalSpace

end

section

theorem mdifferentiableOn_continuousLinearMapCoordChange
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    MDiff[e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)]
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂') := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := 1) |>.mdifferentiableOn one_ne_zero
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := 1) |>.mdifferentiableOn one_ne_zero
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

theorem mdifferentiableWithinAt_hom_bundle (f : M → LE₁E₂) {s : Set M} {x₀ : M} :
    MDiffAt[s] f x₀ ↔
      MDiffAt[s] (fun x ↦ (f x).1) x₀ ∧
        MDiffAt[s]
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableWithinAt_totalSpace IB ..

theorem mdifferentiableAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
    MDiffAt f x₀ ↔
      MDiffAt (fun x ↦ (f x).1) x₀ ∧
        MDiffAt (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableAt_totalSpace ..

end

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

instance Bundle.ContinuousLinearMap.vectorPrebundle.isContMDiff :
    (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂',
      contMDiffOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply (RingHom.id 𝕜) e₁ e₁' e₂ e₂'⟩

instance ContMDiffVectorBundle.continuousLinearMap :
    ContMDiffVectorBundle n (F₁ →L[𝕜] F₂) ((fun (b : B) ↦ E₁ b →L[𝕜] E₂ b)) IB :=
  (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end

section

/- Declare two manifolds `B₁` and `B₂` (with models `IB₁ : HB₁ → EB₁` and `IB₂ : HB₂ → EB₂`),
and two vector bundles `E₁` and `E₂` respectively over `B₁` and `B₂` (with model fibers
`F₁` and `F₂`).

Also a third manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
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
  {ϕ : Π (m : M), E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another base map `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending smoothly
on `m`, one can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

Note that the smoothness of `ϕ` cannot always be stated as smoothness of a map into a manifold,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only when `b₁` and `b₂` are
globally smooth, but we want to apply this lemma with only local information. Therefore, we
formulate it using smoothness of `ϕ` read in coordinates.

Version for `ContMDiffWithinAt`. We also give a version for `ContMDiffAt`, but no version for
`ContMDiffOn` or `ContMDiff` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed without
`inCoordinates`, see `ContMDiffWithinAt.clm_bundle_apply`.
-/
lemma ContMDiffWithinAt.clm_apply_of_inCoordinates
    (hϕ : CMDiffAt[s] n
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : CMDiffAt[s] n (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt[s] n b₂ m₀) :
    CMDiffAt[s] n (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← contMDiffWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [contMDiffWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContMDiffWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
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
lemma ContMDiffAt.clm_apply_of_inCoordinates
    (hϕ : CMDiffAt n (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : CMDiffAt n (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt n b₂ m₀) :
    CMDiffAt n (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← contMDiffWithinAt_univ] at hϕ hv hb₂ ⊢
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

end

section

/- Declare a manifold `B` (with model `IB : HB → EB`),
and three vector bundles `E₁`, `E₂` and `E₃` over `B` (with model fibers `F₁`, `F₂` and `F₃`).

Also a second manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 B F₁ F₂ F₃ M : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
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
  {b : M → B} {v : ∀ x, E₁ (b x)} {s : Set M} {x : M}

section OneVariable

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x))}

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement within a set at a point. -/
lemma ContMDiffWithinAt.clm_bundle_apply
    (hϕ : CMDiffAt[s] n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [contMDiffWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement at a point. -/
lemma ContMDiffAt.clm_bundle_apply
    (hϕ : CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : CMDiffAt n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x :=
  ContMDiffWithinAt.clm_bundle_apply hϕ hv


lemma ContMDiffAt.clm_bundle_apply_trivial_source {ψ : ∀ x, F₁ →L[𝕜] E₂ (b x)}
    (hψ : CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (F₁ →L[𝕜] E₂ x)) (b m) (ψ m)) x)
    {w : M → F₁}
    (hb : CMDiffAt n b x) (hw : CMDiffAt n w x) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' F₂ (b m) (ψ m (w m))) x := by
  apply ContMDiffAt.clm_bundle_apply (E₁ := Bundle.Trivial B F₁) (F₁ := F₁)
  · apply hψ
  · simp [contMDiffAt_totalSpace, hb, hw]

lemma Bundle.Trivialization.contMDiffAt_symm_const {k}
    [IsManifold IB k B]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    (e : Bundle.Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B))
    [MemTrivializationAtlas e] {x : B} (hx : x ∈ e.baseSet) (u : F₁) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁)) k
      (fun m ↦ TotalSpace.mk' F₁ m (Trivialization.symmL 𝕜 e m u)) x := by
  apply ContMDiffAt.clm_bundle_apply_trivial_source
  · exact e.ContMDiffAt_symm hx
  · exact contMDiffAt_id
  · exact contMDiffAt_const

-- unused but nice for symmetry
lemma ContMDiffAt.clm_bundle_apply_trivial_target {ψ : ∀ x, (E₁ (b x) →L[𝕜] F₂)}
    (hψ : CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] F₂)) (b m) (ψ m)) x)
    (hv : CMDiffAt n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    CMDiffAt n (fun m ↦ ψ m (v m)) x := by
  sorry

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement on a set. -/
lemma ContMDiffOn.clm_bundle_apply
    (hϕ : CMDiff[s] n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : CMDiff[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    CMDiff[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply (hv x hx)

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
lemma ContMDiff.clm_bundle_apply
    (hϕ : CMDiff n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : CMDiff n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    CMDiff n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x ↦ (hϕ x).clm_bundle_apply (hv x)


section
variable [CompleteSpace 𝕜] [IsManifold IB 1 B]
    [FiniteDimensional 𝕜 F₁]
    [ContMDiffVectorBundle 1 F₁ E₁ IB]
    [FiniteDimensional 𝕜 F₂]
     [ContMDiffVectorBundle 1 F₂ E₂ IB]
    {φ : Π x : B, E₁ x →L[𝕜] E₂ x}


omit [CompleteSpace 𝕜] [IsManifold IB 1 B] [FiniteDimensional 𝕜 F₁]
  [ContMDiffVectorBundle 1 F₁ E₁ IB] in
lemma contMDiffOn_symm_of_memTrivializationAtlas {k}
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    (e : Bundle.Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B))
    [MemTrivializationAtlas e] :
    CMDiff[e.target] k e.toOpenPartialHomeomorph.symm :=
  e.contMDiffOn_symm

omit [CompleteSpace 𝕜] [IsManifold IB 1 B] [FiniteDimensional 𝕜 F₁]
  [ContMDiffVectorBundle 1 F₁ E₁ IB] in
lemma contMDiffAt_symm_of_memTrivializationAtlas {k}
    [IsManifold IB k B]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    (e : Bundle.Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B))
    [MemTrivializationAtlas e] {x : B} (hx : x ∈ e.baseSet) (u : F₁) :
    CMDiffAt k e.toOpenPartialHomeomorph.symm (x, u) := by
  apply e.contMDiffOn_symm |>.contMDiffAt (e.open_target.mem_nhds ?_)
  simp [e.target_eq, hx]

omit [CompleteSpace 𝕜] [IsManifold IB 1 B] [FiniteDimensional 𝕜 F₁]
     [ContMDiffVectorBundle 1 F₁ E₁ IB] in
lemma Bundle.Trivialization.contMDiffWithinAt_apply {k}
    [IsManifold IB k B]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    (e : Bundle.Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B))
    [MemTrivializationAtlas e] {x : B} (hx : x ∈ e.baseSet) {s : Set B}
    {σ : Π b, E₁ b} (hσ : CMDiffAt[s] k (T% σ) x) :
    CMDiffAt[s] k (fun b ↦ e.continuousLinearMapAt 𝕜 b (σ b)) x := by
  apply (contMDiffWithinAt_section s hx).mp hσ |>.congr_of_eventuallyEq
  · apply mem_nhdsWithin_of_mem_nhds
    filter_upwards [e.open_baseSet.mem_nhds hx] with x' hx'
    simp [hx']
  · simp [hx]

-- Note: In the next lemma, the assumption `∀ᶠ b in 𝓝 x, CMDiffWithinAt k (T% σ) b` is almost
-- equivalent to `CMDiffWithinAt k (T% σ) x` but not quite: it is stronger if `k = ∞`.
omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F₁ E₁ IB]
  [FiniteDimensional 𝕜 F₂] [ContMDiffVectorBundle 1 F₂ E₂ IB] in
lemma ContMDiffWithinAt.clm_bundle_of_apply {k}
    [FiniteDimensional 𝕜 EB]
    [IsManifold IB k B]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₂ E₂ IB] {s : Set B} {x : B}
    (h : ∀ (σ : Π x : B, E₁ x),
      (∀ᶠ b in 𝓝 x, CMDiffAt[s] k (T% σ) b) → CMDiffAt[s] k (T% (fun x ↦ φ x (σ x))) x) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) k
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x)) s x := by
  refine (contMDiffWithinAt_hom_bundle fun x ↦ ⟨x, φ x⟩).mpr ⟨contMDiffWithinAt_id, ?_⟩
  rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  set t₁ := trivializationAt F₁ E₁ x
  set t₂ := trivializationAt F₂ E₂ x
  apply contDiffWithinAt_clm_apply.mpr
  set ψ := extChartAt IB x
  intro u
  have C₀ : CMDiffAt[s] k (fun b ↦ t₂.continuousLinearMapAt 𝕜 b (φ b (t₁.symmL 𝕜 b u)))
      (ψ.symm (ψ x)) := by
    rw [extChartAt_to_inv x]
    apply t₂.contMDiffWithinAt_apply (FiberBundle.mem_baseSet_trivializationAt' x)
    apply h
    filter_upwards [t₁.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)] with
      x' hx'
    exact (t₁.contMDiffAt_symm_const hx' _).contMDiffWithinAt
  have := ContMDiffWithinAt.comp' (ψ x) C₀ (contMDiffWithinAt_extChartAt_symm_range_self x)
  simpa [inter_comm, t₁, t₂, contMDiffWithinAt_iff_contDiffWithinAt, inCoordinates]

-- Note: In the next lemma, the assumption `∀ᶠ b in 𝓝 x, CMDiffAt k (T% σ) b` is almost equivalent
-- to `CMDiffAt k (T% σ) x` but not quite: it is stronger if `k = ∞`.
omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F₁ E₁ IB]
  [FiniteDimensional 𝕜 F₂] [ContMDiffVectorBundle 1 F₂ E₂ IB] in
lemma ContMDiffAt.clm_bundle_of_apply {k}
    [FiniteDimensional 𝕜 EB]
    [IsManifold IB k B]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₂ E₂ IB] {x : B}
    (h : ∀ (σ : Π x : B, E₁ x),
      (∀ᶠ b in 𝓝 x, CMDiffAt k (T% σ) b) → CMDiffAt k (T% (fun x ↦ φ x (σ x))) x) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) k (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x))
    x := by
  simp_rw [← contMDiffWithinAt_univ] at h ⊢
  exact ContMDiffWithinAt.clm_bundle_of_apply (fun σ hσ ↦ h σ hσ)

omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F₁ E₁ IB]
  [FiniteDimensional 𝕜 F₂] [ContMDiffVectorBundle 1 F₂ E₂ IB] in
lemma ContMDiffOn.clm_bundle_of_apply {k}
    [FiniteDimensional 𝕜 EB]
    [IsManifold IB k B]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₂ E₂ IB] {s : Set B}
    (h : ∀ (σ : Π x : B, E₁ x),
      (∀ x ∈ s, (∀ᶠ b in 𝓝 x, CMDiffAt[s] k (T% σ) b) → CMDiffAt[s] k (T% (fun x ↦ φ x (σ x))) x)) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) k (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x))
    s :=
  fun x hx ↦ ContMDiffWithinAt.clm_bundle_of_apply (fun σ hσ ↦ h σ x hx hσ)

omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F₁ E₁ IB]
  [FiniteDimensional 𝕜 F₂] [ContMDiffVectorBundle 1 F₂ E₂ IB] in
lemma ContMDiff.clm_bundle_of_apply {k}
    [FiniteDimensional 𝕜 EB]
    [IsManifold IB k B]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₂ E₂ IB]
    (h : ∀ (σ : Π x : B, E₁ x),
      (∀ x, (∀ᶠ b in 𝓝 x, CMDiffAt k (T% σ) b) → CMDiffAt k (T% (fun x ↦ φ x (σ x))) x)) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) k (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x)) :=
  fun x ↦ ContMDiffAt.clm_bundle_of_apply fun σ ↦ h σ x

-- Note: In the next lemma, the assumption `∀ᶠ b in 𝓝 x, CMDiffWithinAt k (T% σ) b` is almost
-- equivalent to `CMDiffWithinAt k (T% σ) x` but not quite: it is stronger if `k = ∞`.
omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F₁ E₁ IB]
  [FiniteDimensional 𝕜 F₂] [ContMDiffVectorBundle 1 F₂ E₂ IB] in
/-- Version allowing for the loss of a single derivative: we assume that applying `φ` to a
`C^{k+1}` section near `x` within a set `s` produces a `C^k` section near `x` within `s` -/
lemma ContMDiffWithinAt.clm_bundle_of_apply' {k}
    [FiniteDimensional 𝕜 EB]
    [IsManifold IB (k + 1) B] [ContMDiffVectorBundle (k + 1) F₁ E₁ IB]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₂ E₂ IB] {s : Set B} {x : B}
    (h : ∀ (σ : Π x : B, E₁ x),
      (∀ᶠ b in 𝓝 x, CMDiffAt[s] (k + 1) (T% σ) b) → CMDiffAt[s] k (T% (fun x ↦ φ x (σ x))) x) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) k
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x)) s x := by
  have : IsManifold IB k B := IsManifold.of_le (m := k) (n := k + 1) (by simp)
  refine (contMDiffWithinAt_hom_bundle fun x ↦ ⟨x, φ x⟩).mpr ⟨contMDiffWithinAt_id, ?_⟩
  rw [contMDiffWithinAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  set t₁ := trivializationAt F₁ E₁ x
  set t₂ := trivializationAt F₂ E₂ x
  apply contDiffWithinAt_clm_apply.mpr
  set ψ := extChartAt IB x
  intro u
  have C₀ : CMDiffAt[s] k (fun b ↦ t₂.continuousLinearMapAt 𝕜 b (φ b (t₁.symmL 𝕜 b u)))
      (ψ.symm (ψ x)) := by
    rw [extChartAt_to_inv x]
    apply t₂.contMDiffWithinAt_apply (FiberBundle.mem_baseSet_trivializationAt' x)
    apply h
    filter_upwards [t₁.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)] with
      x' hx'
    exact (t₁.contMDiffAt_symm_const hx' _).contMDiffWithinAt
  have := ContMDiffWithinAt.comp' (ψ x) C₀ (contMDiffWithinAt_extChartAt_symm_range_self x)
  simpa [inter_comm, t₁, t₂, contMDiffWithinAt_iff_contDiffWithinAt, inCoordinates]

omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F₁ E₁ IB]
  [FiniteDimensional 𝕜 F₂] [ContMDiffVectorBundle 1 F₂ E₂ IB] in
/-- Version allowing for the loss of a single derivative: we assume that applying `φ` to a
`C^{k+1}` section near `x` produces a `C^k` section near `x` -/
lemma ContMDiffAt.clm_bundle_of_apply' {k}
    [FiniteDimensional 𝕜 EB]
    [IsManifold IB (k + 1) B] [ContMDiffVectorBundle (k + 1) F₁ E₁ IB]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₂ E₂ IB] {x : B}
    (h : ∀ (σ : Π x : B, E₁ x),
      (∀ᶠ b in 𝓝 x, CMDiffAt (k + 1) (T% σ) b) → CMDiffAt k (T% (fun x ↦ φ x (σ x))) x) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) k (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x))
    x := by
  simp_rw [← contMDiffWithinAt_univ] at h ⊢
  exact ContMDiffWithinAt.clm_bundle_of_apply' (fun σ hσ ↦ h σ hσ)

omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F₁ E₁ IB]
  [FiniteDimensional 𝕜 F₂] [ContMDiffVectorBundle 1 F₂ E₂ IB] in
/-- Version allowing for the loss of a single derivative: we assume that applying `φ` to a
`C^{k+1}` section on `s` produces a `C^k` section on `s` -/
lemma ContMDiffOn.clm_bundle_of_apply' {k}
    [FiniteDimensional 𝕜 EB]
    [IsManifold IB (k + 1) B] [ContMDiffVectorBundle (k + 1) F₁ E₁ IB]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₂ E₂ IB] {s : Set B}
    (h : ∀ (σ : Π x : B, E₁ x), (∀ x ∈ s, (∀ᶠ b in 𝓝 x, CMDiffAt[s] (k + 1) (T% σ) b) →
      CMDiffAt[s] k (T% (fun x ↦ φ x (σ x))) x)) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) k (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x))
    s :=
  fun x hx ↦ ContMDiffWithinAt.clm_bundle_of_apply' (fun σ hσ ↦ h σ x hx hσ)

omit [IsManifold IB 1 B] [ContMDiffVectorBundle 1 F₁ E₁ IB]
  [FiniteDimensional 𝕜 F₂] [ContMDiffVectorBundle 1 F₂ E₂ IB] in
/-- Version allowing for the loss of a single derivative: we assume that applying `φ` to a
`C^{k+1}` section produces a `C^k` section -/
lemma ContMDiff.clm_bundle_of_apply' {k}
    [FiniteDimensional 𝕜 EB]
    [IsManifold IB (k + 1) B] [ContMDiffVectorBundle (k + 1) F₁ E₁ IB]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₂ E₂ IB]
    (h : ∀ (σ : Π x : B, E₁ x),
      (∀ x, (∀ᶠ b in 𝓝 x, CMDiffAt (k + 1) (T% σ) b) → CMDiffAt k (T% (fun x ↦ φ x (σ x))) x)) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) k (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) x (φ x)) :=
  fun x ↦ ContMDiffAt.clm_bundle_of_apply' fun σ ↦ h σ x

set_option linter.unusedSectionVars false in
lemma TensorialAt.apply_clm
    {φ : (Π x : B, E₁ x) → (Π x, E₂ x)} {x : B}
    (hφ : TensorialAt IB F₁ (φ · x) x)
    {σ : Π x : B, E₁ x} (hσ : MDiffAt (T% σ) x) :
    TensorialAt.mkHom (φ · x) x hφ (σ x) = φ σ x := by
  rw [mkHom_apply_eq_extend]
  exact hφ.pointwise (FiberBundle.mdifferentiableAt_extend ..) hσ
    <| FiberBundle.extend_apply_self F₁ (σ x)
end

/-- Criterion for a section of a Hom-bundle constructed using the tensoriality criterion to be
smooth. -/
theorem TensorialAt.contMDiff_mkHom
    [CompleteSpace 𝕜] {k} (hk : 1 ≤ k) [IsManifold IB k B]
    [FiniteDimensional 𝕜 EB]
    [FiniteDimensional 𝕜 F₁]
    [∀ (x : B), IsTopologicalAddGroup (E₁ x)] [∀ (x : B), ContinuousSMul 𝕜 (E₁ x)]
    [ContMDiffVectorBundle k F₁ E₁ IB]
    [FiniteDimensional 𝕜 F₂]
    [ContMDiffVectorBundle k F₂ E₂ IB]
    (φ : (Π x : B, E₁ x) → (Π x, E₂ x))
    (hφ : ∀ x, TensorialAt IB F₁ (φ · x) x)
    (φ_contMDiff : ∀ (σ : Π x : B, E₁ x), ∀ x, CMDiffAt k (T% σ) x → CMDiffAt k (T% (φ σ)) x) :
    -- elaborators not working here
    haveI : ContMDiffVectorBundle 1 F₁ E₁ IB := ContMDiffVectorBundle.of_le hk
    letI T (x : B) : TotalSpace (F₁ →L[𝕜] F₂) (fun x ↦ E₁ x →L[𝕜] E₂ x) :=
      ⟨x, TensorialAt.mkHom (φ · x) x (hφ x)⟩
    CMDiff k T := by
  have : IsManifold IB 1 B := IsManifold.of_le hk
  have : ContMDiffVectorBundle 1 F₁ E₁ IB := ContMDiffVectorBundle.of_le hk
  have : ContMDiffVectorBundle 1 F₂ E₂ IB := ContMDiffVectorBundle.of_le hk
  intro b
  apply ContMDiffAt.clm_bundle_of_apply fun σ hσ ↦ ?_
  have : ∀ᶠ x in 𝓝 b, TensorialAt.mkHom (φ · x) x (hφ x) (σ x) = φ σ x := by
    filter_upwards [hσ] with x hx
    apply TensorialAt.apply_clm (hφ x)
    exact hx.mdifferentiableAt (ENat.one_le_iff_ne_zero_withTop.mp hk)
  have : ∀ᶠ x in 𝓝 b,
      (⟨x, TensorialAt.mkHom (φ · x) x (hφ x) (σ x)⟩ : TotalSpace F₂ E₂) = ⟨x, φ σ x⟩ := by
    filter_upwards [this] with x hx
    simp [hx]
  exact (φ_contMDiff σ b hσ.self_of_nhds).congr_of_eventuallyEq this

end OneVariable

section OneVariable'

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x))}

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement within a set at a point. -/
lemma MDifferentiableWithinAt.clm_bundle_apply
    (hϕ : MDiffAt[s]
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : MDiffAt[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    MDiffAt[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [mdifferentiableWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement at a point. -/
lemma MDifferentiableAt.clm_bundle_apply
    (hϕ : MDiffAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : MDiffAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    MDiffAt (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x :=
  MDifferentiableWithinAt.clm_bundle_apply hϕ hv

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement on a set. -/
lemma MDifferentiableOn.clm_bundle_apply
    (hϕ : MDiff[s]
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : MDiff[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    MDiff[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply (hv x hx)

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable. -/
lemma MDifferentiable.clm_bundle_apply
    (hϕ : MDiff
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : MDiff (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    MDiff (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x ↦ (hϕ x).clm_bundle_apply (hv x)

end OneVariable'

section TwoVariables

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x) →L[𝕜] E₃ (b x))} {w : ∀ x, E₂ (b x)}

/-- Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement within a set at a point. -/
lemma ContMDiffWithinAt.clm_bundle_apply₂
    (hψ : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  hψ.clm_bundle_apply hv |>.clm_bundle_apply hw

/-- Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement at a point. -/
lemma ContMDiffAt.clm_bundle_apply₂
    (hψ : CMDiffAt n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : CMDiffAt n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : CMDiffAt n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  ContMDiffWithinAt.clm_bundle_apply₂ hψ hv hw

/-- Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement on a set. -/
lemma ContMDiffOn.clm_bundle_apply₂
    (hψ : CMDiff[s] n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : CMDiff[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : CMDiff[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    CMDiff[s] n (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x hx ↦ (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/-- Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
lemma ContMDiff.clm_bundle_apply₂
    (hψ : CMDiff n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : CMDiff n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : CMDiff n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    CMDiff n (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x ↦ (hψ x).clm_bundle_apply₂ (hv x) (hw x)

end TwoVariables

section TwoVariables'

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x) →L[𝕜] E₃ (b x))} {w : ∀ x, E₂ (b x)}

/-- Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement within a set at a point. -/
lemma MDifferentiableWithinAt.clm_bundle_apply₂
    (hψ : MDiffAt[s] (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : MDiffAt[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : MDiffAt[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    MDiffAt[s] (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  hψ.clm_bundle_apply hv |>.clm_bundle_apply hw

/-- Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement at a point. -/
lemma MDifferentiableAt.clm_bundle_apply₂
    (hψ : MDiffAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : MDiffAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : MDiffAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    MDiffAt (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  MDifferentiableWithinAt.clm_bundle_apply₂ hψ hv hw

/-- Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement on a set. -/
lemma MDifferentiableOn.clm_bundle_apply₂
    (hψ : MDiff[s] (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : MDiff[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : MDiff[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    MDiff[s] (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x hx ↦ (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/-- Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable. -/
lemma MDifferentiable.clm_bundle_apply₂
    (hψ : MDiff (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : MDiff (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : MDiff (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    MDiff (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x ↦ (hψ x).clm_bundle_apply₂ (hv x) (hw x)

end TwoVariables'

end

section real_bundles
variable {B F₁ F₂ M : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module ℝ (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners ℝ EB HB) [TopologicalSpace B] [ChartedSpace HB B]
   [SigmaCompactSpace B] [T2Space B]
  {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂] {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

-- Note there is a closely related  exists_contMDiff_support_eq_eq_one_iff but it assumes a smooth
-- manifold and talks about support, not tsupport.
lemma exists_bumpFunction [IsManifold IB n B] {U V : Set B} (hU : IsClosed U) (hV : IsOpen V)
    (hUV : U ⊆ V) :
    ∃ f : B → ℝ, CMDiff n f ∧ range f ⊆ Icc 0 1 ∧ tsupport f ⊆ V ∧ (∀ x ∈ U, f x = 1) := by
  sorry

include IB in
lemma weakLocallyCompact_of_manifold [FiniteDimensional ℝ EB] : WeaklyLocallyCompactSpace B := by
  sorry

-- Warning: the next lemma is false for general fields
lemma exists_contMDiff_extension
    [FiniteDimensional ℝ EB] [IsManifold IB n B]
    {σ : Π x : B, E₁ x} {b₀ : B} {k : ℕ∞} (hσ : ∀ᶠ b in 𝓝 b₀, CMDiffAt k (T% σ) b) (hk : k ≤ n) :
    ∃ (σ' : Π x : B, E₁ x), CMDiff k (T% σ') ∧ ∀ᶠ b in 𝓝 b₀, σ' b = σ b := by
  have : WeaklyLocallyCompactSpace B := weakLocallyCompact_of_manifold IB
  rcases (nhds_basis_opens b₀).mem_iff.1 hσ with ⟨V, ⟨b₀V, V_open⟩, hσV⟩
  rcases (closed_nhds_basis b₀).mem_iff.1 (V_open.mem_nhds b₀V) with ⟨U, ⟨U_mem, U_closed⟩, UV⟩
  obtain ⟨f, f_diff, range_f, support_f, f_one⟩ := exists_bumpFunction IB
    U_closed V_open UV (n := n)
  use fun b ↦ f b • σ b, ?_, ?_
  · intro x
    by_cases hx : x ∈ V
    · exact ((f_diff x).of_le hk).smul_section (hσV hx)
    · have : ∀ᶠ x' in 𝓝 x, TotalSpace.mk' F₁ x' (f x' • σ x') = ⟨x', 0⟩ := by
        replace hx : x ∉ tsupport f := by tauto
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with x' hx'
        simp [hx']
      exact (contMDiffAt_zeroSection ℝ E₁).congr_of_eventuallyEq this
  filter_upwards [U_mem] with x hx
  simp [f_one x hx]

end real_bundles
