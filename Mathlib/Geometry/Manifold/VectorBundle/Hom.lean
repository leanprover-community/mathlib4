/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Init
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Neighborhoods

/-! # Homs of `C^n` vector bundles over the same base space

Here we show that the bundle of continuous linear maps is a `C^n` vector bundle. We also show
that applying a smooth family of linear maps to a smooth family of vectors gives a smooth
result, in several versions.

Note that we only do this for bundles of linear maps, not for bundles of arbitrary semilinear maps.
Indeed, semilinear maps are typically not smooth. For instance, complex conjugation is not
`ℂ`-differentiable.
-/

@[expose] public section

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
    ContMDiffOn IB 𝓘(𝕜, (F₁ →L[𝕜] F₂) →L[𝕜] F₁ →L[𝕜] F₂) n
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
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
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n f s x₀ ↔
      CMDiffAt[s] n (fun x ↦ (f x).1) x₀ ∧
        CMDiffAt[s] n
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffWithinAt_totalSpace

theorem contMDiffAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n f x₀ ↔
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
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) f s x₀ ↔
      MDiffAt[s] (fun x ↦ (f x).1) x₀ ∧
        MDiffAt[s]
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableWithinAt_totalSpace IB ..

theorem mdifferentiableAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) f x₀ ↔
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
    (hv : ContMDiffWithinAt IM (IB₁.prod 𝓘(𝕜, F₁)) n (fun m ↦ (v m : TotalSpace F₁ E₁)) s m₀)
    (hb₂ : CMDiffAt[s] n b₂ m₀) :
    ContMDiffWithinAt IM (IB₂.prod 𝓘(𝕜, F₂)) n (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) s m₀ := by
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
    (hv : ContMDiffAt IM (IB₁.prod 𝓘(𝕜, F₁)) n (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : CMDiffAt n b₂ m₀) :
    ContMDiffAt IM (IB₂.prod 𝓘(𝕜, F₂)) n (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
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
    (hϕ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m))
      s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂)) n
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s x := by
  simp only [contMDiffWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement at a point. -/
lemma ContMDiffAt.clm_bundle_apply
    (hϕ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x :=
  ContMDiffWithinAt.clm_bundle_apply hϕ hv

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement on a set. -/
lemma ContMDiffOn.clm_bundle_apply
    (hϕ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply (hv x hx)

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
lemma ContMDiff.clm_bundle_apply
    (hϕ : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x ↦ (hϕ x).clm_bundle_apply (hv x)

end OneVariable

section OneVariable'

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x))}

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement within a set at a point. -/
lemma MDifferentiableWithinAt.clm_bundle_apply
    (hϕ : MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m))
      s x)
    (hv : MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁))
      (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₂))
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s x := by
  simp only [mdifferentiableWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement at a point. -/
lemma MDifferentiableAt.clm_bundle_apply
    (hϕ : MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₁)) (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₂)) (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x :=
  MDifferentiableWithinAt.clm_bundle_apply hϕ hv

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement on a set. -/
lemma MDifferentiableOn.clm_bundle_apply
    (hϕ : MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) s)
    (hv : MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₁)) (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s) :
    MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₂)) (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply (hv x hx)

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable. -/
lemma MDifferentiable.clm_bundle_apply
    (hϕ : MDifferentiable IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : MDifferentiable IM (IB.prod 𝓘(𝕜, F₁)) (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    MDifferentiable IM (IB.prod 𝓘(𝕜, F₂)) (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x ↦ (hϕ x).clm_bundle_apply (hv x)

end OneVariable'

section TwoVariables

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x) →L[𝕜] E₃ (b x))} {w : ∀ x, E₂ (b x)}

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement within a set at a point. -/
lemma ContMDiffWithinAt.clm_bundle_apply₂
    (hψ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₃)) n
      (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s x :=
  hψ.clm_bundle_apply hv |>.clm_bundle_apply hw

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement at a point. -/
lemma ContMDiffAt.clm_bundle_apply₂
    (hψ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₃)) n
      (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  ContMDiffWithinAt.clm_bundle_apply₂ hψ hv hw

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement on a set. -/
lemma ContMDiffOn.clm_bundle_apply₂
    (hψ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F₃)) n
      (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s :=
  fun x hx ↦ (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
lemma ContMDiff.clm_bundle_apply₂
    (hψ : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : ContMDiff IM (IB.prod 𝓘(𝕜, F₁)) n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : ContMDiff IM (IB.prod 𝓘(𝕜, F₂)) n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₃)) n
      (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x ↦ (hψ x).clm_bundle_apply₂ (hv x) (hw x)

end TwoVariables

section TwoVariables'

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x) →L[𝕜] E₃ (b x))} {w : ∀ x, E₂ (b x)}

/-- Consider differentiable maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement within a set at a point. -/
lemma MDifferentiableWithinAt.clm_bundle_apply₂
    (hψ : MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) s x)
    (hv : MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₁))
      (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₂))
      (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    MDifferentiableWithinAt IM (IB.prod 𝓘(𝕜, F₃))
      (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s x :=
  hψ.clm_bundle_apply hv |>.clm_bundle_apply hw

/-- Consider differentiable maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement at a point. -/
lemma MDifferentiableAt.clm_bundle_apply₂
    (hψ : MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₁)) (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₂)) (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    MDifferentiableAt IM (IB.prod 𝓘(𝕜, F₃))
      (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  MDifferentiableWithinAt.clm_bundle_apply₂ hψ hv hw

/-- Consider differentiable maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement on a set. -/
lemma MDifferentiableOn.clm_bundle_apply₂
    (hψ : MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) s)
    (hv : MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₁)) (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₂)) (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    MDifferentiableOn IM (IB.prod 𝓘(𝕜, F₃))
      (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s :=
  fun x hx ↦ (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/-- Consider differentiable maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable. -/
lemma MDifferentiable.clm_bundle_apply₂
    (hψ : MDifferentiable IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ →L[𝕜] F₃))
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : MDifferentiable IM (IB.prod 𝓘(𝕜, F₁)) (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : MDifferentiable IM (IB.prod 𝓘(𝕜, F₂)) (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    MDifferentiable IM (IB.prod 𝓘(𝕜, F₃))
      (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x ↦ (hψ x).clm_bundle_apply₂ (hv x) (hw x)

end TwoVariables'

end
