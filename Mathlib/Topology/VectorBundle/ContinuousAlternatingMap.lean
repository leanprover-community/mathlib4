/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# The vector bundle of continuous alternating multilinear maps

We define the topological vector bundle of continuous alternating maps
between two vector bundles over the same base.

Consider topological vector bundles with fibers `E₁ x`, `E₂ x`, `x : B`,
with model fibers `F₁` and `F₂`, and a finite index type `ι`.
If `F₁` and `F₂` are normed spaces over a nontrivially normed field `𝕜`,
then we define a vector bundle with fiber `E₁ x [⋀^ι]→L[𝕜] E₂ x`
with model fiber `F₁ [⋀^ι]→L[𝕜] F₂`.

The topology on the total space is constructed from the trivializations for `E₁` and `E₂` and the
norm-topology on the model fiber `F₁ [⋀^ι]→L[𝕜] F₂` using the `VectorPrebundle` construction.
-/

@[expose] public section


noncomputable section

open Bundle Set Topology
open scoped Bundle

/-!
### Continuous alternating map between fibers written in coordinates
-/

namespace ContinuousAlternatingMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]

variable {B₁ : Type*} (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace B₁] [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {B₂ : Type*} (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace B₂] [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- When `ϕ` is a continuous alternating map
between the fibers `E₁ x` and `E₂ y` of two vector bundles `E` and `E'`,
`ContinuousAlternatingMap.inCoordinates F E F' E' x₀ x y₀ y ϕ`
is a coordinate change of this continuous linear map
w.r.t. the chart around `x₀` and the chart around `y₀`.

It is defined by composing `ϕ` with appropriate coordinate changes
given by the vector bundles `E₁` and `E₂`.
We use the operations `Bundle.Trivialization.continuousLinearMapAt` and
`Bundle.Trivialization.symmL` in the definition, instead of
`Bundle.Trivialization.continuousLinearEquivAt`, so that
`ContinuousAlternatingMap.inCoordinates` is defined everywhere.
See also `ContinuousAlternatingMap.inCoordinates_eq`.

This is the (second component of the) underlying function
of a trivialization of the bundle of continuous alternating maps,
see `FiberBundle.trivializationAt_continuousAlternatingMap_apply`.

However, note that `ContinuousAlternatingMap.inCoordinates` is
defined even when `x` and `y` live in different base sets.
Therefore, it is also convenient when working with the bundle of continuous alternating maps
between pulled back bundles.
-/
def inCoordinates (x₀ x : B₁) (y₀ y : B₂) (ϕ : E₁ x [⋀^ι]→L[𝕜] E₂ y) :
    F₁ [⋀^ι]→L[𝕜] F₂ :=
  trivializationAt F₂ E₂ y₀ |>.continuousLinearMapAt 𝕜 y |>.compContinuousAlternatingMap
    ϕ |>.compContinuousLinearMap <| (trivializationAt F₁ E₁ x₀).symmL 𝕜 x

/-- Rewrite `ContinuousAlternatingMap.inCoordinates` using continuous linear equivalences. -/
theorem inCoordinates_eq {x₀ x : B₁} {y₀ y : B₂} {ϕ : E₁ x [⋀^ι]→L[𝕜] E₂ y}
    (hx : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (hy : y ∈ (trivializationAt F₂ E₂ y₀).baseSet) :
    inCoordinates F₁ F₂ x₀ x y₀ y ϕ =
      (((trivializationAt F₂ E₂ y₀).continuousLinearEquivAt 𝕜 y hy : E₂ y →L[𝕜] F₂)
        |>.compContinuousAlternatingMap ϕ |>.compContinuousLinearMap
          (((trivializationAt F₁ E₁ x₀).continuousLinearEquivAt 𝕜 x hx).symm : F₁ →L[𝕜] E₁ x)) := by
  ext
  simp [inCoordinates, *]

end ContinuousAlternatingMap

open ContinuousAlternatingMap (inCoordinates)

/-!
### Pretrivialization of the bundle of continuous alternating maps
-/

namespace Bundle.Pretrivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

variable (𝕜 ι) in
/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `Pretrivialization.continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂'`
is the coordinate change function between the two induced (pre)trivializations
`Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂`
and `Pretrivialization.continuousAlternatingMap 𝕜 ι e₁' e₂'`
of the bundle of continuous alternating maps. -/
def continuousAlternatingMapCoordChange (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] (b : B) :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
  (e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b) (ι := ι)

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
variable {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

theorem continuousOn_continuousAlternatingMapCoordChange
    [Finite ι]
    [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂]
    [MemTrivializationAtlas e₂'] :
    ContinuousOn (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  cases nonempty_fintype ι
  simp +unfoldPartialApp only [continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr, ContinuousLinearEquiv.symm_symm]
  refine .clm_comp ?_ ?_
  · refine map_continuous (ContinuousLinearMap.compContinuousAlternatingMapCLM (ι := ι) 𝕜 F₁ F₂ F₂)
      |>.comp_continuousOn ((continuousOn_coordChange 𝕜 e₂ e₂').mono ?_)
    mfld_set_tac
  · refine ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn ?_
    exact continuousOn_coordChange 𝕜 e₁' e₁ |>.mono (by mfld_set_tac)

variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

variable (𝕜 ι e₁ e₁' e₂ e₂') in
/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂` is the induced pretrivialization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
def continuousAlternatingMap :
    Pretrivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) where
  toFun p := ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
    p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩
  invFun p := ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap <|
    p.2.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 p.1⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := by
    rintro ⟨x, L⟩ ⟨h₁, h₂⟩
    simp only [TotalSpace.mk_inj]
    ext v
    simp [Function.comp_def, h₁, h₂]
  right_inv' := by
    rintro ⟨x, f⟩ ⟨⟨h₁, h₂⟩, -⟩
    simp only [Prod.mk_right_inj]
    ext v
    simp [Function.comp_def, h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance continuousAlternatingMap.isLinear
    [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] :
    (Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂).IsLinear 𝕜 where
  linear x _ :=
    { map_add L L' := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun']
      map_smul c L := by ext; simp [continuousAlternatingMap, Pretrivialization.toFun'] }

theorem continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) :
    continuousAlternatingMap 𝕜 ι e₁ e₂ p =
      ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1).compContinuousAlternatingMap <|
        p.2.compContinuousLinearMap <| e₁.symmL 𝕜 p.1⟩ :=
  rfl

theorem continuousAlternatingMap_symm_apply (p : B × (F₁ [⋀^ι]→L[𝕜] F₂)) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, (e₂.symmL 𝕜 p.1).compContinuousAlternatingMap <|
        p.2.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 p.1⟩ :=
  rfl

theorem continuousAlternatingMap_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (L : F₁ [⋀^ι]→L[𝕜] F₂) :
    (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L =
      ((e₂.symmL 𝕜 b).compContinuousAlternatingMap <|
        L.compContinuousLinearMap <| e₁.continuousLinearMapAt 𝕜 b) := by
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hb

theorem continuousAlternatingMapCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (L : F₁ [⋀^ι]→L[𝕜] F₂) :
    continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂' b L =
      (continuousAlternatingMap 𝕜 ι e₁' e₂'
        ⟨b, (continuousAlternatingMap 𝕜 ι e₁ e₂).symm b L⟩).2 := by
  ext v
  simp only [mem_inter_iff] at hb
  simp [continuousAlternatingMapCoordChange, continuousAlternatingMap_apply,
    Function.comp_def, Trivialization.coordChangeL_apply,
    continuousAlternatingMap_symm_apply' hb.left, hb]

end Bundle.Pretrivialization

/-!
### Vector (pre)bundle structure
-/

namespace Bundle.ContinuousAlternatingMap

open Pretrivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable (𝕜 ι F₁ E₁ F₂ E₂) in
/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`VectorPrebundle` (this is an auxiliary construction for the
`VectorBundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def vectorPrebundle :
    VectorPrebundle 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) where
  pretrivializationAtlas :=
    {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousAlternatingMap 𝕜 ι e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x := Pretrivialization.continuousAlternatingMap 𝕜 ι
    (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      continuousOn_continuousAlternatingMapCoordChange,
      continuousAlternatingMapCoordChange_apply⟩
  totalSpaceMk_isInducing b := by
    simp only [Function.comp_def, continuousAlternatingMap_apply, isInducing_const_prod]
    let L₁ : E₁ b ≃L[𝕜] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜 b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜 b
        (mem_baseSet_trivializationAt _ _ _)
    convert (L₁.continuousAlternatingMapCongr L₂).toHomeomorph.isInducing
    ext f
    simp [Trivialization.linearMapAt_def_of_mem _ (mem_baseSet_trivializationAt _ _ _), L₁, L₂]

/-- Topology on the total space of the continuous `σ`-semilinear maps between two "normable" vector
bundles over the same base. -/
instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).totalSpaceTopology

/-- The continuous `σ`-semilinear maps between two vector bundles form a fiber bundle. -/
instance instFiberBundle :
    FiberBundle (F₁ [⋀^ι]→L[𝕜] F₂) fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toFiberBundle

/-- The continuous `σ`-semilinear maps between two vector bundles form a vector bundle. -/
instance instVectorBundle : VectorBundle 𝕜 (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) :=
  (vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).toVectorBundle

end Bundle.ContinuousAlternatingMap

/-!
### Trivialization of the bundle of continuous alternating maps
-/

namespace Bundle.Trivialization

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable {e₁ : Trivialization F₁ (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)}
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

variable (𝕜 ι e₁ e₂) in
/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`. -/
def continuousAlternatingMap :
    Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance memTrivializationAtlas_continuousAlternatingMap :
    MemTrivializationAtlas
      (e₁.continuousAlternatingMap 𝕜 ι e₂ :
        Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x))) :=
  ⟨⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩⟩

@[simp]
theorem baseSet_continuousAlternatingMap :
    (e₁.continuousAlternatingMap 𝕜 ι e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

theorem continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    e₁.continuousAlternatingMap 𝕜 ι e₂ p =
      ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1 : _ →L[𝕜] _) |>.compContinuousAlternatingMap p.2
        |>.compContinuousLinearMap (e₁.symmL 𝕜 p.1 : F₁ →L[𝕜] E₁ p.1)⟩ :=
  rfl

end Bundle.Trivialization

/-!
### Lemmas about `trivializationAt` for the bundle of continuous alternating maps
-/

namespace FiberBundle

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

theorem trivializationAt_continuousAlternatingMap (x₀ : B) :
    trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀ =
    (trivializationAt F₁ E₁ x₀).continuousAlternatingMap 𝕜 ι (trivializationAt F₂ E₂ x₀) := rfl

theorem trivializationAt_continuousAlternatingMap_apply (x₀ : B)
    (x : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀ x =
      ⟨x.1, inCoordinates F₁ F₂ x₀ x.1 x₀ x.1 x.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_continuousAlternatingMap_source (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).source =
      π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
theorem trivializationAt_continuousAlternatingMap_target (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
theorem trivializationAt_continuousAlternatingMap_baseSet (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

end FiberBundle

/-!
### Continuity of maps to the total space of the bundle of continuous alternating maps
-/

section Continuity

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

variable {B : Type*} [TopologicalSpace B]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

variable {X : Type*} [TopologicalSpace X] {s : Set X} {x₀ : X}


theorem continuousWithinAt_continuousAlternatingMap_bundle
    (f : X → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x ↦ (f x).1) s x₀ ∧
        ContinuousWithinAt
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ :=
  FiberBundle.continuousWithinAt_totalSpace ..

theorem continuousAt_continuousAlternatingMap_bundle
    (f : X → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x ↦ (f x).1) x₀ ∧
        ContinuousAt
          (fun x ↦ inCoordinates F₁ F₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  FiberBundle.continuousAt_totalSpace ..

end Continuity

end
