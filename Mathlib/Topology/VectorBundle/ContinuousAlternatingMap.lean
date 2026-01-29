module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# The vector bundle of continuous alternating multilinear maps
-/

@[expose] public section


noncomputable section

open Bundle Set Topology
open scoped Bundle

variable (𝕜 ι : Type*) [NontriviallyNormedField 𝕜]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type*)
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type*)
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

namespace Pretrivialization

/-- TODO rewrite
Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `Pretrivialization.continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂'` is the
coordinate change function between the two induced (pre)trivializations
`Pretrivialization.continuousLinearMap σ e₁ e₂` and
`Pretrivialization.continuousLinearMap σ e₁' e₂'` of the bundle of continuous linear maps. -/
def continuousAlternatingMapCoordChange [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜]
    [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] (b : B) :
    (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
  (e₁'.coordChangeL 𝕜 e₁ b).symm.continuousAlternatingMapCongr (e₂.coordChangeL 𝕜 e₂' b) (ι := ι)

variable {𝕜 ι e₁ e₁' e₂ e₂'}
variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

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

variable (𝕜 ι e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

/-- TODO rewrite
Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousLinearMap σ e₁ e₂` is the induced pretrivialization for the
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
  rw [symm_apply]
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
    continuousAlternatingMap_symm_apply' _ _ e₁ e₂ hb.left,
    Trivialization.linearMapAt_apply, hb]

end Pretrivialization

open Pretrivialization

variable [Fintype ι]
variable [∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

namespace Bundle.ContinuousAlternatingMap

variable (F₁ E₁ F₂ E₂) in
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
      continuousAlternatingMapCoordChange_apply 𝕜 ι e₁ e₁' e₂ e₂'⟩
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

variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`. -/
def Trivialization.continuousAlternatingMap :
    Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩

instance Bundle.ContinuousLinearMap.memTrivializationAtlas :
    MemTrivializationAtlas
      (e₁.continuousAlternatingMap 𝕜 ι e₂ :
        Trivialization (F₁ [⋀^ι]→L[𝕜] F₂) (π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x))) :=
  ⟨⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩⟩

variable {e₁ e₂}

@[simp]
theorem Trivialization.baseSet_continuousAlternatingMap :
    (e₁.continuousAlternatingMap 𝕜 ι e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

theorem Trivialization.continuousAlternatingMap_apply
    (p : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    e₁.continuousAlternatingMap 𝕜 ι e₂ p =
      ⟨p.1, (e₂.continuousLinearMapAt 𝕜 p.1 : _ →L[𝕜] _) |>.compContinuousAlternatingMap p.2
        |>.compContinuousLinearMap (e₁.symmL 𝕜 p.1 : F₁ →L[𝕜] E₁ p.1)⟩ :=
  rfl

theorem continuousAlternatingMap_trivializationAt (x₀ : B) :
    trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀ =
    (trivializationAt F₁ E₁ x₀).continuousAlternatingMap 𝕜 ι (trivializationAt F₂ E₂ x₀) := rfl

/-
{E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
[TopologicalSpace (TotalSpace F₁ E₁)] {F₂ : Type*}
[NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)]
[∀ x, Module 𝕜 (E₂ x)]
[TopologicalSpace (TotalSpace F₂ E₂)] [TopologicalSpace B] {e₁ : Trivialization F₁ (π F₁ E₁)}
(e₁' : Trivialization F₁ (π F₁ E₁)) {e₂ : Trivialization F₂ (π F₂ E₂)}
(e₂' : Trivialization F₂ (π F₂ E₂)) [Fintype ι]
[∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
[∀ x : B, TopologicalSpace (E₂ x)]
[FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] [∀ x, IsTopologicalAddGroup (E₂ x)]
[∀ x, ContinuousSMul 𝕜 (E₂ x)]
[he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]
-/

variable {𝕜 ι} (F₁ E₁ F₂ E₂) in
def ContinuousAlternatingMap.inCoordinates := _

/-
info: ContinuousLinearMap.inCoordinates.{u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} {B : Type u_2} (F : Type u_3)
  (E : B → Type u_4) [(x : B) → AddCommMonoid (E x)] [NormedAddCommGroup F] [TopologicalSpace B]
  [(x : B) → TopologicalSpace (E x)] {𝕜₁ : Type u_5} {𝕜₂ : Type u_6} [NontriviallyNormedField 𝕜₁]
  [NontriviallyNormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {B' : Type u_7} [TopologicalSpace B'] [NormedSpace 𝕜₁ F]
  [(x : B) → Module 𝕜₁ (E x)] [TopologicalSpace (TotalSpace F E)] (F' : Type u_8) [NormedAddCommGroup F']
  [NormedSpace 𝕜₂ F'] (E' : B' → Type u_9) [(x : B') → AddCommMonoid (E' x)] [(x : B') → Module 𝕜₂ (E' x)]
  [TopologicalSpace (TotalSpace F' E')] [FiberBundle F E] [VectorBundle 𝕜₁ F E] [(x : B') → TopologicalSpace (E' x)]
  [FiberBundle F' E'] [VectorBundle 𝕜₂ F' E'] (x₀ x : B) (y₀ y : B') (ϕ : E x →SL[σ] E' y) : F →SL[σ] F'
-/



theorem continuousAlternatingMap_trivializationAt_apply (x₀ : B)
    (x : TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) :
    trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀ x =
      ⟨x.1, inCoordinates F₁ E₁ F₂ E₂ x₀ x.1 x₀ x.1 x.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem continuousAlternatingMap_trivializationAt_source (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).source =
      π (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
theorem continuousAlternatingMap_trivializationAt_target (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
theorem continuousAlternatingMap_trivializationAt_baseSet (x₀ : B) :
    (trivializationAt (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

theorem continuousWithinAt_continuousAlternatingMap_bundle {M : Type*} [TopologicalSpace M]
    (f : M → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) {s : Set M} {x₀ : M} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x ↦ (f x).1) s x₀ ∧
        ContinuousWithinAt
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ :=
  FiberBundle.continuousWithinAt_totalSpace ..

theorem continuousAt_continuousAlternatingMap_bundle {M : Type*} [TopologicalSpace M]
    (f : M → TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x)) {x₀ : M} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x ↦ (f x).1) x₀ ∧
        ContinuousAt
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  FiberBundle.continuousAt_totalSpace ..

section

/- Declare two bases spaces `B₁` and `B₂` and two vector bundles `E₁` and `E₂` respectively
over `B₁` and `B₂` (with model fibers `F₁` and `F₂`).

Also a third space `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace M]
  {n : WithTop ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M → B₁} {b₂ : M → B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/-- Consider a continuous map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
continuously on `m`, one can apply `ϕ m` to `g m`, and the resulting map is continuous.

Note that the continuity of `ϕ` cannot be always be stated as continuity of a map into a bundle,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only have a nice topology when `b₁` and `b₂` are
globally continuous, but we want to apply this lemma with only local information. Therefore, we
formulate it using continuity of `ϕ` read in coordinates.

Version for `ContinuousWithinAt`. We also give a version for `ContinuousAt`, but no version for
`ContinuousOn` or `Continuous` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which continuity can be expressed without
`inCoordinates`, see `ContinuousWithinAt.clm_bundle_apply`
-/
lemma ContinuousWithinAt.clm_apply_of_inCoordinates
    (hϕ : ContinuousWithinAt
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) s m₀)
    (hv : ContinuousWithinAt (fun m ↦ (v m : TotalSpace F₁ E₁)) s m₀)
    (hb₂ : ContinuousWithinAt b₂ s m₀) :
    ContinuousWithinAt (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) s m₀ := by
  rw [← continuousWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContinuousWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  simp [inCoordinates_eq hm h'm,
        Trivialization.symm_apply_apply_mk (trivializationAt F₁ E₁ (b₁ m₀)) hm (v m)]


/-- Consider a continuous map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
continuously on `m`, one can apply `ϕ m` to `g m`, and the resulting map is continuous.

Note that the continuity of `ϕ` cannot be always be stated as continuity of a map into a bundle,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only have a nice topology when `b₁` and `b₂` are
globally continuous, but we want to apply this lemma with only local information. Therefore, we
formulate it using continuity of `ϕ` read in coordinates.

Version for `ContinuousAt`. We also give a version for `ContinuousWithinAt`, but no version for
`ContinuousOn` or `Continuous` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which continuity can be expressed without
`inCoordinates`, see `ContinuousWithinAt.clm_bundle_apply`
-/
lemma ContinuousAt.clm_apply_of_inCoordinates
    (hϕ : ContinuousAt
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ContinuousAt (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : ContinuousAt b₂ m₀) :
    ContinuousAt (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← continuousWithinAt_univ] at hϕ hv hb₂ ⊢
  exact hϕ.clm_apply_of_inCoordinates hv hb₂

end

section

/- Declare a base space `B` and three vector bundles `E₁`, `E₂` and `E₃` over `B`
(with model fibers `F₁`, `F₂` and `F₃`).

Also a second space `M`, which will be the source of all our maps.
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
  [TopologicalSpace B] [TopologicalSpace M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  {b : M → B} {v : ∀ x, E₁ (b x)} {s : Set M} {x : M}

section OneVariable

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x))}

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
lemma ContinuousWithinAt.clm_bundle_apply
    (hϕ : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m))
      s x)
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x) :
    ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s x := by
  simp only [continuousWithinAt_continuousAlternatingMap_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
lemma ContinuousAt.clm_bundle_apply
    (hϕ : ContinuousAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    ContinuousAt (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [← continuousWithinAt_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
lemma ContinuousOn.clm_bundle_apply
    (hϕ : ContinuousOn
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) s)
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s) :
    ContinuousOn (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply (hv x hx)

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
lemma Continuous.clm_bundle_apply
    (hϕ : Continuous
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : Continuous (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    Continuous (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) := by
  simp only [← continuousOn_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv

end OneVariable

section TwoVariables

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x) →L[𝕜] E₃ (b x))} {w : ∀ x, E₂ (b x)}

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a basemap
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
lemma ContinuousWithinAt.clm_bundle_apply₂
    (hψ : ContinuousWithinAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) s x)
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s x :=
  (hψ.clm_bundle_apply hv).clm_bundle_apply hw

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a basemap
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
lemma ContinuousAt.clm_bundle_apply₂
    (hψ : ContinuousAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContinuousAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContinuousAt (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  (hψ.clm_bundle_apply hv).clm_bundle_apply hw

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a basemap
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
lemma ContinuousOn.clm_bundle_apply₂
    (hψ : ContinuousOn
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) s)
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContinuousOn (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContinuousOn (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s :=
  fun x hx ↦ (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a basemap
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
lemma Continuous.clm_bundle_apply₂
    (hψ : Continuous (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : Continuous (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : Continuous (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    Continuous (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) := by
  simp only [← continuousOn_univ] at hψ hv hw ⊢
  exact hψ.clm_bundle_apply₂ hv hw

/-- Rewrite `ContinuousLinearMap.inCoordinates` using continuous linear equivalences, in the
bundle of bilinear maps. -/
theorem inCoordinates_apply_eq₂
    {x₀ x : B} {ϕ : E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x} {v : F₁} {w : F₂}
    (h₁x : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (h₂x : x ∈ (trivializationAt F₂ E₂ x₀).baseSet)
    (h₃x : x ∈ (trivializationAt F₃ E₃ x₀).baseSet) :
    inCoordinates F₁ E₁ (F₂ →L[𝕜] F₃) (fun x ↦ E₂ x →L[𝕜] E₃ x) x₀ x x₀ x ϕ v w =
    (trivializationAt F₃ E₃ x₀).linearMapAt 𝕜 x
      (ϕ ((trivializationAt F₁ E₁ x₀).symm x v) ((trivializationAt F₂ E₂ x₀).symm x w)) := by
  rw [inCoordinates_eq h₁x (by simp [h₂x, h₃x])]
  simp [continuousAlternatingMap_trivializationAt, Trivialization.continuousLinearMap_apply]

end TwoVariables

end
