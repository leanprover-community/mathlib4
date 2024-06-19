/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
import Mathlib.Topology.VectorBundle.Basic

#align_import topology.vector_bundle.hom from "leanprover-community/mathlib"@"8905e5ed90859939681a725b00f6063e65096d95"

/-!
# The vector bundle of continuous (semi)linear maps

We define the (topological) vector bundle of continuous (semi)linear maps between two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*`, normed spaces `F₁` and `F₂`, and a ring-homomorphism `σ` between
their respective scalar fields, we define `Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x` to be a
type synonym for `fun x ↦ E₁ x →SL[σ] E₂ x`. If the `E₁` and `E₂` are vector bundles with model
fibers `F₁` and `F₂`, then this will be a vector bundle with fiber `F₁ →SL[σ] F₂`.

The topology on the total space is constructed from the trivializations for `E₁` and `E₂` and the
norm-topology on the model fiber `F₁ →SL[𝕜] F₂` using the `VectorPrebundle` construction.  This is
a bit awkward because it introduces a dependence on the normed space structure of the model fibers,
rather than just their topological vector space structure; it is not clear whether this is
necessary.

Similar constructions should be possible (but are yet to be formalized) for tensor products of
topological vector bundles, exterior algebras, and so on, where again the topology can be defined
using a norm on the fiber model if this helps.

## Main Definitions

* `Bundle.ContinuousLinearMap.vectorBundle`: continuous semilinear maps between
  vector bundles form a vector bundle.

-/


noncomputable section

open scoped Bundle

open Bundle Set ContinuousLinearMap

variable {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁] {𝕜₂ : Type*} [NontriviallyNormedField 𝕜₂]
  (σ : 𝕜₁ →+* 𝕜₂) [iσ : RingHomIsometric σ]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁] (E₁ : B → Type*)
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂] (E₂ : B → Type*)
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

/-- A reducible type synonym for the bundle of continuous (semi)linear maps. For some reason, it
helps with instance search.

Porting note: after the port is done, we may want to remove this definition.
-/
protected abbrev Bundle.ContinuousLinearMap [∀ x, TopologicalSpace (E₁ x)]
    [∀ x, TopologicalSpace (E₂ x)] : B → Type _ := fun x => E₁ x →SL[σ] E₂ x
#align bundle.continuous_linear_map Bundle.ContinuousLinearMap

-- Porting note: possibly remove after the port
instance Bundle.ContinuousLinearMap.module [∀ x, TopologicalSpace (E₁ x)]
    [∀ x, TopologicalSpace (E₂ x)] [∀ x, TopologicalAddGroup (E₂ x)]
    [∀ x, ContinuousConstSMul 𝕜₂ (E₂ x)] : ∀ x, Module 𝕜₂ (Bundle.ContinuousLinearMap σ E₁ E₂ x) :=
  fun _ => inferInstance
#align bundle.continuous_linear_map.module Bundle.ContinuousLinearMap.module

variable {E₁ E₂}
variable [TopologicalSpace B] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

namespace Pretrivialization

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `Pretrivialization.continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂'` is the
coordinate change function between the two induced (pre)trivializations
`Pretrivialization.continuousLinearMap σ e₁ e₂` and
`Pretrivialization.continuousLinearMap σ e₁' e₂'` of `Bundle.ContinuousLinearMap`. -/
def continuousLinearMapCoordChange [e₁.IsLinear 𝕜₁] [e₁'.IsLinear 𝕜₁] [e₂.IsLinear 𝕜₂]
    [e₂'.IsLinear 𝕜₂] (b : B) : (F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂ :=
  ((e₁'.coordChangeL 𝕜₁ e₁ b).symm.arrowCongrSL (e₂.coordChangeL 𝕜₂ e₂' b) :
    (F₁ →SL[σ] F₂) ≃L[𝕜₂] F₁ →SL[σ] F₂)
#align pretrivialization.continuous_linear_map_coord_change Pretrivialization.continuousLinearMapCoordChange

variable {σ e₁ e₁' e₂ e₂'}
variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [ita : ∀ x, TopologicalAddGroup (E₂ x)] [FiberBundle F₂ E₂]

theorem continuousOn_continuousLinearMapCoordChange [VectorBundle 𝕜₁ F₁ E₁] [VectorBundle 𝕜₂ F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂]
    [MemTrivializationAtlas e₂'] :
    ContinuousOn (continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := (compSL F₁ F₂ F₂ σ (RingHom.id 𝕜₂)).continuous
  have h₂ := (ContinuousLinearMap.flip (compSL F₁ F₁ F₂ (RingHom.id 𝕜₁) σ)).continuous
  have h₃ := continuousOn_coordChange 𝕜₁ e₁' e₁
  have h₄ := continuousOn_coordChange 𝕜₂ e₂ e₂'
  refine ((h₁.comp_continuousOn (h₄.mono ?_)).clm_comp (h₂.comp_continuousOn (h₃.mono ?_))).congr ?_
  · mfld_set_tac
  · mfld_set_tac
  · intro b _; ext L v
    -- Porting note: was
    -- simp only [continuousLinearMapCoordChange, ContinuousLinearEquiv.coe_coe,
    --   ContinuousLinearEquiv.arrowCongrₛₗ_apply, LinearEquiv.toFun_eq_coe, coe_comp',
    --   ContinuousLinearEquiv.arrowCongrSL_apply, comp_apply, Function.comp, compSL_apply,
    --   flip_apply, ContinuousLinearEquiv.symm_symm]
    -- Now `simp` fails to use `ContinuousLinearMap.comp_apply` in this case
    dsimp [continuousLinearMapCoordChange]
    rw [ContinuousLinearEquiv.symm_symm]
#align pretrivialization.continuous_on_continuous_linear_map_coord_change Pretrivialization.continuousOn_continuousLinearMapCoordChange

variable (σ e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜₁] [e₁'.IsLinear 𝕜₁] [e₂.IsLinear 𝕜₂] [e₂'.IsLinear 𝕜₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousLinearMap σ e₁ e₂` is the induced pretrivialization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
def continuousLinearMap :
    Pretrivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂)) where
  toFun p := ⟨p.1, .comp (e₂.continuousLinearMapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩
  invFun p := ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1))⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨x, L⟩ h => ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨x, f⟩ h => h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ => by
    simp only [TotalSpace.mk_inj]
    ext (v : E₁ x)
    dsimp only [comp_apply]
    rw [Trivialization.symmL_continuousLinearMapAt, Trivialization.symmL_continuousLinearMapAt]
    exacts [h₁, h₂]
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ => by
    simp only [Prod.mk_inj_left]
    ext v
    dsimp only [comp_apply]
    rw [Trivialization.continuousLinearMapAt_symmL, Trivialization.continuousLinearMapAt_symmL]
    exacts [h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl
#align pretrivialization.continuous_linear_map Pretrivialization.continuousLinearMap

-- Porting note (#11215): TODO: see if Lean 4 can generate this instance without a hint
instance continuousLinearMap.isLinear [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)] :
    (Pretrivialization.continuousLinearMap σ e₁ e₂).IsLinear 𝕜₂ where
  linear x _ :=
    { map_add := fun L L' =>
        show (e₂.continuousLinearMapAt 𝕜₂ x).comp ((L + L').comp (e₁.symmL 𝕜₁ x)) = _ by
          simp_rw [add_comp, comp_add]
          rfl
      map_smul := fun c L =>
        show (e₂.continuousLinearMapAt 𝕜₂ x).comp ((c • L).comp (e₁.symmL 𝕜₁ x)) = _ by
          simp_rw [smul_comp, comp_smulₛₗ, RingHom.id_apply]
          rfl }
#align pretrivialization.continuous_linear_map.is_linear Pretrivialization.continuousLinearMap.isLinear

theorem continuousLinearMap_apply (p : TotalSpace (F₁ →SL[σ] F₂) fun x => E₁ x →SL[σ] E₂ x) :
    (continuousLinearMap σ e₁ e₂) p =
      ⟨p.1, .comp (e₂.continuousLinearMapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩ :=
  rfl
#align pretrivialization.continuous_linear_map_apply Pretrivialization.continuousLinearMap_apply

theorem continuousLinearMap_symm_apply (p : B × (F₁ →SL[σ] F₂)) :
    (continuousLinearMap σ e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1))⟩ :=
  rfl
#align pretrivialization.continuous_linear_map_symm_apply Pretrivialization.continuousLinearMap_symm_apply

theorem continuousLinearMap_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (L : F₁ →SL[σ] F₂) :
    (continuousLinearMap σ e₁ e₂).symm b L =
      (e₂.symmL 𝕜₂ b).comp (L.comp <| e₁.continuousLinearMapAt 𝕜₁ b) := by
  rw [symm_apply]
  · rfl
  · exact hb
#align pretrivialization.continuous_linear_map_symm_apply' Pretrivialization.continuousLinearMap_symm_apply'

theorem continuousLinearMapCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (L : F₁ →SL[σ] F₂) :
    continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂' b L =
      (continuousLinearMap σ e₁' e₂' ⟨b, (continuousLinearMap σ e₁ e₂).symm b L⟩).2 := by
  ext v
  simp_rw [continuousLinearMapCoordChange, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongrSL_apply, continuousLinearMap_apply,
    continuousLinearMap_symm_apply' σ e₁ e₂ hb.1, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_symm, Trivialization.continuousLinearMapAt_apply,
    Trivialization.symmL_apply]
  rw [e₂.coordChangeL_apply e₂', e₁'.coordChangeL_apply e₁, e₁.coe_linearMapAt_of_mem hb.1.1,
    e₂'.coe_linearMapAt_of_mem hb.2.2]
  exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]
#align pretrivialization.continuous_linear_map_coord_change_apply Pretrivialization.continuousLinearMapCoordChange_apply

end Pretrivialization

open Pretrivialization

variable (F₁ E₁ F₂ E₂)
variable [∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜₁ F₁ E₁]
variable [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜₂ F₂ E₂]
variable [∀ x, TopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)]

/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`VectorPrebundle` (this is an auxiliary construction for the
`VectorBundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def Bundle.ContinuousLinearMap.vectorPrebundle :
    VectorPrebundle 𝕜₂ (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂) where
  pretrivializationAtlas :=
    {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousLinearMap σ e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x :=
    Pretrivialization.continuousLinearMap σ (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂',
      continuousOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply σ e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_inducing := by
    intro b
    let L₁ : E₁ b ≃L[𝕜₁] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜₁ b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜₂] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜₂ b
        (mem_baseSet_trivializationAt _ _ _)
    let φ : (E₁ b →SL[σ] E₂ b) ≃L[𝕜₂] F₁ →SL[σ] F₂ := L₁.arrowCongrSL L₂
    have : Inducing fun x => (b, φ x) := inducing_const_prod.mpr φ.toHomeomorph.inducing
    convert this
    ext f
    dsimp [Pretrivialization.continuousLinearMap_apply]
    rw [Trivialization.linearMapAt_def_of_mem _ (mem_baseSet_trivializationAt _ _ _)]
    rfl
#align bundle.continuous_linear_map.vector_prebundle Bundle.ContinuousLinearMap.vectorPrebundle

/-- Topology on the total space of the continuous `σ`-semilinear maps between two "normable" vector
bundles over the same base. -/
instance Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂)) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).totalSpaceTopology
#align bundle.continuous_linear_map.topological_space_total_space Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace

/-- The continuous `σ`-semilinear maps between two vector bundles form a fiber bundle. -/
instance Bundle.ContinuousLinearMap.fiberBundle :
    FiberBundle (F₁ →SL[σ] F₂) fun x => E₁ x →SL[σ] E₂ x :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toFiberBundle
#align bundle.continuous_linear_map.fiber_bundle Bundle.ContinuousLinearMap.fiberBundle

/-- The continuous `σ`-semilinear maps between two vector bundles form a vector bundle. -/
instance Bundle.ContinuousLinearMap.vectorBundle :
    VectorBundle 𝕜₂ (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toVectorBundle
#align bundle.continuous_linear_map.vector_bundle Bundle.ContinuousLinearMap.vectorBundle

variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂] {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`. -/
def Trivialization.continuousLinearMap :
    Trivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩
#align trivialization.continuous_linear_map Trivialization.continuousLinearMap

instance Bundle.ContinuousLinearMap.memTrivializationAtlas :
    MemTrivializationAtlas
      (e₁.continuousLinearMap σ e₂ :
        Trivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂))) where
  out := ⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩
#align bundle.continuous_linear_map.mem_trivialization_atlas Bundle.ContinuousLinearMap.memTrivializationAtlas

variable {e₁ e₂}

@[simp]
theorem Trivialization.baseSet_continuousLinearMap :
    (e₁.continuousLinearMap σ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl
#align trivialization.base_set_continuous_linear_map Trivialization.baseSet_continuousLinearMap

theorem Trivialization.continuousLinearMap_apply
    (p : TotalSpace (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂)) :
    e₁.continuousLinearMap σ e₂ p =
      ⟨p.1, (e₂.continuousLinearMapAt 𝕜₂ p.1 : _ →L[𝕜₂] _).comp
        (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ →L[𝕜₁] E₁ p.1) : F₁ →SL[σ] E₂ p.1)⟩ :=
  rfl
#align trivialization.continuous_linear_map_apply Trivialization.continuousLinearMap_apply

theorem hom_trivializationAt_apply (x₀ : B)
    (x : TotalSpace (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂)) :
    trivializationAt (F₁ →SL[σ] F₂) (fun x => E₁ x →SL[σ] E₂ x) x₀ x =
      ⟨x.1, inCoordinates F₁ E₁ F₂ E₂ x₀ x.1 x₀ x.1 x.2⟩ :=
  rfl
#align hom_trivialization_at_apply hom_trivializationAt_apply

@[simp, mfld_simps]
theorem hom_trivializationAt_source (x₀ : B) :
    (trivializationAt (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂) x₀).source =
      π (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ E₁ E₂) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl
#align hom_trivialization_at_source hom_trivializationAt_source

@[simp, mfld_simps]
theorem hom_trivializationAt_target (x₀ : B) :
    (trivializationAt (F₁ →SL[σ] F₂) (fun x => E₁ x →SL[σ] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl
#align hom_trivialization_at_target hom_trivializationAt_target
