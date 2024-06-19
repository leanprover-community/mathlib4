/-
Copyright (c) 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
import Mathlib.Topology.FiberBundle.Basic

#align_import topology.fiber_bundle.constructions from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Standard constructions on fiber bundles

This file contains several standard constructions on fiber bundles:

* `Bundle.Trivial.fiberBundle 𝕜 B F`: the trivial fiber bundle with model fiber `F` over the base
  `B`

* `FiberBundle.prod`: for fiber bundles `E₁` and `E₂` over a common base, a fiber bundle structure
  on their fiberwise product `E₁ ×ᵇ E₂` (the notation stands for `fun x ↦ E₁ x × E₂ x`).

* `FiberBundle.pullback`: for a fiber bundle `E` over `B`, a fiber bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags

fiber bundle, fibre bundle, fiberwise product, pullback

-/


open TopologicalSpace Filter Set Bundle

open scoped Classical
open Topology Bundle

/-! ### The trivial bundle -/


namespace Bundle

namespace Trivial

variable (B : Type*) (F : Type*)

-- Porting note (#10754): Added name for this instance.
-- TODO: use `TotalSpace.toProd`
instance topologicalSpace [t₁ : TopologicalSpace B]
    [t₂ : TopologicalSpace F] : TopologicalSpace (TotalSpace F (Trivial B F)) :=
  induced TotalSpace.proj t₁ ⊓ induced (TotalSpace.trivialSnd B F) t₂
#align bundle.trivial.bundle.total_space.topological_space Bundle.Trivial.topologicalSpace

variable [TopologicalSpace B] [TopologicalSpace F]

theorem inducing_toProd : Inducing (TotalSpace.toProd B F) :=
  ⟨by simp only [instTopologicalSpaceProd, induced_inf, induced_compose]; rfl⟩

/-- Homeomorphism between the total space of the trivial bundle and the Cartesian product. -/
def homeomorphProd : TotalSpace F (Trivial B F) ≃ₜ B × F :=
  (TotalSpace.toProd _ _).toHomeomorphOfInducing (inducing_toProd B F)

/-- Local trivialization for trivial bundle. -/
def trivialization : Trivialization F (π F (Bundle.Trivial B F)) where
  -- Porting note: golfed
  toPartialHomeomorph := (homeomorphProd B F).toPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := univ_prod_univ.symm
  proj_toFun _ _ := rfl
#align bundle.trivial.trivialization Bundle.Trivial.trivialization

@[simp]
theorem trivialization_source : (trivialization B F).source = univ := rfl
#align bundle.trivial.trivialization_source Bundle.Trivial.trivialization_source

@[simp]
theorem trivialization_target : (trivialization B F).target = univ := rfl
#align bundle.trivial.trivialization_target Bundle.Trivial.trivialization_target

/-- Fiber bundle instance on the trivial bundle. -/
instance fiberBundle : FiberBundle F (Bundle.Trivial B F) where
  trivializationAtlas' := {trivialization B F}
  trivializationAt' _ := trivialization B F
  mem_baseSet_trivializationAt' := mem_univ
  trivialization_mem_atlas' _ := mem_singleton _
  totalSpaceMk_inducing' _ := (homeomorphProd B F).symm.inducing.comp
    (inducing_const_prod.2 inducing_id)
#align bundle.trivial.fiber_bundle Bundle.Trivial.fiberBundle

theorem eq_trivialization (e : Trivialization F (π F (Bundle.Trivial B F)))
    [i : MemTrivializationAtlas e] : e = trivialization B F := i.out
#align bundle.trivial.eq_trivialization Bundle.Trivial.eq_trivialization

end Trivial

end Bundle

/-! ### Fibrewise product of two bundles -/


section Prod

variable {B : Type*}

section Defs

variable (F₁ : Type*) (E₁ : B → Type*) (F₂ : Type*) (E₂ : B → Type*)
variable [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]

/-- Equip the total space of the fiberwise product of two fiber bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `TotalSpace F₁ E₁ × TotalSpace F₂ E₂`. -/
instance FiberBundle.Prod.topologicalSpace : TopologicalSpace (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :=
  TopologicalSpace.induced
    (fun p ↦ ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂)))
    inferInstance
#align fiber_bundle.prod.topological_space FiberBundle.Prod.topologicalSpace

/-- The diagonal map from the total space of the fiberwise product of two fiber bundles
`E₁`, `E₂` into `TotalSpace F₁ E₁ × TotalSpace F₂ E₂` is `Inducing`. -/
theorem FiberBundle.Prod.inducing_diag :
    Inducing (fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
      TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → TotalSpace F₁ E₁ × TotalSpace F₂ E₂) :=
  ⟨rfl⟩
#align fiber_bundle.prod.inducing_diag FiberBundle.Prod.inducing_diag

end Defs

open FiberBundle

variable [TopologicalSpace B] (F₁ : Type*) [TopologicalSpace F₁] (E₁ : B → Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] (F₂ : Type*) [TopologicalSpace F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)]

namespace Trivialization

variable {F₁ E₁ F₂ E₂}
variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `Trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`. -/
def Prod.toFun' : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → B × F₁ × F₂ :=
  fun p ↦ ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩
#align trivialization.prod.to_fun' Trivialization.Prod.toFun'

variable {e₁ e₂}

theorem Prod.continuous_to_fun : ContinuousOn (Prod.toFun' e₁ e₂)
    (π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)) := by
  let f₁ : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → TotalSpace F₁ E₁ × TotalSpace F₂ E₂ :=
    fun p ↦ ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂))
  let f₂ : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ → (B × F₁) × B × F₂ := fun p ↦ ⟨e₁ p.1, e₂ p.2⟩
  let f₃ : (B × F₁) × B × F₂ → B × F₁ × F₂ := fun p ↦ ⟨p.1.1, p.1.2, p.2.2⟩
  have hf₁ : Continuous f₁ := (Prod.inducing_diag F₁ E₁ F₂ E₂).continuous
  have hf₂ : ContinuousOn f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.toPartialHomeomorph.continuousOn.prod_map e₂.toPartialHomeomorph.continuousOn
  have hf₃ : Continuous f₃ :=
    (continuous_fst.comp continuous_fst).prod_mk (continuous_snd.prod_map continuous_snd)
  refine ((hf₃.comp_continuousOn hf₂).comp hf₁.continuousOn ?_).congr ?_
  · rw [e₁.source_eq, e₂.source_eq]
    exact mapsTo_preimage _ _
  rintro ⟨b, v₁, v₂⟩ ⟨hb₁, _⟩
  simp only [f₃, Prod.toFun', Prod.mk.inj_iff, Function.comp_apply, and_true_iff]
  rw [e₁.coe_fst]
  rw [e₁.source_eq, mem_preimage]
  exact hb₁
#align trivialization.prod.continuous_to_fun Trivialization.Prod.continuous_to_fun

variable (e₁ e₂) [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)]

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `Trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`. -/
noncomputable def Prod.invFun' (p : B × F₁ × F₂) : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) :=
  ⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩
#align trivialization.prod.inv_fun' Trivialization.Prod.invFun'

variable {e₁ e₂}

theorem Prod.left_inv {x : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)}
    (h : x ∈ π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)) :
    Prod.invFun' e₁ e₂ (Prod.toFun' e₁ e₂ x) = x := by
  obtain ⟨x, v₁, v₂⟩ := x
  obtain ⟨h₁ : x ∈ e₁.baseSet, h₂ : x ∈ e₂.baseSet⟩ := h
  simp only [Prod.toFun', Prod.invFun', symm_apply_apply_mk, h₁, h₂]
#align trivialization.prod.left_inv Trivialization.Prod.left_inv

theorem Prod.right_inv {x : B × F₁ × F₂}
    (h : x ∈ (e₁.baseSet ∩ e₂.baseSet) ×ˢ (univ : Set (F₁ × F₂))) :
    Prod.toFun' e₁ e₂ (Prod.invFun' e₁ e₂ x) = x := by
  obtain ⟨x, w₁, w₂⟩ := x
  obtain ⟨⟨h₁ : x ∈ e₁.baseSet, h₂ : x ∈ e₂.baseSet⟩, -⟩ := h
  simp only [Prod.toFun', Prod.invFun', apply_mk_symm, h₁, h₂]
#align trivialization.prod.right_inv Trivialization.Prod.right_inv

theorem Prod.continuous_inv_fun :
    ContinuousOn (Prod.invFun' e₁ e₂) ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ) := by
  rw [(Prod.inducing_diag F₁ E₁ F₂ E₂).continuousOn_iff]
  have H₁ : Continuous fun p : B × F₁ × F₂ ↦ ((p.1, p.2.1), (p.1, p.2.2)) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd)
  refine (e₁.continuousOn_symm.prod_map e₂.continuousOn_symm).comp H₁.continuousOn ?_
  exact fun x h ↦ ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩
#align trivialization.prod.continuous_inv_fun Trivialization.Prod.continuous_inv_fun

variable (e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for bundle types `E₁`, `E₂` over a base `B`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`, whose base set is
`e₁.baseSet ∩ e₂.baseSet`. -/
noncomputable def prod : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂)) where
  toFun := Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  source := π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' x h := ⟨h, Set.mem_univ _⟩
  map_target' x h := h.1
  left_inv' x := Prod.left_inv
  right_inv' x := Prod.right_inv
  open_source := by
    convert (e₁.open_source.prod e₂.open_source).preimage
        (FiberBundle.Prod.inducing_diag F₁ E₁ F₂ E₂).continuous
    ext x
    simp only [Trivialization.source_eq, mfld_simps]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  continuousOn_toFun := Prod.continuous_to_fun
  continuousOn_invFun := Prod.continuous_inv_fun
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun x _ := rfl
#align trivialization.prod Trivialization.prod

@[simp]
theorem baseSet_prod : (prod e₁ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet := rfl
#align trivialization.base_set_prod Trivialization.baseSet_prod

theorem prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) :
    (prod e₁ e₂).toPartialEquiv.symm (x, w₁, w₂) = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ := rfl
#align trivialization.prod_symm_apply Trivialization.prod_symm_apply

end Trivialization

open Trivialization

variable [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)] [∀ x : B, TopologicalSpace (E₁ x)]
  [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

/-- The product of two fiber bundles is a fiber bundle. -/
noncomputable instance FiberBundle.prod : FiberBundle (F₁ × F₂) (E₁ ×ᵇ E₂) where
  totalSpaceMk_inducing' b := by
    rw [← (Prod.inducing_diag F₁ E₁ F₂ E₂).of_comp_iff]
    exact (totalSpaceMk_inducing F₁ E₁ b).prod_map (totalSpaceMk_inducing F₂ E₂ b)
  trivializationAtlas' := { e |
    ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
      e = Trivialization.prod e₁ e₂ }
  trivializationAt' b := (trivializationAt F₁ E₁ b).prod (trivializationAt F₂ E₂ b)
  mem_baseSet_trivializationAt' b :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ b, mem_baseSet_trivializationAt F₂ E₂ b⟩
  trivialization_mem_atlas' b :=
    ⟨trivializationAt F₁ E₁ b, trivializationAt F₂ E₂ b, inferInstance, inferInstance, rfl⟩
#align fiber_bundle.prod FiberBundle.prod

instance {e₁ : Trivialization F₁ (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)}
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] :
    MemTrivializationAtlas (e₁.prod e₂ : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂))) where
  out := ⟨e₁, e₂, inferInstance, inferInstance, rfl⟩

end Prod

/-! ### Pullbacks of fiber bundles -/

section

universe u v w₁ w₂ U

variable {B : Type u} (F : Type v) (E : B → Type w₁) {B' : Type w₂} (f : B' → B)

instance [∀ x : B, TopologicalSpace (E x)] : ∀ x : B', TopologicalSpace ((f *ᵖ E) x) := by
  -- Porting note: Original proof was `delta_instance bundle.pullback`
  intro x
  rw [Bundle.Pullback]
  infer_instance

variable [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)]

/-- Definition of `Pullback.TotalSpace.topologicalSpace`, which we make irreducible. -/
irreducible_def pullbackTopology : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  induced TotalSpace.proj ‹TopologicalSpace B'› ⊓
    induced (Pullback.lift f) ‹TopologicalSpace (TotalSpace F E)›
#align pullback_topology pullbackTopology

/-- The topology on the total space of a pullback bundle is the coarsest topology for which both
the projections to the base and the map to the original bundle are continuous. -/
instance Pullback.TotalSpace.topologicalSpace : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  pullbackTopology F E f
#align pullback.total_space.topological_space Pullback.TotalSpace.topologicalSpace

theorem Pullback.continuous_proj (f : B' → B) : Continuous (π F (f *ᵖ E)) := by
  rw [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  exact inf_le_left
#align pullback.continuous_proj Pullback.continuous_proj

theorem Pullback.continuous_lift (f : B' → B) : Continuous (@Pullback.lift B F E B' f) := by
  rw [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  exact inf_le_right
#align pullback.continuous_lift Pullback.continuous_lift

theorem inducing_pullbackTotalSpaceEmbedding (f : B' → B) :
    Inducing (@pullbackTotalSpaceEmbedding B F E B' f) := by
  constructor
  simp_rw [instTopologicalSpaceProd, induced_inf, induced_compose,
    Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  rfl
#align inducing_pullback_total_space_embedding inducing_pullbackTotalSpaceEmbedding

section FiberBundle

variable [TopologicalSpace F] [TopologicalSpace B]

theorem Pullback.continuous_totalSpaceMk [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    {f : B' → B} {x : B'} : Continuous (@TotalSpace.mk _ F (f *ᵖ E) x) := by
  simp only [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, induced_compose,
    induced_inf, Function.comp, induced_const, top_inf_eq, pullbackTopology_def]
  exact le_of_eq (FiberBundle.totalSpaceMk_inducing F E (f x)).induced
#align pullback.continuous_total_space_mk Pullback.continuous_totalSpaceMk

variable {E F} [∀ _b, Zero (E _b)] {K : Type U} [FunLike K B' B] [ContinuousMapClass K B' B]

-- Porting note: universe levels are explicitly provided
/-- A fiber bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
noncomputable def Trivialization.pullback (e : Trivialization F (π F E)) (f : K) :
    Trivialization F (π F ((f : B' → B) *ᵖ E)) where
  toFun z := (z.proj, (e (Pullback.lift f z)).2)
  invFun y := @TotalSpace.mk _ F (f *ᵖ E) y.1 (e.symm (f y.1) y.2)
  source := Pullback.lift f ⁻¹' e.source
  baseSet := f ⁻¹' e.baseSet
  target := (f ⁻¹' e.baseSet) ×ˢ univ
  map_source' x h := by
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj] at h
    simp_rw [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff, mem_preimage, h]
  map_target' y h := by
    rw [mem_prod, mem_preimage] at h
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj, h.1]
  left_inv' x h := by
    simp_rw [mem_preimage, e.mem_source, Pullback.lift_proj] at h
    simp_rw [Pullback.lift, e.symm_apply_apply_mk h]
  right_inv' x h := by
    simp_rw [mem_prod, mem_preimage, mem_univ, and_true_iff] at h
    simp_rw [Pullback.lift_mk, e.apply_mk_symm h]
  open_source := by
    simp_rw [e.source_eq, ← preimage_comp]
    exact e.open_baseSet.preimage ((map_continuous f).comp <| Pullback.continuous_proj F E f)
  open_target := ((map_continuous f).isOpen_preimage _ e.open_baseSet).prod isOpen_univ
  open_baseSet := (map_continuous f).isOpen_preimage _ e.open_baseSet
  continuousOn_toFun :=
    (Pullback.continuous_proj F E f).continuousOn.prod
      (continuous_snd.comp_continuousOn <|
        e.continuousOn.comp (Pullback.continuous_lift F E f).continuousOn Subset.rfl)
  continuousOn_invFun := by
    dsimp only
    simp_rw [(inducing_pullbackTotalSpaceEmbedding F E f).continuousOn_iff, Function.comp,
      pullbackTotalSpaceEmbedding]
    refine
      continuousOn_fst.prod
        (e.continuousOn_symm.comp ((map_continuous f).prod_map continuous_id).continuousOn
          Subset.rfl)
  source_eq := by
    dsimp only
    rw [e.source_eq]
    rfl
  target_eq := rfl
  proj_toFun y _ := rfl
#align trivialization.pullback Trivialization.pullback

noncomputable instance FiberBundle.pullback [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    (f : K) : FiberBundle F ((f : B' → B) *ᵖ E) where
  totalSpaceMk_inducing' x :=
    inducing_of_inducing_compose (Pullback.continuous_totalSpaceMk F E)
      (Pullback.continuous_lift F E f) (totalSpaceMk_inducing F E (f x))
  trivializationAtlas' :=
    { ef | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), ef = e.pullback f }
  trivializationAt' x := (trivializationAt F E (f x)).pullback f
  mem_baseSet_trivializationAt' x := mem_baseSet_trivializationAt F E (f x)
  trivialization_mem_atlas' x := ⟨trivializationAt F E (f x), inferInstance, rfl⟩
#align fiber_bundle.pullback FiberBundle.pullback

end FiberBundle

end
