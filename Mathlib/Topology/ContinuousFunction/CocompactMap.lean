/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.ContinuousFunction.Basic

#align_import topology.continuous_function.cocompact_map from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# Cocompact continuous maps

The type of *cocompact continuous maps* are those which tend to the cocompact filter on the
codomain along the cocompact filter on the domain. When the domain and codomain are Hausdorff, this
is equivalent to many other conditions, including that preimages of compact sets are compact. -/


universe u v w

open Filter Set

/-! ### Cocompact continuous maps -/


/-- A *cocompact continuous map* is a continuous function between topological spaces which
tends to the cocompact filter along the cocompact filter. Functions for which preimages of compact
sets are compact always satisfy this property, and the converse holds for cocompact continuous maps
when the codomain is Hausdorff (see `CocompactMap.tendsto_of_forall_preimage` and
`CocompactMap.isCompact_preimage`).

Cocompact maps thus generalise proper maps, with which they correspond when the codomain is
Hausdorff. -/
structure CocompactMap (α : Type u) (β : Type v) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMap α β : Type max u v where
  /-- The cocompact filter on `α` tends to the cocompact filter on `β` under the function -/
  cocompact_tendsto' : Tendsto toFun (cocompact α) (cocompact β)
#align cocompact_map CocompactMap

section

/-- `CocompactMapClass F α β` states that `F` is a type of cocompact continuous maps.

You should also extend this typeclass when you extend `CocompactMap`. -/
class CocompactMapClass (F : Type*) (α β : outParam <| Type*) [TopologicalSpace α]
  [TopologicalSpace β] extends ContinuousMapClass F α β where
  /-- The cocompact filter on `α` tends to the cocompact filter on `β` under the function -/
  cocompact_tendsto (f : F) : Tendsto f (cocompact α) (cocompact β)
#align cocompact_map_class CocompactMapClass

end

namespace CocompactMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CocompactMapClass F α β]

/-- Turn an element of a type `F` satisfying `CocompactMapClass F α β` into an actual
`CocompactMap`. This is declared as the default coercion from `F` to `CocompactMap α β`. -/
@[coe]
def toCocompactMap (f : F) : CocompactMap α β :=
  { (f : C(α, β)) with
    cocompact_tendsto' := cocompact_tendsto f }

instance : CoeTC F (CocompactMap α β) :=
  ⟨toCocompactMap⟩

end CocompactMapClass

export CocompactMapClass (cocompact_tendsto)

namespace CocompactMap

section Basics

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

instance : CocompactMapClass (CocompactMap α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    -- ⊢ { toContinuousMap := ContinuousMap.mk toFun✝, cocompact_tendsto' := cocompac …
    obtain ⟨⟨_, _⟩, _⟩ := g
    -- ⊢ { toContinuousMap := ContinuousMap.mk toFun✝¹, cocompact_tendsto' := cocompa …
    congr
    -- 🎉 no goals
  map_continuous f := f.continuous_toFun
  cocompact_tendsto f := f.cocompact_tendsto'

/- Porting note: not needed anymore
/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CocompactMap α β) fun _ => α → β :=
  FunLike.hasCoeToFun-/

@[simp]
theorem coe_toContinuousMap {f : CocompactMap α β} : (f.toContinuousMap : α → β) = f :=
  rfl
#align cocompact_map.coe_to_continuous_fun CocompactMap.coe_toContinuousMap

@[ext]
theorem ext {f g : CocompactMap α β} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h
#align cocompact_map.ext CocompactMap.ext

/-- Copy of a `CocompactMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : CocompactMap α β where
  toFun := f'
  continuous_toFun := by
    rw [h]
    -- ⊢ Continuous ↑f
    exact f.continuous_toFun
    -- 🎉 no goals
  cocompact_tendsto' := by
    simp_rw [h]
    -- ⊢ Tendsto (↑f) (cocompact α) (cocompact β)
    exact f.cocompact_tendsto'
    -- 🎉 no goals
#align cocompact_map.copy CocompactMap.copy

@[simp]
theorem coe_copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align cocompact_map.coe_copy CocompactMap.coe_copy

theorem copy_eq (f : CocompactMap α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align cocompact_map.copy_eq CocompactMap.copy_eq

@[simp]
theorem coe_mk (f : C(α, β)) (h : Tendsto f (cocompact α) (cocompact β)) :
    ⇑(⟨f, h⟩ : CocompactMap α β) = f :=
  rfl
#align cocompact_map.coe_mk CocompactMap.coe_mk

section

variable (α)

/-- The identity as a cocompact continuous map. -/
protected def id : CocompactMap α α :=
  ⟨ContinuousMap.id _, tendsto_id⟩
#align cocompact_map.id CocompactMap.id

@[simp]
theorem coe_id : ⇑(CocompactMap.id α) = id :=
  rfl
#align cocompact_map.coe_id CocompactMap.coe_id

end

instance : Inhabited (CocompactMap α α) :=
  ⟨CocompactMap.id α⟩

/-- The composition of cocompact continuous maps, as a cocompact continuous map. -/
def comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ :=
  ⟨f.toContinuousMap.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩
#align cocompact_map.comp CocompactMap.comp

@[simp]
theorem coe_comp (f : CocompactMap β γ) (g : CocompactMap α β) : ⇑(comp f g) = f ∘ g :=
  rfl
#align cocompact_map.coe_comp CocompactMap.coe_comp

@[simp]
theorem comp_apply (f : CocompactMap β γ) (g : CocompactMap α β) (a : α) : comp f g a = f (g a) :=
  rfl
#align cocompact_map.comp_apply CocompactMap.comp_apply

@[simp]
theorem comp_assoc (f : CocompactMap γ δ) (g : CocompactMap β γ) (h : CocompactMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align cocompact_map.comp_assoc CocompactMap.comp_assoc

@[simp]
theorem id_comp (f : CocompactMap α β) : (CocompactMap.id _).comp f = f :=
  ext fun _ => rfl
#align cocompact_map.id_comp CocompactMap.id_comp

@[simp]
theorem comp_id (f : CocompactMap α β) : f.comp (CocompactMap.id _) = f :=
  ext fun _ => rfl
#align cocompact_map.comp_id CocompactMap.comp_id

theorem tendsto_of_forall_preimage {f : α → β} (h : ∀ s, IsCompact s → IsCompact (f ⁻¹' s)) :
    Tendsto f (cocompact α) (cocompact β) := fun s hs =>
  match mem_cocompact.mp hs with
  | ⟨t, ht, hts⟩ =>
    mem_map.mpr (mem_cocompact.mpr ⟨f ⁻¹' t, h t ht, by simpa using preimage_mono hts⟩)
                                                        -- 🎉 no goals
#align cocompact_map.tendsto_of_forall_preimage CocompactMap.tendsto_of_forall_preimage

/-- If the codomain is Hausdorff, preimages of compact sets are compact under a cocompact
continuous map. -/
theorem isCompact_preimage [T2Space β] (f : CocompactMap α β) ⦃s : Set β⦄ (hs : IsCompact s) :
    IsCompact (f ⁻¹' s) := by
  obtain ⟨t, ht, hts⟩ :=
    mem_cocompact'.mp
      (by
        simpa only [preimage_image_preimage, preimage_compl] using
          mem_map.mp
            (cocompact_tendsto f <|
              mem_cocompact.mpr ⟨s, hs, compl_subset_compl.mpr (image_preimage_subset f _)⟩))
  exact
    isCompact_of_isClosed_subset ht (hs.isClosed.preimage <| map_continuous f) (by simpa using hts)
#align cocompact_map.is_compact_preimage CocompactMap.isCompact_preimage

end Basics

end CocompactMap

/-- A homeomorphism is a cocompact map. -/
@[simps]
def Homeomorph.toCocompactMap {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α ≃ₜ β) : CocompactMap α β where
  toFun := f
  continuous_toFun := f.continuous
  cocompact_tendsto' := by
    refine' CocompactMap.tendsto_of_forall_preimage fun K hK => _
    -- ⊢ IsCompact ((ContinuousMap.mk ↑f).toFun ⁻¹' K)
    erw [K.preimage_equiv_eq_image_symm]
    -- ⊢ IsCompact (↑f.symm '' K)
    exact hK.image f.symm.continuous
    -- 🎉 no goals
#align homeomorph.to_cocompact_map Homeomorph.toCocompactMap
