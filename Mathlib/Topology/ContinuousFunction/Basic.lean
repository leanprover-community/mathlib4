/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module topology.continuous_function.basic
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.UnionLift
import Mathbin.Topology.Homeomorph

/-!
# Continuous bundled maps

In this file we define the type `continuous_map` of continuous bundled maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/


open Function

/-- The type of continuous maps from `α` to `β`.

When possible, instead of parametrizing results over `(f : C(α, β))`,
you should parametrize over `{F : Type*} [continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `continuous_map_class`. -/
@[protect_proj]
structure ContinuousMap (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] where
  toFun : α → β
  continuous_toFun : Continuous to_fun := by continuity
#align continuous_map ContinuousMap

-- mathport name: «exprC( , )»
notation "C(" α ", " β ")" => ContinuousMap α β

section

/-- `continuous_map_class F α β` states that `F` is a type of continuous maps.

You should extend this class when you extend `continuous_map`. -/
class ContinuousMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α]
  [TopologicalSpace β] extends FunLike F α fun _ => β where
  map_continuous (f : F) : Continuous f
#align continuous_map_class ContinuousMapClass

end

export ContinuousMapClass (map_continuous)

attribute [continuity] map_continuous

section ContinuousMapClass

variable {F α β : Type _} [TopologicalSpace α] [TopologicalSpace β] [ContinuousMapClass F α β]

include β

theorem map_continuousAt (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).ContinuousAt
#align map_continuous_at map_continuousAt

theorem map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).ContinuousWithinAt
#align map_continuous_within_at map_continuousWithinAt

instance : CoeTC F C(α, β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f }⟩

end ContinuousMapClass

/-! ### Continuous maps-/


namespace ContinuousMap

variable {α β γ δ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

instance : ContinuousMapClass C(α, β) α β
    where
  coe := ContinuousMap.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_continuous := ContinuousMap.continuous_toFun

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun C(α, β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe {f : C(α, β)} : f.toFun = (f : α → β) :=
  rfl
#align continuous_map.to_fun_eq_coe ContinuousMap.toFun_eq_coe

-- this must come after the coe_to_fun definition
initialize_simps_projections ContinuousMap (toFun → apply)

@[protected, simp, norm_cast]
theorem coe_coe {F : Type _} [ContinuousMapClass F α β] (f : F) : ⇑(f : C(α, β)) = f :=
  rfl
#align continuous_map.coe_coe ContinuousMap.coe_coe

@[ext]
theorem ext {f g : C(α, β)} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h
#align continuous_map.ext ContinuousMap.ext

/-- Copy of a `continuous_map` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : C(α, β)) (f' : α → β) (h : f' = f) : C(α, β)
    where
  toFun := f'
  continuous_toFun := h.symm ▸ f.continuous_toFun
#align continuous_map.copy ContinuousMap.copy

@[simp]
theorem coe_copy (f : C(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align continuous_map.coe_copy ContinuousMap.coe_copy

theorem copy_eq (f : C(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align continuous_map.copy_eq ContinuousMap.copy_eq

variable {α β} {f g : C(α, β)}

/-- Deprecated. Use `map_continuous` instead. -/
protected theorem continuous (f : C(α, β)) : Continuous f :=
  f.continuous_toFun
#align continuous_map.continuous ContinuousMap.continuous

@[continuity]
theorem continuous_set_coe (s : Set C(α, β)) (f : s) : Continuous f :=
  f.1.Continuous
#align continuous_map.continuous_set_coe ContinuousMap.continuous_set_coe

/-- Deprecated. Use `map_continuous_at` instead. -/
protected theorem continuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  f.Continuous.ContinuousAt
#align continuous_map.continuous_at ContinuousMap.continuousAt

/-- Deprecated. Use `fun_like.congr_fun` instead. -/
protected theorem congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x :=
  H ▸ rfl
#align continuous_map.congr_fun ContinuousMap.congr_fun

/-- Deprecated. Use `fun_like.congr_arg` instead. -/
protected theorem congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y :=
  h ▸ rfl
#align continuous_map.congr_arg ContinuousMap.congr_arg

theorem coe_injective : @Function.Injective C(α, β) (α → β) coeFn := fun f g h => by
  cases f <;> cases g <;> congr
#align continuous_map.coe_injective ContinuousMap.coe_injective

@[simp]
theorem coe_mk (f : α → β) (h : Continuous f) : ⇑(⟨f, h⟩ : C(α, β)) = f :=
  rfl
#align continuous_map.coe_mk ContinuousMap.coe_mk

theorem map_specializes (f : C(α, β)) {x y : α} (h : x ⤳ y) : f x ⤳ f y :=
  h.map f.2
#align continuous_map.map_specializes ContinuousMap.map_specializes

section

variable (α β)

/--
The continuous functions from `α` to `β` are the same as the plain functions when `α` is discrete.
-/
@[simps]
def equivFnOfDiscrete [DiscreteTopology α] : C(α, β) ≃ (α → β) :=
  ⟨fun f => f, fun f => ⟨f, continuous_of_discreteTopology⟩, fun f =>
    by
    ext
    rfl, fun f => by
    ext
    rfl⟩
#align continuous_map.equiv_fn_of_discrete ContinuousMap.equivFnOfDiscrete

end

variable (α)

/-- The identity as a continuous map. -/
protected def id : C(α, α) :=
  ⟨id⟩
#align continuous_map.id ContinuousMap.id

@[simp]
theorem coe_id : ⇑(ContinuousMap.id α) = id :=
  rfl
#align continuous_map.coe_id ContinuousMap.coe_id

/-- The constant map as a continuous map. -/
def const (b : β) : C(α, β) :=
  ⟨const α b⟩
#align continuous_map.const ContinuousMap.const

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align continuous_map.coe_const ContinuousMap.coe_const

instance [Inhabited β] : Inhabited C(α, β) :=
  ⟨const α default⟩

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousMap.id α a = a :=
  rfl
#align continuous_map.id_apply ContinuousMap.id_apply

@[simp]
theorem const_apply (b : β) (a : α) : const α b a = b :=
  rfl
#align continuous_map.const_apply ContinuousMap.const_apply

/-- The composition of continuous maps, as a continuous map. -/
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) :=
  ⟨f ∘ g⟩
#align continuous_map.comp ContinuousMap.comp

@[simp]
theorem coe_comp (f : C(β, γ)) (g : C(α, β)) : ⇑(comp f g) = f ∘ g :=
  rfl
#align continuous_map.coe_comp ContinuousMap.coe_comp

@[simp]
theorem comp_apply (f : C(β, γ)) (g : C(α, β)) (a : α) : comp f g a = f (g a) :=
  rfl
#align continuous_map.comp_apply ContinuousMap.comp_apply

@[simp]
theorem comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(α, β)) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align continuous_map.comp_assoc ContinuousMap.comp_assoc

@[simp]
theorem id_comp (f : C(α, β)) : (ContinuousMap.id _).comp f = f :=
  ext fun _ => rfl
#align continuous_map.id_comp ContinuousMap.id_comp

@[simp]
theorem comp_id (f : C(α, β)) : f.comp (ContinuousMap.id _) = f :=
  ext fun _ => rfl
#align continuous_map.comp_id ContinuousMap.comp_id

@[simp]
theorem const_comp (c : γ) (f : C(α, β)) : (const β c).comp f = const α c :=
  ext fun _ => rfl
#align continuous_map.const_comp ContinuousMap.const_comp

@[simp]
theorem comp_const (f : C(β, γ)) (b : β) : f.comp (const α b) = const α (f b) :=
  ext fun _ => rfl
#align continuous_map.comp_const ContinuousMap.comp_const

theorem cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align continuous_map.cancel_right ContinuousMap.cancel_right

theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align continuous_map.cancel_left ContinuousMap.cancel_left

instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
    ⟨const _ b₁, const _ b₂, fun h => hb <| FunLike.congr_fun h <| Classical.arbitrary α⟩⟩

section Prod

variable {α₁ α₂ β₁ β₂ : Type _} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁]
  [TopologicalSpace β₂]

/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂)
    where
  toFun x := (f x, g x)
  continuous_toFun := Continuous.prod_mk f.Continuous g.Continuous
#align continuous_map.prod_mk ContinuousMap.prodMk

/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
@[simps]
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂)
    where
  toFun := Prod.map f g
  continuous_toFun := Continuous.prod_map f.Continuous g.Continuous
#align continuous_map.prod_map ContinuousMap.prodMap

@[simp]
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl
#align continuous_map.prod_eval ContinuousMap.prod_eval

end Prod

section Pi

variable {I A : Type _} {X : I → Type _} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where toFun (a : A) (i : I) := f i a
#align continuous_map.pi ContinuousMap.pi

@[simp]
theorem pi_eval (f : ∀ i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl
#align continuous_map.pi_eval ContinuousMap.pi_eval

end Pi

section Restrict

variable (s : Set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) :=
  ⟨f ∘ coe⟩
#align continuous_map.restrict ContinuousMap.restrict

@[simp]
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = f ∘ coe :=
  rfl
#align continuous_map.coe_restrict ContinuousMap.coe_restrict

/-- The restriction of a continuous map onto the preimage of a set. -/
@[simps]
def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun x => f.2.ContinuousAt.restrictPreimage⟩
#align continuous_map.restrict_preimage ContinuousMap.restrictPreimage

end Restrict

section Gluing

variable {ι : Type _} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : ∀ x : α, ∃ i, S i ∈ nhds x)

include hφ hS

/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover : C(α, β) :=
  by
  have H : (⋃ i, S i) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_unionᵢ]
    obtain ⟨i, hi⟩ := hS x
    exact ⟨i, mem_of_mem_nhds hi⟩
  refine' ⟨Set.liftCover S (fun i => φ i) hφ H, continuous_subtype_nhds_cover hS _⟩
  intro i
  convert (φ i).Continuous
  ext x
  exact Set.liftCover_coe x
#align continuous_map.lift_cover ContinuousMap.liftCover

variable {S φ hφ hS}

@[simp]
theorem liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x :=
  Set.liftCover_coe _
#align continuous_map.lift_cover_coe ContinuousMap.liftCover_coe

@[simp]
theorem liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i :=
  ext <| liftCover_coe
#align continuous_map.lift_cover_restrict ContinuousMap.liftCover_restrict

omit hφ hS

variable (A : Set (Set α)) (F : ∀ (s : Set α) (hi : s ∈ A), C(s, β))
  (hF :
    ∀ (s) (hs : s ∈ A) (t) (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
      F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ nhds x)

include hF hA

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover' : C(α, β) :=
  by
  let S : A → Set α := coe
  let F : ∀ i : A, C(i, β) := fun i => F i i.Prop
  refine' lift_cover S F (fun i j => hF i i.Prop j j.Prop) _
  intro x
  obtain ⟨s, hs, hsx⟩ := hA x
  exact ⟨⟨s, hs⟩, hsx⟩
#align continuous_map.lift_cover' ContinuousMap.liftCover'

variable {A F hF hA}

@[simp]
theorem lift_cover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : (coe : A → Set α) ⟨s, hs⟩ := x
  liftCover_coe x'
#align continuous_map.lift_cover_coe' ContinuousMap.lift_cover_coe'

@[simp]
theorem lift_cover_restrict' {s : Set α} {hs : s ∈ A} :
    (liftCover' A F hF hA).restrict s = F s hs :=
  ext <| lift_cover_coe'
#align continuous_map.lift_cover_restrict' ContinuousMap.lift_cover_restrict'

end Gluing

end ContinuousMap

namespace Homeomorph

variable {α β γ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

variable (f : α ≃ₜ β) (g : β ≃ₜ γ)

/-- The forward direction of a homeomorphism, as a bundled continuous map. -/
@[simps]
def toContinuousMap (e : α ≃ₜ β) : C(α, β) :=
  ⟨e⟩
#align homeomorph.to_continuous_map Homeomorph.toContinuousMap

/-- `homeomorph.to_continuous_map` as a coercion. -/
instance : Coe (α ≃ₜ β) C(α, β) :=
  ⟨Homeomorph.toContinuousMap⟩

theorem toContinuousMap_as_coe : f.toContinuousMap = f :=
  rfl
#align homeomorph.to_continuous_map_as_coe Homeomorph.toContinuousMap_as_coe

@[simp]
theorem coe_refl : (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α :=
  rfl
#align homeomorph.coe_refl Homeomorph.coe_refl

@[simp]
theorem coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f :=
  rfl
#align homeomorph.coe_trans Homeomorph.coe_trans

/-- Left inverse to a continuous map from a homeomorphism, mirroring `equiv.symm_comp_self`. -/
@[simp]
theorem symm_comp_to_continuousMap : (f.symm : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α :=
  by rw [← coeTrans, self_trans_symm, coe_refl]
#align homeomorph.symm_comp_to_continuous_map Homeomorph.symm_comp_to_continuousMap

/-- Right inverse to a continuous map from a homeomorphism, mirroring `equiv.self_comp_symm`. -/
@[simp]
theorem to_continuousMap_comp_symm : (f : C(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β :=
  by rw [← coeTrans, symm_trans_self, coe_refl]
#align homeomorph.to_continuous_map_comp_symm Homeomorph.to_continuousMap_comp_symm

end Homeomorph

