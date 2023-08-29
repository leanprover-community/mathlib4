/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.Homeomorph

#align_import topology.continuous_function.basic from "leanprover-community/mathlib"@"55d771df074d0dd020139ee1cd4b95521422df9f"

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `FunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/


open Function

/-- The type of continuous maps from `α` to `β`.

When possible, instead of parametrizing results over `(f : C(α, β))`,
you should parametrize over `{F : Type*} [ContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `ContinuousMapClass`. -/
structure ContinuousMap (α β : Type*) [TopologicalSpace α] [TopologicalSpace β] where
  /-- The function `α → β` -/
  protected toFun : α → β
  /-- Proposition that `toFun` is continuous -/
  protected continuous_toFun : Continuous toFun := by continuity
#align continuous_map ContinuousMap

/-- The type of continuous maps from `α` to `β`. -/
notation "C(" α ", " β ")" => ContinuousMap α β

section

/-- `ContinuousMapClass F α β` states that `F` is a type of continuous maps.

You should extend this class when you extend `ContinuousMap`. -/
class ContinuousMapClass (F : Type*) (α β : outParam <| Type*) [TopologicalSpace α]
  [TopologicalSpace β] extends FunLike F α fun _ => β where
  /-- Continuity -/
  map_continuous (f : F) : Continuous f
#align continuous_map_class ContinuousMapClass

end

export ContinuousMapClass (map_continuous)

attribute [continuity] map_continuous

section ContinuousMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [ContinuousMapClass F α β]

theorem map_continuousAt (f : F) (a : α) : ContinuousAt f a :=
  (map_continuous f).continuousAt
#align map_continuous_at map_continuousAt

theorem map_continuousWithinAt (f : F) (s : Set α) (a : α) : ContinuousWithinAt f s a :=
  (map_continuous f).continuousWithinAt
#align map_continuous_within_at map_continuousWithinAt

/-- Coerce a bundled morphism with a `ContinuousMapClass` instance to a `ContinuousMap`. -/
@[coe] def toContinuousMap (f : F) : C(α, β) := ⟨f, map_continuous f⟩

instance : CoeTC F C(α, β) := ⟨toContinuousMap⟩

end ContinuousMapClass

/-! ### Continuous maps-/


namespace ContinuousMap

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ]

instance toContinuousMapClass : ContinuousMapClass C(α, β) α β where
  coe := ContinuousMap.toFun
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ mk toFun✝ = g
                                      -- ⊢ mk toFun✝¹ = mk toFun✝
                                               -- 🎉 no goals
  map_continuous := ContinuousMap.continuous_toFun

/- Porting note: Probably not needed anymore
/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun C(α, β) fun _ => α → β :=
  FunLike.hasCoeToFun-/

@[simp]
theorem toFun_eq_coe {f : C(α, β)} : f.toFun = (f : α → β) :=
  rfl
#align continuous_map.to_fun_eq_coe ContinuousMap.toFun_eq_coe

instance : CanLift (α → β) C(α, β) FunLike.coe Continuous := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- See note [custom simps projection]. -/
def Simps.apply (f : C(α, β)) : α → β := f

-- this must come after the coe_to_fun definition
initialize_simps_projections ContinuousMap (toFun → apply)

@[simp] -- Porting note: removed `norm_cast` attribute
protected theorem coe_coe {F : Type*} [ContinuousMapClass F α β] (f : F) : ⇑(f : C(α, β)) = f :=
  rfl
#align continuous_map.coe_coe ContinuousMap.coe_coe

@[ext]
theorem ext {f g : C(α, β)} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h
#align continuous_map.ext ContinuousMap.ext

/-- Copy of a `ContinuousMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : C(α, β)) (f' : α → β) (h : f' = f) : C(α, β) where
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

variable {f g : C(α, β)}

/-- Deprecated. Use `map_continuous` instead. -/
protected theorem continuous (f : C(α, β)) : Continuous f :=
  f.continuous_toFun
#align continuous_map.continuous ContinuousMap.continuous

@[continuity]
theorem continuous_set_coe (s : Set C(α, β)) (f : s) : Continuous (f : α → β) :=
  f.1.continuous
#align continuous_map.continuous_set_coe ContinuousMap.continuous_set_coe

/-- Deprecated. Use `map_continuousAt` instead. -/
protected theorem continuousAt (f : C(α, β)) (x : α) : ContinuousAt f x :=
  f.continuous.continuousAt
#align continuous_map.continuous_at ContinuousMap.continuousAt

/-- Deprecated. Use `FunLike.congr_fun` instead. -/
protected theorem congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x :=
  H ▸ rfl
#align continuous_map.congr_fun ContinuousMap.congr_fun

/-- Deprecated. Use `FunLike.congr_arg` instead. -/
protected theorem congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y :=
  h ▸ rfl
#align continuous_map.congr_arg ContinuousMap.congr_arg

theorem coe_injective : @Function.Injective C(α, β) (α → β) (↑) := fun f g h => by
  cases f; cases g; congr
  -- ⊢ mk toFun✝ = g
           -- ⊢ mk toFun✝¹ = mk toFun✝
                    -- 🎉 no goals
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
  ⟨fun f => f,
    fun f => ⟨f, continuous_of_discreteTopology⟩,
    fun _ => by ext; rfl,
                -- ⊢ ↑((fun f => mk f) ((fun f => ↑f) x✝)) a✝ = ↑x✝ a✝
                     -- 🎉 no goals
    fun _ => by ext; rfl⟩
                -- ⊢ (fun f => ↑f) ((fun f => mk f) x✝¹) x✝ = x✝¹ x✝
                     -- 🎉 no goals
#align continuous_map.equiv_fn_of_discrete ContinuousMap.equivFnOfDiscrete

end

variable (α)

/-- The identity as a continuous map. -/
protected def id : C(α, α) where
  toFun := id
#align continuous_map.id ContinuousMap.id

@[simp]
theorem coe_id : ⇑(ContinuousMap.id α) = id :=
  rfl
#align continuous_map.coe_id ContinuousMap.coe_id

/-- The constant map as a continuous map. -/
def const (b : β) : C(α, β) where
  toFun := fun _ : α => b
#align continuous_map.const ContinuousMap.const

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align continuous_map.coe_const ContinuousMap.coe_const

/-- `Function.const α b` as a bundled continuous function of `b`. -/
@[simps (config := .asFn)]
def constPi : C(β, α → β) where
  toFun b := Function.const α b

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
def comp (f : C(β, γ)) (g : C(α, β)) : C(α, γ) where
  toFun := f ∘ g
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
  ⟨fun h => ext <| hg.forall.2 <| FunLike.ext_iff.1 h, congr_arg (ContinuousMap.comp · g)⟩
#align continuous_map.cancel_right ContinuousMap.cancel_right

theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
                                  -- 🎉 no goals
#align continuous_map.cancel_left ContinuousMap.cancel_left

instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
  ⟨const _ b₁, const _ b₂, fun h => hb <| FunLike.congr_fun h <| Classical.arbitrary α⟩⟩

section Prod

variable {α₁ α₂ β₁ β₂ : Type*} [TopologicalSpace α₁] [TopologicalSpace α₂] [TopologicalSpace β₁]
  [TopologicalSpace β₂]

/-- `Prod.fst : (x, y) ↦ x` as a bundled continuous map. -/
@[simps (config := .asFn)]
def fst : C(α × β, α) where
  toFun := Prod.fst

/-- `Prod.snd : (x, y) ↦ y` as a bundled continuous map. -/
@[simps (config := .asFn)]
def snd : C(α × β, β) where
  toFun := Prod.snd

/-- Given two continuous maps `f` and `g`, this is the continuous map `x ↦ (f x, g x)`. -/
def prodMk (f : C(α, β₁)) (g : C(α, β₂)) : C(α, β₁ × β₂) where
  toFun x := (f x, g x)
#align continuous_map.prod_mk ContinuousMap.prodMk

/-- Given two continuous maps `f` and `g`, this is the continuous map `(x, y) ↦ (f x, g y)`. -/
@[simps]
def prodMap (f : C(α₁, α₂)) (g : C(β₁, β₂)) : C(α₁ × β₁, α₂ × β₂) where
  toFun := Prod.map f g
  continuous_toFun := f.continuous.prod_map g.continuous
  -- Porting note: proof was `continuity`
#align continuous_map.prod_map ContinuousMap.prodMap

@[simp]
theorem prod_eval (f : C(α, β₁)) (g : C(α, β₂)) (a : α) : (prodMk f g) a = (f a, g a) :=
  rfl
#align continuous_map.prod_eval ContinuousMap.prod_eval

/-- `Prod.swap` bundled as a `ContinuousMap`. -/
@[simps!]
def prodSwap : C(α × β, β × α) := .prodMk .snd .fst

end Prod

/-- `Sigma.mk i` as a bundled continuous map. -/
@[simps apply]
def sigmaMk {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (i : ι) :
    C(Y i, Σ i, Y i) where
  toFun := Sigma.mk i

section Pi

variable {I A : Type*} {X Y : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (Y i)]

/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : ∀ i, C(A, X i)) : C(A, ∀ i, X i) where
  toFun (a : A) (i : I) := f i a
#align continuous_map.pi ContinuousMap.pi

@[simp]
theorem pi_eval (f : ∀ i, C(A, X i)) (a : A) : (pi f) a = fun i : I => (f i) a :=
  rfl
#align continuous_map.pi_eval ContinuousMap.pi_eval

/-- Evaluation at point as a bundled continuous map. -/
@[simps (config := .asFn)]
def eval (i : I) : C(∀ j, X j, X i) where
  toFun := Function.eval i

/-- Combine a collection of bundled continuous maps `C(X i, Y i)` into a bundled continuous map
`C(∀ i, X i, ∀ i, Y i)`. -/
@[simps!]
def piMap (f : ∀ i, C(X i, Y i)) : C((i : I) → X i, (i : I) → Y i) :=
  .pi fun i ↦ (f i).comp (eval i)

end Pi

section Restrict

variable (s : Set α)

/-- The restriction of a continuous function `α → β` to a subset `s` of `α`. -/
def restrict (f : C(α, β)) : C(s, β) where
  toFun := f ∘ ((↑) : s → α)
#align continuous_map.restrict ContinuousMap.restrict

@[simp]
theorem coe_restrict (f : C(α, β)) : ⇑(f.restrict s) = f ∘ ((↑) : s → α) :=
  rfl
#align continuous_map.coe_restrict ContinuousMap.coe_restrict

@[simp]
theorem restrict_apply (f : C(α, β)) (s : Set α) (x : s) : f.restrict s x = f x :=
  rfl
#align continuous_map.restrict_apply ContinuousMap.restrict_apply

@[simp]
theorem restrict_apply_mk (f : C(α, β)) (s : Set α) (x : α) (hx : x ∈ s) :
    f.restrict s ⟨x, hx⟩ = f x :=
  rfl
#align continuous_map.restrict_apply_mk ContinuousMap.restrict_apply_mk

theorem injective_restrict [T2Space β] {s : Set α} (hs : Dense s) :
    Injective (restrict s : C(α, β) → C(s, β)) := fun f g h ↦
  FunLike.ext' <| f.continuous.ext_on hs g.continuous <| Set.restrict_eq_restrict_iff.1 <|
    congr_arg FunLike.coe h

/-- The restriction of a continuous map to the preimage of a set. -/
@[simps]
def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ => f.2.continuousAt.restrictPreimage⟩
#align continuous_map.restrict_preimage ContinuousMap.restrictPreimage

end Restrict

section Gluing

variable {ι : Type*} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : ∀ x : α, ∃ i, S i ∈ nhds x)

/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover : C(α, β) :=
  haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x ↦ (hS x).imp fun _ ↦ mem_of_mem_nhds
  mk (Set.liftCover S (fun i ↦ φ i) hφ H) <| continuous_of_cover_nhds hS fun i ↦ by
    rw [continuousOn_iff_continuous_restrict]
    -- ⊢ Continuous (Set.restrict (S i) (Set.liftCover S (fun i => ↑(φ i)) hφ H))
    simpa only [Set.restrict, Set.liftCover_coe] using (φ i).continuous
    -- 🎉 no goals
#align continuous_map.lift_cover ContinuousMap.liftCover

variable {S φ hφ hS}

@[simp]
theorem liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x := by
  rw [liftCover, coe_mk, Set.liftCover_coe _]
  -- 🎉 no goals
#align continuous_map.lift_cover_coe ContinuousMap.liftCover_coe

-- @[simp] -- Porting note: the simpNF linter complained
theorem liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i := by
  ext
  -- ⊢ ↑(restrict (S i) (liftCover S φ hφ hS)) a✝ = ↑(φ i) a✝
  simp only [coe_restrict, Function.comp_apply, liftCover_coe]
  -- 🎉 no goals
#align continuous_map.lift_cover_restrict ContinuousMap.liftCover_restrict

variable (A : Set (Set α)) (F : ∀ s ∈ A, C(s, β))
  (hF : ∀ (s) (hs : s ∈ A) (t) (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
    F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ nhds x)

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover' : C(α, β) := by
  let S : A → Set α := (↑)
  -- ⊢ C(α, β)
  let F : ∀ i : A, C(i, β) := fun i => F i i.prop
  -- ⊢ C(α, β)
  refine' liftCover S F (fun i j => hF i i.prop j j.prop) _
  -- ⊢ ∀ (x : α), ∃ i, S i ∈ nhds x
  intro x
  -- ⊢ ∃ i, S i ∈ nhds x
  obtain ⟨s, hs, hsx⟩ := hA x
  -- ⊢ ∃ i, S i ∈ nhds x
  exact ⟨⟨s, hs⟩, hsx⟩
  -- 🎉 no goals
#align continuous_map.lift_cover' ContinuousMap.liftCover'

variable {A F hF hA}

-- porting note: did not need `by delta liftCover'; exact` in mathlib3; goal was
-- closed by `liftCover_coe x'`
-- Might be something to do with the `let`s in the definition of `liftCover'`?
@[simp]
theorem liftCover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : ((↑) : A → Set α) ⟨s, hs⟩ := x
  by delta liftCover'; exact liftCover_coe x'
     -- ⊢ ↑(let S := Subtype.val;
                       -- 🎉 no goals
#align continuous_map.lift_cover_coe' ContinuousMap.liftCover_coe'

-- porting note: porting program suggested `ext <| liftCover_coe'`
@[simp]
theorem liftCover_restrict' {s : Set α} {hs : s ∈ A} :
    (liftCover' A F hF hA).restrict s = F s hs := ext <| liftCover_coe' (hF := hF) (hA := hA)
#align continuous_map.lift_cover_restrict' ContinuousMap.liftCover_restrict'

end Gluing

end ContinuousMap

namespace Homeomorph

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

variable (f : α ≃ₜ β) (g : β ≃ₜ γ)

/-- The forward direction of a homeomorphism, as a bundled continuous map. -/
@[simps]
def toContinuousMap (e : α ≃ₜ β) : C(α, β) :=
  ⟨e, e.continuous_toFun⟩
#align homeomorph.to_continuous_map Homeomorph.toContinuousMap
#align homeomorph.to_continuous_map_apply Homeomorph.toContinuousMap_apply

/-- `Homeomorph.toContinuousMap` as a coercion. -/
instance : Coe (α ≃ₜ β) C(α, β) :=
  ⟨Homeomorph.toContinuousMap⟩

-- Porting note: Syntactic tautology
/-theorem toContinuousMap_as_coe : f.toContinuousMap = f :=
  rfl
#align homeomorph.to_continuous_map_as_coe Homeomorph.toContinuousMap_as_coe-/
#noalign homeomorph.to_continuous_map_as_coe

@[simp]
theorem coe_refl : (Homeomorph.refl α : C(α, α)) = ContinuousMap.id α :=
  rfl
#align homeomorph.coe_refl Homeomorph.coe_refl

@[simp]
theorem coe_trans : (f.trans g : C(α, γ)) = (g : C(β, γ)).comp f :=
  rfl
#align homeomorph.coe_trans Homeomorph.coe_trans

/-- Left inverse to a continuous map from a homeomorphism, mirroring `Equiv.symm_comp_self`. -/
@[simp]
theorem symm_comp_toContinuousMap : (f.symm : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α :=
  by rw [← coe_trans, self_trans_symm, coe_refl]
     -- 🎉 no goals
#align homeomorph.symm_comp_to_continuous_map Homeomorph.symm_comp_toContinuousMap

/-- Right inverse to a continuous map from a homeomorphism, mirroring `Equiv.self_comp_symm`. -/
@[simp]
theorem toContinuousMap_comp_symm : (f : C(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β :=
  by rw [← coe_trans, symm_trans_self, coe_refl]
     -- 🎉 no goals
#align homeomorph.to_continuous_map_comp_symm Homeomorph.toContinuousMap_comp_symm

end Homeomorph
