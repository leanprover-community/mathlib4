/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.Homeomorph

#align_import topology.continuous_function.basic from "leanprover-community/mathlib"@"55d771df074d0dd020139ee1cd4b95521422df9f"

/-!
# Continuous bundled maps

In this file we define the type `ContinuousMap` of continuous bundled maps.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.
-/


open Function
open scoped Topology

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
class ContinuousMapClass (F α β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [FunLike F α β] : Prop where
  /-- Continuity -/
  map_continuous (f : F) : Continuous f
#align continuous_map_class ContinuousMapClass

end

export ContinuousMapClass (map_continuous)

attribute [continuity, fun_prop] map_continuous

section ContinuousMapClass

variable {F α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [FunLike F α β]
variable [ContinuousMapClass F α β]

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

instance funLike : FunLike C(α, β) α β where
  coe := ContinuousMap.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance toContinuousMapClass : ContinuousMapClass C(α, β) α β where
  map_continuous := ContinuousMap.continuous_toFun

@[simp]
theorem toFun_eq_coe {f : C(α, β)} : f.toFun = (f : α → β) :=
  rfl
#align continuous_map.to_fun_eq_coe ContinuousMap.toFun_eq_coe

instance : CanLift (α → β) C(α, β) DFunLike.coe Continuous := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- See note [custom simps projection]. -/
def Simps.apply (f : C(α, β)) : α → β := f

-- this must come after the coe_to_fun definition
initialize_simps_projections ContinuousMap (toFun → apply)

@[simp] -- Porting note: removed `norm_cast` attribute
protected theorem coe_coe {F : Type*} [FunLike F α β] [ContinuousMapClass F α β] (f : F) :
    ⇑(f : C(α, β)) = f :=
  rfl
#align continuous_map.coe_coe ContinuousMap.coe_coe

@[ext]
theorem ext {f g : C(α, β)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h
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
  DFunLike.ext' h
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

/-- Deprecated. Use `DFunLike.congr_fun` instead. -/
protected theorem congr_fun {f g : C(α, β)} (H : f = g) (x : α) : f x = g x :=
  H ▸ rfl
#align continuous_map.congr_fun ContinuousMap.congr_fun

/-- Deprecated. Use `DFunLike.congr_arg` instead. -/
protected theorem congr_arg (f : C(α, β)) {x y : α} (h : x = y) : f x = f y :=
  h ▸ rfl
#align continuous_map.congr_arg ContinuousMap.congr_arg

theorem coe_injective : @Function.Injective C(α, β) (α → β) (↑) := fun f g h => by
  cases f; cases g; congr
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
    fun _ => by ext; rfl⟩
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

@[simp]
theorem cancel_right {f₁ f₂ : C(β, γ)} {g : C(α, β)} (hg : Surjective g) :
    f₁.comp g = f₂.comp g ↔ f₁ = f₂ :=
  ⟨fun h => ext <| hg.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (ContinuousMap.comp · g)⟩
#align continuous_map.cancel_right ContinuousMap.cancel_right

@[simp]
theorem cancel_left {f : C(β, γ)} {g₁ g₂ : C(α, β)} (hf : Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => ext fun a => hf <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align continuous_map.cancel_left ContinuousMap.cancel_left

instance [Nonempty α] [Nontrivial β] : Nontrivial C(α, β) :=
  ⟨let ⟨b₁, b₂, hb⟩ := exists_pair_ne β
  ⟨const _ b₁, const _ b₂, fun h => hb <| DFunLike.congr_fun h <| Classical.arbitrary α⟩⟩

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

section Sigma

variable {I A : Type*} {X : I → Type*} [TopologicalSpace A] [∀ i, TopologicalSpace (X i)]

/-- `Sigma.mk i` as a bundled continuous map. -/
@[simps apply]
def sigmaMk (i : I) : C(X i, Σ i, X i) where
  toFun := Sigma.mk i

/--
To give a continuous map out of a disjoint union, it suffices to give a continuous map out of
each term. This is `Sigma.uncurry` for continuous maps.
-/
@[simps]
def sigma (f : ∀ i, C(X i, A)) : C((Σ i, X i), A) where
  toFun ig := f ig.fst ig.snd

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term. This is a version of `Equiv.piCurry` for continuous maps.
-/
@[simps]
def sigmaEquiv : (∀ i, C(X i, A)) ≃ C((Σ i, X i), A) where
  toFun := sigma
  invFun f i := f.comp (sigmaMk i)
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

end Sigma

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

variable (A X) in
/--
Giving a continuous map out of a disjoint union is the same as giving a continuous map out of
each term
-/
@[simps]
def piEquiv : (∀ i, C(A, X i)) ≃ C(A, ∀ i, X i) where
  toFun := pi
  invFun f i := (eval i).comp f
  left_inv := by intro; ext; simp [pi]
  right_inv := by intro; ext; simp [pi]

/-- Combine a collection of bundled continuous maps `C(X i, Y i)` into a bundled continuous map
`C(∀ i, X i, ∀ i, Y i)`. -/
@[simps!]
def piMap (f : ∀ i, C(X i, Y i)) : C((i : I) → X i, (i : I) → Y i) :=
  .pi fun i ↦ (f i).comp (eval i)

/-- "Precomposition" as a continuous map between dependent types. -/
def precomp {ι : Type*} (φ : ι → I) : C((i : I) → X i, (i : ι) → X (φ i)) :=
  ⟨_, Pi.continuous_precomp' φ⟩

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
  DFunLike.ext' <| f.continuous.ext_on hs g.continuous <| Set.restrict_eq_restrict_iff.1 <|
    congr_arg DFunLike.coe h

/-- The restriction of a continuous map to the preimage of a set. -/
@[simps]
def restrictPreimage (f : C(α, β)) (s : Set β) : C(f ⁻¹' s, s) :=
  ⟨s.restrictPreimage f, continuous_iff_continuousAt.mpr fun _ => f.2.continuousAt.restrictPreimage⟩
#align continuous_map.restrict_preimage ContinuousMap.restrictPreimage

end Restrict

section Gluing

variable {ι : Type*} (S : ι → Set α) (φ : ∀ i : ι, C(S i, β))
  (hφ : ∀ (i j) (x : α) (hxi : x ∈ S i) (hxj : x ∈ S j), φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩)
  (hS : ∀ x : α, ∃ i, S i ∈ 𝓝 x)

/-- A family `φ i` of continuous maps `C(S i, β)`, where the domains `S i` contain a neighbourhood
of each point in `α` and the functions `φ i` agree pairwise on intersections, can be glued to
construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover : C(α, β) :=
  haveI H : ⋃ i, S i = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun x ↦ (hS x).imp fun _ ↦ mem_of_mem_nhds
  mk (Set.liftCover S (fun i ↦ φ i) hφ H) <| continuous_of_cover_nhds hS fun i ↦ by
    rw [continuousOn_iff_continuous_restrict]
    simpa (config := { unfoldPartialApp := true }) only [Set.restrict, Set.liftCover_coe] using
      (φ i).continuous
#align continuous_map.lift_cover ContinuousMap.liftCover

variable {S φ hφ hS}

@[simp]
theorem liftCover_coe {i : ι} (x : S i) : liftCover S φ hφ hS x = φ i x := by
  rw [liftCover, coe_mk, Set.liftCover_coe _]
#align continuous_map.lift_cover_coe ContinuousMap.liftCover_coe

-- @[simp] -- Porting note: the simpNF linter complained
theorem liftCover_restrict {i : ι} : (liftCover S φ hφ hS).restrict (S i) = φ i := by
  ext
  simp only [coe_restrict, Function.comp_apply, liftCover_coe]
#align continuous_map.lift_cover_restrict ContinuousMap.liftCover_restrict

variable (A : Set (Set α)) (F : ∀ s ∈ A, C(s, β))
  (hF : ∀ (s) (hs : s ∈ A) (t) (ht : t ∈ A) (x : α) (hxi : x ∈ s) (hxj : x ∈ t),
    F s hs ⟨x, hxi⟩ = F t ht ⟨x, hxj⟩)
  (hA : ∀ x : α, ∃ i ∈ A, i ∈ 𝓝 x)

/-- A family `F s` of continuous maps `C(s, β)`, where (1) the domains `s` are taken from a set `A`
of sets in `α` which contain a neighbourhood of each point in `α` and (2) the functions `F s` agree
pairwise on intersections, can be glued to construct a continuous map in `C(α, β)`. -/
noncomputable def liftCover' : C(α, β) := by
  let S : A → Set α := (↑)
  let F : ∀ i : A, C(i, β) := fun i => F i i.prop
  refine liftCover S F (fun i j => hF i i.prop j j.prop) ?_
  intro x
  obtain ⟨s, hs, hsx⟩ := hA x
  exact ⟨⟨s, hs⟩, hsx⟩
#align continuous_map.lift_cover' ContinuousMap.liftCover'

variable {A F hF hA}

-- Porting note: did not need `by delta liftCover'; exact` in mathlib3; goal was
-- closed by `liftCover_coe x'`
-- Might be something to do with the `let`s in the definition of `liftCover'`?
@[simp]
theorem liftCover_coe' {s : Set α} {hs : s ∈ A} (x : s) : liftCover' A F hF hA x = F s hs x :=
  let x' : ((↑) : A → Set α) ⟨s, hs⟩ := x
  by delta liftCover'; exact liftCover_coe x'
#align continuous_map.lift_cover_coe' ContinuousMap.liftCover_coe'

-- Porting note: porting program suggested `ext <| liftCover_coe'`
@[simp]
theorem liftCover_restrict' {s : Set α} {hs : s ∈ A} :
    (liftCover' A F hF hA).restrict s = F s hs := ext <| liftCover_coe' (hF := hF) (hA := hA)
#align continuous_map.lift_cover_restrict' ContinuousMap.liftCover_restrict'

end Gluing

end ContinuousMap

section Lift

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : C(X, Y)}

/-- `Setoid.quotientKerEquivOfRightInverse` as a homeomorphism. -/
@[simps!]
def Function.RightInverse.homeomorph {f' : C(Y, X)} (hf : Function.RightInverse f' f) :
    Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfRightInverse _ _ hf
  continuous_toFun := quotientMap_quot_mk.continuous_iff.mpr f.continuous
  continuous_invFun := continuous_quotient_mk'.comp f'.continuous

namespace QuotientMap

/--
The homeomorphism from the quotient of a quotient map to its codomain. This is
`Setoid.quotientKerEquivOfSurjective` as a homeomorphism.
-/
@[simps!]
noncomputable def homeomorph (hf : QuotientMap f) : Quotient (Setoid.ker f) ≃ₜ Y where
  toEquiv := Setoid.quotientKerEquivOfSurjective _ hf.surjective
  continuous_toFun := quotientMap_quot_mk.continuous_iff.mpr hf.continuous
  continuous_invFun := by
    rw [hf.continuous_iff]
    convert continuous_quotient_mk'
    ext
    simp only [Equiv.invFun_as_coe, Function.comp_apply,
      (Setoid.quotientKerEquivOfSurjective f hf.surjective).symm_apply_eq]
    rfl

variable (hf : QuotientMap f) (g : C(X, Z)) (h : Function.FactorsThrough g f)

/-- Descend a continuous map, which is constant on the fibres, along a quotient map. -/
@[simps]
noncomputable def lift : C(Y, Z) where
  toFun := ((fun i ↦ Quotient.liftOn' i g (fun _ _ (hab : f _ = f _) ↦ h hab)) :
    Quotient (Setoid.ker f) → Z) ∘ hf.homeomorph.symm
  continuous_toFun := Continuous.comp (continuous_quot_lift _ g.2) (Homeomorph.continuous _)

/--
The obvious triangle induced by `QuotientMap.lift` commutes:
```
     g
  X --→ Z
  |   ↗
f |  / hf.lift g h
  v /
  Y
```
-/
@[simp]
theorem lift_comp : (hf.lift g h).comp f = g := by
  ext
  simpa using h (Function.rightInverse_surjInv _ _)

/-- `QuotientMap.lift` as an equivalence. -/
@[simps]
noncomputable def liftEquiv : { g : C(X, Z) // Function.FactorsThrough g f} ≃ C(Y, Z) where
  toFun g := hf.lift g g.prop
  invFun g := ⟨g.comp f, fun _ _ h ↦ by simp only [ContinuousMap.comp_apply]; rw [h]⟩
  left_inv := by intro; simp
  right_inv := by
    intro g
    ext a
    simpa using congrArg g (Function.rightInverse_surjInv hf.surjective a)

end QuotientMap

end Lift

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
/- theorem toContinuousMap_as_coe : f.toContinuousMap = f :=
  rfl
-/
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
theorem symm_comp_toContinuousMap :
    (f.symm : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α := by
  rw [← coe_trans, self_trans_symm, coe_refl]
#align homeomorph.symm_comp_to_continuous_map Homeomorph.symm_comp_toContinuousMap

/-- Right inverse to a continuous map from a homeomorphism, mirroring `Equiv.self_comp_symm`. -/
@[simp]
theorem toContinuousMap_comp_symm :
    (f : C(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β := by
  rw [← coe_trans, symm_trans_self, coe_refl]
#align homeomorph.to_continuous_map_comp_symm Homeomorph.toContinuousMap_comp_symm

end Homeomorph
