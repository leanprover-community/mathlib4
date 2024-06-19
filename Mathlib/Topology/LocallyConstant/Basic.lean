/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Sets.Closeds

#align_import topology.locally_constant.basic from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `IsLocallyConstant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `LocallyConstant X Y` : the type of locally constant maps from `X` to `Y`
* `LocallyConstant.map` : push-forward of locally constant maps
* `LocallyConstant.comap` : pull-back of locally constant maps

-/


variable {X Y Z α : Type*} [TopologicalSpace X]

open Set Filter

open Topology

/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
def IsLocallyConstant (f : X → Y) : Prop :=
  ∀ s : Set Y, IsOpen (f ⁻¹' s)
#align is_locally_constant IsLocallyConstant

namespace IsLocallyConstant

open List in
protected theorem tfae (f : X → Y) :
    TFAE [IsLocallyConstant f,
      ∀ x, ∀ᶠ x' in 𝓝 x, f x' = f x,
      ∀ x, IsOpen { x' | f x' = f x },
      ∀ y, IsOpen (f ⁻¹' {y}),
      ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x] := by
  tfae_have 1 → 4
  · exact fun h y => h {y}
  tfae_have 4 → 3
  · exact fun h x => h (f x)
  tfae_have 3 → 2
  · exact fun h x => IsOpen.mem_nhds (h x) rfl
  tfae_have 2 → 5
  · intro h x
    rcases mem_nhds_iff.1 (h x) with ⟨U, eq, hU, hx⟩
    exact ⟨U, hU, hx, eq⟩
  tfae_have 5 → 1
  · intro h s
    refine isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_
    rcases h x with ⟨U, hU, hxU, eq⟩
    exact ⟨U, fun x' hx' => mem_preimage.2 <| (eq x' hx').symm ▸ hx, hU, hxU⟩
  tfae_finish
#align is_locally_constant.tfae IsLocallyConstant.tfae

@[nontriviality]
theorem of_discrete [DiscreteTopology X] (f : X → Y) : IsLocallyConstant f := fun _ =>
  isOpen_discrete _
#align is_locally_constant.of_discrete IsLocallyConstant.of_discrete

theorem isOpen_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsOpen { x | f x = y } :=
  hf {y}
#align is_locally_constant.is_open_fiber IsLocallyConstant.isOpen_fiber

theorem isClosed_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClosed { x | f x = y } :=
  ⟨hf {y}ᶜ⟩
#align is_locally_constant.is_closed_fiber IsLocallyConstant.isClosed_fiber

theorem isClopen_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClopen { x | f x = y } :=
  ⟨isClosed_fiber hf _,  isOpen_fiber hf _⟩
#align is_locally_constant.is_clopen_fiber IsLocallyConstant.isClopen_fiber

theorem iff_exists_open (f : X → Y) :
    IsLocallyConstant f ↔ ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x :=
  (IsLocallyConstant.tfae f).out 0 4
#align is_locally_constant.iff_exists_open IsLocallyConstant.iff_exists_open

theorem iff_eventually_eq (f : X → Y) : IsLocallyConstant f ↔ ∀ x, ∀ᶠ y in 𝓝 x, f y = f x :=
  (IsLocallyConstant.tfae f).out 0 1
#align is_locally_constant.iff_eventually_eq IsLocallyConstant.iff_eventually_eq

theorem exists_open {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ x' ∈ U, f x' = f x :=
  (iff_exists_open f).1 hf x
#align is_locally_constant.exists_open IsLocallyConstant.exists_open

protected theorem eventually_eq {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    ∀ᶠ y in 𝓝 x, f y = f x :=
  (iff_eventually_eq f).1 hf x
#align is_locally_constant.eventually_eq IsLocallyConstant.eventually_eq

-- Porting note (#10756): new lemma
theorem iff_isOpen_fiber_apply {f : X → Y} : IsLocallyConstant f ↔ ∀ x, IsOpen (f ⁻¹' {f x}) :=
  (IsLocallyConstant.tfae f).out 0 2

-- Porting note (#10756): new lemma
theorem iff_isOpen_fiber {f : X → Y} : IsLocallyConstant f ↔ ∀ y, IsOpen (f ⁻¹' {y}) :=
  (IsLocallyConstant.tfae f).out 0 3

protected theorem continuous [TopologicalSpace Y] {f : X → Y} (hf : IsLocallyConstant f) :
    Continuous f :=
  ⟨fun _ _ => hf _⟩
#align is_locally_constant.continuous IsLocallyConstant.continuous

theorem iff_continuous {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X → Y) :
    IsLocallyConstant f ↔ Continuous f :=
  ⟨IsLocallyConstant.continuous, fun h s => h.isOpen_preimage s (isOpen_discrete _)⟩
#align is_locally_constant.iff_continuous IsLocallyConstant.iff_continuous

theorem of_constant (f : X → Y) (h : ∀ x y, f x = f y) : IsLocallyConstant f :=
  (iff_eventually_eq f).2 fun _ => eventually_of_forall fun _ => h _ _
#align is_locally_constant.of_constant IsLocallyConstant.of_constant

protected theorem const (y : Y) : IsLocallyConstant (Function.const X y) :=
  of_constant _ fun _ _ => rfl
#align is_locally_constant.const IsLocallyConstant.const

protected theorem comp {f : X → Y} (hf : IsLocallyConstant f) (g : Y → Z) :
    IsLocallyConstant (g ∘ f) := fun s => by
  rw [Set.preimage_comp]
  exact hf _
#align is_locally_constant.comp IsLocallyConstant.comp

theorem prod_mk {Y'} {f : X → Y} {f' : X → Y'} (hf : IsLocallyConstant f)
    (hf' : IsLocallyConstant f') : IsLocallyConstant fun x => (f x, f' x) :=
  (iff_eventually_eq _).2 fun x =>
    (hf.eventually_eq x).mp <| (hf'.eventually_eq x).mono fun _ hf' hf => Prod.ext hf hf'
#align is_locally_constant.prod_mk IsLocallyConstant.prod_mk

theorem comp₂ {Y₁ Y₂ Z : Type*} {f : X → Y₁} {g : X → Y₂} (hf : IsLocallyConstant f)
    (hg : IsLocallyConstant g) (h : Y₁ → Y₂ → Z) : IsLocallyConstant fun x => h (f x) (g x) :=
  (hf.prod_mk hg).comp fun x : Y₁ × Y₂ => h x.1 x.2
#align is_locally_constant.comp₂ IsLocallyConstant.comp₂

theorem comp_continuous [TopologicalSpace Y] {g : Y → Z} {f : X → Y} (hg : IsLocallyConstant g)
    (hf : Continuous f) : IsLocallyConstant (g ∘ f) := fun s => by
  rw [Set.preimage_comp]
  exact hf.isOpen_preimage _ (hg _)
#align is_locally_constant.comp_continuous IsLocallyConstant.comp_continuous

/-- A locally constant function is constant on any preconnected set. -/
theorem apply_eq_of_isPreconnected {f : X → Y} (hf : IsLocallyConstant f) {s : Set X}
    (hs : IsPreconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  let U := f ⁻¹' {f y}
  suffices x ∉ Uᶜ from Classical.not_not.1 this
  intro hxV
  specialize hs U Uᶜ (hf {f y}) (hf {f y}ᶜ) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩
  · simp only [union_compl_self, subset_univ]
  · simp only [inter_empty, Set.not_nonempty_empty, inter_compl_self] at hs
#align is_locally_constant.apply_eq_of_is_preconnected IsLocallyConstant.apply_eq_of_isPreconnected

theorem apply_eq_of_preconnectedSpace [PreconnectedSpace X] {f : X → Y} (hf : IsLocallyConstant f)
    (x y : X) : f x = f y :=
  hf.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
#align is_locally_constant.apply_eq_of_preconnected_space IsLocallyConstant.apply_eq_of_preconnectedSpace

theorem eq_const [PreconnectedSpace X] {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    f = Function.const X (f x) :=
  funext fun y => hf.apply_eq_of_preconnectedSpace y x
#align is_locally_constant.eq_const IsLocallyConstant.eq_const

theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] {f : X → Y} (hf : IsLocallyConstant f) :
    ∃ y, f = Function.const X y := by
  cases' isEmpty_or_nonempty X with h h
  · exact ⟨Classical.arbitrary Y, funext <| h.elim⟩
  · exact ⟨f (Classical.arbitrary X), hf.eq_const _⟩
#align is_locally_constant.exists_eq_const IsLocallyConstant.exists_eq_const

theorem iff_is_const [PreconnectedSpace X] {f : X → Y} : IsLocallyConstant f ↔ ∀ x y, f x = f y :=
  ⟨fun h _ _ => h.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial, of_constant _⟩
#align is_locally_constant.iff_is_const IsLocallyConstant.iff_is_const

theorem range_finite [CompactSpace X] {f : X → Y} (hf : IsLocallyConstant f) :
    (Set.range f).Finite := by
  letI : TopologicalSpace Y := ⊥; haveI := discreteTopology_bot Y
  exact (isCompact_range hf.continuous).finite_of_discrete
#align is_locally_constant.range_finite IsLocallyConstant.range_finite

@[to_additive]
theorem one [One Y] : IsLocallyConstant (1 : X → Y) := IsLocallyConstant.const 1
#align is_locally_constant.one IsLocallyConstant.one
#align is_locally_constant.zero IsLocallyConstant.zero

@[to_additive]
theorem inv [Inv Y] ⦃f : X → Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant f⁻¹ :=
  hf.comp fun x => x⁻¹
#align is_locally_constant.inv IsLocallyConstant.inv
#align is_locally_constant.neg IsLocallyConstant.neg

@[to_additive]
theorem mul [Mul Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (f * g) :=
  hf.comp₂ hg (· * ·)
#align is_locally_constant.mul IsLocallyConstant.mul
#align is_locally_constant.add IsLocallyConstant.add

@[to_additive]
theorem div [Div Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) :
    IsLocallyConstant (f / g) :=
  hf.comp₂ hg (· / ·)
#align is_locally_constant.div IsLocallyConstant.div
#align is_locally_constant.sub IsLocallyConstant.sub

/-- If a composition of a function `f` followed by an injection `g` is locally
constant, then the locally constant property descends to `f`. -/
theorem desc {α β : Type*} (f : X → α) (g : α → β) (h : IsLocallyConstant (g ∘ f))
    (inj : Function.Injective g) : IsLocallyConstant f := fun s => by
  rw [← preimage_image_eq s inj, preimage_preimage]
  exact h (g '' s)
#align is_locally_constant.desc IsLocallyConstant.desc

theorem of_constant_on_connected_components [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ x, ∀ y ∈ connectedComponent x, f y = f x) : IsLocallyConstant f :=
  (iff_exists_open _).2 fun x =>
    ⟨connectedComponent x, isOpen_connectedComponent, mem_connectedComponent, h x⟩
#align is_locally_constant.of_constant_on_connected_components IsLocallyConstant.of_constant_on_connected_components

theorem of_constant_on_connected_clopens [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ U : Set X, IsConnected U → IsClopen U → ∀ x ∈ U, ∀ y ∈ U, f y = f x) :
    IsLocallyConstant f :=
  of_constant_on_connected_components fun x =>
    h (connectedComponent x) isConnected_connectedComponent isClopen_connectedComponent x
      mem_connectedComponent

theorem of_constant_on_preconnected_clopens [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ U : Set X, IsPreconnected U → IsClopen U → ∀ x ∈ U, ∀ y ∈ U, f y = f x) :
    IsLocallyConstant f :=
  of_constant_on_connected_clopens fun U hU ↦ h U hU.isPreconnected
#align is_locally_constant.of_constant_on_preconnected_clopens IsLocallyConstant.of_constant_on_preconnected_clopens

end IsLocallyConstant

/-- A (bundled) locally constant function from a topological space `X` to a type `Y`. -/
structure LocallyConstant (X Y : Type*) [TopologicalSpace X] where
  /-- The underlying function. -/
  protected toFun : X → Y
  /-- The map is locally constant. -/
  protected isLocallyConstant : IsLocallyConstant toFun
#align locally_constant LocallyConstant

namespace LocallyConstant

instance [Inhabited Y] : Inhabited (LocallyConstant X Y) :=
  ⟨⟨_, IsLocallyConstant.const default⟩⟩

instance : FunLike (LocallyConstant X Y) X Y where
  coe := LocallyConstant.toFun
  coe_injective' := by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

/-- See Note [custom simps projections]. -/
def Simps.apply (f : LocallyConstant X Y) : X → Y := f

initialize_simps_projections LocallyConstant (toFun → apply)

@[simp]
theorem toFun_eq_coe (f : LocallyConstant X Y) : f.toFun = f :=
  rfl
#align locally_constant.to_fun_eq_coe LocallyConstant.toFun_eq_coe

@[simp]
theorem coe_mk (f : X → Y) (h) : ⇑(⟨f, h⟩ : LocallyConstant X Y) = f :=
  rfl
#align locally_constant.coe_mk LocallyConstant.coe_mk

theorem congr_fun {f g : LocallyConstant X Y} (h : f = g) (x : X) : f x = g x :=
  DFunLike.congr_fun h x
#align locally_constant.congr_fun LocallyConstant.congr_fun

theorem congr_arg (f : LocallyConstant X Y) {x y : X} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h
#align locally_constant.congr_arg LocallyConstant.congr_arg

theorem coe_injective : @Function.Injective (LocallyConstant X Y) (X → Y) (↑) := fun _ _ =>
  DFunLike.ext'
#align locally_constant.coe_injective LocallyConstant.coe_injective

@[norm_cast]
theorem coe_inj {f g : LocallyConstant X Y} : (f : X → Y) = g ↔ f = g :=
  coe_injective.eq_iff
#align locally_constant.coe_inj LocallyConstant.coe_inj

@[ext]
theorem ext ⦃f g : LocallyConstant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h
#align locally_constant.ext LocallyConstant.ext

theorem ext_iff {f g : LocallyConstant X Y} : f = g ↔ ∀ x, f x = g x := DFunLike.ext_iff
#align locally_constant.ext_iff LocallyConstant.ext_iff

section CodomainTopologicalSpace

variable [TopologicalSpace Y] (f : LocallyConstant X Y)

protected theorem continuous : Continuous f :=
  f.isLocallyConstant.continuous
#align locally_constant.continuous LocallyConstant.continuous

/-- We can turn a locally-constant function into a bundled `ContinuousMap`. -/
@[coe] def toContinuousMap : C(X, Y) :=
  ⟨f, f.continuous⟩
#align locally_constant.to_continuous_map LocallyConstant.toContinuousMap

/-- As a shorthand, `LocallyConstant.toContinuousMap` is available as a coercion -/
instance : Coe (LocallyConstant X Y) C(X, Y) := ⟨toContinuousMap⟩

-- Porting note: became a syntactic `rfl`
#noalign locally_constant.to_continuous_map_eq_coe

@[simp] theorem coe_continuousMap : ((f : C(X, Y)) : X → Y) = (f : X → Y) := rfl
#align locally_constant.coe_continuous_map LocallyConstant.coe_continuousMap

theorem toContinuousMap_injective :
    Function.Injective (toContinuousMap : LocallyConstant X Y → C(X, Y)) := fun _ _ h =>
  ext (ContinuousMap.congr_fun h)
#align locally_constant.to_continuous_map_injective LocallyConstant.toContinuousMap_injective

end CodomainTopologicalSpace

/-- The constant locally constant function on `X` with value `y : Y`. -/
def const (X : Type*) {Y : Type*} [TopologicalSpace X] (y : Y) : LocallyConstant X Y :=
  ⟨Function.const X y, IsLocallyConstant.const _⟩
#align locally_constant.const LocallyConstant.const

@[simp]
theorem coe_const (y : Y) : (const X y : X → Y) = Function.const X y :=
  rfl
#align locally_constant.coe_const LocallyConstant.coe_const

/-- The locally constant function to `Fin 2` associated to a clopen set. -/
def ofIsClopen {X : Type*} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : LocallyConstant X (Fin 2) where
  toFun x := if x ∈ U then 0 else 1
  isLocallyConstant := by
    refine IsLocallyConstant.iff_isOpen_fiber.2 <| Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · convert hU.2 using 1
      ext
      simp only [mem_singleton_iff, Fin.one_eq_zero_iff, mem_preimage, ite_eq_left_iff,
        Nat.succ_succ_ne_one]
      tauto
    · rw [← isClosed_compl_iff]
      convert hU.1
      ext
      simp
#align locally_constant.of_clopen LocallyConstant.ofIsClopen

@[simp]
theorem ofIsClopen_fiber_zero {X : Type*} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : ofIsClopen hU ⁻¹' ({0} : Set (Fin 2)) = U := by
  ext
  simp only [ofIsClopen, mem_singleton_iff, Fin.one_eq_zero_iff, coe_mk, mem_preimage,
    ite_eq_left_iff, Nat.succ_succ_ne_one]
  tauto
#align locally_constant.of_clopen_fiber_zero LocallyConstant.ofIsClopen_fiber_zero

@[simp]
theorem ofIsClopen_fiber_one {X : Type*} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)]
    (hU : IsClopen U) : ofIsClopen hU ⁻¹' ({1} : Set (Fin 2)) = Uᶜ := by
  ext
  simp only [ofIsClopen, mem_singleton_iff, coe_mk, Fin.zero_eq_one_iff, mem_preimage,
    ite_eq_right_iff, mem_compl_iff, Nat.succ_succ_ne_one]
#align locally_constant.of_clopen_fiber_one LocallyConstant.ofIsClopen_fiber_one

theorem locallyConstant_eq_of_fiber_zero_eq {X : Type*} [TopologicalSpace X]
    (f g : LocallyConstant X (Fin 2)) (h : f ⁻¹' ({0} : Set (Fin 2)) = g ⁻¹' {0}) : f = g := by
  simp only [Set.ext_iff, mem_singleton_iff, mem_preimage] at h
  ext1 x
  exact Fin.fin_two_eq_of_eq_zero_iff (h x)
#align locally_constant.locally_constant_eq_of_fiber_zero_eq LocallyConstant.locallyConstant_eq_of_fiber_zero_eq

theorem range_finite [CompactSpace X] (f : LocallyConstant X Y) : (Set.range f).Finite :=
  f.isLocallyConstant.range_finite
#align locally_constant.range_finite LocallyConstant.range_finite

theorem apply_eq_of_isPreconnected (f : LocallyConstant X Y) {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  f.isLocallyConstant.apply_eq_of_isPreconnected hs hx hy
#align locally_constant.apply_eq_of_is_preconnected LocallyConstant.apply_eq_of_isPreconnected

theorem apply_eq_of_preconnectedSpace [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X) :
    f x = f y :=
  f.isLocallyConstant.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial
#align locally_constant.apply_eq_of_preconnected_space LocallyConstant.apply_eq_of_preconnectedSpace

theorem eq_const [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X) : f = const X (f x) :=
  ext fun _ => apply_eq_of_preconnectedSpace f _ _
#align locally_constant.eq_const LocallyConstant.eq_const

theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X Y) :
    ∃ y, f = const X y := by
  rcases Classical.em (Nonempty X) with (⟨⟨x⟩⟩ | hX)
  · exact ⟨f x, f.eq_const x⟩
  · exact ⟨Classical.arbitrary Y, ext fun x => (hX ⟨x⟩).elim⟩
#align locally_constant.exists_eq_const LocallyConstant.exists_eq_const

/-- Push forward of locally constant maps under any map, by post-composition. -/
def map (f : Y → Z) (g : LocallyConstant X Y) : LocallyConstant X Z :=
  ⟨f ∘ g, g.isLocallyConstant.comp f⟩
#align locally_constant.map LocallyConstant.map

@[simp]
theorem map_apply (f : Y → Z) (g : LocallyConstant X Y) : ⇑(map f g) = f ∘ g :=
  rfl
#align locally_constant.map_apply LocallyConstant.map_apply

@[simp]
theorem map_id : @map X Y Y _ id = id := rfl
#align locally_constant.map_id LocallyConstant.map_id

@[simp]
theorem map_comp {Y₁ Y₂ Y₃ : Type*} (g : Y₂ → Y₃) (f : Y₁ → Y₂) :
    @map X _ _ _ g ∘ map f = map (g ∘ f) := rfl
#align locally_constant.map_comp LocallyConstant.map_comp

/-- Given a locally constant function to `α → β`, construct a family of locally constant
functions with values in β indexed by α. -/
def flip {X α β : Type*} [TopologicalSpace X] (f : LocallyConstant X (α → β)) (a : α) :
    LocallyConstant X β :=
  f.map fun f => f a
#align locally_constant.flip LocallyConstant.flip

/-- If α is finite, this constructs a locally constant function to `α → β` given a
family of locally constant functions with values in β indexed by α. -/
def unflip {X α β : Type*} [Finite α] [TopologicalSpace X] (f : α → LocallyConstant X β) :
    LocallyConstant X (α → β) where
  toFun x a := f a x
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.2 fun g => by
    have : (fun (x : X) (a : α) => f a x) ⁻¹' {g} = ⋂ a : α, f a ⁻¹' {g a} := by
      ext; simp [Function.funext_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun a => (f a).isLocallyConstant _
#align locally_constant.unflip LocallyConstant.unflip

@[simp]
theorem unflip_flip {X α β : Type*} [Finite α] [TopologicalSpace X]
    (f : LocallyConstant X (α → β)) : unflip f.flip = f := rfl
#align locally_constant.unflip_flip LocallyConstant.unflip_flip

@[simp]
theorem flip_unflip {X α β : Type*} [Finite α] [TopologicalSpace X]
    (f : α → LocallyConstant X β) : (unflip f).flip = f := rfl
#align locally_constant.flip_unflip LocallyConstant.flip_unflip

section Comap

variable [TopologicalSpace Y]

/-- Pull back of locally constant maps under a continuous map, by pre-composition. -/
def comap (f : C(X, Y)) (g : LocallyConstant Y Z) : LocallyConstant X Z :=
  ⟨g ∘ f, g.isLocallyConstant.comp_continuous f.continuous⟩
#align locally_constant.comap LocallyConstant.comap

@[simp]
theorem coe_comap (f : C(X, Y)) (g : LocallyConstant Y Z) :
    (comap f g) = g ∘ f := rfl
#align locally_constant.coe_comap LocallyConstant.coe_comap

theorem coe_comap_apply (f : C(X, Y)) (g : LocallyConstant Y Z) (x : X) :
    comap f g x = g (f x) := rfl

@[simp]
theorem comap_id : comap (@ContinuousMap.id X _) = @id (LocallyConstant X Z) := rfl
#align locally_constant.comap_id LocallyConstant.comap_id

theorem comap_comp {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y)) :
    comap (Z := Z) (g.comp f) = comap f ∘ comap g := rfl
#align locally_constant.comap_comp LocallyConstant.comap_comp

theorem comap_comap {W : Type*} [TopologicalSpace W] (f : C(W, X)) (g : C(X, Y))
    (x : LocallyConstant Y Z) : comap f (comap g x) = comap (g.comp f) x := rfl

theorem comap_const (f : C(X, Y)) (y : Y) (h : ∀ x, f x = y) :
    (comap f : LocallyConstant Y Z → LocallyConstant X Z) = fun g => const X (g y) := by
  ext; simp [h]
#align locally_constant.comap_const LocallyConstant.comap_const

lemma comap_injective (f : C(X, Y)) (hfs : f.1.Surjective) :
    (comap (Z := Z) f).Injective := by
  intro a b h
  ext y
  obtain ⟨x, hx⟩ := hfs y
  simpa [← hx] using LocallyConstant.congr_fun h x

end Comap

section Desc

/-- If a locally constant function factors through an injection, then it factors through a locally
constant function. -/
def desc {X α β : Type*} [TopologicalSpace X] {g : α → β} (f : X → α) (h : LocallyConstant X β)
    (cond : g ∘ f = h) (inj : Function.Injective g) : LocallyConstant X α where
  toFun := f
  isLocallyConstant := IsLocallyConstant.desc _ g (cond.symm ▸ h.isLocallyConstant) inj
#align locally_constant.desc LocallyConstant.desc

@[simp]
theorem coe_desc {X α β : Type*} [TopologicalSpace X] (f : X → α) (g : α → β)
    (h : LocallyConstant X β) (cond : g ∘ f = h) (inj : Function.Injective g) :
    ⇑(desc f h cond inj) = f :=
  rfl
#align locally_constant.coe_desc LocallyConstant.coe_desc

end Desc

section Indicator

variable {R : Type*} [One R] {U : Set X} (f : LocallyConstant X R)

open scoped Classical

/-- Given a clopen set `U` and a locally constant function `f`, `LocallyConstant.mulIndicator`
  returns the locally constant function that is `f` on `U` and `1` otherwise. -/
@[to_additive (attr := simps) "Given a clopen set `U` and a locally constant function `f`,
  `LocallyConstant.indicator` returns the locally constant function that is `f` on `U` and `0`
  otherwise. "]
noncomputable def mulIndicator (hU : IsClopen U) : LocallyConstant X R where
  toFun := Set.mulIndicator U f
  isLocallyConstant := fun s => by
    rw [mulIndicator_preimage, Set.ite, Set.diff_eq]
    exact ((f.2 s).inter hU.isOpen).union ((IsLocallyConstant.const 1 s).inter hU.compl.isOpen)
#align locally_constant.mul_indicator LocallyConstant.mulIndicator
#align locally_constant.indicator LocallyConstant.indicator

variable (a : X)

@[to_additive]
theorem mulIndicator_apply_eq_if (hU : IsClopen U) :
    mulIndicator f hU a = if a ∈ U then f a else 1 :=
  Set.mulIndicator_apply U f a
#align locally_constant.mul_indicator_apply_eq_if LocallyConstant.mulIndicator_apply_eq_if
#align locally_constant.indicator_apply_eq_if LocallyConstant.indicator_apply_eq_if

variable {a}

@[to_additive]
theorem mulIndicator_of_mem (hU : IsClopen U) (h : a ∈ U) : f.mulIndicator hU a = f a :=
  Set.mulIndicator_of_mem h _
#align locally_constant.mul_indicator_of_mem LocallyConstant.mulIndicator_of_mem
#align locally_constant.indicator_of_mem LocallyConstant.indicator_of_mem

@[to_additive]
theorem mulIndicator_of_not_mem (hU : IsClopen U) (h : a ∉ U) : f.mulIndicator hU a = 1 :=
  Set.mulIndicator_of_not_mem h _
#align locally_constant.mul_indicator_of_not_mem LocallyConstant.mulIndicator_of_not_mem
#align locally_constant.indicator_of_not_mem LocallyConstant.indicator_of_not_mem

end Indicator

section Equiv

/--
The equivalence between `LocallyConstant X Z` and `LocallyConstant Y Z` given a
homeomorphism `X ≃ₜ Y`
-/
@[simps]
def congrLeft [TopologicalSpace Y] (e : X ≃ₜ Y) : LocallyConstant X Z ≃ LocallyConstant Y Z where
  toFun := comap e.symm
  invFun := comap e
  left_inv := by
    intro
    simp [comap_comap]
  right_inv := by
    intro
    simp [comap_comap]

/--
The equivalence between `LocallyConstant X Y` and `LocallyConstant X Z` given an
equivalence `Y ≃ Z`
-/
@[simps]
def congrRight (e : Y ≃ Z) : LocallyConstant X Y ≃ LocallyConstant X Z where
  toFun := map e
  invFun := map e.symm
  left_inv := by intro; ext; simp
  right_inv := by intro; ext; simp

variable (X) in
/--
The set of clopen subsets of a topological space is equivalent to the locally constant maps to
a two-element set
-/
def equivClopens [∀ (s : Set X) x, Decidable (x ∈ s)] :
    LocallyConstant X (Fin 2) ≃ TopologicalSpace.Clopens X where
  toFun f := ⟨f ⁻¹' {0}, f.2.isClopen_fiber _⟩
  invFun s := ofIsClopen s.2
  left_inv _ := locallyConstant_eq_of_fiber_zero_eq _ _ (by simp)
  right_inv _ := by simp

end Equiv

section Piecewise

/-- Given two closed sets covering a topological space, and locally constant maps on these two sets,
    then if these two locally constant maps agree on the intersection, we get a piecewise defined
    locally constant map on the whole space.

TODO: Generalise this construction to `ContinuousMap`. -/
def piecewise {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂) (h : C₁ ∪ C₂ = Set.univ)
    (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· ∈ C₁)] : LocallyConstant X Z where
  toFun i := if hi : i ∈ C₁ then f ⟨i, hi⟩ else g ⟨i, (Set.compl_subset_iff_union.mpr h) hi⟩
  isLocallyConstant := by
    let dZ : TopologicalSpace Z := ⊥
    haveI : DiscreteTopology Z := discreteTopology_bot Z
    obtain ⟨f, hf⟩ := f
    obtain ⟨g, hg⟩ := g
    rw [IsLocallyConstant.iff_continuous] at hf hg ⊢
    dsimp only [coe_mk]
    rw [Set.union_eq_iUnion] at h
    refine (locallyFinite_of_finite _).continuous h (fun i ↦ ?_) (fun i ↦ ?_)
    · cases i <;> [exact h₂; exact h₁]
    · cases i <;> rw [continuousOn_iff_continuous_restrict]
      · convert hg
        ext x
        simp only [cond_false, restrict_apply, Subtype.coe_eta, dite_eq_right_iff]
        exact fun hx ↦ hfg x ⟨hx, x.prop⟩
      · simp only [cond_true, restrict_dite, Subtype.coe_eta]
        exact hf

@[simp]
lemma piecewise_apply_left {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· ∈ C₁)] (x : X) (hx : x ∈ C₁) :
    piecewise h₁ h₂ h f g hfg x = f ⟨x, hx⟩ := by
  simp only [piecewise, Set.mem_preimage, continuous_subtype_val.restrictPreimage,
    coe_comap, Function.comp_apply, coe_mk]
  rw [dif_pos hx]

@[simp]
lemma piecewise_apply_right {C₁ C₂ : Set X} (h₁ : IsClosed C₁) (h₂ : IsClosed C₂)
    (h : C₁ ∪ C₂ = Set.univ) (f : LocallyConstant C₁ Z) (g : LocallyConstant C₂ Z)
    (hfg : ∀ (x : X) (hx : x ∈ C₁ ∩ C₂), f ⟨x, hx.1⟩ = g ⟨x, hx.2⟩)
    [DecidablePred (· ∈ C₁)] (x : X) (hx : x ∈ C₂) :
    piecewise h₁ h₂ h f g hfg x = g ⟨x, hx⟩ := by
  simp only [piecewise, Set.mem_preimage, continuous_subtype_val.restrictPreimage,
    coe_comap, Function.comp_apply, coe_mk]
  split_ifs with h
  · exact hfg x ⟨h, hx⟩
  · rfl

/-- A variant of `LocallyConstant.piecewise` where the two closed sets cover a subset.

TODO: Generalise this construction to `ContinuousMap`. -/
def piecewise' {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· ∈ C₁)] (hf : ∀ x (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩) :
    LocallyConstant C₀ Z :=
  letI : ∀ j : C₀, Decidable (j ∈ Subtype.val ⁻¹' C₁) := fun j ↦ decidable_of_iff (↑j ∈ C₁) Iff.rfl
  piecewise (h₁.preimage continuous_subtype_val) (h₂.preimage continuous_subtype_val)
    (by simpa [eq_univ_iff_forall] using h₀)
    (f₁.comap ⟨(restrictPreimage C₁ ((↑) : C₀ → X)), continuous_subtype_val.restrictPreimage⟩)
    (f₂.comap ⟨(restrictPreimage C₂ ((↑) : C₀ → X)), continuous_subtype_val.restrictPreimage⟩) <| by
      rintro ⟨x, hx₀⟩ ⟨hx₁ : x ∈ C₁, hx₂ : x ∈ C₂⟩
      simpa using hf x ⟨hx₁, hx₂⟩

@[simp]
lemma piecewise'_apply_left {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· ∈ C₁)] (hf : ∀ x (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩)
    (x : C₀) (hx : x.val ∈ C₁) :
    piecewise' h₀ h₁ h₂ f₁ f₂ hf x = f₁ ⟨x.val, hx⟩ := by
  letI : ∀ j : C₀, Decidable (j ∈ Subtype.val ⁻¹' C₁) := fun j ↦ decidable_of_iff (↑j ∈ C₁) Iff.rfl
  rw [piecewise', piecewise_apply_left (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ → X)), continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

@[simp]
lemma piecewise'_apply_right {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed C₁)
    (h₂ : IsClosed C₂) (f₁ : LocallyConstant C₁ Z) (f₂ : LocallyConstant C₂ Z)
    [DecidablePred (· ∈ C₁)] (hf : ∀ x (hx : x ∈ C₁ ∩ C₂), f₁ ⟨x, hx.1⟩ = f₂ ⟨x, hx.2⟩)
    (x : C₀) (hx : x.val ∈ C₂) :
    piecewise' h₀ h₁ h₂ f₁ f₂ hf x = f₂ ⟨x.val, hx⟩ := by
  letI : ∀ j : C₀, Decidable (j ∈ Subtype.val ⁻¹' C₁) := fun j ↦ decidable_of_iff (↑j ∈ C₁) Iff.rfl
  rw [piecewise', piecewise_apply_right (f := (f₁.comap
    ⟨(restrictPreimage C₁ ((↑) : C₀ → X)), continuous_subtype_val.restrictPreimage⟩))
    (hx := hx)]
  rfl

end Piecewise

end LocallyConstant
