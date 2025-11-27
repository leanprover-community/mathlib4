/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Pi
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Simple functions

A function `f` from a measurable space to any type is called *simple*, if every preimage `f ⁻¹' {x}`
is measurable, and the range is finite. In this file, we define simple functions and establish their
basic properties; and we construct a sequence of simple functions approximating an arbitrary Borel
measurable function `f : α → ℝ≥0∞`.

The theorem `Measurable.ennreal_induction` shows that in order to prove something for an arbitrary
measurable function into `ℝ≥0∞`, it is sufficient to show that the property holds for (multiples of)
characteristic functions and is closed under addition and supremum of increasing sequences of
functions.
-/

@[expose] public section


noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type*}

/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure SimpleFunc.{u, v} (α : Type u) [MeasurableSpace α] (β : Type v) where
  /-- The underlying function -/
  toFun : α → β
  measurableSet_fiber' : ∀ x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section Measurable

variable [MeasurableSpace α]

instance instFunLike : FunLike (α →ₛ β) α β where
  coe := toFun
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem coe_injective ⦃f g : α →ₛ β⦄ (H : (f : α → β) = g) : f = g := DFunLike.ext' H

@[ext]
theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ H

theorem finite_range (f : α →ₛ β) : (Set.range f).Finite :=
  f.finite_range'

theorem measurableSet_fiber (f : α →ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x}) :=
  f.measurableSet_fiber' x

@[simp] theorem coe_mk (f : α → β) (h h') : ⇑(mk f h h') = f := rfl

theorem apply_mk (f : α → β) (h h') (x : α) : SimpleFunc.mk f h h' x = f x :=
  rfl

/-- Simple function defined on a finite type. -/
def ofFinite [Finite α] [MeasurableSingletonClass α] (f : α → β) : α →ₛ β where
  toFun := f
  measurableSet_fiber' x := (toFinite (f ⁻¹' {x})).measurableSet
  finite_range' := Set.finite_range f


/-- Simple function defined on the empty type. -/
def ofIsEmpty [IsEmpty α] : α →ₛ β := ofFinite isEmptyElim

/-- Range of a simple function `α →ₛ β` as a `Finset β`. -/
protected def range (f : α →ₛ β) : Finset β :=
  f.finite_range.toFinset

@[simp]
theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
  Finite.mem_toFinset _

theorem mem_range_self (f : α →ₛ β) (x : α) : f x ∈ f.range :=
  mem_range.2 ⟨x, rfl⟩

@[simp]
theorem coe_range (f : α →ₛ β) : (↑f.range : Set β) = Set.range f :=
  f.finite_range.coe_toFinset

theorem mem_range_of_measure_ne_zero {f : α →ₛ β} {x : β} {μ : Measure α} (H : μ (f ⁻¹' {x}) ≠ 0) :
    x ∈ f.range :=
  let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H
  mem_range.2 ⟨a, ha⟩

theorem forall_mem_range {f : α →ₛ β} {p : β → Prop} : (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) := by
  simp only [mem_range, Set.forall_mem_range]

theorem exists_range_iff {f : α →ₛ β} {p : β → Prop} : (∃ y ∈ f.range, p y) ↔ ∃ x, p (f x) := by
  simpa only [mem_range, exists_prop] using Set.exists_range_iff

theorem preimage_eq_empty_iff (f : α →ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
  preimage_singleton_eq_empty.trans <| not_congr mem_range.symm

theorem exists_forall_le [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] (f : α →ₛ β) :
    ∃ C, ∀ x, f x ≤ C :=
  f.range.exists_le.imp fun _ => forall_mem_range.1

/-- Constant function as a `SimpleFunc`. -/
def const (α) {β} [MeasurableSpace α] (b : β) : α →ₛ β :=
  ⟨fun _ => b, fun _ => MeasurableSet.const _, finite_range_const⟩

instance instInhabited [Inhabited β] : Inhabited (α →ₛ β) :=
  ⟨const _ default⟩

theorem const_apply (a : α) (b : β) : (const α b) a = b :=
  rfl

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl

@[simp]
theorem range_const (α) [MeasurableSpace α] [Nonempty α] (b : β) : (const α b).range = {b} :=
  Finset.coe_injective <| by simp +unfoldPartialApp [Function.const]

theorem range_const_subset (α) [MeasurableSpace α] (b : β) : (const α b).range ⊆ {b} :=
  Finset.coe_subset.1 <| by simp

theorem simpleFunc_bot {α} (f : @SimpleFunc α ⊥ β) [Nonempty β] : ∃ c, ∀ x, f x = c := by
  have hf_meas := @SimpleFunc.measurableSet_fiber α _ ⊥ f
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hf_meas
  exact (exists_eq_const_of_preimage_singleton hf_meas).imp fun c hc ↦ congr_fun hc

theorem simpleFunc_bot' {α} [Nonempty β] (f : @SimpleFunc α ⊥ β) :
    ∃ c, f = @SimpleFunc.const α _ ⊥ c :=
  letI : MeasurableSpace α := ⊥; (simpleFunc_bot f).imp fun _ ↦ ext

theorem measurableSet_cut (r : α → β → Prop) (f : α →ₛ β) (h : ∀ b, MeasurableSet { a | r a b }) :
    MeasurableSet { a | r a (f a) } := by
  have : { a | r a (f a) } = ⋃ b ∈ range f, { a | r a b } ∩ f ⁻¹' {b} := by
    ext a
    suffices r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i by simpa
    exact ⟨fun h => ⟨a, ⟨h, rfl⟩⟩, fun ⟨a', ⟨h', e⟩⟩ => e.symm ▸ h'⟩
  rw [this]
  exact
    MeasurableSet.biUnion f.finite_range.countable fun b _ =>
      MeasurableSet.inter (h b) (f.measurableSet_fiber _)

@[measurability]
theorem measurableSet_preimage (f : α →ₛ β) (s) : MeasurableSet (f ⁻¹' s) :=
  measurableSet_cut (fun _ b => b ∈ s) f fun b => MeasurableSet.const (b ∈ s)

/-- A simple function is measurable -/
@[fun_prop]
protected theorem measurable [MeasurableSpace β] (f : α →ₛ β) : Measurable f := fun s _ =>
  measurableSet_preimage f s

@[fun_prop]
protected theorem aemeasurable [MeasurableSpace β] {μ : Measure α} (f : α →ₛ β) :
    AEMeasurable f μ :=
  f.measurable.aemeasurable

protected theorem sum_measure_preimage_singleton (f : α →ₛ β) {μ : Measure α} (s : Finset β) :
    (∑ y ∈ s, μ (f ⁻¹' {y})) = μ (f ⁻¹' ↑s) :=
  sum_measure_preimage_singleton _ fun _ _ => f.measurableSet_fiber _

theorem sum_range_measure_preimage_singleton (f : α →ₛ β) (μ : Measure α) :
    (∑ y ∈ f.range, μ (f ⁻¹' {y})) = μ univ := by
  rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]

open scoped Classical in
/-- If-then-else as a `SimpleFunc`. -/
def piecewise (s : Set α) (hs : MeasurableSet s) (f g : α →ₛ β) : α →ₛ β :=
  ⟨s.piecewise f g, fun _ =>
    letI : MeasurableSpace β := ⊤
    f.measurable.piecewise hs g.measurable trivial,
    (f.finite_range.union g.finite_range).subset range_ite_subset⟩

open scoped Classical in
@[simp]
theorem coe_piecewise {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) :
    ⇑(piecewise s hs f g) = s.piecewise f g :=
  rfl

open scoped Classical in
theorem piecewise_apply {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) (a) :
    piecewise s hs f g a = if a ∈ s then f a else g a :=
  rfl

open scoped Classical in
@[simp]
theorem piecewise_compl {s : Set α} (hs : MeasurableSet sᶜ) (f g : α →ₛ β) :
    piecewise sᶜ hs f g = piecewise s hs.of_compl g f :=
  coe_injective <| by simp

@[simp]
theorem piecewise_univ (f g : α →ₛ β) : piecewise univ MeasurableSet.univ f g = f :=
  coe_injective <| by simp

@[simp]
theorem piecewise_empty (f g : α →ₛ β) : piecewise ∅ MeasurableSet.empty f g = g :=
  coe_injective <| by simp

open scoped Classical in
@[simp]
theorem piecewise_same (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) :
    piecewise s hs f f = f :=
  coe_injective <| Set.piecewise_same _ _

theorem support_indicator [Zero β] {s : Set α} (hs : MeasurableSet s) (f : α →ₛ β) :
    Function.support (f.piecewise s hs (SimpleFunc.const α 0)) = s ∩ Function.support f :=
  Set.support_indicator

open scoped Classical in
theorem range_indicator {s : Set α} (hs : MeasurableSet s) (hs_nonempty : s.Nonempty)
    (hs_ne_univ : s ≠ univ) (x y : β) :
    (piecewise s hs (const α x) (const α y)).range = {x, y} := by
  simp only [← Finset.coe_inj, coe_range, coe_piecewise, range_piecewise, coe_const,
    Finset.coe_insert, Finset.coe_singleton, hs_nonempty.image_const,
    (nonempty_compl.2 hs_ne_univ).image_const, singleton_union, Function.const]

theorem measurable_bind [MeasurableSpace γ] (f : α →ₛ β) (g : β → α → γ)
    (hg : ∀ b, Measurable (g b)) : Measurable fun a => g (f a) a := fun s hs =>
  f.measurableSet_cut (fun a b => g b a ∈ s) fun b => hg b hs

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
  ⟨fun a => g (f a) a, fun c =>
    f.measurableSet_cut (fun a b => g b a = c) fun b => (g b).measurableSet_preimage {c},
    (f.finite_range.biUnion fun b _ => (g b).finite_range).subset <| by
      rintro _ ⟨a, rfl⟩; simp⟩

@[simp]
theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) : f.bind g a = g (f a) a :=
  rfl

/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
function `g ∘ f : α →ₛ γ` -/
def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ :=
  bind f (const α ∘ g)

theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) :=
  rfl

theorem map_map (g : β → γ) (h : γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) :=
  rfl

@[simp]
theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = g ∘ f :=
  rfl

@[simp]
theorem range_map [DecidableEq γ] (g : β → γ) (f : α →ₛ β) : (f.map g).range = f.range.image g :=
  Finset.coe_injective <| by simp only [coe_range, coe_map, Finset.coe_image, range_comp]

@[simp]
theorem map_const (g : β → γ) (b : β) : (const α b).map g = const α (g b) :=
  rfl

open scoped Classical in
theorem map_preimage (f : α →ₛ β) (g : β → γ) (s : Set γ) :
    f.map g ⁻¹' s = f ⁻¹' ↑{b ∈ f.range | g b ∈ s} := by
  simp only [coe_range, sep_mem_eq, coe_map, Finset.coe_filter,
    ← mem_preimage, inter_comm, preimage_inter_range, ← Finset.mem_coe]
  exact preimage_comp

open scoped Classical in
theorem map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
    f.map g ⁻¹' {c} = f ⁻¹' ↑{b ∈ f.range | g b = c} :=
  map_preimage _ _ _

/-- Composition of a `SimpleFun` and a measurable function is a `SimpleFunc`. -/
def comp [MeasurableSpace β] (f : β →ₛ γ) (g : α → β) (hgm : Measurable g) : α →ₛ γ where
  toFun := f ∘ g
  finite_range' := f.finite_range.subset <| Set.range_comp_subset_range _ _
  measurableSet_fiber' z := hgm (f.measurableSet_fiber z)

@[simp]
theorem coe_comp [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
    ⇑(f.comp g hgm) = f ∘ g :=
  rfl

theorem range_comp_subset_range [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
    (f.comp g hgm).range ⊆ f.range :=
  Finset.coe_subset.1 <| by simp only [coe_range, coe_comp, Set.range_comp_subset_range]

/-- Extend a `SimpleFunc` along a measurable embedding: `f₁.extend g hg f₂` is the function
`F : β →ₛ γ` such that `F ∘ g = f₁` and `F y = f₂ y` whenever `y ∉ range g`. -/
def extend [MeasurableSpace β] (f₁ : α →ₛ γ) (g : α → β) (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : β →ₛ γ where
  toFun := Function.extend g f₁ f₂
  finite_range' :=
    (f₁.finite_range.union <| f₂.finite_range.subset (image_subset_range _ _)).subset
      (range_extend_subset _ _ _)
  measurableSet_fiber' := by
    letI : MeasurableSpace γ := ⊤; haveI : MeasurableSingletonClass γ := ⟨fun _ => trivial⟩
    exact fun x => hg.measurable_extend f₁.measurable f₂.measurable (measurableSet_singleton _)

@[simp]
theorem extend_apply [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) (x : α) : (f₁.extend g hg f₂) (g x) = f₁ x :=
  hg.injective.extend_apply _ _ _

@[simp]
theorem extend_apply' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) {y : β} (h : ¬∃ x, g x = y) : (f₁.extend g hg f₂) y = f₂ y :=
  Function.extend_apply' _ _ _ h

@[simp]
theorem extend_comp_eq' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : f₁.extend g hg f₂ ∘ g = f₁ :=
  funext fun _ => extend_apply _ _ _ _

@[simp]
theorem extend_comp_eq [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : (f₁.extend g hg f₂).comp g hg.measurable = f₁ :=
  coe_injective <| extend_comp_eq' _ hg _

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq (f : α →ₛ β → γ) (g : α →ₛ β) : α →ₛ γ :=
  f.bind fun f => g.map f

@[simp]
theorem seq_apply (f : α →ₛ β → γ) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) :=
  rfl

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `fun a => (f a, g a)`. -/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ β × γ :=
  (f.map Prod.mk).seq g

@[simp]
theorem pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) :=
  rfl

theorem pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : Set β) (t : Set γ) :
    pair f g ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl

-- A special form of `pair_preimage`
theorem pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
    pair f g ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} := by
  rw [← singleton_prod_singleton]
  exact pair_preimage _ _ _ _

@[simp] theorem map_fst_pair (f : α →ₛ β) (g : α →ₛ γ) : (f.pair g).map Prod.fst = f := rfl
@[simp] theorem map_snd_pair (f : α →ₛ β) (g : α →ₛ γ) : (f.pair g).map Prod.snd = g := rfl

@[simp]
theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext; simp

@[to_additive]
instance instOne [One β] : One (α →ₛ β) :=
  ⟨const α 1⟩

@[to_additive]
instance instMul [Mul β] : Mul (α →ₛ β) :=
  ⟨fun f g => (f.map (· * ·)).seq g⟩

@[to_additive]
instance instDiv [Div β] : Div (α →ₛ β) :=
  ⟨fun f g => (f.map (· / ·)).seq g⟩

@[to_additive]
instance instInv [Inv β] : Inv (α →ₛ β) :=
  ⟨fun f => f.map Inv.inv⟩

instance instSup [Max β] : Max (α →ₛ β) :=
  ⟨fun f g => (f.map (· ⊔ ·)).seq g⟩

instance instInf [Min β] : Min (α →ₛ β) :=
  ⟨fun f g => (f.map (· ⊓ ·)).seq g⟩

instance instLE [LE β] : LE (α →ₛ β) :=
  ⟨fun f g => ∀ a, f a ≤ g a⟩

@[to_additive (attr := simp)]
theorem const_one [One β] : const α (1 : β) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_one [One β] : ⇑(1 : α →ₛ β) = 1 :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul [Mul β] (f g : α →ₛ β) : ⇑(f * g) = ⇑f * ⇑g :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv [Inv β] (f : α →ₛ β) : ⇑(f⁻¹) = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_div [Div β] (f g : α →ₛ β) : ⇑(f / g) = ⇑f / ⇑g :=
  rfl

@[simp, norm_cast]
theorem coe_sup [Max β] (f g : α →ₛ β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[simp, norm_cast]
theorem coe_inf [Min β] (f g : α →ₛ β) : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl

@[to_additive]
theorem mul_apply [Mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a :=
  rfl

@[to_additive]
theorem div_apply [Div β] (f g : α →ₛ β) (x : α) : (f / g) x = f x / g x :=
  rfl

@[to_additive]
theorem inv_apply [Inv β] (f : α →ₛ β) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl

theorem sup_apply [Max β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

theorem inf_apply [Min β] (f g : α →ₛ β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl

@[to_additive (attr := simp)]
theorem range_one [Nonempty α] [One β] : (1 : α →ₛ β).range = {1} :=
  Finset.ext fun x => by simp

@[simp]
theorem range_eq_empty_of_isEmpty {β} [hα : IsEmpty α] (f : α →ₛ β) : f.range = ∅ := by
  ext
  simp

theorem eq_zero_of_mem_range_zero [Zero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
  @(forall_mem_range.2 fun _ => rfl)

@[to_additive]
theorem mul_eq_map₂ [Mul β] (f g : α →ₛ β) : f * g = (pair f g).map fun p : β × β => p.1 * p.2 :=
  rfl

theorem sup_eq_map₂ [Max β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map fun p : β × β => p.1 ⊔ p.2 :=
  rfl

@[to_additive]
theorem const_mul_eq_map [Mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map fun a => b * a :=
  rfl

@[to_additive]
theorem map_mul [Mul β] [Mul γ] {g : β → γ} (hg : ∀ x y, g (x * y) = g x * g y) (f₁ f₂ : α →ₛ β) :
    (f₁ * f₂).map g = f₁.map g * f₂.map g :=
  ext fun _ => hg _ _

variable {K : Type*}

@[to_additive]
instance instSMul [SMul K β] : SMul K (α →ₛ β) :=
  ⟨fun k f => f.map (k • ·)⟩

@[to_additive (attr := simp)]
theorem coe_smul [SMul K β] (c : K) (f : α →ₛ β) : ⇑(c • f) = c • ⇑f :=
  rfl

@[to_additive (attr := simp)]
theorem smul_apply [SMul K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a :=
  rfl

instance hasNatSMul [AddMonoid β] : SMul ℕ (α →ₛ β) := inferInstance

@[to_additive existing hasNatSMul]
instance hasNatPow [Monoid β] : Pow (α →ₛ β) ℕ :=
  ⟨fun f n => f.map (· ^ n)⟩

@[simp]
theorem coe_pow [Monoid β] (f : α →ₛ β) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

theorem pow_apply [Monoid β] (n : ℕ) (f : α →ₛ β) (a : α) : (f ^ n) a = f a ^ n :=
  rfl

instance hasIntPow [DivInvMonoid β] : Pow (α →ₛ β) ℤ :=
  ⟨fun f n => f.map (· ^ n)⟩

@[simp]
theorem coe_zpow [DivInvMonoid β] (f : α →ₛ β) (z : ℤ) : ⇑(f ^ z) = (⇑f) ^ z :=
  rfl

theorem zpow_apply [DivInvMonoid β] (z : ℤ) (f : α →ₛ β) (a : α) : (f ^ z) a = f a ^ z :=
  rfl

-- TODO: work out how to generate these instances with `to_additive`, which gets confused by the
-- argument order swap between `coe_smul` and `coe_pow`.
section Additive

instance instAddMonoid [AddMonoid β] : AddMonoid (α →ₛ β) :=
  fast_instance% Function.Injective.addMonoid (fun f => show α → β from f) coe_injective coe_zero
    coe_add fun _ _ => coe_smul _ _

instance instAddCommMonoid [AddCommMonoid β] : AddCommMonoid (α →ₛ β) :=
  fast_instance% Function.Injective.addCommMonoid (fun f => show α → β from f)
    coe_injective coe_zero coe_add fun _ _ => coe_smul _ _

instance instAddGroup [AddGroup β] : AddGroup (α →ₛ β) :=
  Function.Injective.addGroup (fun f => show α → β from f) coe_injective coe_zero coe_add coe_neg
    coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

instance instAddCommGroup [AddCommGroup β] : AddCommGroup (α →ₛ β) :=
  fast_instance% Function.Injective.addCommGroup (fun f => show α → β from f) coe_injective
    coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _

end Additive

@[to_additive existing]
instance instMonoid [Monoid β] : Monoid (α →ₛ β) :=
  fast_instance% Function.Injective.monoid (fun f => show α → β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]
instance instCommMonoid [CommMonoid β] : CommMonoid (α →ₛ β) :=
  fast_instance% Function.Injective.commMonoid (fun f => show α → β from f) coe_injective coe_one
    coe_mul coe_pow

@[to_additive existing]
instance instGroup [Group β] : Group (α →ₛ β) :=
  fast_instance% Function.Injective.group (fun f => show α → β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive existing]
instance instCommGroup [CommGroup β] : CommGroup (α →ₛ β) :=
  fast_instance% Function.Injective.commGroup (fun f => show α → β from f) coe_injective coe_one
    coe_mul coe_inv coe_div coe_pow coe_zpow

instance [Monoid K] [MulAction K β] : MulAction K (α →ₛ β) :=
  fast_instance% Function.Injective.mulAction (fun f => show α → β from f) coe_injective coe_smul

instance instModule [Semiring K] [AddCommMonoid β] [Module K β] : Module K (α →ₛ β) :=
  fast_instance% Function.Injective.module K ⟨⟨fun f => show α → β from f, coe_zero⟩, coe_add⟩
    coe_injective coe_smul

theorem smul_eq_map [SMul K β] (k : K) (f : α →ₛ β) : k • f = f.map (k • ·) :=
  rfl

lemma smul_const [SMul K β] (k : K) (b : β) :
    (k • const α b : α →ₛ β) = const α (k • b) := ext fun _ ↦ rfl

instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalNonAssocSemiring (fun f => show α → β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul

instance [NonUnitalSemiring β] : NonUnitalSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalSemiring (fun f => show α → β from f)
    SimpleFunc.coe_injective coe_zero coe_add coe_mul coe_smul

instance [NatCast β] : NatCast (α →ₛ β) where
  natCast n := const _ (NatCast.natCast n)

@[simp, norm_cast]
lemma coe_natCast [NatCast β] (n : ℕ) :
    ⇑(↑n : α →ₛ β) = fun _ ↦ ↑n := rfl

instance [NonAssocSemiring β] : NonAssocSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.nonAssocSemiring (fun f => show α → β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_natCast

instance [IntCast β] : IntCast (α →ₛ β) where
  intCast n := const _ (IntCast.intCast n)

@[simp, norm_cast]
lemma coe_intCast [IntCast β] (n : ℤ) :
    ⇑(↑n : α →ₛ β) = fun _ ↦ ↑n := rfl

instance [NonAssocRing β] : NonAssocRing (α →ₛ β) :=
  fast_instance% Function.Injective.nonAssocRing (fun f => show α → β from f) coe_injective
    coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_natCast coe_intCast

instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalCommSemiring (fun f => show α → β from f)
    coe_injective coe_zero coe_add coe_mul coe_smul

instance [CommSemiring β] : CommSemiring (α →ₛ β) :=
  fast_instance% Function.Injective.commSemiring (fun f => show α → β from f)
    coe_injective coe_zero coe_one coe_add coe_mul coe_smul coe_pow coe_natCast

instance [NonUnitalCommRing β] : NonUnitalCommRing (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalCommRing (fun f => show α → β from f)
    coe_injective coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul

instance [CommRing β] : CommRing (α →ₛ β) :=
  fast_instance% Function.Injective.commRing (fun f => show α → β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

instance [Semiring β] : Semiring (α →ₛ β) :=
  fast_instance% Function.Injective.semiring (fun f => show α → β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_smul coe_pow coe_natCast

instance [NonUnitalRing β] : NonUnitalRing (α →ₛ β) :=
  fast_instance% Function.Injective.nonUnitalRing (fun f => show α → β from f) coe_injective
    coe_zero coe_add coe_mul coe_neg coe_sub coe_smul coe_smul

instance [Ring β] : Ring (α →ₛ β) :=
  fast_instance% Function.Injective.ring (fun f => show α → β from f) coe_injective coe_zero
    coe_one coe_add coe_mul coe_neg coe_sub coe_smul coe_smul coe_pow coe_natCast coe_intCast

instance [SMul K γ] [SMul γ β] [SMul K β] [IsScalarTower K γ β] : IsScalarTower K γ (α →ₛ β) where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc ..

instance [SMul γ β] [SMul K β] [SMulCommClass K γ β] : SMulCommClass K γ (α →ₛ β) where
  smul_comm _ _ _ := ext fun _ ↦  smul_comm ..

instance [CommSemiring K] [Semiring β] [Algebra K β] : Algebra K (α →ₛ β) where
  algebraMap :={
    toFun r := const α <| algebraMap K β r
    map_one' := ext fun _ ↦ algebraMap K β |>.map_one ▸ rfl
    map_mul' _ _ := ext fun _ ↦ algebraMap K β |>.map_mul ..
    map_zero' := ext fun _ ↦ algebraMap K β |>.map_zero ▸ rfl
    map_add' _ _ := ext fun _ ↦ algebraMap K β |>.map_add ..}
  commutes' _ _ := ext fun _ ↦ Algebra.commutes ..
  smul_def' _ _ := ext fun _ ↦ Algebra.smul_def ..

@[simp]
lemma const_algebraMap [CommSemiring K] [Semiring β] [Algebra K β] (k : K) :
    const α (algebraMap K β k) = algebraMap K (α →ₛ β) k := rfl

@[simp]
lemma coe_algebraMap [CommSemiring K] [Semiring β] [Algebra K β] (k : K) (x : α) :
    ⇑(algebraMap K (α →ₛ β)) k x = algebraMap K (α → β) k x := rfl

section Star

instance [Star β] : Star (α →ₛ β) where
  star f := f.map Star.star

@[simp]
lemma coe_star [Star β] {f : α →ₛ β} : ⇑(star f) = star ⇑f := rfl

instance [InvolutiveStar β] : InvolutiveStar (α →ₛ β) where
  star_involutive _ := ext fun _ ↦ star_star _

instance [AddMonoid β] [StarAddMonoid β] : StarAddMonoid (α →ₛ β) where
  star_add _ _ := ext fun _ ↦ star_add ..

instance [Mul β] [StarMul β] : StarMul (α →ₛ β) where
  star_mul _ _ := ext fun _ ↦ star_mul ..

instance [NonUnitalNonAssocSemiring β] [StarRing β] : StarRing (α →ₛ β) where
  star_add _ _ := ext fun _ ↦ star_add ..

end Star

section Preorder
variable [Preorder β] {s : Set α} {f f₁ f₂ g g₁ g₂ : α →ₛ β} {hs : MeasurableSet s}

instance instPreorder : Preorder (α →ₛ β) := Preorder.lift (⇑)

@[simp, norm_cast] lemma coe_le_coe : ⇑f ≤ g ↔ f ≤ g := .rfl
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := .rfl

@[deprecated (since := "2025-10-21")] alias coe_le := coe_le_coe

@[simp] lemma mk_le_mk {f g : α → β} {hf hg hf' hg'} : mk f hf hf' ≤ mk g hg hg' ↔ f ≤ g := Iff.rfl
@[simp] lemma mk_lt_mk {f g : α → β} {hf hg hf' hg'} : mk f hf hf' < mk g hg hg' ↔ f < g := Iff.rfl

@[gcongr] protected alias ⟨_, GCongr.mk_le_mk⟩ := mk_le_mk
@[gcongr] protected alias ⟨_, GCongr.mk_lt_mk⟩ := mk_lt_mk
@[gcongr] protected alias ⟨_, GCongr.coe_le_coe⟩ := coe_le_coe
@[gcongr] protected alias ⟨_, GCongr.coe_lt_coe⟩ := coe_lt_coe

open scoped Classical in
@[gcongr]
lemma piecewise_mono (hf : ∀ a ∈ s, f₁ a ≤ f₂ a) (hg : ∀ a ∉ s, g₁ a ≤ g₂ a) :
    piecewise s hs f₁ g₁ ≤ piecewise s hs f₂ g₂ := Set.piecewise_mono hf hg

end Preorder

instance instPartialOrder [PartialOrder β] : PartialOrder (α →ₛ β) :=
  { SimpleFunc.instPreorder with
    le_antisymm := fun _f _g hfg hgf => ext fun a => le_antisymm (hfg a) (hgf a) }

instance instOrderBot [LE β] [OrderBot β] : OrderBot (α →ₛ β) where
  bot := const α ⊥
  bot_le _ _ := bot_le

instance instOrderTop [LE β] [OrderTop β] : OrderTop (α →ₛ β) where
  top := const α ⊤
  le_top _ _ := le_top

@[to_additive]
instance [CommMonoid β] [PartialOrder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (α →ₛ β) where
  mul_le_mul_left _ _ h _ _ := mul_le_mul_left (h _) _

instance instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (α →ₛ β) :=
  { SimpleFunc.instPartialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _f _g _h hfh hgh a => le_inf (hfh a) (hgh a) }

instance instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (α →ₛ β) :=
  { SimpleFunc.instPartialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _f _g _h hfh hgh a => sup_le (hfh a) (hgh a) }

instance instLattice [Lattice β] : Lattice (α →ₛ β) :=
  { SimpleFunc.instSemilatticeSup, SimpleFunc.instSemilatticeInf with }

instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (α →ₛ β) :=
  { SimpleFunc.instOrderBot, SimpleFunc.instOrderTop with }

theorem finset_sup_apply [SemilatticeSup β] [OrderBot β] {f : γ → α →ₛ β} (s : Finset γ) (a : α) :
    s.sup f a = s.sup fun c => f c a := by
  classical
  refine Finset.induction_on s rfl ?_
  intro a s _ ih
  rw [Finset.sup_insert, Finset.sup_insert, sup_apply, ih]

section Restrict

variable [Zero β]

open scoped Classical in
/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict (f : α →ₛ β) (s : Set α) : α →ₛ β :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0

theorem restrict_of_not_measurable {f : α →ₛ β} {s : Set α} (hs : ¬MeasurableSet s) :
    restrict f s = 0 :=
  dif_neg hs

@[simp]
theorem coe_restrict (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) :
    ⇑(restrict f s) = indicator s f := by
  classical
  rw [restrict, dif_pos hs, coe_piecewise, coe_zero, piecewise_eq_indicator]

@[simp]
theorem restrict_univ (f : α →ₛ β) : restrict f univ = f := by simp [restrict]

@[simp]
theorem restrict_empty (f : α →ₛ β) : restrict f ∅ = 0 := by simp [restrict]

open scoped Classical in
theorem map_restrict_of_zero [Zero γ] {g : β → γ} (hg : g 0 = 0) (f : α →ₛ β) (s : Set α) :
    (f.restrict s).map g = (f.map g).restrict s :=
  ext fun x =>
    if hs : MeasurableSet s then by simp [hs, Set.indicator_comp_of_zero hg]
    else by simp [restrict_of_not_measurable hs, hg]

theorem map_coe_ennreal_restrict (f : α →ₛ ℝ≥0) (s : Set α) :
    (f.restrict s).map ((↑) : ℝ≥0 → ℝ≥0∞) = (f.map (↑)).restrict s :=
  map_restrict_of_zero ENNReal.coe_zero _ _

theorem map_coe_nnreal_restrict (f : α →ₛ ℝ≥0) (s : Set α) :
    (f.restrict s).map ((↑) : ℝ≥0 → ℝ) = (f.map (↑)).restrict s :=
  map_restrict_of_zero NNReal.coe_zero _ _

theorem restrict_apply (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) (a) :
    restrict f s a = indicator s f a := by simp only [f.coe_restrict hs]

theorem restrict_preimage (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Set β}
    (ht : (0 : β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t := by
  simp [hs, indicator_preimage_of_notMem _ _ ht, inter_comm]

theorem restrict_preimage_singleton (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β}
    (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
  f.restrict_preimage hs hr.symm

theorem mem_restrict_range {r : β} {s : Set α} {f : α →ₛ β} (hs : MeasurableSet s) :
    r ∈ (restrict f s).range ↔ r = 0 ∧ s ≠ univ ∨ r ∈ f '' s := by
  rw [← Finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]

open scoped Classical in
theorem mem_image_of_mem_range_restrict {r : β} {s : Set α} {f : α →ₛ β}
    (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) : r ∈ f '' s :=
  if hs : MeasurableSet s then by simpa [mem_restrict_range hs, h0, -mem_range] using hr
  else by
    rw [restrict_of_not_measurable hs] at hr
    exact (h0 <| eq_zero_of_mem_range_zero hr).elim

open scoped Classical in
@[gcongr, mono]
theorem restrict_mono [Preorder β] (s : Set α) {f g : α →ₛ β} (H : f ≤ g) :
    f.restrict s ≤ g.restrict s :=
  if hs : MeasurableSet s then fun x => by
    simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
  else by simp only [restrict_of_not_measurable hs, le_refl]

end Restrict

section Approx

section

variable [SemilatticeSup β] [OrderBot β] [Zero β]

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `iSup_approx_apply` for details. -/
def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
  (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k ≤ f a }

open scoped Classical in
theorem approx_apply [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : Measurable f) :
    (approx i f n : α →ₛ β) a = (Finset.range n).sup fun k => if i k ≤ f a then i k else 0 := by
  dsimp only [approx]
  rw [finset_sup_apply]
  congr
  funext k
  rw [restrict_apply]
  · simp only [coe_const, mem_setOf_eq, indicator_apply, Function.const_apply]
  · exact hf measurableSet_Ici

theorem monotone_approx (i : ℕ → β) (f : α → β) : Monotone (approx i f) := fun _ _ h =>
  Finset.sup_mono <| Finset.range_subset_range.2 h

theorem approx_comp [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] [MeasurableSpace γ] {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α)
    (hf : Measurable f) (hg : Measurable g) :
    (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) := by
  rw [approx_apply _ hf, approx_apply _ (hf.comp hg), Function.comp_apply]

end

theorem iSup_approx_apply [TopologicalSpace β] [CompleteLattice β] [OrderClosedTopology β] [Zero β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (i : ℕ → β) (f : α → β) (a : α) (hf : Measurable f)
    (h_zero : (0 : β) = ⊥) : ⨆ n, (approx i f n : α →ₛ β) a = ⨆ (k) (_ : i k ≤ f a), i k := by
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun k => iSup_le fun hk => ?_)
  · rw [approx_apply a hf, h_zero]
    refine Finset.sup_le fun k _ => ?_
    split_ifs with h
    · exact le_iSup_of_le k (le_iSup (fun _ : i k ≤ f a => i k) h)
    · exact bot_le
  · refine le_iSup_of_le (k + 1) ?_
    rw [approx_apply a hf]
    have : k ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self _)
    refine le_trans (le_of_eq ?_) (Finset.le_sup this)
    rw [if_pos hk]

end Approx

section EApprox
variable {f : α → ℝ≥0∞}

/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
def ennrealRatEmbed (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Encodable.decode (α := ℚ) n).getD (0 : ℚ))

theorem ennrealRatEmbed_encode (q : ℚ) :
    ennrealRatEmbed (Encodable.encode q) = Real.toNNReal q := by
  rw [ennrealRatEmbed, Encodable.encodek]; rfl

/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
  approx ennrealRatEmbed

theorem eapprox_lt_top (f : α → ℝ≥0∞) (n : ℕ) (a : α) : eapprox f n a < ∞ := by
  simp only [eapprox, approx, finset_sup_apply, restrict]
  rw [Finset.sup_lt_iff (α := ℝ≥0∞) WithTop.top_pos]
  intro b _
  split_ifs
  · simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
    calc
      { a : α | ennrealRatEmbed b ≤ f a }.indicator (fun _ => ennrealRatEmbed b) a ≤
          ennrealRatEmbed b :=
        indicator_le_self _ _ a
      _ < ⊤ := ENNReal.coe_lt_top
  · exact WithTop.top_pos

@[gcongr, mono]
theorem monotone_eapprox (f : α → ℝ≥0∞) : Monotone (eapprox f) :=
  monotone_approx _ f

@[deprecated monotone_eapprox (since := "2025-08-13")]
lemma eapprox_mono {m n : ℕ} (hmn : m ≤ n) : eapprox f m ≤ eapprox f n := monotone_eapprox _ hmn

lemma iSup_eapprox_apply (hf : Measurable f) (a : α) : ⨆ n, (eapprox f n : α →ₛ ℝ≥0∞) a = f a := by
  rw [eapprox, iSup_approx_apply ennrealRatEmbed f a hf rfl]
  refine le_antisymm (iSup_le fun i => iSup_le fun hi => hi) (le_of_not_gt ?_)
  intro h
  rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, _, lt_q, q_lt⟩
  have :
    (Real.toNNReal q : ℝ≥0∞) ≤ ⨆ (k : ℕ) (_ : ennrealRatEmbed k ≤ f a), ennrealRatEmbed k := by
    refine le_iSup_of_le (Encodable.encode q) ?_
    rw [ennrealRatEmbed_encode q]
    exact le_iSup_of_le (le_of_lt q_lt) le_rfl
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)

lemma iSup_coe_eapprox (hf : Measurable f) : ⨆ n, ⇑(eapprox f n) = f := by
  simpa [funext_iff] using iSup_eapprox_apply hf

theorem eapprox_comp [MeasurableSpace γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ} (hf : Measurable f)
    (hg : Measurable g) : (eapprox (f ∘ g) n : α → ℝ≥0∞) = (eapprox f n : γ →ₛ ℝ≥0∞) ∘ g :=
  funext fun a => approx_comp a hf hg

lemma tendsto_eapprox {f : α → ℝ≥0∞} (hf_meas : Measurable f) (a : α) :
    Tendsto (fun n ↦ eapprox f n a) atTop (𝓝 (f a)) := by
  nth_rw 2 [← iSup_coe_eapprox hf_meas]
  rw [iSup_apply]
  exact tendsto_atTop_iSup fun _ _ hnm ↦ monotone_eapprox f hnm a

/-- Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their values
in `ℝ≥0`. -/
def eapproxDiff (f : α → ℝ≥0∞) : ℕ → α →ₛ ℝ≥0
  | 0 => (eapprox f 0).map ENNReal.toNNReal
  | n + 1 => (eapprox f (n + 1) - eapprox f n).map ENNReal.toNNReal

theorem sum_eapproxDiff (f : α → ℝ≥0∞) (n : ℕ) (a : α) :
    (∑ k ∈ Finset.range (n + 1), (eapproxDiff f k a : ℝ≥0∞)) = eapprox f n a := by
  induction n with
  | zero =>
    simp [eapproxDiff, (eapprox_lt_top f 0 a).ne]
  | succ n IH =>
    rw [Finset.sum_range_succ, IH, eapproxDiff, coe_map, Function.comp_apply,
      coe_sub, Pi.sub_apply, ENNReal.coe_toNNReal,
      add_tsub_cancel_of_le (monotone_eapprox f (Nat.le_succ _) _)]
    apply (lt_of_le_of_lt _ (eapprox_lt_top f (n + 1) a)).ne
    rw [tsub_le_iff_right]
    exact le_self_add

theorem tsum_eapproxDiff (f : α → ℝ≥0∞) (hf : Measurable f) (a : α) :
    (∑' n, (eapproxDiff f n a : ℝ≥0∞)) = f a := by
  simp_rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1), sum_eapproxDiff,
    iSup_eapprox_apply hf a]

end EApprox

end Measurable

section Measure

variable {m : MeasurableSpace α} {μ ν : Measure α}

/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
def lintegral {_m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  ∑ x ∈ f.range, x * μ (f ⁻¹' {x})

theorem lintegral_eq_of_subset (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞}
    (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
    f.lintegral μ = ∑ x ∈ s, x * μ (f ⁻¹' {x}) := by
  refine Finset.sum_bij_ne_zero (fun r _ _ => r) ?_ ?_ ?_ ?_
  · simpa only [forall_mem_range, mul_ne_zero_iff, and_imp]
  · intros
    assumption
  · intro b _ hb
    refine ⟨b, ?_, hb, rfl⟩
    rw [mem_range, ← preimage_singleton_nonempty]
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2
  · intros
    rfl

theorem lintegral_eq_of_subset' (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞} (hs : f.range \ {0} ⊆ s) :
    f.lintegral μ = ∑ x ∈ s, x * μ (f ⁻¹' {x}) :=
  f.lintegral_eq_of_subset fun x hfx _ =>
    hs <| Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hfx⟩

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`. -/
theorem map_lintegral (g : β → ℝ≥0∞) (f : α →ₛ β) :
    (f.map g).lintegral μ = ∑ x ∈ f.range, g x * μ (f ⁻¹' {x}) := by
  simp only [lintegral, range_map]
  refine Finset.sum_image' _ fun b hb => ?_
  rcases mem_range.1 hb with ⟨a, rfl⟩
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton, Finset.mul_sum]
  refine Finset.sum_congr ?_ ?_
  · congr
  · grind

theorem add_lintegral (f g : α →ₛ ℝ≥0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
  calc
    (f + g).lintegral μ =
        ∑ x ∈ (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) := by
      rw [add_eq_map₂, map_lintegral]; exact Finset.sum_congr rfl fun a _ => add_mul _ _ _
    _ = (∑ x ∈ (pair f g).range, x.1 * μ (pair f g ⁻¹' {x})) +
          ∑ x ∈ (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) := by
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).lintegral μ + ((pair f g).map Prod.snd).lintegral μ := by
      rw [map_lintegral, map_lintegral]
    _ = lintegral f μ + lintegral g μ := rfl

theorem const_mul_lintegral (f : α →ₛ ℝ≥0∞) (x : ℝ≥0∞) :
    (const α x * f).lintegral μ = x * f.lintegral μ :=
  calc
    (f.map fun a => x * a).lintegral μ = ∑ r ∈ f.range, x * r * μ (f ⁻¹' {r}) := map_lintegral _ _
    _ = x * ∑ r ∈ f.range, r * μ (f ⁻¹' {r}) := by simp_rw [Finset.mul_sum, mul_assoc]

/-- Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map. -/
def lintegralₗ {m : MeasurableSpace α} : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] Measure α →ₗ[ℝ≥0∞] ℝ≥0∞ where
  toFun f :=
    { toFun := lintegral f
      map_add' := by simp [lintegral, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c μ => by
        simp [lintegral, mul_left_comm _ c, Finset.mul_sum, Measure.smul_apply c] }
  map_add' f g := LinearMap.ext fun _ => add_lintegral f g
  map_smul' c f := LinearMap.ext fun _ => const_mul_lintegral f c

@[simp]
theorem zero_lintegral : (0 : α →ₛ ℝ≥0∞).lintegral μ = 0 :=
  LinearMap.ext_iff.1 lintegralₗ.map_zero μ

theorem lintegral_add {ν} (f : α →ₛ ℝ≥0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
  (lintegralₗ f).map_add μ ν

theorem lintegral_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (f : α →ₛ ℝ≥0∞) (c : R) : f.lintegral (c • μ) = c • f.lintegral μ := by
  simpa only [smul_one_smul] using (lintegralₗ f).map_smul (c • 1) μ

@[simp]
theorem lintegral_zero [MeasurableSpace α] (f : α →ₛ ℝ≥0∞) : f.lintegral 0 = 0 :=
  (lintegralₗ f).map_zero

theorem lintegral_finset_sum {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → Measure α) (s : Finset ι) :
    f.lintegral (∑ i ∈ s, μ i) = ∑ i ∈ s, f.lintegral (μ i) :=
  map_sum (lintegralₗ f) ..

theorem lintegral_sum {m : MeasurableSpace α} {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → Measure α) :
    f.lintegral (Measure.sum μ) = ∑' i, f.lintegral (μ i) := by
  simp only [lintegral, Measure.sum_apply, f.measurableSet_preimage, ← Finset.tsum_subtype, ←
    ENNReal.tsum_mul_left]
  apply ENNReal.tsum_comm

open scoped Classical in
theorem restrict_lintegral (f : α →ₛ ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    (restrict f s).lintegral μ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r} ∩ s) :=
  calc
    (restrict f s).lintegral μ = ∑ r ∈ f.range, r * μ (restrict f s ⁻¹' {r}) :=
      lintegral_eq_of_subset _ fun x hx =>
        if hxs : x ∈ s then fun _ => by
          simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
        else False.elim <| hx <| by simp [*]
    _ = ∑ r ∈ f.range, r * μ (f ⁻¹' {r} ∩ s) :=
      Finset.sum_congr rfl <|
        forall_mem_range.2 fun b =>
          if hb : f b = 0 then by simp only [hb, zero_mul]
          else by rw [restrict_preimage_singleton _ hs hb, inter_comm]

theorem lintegral_restrict {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (s : Set α) (μ : Measure α) :
    f.lintegral (μ.restrict s) = ∑ y ∈ f.range, y * μ (f ⁻¹' {y} ∩ s) := by
  simp only [lintegral, Measure.restrict_apply, f.measurableSet_preimage]

theorem restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ℝ≥0∞) {s : Set α}
    (hs : MeasurableSet s) : (restrict f s).lintegral μ = f.lintegral (μ.restrict s) := by
  rw [f.restrict_lintegral hs, lintegral_restrict]

theorem lintegral_restrict_iUnion_of_directed {ι : Type*} [Countable ι]
    (f : α →ₛ ℝ≥0∞) {s : ι → Set α} (hd : Directed (· ⊆ ·) s) (μ : Measure α) :
    f.lintegral (μ.restrict (⋃ i, s i)) = ⨆ i, f.lintegral (μ.restrict (s i)) := by
  simp only [lintegral, Measure.restrict_iUnion_apply_eq_iSup hd (measurableSet_preimage ..),
    ENNReal.mul_iSup]
  refine finsetSum_iSup fun i j ↦ (hd i j).imp fun k ⟨hik, hjk⟩ ↦ fun a ↦ ?_
  -- TODO https://github.com/leanprover-community/mathlib4/pull/14739 make `gcongr` close this goal
  constructor <;> · gcongr; refine Measure.restrict_mono ?_ le_rfl _; assumption

theorem const_lintegral (c : ℝ≥0∞) : (const α c).lintegral μ = c * μ univ := by
  rw [lintegral]
  cases isEmpty_or_nonempty α
  · simp [μ.eq_zero_of_isEmpty]
  · simp only [range_const, coe_const, Finset.sum_singleton]
    unfold Function.const; rw [preimage_const_of_mem (mem_singleton c)]

theorem const_lintegral_restrict (c : ℝ≥0∞) (s : Set α) :
    (const α c).lintegral (μ.restrict s) = c * μ s := by
  rw [const_lintegral, Measure.restrict_apply MeasurableSet.univ, univ_inter]

theorem restrict_const_lintegral (c : ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ((const α c).restrict s).lintegral μ = c * μ s := by
  rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]

theorem lintegral_mono_fun {f g : α →ₛ ℝ≥0∞} (h : f ≤ g) : f.lintegral μ ≤ g.lintegral μ := by
  refine Monotone.of_left_le_map_sup (f := (lintegral · μ)) (fun f g ↦ ?_) h
  calc
    f.lintegral μ = ((pair f g).map Prod.fst).lintegral μ := by rw [map_fst_pair]
    _ ≤ ((pair f g).map fun p ↦ p.1 ⊔ p.2).lintegral μ := by
      simp only [map_lintegral]
      gcongr
      exact le_sup_left

theorem le_sup_lintegral (f g : α →ₛ ℝ≥0∞) : f.lintegral μ ⊔ g.lintegral μ ≤ (f ⊔ g).lintegral μ :=
  Monotone.le_map_sup (fun _ _ ↦ lintegral_mono_fun) f g

theorem lintegral_mono_measure {f : α →ₛ ℝ≥0∞} (h : μ ≤ ν) : f.lintegral μ ≤ f.lintegral ν := by
  simp only [lintegral]
  gcongr
  apply h

/-- `SimpleFunc.lintegral` is monotone both in function and in measure. -/
@[mono, gcongr]
theorem lintegral_mono {f g : α →ₛ ℝ≥0∞} (hfg : f ≤ g) (hμν : μ ≤ ν) :
    f.lintegral μ ≤ g.lintegral ν :=
  (lintegral_mono_fun hfg).trans (lintegral_mono_measure hμν)

/-- `SimpleFunc.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
theorem lintegral_eq_of_measure_preimage [MeasurableSpace β] {f : α →ₛ ℝ≥0∞} {g : β →ₛ ℝ≥0∞}
    {ν : Measure β} (H : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) : f.lintegral μ = g.lintegral ν := by
  simp only [lintegral, ← H]
  apply lintegral_eq_of_subset
  simp only [H]
  intros
  exact mem_range_of_measure_ne_zero ‹_›

/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
theorem lintegral_congr {f g : α →ₛ ℝ≥0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g.lintegral μ :=
  lintegral_eq_of_measure_preimage fun y =>
    measure_congr <| Eventually.set_eq <| h.mono fun x hx => by simp [hx]

theorem lintegral_map' {β} [MeasurableSpace β] {μ' : Measure β} (f : α →ₛ ℝ≥0∞) (g : β →ₛ ℝ≥0∞)
    (m' : α → β) (eq : ∀ a, f a = g (m' a)) (h : ∀ s, MeasurableSet s → μ' s = μ (m' ⁻¹' s)) :
    f.lintegral μ = g.lintegral μ' :=
  lintegral_eq_of_measure_preimage fun y => by
    simp only [preimage, eq]
    exact (h (g ⁻¹' {y}) (g.measurableSet_preimage _)).symm

theorem lintegral_map {β} [MeasurableSpace β] (g : β →ₛ ℝ≥0∞) {f : α → β} (hf : Measurable f) :
    g.lintegral (Measure.map f μ) = (g.comp f hf).lintegral μ :=
  Eq.symm <| lintegral_map' _ _ f (fun _ => rfl) fun _s hs => Measure.map_apply hf hs

end Measure

section FinMeasSupp

open Finset Function

open scoped Classical in
theorem support_eq [MeasurableSpace α] [Zero β] (f : α →ₛ β) :
    support f = ⋃ y ∈ {y ∈ f.range | y ≠ 0}, f ⁻¹' {y} :=
  Set.ext fun x => by
    simp only [mem_support, Set.mem_preimage, mem_filter, mem_range_self, true_and, exists_prop,
      mem_iUnion, mem_singleton_iff, exists_eq_right']

variable {m : MeasurableSpace α} [Zero β] [Zero γ] {μ : Measure α} {f : α →ₛ β}

theorem measurableSet_support [MeasurableSpace α] (f : α →ₛ β) : MeasurableSet (support f) := by
  rw [f.support_eq]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_fiber _ _

lemma measure_support_lt_top (f : α →ₛ β) (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    μ (support f) < ∞ := by
  classical
  rw [support_eq]
  refine (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun y hy => ?_)
  rw [Finset.mem_filter] at hy
  exact hf y hy.2

/-- A `SimpleFunc` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
protected def FinMeasSupp {_m : MeasurableSpace α} (f : α →ₛ β) (μ : Measure α) : Prop :=
  f =ᶠ[μ.cofinite] 0

theorem finMeasSupp_iff_support : f.FinMeasSupp μ ↔ μ (support f) < ∞ :=
  Iff.rfl

theorem finMeasSupp_iff : f.FinMeasSupp μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ := by
  classical
  constructor
  · refine fun h y hy => lt_of_le_of_lt (measure_mono ?_) h
    exact fun x hx (H : f x = 0) => hy <| H ▸ Eq.symm hx
  · intro H
    rw [finMeasSupp_iff_support, support_eq]
    exact measure_biUnion_lt_top (finite_toSet _) fun y hy ↦ H y (mem_filter.1 hy).2

namespace FinMeasSupp

theorem meas_preimage_singleton_ne_zero (h : f.FinMeasSupp μ) {y : β} (hy : y ≠ 0) :
    μ (f ⁻¹' {y}) < ∞ :=
  finMeasSupp_iff.1 h y hy

protected theorem map {g : β → γ} (hf : f.FinMeasSupp μ) (hg : g 0 = 0) : (f.map g).FinMeasSupp μ :=
  flip lt_of_le_of_lt hf (measure_mono <| support_comp_subset hg f)

theorem of_map {g : β → γ} (h : (f.map g).FinMeasSupp μ) (hg : ∀ b, g b = 0 → b = 0) :
    f.FinMeasSupp μ :=
  flip lt_of_le_of_lt h <| measure_mono <| support_subset_comp @(hg) _

theorem map_iff {g : β → γ} (hg : ∀ {b}, g b = 0 ↔ b = 0) :
    (f.map g).FinMeasSupp μ ↔ f.FinMeasSupp μ :=
  ⟨fun h => h.of_map fun _ => hg.1, fun h => h.map <| hg.2 rfl⟩

protected theorem pair {g : α →ₛ γ} (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ) :
    (pair f g).FinMeasSupp μ :=
  calc
    μ (support <| pair f g) = μ (support f ∪ support g) := congr_arg μ <| support_prodMk f g
    _ ≤ μ (support f) + μ (support g) := measure_union_le _ _
    _ < _ := add_lt_top.2 ⟨hf, hg⟩

protected theorem map₂ [Zero δ] (hf : f.FinMeasSupp μ) {g : α →ₛ γ} (hg : g.FinMeasSupp μ)
    {op : β → γ → δ} (H : op 0 0 = 0) : ((pair f g).map (Function.uncurry op)).FinMeasSupp μ :=
  (hf.pair hg).map H

protected theorem add {β} [AddZeroClass β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f + g).FinMeasSupp μ := by
  rw [add_eq_map₂]
  exact hf.map₂ hg (zero_add 0)

protected theorem mul {β} [MulZeroClass β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f * g).FinMeasSupp μ := by
  rw [mul_eq_map₂]
  exact hf.map₂ hg (zero_mul 0)

theorem lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hm : f.FinMeasSupp μ) (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
    f.lintegral μ < ∞ := by
  refine sum_lt_top.2 fun a ha => ?_
  rcases eq_or_ne a ∞ with (rfl | ha)
  · simp only [ae_iff, Ne, Classical.not_not] at hf
    simp [Set.preimage, hf]
  · by_cases ha0 : a = 0
    · subst a
      simp
    · exact mul_lt_top ha.lt_top (finMeasSupp_iff.1 hm _ ha0)

theorem of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (h : f.lintegral μ ≠ ∞) : f.FinMeasSupp μ := by
  refine finMeasSupp_iff.2 fun b hb => ?_
  rw [f.lintegral_eq_of_subset' (Finset.subset_insert b _)] at h
  refine ENNReal.lt_top_of_mul_ne_top_right ?_ hb
  exact (lt_top_of_sum_ne_top h (Finset.mem_insert_self _ _)).ne

theorem iff_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
    f.FinMeasSupp μ ↔ f.lintegral μ < ∞ :=
  ⟨fun h => h.lintegral_lt_top hf, fun h => of_lintegral_ne_top h.ne⟩

end FinMeasSupp

lemma measure_support_lt_top_of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (hf : f.lintegral μ ≠ ∞) :
    μ (support f) < ∞ := by
  refine measure_support_lt_top f ?_
  rw [← finMeasSupp_iff]
  exact FinMeasSupp.of_lintegral_ne_top hf

end FinMeasSupp

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`).

To use in an induction proof, the syntax is `induction f using SimpleFunc.induction with`. -/
@[elab_as_elim]
protected theorem induction {α γ} [MeasurableSpace α] [AddZeroClass γ]
    {motive : SimpleFunc α γ → Prop}
    (const : ∀ (c) {s} (hs : MeasurableSet s),
      motive (SimpleFunc.piecewise s hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0)))
    (add : ∀ ⦃f g : SimpleFunc α γ⦄,
      Disjoint (support f) (support g) → motive f → motive g → motive (f + g))
    (f : SimpleFunc α γ) : motive f := by
  classical
  generalize h : f.range \ {0} = s
  rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty, diff_eq_empty, range_subset_singleton] at h
    convert const 0 MeasurableSet.univ
    ext x
    simp [h]
  | insert x s hxs ih =>
    have mx := f.measurableSet_preimage {x}
    let g := SimpleFunc.piecewise (f ⁻¹' {x}) mx 0 f
    have Pg : motive g := by
      apply ih
      simp only [g, SimpleFunc.coe_piecewise, range_piecewise]
      rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, h, Finset.coe_insert,
        insert_diff_self_of_notMem, diff_eq_empty.mpr, Set.empty_union]
      · rw [Set.image_subset_iff]
        convert Set.subset_univ _
        exact preimage_const_of_mem (mem_singleton _)
      · rwa [Finset.mem_coe]
    convert add _ Pg (const x mx)
    · ext1 y
      by_cases hy : y ∈ f ⁻¹' {x}
      · simpa [g, hy]
      · simp [g, hy]
    rw [disjoint_iff_inf_le]
    rintro y
    by_cases hy : y ∈ f ⁻¹' {x} <;> simp [g, hy]

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for constant functions and that it is closed under piecewise combinations
of functions.

To use in an induction proof, the syntax is `induction f with`. -/
@[induction_eliminator]
protected theorem induction' {α γ} [MeasurableSpace α] [Nonempty γ] {P : SimpleFunc α γ → Prop}
    (const : ∀ (c), P (SimpleFunc.const _ c))
    (pcw : ∀ ⦃f g : SimpleFunc α γ⦄ {s} (hs : MeasurableSet s), P f → P g →
      P (f.piecewise s hs g))
    (f : SimpleFunc α γ) : P f := by
  let c : γ := Classical.ofNonempty
  classical
  generalize h : f.range \ {c} = s
  rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at h
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty, diff_eq_empty, range_subset_singleton] at h
    convert const c
    ext x
    simp [h]
  | insert x s hxs ih =>
    have mx := f.measurableSet_preimage {x}
    let g := SimpleFunc.piecewise (f ⁻¹' {x}) mx (SimpleFunc.const α c) f
    have Pg : P g := by
      apply ih
      simp only [g, SimpleFunc.coe_piecewise, range_piecewise]
      rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, h, Finset.coe_insert,
        insert_diff_self_of_notMem, diff_eq_empty.mpr, Set.empty_union]
      · rw [Set.image_subset_iff]
        convert Set.subset_univ _
        exact preimage_const_of_mem (mem_singleton _)
      · rwa [Finset.mem_coe]
    convert pcw mx.compl Pg (const x)
    · ext1 y
      by_cases hy : y ∈ f ⁻¹' {x}
      · simpa [g, hy]
      · simp [g, hy]

/-- In a topological vector space, the addition of a measurable function and a simple function is
measurable. -/
theorem _root_.Measurable.add_simpleFunc
    {E : Type*} {_ : MeasurableSpace α} [MeasurableSpace E] [AddCancelMonoid E] [MeasurableAdd E]
    {g : α → E} (hg : Measurable g) (f : SimpleFunc α E) :
    Measurable (g + (f : α → E)) := by
  classical
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero]
    rw [← s.piecewise_same g, ← piecewise_add]
    exact Measurable.piecewise hs (hg.add_const _) (hg.add_const _)
  | @add f f' hff' hf hf' =>
    have : (g + ↑(f + f')) = (Function.support f).piecewise (g + (f : α → E)) (g + f') := by
      ext x
      by_cases hx : x ∈ Function.support f
      · simpa only [SimpleFunc.coe_add, Pi.add_apply, Function.mem_support, ne_eq, not_not,
          Set.piecewise_eq_of_mem _ _ _ hx, _root_.add_right_inj, add_eq_left]
          using Set.disjoint_left.1 hff' hx
      · simpa only [SimpleFunc.coe_add, Pi.add_apply, Function.mem_support, ne_eq, not_not,
          Set.piecewise_eq_of_notMem _ _ _ hx, _root_.add_right_inj, add_eq_right] using hx
    rw [this]
    exact Measurable.piecewise f.measurableSet_support hf hf'

/-- In a topological vector space, the addition of a simple function and a measurable function is
measurable. -/
theorem _root_.Measurable.simpleFunc_add
    {E : Type*} {_ : MeasurableSpace α} [MeasurableSpace E] [AddCancelMonoid E] [MeasurableAdd E]
    {g : α → E} (hg : Measurable g) (f : SimpleFunc α E) :
    Measurable ((f : α → E) + g) := by
  classical
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero]
    rw [← s.piecewise_same g, ← piecewise_add]
    exact Measurable.piecewise hs (hg.const_add _) (hg.const_add _)
  | @add f f' hff' hf hf' =>
    have : (↑(f + f') + g) = (Function.support f).piecewise ((f : α → E) + g) (f' + g) := by
      ext x
      by_cases hx : x ∈ Function.support f
      · simpa only [coe_add, Pi.add_apply, Function.mem_support, ne_eq, not_not,
          Set.piecewise_eq_of_mem _ _ _ hx, _root_.add_left_inj, add_eq_left]
          using Set.disjoint_left.1 hff' hx
      · simpa only [SimpleFunc.coe_add, Pi.add_apply, Function.mem_support, ne_eq, not_not,
          Set.piecewise_eq_of_notMem _ _ _ hx, _root_.add_left_inj, add_eq_right] using hx
    rw [this]
    exact Measurable.piecewise f.measurableSet_support hf hf'

end SimpleFunc

end MeasureTheory

open MeasureTheory MeasureTheory.SimpleFunc

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_elim]
theorem Measurable.ennreal_induction {motive : (α → ℝ≥0∞) → Prop}
    (indicator : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → motive (Set.indicator s fun _ => c))
    (add : ∀ ⦃f g : α → ℝ≥0∞⦄, Disjoint (support f) (support g) →
      Measurable f → Measurable g → motive f → motive g → motive (f + g))
    (iSup : ∀ ⦃f : ℕ → α → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f →
      (∀ n, motive (f n)) → motive fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : motive f := by
  convert iSup (fun n => (eapprox f n).measurable) (monotone_eapprox f) _ using 2
  · rw [iSup_eapprox_apply hf]
  · exact fun n =>
      SimpleFunc.induction (fun c s hs => indicator c hs)
        (fun f g hfg hf hg => add hfg f.measurable g.measurable hf hg) (eapprox f n)

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions with finite mass according to
some sigma-finite measure and is closed under addition and supremum of increasing sequences of
functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_elim]
lemma Measurable.ennreal_sigmaFinite_induction [SigmaFinite μ] {motive : (α → ℝ≥0∞) → Prop}
    (indicator : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → μ s < ∞ → motive (Set.indicator s fun _ ↦ c))
    (add : ∀ ⦃f g : α → ℝ≥0∞⦄, Disjoint (support f) (support g) →
      Measurable f → Measurable g → motive f → motive g → motive (f + g))
    (iSup : ∀ ⦃f : ℕ → α → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f →
      (∀ n, motive (f n)) → motive fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : motive f := by
  refine Measurable.ennreal_induction (fun c s hs ↦ ?_) add iSup hf
  convert iSup (f := fun n ↦ (s ∩ spanningSets μ n).indicator fun _ ↦ c)
    (fun n ↦ measurable_const.indicator (hs.inter (measurableSet_spanningSets ..)))
    (fun m n hmn a ↦ by dsimp; grw [hmn])
    (fun n ↦ indicator _ (hs.inter (measurableSet_spanningSets ..))
      (measure_inter_lt_top_of_right_ne_top (measure_spanningSets_lt_top ..).ne)) with a
  simp [← Set.indicator_iUnion_apply (M := ℝ≥0∞) rfl, ← Set.inter_iUnion]
