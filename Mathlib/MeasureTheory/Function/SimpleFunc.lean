/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.IndicatorFunction
import Mathlib.Algebra.Support

#align_import measure_theory.function.simple_func from "leanprover-community/mathlib"@"bf6a01357ff5684b1ebcd0f1a13be314fc82c0bf"

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


noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open Classical Topology BigOperators NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α β γ δ : Type*}

/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure SimpleFunc.{u, v} (α : Type u) [MeasurableSpace α] (β : Type v) where
  toFun : α → β
  measurableSet_fiber' : ∀ x, MeasurableSet (toFun ⁻¹' {x})
  finite_range' : (Set.range toFun).Finite
#align measure_theory.simple_func MeasureTheory.SimpleFunc
#align measure_theory.simple_func.to_fun MeasureTheory.SimpleFunc.toFun
#align measure_theory.simple_func.measurable_set_fiber' MeasureTheory.SimpleFunc.measurableSet_fiber'
#align measure_theory.simple_func.finite_range' MeasureTheory.SimpleFunc.finite_range'

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section Measurable

variable [MeasurableSpace α]

attribute [coe] toFun

instance instCoeFun : CoeFun (α →ₛ β) fun _ => α → β :=
  ⟨toFun⟩
#align measure_theory.simple_func.has_coe_to_fun MeasureTheory.SimpleFunc.instCoeFun

theorem coe_injective ⦃f g : α →ₛ β⦄ (H : (f : α → β) = g) : f = g := by
  cases f; cases g; congr
  -- ⊢ { toFun := toFun✝, measurableSet_fiber' := measurableSet_fiber'✝, finite_ran …
           -- ⊢ { toFun := toFun✝¹, measurableSet_fiber' := measurableSet_fiber'✝¹, finite_r …
                    -- 🎉 no goals
#align measure_theory.simple_func.coe_injective MeasureTheory.SimpleFunc.coe_injective

@[ext]
theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
  coe_injective <| funext H
#align measure_theory.simple_func.ext MeasureTheory.SimpleFunc.ext

theorem finite_range (f : α →ₛ β) : (Set.range f).Finite :=
  f.finite_range'
#align measure_theory.simple_func.finite_range MeasureTheory.SimpleFunc.finite_range

theorem measurableSet_fiber (f : α →ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x}) :=
  f.measurableSet_fiber' x
#align measure_theory.simple_func.measurable_set_fiber MeasureTheory.SimpleFunc.measurableSet_fiber

-- @[simp] -- Porting note: simp can prove this
theorem apply_mk (f : α → β) (h h') (x : α) : SimpleFunc.mk f h h' x = f x :=
  rfl
#align measure_theory.simple_func.apply_mk MeasureTheory.SimpleFunc.apply_mk

/-- Simple function defined on the empty type. -/
def ofIsEmpty [IsEmpty α] : α →ₛ β where
  toFun := isEmptyElim
  measurableSet_fiber' x := Subsingleton.measurableSet
  finite_range' := by simp [range_eq_empty]
                      -- 🎉 no goals
#align measure_theory.simple_func.of_is_empty MeasureTheory.SimpleFunc.ofIsEmpty

/-- Range of a simple function `α →ₛ β` as a `Finset β`. -/
protected def range (f : α →ₛ β) : Finset β :=
  f.finite_range.toFinset
#align measure_theory.simple_func.range MeasureTheory.SimpleFunc.range

@[simp]
theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
  Finite.mem_toFinset _
#align measure_theory.simple_func.mem_range MeasureTheory.SimpleFunc.mem_range

theorem mem_range_self (f : α →ₛ β) (x : α) : f x ∈ f.range :=
  mem_range.2 ⟨x, rfl⟩
#align measure_theory.simple_func.mem_range_self MeasureTheory.SimpleFunc.mem_range_self

@[simp]
theorem coe_range (f : α →ₛ β) : (↑f.range : Set β) = Set.range f :=
  f.finite_range.coe_toFinset
#align measure_theory.simple_func.coe_range MeasureTheory.SimpleFunc.coe_range

theorem mem_range_of_measure_ne_zero {f : α →ₛ β} {x : β} {μ : Measure α} (H : μ (f ⁻¹' {x}) ≠ 0) :
    x ∈ f.range :=
  let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H
  mem_range.2 ⟨a, ha⟩
#align measure_theory.simple_func.mem_range_of_measure_ne_zero MeasureTheory.SimpleFunc.mem_range_of_measure_ne_zero

theorem forall_range_iff {f : α →ₛ β} {p : β → Prop} : (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) := by
  simp only [mem_range, Set.forall_range_iff]
  -- 🎉 no goals
#align measure_theory.simple_func.forall_range_iff MeasureTheory.SimpleFunc.forall_range_iff

theorem exists_range_iff {f : α →ₛ β} {p : β → Prop} : (∃ y ∈ f.range, p y) ↔ ∃ x, p (f x) := by
  simpa only [mem_range, exists_prop] using Set.exists_range_iff
  -- 🎉 no goals
#align measure_theory.simple_func.exists_range_iff MeasureTheory.SimpleFunc.exists_range_iff

theorem preimage_eq_empty_iff (f : α →ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
  preimage_singleton_eq_empty.trans <| not_congr mem_range.symm
#align measure_theory.simple_func.preimage_eq_empty_iff MeasureTheory.SimpleFunc.preimage_eq_empty_iff

theorem exists_forall_le [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)] (f : α →ₛ β) :
    ∃ C, ∀ x, f x ≤ C :=
  f.range.exists_le.imp fun _ => forall_range_iff.1
#align measure_theory.simple_func.exists_forall_le MeasureTheory.SimpleFunc.exists_forall_le

/-- Constant function as a `SimpleFunc`. -/
def const (α) {β} [MeasurableSpace α] (b : β) : α →ₛ β :=
  ⟨fun _ => b, fun _ => MeasurableSet.const _, finite_range_const⟩
#align measure_theory.simple_func.const MeasureTheory.SimpleFunc.const

instance instInhabited [Inhabited β] : Inhabited (α →ₛ β) :=
  ⟨const _ default⟩
#align measure_theory.simple_func.inhabited MeasureTheory.SimpleFunc.instInhabited

theorem const_apply (a : α) (b : β) : (const α b) a = b :=
  rfl
#align measure_theory.simple_func.const_apply MeasureTheory.SimpleFunc.const_apply

@[simp]
theorem coe_const (b : β) : ⇑(const α b) = Function.const α b :=
  rfl
#align measure_theory.simple_func.coe_const MeasureTheory.SimpleFunc.coe_const

@[simp]
theorem range_const (α) [MeasurableSpace α] [Nonempty α] (b : β) : (const α b).range = {b} :=
  Finset.coe_injective <| by simp [Function.const]
                             -- 🎉 no goals
#align measure_theory.simple_func.range_const MeasureTheory.SimpleFunc.range_const

theorem range_const_subset (α) [MeasurableSpace α] (b : β) : (const α b).range ⊆ {b} :=
  Finset.coe_subset.1 <| by simp
                            -- 🎉 no goals
#align measure_theory.simple_func.range_const_subset MeasureTheory.SimpleFunc.range_const_subset

theorem simpleFunc_bot {α} (f : @SimpleFunc α ⊥ β) [Nonempty β] : ∃ c, ∀ x, f x = c := by
  have hf_meas := @SimpleFunc.measurableSet_fiber α _ ⊥ f
  -- ⊢ ∃ c, ∀ (x : α), ↑f x = c
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hf_meas
  -- ⊢ ∃ c, ∀ (x : α), ↑f x = c
  cases' isEmpty_or_nonempty α with h h
  -- ⊢ ∃ c, ∀ (x : α), ↑f x = c
  · simp only [IsEmpty.forall_iff, exists_const]
    -- 🎉 no goals
  · specialize hf_meas (f h.some)
    -- ⊢ ∃ c, ∀ (x : α), ↑f x = c
    cases' hf_meas with hf_meas hf_meas
    -- ⊢ ∃ c, ∀ (x : α), ↑f x = c
    · exfalso
      -- ⊢ False
      refine' Set.not_mem_empty h.some _
      -- ⊢ Nonempty.some h ∈ ∅
      rw [← hf_meas, Set.mem_preimage]
      -- ⊢ ↑f (Nonempty.some h) ∈ {↑f (Nonempty.some h)}
      exact Set.mem_singleton _
      -- 🎉 no goals
    · refine' ⟨f h.some, fun x => _⟩
      -- ⊢ ↑f x = ↑f (Nonempty.some h)
      have : x ∈ f ⁻¹' {f h.some} := by
        rw [hf_meas]
        exact Set.mem_univ x
      rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
      -- 🎉 no goals
#align measure_theory.simple_func.simple_func_bot MeasureTheory.SimpleFunc.simpleFunc_bot

theorem simpleFunc_bot' {α} [Nonempty β] (f : @SimpleFunc α ⊥ β) :
    ∃ c, f = @SimpleFunc.const α _ ⊥ c := by
  letI : MeasurableSpace α := ⊥
  -- ⊢ ∃ c, f = const α c
  obtain ⟨c, h_eq⟩ := simpleFunc_bot f
  -- ⊢ ∃ c, f = const α c
  refine' ⟨c, _⟩
  -- ⊢ f = const α c
  ext1 x
  -- ⊢ ↑f x = ↑(const α c) x
  rw [h_eq x, SimpleFunc.coe_const, Function.const]
  -- 🎉 no goals
#align measure_theory.simple_func.simple_func_bot' MeasureTheory.SimpleFunc.simpleFunc_bot'

theorem measurableSet_cut (r : α → β → Prop) (f : α →ₛ β) (h : ∀ b, MeasurableSet { a | r a b }) :
    MeasurableSet { a | r a (f a) } := by
  have : { a | r a (f a) } = ⋃ b ∈ range f, { a | r a b } ∩ f ⁻¹' {b} := by
    ext a
    suffices r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i by simpa
    exact ⟨fun h => ⟨a, ⟨h, rfl⟩⟩, fun ⟨a', ⟨h', e⟩⟩ => e.symm ▸ h'⟩
  rw [this]
  -- ⊢ MeasurableSet (⋃ (b : β) (_ : b ∈ range ↑f), {a | r a b} ∩ ↑f ⁻¹' {b})
  exact
    MeasurableSet.biUnion f.finite_range.countable fun b _ =>
      MeasurableSet.inter (h b) (f.measurableSet_fiber _)
#align measure_theory.simple_func.measurable_set_cut MeasureTheory.SimpleFunc.measurableSet_cut

@[measurability]
theorem measurableSet_preimage (f : α →ₛ β) (s) : MeasurableSet (f ⁻¹' s) :=
  measurableSet_cut (fun _ b => b ∈ s) f fun b => MeasurableSet.const (b ∈ s)
#align measure_theory.simple_func.measurable_set_preimage MeasureTheory.SimpleFunc.measurableSet_preimage

/-- A simple function is measurable -/
@[measurability]
protected theorem measurable [MeasurableSpace β] (f : α →ₛ β) : Measurable f := fun s _ =>
  measurableSet_preimage f s
#align measure_theory.simple_func.measurable MeasureTheory.SimpleFunc.measurable

@[measurability]
protected theorem aemeasurable [MeasurableSpace β] {μ : Measure α} (f : α →ₛ β) :
    AEMeasurable f μ :=
  f.measurable.aemeasurable
#align measure_theory.simple_func.ae_measurable MeasureTheory.SimpleFunc.aemeasurable

protected theorem sum_measure_preimage_singleton (f : α →ₛ β) {μ : Measure α} (s : Finset β) :
    (∑ y in s, μ (f ⁻¹' {y})) = μ (f ⁻¹' ↑s) :=
  sum_measure_preimage_singleton _ fun _ _ => f.measurableSet_fiber _
#align measure_theory.simple_func.sum_measure_preimage_singleton MeasureTheory.SimpleFunc.sum_measure_preimage_singleton

theorem sum_range_measure_preimage_singleton (f : α →ₛ β) (μ : Measure α) :
    (∑ y in f.range, μ (f ⁻¹' {y})) = μ univ := by
  rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]
  -- 🎉 no goals
#align measure_theory.simple_func.sum_range_measure_preimage_singleton MeasureTheory.SimpleFunc.sum_range_measure_preimage_singleton

/-- If-then-else as a `SimpleFunc`. -/
def piecewise (s : Set α) (hs : MeasurableSet s) (f g : α →ₛ β) : α →ₛ β :=
  ⟨s.piecewise f g, fun _ =>
    letI : MeasurableSpace β := ⊤
    f.measurable.piecewise hs g.measurable trivial,
    (f.finite_range.union g.finite_range).subset range_ite_subset⟩
#align measure_theory.simple_func.piecewise MeasureTheory.SimpleFunc.piecewise

@[simp]
theorem coe_piecewise {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) :
    ⇑(piecewise s hs f g) = s.piecewise f g :=
  rfl
#align measure_theory.simple_func.coe_piecewise MeasureTheory.SimpleFunc.coe_piecewise

theorem piecewise_apply {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) (a) :
    piecewise s hs f g a = if a ∈ s then f a else g a :=
  rfl
#align measure_theory.simple_func.piecewise_apply MeasureTheory.SimpleFunc.piecewise_apply

@[simp]
theorem piecewise_compl {s : Set α} (hs : MeasurableSet sᶜ) (f g : α →ₛ β) :
    piecewise sᶜ hs f g = piecewise s hs.of_compl g f :=
  coe_injective <| by simp [hs]; convert Set.piecewise_compl s f g
                      -- ⊢ Set.piecewise sᶜ ↑f ↑g = Set.piecewise s ↑g ↑f
                                 -- 🎉 no goals
#align measure_theory.simple_func.piecewise_compl MeasureTheory.SimpleFunc.piecewise_compl

@[simp]
theorem piecewise_univ (f g : α →ₛ β) : piecewise univ MeasurableSet.univ f g = f :=
  coe_injective <| by simp; convert Set.piecewise_univ f g
                      -- ⊢ Set.piecewise univ ↑f ↑g = ↑f
                            -- 🎉 no goals
#align measure_theory.simple_func.piecewise_univ MeasureTheory.SimpleFunc.piecewise_univ

@[simp]
theorem piecewise_empty (f g : α →ₛ β) : piecewise ∅ MeasurableSet.empty f g = g :=
  coe_injective <| by simp; convert Set.piecewise_empty f g
                      -- ⊢ Set.piecewise ∅ ↑f ↑g = ↑g
                            -- 🎉 no goals
#align measure_theory.simple_func.piecewise_empty MeasureTheory.SimpleFunc.piecewise_empty

theorem support_indicator [Zero β] {s : Set α} (hs : MeasurableSet s) (f : α →ₛ β) :
    Function.support (f.piecewise s hs (SimpleFunc.const α 0)) = s ∩ Function.support f :=
  Set.support_indicator
#align measure_theory.simple_func.support_indicator MeasureTheory.SimpleFunc.support_indicator

theorem range_indicator {s : Set α} (hs : MeasurableSet s) (hs_nonempty : s.Nonempty)
    (hs_ne_univ : s ≠ univ) (x y : β) :
    (piecewise s hs (const α x) (const α y)).range = {x, y} := by
  simp only [← Finset.coe_inj, coe_range, coe_piecewise, range_piecewise, coe_const,
    Finset.coe_insert, Finset.coe_singleton, hs_nonempty.image_const,
    (nonempty_compl.2 hs_ne_univ).image_const, singleton_union, Function.const]
#align measure_theory.simple_func.range_indicator MeasureTheory.SimpleFunc.range_indicator

theorem measurable_bind [MeasurableSpace γ] (f : α →ₛ β) (g : β → α → γ)
    (hg : ∀ b, Measurable (g b)) : Measurable fun a => g (f a) a := fun s hs =>
  f.measurableSet_cut (fun a b => g b a ∈ s) fun b => hg b hs
#align measure_theory.simple_func.measurable_bind MeasureTheory.SimpleFunc.measurable_bind

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
  ⟨fun a => g (f a) a, fun c =>
    f.measurableSet_cut (fun a b => g b a = c) fun b => (g b).measurableSet_preimage {c},
    (f.finite_range.biUnion fun b _ => (g b).finite_range).subset <| by
      rintro _ ⟨a, rfl⟩; simp; exact ⟨a, a, rfl⟩⟩
      -- ⊢ (fun a => ↑(g (↑f a)) a) a ∈ ⋃ (i : β) (_ : i ∈ range ↑f), range ↑(g i)
                         -- ⊢ ∃ i y, ↑(g (↑f i)) y = ↑(g (↑f a)) a
                               -- 🎉 no goals
#align measure_theory.simple_func.bind MeasureTheory.SimpleFunc.bind

@[simp]
theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) : f.bind g a = g (f a) a :=
  rfl
#align measure_theory.simple_func.bind_apply MeasureTheory.SimpleFunc.bind_apply

/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
    function `g ∘ f : α →ₛ γ` -/
def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ :=
  bind f (const α ∘ g)
#align measure_theory.simple_func.map MeasureTheory.SimpleFunc.map

theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) :=
  rfl
#align measure_theory.simple_func.map_apply MeasureTheory.SimpleFunc.map_apply

theorem map_map (g : β → γ) (h : γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) :=
  rfl
#align measure_theory.simple_func.map_map MeasureTheory.SimpleFunc.map_map

@[simp]
theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = g ∘ f :=
  rfl
#align measure_theory.simple_func.coe_map MeasureTheory.SimpleFunc.coe_map

@[simp]
theorem range_map [DecidableEq γ] (g : β → γ) (f : α →ₛ β) : (f.map g).range = f.range.image g :=
  Finset.coe_injective <| by simp only [coe_range, coe_map, Finset.coe_image, range_comp]
                             -- 🎉 no goals
#align measure_theory.simple_func.range_map MeasureTheory.SimpleFunc.range_map

@[simp]
theorem map_const (g : β → γ) (b : β) : (const α b).map g = const α (g b) :=
  rfl
#align measure_theory.simple_func.map_const MeasureTheory.SimpleFunc.map_const

theorem map_preimage (f : α →ₛ β) (g : β → γ) (s : Set γ) :
    f.map g ⁻¹' s = f ⁻¹' ↑(f.range.filter fun b => g b ∈ s) := by
  simp only [coe_range, sep_mem_eq, coe_map, Finset.coe_filter,
    ← mem_preimage, inter_comm, preimage_inter_range, ← Finset.mem_coe]
  exact preimage_comp
  -- 🎉 no goals
#align measure_theory.simple_func.map_preimage MeasureTheory.SimpleFunc.map_preimage

theorem map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
    f.map g ⁻¹' {c} = f ⁻¹' ↑(f.range.filter fun b => g b = c) :=
  map_preimage _ _ _
#align measure_theory.simple_func.map_preimage_singleton MeasureTheory.SimpleFunc.map_preimage_singleton

/-- Composition of a `SimpleFun` and a measurable function is a `SimpleFunc`. -/
def comp [MeasurableSpace β] (f : β →ₛ γ) (g : α → β) (hgm : Measurable g) : α →ₛ γ where
  toFun := f ∘ g
  finite_range' := f.finite_range.subset <| Set.range_comp_subset_range _ _
  measurableSet_fiber' z := hgm (f.measurableSet_fiber z)
#align measure_theory.simple_func.comp MeasureTheory.SimpleFunc.comp

@[simp]
theorem coe_comp [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
    ⇑(f.comp g hgm) = f ∘ g :=
  rfl
#align measure_theory.simple_func.coe_comp MeasureTheory.SimpleFunc.coe_comp

theorem range_comp_subset_range [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
    (f.comp g hgm).range ⊆ f.range :=
  Finset.coe_subset.1 <| by simp only [coe_range, coe_comp, Set.range_comp_subset_range]
                            -- 🎉 no goals
#align measure_theory.simple_func.range_comp_subset_range MeasureTheory.SimpleFunc.range_comp_subset_range

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
    -- ⊢ ∀ (x : γ), MeasurableSet (Function.extend g ↑f₁ ↑f₂ ⁻¹' {x})
                                   -- ⊢ ∀ (x : γ), MeasurableSet (Function.extend g ↑f₁ ↑f₂ ⁻¹' {x})
    exact fun x => hg.measurable_extend f₁.measurable f₂.measurable (measurableSet_singleton _)
    -- 🎉 no goals
#align measure_theory.simple_func.extend MeasureTheory.SimpleFunc.extend

@[simp]
theorem extend_apply [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) (x : α) : (f₁.extend g hg f₂) (g x) = f₁ x :=
  hg.injective.extend_apply _ _ _
#align measure_theory.simple_func.extend_apply MeasureTheory.SimpleFunc.extend_apply

@[simp]
theorem extend_apply' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) {y : β} (h : ¬∃ x, g x = y) : (f₁.extend g hg f₂) y = f₂ y :=
  Function.extend_apply' _ _ _ h
#align measure_theory.simple_func.extend_apply' MeasureTheory.SimpleFunc.extend_apply'

@[simp]
theorem extend_comp_eq' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : f₁.extend g hg f₂ ∘ g = f₁ :=
  funext fun _ => extend_apply _ _ _ _
#align measure_theory.simple_func.extend_comp_eq' MeasureTheory.SimpleFunc.extend_comp_eq'

@[simp]
theorem extend_comp_eq [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g)
    (f₂ : β →ₛ γ) : (f₁.extend g hg f₂).comp g hg.measurable = f₁ :=
  coe_injective <| extend_comp_eq' _ hg _
#align measure_theory.simple_func.extend_comp_eq MeasureTheory.SimpleFunc.extend_comp_eq

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq (f : α →ₛ β → γ) (g : α →ₛ β) : α →ₛ γ :=
  f.bind fun f => g.map f
#align measure_theory.simple_func.seq MeasureTheory.SimpleFunc.seq

@[simp]
theorem seq_apply (f : α →ₛ β → γ) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) :=
  rfl
#align measure_theory.simple_func.seq_apply MeasureTheory.SimpleFunc.seq_apply

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `fun a => (f a, g a)`. -/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ β × γ :=
  (f.map Prod.mk).seq g
#align measure_theory.simple_func.pair MeasureTheory.SimpleFunc.pair

@[simp]
theorem pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) :=
  rfl
#align measure_theory.simple_func.pair_apply MeasureTheory.SimpleFunc.pair_apply

theorem pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : Set β) (t : Set γ) :
    pair f g ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl
#align measure_theory.simple_func.pair_preimage MeasureTheory.SimpleFunc.pair_preimage

-- A special form of `pair_preimage`
theorem pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
    pair f g ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} := by
  rw [← singleton_prod_singleton]
  -- ⊢ ↑(pair f g) ⁻¹' {b} ×ˢ {c} = ↑f ⁻¹' {b} ∩ ↑g ⁻¹' {c}
  exact pair_preimage _ _ _ _
  -- 🎉 no goals
#align measure_theory.simple_func.pair_preimage_singleton MeasureTheory.SimpleFunc.pair_preimage_singleton

theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext; simp
                                                             -- ⊢ ↑(bind f (const α)) a✝ = ↑f a✝
                                                                  -- 🎉 no goals
#align measure_theory.simple_func.bind_const MeasureTheory.SimpleFunc.bind_const

@[to_additive]
instance instOne [One β] : One (α →ₛ β) :=
  ⟨const α 1⟩
#align measure_theory.simple_func.has_one MeasureTheory.SimpleFunc.instOne
#align measure_theory.simple_func.has_zero MeasureTheory.SimpleFunc.instZero

@[to_additive]
instance instMul [Mul β] : Mul (α →ₛ β) :=
  ⟨fun f g => (f.map (· * ·)).seq g⟩
#align measure_theory.simple_func.has_mul MeasureTheory.SimpleFunc.instMul
#align measure_theory.simple_func.has_add MeasureTheory.SimpleFunc.instAdd

@[to_additive]
instance instDiv [Div β] : Div (α →ₛ β) :=
  ⟨fun f g => (f.map (· / ·)).seq g⟩
#align measure_theory.simple_func.has_div MeasureTheory.SimpleFunc.instDiv
#align measure_theory.simple_func.has_sub MeasureTheory.SimpleFunc.instSub

@[to_additive]
instance instInv [Inv β] : Inv (α →ₛ β) :=
  ⟨fun f => f.map Inv.inv⟩
#align measure_theory.simple_func.has_inv MeasureTheory.SimpleFunc.instInv
#align measure_theory.simple_func.has_neg MeasureTheory.SimpleFunc.instNeg

instance instSup [Sup β] : Sup (α →ₛ β) :=
  ⟨fun f g => (f.map (· ⊔ ·)).seq g⟩
#align measure_theory.simple_func.has_sup MeasureTheory.SimpleFunc.instSup

instance instInf [Inf β] : Inf (α →ₛ β) :=
  ⟨fun f g => (f.map (· ⊓ ·)).seq g⟩
#align measure_theory.simple_func.has_inf MeasureTheory.SimpleFunc.instInf

instance instLE [LE β] : LE (α →ₛ β) :=
  ⟨fun f g => ∀ a, f a ≤ g a⟩
#align measure_theory.simple_func.has_le MeasureTheory.SimpleFunc.instLE

@[to_additive (attr := simp)]
theorem const_one [One β] : const α (1 : β) = 1 :=
  rfl
#align measure_theory.simple_func.const_one MeasureTheory.SimpleFunc.const_one
#align measure_theory.simple_func.const_zero MeasureTheory.SimpleFunc.const_zero

@[to_additive (attr := simp, norm_cast)]
theorem coe_one [One β] : ⇑(1 : α →ₛ β) = 1 :=
  rfl
#align measure_theory.simple_func.coe_one MeasureTheory.SimpleFunc.coe_one
#align measure_theory.simple_func.coe_zero MeasureTheory.SimpleFunc.coe_zero

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul [Mul β] (f g : α →ₛ β) : ⇑(f * g) = ⇑f * ⇑g :=
  rfl
#align measure_theory.simple_func.coe_mul MeasureTheory.SimpleFunc.coe_mul
#align measure_theory.simple_func.coe_add MeasureTheory.SimpleFunc.coe_add

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv [Inv β] (f : α →ₛ β) : ⇑(f⁻¹) = (⇑f)⁻¹ :=
  rfl
#align measure_theory.simple_func.coe_inv MeasureTheory.SimpleFunc.coe_inv
#align measure_theory.simple_func.coe_neg MeasureTheory.SimpleFunc.coe_neg

@[to_additive (attr := simp, norm_cast)]
theorem coe_div [Div β] (f g : α →ₛ β) : ⇑(f / g) = ⇑f / ⇑g :=
  rfl
#align measure_theory.simple_func.coe_div MeasureTheory.SimpleFunc.coe_div
#align measure_theory.simple_func.coe_sub MeasureTheory.SimpleFunc.coe_sub

@[simp, norm_cast]
theorem coe_le [Preorder β] {f g : α →ₛ β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl
#align measure_theory.simple_func.coe_le MeasureTheory.SimpleFunc.coe_le

@[simp, norm_cast]
theorem coe_sup [Sup β] (f g : α →ₛ β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl
#align measure_theory.simple_func.coe_sup MeasureTheory.SimpleFunc.coe_sup

@[simp, norm_cast]
theorem coe_inf [Inf β] (f g : α →ₛ β) : ⇑(f ⊓ g) = ⇑f ⊓ ⇑g :=
  rfl
#align measure_theory.simple_func.coe_inf MeasureTheory.SimpleFunc.coe_inf

@[to_additive]
theorem mul_apply [Mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a :=
  rfl
#align measure_theory.simple_func.mul_apply MeasureTheory.SimpleFunc.mul_apply
#align measure_theory.simple_func.add_apply MeasureTheory.SimpleFunc.add_apply

@[to_additive]
theorem div_apply [Div β] (f g : α →ₛ β) (x : α) : (f / g) x = f x / g x :=
  rfl
#align measure_theory.simple_func.div_apply MeasureTheory.SimpleFunc.div_apply
#align measure_theory.simple_func.sub_apply MeasureTheory.SimpleFunc.sub_apply

@[to_additive]
theorem inv_apply [Inv β] (f : α →ₛ β) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align measure_theory.simple_func.inv_apply MeasureTheory.SimpleFunc.inv_apply
#align measure_theory.simple_func.neg_apply MeasureTheory.SimpleFunc.neg_apply

theorem sup_apply [Sup β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl
#align measure_theory.simple_func.sup_apply MeasureTheory.SimpleFunc.sup_apply

theorem inf_apply [Inf β] (f g : α →ₛ β) (a : α) : (f ⊓ g) a = f a ⊓ g a :=
  rfl
#align measure_theory.simple_func.inf_apply MeasureTheory.SimpleFunc.inf_apply

@[to_additive (attr := simp)]
theorem range_one [Nonempty α] [One β] : (1 : α →ₛ β).range = {1} :=
  Finset.ext fun x => by simp [eq_comm]
                         -- 🎉 no goals
#align measure_theory.simple_func.range_one MeasureTheory.SimpleFunc.range_one
#align measure_theory.simple_func.range_zero MeasureTheory.SimpleFunc.range_zero

@[simp]
theorem range_eq_empty_of_isEmpty {β} [hα : IsEmpty α] (f : α →ₛ β) : f.range = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  -- ⊢ ¬Finset.Nonempty (SimpleFunc.range f)
  by_contra h
  -- ⊢ False
  obtain ⟨y, hy_mem⟩ := h
  -- ⊢ False
  rw [SimpleFunc.mem_range, Set.mem_range] at hy_mem
  -- ⊢ False
  obtain ⟨x, hxy⟩ := hy_mem
  -- ⊢ False
  rw [isEmpty_iff] at hα
  -- ⊢ False
  exact hα x
  -- 🎉 no goals
#align measure_theory.simple_func.range_eq_empty_of_is_empty MeasureTheory.SimpleFunc.range_eq_empty_of_isEmpty

theorem eq_zero_of_mem_range_zero [Zero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
  @(forall_range_iff.2 fun _ => rfl)
#align measure_theory.simple_func.eq_zero_of_mem_range_zero MeasureTheory.SimpleFunc.eq_zero_of_mem_range_zero

@[to_additive]
theorem mul_eq_map₂ [Mul β] (f g : α →ₛ β) : f * g = (pair f g).map fun p : β × β => p.1 * p.2 :=
  rfl
#align measure_theory.simple_func.mul_eq_map₂ MeasureTheory.SimpleFunc.mul_eq_map₂
#align measure_theory.simple_func.add_eq_map₂ MeasureTheory.SimpleFunc.add_eq_map₂

theorem sup_eq_map₂ [Sup β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map fun p : β × β => p.1 ⊔ p.2 :=
  rfl
#align measure_theory.simple_func.sup_eq_map₂ MeasureTheory.SimpleFunc.sup_eq_map₂

@[to_additive]
theorem const_mul_eq_map [Mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map fun a => b * a :=
  rfl
#align measure_theory.simple_func.const_mul_eq_map MeasureTheory.SimpleFunc.const_mul_eq_map
#align measure_theory.simple_func.const_add_eq_map MeasureTheory.SimpleFunc.const_add_eq_map

@[to_additive]
theorem map_mul [Mul β] [Mul γ] {g : β → γ} (hg : ∀ x y, g (x * y) = g x * g y) (f₁ f₂ : α →ₛ β) :
    (f₁ * f₂).map g = f₁.map g * f₂.map g :=
  ext fun _ => hg _ _
#align measure_theory.simple_func.map_mul MeasureTheory.SimpleFunc.map_mul
#align measure_theory.simple_func.map_add MeasureTheory.SimpleFunc.map_add

variable {K : Type*}

instance instSMul [SMul K β] : SMul K (α →ₛ β) :=
  ⟨fun k f => f.map ((· • ·) k)⟩
#align measure_theory.simple_func.has_smul MeasureTheory.SimpleFunc.instSMul

@[simp]
theorem coe_smul [SMul K β] (c : K) (f : α →ₛ β) : ⇑(c • f) = c • ⇑f :=
  rfl
#align measure_theory.simple_func.coe_smul MeasureTheory.SimpleFunc.coe_smul

theorem smul_apply [SMul K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a :=
  rfl
#align measure_theory.simple_func.smul_apply MeasureTheory.SimpleFunc.smul_apply

instance hasNatPow [Monoid β] : Pow (α →ₛ β) ℕ :=
  ⟨fun f n => f.map (· ^ n)⟩
#align measure_theory.simple_func.has_nat_pow MeasureTheory.SimpleFunc.hasNatPow

@[simp]
theorem coe_pow [Monoid β] (f : α →ₛ β) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl
#align measure_theory.simple_func.coe_pow MeasureTheory.SimpleFunc.coe_pow

theorem pow_apply [Monoid β] (n : ℕ) (f : α →ₛ β) (a : α) : (f ^ n) a = f a ^ n :=
  rfl
#align measure_theory.simple_func.pow_apply MeasureTheory.SimpleFunc.pow_apply

instance hasIntPow [DivInvMonoid β] : Pow (α →ₛ β) ℤ :=
  ⟨fun f n => f.map (· ^ n)⟩
#align measure_theory.simple_func.has_int_pow MeasureTheory.SimpleFunc.hasIntPow

@[simp]
theorem coe_zpow [DivInvMonoid β] (f : α →ₛ β) (z : ℤ) : ⇑(f ^ z) = (⇑f) ^ z :=
  rfl
#align measure_theory.simple_func.coe_zpow MeasureTheory.SimpleFunc.coe_zpow

theorem zpow_apply [DivInvMonoid β] (z : ℤ) (f : α →ₛ β) (a : α) : (f ^ z) a = f a ^ z :=
  rfl
#align measure_theory.simple_func.zpow_apply MeasureTheory.SimpleFunc.zpow_apply

-- TODO: work out how to generate these instances with `to_additive`, which gets confused by the
-- argument order swap between `coe_smul` and `coe_pow`.
section Additive

instance instAddMonoid [AddMonoid β] : AddMonoid (α →ₛ β) :=
  Function.Injective.addMonoid (fun f => show α → β from f) coe_injective coe_zero coe_add
    fun _ _ => coe_smul _ _
#align measure_theory.simple_func.add_monoid MeasureTheory.SimpleFunc.instAddMonoid

instance instAddCommMonoid [AddCommMonoid β] : AddCommMonoid (α →ₛ β) :=
  Function.Injective.addCommMonoid (fun f => show α → β from f) coe_injective coe_zero coe_add
    fun _ _ => coe_smul _ _
#align measure_theory.simple_func.add_comm_monoid MeasureTheory.SimpleFunc.instAddCommMonoid

instance instAddGroup [AddGroup β] : AddGroup (α →ₛ β) :=
  Function.Injective.addGroup (fun f => show α → β from f) coe_injective coe_zero coe_add coe_neg
    coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _
#align measure_theory.simple_func.add_group MeasureTheory.SimpleFunc.instAddGroup

instance instAddCommGroup [AddCommGroup β] : AddCommGroup (α →ₛ β) :=
  Function.Injective.addCommGroup (fun f => show α → β from f) coe_injective coe_zero coe_add
    coe_neg coe_sub (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _
#align measure_theory.simple_func.add_comm_group MeasureTheory.SimpleFunc.instAddCommGroup

end Additive

@[to_additive existing]
instance instMonoid [Monoid β] : Monoid (α →ₛ β) :=
  Function.Injective.monoid (fun f => show α → β from f) coe_injective coe_one coe_mul coe_pow
#align measure_theory.simple_func.monoid MeasureTheory.SimpleFunc.instMonoid

@[to_additive existing]
instance instCommMonoid [CommMonoid β] : CommMonoid (α →ₛ β) :=
  Function.Injective.commMonoid (fun f => show α → β from f) coe_injective coe_one coe_mul coe_pow
#align measure_theory.simple_func.comm_monoid MeasureTheory.SimpleFunc.instCommMonoid

@[to_additive existing]
instance instGroup [Group β] : Group (α →ₛ β) :=
  Function.Injective.group (fun f => show α → β from f) coe_injective coe_one coe_mul coe_inv
    coe_div coe_pow coe_zpow
#align measure_theory.simple_func.group MeasureTheory.SimpleFunc.instGroup

@[to_additive existing]
instance instCommGroup [CommGroup β] : CommGroup (α →ₛ β) :=
  Function.Injective.commGroup (fun f => show α → β from f) coe_injective coe_one coe_mul coe_inv
    coe_div coe_pow coe_zpow
#align measure_theory.simple_func.comm_group MeasureTheory.SimpleFunc.instCommGroup

instance instModule [Semiring K] [AddCommMonoid β] [Module K β] : Module K (α →ₛ β) :=
  Function.Injective.module K ⟨⟨fun f => show α → β from f, coe_zero⟩, coe_add⟩
    coe_injective coe_smul
#align measure_theory.simple_func.module MeasureTheory.SimpleFunc.instModule

theorem smul_eq_map [SMul K β] (k : K) (f : α →ₛ β) : k • f = f.map ((· • ·) k) :=
  rfl
#align measure_theory.simple_func.smul_eq_map MeasureTheory.SimpleFunc.smul_eq_map

instance instPreorder [Preorder β] : Preorder (α →ₛ β) :=
  { SimpleFunc.instLE with
    le_refl := fun f a => le_rfl
    le_trans := fun f g h hfg hgh a => le_trans (hfg _) (hgh a) }
#align measure_theory.simple_func.preorder MeasureTheory.SimpleFunc.instPreorder

instance instPartialOrder [PartialOrder β] : PartialOrder (α →ₛ β) :=
  { SimpleFunc.instPreorder with
    le_antisymm := fun _f _g hfg hgf => ext fun a => le_antisymm (hfg a) (hgf a) }
#align measure_theory.simple_func.partial_order MeasureTheory.SimpleFunc.instPartialOrder

instance instOrderBot [LE β] [OrderBot β] : OrderBot (α →ₛ β) where
  bot := const α ⊥
  bot_le _ _ := bot_le
#align measure_theory.simple_func.order_bot MeasureTheory.SimpleFunc.instOrderBot

instance instOrderTop [LE β] [OrderTop β] : OrderTop (α →ₛ β) where
  top := const α ⊤
  le_top _ _ := le_top
#align measure_theory.simple_func.order_top MeasureTheory.SimpleFunc.instOrderTop

instance instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (α →ₛ β) :=
  { SimpleFunc.instPartialOrder with
    inf := (· ⊓ ·)
    inf_le_left := fun _ _ _ => inf_le_left
    inf_le_right := fun _ _ _ => inf_le_right
    le_inf := fun _f _g _h hfh hgh a => le_inf (hfh a) (hgh a) }
#align measure_theory.simple_func.semilattice_inf MeasureTheory.SimpleFunc.instSemilatticeInf

instance instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (α →ₛ β) :=
  { SimpleFunc.instPartialOrder with
    sup := (· ⊔ ·)
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _f _g _h hfh hgh a => sup_le (hfh a) (hgh a) }
#align measure_theory.simple_func.semilattice_sup MeasureTheory.SimpleFunc.instSemilatticeSup

instance instLattice [Lattice β] : Lattice (α →ₛ β) :=
  { SimpleFunc.instSemilatticeSup, SimpleFunc.instSemilatticeInf with }
#align measure_theory.simple_func.lattice MeasureTheory.SimpleFunc.instLattice

instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (α →ₛ β) :=
  { SimpleFunc.instOrderBot, SimpleFunc.instOrderTop with }
#align measure_theory.simple_func.bounded_order MeasureTheory.SimpleFunc.instBoundedOrder

theorem finset_sup_apply [SemilatticeSup β] [OrderBot β] {f : γ → α →ₛ β} (s : Finset γ) (a : α) :
    s.sup f a = s.sup fun c => f c a := by
  refine' Finset.induction_on s rfl _
  -- ⊢ ∀ ⦃a_1 : γ⦄ {s : Finset γ}, ¬a_1 ∈ s → (↑(Finset.sup s f) a = Finset.sup s f …
  intro a s _ ih
  -- ⊢ ↑(Finset.sup (insert a s) f) a✝¹ = Finset.sup (insert a s) fun c => ↑(f c) a✝¹
  rw [Finset.sup_insert, Finset.sup_insert, sup_apply, ih]
  -- 🎉 no goals
#align measure_theory.simple_func.finset_sup_apply MeasureTheory.SimpleFunc.finset_sup_apply

section Restrict

variable [Zero β]

/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict (f : α →ₛ β) (s : Set α) : α →ₛ β :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0
#align measure_theory.simple_func.restrict MeasureTheory.SimpleFunc.restrict

theorem restrict_of_not_measurable {f : α →ₛ β} {s : Set α} (hs : ¬MeasurableSet s) :
    restrict f s = 0 :=
  dif_neg hs
#align measure_theory.simple_func.restrict_of_not_measurable MeasureTheory.SimpleFunc.restrict_of_not_measurable

@[simp]
theorem coe_restrict (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) :
    ⇑(restrict f s) = indicator s f := by
  rw [restrict, dif_pos hs, coe_piecewise, coe_zero, piecewise_eq_indicator]
  -- 🎉 no goals
#align measure_theory.simple_func.coe_restrict MeasureTheory.SimpleFunc.coe_restrict

@[simp]
theorem restrict_univ (f : α →ₛ β) : restrict f univ = f := by simp [restrict]
                                                               -- 🎉 no goals
#align measure_theory.simple_func.restrict_univ MeasureTheory.SimpleFunc.restrict_univ

@[simp]
theorem restrict_empty (f : α →ₛ β) : restrict f ∅ = 0 := by simp [restrict]
                                                             -- 🎉 no goals
#align measure_theory.simple_func.restrict_empty MeasureTheory.SimpleFunc.restrict_empty

theorem map_restrict_of_zero [Zero γ] {g : β → γ} (hg : g 0 = 0) (f : α →ₛ β) (s : Set α) :
    (f.restrict s).map g = (f.map g).restrict s :=
  ext fun x =>
    if hs : MeasurableSet s then by simp [hs, Set.indicator_comp_of_zero hg]
                                    -- 🎉 no goals
    else by simp [restrict_of_not_measurable hs, hg]
            -- 🎉 no goals
#align measure_theory.simple_func.map_restrict_of_zero MeasureTheory.SimpleFunc.map_restrict_of_zero

theorem map_coe_ennreal_restrict (f : α →ₛ ℝ≥0) (s : Set α) :
    (f.restrict s).map ((↑) : ℝ≥0 → ℝ≥0∞) = (f.map (↑)).restrict s :=
  map_restrict_of_zero ENNReal.coe_zero _ _
#align measure_theory.simple_func.map_coe_ennreal_restrict MeasureTheory.SimpleFunc.map_coe_ennreal_restrict

theorem map_coe_nnreal_restrict (f : α →ₛ ℝ≥0) (s : Set α) :
    (f.restrict s).map ((↑) : ℝ≥0 → ℝ) = (f.map (↑)).restrict s :=
  map_restrict_of_zero NNReal.coe_zero _ _
#align measure_theory.simple_func.map_coe_nnreal_restrict MeasureTheory.SimpleFunc.map_coe_nnreal_restrict

theorem restrict_apply (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) (a) :
    restrict f s a = indicator s f a := by simp only [f.coe_restrict hs]
                                           -- 🎉 no goals
#align measure_theory.simple_func.restrict_apply MeasureTheory.SimpleFunc.restrict_apply

theorem restrict_preimage (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Set β}
    (ht : (0 : β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t := by
  simp [hs, indicator_preimage_of_not_mem _ _ ht, inter_comm]
  -- 🎉 no goals
#align measure_theory.simple_func.restrict_preimage MeasureTheory.SimpleFunc.restrict_preimage

theorem restrict_preimage_singleton (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β}
    (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
  f.restrict_preimage hs hr.symm
#align measure_theory.simple_func.restrict_preimage_singleton MeasureTheory.SimpleFunc.restrict_preimage_singleton

theorem mem_restrict_range {r : β} {s : Set α} {f : α →ₛ β} (hs : MeasurableSet s) :
    r ∈ (restrict f s).range ↔ r = 0 ∧ s ≠ univ ∨ r ∈ f '' s := by
  rw [← Finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]
  -- 🎉 no goals
#align measure_theory.simple_func.mem_restrict_range MeasureTheory.SimpleFunc.mem_restrict_range

theorem mem_image_of_mem_range_restrict {r : β} {s : Set α} {f : α →ₛ β}
    (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) : r ∈ f '' s :=
  if hs : MeasurableSet s then by simpa [mem_restrict_range hs, h0, -mem_range] using hr
                                  -- 🎉 no goals
  else by
    rw [restrict_of_not_measurable hs] at hr
    -- ⊢ r ∈ ↑f '' s
    exact (h0 <| eq_zero_of_mem_range_zero hr).elim
    -- 🎉 no goals
#align measure_theory.simple_func.mem_image_of_mem_range_restrict MeasureTheory.SimpleFunc.mem_image_of_mem_range_restrict

@[mono]
theorem restrict_mono [Preorder β] (s : Set α) {f g : α →ₛ β} (H : f ≤ g) :
    f.restrict s ≤ g.restrict s :=
  if hs : MeasurableSet s then fun x => by
    simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
    -- 🎉 no goals
  else by simp only [restrict_of_not_measurable hs, le_refl]
          -- 🎉 no goals
#align measure_theory.simple_func.restrict_mono MeasureTheory.SimpleFunc.restrict_mono

end Restrict

section Approx

section

variable [SemilatticeSup β] [OrderBot β] [Zero β]

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `iSup_approx_apply` for details. -/
def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
  (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k ≤ f a }
#align measure_theory.simple_func.approx MeasureTheory.SimpleFunc.approx

theorem approx_apply [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : Measurable f) :
    (approx i f n : α →ₛ β) a = (Finset.range n).sup fun k => if i k ≤ f a then i k else 0 := by
  dsimp only [approx]
  -- ⊢ ↑(Finset.sup (Finset.range n) fun k => restrict (const α (i k)) {a | i k ≤ f …
  rw [finset_sup_apply]
  -- ⊢ (Finset.sup (Finset.range n) fun c => ↑(restrict (const α (i c)) {a | i c ≤  …
  congr
  -- ⊢ (fun c => ↑(restrict (const α (i c)) {a | i c ≤ f a}) a) = fun k => if i k ≤ …
  funext k
  -- ⊢ ↑(restrict (const α (i k)) {a | i k ≤ f a}) a = if i k ≤ f a then i k else 0
  rw [restrict_apply]
  -- ⊢ indicator {a | i k ≤ f a} (↑(const α (i k))) a = if i k ≤ f a then i k else 0
  · simp only [coe_const, mem_setOf_eq, indicator_apply, Function.const_apply]
    -- 🎉 no goals
  · exact hf measurableSet_Ici
    -- 🎉 no goals
#align measure_theory.simple_func.approx_apply MeasureTheory.SimpleFunc.approx_apply

theorem monotone_approx (i : ℕ → β) (f : α → β) : Monotone (approx i f) := fun _ _ h =>
  Finset.sup_mono <| Finset.range_subset.2 h
#align measure_theory.simple_func.monotone_approx MeasureTheory.SimpleFunc.monotone_approx

theorem approx_comp [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
    [OpensMeasurableSpace β] [MeasurableSpace γ] {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α)
    (hf : Measurable f) (hg : Measurable g) :
    (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) := by
  rw [approx_apply _ hf, approx_apply _ (hf.comp hg), Function.comp_apply]
  -- 🎉 no goals
#align measure_theory.simple_func.approx_comp MeasureTheory.SimpleFunc.approx_comp

end

theorem iSup_approx_apply [TopologicalSpace β] [CompleteLattice β] [OrderClosedTopology β] [Zero β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (i : ℕ → β) (f : α → β) (a : α) (hf : Measurable f)
    (h_zero : (0 : β) = ⊥) : ⨆ n, (approx i f n : α →ₛ β) a = ⨆ (k) (_ : i k ≤ f a), i k := by
  refine' le_antisymm (iSup_le fun n => _) (iSup_le fun k => iSup_le fun hk => _)
  -- ⊢ ↑(approx i f n) a ≤ ⨆ (k : ℕ) (_ : i k ≤ f a), i k
  · rw [approx_apply a hf, h_zero]
    -- ⊢ (Finset.sup (Finset.range n) fun k => if i k ≤ f a then i k else ⊥) ≤ ⨆ (k : …
    refine' Finset.sup_le fun k _ => _
    -- ⊢ (if i k ≤ f a then i k else ⊥) ≤ ⨆ (k : ℕ) (_ : i k ≤ f a), i k
    split_ifs with h
    -- ⊢ i k ≤ ⨆ (k : ℕ) (_ : i k ≤ f a), i k
    · exact le_iSup_of_le k (le_iSup (fun _ : i k ≤ f a => i k) h)
      -- 🎉 no goals
    · exact bot_le
      -- 🎉 no goals
  · refine' le_iSup_of_le (k + 1) _
    -- ⊢ i k ≤ ↑(approx i f (k + 1)) a
    rw [approx_apply a hf]
    -- ⊢ i k ≤ Finset.sup (Finset.range (k + 1)) fun k => if i k ≤ f a then i k else 0
    have : k ∈ Finset.range (k + 1) := Finset.mem_range.2 (Nat.lt_succ_self _)
    -- ⊢ i k ≤ Finset.sup (Finset.range (k + 1)) fun k => if i k ≤ f a then i k else 0
    refine' le_trans (le_of_eq _) (Finset.le_sup this)
    -- ⊢ i k = if i k ≤ f a then i k else 0
    rw [if_pos hk]
    -- 🎉 no goals
#align measure_theory.simple_func.supr_approx_apply MeasureTheory.SimpleFunc.iSup_approx_apply

end Approx

section EApprox

/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
def ennrealRatEmbed (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Encodable.decode (α := ℚ) n).getD (0 : ℚ))
#align measure_theory.simple_func.ennreal_rat_embed MeasureTheory.SimpleFunc.ennrealRatEmbed

theorem ennrealRatEmbed_encode (q : ℚ) : ennrealRatEmbed (Encodable.encode q) = Real.toNNReal q :=
  by rw [ennrealRatEmbed, Encodable.encodek]; rfl
     -- ⊢ ENNReal.ofReal ↑(Option.getD (Option.some q) 0) = ↑(Real.toNNReal ↑q)
                                              -- 🎉 no goals
#align measure_theory.simple_func.ennreal_rat_embed_encode MeasureTheory.SimpleFunc.ennrealRatEmbed_encode

/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
  approx ennrealRatEmbed
#align measure_theory.simple_func.eapprox MeasureTheory.SimpleFunc.eapprox

theorem eapprox_lt_top (f : α → ℝ≥0∞) (n : ℕ) (a : α) : eapprox f n a < ∞ := by
  simp only [eapprox, approx, finset_sup_apply, Finset.mem_range, ENNReal.bot_eq_zero, restrict]
  -- ⊢ (Finset.sup (Finset.range n) fun c => ↑(if hs : MeasurableSet {a | ennrealRa …
  rw [Finset.sup_lt_iff (α := ℝ≥0∞) WithTop.zero_lt_top]
  -- ⊢ ∀ (b : ℕ), b ∈ Finset.range n → ↑(if hs : MeasurableSet {a | ennrealRatEmbed …
  intro b _
  -- ⊢ ↑(if hs : MeasurableSet {a | ennrealRatEmbed b ≤ f a} then piecewise {a | en …
  split_ifs
  -- ⊢ ↑(piecewise {a | ennrealRatEmbed b ≤ f a} h✝ (const α (ennrealRatEmbed b)) 0 …
  · simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
    -- ⊢ Set.piecewise {a | ennrealRatEmbed b ≤ f a} (Function.const α (ennrealRatEmb …
    calc
      { a : α | ennrealRatEmbed b ≤ f a }.indicator (fun _ => ennrealRatEmbed b) a ≤
          ennrealRatEmbed b :=
        indicator_le_self _ _ a
      _ < ⊤ := ENNReal.coe_lt_top
  · exact WithTop.zero_lt_top
    -- 🎉 no goals
#align measure_theory.simple_func.eapprox_lt_top MeasureTheory.SimpleFunc.eapprox_lt_top

@[mono]
theorem monotone_eapprox (f : α → ℝ≥0∞) : Monotone (eapprox f) :=
  monotone_approx _ f
#align measure_theory.simple_func.monotone_eapprox MeasureTheory.SimpleFunc.monotone_eapprox

theorem iSup_eapprox_apply (f : α → ℝ≥0∞) (hf : Measurable f) (a : α) :
    ⨆ n, (eapprox f n : α →ₛ ℝ≥0∞) a = f a := by
  rw [eapprox, iSup_approx_apply ennrealRatEmbed f a hf rfl]
  -- ⊢ ⨆ (k : ℕ) (_ : ennrealRatEmbed k ≤ f a), ennrealRatEmbed k = f a
  refine' le_antisymm (iSup_le fun i => iSup_le fun hi => hi) (le_of_not_gt _)
  -- ⊢ ¬f a > ⨆ (k : ℕ) (_ : ennrealRatEmbed k ≤ f a), ennrealRatEmbed k
  intro h
  -- ⊢ False
  rcases ENNReal.lt_iff_exists_rat_btwn.1 h with ⟨q, _, lt_q, q_lt⟩
  -- ⊢ False
  have :
    (Real.toNNReal q : ℝ≥0∞) ≤ ⨆ (k : ℕ) (_ : ennrealRatEmbed k ≤ f a), ennrealRatEmbed k := by
    refine' le_iSup_of_le (Encodable.encode q) _
    rw [ennrealRatEmbed_encode q]
    exact le_iSup_of_le (le_of_lt q_lt) le_rfl
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)
  -- 🎉 no goals
#align measure_theory.simple_func.supr_eapprox_apply MeasureTheory.SimpleFunc.iSup_eapprox_apply

theorem eapprox_comp [MeasurableSpace γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ} (hf : Measurable f)
    (hg : Measurable g) : (eapprox (f ∘ g) n : α → ℝ≥0∞) = (eapprox f n : γ →ₛ ℝ≥0∞) ∘ g :=
  funext fun a => approx_comp a hf hg
#align measure_theory.simple_func.eapprox_comp MeasureTheory.SimpleFunc.eapprox_comp

/-- Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their values
in `ℝ≥0`. -/
def eapproxDiff (f : α → ℝ≥0∞) : ℕ → α →ₛ ℝ≥0
  | 0 => (eapprox f 0).map ENNReal.toNNReal
  | n + 1 => (eapprox f (n + 1) - eapprox f n).map ENNReal.toNNReal
#align measure_theory.simple_func.eapprox_diff MeasureTheory.SimpleFunc.eapproxDiff

theorem sum_eapproxDiff (f : α → ℝ≥0∞) (n : ℕ) (a : α) :
    (∑ k in Finset.range (n + 1), (eapproxDiff f k a : ℝ≥0∞)) = eapprox f n a := by
  induction' n with n IH
  -- ⊢ ∑ k in Finset.range (Nat.zero + 1), ↑(↑(eapproxDiff f k) a) = ↑(eapprox f Na …
  · simp only [Nat.zero_eq, Nat.zero_add, Finset.sum_singleton, Finset.range_one]
    -- ⊢ ↑(↑(eapproxDiff f 0) a) = ↑(eapprox f 0) a
    rfl
    -- 🎉 no goals
  · erw [Finset.sum_range_succ, Nat.succ_eq_add_one, IH, eapproxDiff, coe_map, Function.comp_apply,
      coe_sub, Pi.sub_apply, ENNReal.coe_toNNReal,
      add_tsub_cancel_of_le (monotone_eapprox f (Nat.le_succ _) _)]
    apply (lt_of_le_of_lt _ (eapprox_lt_top f (n + 1) a)).ne
    -- ⊢ ↑(eapprox f (Nat.add n 0 + 1)) a - ↑(eapprox f (Nat.add n 0)) a ≤ ↑(eapprox  …
    rw [tsub_le_iff_right]
    -- ⊢ ↑(eapprox f (Nat.add n 0 + 1)) a ≤ ↑(eapprox f (n + 1)) a + ↑(eapprox f (Nat …
    exact le_self_add
    -- 🎉 no goals
#align measure_theory.simple_func.sum_eapprox_diff MeasureTheory.SimpleFunc.sum_eapproxDiff

theorem tsum_eapproxDiff (f : α → ℝ≥0∞) (hf : Measurable f) (a : α) :
    (∑' n, (eapproxDiff f n a : ℝ≥0∞)) = f a := by
  simp_rw [ENNReal.tsum_eq_iSup_nat' (tendsto_add_atTop_nat 1), sum_eapproxDiff,
    iSup_eapprox_apply f hf a]
#align measure_theory.simple_func.tsum_eapprox_diff MeasureTheory.SimpleFunc.tsum_eapproxDiff

end EApprox

end Measurable

section Measure

variable {m : MeasurableSpace α} {μ ν : Measure α}

/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
def lintegral {_m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  ∑ x in f.range, x * μ (f ⁻¹' {x})
#align measure_theory.simple_func.lintegral MeasureTheory.SimpleFunc.lintegral

theorem lintegral_eq_of_subset (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞}
    (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
    f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) := by
  refine' Finset.sum_bij_ne_zero (fun r _ _ => r) _ _ _ _
  · simpa only [forall_range_iff, mul_ne_zero_iff, and_imp]
    -- 🎉 no goals
  · intros
    -- ⊢ a₁✝ = a₂✝
    assumption
    -- 🎉 no goals
  · intro b _ hb
    -- ⊢ ∃ a h₁ h₂, b = (fun r x x => r) a h₁ h₂
    refine' ⟨b, _, hb, rfl⟩
    -- ⊢ b ∈ SimpleFunc.range f
    rw [mem_range, ← preimage_singleton_nonempty]
    -- ⊢ Set.Nonempty (↑f ⁻¹' {b})
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2
    -- 🎉 no goals
  · intros
    -- ⊢ a✝ * ↑↑μ (↑f ⁻¹' {a✝}) = (fun r x x => r) a✝ h₁✝ h₂✝ * ↑↑μ (↑f ⁻¹' {(fun r x …
    rfl
    -- 🎉 no goals
#align measure_theory.simple_func.lintegral_eq_of_subset MeasureTheory.SimpleFunc.lintegral_eq_of_subset

theorem lintegral_eq_of_subset' (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞} (hs : f.range \ {0} ⊆ s) :
    f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
  f.lintegral_eq_of_subset fun x hfx _ =>
    hs <| Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hfx⟩
#align measure_theory.simple_func.lintegral_eq_of_subset' MeasureTheory.SimpleFunc.lintegral_eq_of_subset'

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`.  -/
theorem map_lintegral (g : β → ℝ≥0∞) (f : α →ₛ β) :
    (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x}) := by
  simp only [lintegral, range_map]
  -- ⊢ ∑ x in Finset.image g (SimpleFunc.range f), x * ↑↑μ (↑(map g f) ⁻¹' {x}) = ∑ …
  refine' Finset.sum_image' _ fun b hb => _
  -- ⊢ g b * ↑↑μ (↑(map g f) ⁻¹' {g b}) = ∑ x in Finset.filter (fun c' => g c' = g  …
  rcases mem_range.1 hb with ⟨a, rfl⟩
  -- ⊢ g (↑f a) * ↑↑μ (↑(map g f) ⁻¹' {g (↑f a)}) = ∑ x in Finset.filter (fun c' => …
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton, Finset.mul_sum]
  -- ⊢ ∑ x in Finset.filter (fun b => g b = g (↑f a)) (SimpleFunc.range f), g (↑f a …
  refine' Finset.sum_congr _ _
  -- ⊢ Finset.filter (fun b => g b = g (↑f a)) (SimpleFunc.range f) = Finset.filter …
  · congr
    -- 🎉 no goals
  · intro x
    -- ⊢ x ∈ Finset.filter (fun c' => g c' = g (↑f a)) (SimpleFunc.range f) → g (↑f a …
    simp only [Finset.mem_filter]
    -- ⊢ x ∈ SimpleFunc.range f ∧ g x = g (↑f a) → g (↑f a) * ↑↑μ (↑f ⁻¹' {x}) = g x  …
    rintro ⟨_, h⟩
    -- ⊢ g (↑f a) * ↑↑μ (↑f ⁻¹' {x}) = g x * ↑↑μ (↑f ⁻¹' {x})
    rw [h]
    -- 🎉 no goals
#align measure_theory.simple_func.map_lintegral MeasureTheory.SimpleFunc.map_lintegral

theorem add_lintegral (f g : α →ₛ ℝ≥0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
  calc
    (f + g).lintegral μ =
        ∑ x in (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) :=
      by rw [add_eq_map₂, map_lintegral]; exact Finset.sum_congr rfl fun a _ => add_mul _ _ _
         -- ⊢ ∑ x in SimpleFunc.range (pair f g), (x.fst + x.snd) * ↑↑μ (↑(pair f g) ⁻¹' { …
                                          -- 🎉 no goals
    _ = (∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x})) +
          ∑ x in (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) :=
      by rw [Finset.sum_add_distrib]
         -- 🎉 no goals
    _ = ((pair f g).map Prod.fst).lintegral μ + ((pair f g).map Prod.snd).lintegral μ := by
      rw [map_lintegral, map_lintegral]
      -- 🎉 no goals
    _ = lintegral f μ + lintegral g μ := rfl
#align measure_theory.simple_func.add_lintegral MeasureTheory.SimpleFunc.add_lintegral

theorem const_mul_lintegral (f : α →ₛ ℝ≥0∞) (x : ℝ≥0∞) :
    (const α x * f).lintegral μ = x * f.lintegral μ :=
  calc
    (f.map fun a => x * a).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) := map_lintegral _ _
    _ = ∑ r in f.range, x * (r * μ (f ⁻¹' {r})) :=
      (Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _)
    _ = x * f.lintegral μ := Finset.mul_sum.symm
#align measure_theory.simple_func.const_mul_lintegral MeasureTheory.SimpleFunc.const_mul_lintegral

/-- Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map. -/
def lintegralₗ {m : MeasurableSpace α} : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] Measure α →ₗ[ℝ≥0∞] ℝ≥0∞ where
  toFun f :=
    { toFun := lintegral f
      map_add' := by simp [lintegral, mul_add, Finset.sum_add_distrib]
                     -- 🎉 no goals
      map_smul' := fun c μ => by
        simp [lintegral, mul_left_comm _ c, Finset.mul_sum, Measure.smul_apply c] }
        -- 🎉 no goals
  map_add' f g := LinearMap.ext fun μ => add_lintegral f g
  map_smul' c f := LinearMap.ext fun μ => const_mul_lintegral f c
#align measure_theory.simple_func.lintegralₗ MeasureTheory.SimpleFunc.lintegralₗ

@[simp]
theorem zero_lintegral : (0 : α →ₛ ℝ≥0∞).lintegral μ = 0 :=
  LinearMap.ext_iff.1 lintegralₗ.map_zero μ
#align measure_theory.simple_func.zero_lintegral MeasureTheory.SimpleFunc.zero_lintegral

theorem lintegral_add {ν} (f : α →ₛ ℝ≥0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
  (lintegralₗ f).map_add μ ν
#align measure_theory.simple_func.lintegral_add MeasureTheory.SimpleFunc.lintegral_add

theorem lintegral_smul (f : α →ₛ ℝ≥0∞) (c : ℝ≥0∞) : f.lintegral (c • μ) = c • f.lintegral μ :=
  (lintegralₗ f).map_smul c μ
#align measure_theory.simple_func.lintegral_smul MeasureTheory.SimpleFunc.lintegral_smul

@[simp]
theorem lintegral_zero [MeasurableSpace α] (f : α →ₛ ℝ≥0∞) : f.lintegral 0 = 0 :=
  (lintegralₗ f).map_zero
#align measure_theory.simple_func.lintegral_zero MeasureTheory.SimpleFunc.lintegral_zero

theorem lintegral_sum {m : MeasurableSpace α} {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → Measure α) :
    f.lintegral (Measure.sum μ) = ∑' i, f.lintegral (μ i) := by
  simp only [lintegral, Measure.sum_apply, f.measurableSet_preimage, ← Finset.tsum_subtype, ←
    ENNReal.tsum_mul_left]
  apply ENNReal.tsum_comm
  -- 🎉 no goals
#align measure_theory.simple_func.lintegral_sum MeasureTheory.SimpleFunc.lintegral_sum

theorem restrict_lintegral (f : α →ₛ ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    (restrict f s).lintegral μ = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :=
  calc
    (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :=
      lintegral_eq_of_subset _ fun x hx =>
        if hxs : x ∈ s then fun _ => by
          simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
          -- 🎉 no goals
        else False.elim <| hx <| by simp [*]
                                    -- 🎉 no goals
    _ = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :=
      Finset.sum_congr rfl <|
        forall_range_iff.2 fun b =>
          if hb : f b = 0 then by simp only [hb, zero_mul]
                                  -- 🎉 no goals
          else by rw [restrict_preimage_singleton _ hs hb, inter_comm]
                  -- 🎉 no goals
#align measure_theory.simple_func.restrict_lintegral MeasureTheory.SimpleFunc.restrict_lintegral

theorem lintegral_restrict {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (s : Set α) (μ : Measure α) :
    f.lintegral (μ.restrict s) = ∑ y in f.range, y * μ (f ⁻¹' {y} ∩ s) := by
  simp only [lintegral, Measure.restrict_apply, f.measurableSet_preimage]
  -- 🎉 no goals
#align measure_theory.simple_func.lintegral_restrict MeasureTheory.SimpleFunc.lintegral_restrict

theorem restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ℝ≥0∞) {s : Set α}
    (hs : MeasurableSet s) : (restrict f s).lintegral μ = f.lintegral (μ.restrict s) := by
  rw [f.restrict_lintegral hs, lintegral_restrict]
  -- 🎉 no goals
#align measure_theory.simple_func.restrict_lintegral_eq_lintegral_restrict MeasureTheory.SimpleFunc.restrict_lintegral_eq_lintegral_restrict

theorem const_lintegral (c : ℝ≥0∞) : (const α c).lintegral μ = c * μ univ := by
  rw [lintegral]
  -- ⊢ ∑ x in SimpleFunc.range (const α c), x * ↑↑μ (↑(const α c) ⁻¹' {x}) = c * ↑↑ …
  cases isEmpty_or_nonempty α
  -- ⊢ ∑ x in SimpleFunc.range (const α c), x * ↑↑μ (↑(const α c) ⁻¹' {x}) = c * ↑↑ …
  · simp [μ.eq_zero_of_isEmpty]
    -- 🎉 no goals
  · simp; unfold Function.const; rw [preimage_const_of_mem (mem_singleton c)]
    -- ⊢ c * ↑↑μ (Function.const α c ⁻¹' {c}) = c * ↑↑μ univ
          -- ⊢ c * ↑↑μ ((fun x => c) ⁻¹' {c}) = c * ↑↑μ univ
                                 -- 🎉 no goals
#align measure_theory.simple_func.const_lintegral MeasureTheory.SimpleFunc.const_lintegral

theorem const_lintegral_restrict (c : ℝ≥0∞) (s : Set α) :
    (const α c).lintegral (μ.restrict s) = c * μ s := by
  rw [const_lintegral, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  -- 🎉 no goals
#align measure_theory.simple_func.const_lintegral_restrict MeasureTheory.SimpleFunc.const_lintegral_restrict

theorem restrict_const_lintegral (c : ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
    ((const α c).restrict s).lintegral μ = c * μ s := by
  rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]
  -- 🎉 no goals
#align measure_theory.simple_func.restrict_const_lintegral MeasureTheory.SimpleFunc.restrict_const_lintegral

theorem le_sup_lintegral (f g : α →ₛ ℝ≥0∞) : f.lintegral μ ⊔ g.lintegral μ ≤ (f ⊔ g).lintegral μ :=
  calc
    f.lintegral μ ⊔ g.lintegral μ =
        ((pair f g).map Prod.fst).lintegral μ ⊔ ((pair f g).map Prod.snd).lintegral μ :=
      rfl
    _ ≤ ∑ x in (pair f g).range, (x.1 ⊔ x.2) * μ (pair f g ⁻¹' {x}) := by
      rw [map_lintegral, map_lintegral]
      -- ⊢ (∑ x in SimpleFunc.range (pair f g), x.fst * ↑↑μ (↑(pair f g) ⁻¹' {x})) ⊔ ∑  …
      refine' sup_le _ _ <;> refine' Finset.sum_le_sum fun a _ => mul_le_mul_right' _ _
      -- ⊢ ∑ x in SimpleFunc.range (pair f g), x.fst * ↑↑μ (↑(pair f g) ⁻¹' {x}) ≤ ∑ x  …
                             -- ⊢ a.fst ≤ a.fst ⊔ a.snd
                             -- ⊢ a.snd ≤ a.fst ⊔ a.snd
      · exact le_sup_left
        -- 🎉 no goals
      · exact le_sup_right
        -- 🎉 no goals
    _ = (f ⊔ g).lintegral μ := by rw [sup_eq_map₂, map_lintegral]
                                  -- 🎉 no goals
#align measure_theory.simple_func.le_sup_lintegral MeasureTheory.SimpleFunc.le_sup_lintegral

/-- `SimpleFunc.lintegral` is monotone both in function and in measure. -/
@[mono]
theorem lintegral_mono {f g : α →ₛ ℝ≥0∞} (hfg : f ≤ g) (hμν : μ ≤ ν) :
    f.lintegral μ ≤ g.lintegral ν :=
  calc
    f.lintegral μ ≤ f.lintegral μ ⊔ g.lintegral μ := le_sup_left
    _ ≤ (f ⊔ g).lintegral μ := (le_sup_lintegral _ _)
    _ = g.lintegral μ := by rw [sup_of_le_right hfg]
                            -- 🎉 no goals
    _ ≤ g.lintegral ν :=
      Finset.sum_le_sum fun y _ => ENNReal.mul_left_mono <| hμν _ (g.measurableSet_preimage _)

#align measure_theory.simple_func.lintegral_mono MeasureTheory.SimpleFunc.lintegral_mono

/-- `SimpleFunc.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
theorem lintegral_eq_of_measure_preimage [MeasurableSpace β] {f : α →ₛ ℝ≥0∞} {g : β →ₛ ℝ≥0∞}
    {ν : Measure β} (H : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) : f.lintegral μ = g.lintegral ν := by
  simp only [lintegral, ← H]
  -- ⊢ ∑ x in SimpleFunc.range f, x * ↑↑μ (↑f ⁻¹' {x}) = ∑ x in SimpleFunc.range g, …
  apply lintegral_eq_of_subset
  -- ⊢ ∀ (x : α), ↑f x ≠ 0 → ↑↑μ (↑f ⁻¹' {↑f x}) ≠ 0 → ↑f x ∈ SimpleFunc.range g
  simp only [H]
  -- ⊢ ∀ (x : α), ↑f x ≠ 0 → ↑↑ν (↑g ⁻¹' {↑f x}) ≠ 0 → ↑f x ∈ SimpleFunc.range g
  intros
  -- ⊢ ↑f x✝ ∈ SimpleFunc.range g
  exact mem_range_of_measure_ne_zero ‹_›
  -- 🎉 no goals
#align measure_theory.simple_func.lintegral_eq_of_measure_preimage MeasureTheory.SimpleFunc.lintegral_eq_of_measure_preimage

/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
theorem lintegral_congr {f g : α →ₛ ℝ≥0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g.lintegral μ :=
  lintegral_eq_of_measure_preimage fun y =>
    measure_congr <| Eventually.set_eq <| h.mono fun x hx => by simp [hx]
                                                                -- 🎉 no goals
#align measure_theory.simple_func.lintegral_congr MeasureTheory.SimpleFunc.lintegral_congr

theorem lintegral_map' {β} [MeasurableSpace β] {μ' : Measure β} (f : α →ₛ ℝ≥0∞) (g : β →ₛ ℝ≥0∞)
    (m' : α → β) (eq : ∀ a, f a = g (m' a)) (h : ∀ s, MeasurableSet s → μ' s = μ (m' ⁻¹' s)) :
    f.lintegral μ = g.lintegral μ' :=
  lintegral_eq_of_measure_preimage fun y => by
    simp only [preimage, eq]
    -- ⊢ ↑↑μ {x | ↑g (m' x) ∈ {y}} = ↑↑μ' {x | ↑g x ∈ {y}}
    exact (h (g ⁻¹' {y}) (g.measurableSet_preimage _)).symm
    -- 🎉 no goals
#align measure_theory.simple_func.lintegral_map' MeasureTheory.SimpleFunc.lintegral_map'

theorem lintegral_map {β} [MeasurableSpace β] (g : β →ₛ ℝ≥0∞) {f : α → β} (hf : Measurable f) :
    g.lintegral (Measure.map f μ) = (g.comp f hf).lintegral μ :=
  Eq.symm <| lintegral_map' _ _ f (fun _ => rfl) fun _s hs => Measure.map_apply hf hs
#align measure_theory.simple_func.lintegral_map MeasureTheory.SimpleFunc.lintegral_map

end Measure

section FinMeasSupp

open Finset Function

theorem support_eq [MeasurableSpace α] [Zero β] (f : α →ₛ β) :
    support f = ⋃ y ∈ f.range.filter fun y => y ≠ 0, f ⁻¹' {y} :=
  Set.ext fun x => by
    simp only [mem_support, Set.mem_preimage, mem_filter, mem_range_self, true_and_iff, exists_prop,
      mem_iUnion, Set.mem_range, mem_singleton_iff, exists_eq_right']
#align measure_theory.simple_func.support_eq MeasureTheory.SimpleFunc.support_eq

variable {m : MeasurableSpace α} [Zero β] [Zero γ] {μ : Measure α} {f : α →ₛ β}

theorem measurableSet_support [MeasurableSpace α] (f : α →ₛ β) : MeasurableSet (support f) := by
  rw [f.support_eq]
  -- ⊢ MeasurableSet (⋃ (y : β) (_ : y ∈ filter (fun y => y ≠ 0) (SimpleFunc.range  …
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_fiber _ _
  -- 🎉 no goals
#align measure_theory.simple_func.measurable_set_support MeasureTheory.SimpleFunc.measurableSet_support

/-- A `SimpleFunc` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
protected def FinMeasSupp {_m : MeasurableSpace α} (f : α →ₛ β) (μ : Measure α) : Prop :=
  f =ᶠ[μ.cofinite] 0
#align measure_theory.simple_func.fin_meas_supp MeasureTheory.SimpleFunc.FinMeasSupp

theorem finMeasSupp_iff_support : f.FinMeasSupp μ ↔ μ (support f) < ∞ :=
  Iff.rfl
#align measure_theory.simple_func.fin_meas_supp_iff_support MeasureTheory.SimpleFunc.finMeasSupp_iff_support

theorem finMeasSupp_iff : f.FinMeasSupp μ ↔ ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞ := by
  constructor
  -- ⊢ SimpleFunc.FinMeasSupp f μ → ∀ (y : β), y ≠ 0 → ↑↑μ (↑f ⁻¹' {y}) < ⊤
  · refine' fun h y hy => lt_of_le_of_lt (measure_mono _) h
    -- ⊢ ↑f ⁻¹' {y} ⊆ {x | (fun x => ↑f x = OfNat.ofNat 0 x) x}ᶜ
    exact fun x hx (H : f x = 0) => hy <| H ▸ Eq.symm hx
    -- 🎉 no goals
  · intro H
    -- ⊢ SimpleFunc.FinMeasSupp f μ
    rw [finMeasSupp_iff_support, support_eq]
    -- ⊢ ↑↑μ (⋃ (y : β) (_ : y ∈ filter (fun y => y ≠ 0) (SimpleFunc.range f)), ↑f ⁻¹ …
    refine' lt_of_le_of_lt (measure_biUnion_finset_le _ _) (sum_lt_top _)
    -- ⊢ ∀ (a : β), a ∈ filter (fun y => y ≠ 0) (SimpleFunc.range f) → ↑↑μ (↑f ⁻¹' {a …
    exact fun y hy => (H y (Finset.mem_filter.1 hy).2).ne
    -- 🎉 no goals
#align measure_theory.simple_func.fin_meas_supp_iff MeasureTheory.SimpleFunc.finMeasSupp_iff

namespace FinMeasSupp

theorem meas_preimage_singleton_ne_zero (h : f.FinMeasSupp μ) {y : β} (hy : y ≠ 0) :
    μ (f ⁻¹' {y}) < ∞ :=
  finMeasSupp_iff.1 h y hy
#align measure_theory.simple_func.fin_meas_supp.meas_preimage_singleton_ne_zero MeasureTheory.SimpleFunc.FinMeasSupp.meas_preimage_singleton_ne_zero

protected theorem map {g : β → γ} (hf : f.FinMeasSupp μ) (hg : g 0 = 0) : (f.map g).FinMeasSupp μ :=
  flip lt_of_le_of_lt hf (measure_mono <| support_comp_subset hg f)
#align measure_theory.simple_func.fin_meas_supp.map MeasureTheory.SimpleFunc.FinMeasSupp.map

theorem of_map {g : β → γ} (h : (f.map g).FinMeasSupp μ) (hg : ∀ b, g b = 0 → b = 0) :
    f.FinMeasSupp μ :=
  flip lt_of_le_of_lt h <| measure_mono <| support_subset_comp @(hg) _
#align measure_theory.simple_func.fin_meas_supp.of_map MeasureTheory.SimpleFunc.FinMeasSupp.of_map

theorem map_iff {g : β → γ} (hg : ∀ {b}, g b = 0 ↔ b = 0) :
    (f.map g).FinMeasSupp μ ↔ f.FinMeasSupp μ :=
  ⟨fun h => h.of_map fun _ => hg.1, fun h => h.map <| hg.2 rfl⟩
#align measure_theory.simple_func.fin_meas_supp.map_iff MeasureTheory.SimpleFunc.FinMeasSupp.map_iff

protected theorem pair {g : α →ₛ γ} (hf : f.FinMeasSupp μ) (hg : g.FinMeasSupp μ) :
    (pair f g).FinMeasSupp μ :=
  calc
    μ (support <| pair f g) = μ (support f ∪ support g) := congr_arg μ <| support_prod_mk f g
    _ ≤ μ (support f) + μ (support g) := (measure_union_le _ _)
    _ < _ := add_lt_top.2 ⟨hf, hg⟩
#align measure_theory.simple_func.fin_meas_supp.pair MeasureTheory.SimpleFunc.FinMeasSupp.pair

protected theorem map₂ [Zero δ] (hf : f.FinMeasSupp μ) {g : α →ₛ γ} (hg : g.FinMeasSupp μ)
    {op : β → γ → δ} (H : op 0 0 = 0) : ((pair f g).map (Function.uncurry op)).FinMeasSupp μ :=
  (hf.pair hg).map H
#align measure_theory.simple_func.fin_meas_supp.map₂ MeasureTheory.SimpleFunc.FinMeasSupp.map₂

protected theorem add {β} [AddMonoid β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f + g).FinMeasSupp μ := by
  rw [add_eq_map₂]
  -- ⊢ SimpleFunc.FinMeasSupp (map (fun p => p.fst + p.snd) (pair f g)) μ
  exact hf.map₂ hg (zero_add 0)
  -- 🎉 no goals
#align measure_theory.simple_func.fin_meas_supp.add MeasureTheory.SimpleFunc.FinMeasSupp.add

protected theorem mul {β} [MonoidWithZero β] {f g : α →ₛ β} (hf : f.FinMeasSupp μ)
    (hg : g.FinMeasSupp μ) : (f * g).FinMeasSupp μ := by
  rw [mul_eq_map₂]
  -- ⊢ SimpleFunc.FinMeasSupp (map (fun p => p.fst * p.snd) (pair f g)) μ
  exact hf.map₂ hg (zero_mul 0)
  -- 🎉 no goals
#align measure_theory.simple_func.fin_meas_supp.mul MeasureTheory.SimpleFunc.FinMeasSupp.mul

theorem lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hm : f.FinMeasSupp μ) (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
    f.lintegral μ < ∞ := by
  refine' sum_lt_top fun a ha => _
  -- ⊢ a * ↑↑μ (↑f ⁻¹' {a}) ≠ ⊤
  rcases eq_or_ne a ∞ with (rfl | ha)
  -- ⊢ ⊤ * ↑↑μ (↑f ⁻¹' {⊤}) ≠ ⊤
  · simp only [ae_iff, Ne.def, Classical.not_not] at hf
    -- ⊢ ⊤ * ↑↑μ (↑f ⁻¹' {⊤}) ≠ ⊤
    simp [Set.preimage, hf]
    -- 🎉 no goals
  · by_cases ha0 : a = 0
    -- ⊢ a * ↑↑μ (↑f ⁻¹' {a}) ≠ ⊤
    · subst a
      -- ⊢ 0 * ↑↑μ (↑f ⁻¹' {0}) ≠ ⊤
      rwa [zero_mul]
      -- 🎉 no goals
    · exact mul_ne_top ha (finMeasSupp_iff.1 hm _ ha0).ne
      -- 🎉 no goals
#align measure_theory.simple_func.fin_meas_supp.lintegral_lt_top MeasureTheory.SimpleFunc.FinMeasSupp.lintegral_lt_top

theorem of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (h : f.lintegral μ ≠ ∞) : f.FinMeasSupp μ := by
  refine' finMeasSupp_iff.2 fun b hb => _
  -- ⊢ ↑↑μ (↑f ⁻¹' {b}) < ⊤
  rw [f.lintegral_eq_of_subset' (Finset.subset_insert b _)] at h
  -- ⊢ ↑↑μ (↑f ⁻¹' {b}) < ⊤
  refine' ENNReal.lt_top_of_mul_ne_top_right _ hb
  -- ⊢ b * ↑↑μ (↑f ⁻¹' {b}) ≠ ⊤
  exact (lt_top_of_sum_ne_top h (Finset.mem_insert_self _ _)).ne
  -- 🎉 no goals
#align measure_theory.simple_func.fin_meas_supp.of_lintegral_ne_top MeasureTheory.SimpleFunc.FinMeasSupp.of_lintegral_ne_top

theorem iff_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
    f.FinMeasSupp μ ↔ f.lintegral μ < ∞ :=
  ⟨fun h => h.lintegral_lt_top hf, fun h => of_lintegral_ne_top h.ne⟩
#align measure_theory.simple_func.fin_meas_supp.iff_lintegral_lt_top MeasureTheory.SimpleFunc.FinMeasSupp.iff_lintegral_lt_top

end FinMeasSupp

end FinMeasSupp

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`) -/
@[elab_as_elim]
protected theorem induction {α γ} [MeasurableSpace α] [AddMonoid γ] {P : SimpleFunc α γ → Prop}
    (h_ind :
      ∀ (c) {s} (hs : MeasurableSet s),
        P (SimpleFunc.piecewise s hs (SimpleFunc.const _ c) (SimpleFunc.const _ 0)))
    (h_add : ∀ ⦃f g : SimpleFunc α γ⦄, Disjoint (support f) (support g) → P f → P g → P (f + g))
    (f : SimpleFunc α γ) : P f := by
  generalize h : f.range \ {0} = s
  -- ⊢ P f
  rw [← Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, SimpleFunc.coe_range] at h
  -- ⊢ P f
  induction s using Finset.induction generalizing f with
  | empty =>
    rw [Finset.coe_empty, diff_eq_empty, range_subset_singleton] at h
    convert h_ind 0 MeasurableSet.univ
    ext x
    simp [h]
  | @insert x s hxs ih =>
    have mx := f.measurableSet_preimage {x}
    let g := SimpleFunc.piecewise (f ⁻¹' {x}) mx 0 f
    have Pg : P g := by
      apply ih
      simp only [SimpleFunc.coe_piecewise, range_piecewise]
      rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, h, Finset.coe_insert,
        insert_diff_self_of_not_mem, diff_eq_empty.mpr, Set.empty_union]
      · rw [Set.image_subset_iff]
        convert Set.subset_univ _
        exact preimage_const_of_mem (mem_singleton _)
      · rwa [Finset.mem_coe]
    convert h_add _ Pg (h_ind x mx)
    · ext1 y
      by_cases hy : y ∈ f ⁻¹' {x}
      · simpa [piecewise_eq_of_mem _ _ _ hy, -piecewise_eq_indicator]
      · simp [piecewise_eq_of_not_mem _ _ _ hy, -piecewise_eq_indicator]
    rw [disjoint_iff_inf_le]
    rintro y
    by_cases hy : y ∈ f ⁻¹' {x}
    · simp [piecewise_eq_of_mem _ _ _ hy, -piecewise_eq_indicator]
    · simp [piecewise_eq_of_not_mem _ _ _ hy, -piecewise_eq_indicator]
#align measure_theory.simple_func.induction MeasureTheory.SimpleFunc.induction

end SimpleFunc

end MeasureTheory

open MeasureTheory MeasureTheory.SimpleFunc

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_elim]
theorem Measurable.ennreal_induction {α} [MeasurableSpace α] {P : (α → ℝ≥0∞) → Prop}
    (h_ind : ∀ (c : ℝ≥0∞) ⦃s⦄, MeasurableSet s → P (Set.indicator s fun _ => c))
    (h_add :
      ∀ ⦃f g : α → ℝ≥0∞⦄,
        Disjoint (support f) (support g) → Measurable f → Measurable g → P f → P g → P (f + g))
    (h_iSup :
      ∀ ⦃f : ℕ → α → ℝ≥0∞⦄, (∀ n, Measurable (f n)) → Monotone f → (∀ n, P (f n)) →
        P fun x => ⨆ n, f n x)
    ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : P f := by
  convert h_iSup (fun n => (eapprox f n).measurable) (monotone_eapprox f) _ using 1
  -- ⊢ f = fun x => ⨆ (n : ℕ), ↑(eapprox f n) x
  · ext1 x
    -- ⊢ f x = ⨆ (n : ℕ), ↑(eapprox f n) x
    rw [iSup_eapprox_apply f hf]
    -- 🎉 no goals
  · exact fun n =>
      SimpleFunc.induction (fun c s hs => h_ind c hs)
        (fun f g hfg hf hg => h_add hfg f.measurable g.measurable hf hg) (eapprox f n)
#align measurable.ennreal_induction Measurable.ennreal_induction
