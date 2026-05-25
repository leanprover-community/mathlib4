/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# AuxLemmas
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

-- from BrownianMotion
theorem Set.Finite.lt_iInf_iff {α ι : Type*} [CompleteLinearOrder α]
    {s : Set ι} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) {a : α} :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := sorry

lemma iInf_eq_bot_iff_of_finite {α ι : Type*} [CompleteLinearOrder α] [Finite ι] [Nonempty ι]
    {f : ι → α} : (⨅ i, f i) = ⊥ ↔ ∃ i, f i = ⊥ := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ le_antisymm ((iInf_le _ i).trans_eq hi) bot_le⟩
  by_contra! h'
  simp_rw [← bot_lt_iff_ne_bot] at h'
  have h'' : ∀ i ∈ (Set.univ : Set ι), ⊥ < f i := by simpa
  rw [← Set.Finite.lt_iInf_iff (by simp) Set.finite_univ] at h''
  simp only [Set.mem_univ, iInf_pos] at h''
  exact h''.ne' h

lemma measurable_encode {α : Type*} {_ : MeasurableSpace α} [Encodable α]
    [MeasurableSingletonClass α] :
    Measurable (Encodable.encode (α := α)) := by
  refine measurable_to_nat fun a ↦ ?_
  have : Encodable.encode ⁻¹' {Encodable.encode a} = {a} := by ext; simp
  rw [this]
  exact measurableSet_singleton _

lemma measurableEmbedding_encode (α : Type*) {_ : MeasurableSpace α} [Encodable α]
    [MeasurableSingletonClass α] :
    MeasurableEmbedding (Encodable.encode (α := α)) where
  injective := Encodable.encode_injective
  measurable := measurable_encode
  measurableSet_image' _ _ := .of_discrete

section Finite

variable {𝓧 𝓨 α : Type*} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {mα : MeasurableSpace α} [TopologicalSpace α] [LinearOrder α]
  [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]

lemma measurableSet_isMin [Countable 𝓨]
    {f : 𝓧 → 𝓨 → α} (hf : ∀ y, Measurable (fun x ↦ f x y)) (y : 𝓨) :
    MeasurableSet {x | ∀ z, f x y ≤ f x z} := by
  rw [show {x | ∀ y', f x y ≤ f x y'} = ⋂ y', {x | f x y ≤ f x y'} by ext; simp]
  exact MeasurableSet.iInter fun z ↦ measurableSet_le (by fun_prop) (by fun_prop)

lemma exists_isMinOn' {α : Type*} [LinearOrder α]
    [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] (f : 𝓧 → 𝓨 → α) (x : 𝓧) :
    ∃ n : ℕ, ∃ y, n = Encodable.encode y ∧ ∀ z, f x y ≤ f x z := by
  obtain ⟨y, h⟩ := Finite.exists_min (f x)
  exact ⟨Encodable.encode y, y, rfl, h⟩

noncomputable
def measurableArgmin [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    (f : 𝓧 → 𝓨 → α)
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x y ≤ f x z]
    (x : 𝓧) :
    𝓨 :=
  (measurableEmbedding_encode 𝓨).invFun (Nat.find (exists_isMinOn' f x))

lemma measurable_measurableArgmin [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    {f : 𝓧 → 𝓨 → α}
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x y ≤ f x z]
    (hf : ∀ y, Measurable (fun x ↦ f x y)) :
    Measurable (measurableArgmin f) := by
  refine (MeasurableEmbedding.measurable_invFun (measurableEmbedding_encode 𝓨)).comp ?_
  refine measurable_find _ fun n ↦ ?_
  have : {x | ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x y ≤ f x z}
      = ⋃ y, ({x | n = Encodable.encode y} ∩ {x | ∀ z, f x y ≤ f x z}) := by ext; simp
  rw [this]
  refine MeasurableSet.iUnion fun y ↦ (MeasurableSet.inter (by simp) ?_)
  exact measurableSet_isMin (by fun_prop) y

lemma isMinOn_measurableArgmin {α : Type*} [LinearOrder α]
    [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    (f : 𝓧 → 𝓨 → α)
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x y ≤ f x z]
    (x : 𝓧) (z : 𝓨) :
    f x (measurableArgmin f x) ≤ f x z := by
  obtain ⟨y, h_eq, h_le⟩ := Nat.find_spec (exists_isMinOn' f x)
  refine le_trans (le_of_eq ?_) (h_le z)
  rw [measurableArgmin, h_eq,
    MeasurableEmbedding.leftInverse_invFun (measurableEmbedding_encode 𝓨) y]

end Finite
