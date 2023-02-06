/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measurable_space_def
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Countable
import Mathbin.Logic.Encodable.Lattice
import Mathbin.Order.Disjointed

/-!
# Measurable spaces and measurable functions

This file defines measurable spaces and measurable functions.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them.

Do not add measurability lemmas (which could be tagged with
@[measurability]) to this file, since the measurability tactic is downstream
from here. Use `measure_theory.measurable_space` instead.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/


open Set Encodable Function Equiv

open Classical

variable {α β γ δ δ' : Type _} {ι : Sort _} {s t u : Set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
structure MeasurableSpace (α : Type _) where
  MeasurableSet' : Set α → Prop
  measurable_set_empty : measurable_set' ∅
  measurable_set_compl : ∀ s, measurable_set' s → measurable_set' (sᶜ)
  measurable_set_unionᵢ : ∀ f : ℕ → Set α, (∀ i, measurable_set' (f i)) → measurable_set' (⋃ i, f i)
#align measurable_space MeasurableSpace

attribute [class] MeasurableSpace

instance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ :=
  h

section

/-- `measurable_set s` means that `s` is measurable (in the ambient measure space on `α`) -/
def MeasurableSet [MeasurableSpace α] : Set α → Prop :=
  ‹MeasurableSpace α›.MeasurableSet'
#align measurable_set MeasurableSet

-- mathport name: measurable_set_of
scoped[MeasureTheory] notation "measurable_set[" m "]" => @MeasurableSet hole! m

@[simp]
theorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=
  ‹MeasurableSpace α›.measurable_set_empty
#align measurable_set.empty MeasurableSet.empty

variable {m : MeasurableSpace α}

include m

theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet (sᶜ) :=
  ‹MeasurableSpace α›.measurable_set_compl s
#align measurable_set.compl MeasurableSet.compl

theorem MeasurableSet.of_compl (h : MeasurableSet (sᶜ)) : MeasurableSet s :=
  compl_compl s ▸ h.compl
#align measurable_set.of_compl MeasurableSet.of_compl

@[simp]
theorem MeasurableSet.compl_iff : MeasurableSet (sᶜ) ↔ MeasurableSet s :=
  ⟨MeasurableSet.of_compl, MeasurableSet.compl⟩
#align measurable_set.compl_iff MeasurableSet.compl_iff

@[simp]
theorem MeasurableSet.univ : MeasurableSet (univ : Set α) := by
  simpa using (@MeasurableSet.empty α _).compl
#align measurable_set.univ MeasurableSet.univ

@[nontriviality]
theorem Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s
#align subsingleton.measurable_set Subsingleton.measurableSet

theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by
  rwa [← h]
#align measurable_set.congr MeasurableSet.congr

theorem MeasurableSet.bUnion_decode₂ [Encodable β] ⦃f : β → Set α⦄ (h : ∀ b, MeasurableSet (f b))
    (n : ℕ) : MeasurableSet (⋃ b ∈ decode₂ β n, f b) :=
  Encodable.unionᵢ_decode₂_cases MeasurableSet.empty h
#align measurable_set.bUnion_decode₂ MeasurableSet.bUnion_decode₂

theorem MeasurableSet.unionᵢ [Countable ι] ⦃f : ι → Set α⦄ (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋃ b, f b) := by
  cases nonempty_encodable (PLift ι)
  rw [← Union_plift_down, ← Encodable.unionᵢ_decode₂]
  exact ‹MeasurableSpace α›.measurable_set_unionᵢ _ (MeasurableSet.bUnion_decode₂ fun _ => h _)
#align measurable_set.Union MeasurableSet.unionᵢ

theorem MeasurableSet.bUnion {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  by
  rw [bUnion_eq_Union]
  haveI := hs.to_encodable
  exact MeasurableSet.unionᵢ (by simpa using h)
#align measurable_set.bUnion MeasurableSet.bUnion

theorem Set.Finite.measurableSet_bUnion {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  MeasurableSet.bUnion hs.Countable h
#align set.finite.measurable_set_bUnion Set.Finite.measurableSet_bUnion

theorem Finset.measurableSet_bUnion {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_bUnion h
#align finset.measurable_set_bUnion Finset.measurableSet_bUnion

theorem MeasurableSet.unionₛ {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋃₀ s) := by
  rw [sUnion_eq_bUnion]
  exact MeasurableSet.bUnion hs h
#align measurable_set.sUnion MeasurableSet.unionₛ

theorem Set.Finite.measurableSet_unionₛ {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) :=
  MeasurableSet.unionₛ hs.Countable h
#align set.finite.measurable_set_sUnion Set.Finite.measurableSet_unionₛ

theorem MeasurableSet.interᵢ [Countable ι] {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) :=
  MeasurableSet.compl_iff.1 <| by
    rw [compl_Inter]
    exact MeasurableSet.unionᵢ fun b => (h b).compl
#align measurable_set.Inter MeasurableSet.interᵢ

theorem MeasurableSet.bInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  MeasurableSet.compl_iff.1 <| by
    rw [compl_Inter₂]
    exact MeasurableSet.bUnion hs fun b hb => (h b hb).compl
#align measurable_set.bInter MeasurableSet.bInter

theorem Set.Finite.measurableSet_bInter {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  MeasurableSet.bInter hs.Countable h
#align set.finite.measurable_set_bInter Set.Finite.measurableSet_bInter

theorem Finset.measurableSet_bInter {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_bInter h
#align finset.measurable_set_bInter Finset.measurableSet_bInter

theorem MeasurableSet.interₛ {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_bInter]
  exact MeasurableSet.bInter hs h
#align measurable_set.sInter MeasurableSet.interₛ

theorem Set.Finite.measurableSet_interₛ {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋂₀ s) :=
  MeasurableSet.interₛ hs.Countable h
#align set.finite.measurable_set_sInter Set.Finite.measurableSet_interₛ

@[simp]
theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ∪ s₂) := by
  rw [union_eq_Union]
  exact MeasurableSet.unionᵢ (Bool.forall_bool.2 ⟨h₂, h₁⟩)
#align measurable_set.union MeasurableSet.union

@[simp]
theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ∩ s₂) := by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl
#align measurable_set.inter MeasurableSet.inter

@[simp]
theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl
#align measurable_set.diff MeasurableSet.diff

@[simp]
theorem MeasurableSet.symmDiff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diffₓ h₂).union (h₂.diffₓ h₁)
#align measurable_set.symm_diff MeasurableSet.symmDiff

@[simp]
theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t) (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diffₓ ht)
#align measurable_set.ite MeasurableSet.ite

theorem MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p → MeasurableSet s)
    (ht : ¬p → MeasurableSet t) : MeasurableSet (ite p s t) :=
  by
  split_ifs
  exacts[hs h, ht h]
#align measurable_set.ite' MeasurableSet.ite'

@[simp]
theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂)
    {i : Bool} : MeasurableSet (cond i s₁ s₂) :=
  by
  cases i
  exacts[h₂, h₁]
#align measurable_set.cond MeasurableSet.cond

@[simp]
theorem MeasurableSet.disjointed {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) (n) :
    MeasurableSet (disjointed f n) :=
  disjointedRec (fun t i ht => MeasurableSet.diff ht <| h _) (h n)
#align measurable_set.disjointed MeasurableSet.disjointed

@[simp]
theorem MeasurableSet.const (p : Prop) : MeasurableSet { a : α | p } := by
  by_cases p <;> simp [h, MeasurableSet.empty] <;> apply MeasurableSet.univ
#align measurable_set.const MeasurableSet.const

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩
#align nonempty_measurable_superset nonempty_measurable_superset

end

open MeasureTheory

@[ext]
theorem MeasurableSpace.ext :
    ∀ {m₁ m₂ : MeasurableSpace α},
      (∀ s : Set α, measurable_set[m₁] s ↔ measurable_set[m₂] s) → m₁ = m₂
  | ⟨s₁, _, _, _⟩, ⟨s₂, _, _, _⟩, h =>
    by
    have : s₁ = s₂ := funext fun x => propext <| h x
    subst this
#align measurable_space.ext MeasurableSpace.ext

@[ext]
theorem MeasurableSpace.ext_iff {m₁ m₂ : MeasurableSpace α} :
    m₁ = m₂ ↔ ∀ s : Set α, measurable_set[m₁] s ↔ measurable_set[m₂] s :=
  ⟨by
    rintro rfl
    intro s
    rfl, MeasurableSpace.ext⟩
#align measurable_space.ext_iff MeasurableSpace.ext_iff

/-- A typeclass mixin for `measurable_space`s such that each singleton is measurable. -/
class MeasurableSingletonClass (α : Type _) [MeasurableSpace α] : Prop where
  measurableSet_singleton : ∀ x, MeasurableSet ({x} : Set α)
#align measurable_singleton_class MeasurableSingletonClass

export MeasurableSingletonClass (measurableSet_singleton)

attribute [simp] measurable_set_singleton

section MeasurableSingletonClass

variable [MeasurableSpace α] [MeasurableSingletonClass α]

theorem measurableSet_eq {a : α} : MeasurableSet { x | x = a } :=
  measurableSet_singleton a
#align measurable_set_eq measurableSet_eq

theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) :
    MeasurableSet (insert a s) :=
  (measurableSet_singleton a).union hs
#align measurable_set.insert MeasurableSet.insert

@[simp]
theorem measurableSet_insert {a : α} {s : Set α} : MeasurableSet (insert a s) ↔ MeasurableSet s :=
  ⟨fun h =>
    if ha : a ∈ s then by rwa [← insert_eq_of_mem ha]
    else insert_diff_self_of_not_mem ha ▸ h.diffₓ (measurableSet_singleton _),
    fun h => h.insert a⟩
#align measurable_set_insert measurableSet_insert

theorem Set.Subsingleton.measurableSet {s : Set α} (hs : s.Subsingleton) : MeasurableSet s :=
  hs.inductionOn MeasurableSet.empty measurableSet_singleton
#align set.subsingleton.measurable_set Set.Subsingleton.measurableSet

theorem Set.Finite.measurableSet {s : Set α} (hs : s.Finite) : MeasurableSet s :=
  Finite.induction_on hs MeasurableSet.empty fun a s ha hsf hsm => hsm.insert _
#align set.finite.measurable_set Set.Finite.measurableSet

protected theorem Finset.measurableSet (s : Finset α) : MeasurableSet (↑s : Set α) :=
  s.finite_toSet.MeasurableSet
#align finset.measurable_set Finset.measurableSet

theorem Set.Countable.measurableSet {s : Set α} (hs : s.Countable) : MeasurableSet s :=
  by
  rw [← bUnion_of_singleton s]
  exact MeasurableSet.bUnion hs fun b hb => measurable_set_singleton b
#align set.countable.measurable_set Set.Countable.measurableSet

end MeasurableSingletonClass

namespace MeasurableSpace

section CompleteLattice

instance : LE (MeasurableSpace α) where le m₁ m₂ := ∀ s, measurable_set[m₁] s → measurable_set[m₂] s

theorem le_def {α} {a b : MeasurableSpace α} : a ≤ b ↔ a.MeasurableSet' ≤ b.MeasurableSet' :=
  Iff.rfl
#align measurable_space.le_def MeasurableSpace.le_def

instance : PartialOrder (MeasurableSpace α) :=
  { MeasurableSpace.hasLe,
    PartialOrder.lift (@MeasurableSet α) fun m₁ m₂ h => ext fun s => h ▸ Iff.rfl with
    lt := fun m₁ m₂ => m₁ ≤ m₂ ∧ ¬m₂ ≤ m₁ }

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | basic : ∀ u ∈ s, generate_measurable u
  | Empty : generate_measurable ∅
  | compl : ∀ s, generate_measurable s → generate_measurable (sᶜ)
  | union : ∀ f : ℕ → Set α, (∀ n, generate_measurable (f n)) → generate_measurable (⋃ i, f i)
#align measurable_space.generate_measurable MeasurableSpace.GenerateMeasurable

/-- Construct the smallest measure space containing a collection of basic sets -/
def generateFrom (s : Set (Set α)) : MeasurableSpace α
    where
  MeasurableSet' := GenerateMeasurable s
  measurable_set_empty := GenerateMeasurable.empty
  measurable_set_compl := GenerateMeasurable.compl
  measurable_set_unionᵢ := GenerateMeasurable.union
#align measurable_space.generate_from MeasurableSpace.generateFrom

theorem measurableSet_generateFrom {s : Set (Set α)} {t : Set α} (ht : t ∈ s) :
    @MeasurableSet _ (generateFrom s) t :=
  GenerateMeasurable.basic t ht
#align measurable_space.measurable_set_generate_from MeasurableSpace.measurableSet_generateFrom

@[elab_as_elim]
theorem generateFrom_induction (p : Set α → Prop) (C : Set (Set α)) (hC : ∀ t ∈ C, p t)
    (h_empty : p ∅) (h_compl : ∀ t, p t → p (tᶜ))
    (h_Union : ∀ f : ℕ → Set α, (∀ n, p (f n)) → p (⋃ i, f i)) {s : Set α}
    (hs : measurable_set[generateFrom C] s) : p s :=
  by
  induction hs
  exacts[hC _ hs_H, h_empty, h_compl _ hs_ih, h_Union hs_f hs_ih]
#align measurable_space.generate_from_induction MeasurableSpace.generateFrom_induction

theorem generateFrom_le {s : Set (Set α)} {m : MeasurableSpace α}
    (h : ∀ t ∈ s, measurable_set[m] t) : generateFrom s ≤ m :=
  fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h (measurable_set_empty m) (fun s _ hs => measurable_set_compl m s hs) fun f _ hf =>
    measurable_set_unionᵢ m f hf
#align measurable_space.generate_from_le MeasurableSpace.generateFrom_le

theorem generateFrom_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
    generateFrom s ≤ m ↔ s ⊆ { t | measurable_set[m] t } :=
  Iff.intro (fun h u hu => h _ <| measurableSet_generateFrom hu) fun h => generateFrom_le h
#align measurable_space.generate_from_le_iff MeasurableSpace.generateFrom_le_iff

@[simp]
theorem generateFrom_measurableSet [MeasurableSpace α] :
    generateFrom { s : Set α | MeasurableSet s } = ‹_› :=
  le_antisymm (generateFrom_le fun _ => id) fun s => measurableSet_generateFrom
#align measurable_space.generate_from_measurable_set MeasurableSpace.generateFrom_measurableSet

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
protected def mkOfClosure (g : Set (Set α)) (hg : { t | measurable_set[generateFrom g] t } = g) :
    MeasurableSpace α where
  MeasurableSet' s := s ∈ g
  measurable_set_empty := hg ▸ measurable_set_empty _
  measurable_set_compl := hg ▸ measurable_set_compl _
  measurable_set_unionᵢ := hg ▸ measurable_set_unionᵢ _
#align measurable_space.mk_of_closure MeasurableSpace.mkOfClosure

theorem mkOfClosure_sets {s : Set (Set α)} {hs : { t | measurable_set[generateFrom s] t } = s} :
    MeasurableSpace.mkOfClosure s hs = generateFrom s :=
  MeasurableSpace.ext fun t =>
    show t ∈ s ↔ _ by
      conv_lhs => rw [← hs]
      rfl
#align measurable_space.mk_of_closure_sets MeasurableSpace.mkOfClosure_sets

/-- We get a Galois insertion between `σ`-algebras on `α` and `set (set α)` by using `generate_from`
  on one side and the collection of measurable sets on the other side. -/
def giGenerateFrom : GaloisInsertion (@generateFrom α) fun m => { t | @MeasurableSet α m t }
    where
  gc s := generateFrom_le_iff
  le_l_u m s := measurableSet_generateFrom
  choice g hg := MeasurableSpace.mkOfClosure g <| le_antisymm hg <| (generateFrom_le_iff _).1 le_rfl
  choice_eq g hg := mkOfClosure_sets
#align measurable_space.gi_generate_from MeasurableSpace.giGenerateFrom

instance : CompleteLattice (MeasurableSpace α) :=
  giGenerateFrom.liftCompleteLattice

instance : Inhabited (MeasurableSpace α) :=
  ⟨⊤⟩

@[mono]
theorem generateFrom_mono {s t : Set (Set α)} (h : s ⊆ t) : generateFrom s ≤ generateFrom t :=
  giGenerateFrom.gc.monotone_l h
#align measurable_space.generate_from_mono MeasurableSpace.generateFrom_mono

theorem generateFrom_sup_generateFrom {s t : Set (Set α)} :
    generateFrom s ⊔ generateFrom t = generateFrom (s ∪ t) :=
  (@giGenerateFrom α).gc.l_sup.symm
#align measurable_space.generate_from_sup_generate_from MeasurableSpace.generateFrom_sup_generateFrom

@[simp]
theorem generateFrom_insert_univ (S : Set (Set α)) :
    generateFrom (insert Set.univ S) = generateFrom S :=
  by
  refine' le_antisymm _ (generate_from_mono (Set.subset_insert _ _))
  rw [generate_from_le_iff]
  intro t ht
  cases ht
  · rw [ht]
    exact MeasurableSet.univ
  · exact measurable_set_generate_from ht
#align measurable_space.generate_from_insert_univ MeasurableSpace.generateFrom_insert_univ

@[simp]
theorem generateFrom_insert_empty (S : Set (Set α)) : generateFrom (insert ∅ S) = generateFrom S :=
  by
  refine' le_antisymm _ (generate_from_mono (Set.subset_insert _ _))
  rw [generate_from_le_iff]
  intro t ht
  cases ht
  · rw [ht]
    exact @MeasurableSet.empty _ (generate_from S)
  · exact measurable_set_generate_from ht
#align measurable_space.generate_from_insert_empty MeasurableSpace.generateFrom_insert_empty

@[simp]
theorem generateFrom_singleton_empty : generateFrom {∅} = (⊥ : MeasurableSpace α) :=
  by
  rw [eq_bot_iff, generate_from_le_iff]
  simp
#align measurable_space.generate_from_singleton_empty MeasurableSpace.generateFrom_singleton_empty

@[simp]
theorem generateFrom_singleton_univ : generateFrom {Set.univ} = (⊥ : MeasurableSpace α) :=
  by
  rw [eq_bot_iff, generate_from_le_iff]
  simp
#align measurable_space.generate_from_singleton_univ MeasurableSpace.generateFrom_singleton_univ

theorem measurableSet_bot_iff {s : Set α} : @MeasurableSet α ⊥ s ↔ s = ∅ ∨ s = univ :=
  let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ
      measurable_set_empty := Or.inl rfl
      measurable_set_compl := by simp (config := { contextual := true }) [or_imp]
      measurable_set_unionᵢ := fun f hf =>
        by_cases
          (fun h : ∃ i, f i = univ =>
            let ⟨i, hi⟩ := h
            Or.inr <| eq_univ_of_univ_subset <| hi ▸ le_supᵢ f i)
          fun h : ¬∃ i, f i = univ =>
          Or.inl <|
            eq_empty_of_subset_empty <|
              unionᵢ_subset fun i =>
                (hf i).elim (by simp (config := { contextual := true })) fun hi =>
                  False.elim <| h ⟨i, hi⟩ }
  have : b = ⊥ :=
    bot_unique fun s hs =>
      hs.elim (fun s => s.symm ▸ @measurable_set_empty _ ⊥) fun s =>
        s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl
#align measurable_space.measurable_set_bot_iff MeasurableSpace.measurableSet_bot_iff

@[simp]
theorem measurableSet_top {s : Set α} : @MeasurableSet _ ⊤ s :=
  trivial
#align measurable_space.measurable_set_top MeasurableSpace.measurableSet_top

@[simp]
theorem measurableSet_inf {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (m₁ ⊓ m₂) s ↔ @MeasurableSet _ m₁ s ∧ @MeasurableSet _ m₂ s :=
  Iff.rfl
#align measurable_space.measurable_set_inf MeasurableSpace.measurableSet_inf

@[simp]
theorem measurableSet_infₛ {ms : Set (MeasurableSpace α)} {s : Set α} :
    @MeasurableSet _ (infₛ ms) s ↔ ∀ m ∈ ms, @MeasurableSet _ m s :=
  show s ∈ ⋂₀ _ ↔ _ by simp
#align measurable_space.measurable_set_Inf MeasurableSpace.measurableSet_infₛ

@[simp]
theorem measurableSet_infᵢ {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (infᵢ m) s ↔ ∀ i, @MeasurableSet _ (m i) s := by
  rw [infᵢ, measurable_set_Inf, forall_range_iff]
#align measurable_space.measurable_set_infi MeasurableSpace.measurableSet_infᵢ

theorem measurableSet_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    measurable_set[m₁ ⊔ m₂] s ↔ GenerateMeasurable (measurable_set[m₁] ∪ measurable_set[m₂]) s :=
  Iff.refl _
#align measurable_space.measurable_set_sup MeasurableSpace.measurableSet_sup

theorem measurableSet_supₛ {ms : Set (MeasurableSpace α)} {s : Set α} :
    measurable_set[supₛ ms] s ↔
      GenerateMeasurable { s : Set α | ∃ m ∈ ms, measurable_set[m] s } s :=
  by
  change @measurable_set' _ (generate_from <| ⋃₀ _) _ ↔ _
  simp [generate_from, ← set_of_exists]
#align measurable_space.measurable_set_Sup MeasurableSpace.measurableSet_supₛ

theorem measurableSet_supᵢ {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (supᵢ m) s ↔ GenerateMeasurable { s : Set α | ∃ i, measurable_set[m i] s } s :=
  by simp only [supᵢ, measurable_set_Sup, exists_range_iff]
#align measurable_space.measurable_set_supr MeasurableSpace.measurableSet_supᵢ

theorem measurableSpace_supᵢ_eq (m : ι → MeasurableSpace α) :
    (⨆ n, m n) = generateFrom { s | ∃ n, measurable_set[m n] s } :=
  by
  ext s
  rw [measurable_set_supr]
  rfl
#align measurable_space.measurable_space_supr_eq MeasurableSpace.measurableSpace_supᵢ_eq

theorem generateFrom_unionᵢ_measurableSet (m : ι → MeasurableSpace α) :
    generateFrom (⋃ n, { t | measurable_set[m n] t }) = ⨆ n, m n :=
  (@giGenerateFrom α).l_supᵢ_u m
#align measurable_space.generate_from_Union_measurable_set MeasurableSpace.generateFrom_unionᵢ_measurableSet

end CompleteLattice

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)
#align measurable Measurable

-- mathport name: measurable_of
scoped[MeasureTheory] notation "measurable[" m "]" => @Measurable hole! hole! m hole!

theorem measurable_id {ma : MeasurableSpace α} : Measurable (@id α) := fun t => id
#align measurable_id measurable_id

theorem measurable_id' {ma : MeasurableSpace α} : Measurable fun a : α => a :=
  measurable_id
#align measurable_id' measurable_id'

theorem Measurable.comp {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) : Measurable (g ∘ f) :=
  fun t ht => hf (hg ht)
#align measurable.comp Measurable.comp

@[simp]
theorem measurable_const {ma : MeasurableSpace α} {mb : MeasurableSpace β} {a : α} :
    Measurable fun b : β => a := fun s hs => MeasurableSet.const (a ∈ s)
#align measurable_const measurable_const

theorem Measurable.le {α} {m m0 : MeasurableSpace α} {mb : MeasurableSpace β} (hm : m ≤ m0)
    {f : α → β} (hf : measurable[m] f) : measurable[m0] f := fun s hs => hm _ (hf hs)
#align measurable.le Measurable.le

theorem MeasurableSpace.Top.measurable {α β : Type _} [MeasurableSpace β] (f : α → β) :
    @Measurable α β ⊤ _ f := fun s hs => MeasurableSpace.measurableSet_top
#align measurable_space.top.measurable MeasurableSpace.Top.measurable

end MeasurableFunctions

