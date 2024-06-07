/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Set.Countable
import Mathlib.Order.Disjointed
import Mathlib.Tactic.Measurability

#align_import measure_theory.measurable_space_def from "leanprover-community/mathlib"@"001ffdc42920050657fd45bd2b8bfbec8eaaeb29"

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

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/


open Set Encodable Function Equiv

open scoped Classical

variable {α β γ δ δ' : Type*} {ι : Sort*} {s t u : Set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
@[class] structure MeasurableSpace (α : Type*) where
  /-- Predicate saying that a given set is measurable. Use `MeasurableSet` in the root namespace
  instead. -/
  MeasurableSet' : Set α → Prop
  /-- The empty set is a measurable set. Use `MeasurableSet.empty` instead. -/
  measurableSet_empty : MeasurableSet' ∅
  /-- The complement of a measurable set is a measurable set. Use `MeasurableSet.compl` instead. -/
  measurableSet_compl : ∀ s, MeasurableSet' s → MeasurableSet' sᶜ
  /-- The union of a sequence of measurable sets is a measurable set. Use a more general
  `MeasurableSet.iUnion` instead. -/
  measurableSet_iUnion : ∀ f : ℕ → Set α, (∀ i, MeasurableSet' (f i)) → MeasurableSet' (⋃ i, f i)
#align measurable_space MeasurableSpace

instance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ := h

/-- `MeasurableSet s` means that `s` is measurable (in the ambient measure space on `α`) -/
def MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=
  ‹MeasurableSpace α›.MeasurableSet' s
#align measurable_set MeasurableSet

-- Porting note (#11215): TODO: `scoped[MeasureTheory]` doesn't work for unknown reason
namespace MeasureTheory
set_option quotPrecheck false in
/-- Notation for `MeasurableSet` with respect to a non-standard σ-algebra. -/
scoped notation "MeasurableSet[" m "]" => @MeasurableSet _ m

end MeasureTheory
open MeasureTheory

section

open scoped symmDiff

@[simp, measurability]
theorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=
  MeasurableSpace.measurableSet_empty _
#align measurable_set.empty MeasurableSet.empty

variable {m : MeasurableSpace α}

@[measurability]
protected theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ :=
  MeasurableSpace.measurableSet_compl _ s
#align measurable_set.compl MeasurableSet.compl

protected theorem MeasurableSet.of_compl (h : MeasurableSet sᶜ) : MeasurableSet s :=
  compl_compl s ▸ h.compl
#align measurable_set.of_compl MeasurableSet.of_compl

@[simp]
theorem MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ MeasurableSet s :=
  ⟨.of_compl, .compl⟩
#align measurable_set.compl_iff MeasurableSet.compl_iff

@[simp, measurability]
protected theorem MeasurableSet.univ : MeasurableSet (univ : Set α) :=
  .of_compl <| by simp
#align measurable_set.univ MeasurableSet.univ

@[nontriviality, measurability]
theorem Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s
#align subsingleton.measurable_set Subsingleton.measurableSet

theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by
  rwa [← h]
#align measurable_set.congr MeasurableSet.congr

@[measurability]
protected theorem MeasurableSet.iUnion [Countable ι] ⦃f : ι → Set α⦄
    (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) := by
  cases isEmpty_or_nonempty ι
  · simp
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective _ he (fun _ => rfl)]
    exact m.measurableSet_iUnion _ fun _ => h _
#align measurable_set.Union MeasurableSet.iUnion

@[deprecated MeasurableSet.iUnion]
theorem MeasurableSet.biUnion_decode₂ [Encodable β] ⦃f : β → Set α⦄ (h : ∀ b, MeasurableSet (f b))
    (n : ℕ) : MeasurableSet (⋃ b ∈ decode₂ β n, f b) :=
  .iUnion fun _ => .iUnion fun _ => h _
#align measurable_set.bUnion_decode₂ MeasurableSet.biUnion_decode₂

protected theorem MeasurableSet.biUnion {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) := by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion (by simpa using h)
#align measurable_set.bUnion MeasurableSet.biUnion

theorem Set.Finite.measurableSet_biUnion {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  .biUnion hs.countable h
#align set.finite.measurable_set_bUnion Set.Finite.measurableSet_biUnion

theorem Finset.measurableSet_biUnion {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biUnion h
#align finset.measurable_set_bUnion Finset.measurableSet_biUnion

protected theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) := by
  rw [sUnion_eq_biUnion]
  exact .biUnion hs h
#align measurable_set.sUnion MeasurableSet.sUnion

theorem Set.Finite.measurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs.countable h
#align set.finite.measurable_set_sUnion Set.Finite.measurableSet_sUnion

@[measurability]
theorem MeasurableSet.iInter [Countable ι] {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) :=
  .of_compl <| by rw [compl_iInter]; exact .iUnion fun b => (h b).compl
#align measurable_set.Inter MeasurableSet.iInter

theorem MeasurableSet.biInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .of_compl <| by rw [compl_iInter₂]; exact .biUnion hs fun b hb => (h b hb).compl
#align measurable_set.bInter MeasurableSet.biInter

theorem Set.Finite.measurableSet_biInter {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
 .biInter hs.countable h
#align set.finite.measurable_set_bInter Set.Finite.measurableSet_biInter

theorem Finset.measurableSet_biInter {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biInter h
#align finset.measurable_set_bInter Finset.measurableSet_biInter

theorem MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_biInter]
  exact MeasurableSet.biInter hs h
#align measurable_set.sInter MeasurableSet.sInter

theorem Set.Finite.measurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs.countable h
#align set.finite.measurable_set_sInter Set.Finite.measurableSet_sInter

@[simp, measurability]
protected theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]
  exact .iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)
#align measurable_set.union MeasurableSet.union

@[simp, measurability]
protected theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂) := by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl
#align measurable_set.inter MeasurableSet.inter

@[simp, measurability]
protected theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl
#align measurable_set.diff MeasurableSet.diff

@[simp, measurability]
protected lemma MeasurableSet.himp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ⇨ s₂) := by rw [himp_eq]; exact h₂.union h₁.compl

@[simp, measurability]
protected theorem MeasurableSet.symmDiff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)
#align measurable_set.symm_diff MeasurableSet.symmDiff

@[simp, measurability]
protected lemma MeasurableSet.bihimp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ⇔ s₂) := (h₂.himp h₁).inter (h₁.himp h₂)

@[simp, measurability]
protected theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t)
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)
#align measurable_set.ite MeasurableSet.ite

theorem MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p → MeasurableSet s)
    (ht : ¬p → MeasurableSet t) : MeasurableSet (ite p s t) := by
  split_ifs with h
  exacts [hs h, ht h]
#align measurable_set.ite' MeasurableSet.ite'

@[simp, measurability]
protected theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) {i : Bool} : MeasurableSet (cond i s₁ s₂) := by
  cases i
  exacts [h₂, h₁]
#align measurable_set.cond MeasurableSet.cond

@[simp, measurability]
protected theorem MeasurableSet.disjointed {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) (n) :
    MeasurableSet (disjointed f n) :=
  disjointedRec (fun _ _ ht => MeasurableSet.diff ht <| h _) (h n)
#align measurable_set.disjointed MeasurableSet.disjointed

protected theorem MeasurableSet.const (p : Prop) : MeasurableSet { _a : α | p } := by
  by_cases p <;> simp [*]
#align measurable_set.const MeasurableSet.const

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩
#align nonempty_measurable_superset nonempty_measurable_superset

end

theorem MeasurableSpace.measurableSet_injective : Injective (@MeasurableSet α)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _ => by congr

@[ext]
theorem MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α}
    (h : ∀ s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂ :=
  measurableSet_injective <| funext fun s => propext (h s)
#align measurable_space.ext MeasurableSpace.ext

theorem MeasurableSpace.ext_iff {m₁ m₂ : MeasurableSpace α} :
    m₁ = m₂ ↔ ∀ s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s :=
  ⟨fun h _ => h ▸ Iff.rfl, MeasurableSpace.ext⟩
#align measurable_space.ext_iff MeasurableSpace.ext_iff

/-- A typeclass mixin for `MeasurableSpace`s such that each singleton is measurable. -/
class MeasurableSingletonClass (α : Type*) [MeasurableSpace α] : Prop where
  /-- A singleton is a measurable set. -/
  measurableSet_singleton : ∀ x, MeasurableSet ({x} : Set α)
#align measurable_singleton_class MeasurableSingletonClass

export MeasurableSingletonClass (measurableSet_singleton)

@[simp]
lemma MeasurableSet.singleton [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    MeasurableSet {a} :=
  measurableSet_singleton a

section MeasurableSingletonClass

variable [MeasurableSpace α] [MeasurableSingletonClass α]

@[measurability]
theorem measurableSet_eq {a : α} : MeasurableSet { x | x = a } := .singleton a
#align measurable_set_eq measurableSet_eq

@[measurability]
protected theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) :
    MeasurableSet (insert a s) :=
  .union (.singleton a) hs
#align measurable_set.insert MeasurableSet.insert

@[simp]
theorem measurableSet_insert {a : α} {s : Set α} : MeasurableSet (insert a s) ↔ MeasurableSet s :=
  ⟨fun h =>
    if ha : a ∈ s then by rwa [← insert_eq_of_mem ha]
    else insert_diff_self_of_not_mem ha ▸ h.diff (.singleton _),
    fun h => h.insert a⟩
#align measurable_set_insert measurableSet_insert

theorem Set.Subsingleton.measurableSet {s : Set α} (hs : s.Subsingleton) : MeasurableSet s :=
  hs.induction_on .empty .singleton
#align set.subsingleton.measurable_set Set.Subsingleton.measurableSet

theorem Set.Finite.measurableSet {s : Set α} (hs : s.Finite) : MeasurableSet s :=
  Finite.induction_on hs MeasurableSet.empty fun _ _ hsm => hsm.insert _
#align set.finite.measurable_set Set.Finite.measurableSet

@[measurability]
protected theorem Finset.measurableSet (s : Finset α) : MeasurableSet (↑s : Set α) :=
  s.finite_toSet.measurableSet
#align finset.measurable_set Finset.measurableSet

theorem Set.Countable.measurableSet {s : Set α} (hs : s.Countable) : MeasurableSet s := by
  rw [← biUnion_of_singleton s]
  exact .biUnion hs fun b _ => .singleton b
#align set.countable.measurable_set Set.Countable.measurableSet

end MeasurableSingletonClass

namespace MeasurableSpace

/-- Copy of a `MeasurableSpace` with a new `MeasurableSet` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (m : MeasurableSpace α) (p : Set α → Prop) (h : ∀ s, p s ↔ MeasurableSet[m] s) :
    MeasurableSpace α where
  MeasurableSet' := p
  measurableSet_empty := by simpa only [h] using m.measurableSet_empty
  measurableSet_compl := by simpa only [h] using m.measurableSet_compl
  measurableSet_iUnion := by simpa only [h] using m.measurableSet_iUnion

lemma measurableSet_copy {m : MeasurableSpace α} {p : Set α → Prop}
    (h : ∀ s, p s ↔ MeasurableSet[m] s) {s} : MeasurableSet[.copy m p h] s ↔ p s :=
  Iff.rfl

lemma copy_eq {m : MeasurableSpace α} {p : Set α → Prop} (h : ∀ s, p s ↔ MeasurableSet[m] s) :
    m.copy p h = m :=
  ext h

section CompleteLattice

instance : LE (MeasurableSpace α) where le m₁ m₂ := ∀ s, MeasurableSet[m₁] s → MeasurableSet[m₂] s

theorem le_def {α} {a b : MeasurableSpace α} : a ≤ b ↔ a.MeasurableSet' ≤ b.MeasurableSet' :=
  Iff.rfl
#align measurable_space.le_def MeasurableSpace.le_def

instance : PartialOrder (MeasurableSpace α) :=
  { PartialOrder.lift (@MeasurableSet α) measurableSet_injective with
    le := LE.le
    lt := fun m₁ m₂ => m₁ ≤ m₂ ∧ ¬m₂ ≤ m₁ }

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | protected basic : ∀ u ∈ s, GenerateMeasurable s u
  | protected empty : GenerateMeasurable s ∅
  | protected compl : ∀ t, GenerateMeasurable s t → GenerateMeasurable s tᶜ
  | protected iUnion : ∀ f : ℕ → Set α, (∀ n, GenerateMeasurable s (f n)) →
      GenerateMeasurable s (⋃ i, f i)
#align measurable_space.generate_measurable MeasurableSpace.GenerateMeasurable

/-- Construct the smallest measure space containing a collection of basic sets -/
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion
#align measurable_space.generate_from MeasurableSpace.generateFrom

theorem measurableSet_generateFrom {s : Set (Set α)} {t : Set α} (ht : t ∈ s) :
    MeasurableSet[generateFrom s] t :=
  .basic t ht
#align measurable_space.measurable_set_generate_from MeasurableSpace.measurableSet_generateFrom

@[elab_as_elim]
theorem generateFrom_induction (p : Set α → Prop) (C : Set (Set α)) (hC : ∀ t ∈ C, p t)
    (h_empty : p ∅) (h_compl : ∀ t, p t → p tᶜ)
    (h_Union : ∀ f : ℕ → Set α, (∀ n, p (f n)) → p (⋃ i, f i)) {s : Set α}
    (hs : MeasurableSet[generateFrom C] s) : p s := by
  induction hs
  exacts [hC _ ‹_›, h_empty, h_compl _ ‹_›, h_Union ‹_› ‹_›]
#align measurable_space.generate_from_induction MeasurableSpace.generateFrom_induction

theorem generateFrom_le {s : Set (Set α)} {m : MeasurableSpace α}
    (h : ∀ t ∈ s, MeasurableSet[m] t) : generateFrom s ≤ m :=
  fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h .empty (fun _ _ => .compl) fun _ _ hf => .iUnion hf
#align measurable_space.generate_from_le MeasurableSpace.generateFrom_le

theorem generateFrom_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
    generateFrom s ≤ m ↔ s ⊆ { t | MeasurableSet[m] t } :=
  Iff.intro (fun h _ hu => h _ <| measurableSet_generateFrom hu) fun h => generateFrom_le h
#align measurable_space.generate_from_le_iff MeasurableSpace.generateFrom_le_iff

@[simp]
theorem generateFrom_measurableSet [MeasurableSpace α] :
    generateFrom { s : Set α | MeasurableSet s } = ‹_› :=
  le_antisymm (generateFrom_le fun _ => id) fun _ => measurableSet_generateFrom
#align measurable_space.generate_from_measurable_set MeasurableSpace.generateFrom_measurableSet

theorem forall_generateFrom_mem_iff_mem_iff {S : Set (Set α)} {x y : α} :
    (∀ s, MeasurableSet[generateFrom S] s → (x ∈ s ↔ y ∈ s)) ↔ (∀ s ∈ S, x ∈ s ↔ y ∈ s) := by
  refine ⟨fun H s hs ↦ H s (.basic s hs), fun H s ↦ ?_⟩
  apply generateFrom_induction
  · exact H
  · rfl
  · exact fun _ ↦ Iff.not
  · intro f hf
    simp only [mem_iUnion, hf]

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
protected def mkOfClosure (g : Set (Set α)) (hg : { t | MeasurableSet[generateFrom g] t } = g) :
    MeasurableSpace α :=
  (generateFrom g).copy (· ∈ g) <| Set.ext_iff.1 hg.symm
#align measurable_space.mk_of_closure MeasurableSpace.mkOfClosure

theorem mkOfClosure_sets {s : Set (Set α)} {hs : { t | MeasurableSet[generateFrom s] t } = s} :
    MeasurableSpace.mkOfClosure s hs = generateFrom s :=
  copy_eq _
#align measurable_space.mk_of_closure_sets MeasurableSpace.mkOfClosure_sets

/-- We get a Galois insertion between `σ`-algebras on `α` and `Set (Set α)` by using `generate_from`
  on one side and the collection of measurable sets on the other side. -/
def giGenerateFrom : GaloisInsertion (@generateFrom α) fun m => { t | MeasurableSet[m] t } where
  gc _ := generateFrom_le_iff
  le_l_u _ _ := measurableSet_generateFrom
  choice g hg := MeasurableSpace.mkOfClosure g <| le_antisymm hg <| (generateFrom_le_iff _).1 le_rfl
  choice_eq _ _ := mkOfClosure_sets
#align measurable_space.gi_generate_from MeasurableSpace.giGenerateFrom

instance : CompleteLattice (MeasurableSpace α) :=
  giGenerateFrom.liftCompleteLattice

instance : Inhabited (MeasurableSpace α) := ⟨⊤⟩

@[mono]
theorem generateFrom_mono {s t : Set (Set α)} (h : s ⊆ t) : generateFrom s ≤ generateFrom t :=
  giGenerateFrom.gc.monotone_l h
#align measurable_space.generate_from_mono MeasurableSpace.generateFrom_mono

theorem generateFrom_sup_generateFrom {s t : Set (Set α)} :
    generateFrom s ⊔ generateFrom t = generateFrom (s ∪ t) :=
  (@giGenerateFrom α).gc.l_sup.symm
#align measurable_space.generate_from_sup_generate_from MeasurableSpace.generateFrom_sup_generateFrom

lemma iSup_generateFrom (s : ι → Set (Set α)) :
    ⨆ i, generateFrom (s i) = generateFrom (⋃ i, s i) :=
  (@MeasurableSpace.giGenerateFrom α).gc.l_iSup.symm

@[simp]
lemma generateFrom_empty : generateFrom (∅ : Set (Set α)) = ⊥ :=
  le_bot_iff.mp (generateFrom_le (by simp))

theorem generateFrom_singleton_empty : generateFrom {∅} = (⊥ : MeasurableSpace α) :=
  bot_unique <| generateFrom_le <| by simp [@MeasurableSet.empty α ⊥]
#align measurable_space.generate_from_singleton_empty MeasurableSpace.generateFrom_singleton_empty

theorem generateFrom_singleton_univ : generateFrom {Set.univ} = (⊥ : MeasurableSpace α) :=
  bot_unique <| generateFrom_le <| by simp
#align measurable_space.generate_from_singleton_univ MeasurableSpace.generateFrom_singleton_univ

@[simp]
theorem generateFrom_insert_univ (S : Set (Set α)) :
    generateFrom (insert Set.univ S) = generateFrom S := by
  rw [insert_eq, ← generateFrom_sup_generateFrom, generateFrom_singleton_univ, bot_sup_eq]
#align measurable_space.generate_from_insert_univ MeasurableSpace.generateFrom_insert_univ

@[simp]
theorem generateFrom_insert_empty (S : Set (Set α)) :
    generateFrom (insert ∅ S) = generateFrom S := by
  rw [insert_eq, ← generateFrom_sup_generateFrom, generateFrom_singleton_empty, bot_sup_eq]
#align measurable_space.generate_from_insert_empty MeasurableSpace.generateFrom_insert_empty

theorem measurableSet_bot_iff {s : Set α} : MeasurableSet[⊥] s ↔ s = ∅ ∨ s = univ :=
  let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ
      measurableSet_empty := Or.inl rfl
      measurableSet_compl := by simp (config := { contextual := true }) [or_imp]
      measurableSet_iUnion := fun f hf => sUnion_mem_empty_univ (forall_mem_range.2 hf) }
  have : b = ⊥ :=
    bot_unique fun s hs =>
      hs.elim (fun s => s.symm ▸ @measurableSet_empty _ ⊥) fun s =>
        s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl
#align measurable_space.measurable_set_bot_iff MeasurableSpace.measurableSet_bot_iff

@[simp, measurability] theorem measurableSet_top {s : Set α} : MeasurableSet[⊤] s := trivial
#align measurable_space.measurable_set_top MeasurableSpace.measurableSet_top

@[simp, nolint simpNF] -- Porting note (#11215): TODO: `simpNF` claims that
-- this lemma doesn't simplify LHS
theorem measurableSet_inf {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    MeasurableSet[m₁ ⊓ m₂] s ↔ MeasurableSet[m₁] s ∧ MeasurableSet[m₂] s :=
  Iff.rfl
#align measurable_space.measurable_set_inf MeasurableSpace.measurableSet_inf

@[simp]
theorem measurableSet_sInf {ms : Set (MeasurableSpace α)} {s : Set α} :
    MeasurableSet[sInf ms] s ↔ ∀ m ∈ ms, MeasurableSet[m] s :=
  show s ∈ ⋂₀ _ ↔ _ by simp
#align measurable_space.measurable_set_Inf MeasurableSpace.measurableSet_sInf

theorem measurableSet_iInf {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    MeasurableSet[iInf m] s ↔ ∀ i, MeasurableSet[m i] s := by
  rw [iInf, measurableSet_sInf, forall_mem_range]
#align measurable_space.measurable_set_infi MeasurableSpace.measurableSet_iInf

theorem measurableSet_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    MeasurableSet[m₁ ⊔ m₂] s ↔ GenerateMeasurable (MeasurableSet[m₁] ∪ MeasurableSet[m₂]) s :=
  Iff.rfl
#align measurable_space.measurable_set_sup MeasurableSpace.measurableSet_sup

theorem measurableSet_sSup {ms : Set (MeasurableSpace α)} {s : Set α} :
    MeasurableSet[sSup ms] s ↔
      GenerateMeasurable { s : Set α | ∃ m ∈ ms, MeasurableSet[m] s } s := by
  change GenerateMeasurable (⋃₀ _) _ ↔ _
  simp [← setOf_exists]
#align measurable_space.measurable_set_Sup MeasurableSpace.measurableSet_sSup

theorem measurableSet_iSup {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    MeasurableSet[iSup m] s ↔ GenerateMeasurable { s : Set α | ∃ i, MeasurableSet[m i] s } s := by
  simp only [iSup, measurableSet_sSup, exists_range_iff]
#align measurable_space.measurable_set_supr MeasurableSpace.measurableSet_iSup

theorem measurableSpace_iSup_eq (m : ι → MeasurableSpace α) :
    ⨆ n, m n = generateFrom { s | ∃ n, MeasurableSet[m n] s } := by
  ext s
  rw [measurableSet_iSup]
  rfl
#align measurable_space.measurable_space_supr_eq MeasurableSpace.measurableSpace_iSup_eq

theorem generateFrom_iUnion_measurableSet (m : ι → MeasurableSpace α) :
    generateFrom (⋃ n, { t | MeasurableSet[m n] t }) = ⨆ n, m n :=
  (@giGenerateFrom α).l_iSup_u m
#align measurable_space.generate_from_Union_measurable_set MeasurableSpace.generateFrom_iUnion_measurableSet

end CompleteLattice

end MeasurableSpace

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)
#align measurable Measurable

namespace MeasureTheory

set_option quotPrecheck false in
/-- Notation for `Measurable` with respect to a non-standanrd σ-algebra in the domain. -/
scoped notation "Measurable[" m "]" => @Measurable _ _ m _

end MeasureTheory

section MeasurableFunctions

@[measurability]
theorem measurable_id {_ : MeasurableSpace α} : Measurable (@id α) := fun _ => id
#align measurable_id measurable_id

@[measurability]
theorem measurable_id' {_ : MeasurableSpace α} : Measurable fun a : α => a := measurable_id
#align measurable_id' measurable_id'

protected theorem Measurable.comp {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  fun _ h => hf (hg h)
#align measurable.comp Measurable.comp

-- This is needed due to reducibility issues with the `measurability` tactic.
@[aesop safe 50 (rule_sets := [Measurable])]
protected theorem Measurable.comp' {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (fun x => g (f x)) := Measurable.comp hg hf

@[simp, measurability]
theorem measurable_const {_ : MeasurableSpace α} {_ : MeasurableSpace β} {a : α} :
    Measurable fun _ : β => a := fun s _ => .const (a ∈ s)
#align measurable_const measurable_const

theorem Measurable.le {α} {m m0 : MeasurableSpace α} {_ : MeasurableSpace β} (hm : m ≤ m0)
    {f : α → β} (hf : Measurable[m] f) : Measurable[m0] f := fun _ hs => hm _ (hf hs)
#align measurable.le Measurable.le

end MeasurableFunctions

/-- A typeclass mixin for `MeasurableSpace`s such that all sets are measurable. -/
class DiscreteMeasurableSpace (α : Type*) [MeasurableSpace α] : Prop where
  /-- Do not use this. Use `measurableSet_discrete` instead. -/
  forall_measurableSet : ∀ s : Set α, MeasurableSet s

instance : @DiscreteMeasurableSpace α ⊤ :=
  @DiscreteMeasurableSpace.mk _ (_) fun _ ↦ MeasurableSpace.measurableSet_top

-- See note [lower instance priority]
instance (priority := 100) MeasurableSingletonClass.toDiscreteMeasurableSpace [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] : DiscreteMeasurableSpace α where
  forall_measurableSet _ := (Set.to_countable _).measurableSet

section DiscreteMeasurableSpace
variable [MeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace α]

@[measurability] lemma measurableSet_discrete (s : Set α) : MeasurableSet s :=
  DiscreteMeasurableSpace.forall_measurableSet _

@[measurability]
lemma measurable_discrete (f : α → β) : Measurable f := fun _ _ ↦ measurableSet_discrete _
#align measurable_space.top.measurable measurable_discrete

/-- Warning: Creates a typeclass loop with `MeasurableSingletonClass.toDiscreteMeasurableSpace`.
To be monitored. -/
-- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableSingletonClass :
    MeasurableSingletonClass α where
  measurableSet_singleton _ := measurableSet_discrete _

end DiscreteMeasurableSpace
