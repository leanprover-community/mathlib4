/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Set.Countable
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FunProp.Attr
import Mathlib.Tactic.Measurability

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

assert_not_exists Covariant MonoidWithZero

open Set Encodable Function Equiv

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

instance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ := h

/-- `MeasurableSet s` means that `s` is measurable (in the ambient measure space on `α`) -/
def MeasurableSet [MeasurableSpace α] (s : Set α) : Prop :=
  ‹MeasurableSpace α›.MeasurableSet' s

/-- Notation for `MeasurableSet` with respect to a non-standard σ-algebra. -/
scoped[MeasureTheory] notation "MeasurableSet[" m "]" => @MeasurableSet _ m

open MeasureTheory

section

open scoped symmDiff

@[simp, measurability]
theorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=
  MeasurableSpace.measurableSet_empty _

variable {m : MeasurableSpace α}

@[measurability]
protected theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet sᶜ :=
  MeasurableSpace.measurableSet_compl _ s

protected theorem MeasurableSet.of_compl (h : MeasurableSet sᶜ) : MeasurableSet s :=
  compl_compl s ▸ h.compl

@[simp]
theorem MeasurableSet.compl_iff : MeasurableSet sᶜ ↔ MeasurableSet s :=
  ⟨.of_compl, .compl⟩

@[simp, measurability]
protected theorem MeasurableSet.univ : MeasurableSet (univ : Set α) :=
  .of_compl <| by simp

@[nontriviality, measurability]
theorem Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by
  rwa [← h]

@[measurability]
protected theorem MeasurableSet.iUnion [Countable ι] ⦃f : ι → Set α⦄
    (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) := by
  cases isEmpty_or_nonempty ι
  · simp
  · rcases exists_surjective_nat ι with ⟨e, he⟩
    rw [← iUnion_congr_of_surjective _ he (fun _ => rfl)]
    exact m.measurableSet_iUnion _ fun _ => h _

protected theorem MeasurableSet.biUnion {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) := by
  rw [biUnion_eq_iUnion]
  have := hs.to_subtype
  exact MeasurableSet.iUnion (by simpa using h)

theorem Set.Finite.measurableSet_biUnion {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  .biUnion hs.countable h

theorem Finset.measurableSet_biUnion {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋃ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biUnion h

protected theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : s.Countable)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) := by
  rw [sUnion_eq_biUnion]
  exact .biUnion hs h

theorem Set.Finite.measurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋃₀ s) :=
  MeasurableSet.sUnion hs.countable h

@[measurability]
theorem MeasurableSet.iInter [Countable ι] {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋂ b, f b) :=
  .of_compl <| by rw [compl_iInter]; exact .iUnion fun b => (h b).compl

theorem MeasurableSet.biInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .of_compl <| by rw [compl_iInter₂]; exact .biUnion hs fun b hb => (h b hb).compl

theorem Set.Finite.measurableSet_biInter {f : β → Set α} {s : Set β} (hs : s.Finite)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  .biInter hs.countable h

theorem Finset.measurableSet_biInter {f : β → Set α} (s : Finset β)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b) :=
  s.finite_toSet.measurableSet_biInter h

theorem MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_biInter]
  exact MeasurableSet.biInter hs h

theorem Set.Finite.measurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, MeasurableSet t) : MeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs.countable h

@[simp, measurability]
protected theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]
  exact .iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp, measurability]
protected theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂) := by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp, measurability]
protected theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl

@[simp, measurability]
protected lemma MeasurableSet.himp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ⇨ s₂) := by rw [himp_eq]; exact h₂.union h₁.compl

@[simp, measurability]
protected theorem MeasurableSet.symmDiff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp, measurability]
protected lemma MeasurableSet.bihimp {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ⇔ s₂) := (h₂.himp h₁).inter (h₁.himp h₂)

@[simp, measurability]
protected theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t)
    (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)

open Classical in
theorem MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p → MeasurableSet s)
    (ht : ¬p → MeasurableSet t) : MeasurableSet (ite p s t) := by
  split_ifs with h
  exacts [hs h, ht h]

@[simp, measurability]
protected theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁)
    (h₂ : MeasurableSet s₂) {i : Bool} : MeasurableSet (cond i s₁ s₂) := by
  cases i
  exacts [h₂, h₁]

protected theorem MeasurableSet.const (p : Prop) : MeasurableSet { _a : α | p } := by
  by_cases p <;> simp [*]

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨univ, subset_univ s, MeasurableSet.univ⟩⟩

end

theorem MeasurableSpace.measurableSet_injective : Injective (@MeasurableSet α)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, _ => by congr

@[ext]
theorem MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α}
    (h : ∀ s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂ :=
  measurableSet_injective <| funext fun s => propext (h s)

/-- A typeclass mixin for `MeasurableSpace`s such that each singleton is measurable. -/
class MeasurableSingletonClass (α : Type*) [MeasurableSpace α] : Prop where
  /-- A singleton is a measurable set. -/
  measurableSet_singleton : ∀ x, MeasurableSet ({x} : Set α)

export MeasurableSingletonClass (measurableSet_singleton)

@[simp]
lemma MeasurableSet.singleton [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    MeasurableSet {a} :=
  measurableSet_singleton a

section MeasurableSingletonClass

variable [MeasurableSpace α] [MeasurableSingletonClass α]

@[measurability]
theorem measurableSet_eq {a : α} : MeasurableSet { x | x = a } := .singleton a

@[measurability]
protected theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) :
    MeasurableSet (insert a s) :=
  .union (.singleton a) hs

@[simp]
theorem measurableSet_insert {a : α} {s : Set α} :
    MeasurableSet (insert a s) ↔ MeasurableSet s := by
  classical
  exact ⟨fun h =>
    if ha : a ∈ s then by rwa [← insert_eq_of_mem ha]
    else insert_diff_self_of_notMem ha ▸ h.diff (.singleton _),
    fun h => h.insert a⟩

theorem Set.Subsingleton.measurableSet {s : Set α} (hs : s.Subsingleton) : MeasurableSet s :=
  hs.induction_on .empty .singleton

theorem Set.Finite.measurableSet {s : Set α} (hs : s.Finite) : MeasurableSet s :=
  Finite.induction_on _ hs .empty fun _ _ hsm => hsm.insert _

@[measurability]
protected theorem Finset.measurableSet (s : Finset α) : MeasurableSet (↑s : Set α) :=
  s.finite_toSet.measurableSet

theorem Set.Countable.measurableSet {s : Set α} (hs : s.Countable) : MeasurableSet s := by
  rw [← biUnion_of_singleton s]
  exact .biUnion hs fun b _ => .singleton b

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

/-- Construct the smallest measure space containing a collection of basic sets -/
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurableSet_empty := .empty
  measurableSet_compl := .compl
  measurableSet_iUnion := .iUnion

theorem measurableSet_generateFrom {s : Set (Set α)} {t : Set α} (ht : t ∈ s) :
    MeasurableSet[generateFrom s] t :=
  .basic t ht

@[elab_as_elim]
theorem generateFrom_induction (C : Set (Set α))
    (p : ∀ s : Set α, MeasurableSet[generateFrom C] s → Prop) (hC : ∀ t ∈ C, ∀ ht, p t ht)
    (empty : p ∅ (measurableSet_empty _)) (compl : ∀ t ht, p t ht → p tᶜ ht.compl)
    (iUnion : ∀ (s : ℕ → Set α) (hs : ∀ n, MeasurableSet[generateFrom C] (s n)),
      (∀ n, p (s n) (hs n)) → p (⋃ i, s i) (.iUnion hs)) (s : Set α)
    (hs : MeasurableSet[generateFrom C] s) : p s hs := by
  induction hs
  exacts [hC _ ‹_› _, empty, compl _ ‹_› ‹_›, iUnion ‹_› ‹_› ‹_›]

theorem generateFrom_le {s : Set (Set α)} {m : MeasurableSpace α}
    (h : ∀ t ∈ s, MeasurableSet[m] t) : generateFrom s ≤ m :=
  fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h .empty (fun _ _ => .compl) fun _ _ hf => .iUnion hf

theorem generateFrom_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
    generateFrom s ≤ m ↔ s ⊆ { t | MeasurableSet[m] t } :=
  Iff.intro (fun h _ hu => h _ <| measurableSet_generateFrom hu) fun h => generateFrom_le h

@[simp]
theorem generateFrom_measurableSet [MeasurableSpace α] :
    generateFrom { s : Set α | MeasurableSet s } = ‹_› :=
  le_antisymm (generateFrom_le fun _ => id) fun _ => measurableSet_generateFrom

theorem forall_generateFrom_mem_iff_mem_iff {S : Set (Set α)} {x y : α} :
    (∀ s, MeasurableSet[generateFrom S] s → (x ∈ s ↔ y ∈ s)) ↔ (∀ s ∈ S, x ∈ s ↔ y ∈ s) := by
  refine ⟨fun H s hs ↦ H s (.basic s hs), fun H s ↦ ?_⟩
  apply generateFrom_induction
  · exact fun s hs _ ↦ H s hs
  · rfl
  · exact fun _ _ ↦ Iff.not
  · intro f _ hf
    simp only [mem_iUnion, hf]

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
protected def mkOfClosure (g : Set (Set α)) (hg : { t | MeasurableSet[generateFrom g] t } = g) :
    MeasurableSpace α :=
  (generateFrom g).copy (· ∈ g) <| Set.ext_iff.1 hg.symm

theorem mkOfClosure_sets {s : Set (Set α)} {hs : { t | MeasurableSet[generateFrom s] t } = s} :
    MeasurableSpace.mkOfClosure s hs = generateFrom s :=
  copy_eq _

/-- We get a Galois insertion between `σ`-algebras on `α` and `Set (Set α)` by using `generate_from`
  on one side and the collection of measurable sets on the other side. -/
def giGenerateFrom : GaloisInsertion (@generateFrom α) fun m => { t | MeasurableSet[m] t } where
  gc _ := generateFrom_le_iff
  le_l_u _ _ := measurableSet_generateFrom
  choice g hg := MeasurableSpace.mkOfClosure g <| le_antisymm hg <| (generateFrom_le_iff _).1 le_rfl
  choice_eq _ _ := mkOfClosure_sets

instance : CompleteLattice (MeasurableSpace α) :=
  giGenerateFrom.liftCompleteLattice

instance : Inhabited (MeasurableSpace α) := ⟨⊤⟩

@[mono]
theorem generateFrom_mono {s t : Set (Set α)} (h : s ⊆ t) : generateFrom s ≤ generateFrom t :=
  giGenerateFrom.gc.monotone_l h

theorem generateFrom_sup_generateFrom {s t : Set (Set α)} :
    generateFrom s ⊔ generateFrom t = generateFrom (s ∪ t) :=
  (@giGenerateFrom α).gc.l_sup.symm

lemma iSup_generateFrom (s : ι → Set (Set α)) :
    ⨆ i, generateFrom (s i) = generateFrom (⋃ i, s i) :=
  (@MeasurableSpace.giGenerateFrom α).gc.l_iSup.symm

@[simp]
lemma generateFrom_empty : generateFrom (∅ : Set (Set α)) = ⊥ :=
  le_bot_iff.mp (generateFrom_le (by simp))

theorem generateFrom_singleton_empty : generateFrom {∅} = (⊥ : MeasurableSpace α) :=
  bot_unique <| generateFrom_le <| by simp [@MeasurableSet.empty α ⊥]

theorem generateFrom_singleton_univ : generateFrom {Set.univ} = (⊥ : MeasurableSpace α) :=
  bot_unique <| generateFrom_le <| by simp

@[simp]
theorem generateFrom_insert_univ (S : Set (Set α)) :
    generateFrom (insert Set.univ S) = generateFrom S := by
  rw [insert_eq, ← generateFrom_sup_generateFrom, generateFrom_singleton_univ, bot_sup_eq]

@[simp]
theorem generateFrom_insert_empty (S : Set (Set α)) :
    generateFrom (insert ∅ S) = generateFrom S := by
  rw [insert_eq, ← generateFrom_sup_generateFrom, generateFrom_singleton_empty, bot_sup_eq]

theorem measurableSet_bot_iff {s : Set α} : MeasurableSet[⊥] s ↔ s = ∅ ∨ s = univ :=
  let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ
      measurableSet_empty := Or.inl rfl
      measurableSet_compl := by simp +contextual [or_imp]
      measurableSet_iUnion := fun _ hf => sUnion_mem_empty_univ (forall_mem_range.2 hf) }
  have : b = ⊥ :=
    bot_unique fun _ hs =>
      hs.elim (fun s => s.symm ▸ @measurableSet_empty _ ⊥) fun s =>
        s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl

@[simp, measurability] theorem measurableSet_top {s : Set α} : MeasurableSet[⊤] s := trivial

@[simp]
-- The `m₁` parameter gets filled in by typeclass instance synthesis (for some reason...)
-- so we have to order it *after* `m₂`. Otherwise `simp` can't apply this lemma.
theorem measurableSet_inf {m₂ m₁ : MeasurableSpace α} {s : Set α} :
    MeasurableSet[m₁ ⊓ m₂] s ↔ MeasurableSet[m₁] s ∧ MeasurableSet[m₂] s :=
  Iff.rfl

@[simp]
theorem measurableSet_sInf {ms : Set (MeasurableSpace α)} {s : Set α} :
    MeasurableSet[sInf ms] s ↔ ∀ m ∈ ms, MeasurableSet[m] s :=
  show s ∈ ⋂₀ _ ↔ _ by simp

theorem measurableSet_iInf {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    MeasurableSet[iInf m] s ↔ ∀ i, MeasurableSet[m i] s := by
  rw [iInf, measurableSet_sInf, forall_mem_range]

theorem measurableSet_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    MeasurableSet[m₁ ⊔ m₂] s ↔ GenerateMeasurable (MeasurableSet[m₁] ∪ MeasurableSet[m₂]) s :=
  Iff.rfl

theorem measurableSet_sSup {ms : Set (MeasurableSpace α)} {s : Set α} :
    MeasurableSet[sSup ms] s ↔
      GenerateMeasurable { s : Set α | ∃ m ∈ ms, MeasurableSet[m] s } s := by
  change GenerateMeasurable (⋃₀ _) _ ↔ _
  simp [← setOf_exists]

theorem measurableSet_iSup {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    MeasurableSet[iSup m] s ↔ GenerateMeasurable { s : Set α | ∃ i, MeasurableSet[m i] s } s := by
  simp only [iSup, measurableSet_sSup, exists_range_iff]

theorem measurableSpace_iSup_eq (m : ι → MeasurableSpace α) :
    ⨆ n, m n = generateFrom { s | ∃ n, MeasurableSet[m n] s } := by
  ext s
  rw [measurableSet_iSup]
  rfl

theorem generateFrom_iUnion_measurableSet (m : ι → MeasurableSpace α) :
    generateFrom (⋃ n, { t | MeasurableSet[m n] t }) = ⨆ n, m n :=
  (@giGenerateFrom α).l_iSup_u m

end CompleteLattice

end MeasurableSpace

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
@[fun_prop]
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)

namespace MeasureTheory

set_option quotPrecheck false in
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measurable[" m "]" => @Measurable _ _ m _
/-- Notation for `Measurable` with respect to a non-standard σ-algebra in the domain and codomain.
-/
scoped notation "Measurable[" mα ", " mβ "]" => @Measurable _ _ mα mβ

end MeasureTheory

section MeasurableFunctions

@[measurability]
theorem measurable_id {_ : MeasurableSpace α} : Measurable (@id α) := fun _ => id

@[fun_prop, measurability]
theorem measurable_id' {_ : MeasurableSpace α} : Measurable fun a : α => a := measurable_id

protected theorem Measurable.comp {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (g ∘ f) :=
  fun _ h => hf (hg h)

-- This is needed due to reducibility issues with the `measurability` tactic.
@[fun_prop, aesop safe 50 (rule_sets := [Measurable])]
protected theorem Measurable.comp' {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    Measurable (fun x => g (f x)) := Measurable.comp hg hf

@[simp, fun_prop, measurability]
theorem measurable_const {_ : MeasurableSpace α} {_ : MeasurableSpace β} {a : α} :
    Measurable fun _ : β => a := fun s _ => .const (a ∈ s)

theorem Measurable.le {α} {m m0 : MeasurableSpace α} {_ : MeasurableSpace β} (hm : m ≤ m0)
    {f : α → β} (hf : Measurable[m] f) : Measurable[m0] f := fun _ hs => hm _ (hf hs)

end MeasurableFunctions

/-- A typeclass mixin for `MeasurableSpace`s such that all sets are measurable. -/
class DiscreteMeasurableSpace (α : Type*) [MeasurableSpace α] : Prop where
  /-- Do not use this. Use `MeasurableSet.of_discrete` instead. -/
  forall_measurableSet : ∀ s : Set α, MeasurableSet s

instance : @DiscreteMeasurableSpace α ⊤ :=
  @DiscreteMeasurableSpace.mk _ (_) fun _ ↦ MeasurableSpace.measurableSet_top

-- See note [lower instance priority]
instance (priority := 100) MeasurableSingletonClass.toDiscreteMeasurableSpace [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] : DiscreteMeasurableSpace α where
  forall_measurableSet _ := (Set.to_countable _).measurableSet

section DiscreteMeasurableSpace
variable [MeasurableSpace α] [MeasurableSpace β] [DiscreteMeasurableSpace α] {s : Set α} {f : α → β}

@[measurability] lemma MeasurableSet.of_discrete : MeasurableSet s :=
  DiscreteMeasurableSpace.forall_measurableSet _

@[measurability, fun_prop] lemma Measurable.of_discrete : Measurable f := fun _ _ ↦ .of_discrete

/-- Warning: Creates a typeclass loop with `MeasurableSingletonClass.toDiscreteMeasurableSpace`.
To be monitored. -/
-- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableSingletonClass :
    MeasurableSingletonClass α where
  measurableSet_singleton _ := .of_discrete

end DiscreteMeasurableSpace
