import Mathlib.Data.List.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.List
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.WLOG
import Mathlib.Order.WithBot

/-- The exchange property of greedoid. -/
def exchangeProperty {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  {s₁ : Finset α} → s₁ ∈ Sys →
  {s₂ : Finset α} → s₂ ∈ Sys →
  s₂.card < s₁.card →
  ∃ x ∈ s₁ \ s₂, insert x s₂ ∈ Sys

instance {α : Type _} [DecidableEq α] : @DecidablePred (Finset (Finset α)) exchangeProperty :=
  fun Sys =>
    if h : ∃ s₁ ∈ Sys, ∃ s₂ ∈ Sys, s₂.card < s₁.card ∧ ∀ x ∈ s₁ \ s₂, insert x s₂ ∉ Sys
    then isFalse (fun h' => by
      let ⟨s₁, hs₁, s₂, hs₂, hs₃, hs₄⟩ := h
      have ⟨_, ha₁, ha₂⟩ := h' hs₁ hs₂ hs₃
      exact hs₄ _ ha₁ ha₂)
    else isTrue (by
      simp at h
      intro _ hs₁ _ hs₂ hs
      have ⟨a, ha⟩ := h _ hs₁ _ hs₂ hs
      exists a; simp only [Finset.mem_sdiff, ha, not_false_eq_true, and_self])

/-- The accessible property of greedoid -/
def accessibleProperty {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) : Prop :=
  {s : Finset α} → s ∈ Sys → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys

theorem induction_on_accessible {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} (hSys : accessibleProperty Sys)
  {s : Finset α} (hs₀ : s ∈ Sys)
  {p : Finset α → Prop}
  (empty : p ∅)
  (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → s ∈ Sys → Insert.insert a s ∈ Sys → p s →
    p (Insert.insert a s)) :
    p s := by
  by_cases h : s = ∅ <;> try exact h ▸ empty
  have ⟨x, hx₁, hx₂⟩ := hSys hs₀ h
  have h' := Finset.sdiff_insert_insert_of_mem_of_not_mem hx₁ (Finset.not_mem_empty x)
  simp only [insert_emptyc_eq, Finset.mem_sdiff, Finset.mem_singleton, Finset.sdiff_empty] at h'
  have : p (Insert.insert x (s \ {x})) := insert (by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, and_false] : x ∉ s \ {x}) hx₂ (by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, h', hs₀])
    (induction_on_accessible hSys hx₂ empty insert)
  exact h' ▸ this
termination_by induction_on_accessible => s.card
decreasing_by
  simp_wf
  rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hx₁), Finset.card_singleton]
  simp only [Nat.sub_lt (Finset.card_pos.mpr ⟨x, hx₁⟩)]

theorem construction_of_accessible {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} (hSys : ∅ ∈ Sys ∧ accessibleProperty Sys)
  {s : Finset α} (hs₀ : s ∈ Sys) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s ∧ ∀ l' ∈ l.tails, l'.toFinset ∈ Sys := by
  apply induction_on_accessible hSys.2 hs₀
  . exists []; simp [hSys.1]
  . simp only [List.mem_tails, forall_exists_index, and_imp]
    intro a s ha _ hs l hl₁ hl₂ hl₃
    exists a :: l
    simp only [List.nodup_cons, hl₁, and_true, List.toFinset_cons, hl₂, true_and]
    have : a ∉ l := by simp only [← hl₂, List.mem_toFinset] at ha ; exact ha
    simp only [this, true_and]
    intro l' hl'
    rw [List.suffix_cons_iff] at hl'
    apply hl'.elim <;> intro hl'
    . simp only [hl', List.toFinset_cons, hl₂, hs]
    . exact hl₃ _ hl'

structure Greedoid (α : Type _) [DecidableEq α] [Fintype α] where
  feasibleSet : Finset (Finset α)
  containsEmpty : ∅ ∈ feasibleSet
  accessibleProperty : accessibleProperty feasibleSet
  exchangeProperty : exchangeProperty feasibleSet

section Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α]

/-- Definition of `Finset` in `Greedoid`.
    This is often called 'feasible'. -/
protected def Greedoid.mem (s : Finset α) (G : Greedoid α) := s ∈ G.feasibleSet

instance {α : Type _} [DecidableEq α] [Fintype α] :
    Membership (Finset α) (Greedoid α) :=
  ⟨Greedoid.mem⟩

instance {α : Type _} [DecidableEq α] [Fintype α] {G : Greedoid α} :
    DecidablePred (fun s => s ∈ G) := fun s =>
  if h : s ∈ G.feasibleSet
  then isTrue h
  else isFalse fun h' => h h'

end Greedoid

namespace Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α] {G : Greedoid α}

open Nat List Finset

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
  G₁.feasibleSet = G₂.feasibleSet → G₁ = G₂
  | ⟨Sys₁, _, _, _⟩, ⟨Sys₂, _, _, _⟩, h => by cases h; rfl

theorem feasibleSet_injective :
    Function.Injective (feasibleSet : Greedoid α → Finset (Finset α)) :=
  fun _ _ => eq_of_veq

@[simp]
theorem feasibleSet_inj {G₁ G₂ : Greedoid α} :
    G₁.feasibleSet = G₂.feasibleSet ↔ G₁ = G₂ :=
  feasibleSet_injective.eq_iff

instance : DecidableEq (Greedoid α) := fun G₁ G₂ =>
  if h : G₁.feasibleSet = G₂.feasibleSet
  then isTrue (eq_of_veq h)
  else isFalse (fun h' => h (h' ▸ rfl))

instance : Fintype (Greedoid α) where
  elems := ((@univ (Finset (Finset α)) _).filter fun Sys =>
    ∅ ∈ Sys ∧
    ({s : Finset α} → s ∈ Sys → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys) ∧
    _root_.exchangeProperty Sys).attach.map ⟨fun Sys => ⟨Sys.val, by
      let ⟨val, prop⟩ := Sys; simp only; simp at prop; exact prop.1, fun h₁ h₂ => by
      let ⟨val, prop⟩ := Sys; simp only; simp at prop h₁; exact prop.2.1 h₁ h₂,
      fun {_} a {_} b c => by
      let ⟨val, prop⟩ := Sys; simp only; simp at prop a b; exact prop.2.2 a b c⟩,
    fun S₁ S₂ hS => by simp only [Greedoid.mk.injEq] at hS; exact Subtype.ext hS⟩
  complete G := by
    simp; exists G.feasibleSet; simp only [exists_prop, and_true]
    exact ⟨G.containsEmpty, G.accessibleProperty, G.exchangeProperty⟩

section Membership

@[simp]
theorem system_feasible_set_mem_mem {s : Finset α} : s ∈ G.feasibleSet ↔ s ∈ G := by rfl

theorem emptyset_mem : ∅ ∈ G := G.containsEmpty

theorem mem_accessible {s : Finset α} (hs₁ : s ∈ G.feasibleSet) (hs₂ : s ≠ ∅) :
    ∃ x ∈ s, s \ {x} ∈ G.feasibleSet :=
  G.accessibleProperty hs₁ hs₂

theorem mem_exchangeAxiom
  {s₁ : Finset α} (hs₁ : s₁ ∈ G) {s₂ : Finset α} (hs₂ : s₂ ∈ G) (hs : s₂.card < s₁.card) :
    ∃ x ∈ s₁ \ s₂, insert x s₂ ∈ G :=
  G.exchangeProperty hs₁ hs₂ hs

end Membership

-- Possible typo at IV. Lemma 1.5
/-- Normal greedoid contains no loops. -/
class Normal (G : Greedoid α) where
  /-- Loops are elements of the ground set which is not contained in any feasible set. -/
  noLoops : {a : α} → ∃ s, s ∈ G ∧ a ∈ s

/-- `Greedoid` is full if the ground set is feasible. -/
class Full (G : Greedoid α) where
  /-- Full greedoids contain its ground. -/
  full : Finset.univ ∈ G

/-- The interval property is satisfied by matroids, antimatroids, and some greedoids. -/
class IntervalProperty (G : Greedoid α) where
  /-- If there are three intervals A ⊆ B ⊆ C and
      some x which A ∪ {x} and C ∪ {x} are both intervals,
      then B ∪ {x} is also an interval. -/
  intervalProperty : {A : Finset α} → A ∈ G →
                     {B : Finset α} → B ∈ G →
                     {C : Finset α} → C ∈ G →
                     A ⊆ B → B ⊆ C → {x : α} → x ∉ C →
                     insert x A ∈ G → insert x C ∈ G → insert x B ∈ G

/-- Matroid is an interval greedoid without lower bound. -/
class IntervalPropertyWithoutLowerBound (G : Greedoid α) where
  /-- If there are two intervals A ⊆ B and
      some x ∉ B which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval. -/
  intervalPropertyWOLowerBound : {A : Finset α} → A ∈ G →
                                 {B : Finset α} → B ∈ G → A ⊆ B →
                                 {x : α} → x ∉ B →
                                 insert x B ∈ G → insert x A ∈ G

instance [IntervalPropertyWithoutLowerBound G] : IntervalProperty G where
  intervalProperty := by
    intro _ _ _ hB _ hC _ h₂ _ hx _ hCx
    exact IntervalPropertyWithoutLowerBound.intervalPropertyWOLowerBound hB hC h₂ hx hCx

/-- Antimatroid is an interval greedoid without upper bound. -/
class IntervalPropertyWithoutUpperBound (G : Greedoid α) where
  /-- If there are two intervals B ⊆ A and
      some x ∉ A which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval. -/
  intervalPropertyWOUpperBound : {A : Finset α} → A ∈ G →
                                 {B : Finset α} → B ∈ G → B ⊆ A →
                                 {x : α} → x ∉ A →
                                 insert x B ∈ G → insert x A ∈ G

instance [IntervalPropertyWithoutUpperBound G] : IntervalProperty G where
  intervalProperty := by
    intro _ hA _ hB _ _ h₁ h₂ _ hx hAx _
    exact IntervalPropertyWithoutUpperBound.intervalPropertyWOUpperBound
      hB hA h₁ (fun h => hx (h₂ h)) hAx

/-- Base of a set system is the collection of feasible sets which is maximal. -/
def base (G : Greedoid α) : Finset (Finset α) :=
  G.feasibleSet.filter fun s => {a : α} → insert a s ∈ G.feasibleSet → a ∈ s

/-- Bases of a set `a` given a greedoid `G` is
    the collection of feasible sets which is maximal in `a`. -/
def bases {α : Type _} [Fintype α] [DecidableEq α] (G : Greedoid α) (s : Finset α) :=
  G.feasibleSet.filter (fun s' => s' ⊆ s ∧ ({a : α} → a ∈ s → insert a s' ∈ G.feasibleSet → a ∈ s'))

section Bases

variable {s b : Finset α} (hb : b ∈ G.bases s)

theorem base_bases_eq : G.base = G.bases univ := by ext s; simp [bases, base]

theorem basis_mem_feasible : b ∈ G := by simp only [bases, Finset.mem_filter] at hb; exact hb.1

theorem basis_subset : b ⊆ s := by simp only [bases, Finset.mem_filter] at hb; exact hb.2.1

theorem basis_maximal {a : α} (ha₁ : a ∈ s) (ha₂ : insert a b ∈ G) :
    a ∈ b := by
  simp only [bases, Finset.mem_filter] at hb; exact hb.2.2 ha₁ ha₂

theorem exists_basis_containing_feasible_set {s' : Finset α} (hs'₁ : s' ∈ G) (hs'₂ : s' ⊆ s) :
    ∃ b ∈ G.bases s, s' ⊆ b := by
  by_cases h : ∀ x ∈ s, insert x s' ∈ G → x ∈ s'
  . exists s'
    simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter, Finset.Subset.refl,
      hs'₁, hs'₂, and_true, true_and]
    exact fun {_} => h _
  . simp only [not_forall, exists_prop, exists_and_left] at h
    have ⟨x, hx₁, hx₂, _⟩ := h
    have ⟨b, hb₁, hb₂⟩ := exists_basis_containing_feasible_set hx₂ (by
      intro y h
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at h
      exact h.elim (fun h => h ▸ hx₁) (fun h => hs'₂ h))
    exists b
    apply And.intro hb₁
    intro y hy
    exact hb₂ (mem_insert.mpr (Or.inr hy))
termination_by exists_basis_containing_feasible_set => s.card - s'.card
decreasing_by
  simp_wf
  have hx₃ := ‹x ∉ s'›
  exact Nat.sub_lt_sub_left
    (card_lt_card ((ssubset_iff_of_subset hs'₂).mpr ⟨x, hx₁, hx₃⟩))
    (by simp [hx₃])

theorem bases_nonempty :
    Nonempty (G.bases s) := by
  simp only [nonempty_subtype]
  have ⟨b, _⟩ :=
    exists_basis_containing_feasible_set G.containsEmpty (empty_subset s)
  exists b; tauto

theorem bases_card_eq
  {b₁ : Finset α} (hb₁ : b₁ ∈ G.bases s)
  {b₂ : Finset α} (hb₂ : b₂ ∈ G.bases s) :
    b₁.card = b₂.card := by
  by_contra' h'
  apply (lt_or_gt_of_ne h').elim <;> intro h' <;> simp only [bases, Finset.mem_filter] at hb₁ hb₂
  . let ⟨x, hx₁, hx₂⟩ := G.exchangeProperty hb₂.1 hb₁.1 h'
    simp only [mem_sdiff] at hx₁
    exact hx₁.2 (hb₁.2.2 (hb₂.2.1 hx₁.1) hx₂)
  . let ⟨x, hx₁, hx₂⟩ := G.exchangeProperty hb₁.1 hb₂.1 h'
    simp only [mem_sdiff] at hx₁
    exact hx₁.2 (hb₂.2.2 (hb₁.2.1 hx₁.1) hx₂)

theorem bases_empty (h : ∅ ∈ G.bases s) :
    G.bases s = {∅} := by
  ext t; constructor <;> intro h₁ <;> simp_all
  exact card_eq_zero.mp (bases_card_eq h h₁).symm

@[simp]
theorem bases_of_empty : G.bases ∅ = {∅} := by
  ext t; constructor <;> intro h
  . rw [Finset.mem_singleton]
    simp only [bases, not_mem_empty, system_feasible_set_mem_mem, IsEmpty.forall_iff,
      implies_true, and_true, Finset.mem_filter] at h
    exact subset_empty.mp h.2
  . rw [Finset.mem_singleton] at h
    rw [h]
    simp only [bases, not_mem_empty, system_feasible_set_mem_mem, IsEmpty.forall_iff,
      implies_true, and_true, Finset.mem_filter, Finset.Subset.refl]
    exact G.containsEmpty

@[simp]
theorem bases_empty_iff :
    ∅ ∈ G.bases s ↔ G.bases s = {∅} :=
  ⟨bases_empty, by simp_all⟩

theorem bases_empty_card (h : ∅ ∈ G.bases s) :
    (G.bases s).card = 1 :=
  bases_empty_iff.mp h ▸ card_singleton _

theorem bases_of_singleton {a : α} (hb : b ∈ G.bases {a}) :
    b = ∅ ∨ b = {a} :=
  subset_singleton_iff.mp (basis_subset hb)

theorem bases_singleton_of_feasible {a : α} (ha : {a} ∈ G) (hb : b ∈ G.bases {a}) :
    b = {a} := by
  apply (bases_of_singleton hb).elim _ (fun h => h)
  intro h
  rw [h] at hb; rw [h]
  simp [bases] at hb
  exfalso
  exact hb.2 ha

theorem basis_def {s b : Finset α} :
    b ∈ G.bases s ↔ (b ∈ G ∧ b ⊆ s ∧ (∀ a ∈ s, insert a b ∈ G → a ∈ b)) := by
  constructor <;> intro h <;>
    simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter] at * <;> exact h

theorem basis_of_full_unique [Full G] : ∃! b, b ∈ G.base := by
  exists univ
  simp only; constructor
  . simp only [base, system_feasible_set_mem_mem, Finset.mem_filter, mem_univ,
      insert_eq_of_mem, implies_true, and_true]
    exact Full.full
  . intro s hs
    apply eq_univ_of_card
    apply @bases_card_eq _ _ _ G univ <;> rw [← base_bases_eq]
    . exact hs
    . simp only [base, system_feasible_set_mem_mem, Finset.mem_filter, mem_univ,
        insert_eq_of_mem, implies_true, and_true]
      exact Full.full

theorem bases_of_full_card_eq_one [Full G] : G.base.card = 1 := by
  let ⟨_, _⟩ := (Finset.singleton_iff_unique_mem (G.base)).mpr basis_of_full_unique
  simp_all only [card_singleton]

theorem basis_max_card_of_feasible {s' : Finset α} (hs'₁ : s' ∈ G) (hs'₂ : s' ⊆ s) :
    s'.card ≤ b.card :=
  have ⟨_, h₁, h₂⟩ := exists_basis_containing_feasible_set hs'₁ hs'₂
  bases_card_eq hb h₁ ▸ card_le_of_subset h₂

theorem mem_bases_self_iff : s ∈ G ↔ s ∈ G.bases s := by
  apply Iff.intro _ (fun h => basis_mem_feasible h)
  intro h
  simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter, Finset.Subset.refl, true_and, h]
  intro _ h _; exact h

theorem bases_of_card_eq (h : b.card = s.card) : b = s := by
  rw [basis_def] at hb
  rw [← subset_iff_eq_of_card_le (h ▸ (le_refl _))]
  exact hb.2.1

@[simp]
theorem bases_of_feasible_eq_singleton (hs : s ∈ G) : G.bases s = {s} := by
  ext t; constructor <;> intro h
  . rw [Finset.mem_singleton]
    rw [mem_bases_self_iff] at hs
    exact eq_of_subset_of_card_le (basis_subset h) (by simp only [bases_card_eq h hs, le_refl])
  . rw [Finset.mem_singleton] at h
    rw [mem_bases_self_iff] at hs
    exact h ▸ hs

theorem basis_card_le_of_subset_bases
  {s₁ b₁ : Finset α} (h₁ : b₁ ∈ G.bases s₁)
  {s₂ b₂ : Finset α} (h₂ : b₂ ∈ G.bases s₂)
  (h₃ : s₁ ⊆ s₂) :
    b₁.card ≤ b₂.card := by
  simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter] at h₁ h₂
  by_contra' h'
  have ⟨x, hx₁, hx₂⟩ := G.exchangeProperty h₁.1 h₂.1 h'
  rw [mem_sdiff] at hx₁
  exact hx₁.2 (h₂.2.2 (subset_trans h₁.2.1 h₃ hx₁.1) hx₂)

theorem basis_of_basis_card_eq_of_subset
  {b' : Finset α} (hb'₁ : b'.card = b.card) (hb'₂ : b' ⊆ s) (hb'₃ : b' ∈ G) :
    b' ∈ G.bases s := by
  simp only [basis_def, hb'₃, hb'₂, true_and]
  intro a ha₁ ha₂
  by_contra' h'
  have h := basis_max_card_of_feasible hb ha₂ (by
    intro x hx
    simp only [mem_insert] at hx
    apply hx.elim _ (fun h => hb'₂ h)
    intro h; rw [h]; exact ha₁)
  simp only [h', card_insert_of_not_mem, hb'₁, add_le_iff_nonpos_right] at h

theorem exists_subset_basis_of_subset_bases
  {s₁ b₁ : Finset α} (h₁ : b₁ ∈ G.bases s₁)
  {s₂ : Finset α} (h₂ : s₁ ⊆ s₂) :
    ∃ b₂ ∈ G.bases s₂, b₁ ⊆ b₂ := by
  by_cases h : b₁ ∈ G.bases s₂
  . exists b₁
  . have ⟨b, hb⟩ : Nonempty (G.bases s₂) := bases_nonempty
    have h₃: b₁.card < b.card := by
      have h₃ := subset_trans (basis_subset h₁) h₂
      have h₄ := card_le_of_subset h₃
      by_contra' h'
      apply h; clear h
      have h₅ := basis_card_le_of_subset_bases h₁ hb h₂
      exact basis_of_basis_card_eq_of_subset hb (Nat.le_antisymm h₅ h') h₃ (basis_mem_feasible h₁)
    have ⟨x, hx₁, hx₂⟩ := G.exchangeProperty (basis_mem_feasible hb) (basis_mem_feasible h₁) h₃
    rw [system_feasible_set_mem_mem] at hx₂
    have h₄ : x ∈ s₂ ∧ x ∉ s₁ := by
      rw [mem_sdiff] at hx₁
      constructor
      . apply basis_subset hb
        exact hx₁.1
      . intro h'
        exact hx₁.2 (basis_maximal h₁ h' hx₂)
    have h₅ : insert x b₁ ⊆ s₂ := insert_subset h₄.1 (subset_trans (basis_subset h₁) h₂)
    have ⟨b₂, hb₂⟩ := exists_subset_basis_of_subset_bases (mem_bases_self_iff.mp hx₂) h₅
    exists b₂
    simp only [hb₂, true_and]
    exact subset_trans (subset_insert x b₁) hb₂.2
termination_by exists_subset_basis_of_subset_bases => s₂.card - b₁.card
decreasing_by
  simp_wf
  simp_all only [mem_sdiff, system_feasible_set_mem_mem, card_insert_of_not_mem, h₄]
  rw [← Nat.sub_sub]
  apply sub_lt _ (by decide)
  rw [tsub_pos_iff_lt]
  exact lt_of_lt_of_le h₃ (card_le_of_subset (basis_subset hb))

end Bases

/-- A cardinality of largest feasible subset of `s` in `G`. -/
def rank (G : Greedoid α) (s : Finset α) :=
  ((G.feasibleSet.filter (fun s' => s' ⊆ s)).image (fun t => t.card)).max.unbot (by
    intro h
    simp [Finset.max_eq_bot, filter_eq_empty_iff] at h
    exact h _ G.containsEmpty (empty_subset _))

-- TODO: move to somewhere else like `Mathlib.Order.WithBot`
theorem unbot_le_iff [LE α] {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    WithBot.unbot b h ≤ a ↔ b ≤ (a : WithBot α) := by
  lift b to α
  . exact h
  . simp only [WithBot.unbot_coe, WithBot.coe_le_coe]

section rank

variable {s t : Finset α} {x y : α}

open Nat List Finset Greedoid

theorem rank_eq_bases_card
  {b : Finset α} (hb : b ∈ G.bases s) :
    G.rank s = b.card := by
  apply Eq.symm (Nat.le_antisymm _ _)
  . simp only [rank, WithBot.le_unbot_iff, Finset.le_max_of_eq]
    apply Finset.le_max
    simp only [system_feasible_set_mem_mem, mem_image, Finset.mem_filter]
    exists b
    simp only [basis_mem_feasible hb, basis_subset hb]
  . simp [rank, unbot_le_iff]
    apply Finset.max_le
    rintro n hn
    simp at *
    let ⟨_, hs'⟩ := hn
    exact hs'.2 ▸ basis_max_card_of_feasible hb hs'.1.1 hs'.1.2

@[simp]
theorem rank_of_empty : G.rank ∅ = 0 := by
  simp only [rank_eq_bases_card (mem_bases_self_iff.mp G.containsEmpty), card_empty]

theorem rank_of_singleton_le_one {a : α} : G.rank {a} ≤ 1 := by
  have ⟨_, h⟩ : Nonempty (G.bases {a}) := G.bases_nonempty
  rw [rank_eq_bases_card h]
  apply (bases_of_singleton h).elim <;> intro h <;> simp only [h, card_empty, card_singleton]

@[simp]
theorem rank_of_singleton_of_feasible {a : α} (ha : {a} ∈ G) : G.rank {a} = 1 := by
  apply (le_iff_lt_or_eq.mp (rank_of_singleton_le_one : G.rank {a} ≤ 1)).elim _ (fun h => h)
  intro h
  exfalso
  have ⟨_, h'⟩ : Nonempty (G.bases {a}) := G.bases_nonempty
  rw [rank_eq_bases_card h'] at h
  simp only [lt_one_iff, card_eq_zero] at h
  simp only [h, bases_empty_iff] at h'
  have := bases_singleton_of_feasible ha
    (by simp only [h', Finset.mem_singleton] : ∅ ∈ G.bases {a})
  have : a ∈ (∅ : Finset α) := by simp only [this, Finset.mem_singleton]
  contradiction

@[simp]
theorem rank_of_singleton_of_infeasible {a : α} (ha : {a} ∉ G) : G.rank {a} = 0 := by
  apply (le_iff_lt_or_eq.mp (rank_of_singleton_le_one : G.rank {a} ≤ 1)).elim
    (fun h => lt_one_iff.mp h)
  intro h
  simp only [h, one_ne_zero]
  apply ha
  have ⟨_, h'⟩ : Nonempty (G.bases {a}) := G.bases_nonempty
  rw [rank_eq_bases_card h'] at h
  exact basis_mem_feasible (eq_of_subset_of_card_le (basis_subset h') (by simp [h]) ▸ h')

theorem rank_le_card : G.rank s ≤ s.card := by
  simp only [rank, system_feasible_set_mem_mem, WithBot.unbot_le_iff]
  apply Finset.max_le
  simp only [system_feasible_set_mem_mem, mem_image, Finset.mem_filter, WithBot.coe_le_coe,
    forall_exists_index, and_imp]
  intro _ _ _ h h'
  exact h' ▸ card_le_of_subset h

theorem rank_le_of_subset (hs : s ⊆ t) : G.rank s ≤ G.rank t := by
  simp only [rank, system_feasible_set_mem_mem, WithBot.le_unbot_iff, WithBot.coe_unbot]
  apply Finset.max_le
  simp only [system_feasible_set_mem_mem, mem_image, Finset.mem_filter, forall_exists_index,
    and_imp]
  intro _ x hx₁ hx₂ h
  apply Finset.le_max
  simp only [system_feasible_set_mem_mem, mem_image, Finset.mem_filter]
  exists x
  simp only [hx₁, h, subset_trans hx₂ hs]

@[simp]
theorem rank_of_feasible (hs : s ∈ G) : G.rank s = s.card :=
  @induction_on_accessible α _ _ G.accessibleProperty _ hs (fun x => G.rank x = x.card)
    rank_of_empty (by
      simp only [system_feasible_set_mem_mem]
      intro _ _ h₁ _ h₂ _
      rw [card_insert_of_not_mem h₁]
      simp only [h₁, rank_eq_bases_card (mem_bases_self_iff.mp h₂), card_insert_of_not_mem])

theorem rank_of_infeasible (hs : s ∉ G) : G.rank s < s.card := by
  apply lt_of_le_of_ne rank_le_card
  intro h
  apply hs
  have ⟨_, hb⟩ : Nonempty (G.bases s) := G.bases_nonempty
  exact mem_bases_self_iff.mpr (bases_of_card_eq hb (rank_eq_bases_card hb ▸ h) ▸ hb)

@[simp]
theorem rank_eq_card_iff_feasible : G.rank s = s.card ↔ s ∈ G := by
  apply Iff.intro _ (fun h => rank_of_feasible h)
  intro h
  have := mt (@rank_of_infeasible _ _ _ G s)
  simp only [not_lt, not_not] at this
  apply this
  simp only [h, le_refl]

theorem local_submodularity
  (h₁ : G.rank s = G.rank (insert x s))
  (h₂ : G.rank s = G.rank (insert y s)) :
    G.rank (insert x (insert y s)) = G.rank s := by
  have h : G.rank s ≤ G.rank (insert x (insert y s)) :=
    rank_le_of_subset (subset_trans (subset_insert y _) (subset_insert _ _))
  have h := le_iff_lt_or_eq.mp h
  by_contra' h'
  simp only [mem_insert, h'.symm, or_false] at h; clear h'
  have ⟨b₁, hb₁₁⟩ : Nonempty (G.bases s) := G.bases_nonempty
  have hb₁₂ := rank_eq_bases_card hb₁₁
  have hb₁₃ := basis_mem_feasible hb₁₁
  have ⟨b₂, hb₂₁⟩ : Nonempty (G.bases (insert x (insert y s))) := G.bases_nonempty
  have hb₂₂ := rank_eq_bases_card hb₂₁
  have hb₂₃ := basis_mem_feasible hb₂₁
  rw [hb₁₂, hb₂₂] at h
  have ⟨a, ha₁, ha₂⟩ := G.exchangeProperty hb₂₃ hb₁₃ h
  rw [system_feasible_set_mem_mem] at ha₂
  rw [mem_sdiff] at ha₁
  by_cases h₃ : a ∈ s
  . exact ha₁.2 (basis_maximal hb₁₁ h₃ ha₂)
  . have h₄ : a = x ∨ a = y := by
      have : a ∈ insert x (insert y s) := basis_subset hb₂₁ ha₁.1
      simp only [mem_insert, h₃, or_false] at this
      exact this
    apply h₄.elim <;> intro h₄ <;> rw [h₄] at ha₁ ha₂
    . have h₅ : (insert x b₁).card ≤ G.rank (insert x s) := by
        rw [← rank_of_feasible ha₂]
        apply rank_le_of_subset
        intro e; simp only [mem_insert]; intro he
        exact he.elim (fun h => Or.inl h) (fun h => Or.inr ((basis_subset hb₁₁) h))
      have h₆ : G.rank s < (insert x b₁).card := by
        simp only [hb₁₂, ha₁, card_insert_of_not_mem, lt_add_iff_pos_right]
      have h₇ := lt_of_lt_of_le h₆ h₅
      simp only [h₁, lt_self_iff_false] at h₇
    . have h₅ : (insert y b₁).card ≤ G.rank (insert y s) := by
        rw [← rank_of_feasible ha₂]
        apply rank_le_of_subset
        intro e; simp only [mem_insert]; intro he
        exact he.elim (fun h => Or.inl h) (fun h => Or.inr ((basis_subset hb₁₁) h))
      have h₆ : G.rank s < (insert y b₁).card := by
        simp only [hb₁₂, ha₁, card_insert_of_not_mem, lt_add_iff_pos_right]
      have h₇ := lt_of_lt_of_le h₆ h₅
      simp only [h₂, lt_self_iff_false] at h₇

theorem stronger_local_submodularity_left
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank (s ∪ t) = G.rank s := by
  by_contra' h'
  have ⟨_, hb₁₁⟩ : Nonempty (G.bases (s ∪ t)) := G.bases_nonempty
  have ⟨_, hb₂₁⟩ : Nonempty (G.bases s) := G.bases_nonempty
  have hb₂₂ := rank_eq_bases_card hb₂₁
  have ⟨b₃, hb₃₁⟩ : Nonempty (G.bases (s ∩ t)) := G.bases_nonempty
  have hb₃₂ := rank_eq_bases_card hb₃₁
  have h' := lt_of_le_of_ne (G.rank_le_of_subset (subset_union_left s t)) h'.symm
  rw [rank_eq_bases_card hb₁₁] at h'
  have ⟨x, hx₁, hx₂⟩ := G.exchangeProperty
    (basis_mem_feasible hb₁₁) (basis_mem_feasible hb₃₁) (hb₃₂ ▸ h₁ ▸ h')
  rw [system_feasible_set_mem_mem] at hx₂
  rw [mem_sdiff] at hx₁
  apply (Finset.mem_union.mp (basis_subset hb₁₁ hx₁.1)).elim <;> intro h₃
  . have h₅ : G.rank (insert x b₃) ≤ G.rank s := by
      apply rank_le_of_subset
      intro _ ha
      exact (mem_insert.mp ha).elim
        (fun h => h ▸ h₃)
        (fun h => inter_subset_left s t (basis_subset hb₃₁ h))
    simp_all only
      [rank_of_feasible, card_insert_of_not_mem, lt_add_iff_pos_right, add_le_iff_nonpos_right]
  . have h₅ : G.rank (insert x b₃) ≤ G.rank t := by
      apply rank_le_of_subset
      intro _ ha
      exact (mem_insert.mp ha).elim
        (fun h => h ▸ h₃)
        (fun h => inter_subset_right s t (basis_subset hb₃₁ h))
    simp_all only
      [rank_of_feasible, card_insert_of_not_mem, lt_add_iff_pos_right, add_le_iff_nonpos_right]

theorem stronger_local_submodularity_right
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank (s ∪ t) = G.rank t := by
  simp only [h₂, ← h₁, stronger_local_submodularity_left h₁ h₂]

theorem ssubset_of_feasible_rank (hs : s ∈ G) (h : t ⊂ s) : G.rank t < G.rank s := by
  apply (le_iff_lt_or_eq.mp (G.rank_le_of_subset (subset_of_ssubset h))).elim <;>
    simp only [imp_self]
  intro h'
  exfalso
  have h₁ := bases_of_feasible_eq_singleton hs
  have ⟨_, hb₁⟩ : Nonempty (G.bases s) := G.bases_nonempty
  have hb₂ := rank_eq_bases_card hb₁
  rw [h₁, Finset.mem_singleton] at hb₁
  rw [hb₂, hb₁] at h'
  have h₂ : s.card ≤ t.card := (h') ▸ rank_le_card
  rw [ssubset_def] at h
  exact absurd ((eq_of_subset_of_card_le h.1 h₂) ▸ h.2) (by simp only [Finset.Subset.refl])

/-- List of axioms for rank of greedoid. -/
def greedoidRankAxioms (r : Finset α → ℕ) :=
  (r ∅ = 0) ∧ (∀ {s}, r s ≤ s.card) ∧ (∀ {s t}, s ⊆ t → r s ≤ r t) ∧
  (∀ {s x y}, r s = r (insert x s) → r s = r (insert y s) → r s = r (insert x (insert y s)))

end rank

/-- Closure of `s` is the largest set which contains `s` and have the same rank with `s`. -/
def closure (G : Greedoid α) (s : Finset α) : Finset α :=
  univ.filter fun x => G.rank (insert x s) = G.rank s

set_option linter.unusedVariables false in
def feasibleContinuations (G : Greedoid α) (s : Finset α) (hs : s ∈ G) :=
  univ.filter fun x => x ∉ s ∧ insert x s ∈ G

theorem feasibleContinuations_eq (hs : s ∈ G):
    G.feasibleContinuations s hs = univ \ G.closure s := by
  simp only [feasibleContinuations, mem_univ, closure]
  ext x
  simp only [mem_univ, Finset.mem_filter, true_and, mem_sdiff]
  constructor <;> intro h
  . intro h'
    let ⟨h₁, h₂⟩ := h
    rw [← rank_eq_card_iff_feasible, h'] at h₂
    simp only [h₁, card_insert_of_not_mem] at h₂
    have : G.rank s ≤ s.card := rank_le_card
    simp only [h₂, add_le_iff_nonpos_right] at this
  . constructor
    . intro h'; apply h; rw [insert_eq_of_mem h']
    . have h₁ := Nat.lt_of_le_and_ne (rank_le_of_subset (subset_insert _ _)) (Ne.symm h)
      rw [← rank_eq_card_iff_feasible]
      rw [← rank_eq_card_iff_feasible] at hs
      rw [hs] at h₁
      have h₂ : G.rank (insert x s) = s.card + 1 := by
        apply Nat.le_antisymm (le_trans rank_le_card (card_insert_le x s))
        simp_arith at h₁
        exact h₁
      exact Nat.le_antisymm rank_le_card (h₂ ▸ card_insert_le _ _)

section closure

variable {s t : Finset α} {x y : α}

theorem mem_closure : x ∈ G.closure s ↔ G.rank (insert x s) = G.rank s :=
  ⟨fun h => by simp [closure] at h; exact h, fun h => by simp [closure]; exact h⟩

theorem self_subset_closure : s ⊆ G.closure s := by
  intro x hx
  simp only [mem_closure, insert_eq_of_mem hx]

theorem closure_subset_of_subset (h : s ⊆ t) : G.closure s ⊆ G.closure t := by
  intro x hx
  rw [mem_closure] at *
  apply Nat.le_antisymm _ (rank_le_of_subset _)
  . sorry
  . intro _ h
    have := sdiff_insert_insert_of_mem_of_not_mem h (not_mem_empty _)
    simp_all only [Finset.mem_singleton, mem_insert, or_true]

@[simp]
theorem rank_closure_eq_rank_self (s : Finset α) : G.rank (G.closure s) = G.rank s := by
  symm
  by_cases h : s = G.closure s
  . rw [← h]
  . have h₁ : s.card < (G.closure s).card := by
      rw [lt_iff_le_and_ne]
      constructor
      . exact card_le_of_subset self_subset_closure
      . exact fun h' => h (eq_of_subset_of_card_le self_subset_closure (by rw [h']))
    have ⟨x, hx⟩ : ∃ x, x ∈ G.closure s \ s := by
      by_contra' h'
      simp only [mem_sdiff, not_and, not_not] at h'
      simp only [← subset_antisymm self_subset_closure h', lt_self_iff_false] at h₁
    have h₂ := rank_closure_eq_rank_self (insert x s)
    simp only [mem_sdiff, mem_closure] at hx
    rw [← hx.1, ← h₂]
    apply congr_arg
    ext y; simp only [mem_closure]
    constructor <;> intro hy
    . rw [Insert.comm, hx.1] at hy
      have h₃ : G.rank s ≤ G.rank (insert y s) := rank_le_of_subset (subset_insert _ _)
      have h₄ : G.rank (insert y s) ≤ G.rank (insert x (insert y s)) :=
        rank_le_of_subset (subset_insert _ _)
      rw [hy] at h₄
      exact le_antisymm h₄ h₃
    . rw [local_submodularity hy.symm hx.1.symm, hx.1]
termination_by rank_closure_eq_rank_self => (@univ α _).card - s.card
decreasing_by
  simp_wf
  rw [mem_sdiff] at hx
  simp only [hx.2, card_insert_of_not_mem]
  rw [← Nat.sub_sub]
  exact Nat.sub_lt (tsub_pos_iff_lt.mpr (card_lt_univ_of_not_mem hx.2)) (by decide)

theorem closure_unique_largest_superset
  (ht₁ : s ⊆ t) (ht₂ : G.rank s = G.rank t) (ht₃ : ∀ x, G.rank s = G.rank (insert x t) → x ∈ t) :
    t = G.closure s := by
  apply subset_antisymm
  . intro x hx
    rw [mem_closure]
    have h₁ : G.rank s ≤ G.rank (insert x s) := rank_le_of_subset (subset_insert x s)
    have h₂ : G.rank (insert x s) ≤ G.rank t := by
      apply rank_le_of_subset
      intro _ hy
      exact (mem_insert.mp hy).elim (fun h => h ▸ hx) (fun h => ht₁ h)
    rw [← ht₂] at h₂
    exact Nat.le_antisymm h₂ h₁
  . intro x hx
    rw [mem_closure] at hx
    apply ht₃
    rw [ht₂]
    sorry

theorem feasible_iff_elem_notin_closure_minus_elem :
    s ∈ G ↔ ∀ x ∈ s, x ∉ G.closure (s \ {x}) := by
  constructor <;> intro h
  . intro x hx h'
    rw [mem_closure] at h'
    have h₁ := sdiff_insert_insert_of_mem_of_not_mem hx (not_mem_empty x)
    simp only [insert_emptyc_eq, mem_sdiff, Finset.mem_singleton, sdiff_empty] at h₁
    rw [h₁] at h'
    have h₃ : G.rank (s \ {x}) ≤ (s \ {x}).card := rank_le_card
    rw [← h', rank_of_feasible h, card_sdiff (fun y hy => by simp_all)] at h₃
    have : s.card - 1 < s.card := sub_lt (card_pos.mpr ⟨x, hx⟩) (by decide)
    rw [lt_iff_not_ge] at this
    exact this h₃
  . by_contra' h'
    have ⟨b, hb₁⟩ : Nonempty (G.bases s) := G.bases_nonempty
    have ⟨y, hy₁, hy₂⟩ : ∃ y ∈ s, y ∉ b := by
      by_contra' h'
      rw [subset_antisymm (basis_subset hb₁) h', ← mem_bases_self_iff] at hb₁
      contradiction
    apply h y hy₁
    rw [mem_closure]
    have : insert y (s \ {y}) = s := by
      ext x; constructor <;> intro h <;>
        simp only [mem_sdiff, Finset.mem_singleton, mem_insert] at *
      . exact h.elim (fun h => h ▸ hy₁) (fun h => h.1)
      . by_cases h₁ : x = y
        . simp only [h₁, true_or]
        . simp only [h, h₁]
    rw [this]
    apply Nat.le_antisymm _ (rank_le_of_subset (sdiff_subset _ _))
    rw [rank_eq_bases_card hb₁, ← rank_of_feasible (basis_mem_feasible hb₁)]
    apply rank_le_of_subset
    intro z hz
    simp only [mem_sdiff, Finset.mem_singleton]
    apply And.intro (basis_subset hb₁ hz)
    exact fun h => hy₂ (h ▸ hz)

theorem closure_eq_of_subset_adj_closure (hst : s ⊆ G.closure t) (hts : t ⊆ G.closure s) :
    G.closure s = G.closure t := by
  have h₁ : G.rank s ≤ G.rank t := by
    have := G.rank_le_of_subset hst
    rw [rank_closure_eq_rank_self] at this
    exact this
  have h₂ : G.rank t ≤ G.rank s := by
    have := G.rank_le_of_subset hts
    rw [rank_closure_eq_rank_self] at this
    exact this
  apply subset_antisymm
  . sorry
  . sorry

theorem closure_idempotent : G.closure (G.closure s) = G.closure s :=
  closure_eq_of_subset_adj_closure Subset.rfl
    (Finset.Subset.trans self_subset_closure self_subset_closure)

theorem closure_exchange_property
  (hx : x ∉ s) (hy : y ∉ s) (hs : s ∪ {x} ∈ G)
  (h : x ∈ G.closure (s ∪ {y})) :
    y ∈ G.closure (s ∪ {x}) := sorry

/-- `cospanning` is an equivalence relation in `2^E`. -/
def cospanning (G : Greedoid α) (s t : Finset α) := G.closure s = G.closure t

section cospanning

theorem cospanning_refl : ∀ s, G.cospanning s s := by simp [cospanning]

theorem cospanning_symm (h : G.cospanning s t) : G.cospanning t s := by
  simp only [cospanning] at h; simp only [cospanning, h]

theorem cospanning_comm : G.cospanning s t ↔ G.cospanning t s :=
  ⟨cospanning_symm, cospanning_symm⟩

theorem cospanning_trans {s t u : Finset α}
  (hst : G.cospanning s t) (htu : G.cospanning t u) :
    G.cospanning s u := by
  simp only [cospanning] at hst htu; simp only [cospanning, hst, htu]

theorem cospanning_eqv : Equivalence (G.cospanning) :=
  ⟨cospanning_refl, cospanning_symm, cospanning_trans⟩

theorem cospanning_rel_left_union (h : G.cospanning s t) : G.cospanning s (s ∪ t) := sorry

theorem cospanning_rel_right_union (h : G.cospanning s t) : G.cospanning (s ∪ t) t :=
  cospanning_trans (cospanning_symm (cospanning_rel_left_union h)) h

theorem cospanning_rel_between_subset_left {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.cospanning s u) :
    G.cospanning s t := sorry

theorem cospanning_rel_between_subset_right {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.cospanning s u) :
    G.cospanning t u :=
  G.cospanning_trans (cospanning_symm (cospanning_rel_between_subset_left hst htu hsu)) hsu

theorem cospanning_rel_ex
  (h₁ : G.cospanning (s ∪ {y}) (s ∪ {x, y}))
  (h₂ : ¬ G.cospanning (s ∪ {x}) (s ∪ {x, y})) :
    ∃ z ∈ s ∪ {x}, G.cospanning ((s ∪ {x}) \ {z}) (s ∪ {x}) := sorry

theorem cospanning_rel_ex'
  (h₁ : G.cospanning (s ∪ {y}) (s ∪ {x, y}))
  (h₂ : ¬ G.cospanning (s ∪ {x}) (s ∪ {x, y})) :
    ∃ z ∈ s ∪ {x}, G.cospanning (s ∪ {x}) ((s ∪ {x}) \ {z}) :=
  let ⟨z, hz⟩ := cospanning_rel_ex h₁ h₂
  ⟨z, hz.1, G.cospanning_symm hz.2⟩

end cospanning

end closure

end Greedoid

#lint
