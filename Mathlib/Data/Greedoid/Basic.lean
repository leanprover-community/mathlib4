import Mathlib.Data.List.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.List
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.WLOG
import Mathlib.Order.WithBot

/-- The exchange property of greedoid· -/
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

theorem exchangeProperty_exists_superset_of_card_le {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} (hSys : exchangeProperty Sys)
  {s₁ : Finset α} (hs₁ : s₁ ∈ Sys)
  {s₂ : Finset α} (hs₂ : s₂ ∈ Sys)
  (hs : s₂.card ≤ s₁.card)
  {n : ℕ} (hn₁ : n ≤ s₁.card) (hn₂ : s₂.card ≤ n) :
    ∃ s ∈ Sys, s₂ ⊆ s ∧ s ⊆ s₁ ∪ s₂ ∧ s.card = n := by
  by_cases h : s₂.card = n
  · exists s₂
    simp_all only [Finset.Subset.refl, Finset.subset_union_right, and_self, hn₁, hs₂]
  · have ⟨x, hx₁, hx₂⟩ := hSys hs₁ hs₂ (Nat.lt_iff_le_and_ne.mpr ⟨hs, by
      intro h₁
      apply h
      apply le_antisymm hn₂
      exact h₁ ▸ hn₁⟩)
    have h₁ : (insert x s₂).card = s₂.card + 1 :=
      Finset.card_insert_of_not_mem (Finset.mem_sdiff.mp hx₁).2
    have ⟨b, hb⟩ := exchangeProperty_exists_superset_of_card_le hSys hs₁ hx₂ (by
      rw [h₁, Nat.succ_le, Nat.lt_iff_le_and_ne]
      apply And.intro hs
      intro h₂
      apply h
      apply le_antisymm hn₂
      exact h₂ ▸ hn₁) hn₁ (by
      rw [h₁, Nat.succ_le]
      exact Nat.lt_of_lt_of_le (Nat.lt_iff_le_and_ne.mpr ⟨hn₂, h⟩) le_rfl)
    exists b
    exact ⟨hb.1, subset_trans (Finset.subset_insert _ _) hb.2.1, by
      intro _ h
      have h := hb.2.2.1 h
      simp only [Finset.union_insert, Finset.mem_union, Finset.mem_insert] at h
      rw [Finset.mem_union]
      apply h.elim _ id
      intro h
      simp only [← h, Finset.mem_sdiff] at hx₁
      simp only [hx₁, or_false], hb.2.2.2⟩
termination_by s₁.card - s₂.card
decreasing_by
  simp_wf
  rw [h₁, Nat.sub_add_eq]
  apply Nat.sub_lt _ (by decide)
  rw [tsub_pos_iff_lt, Nat.lt_iff_le_and_ne]
  apply And.intro hs
  intro h₂
  apply h
  exact le_antisymm hn₂ (h₂ ▸ hn₁)

-- TODO: Fix name.
theorem exchangeProperty_exists_feasible_superset_add_element_feasible {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} (hSys : exchangeProperty Sys)
  {s₁ : Finset α} (hs₁ : s₁ ∈ Sys)
  {s₂ : Finset α} (hs₂ : s₂ ∈ Sys)
  (hs : s₂ ⊆ s₁)
  {a : α} (ha₁ : a ∈ s₁) (ha₂ : a ∉ s₂) :
    ∃ s ∈ Sys, s₂ ⊆ s ∧ s ⊆ s₁ ∧ a ∉ s ∧ Insert.insert a s ∈ Sys := by
  have h₁ : s₂.card < s₁.card := by
    apply Finset.card_lt_card
    simp only [Finset.ssubset_def, hs, true_and]
    intro h
    exact ha₂ (h ha₁)
  by_cases h : Insert.insert a s₂ ∈ Sys
  · exists s₂
  · let ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := exchangeProperty_exists_superset_of_card_le hSys hs₁ hs₂
      (Finset.card_le_card hs) h₁ (Nat.le_succ _)
    have ht₅ : a ∉ t := by
      intro h'
      apply h; clear h
      have h : insert a s₂ = t := by
        apply Finset.eq_of_subset_of_card_le
        · intro _ h
          rw [Finset.mem_insert] at h
          exact h.elim (fun h => h ▸ h') (fun h => ht₂ h)
        · rw [ht₄, Finset.card_insert_of_not_mem ha₂]
      exact h ▸ ht₁
    let ⟨s', hs'₁, hs'₂, hs'₃, hs'₄, hs'₅⟩ :=
      exchangeProperty_exists_feasible_superset_add_element_feasible hSys hs₁ ht₁
        (Finset.union_eq_left.mpr hs ▸ ht₃) ha₁ ht₅
    exists s'
    exact ⟨hs'₁, subset_trans ht₂ hs'₂, hs'₃, hs'₄, hs'₅⟩
termination_by s₁.card - s₂.card
decreasing_by
  simp_wf
  rw [ht₄]
  exact Nat.sub_succ_lt_self _ _ h₁

/-- The accessible property of greedoid -/
def accessibleProperty {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) : Prop :=
  {s : Finset α} → s ∈ Sys → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys

class Accessible {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) : Prop where
  accessible : {s : Finset α} → s ∈ Sys → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys

theorem accessible_accessibleProperty {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} [Accessible Sys] :
    accessibleProperty Sys := Accessible.accessible

theorem induction_on_accessible {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} [Accessible Sys]
  {s : Finset α} (hs₀ : s ∈ Sys)
  {p : Finset α → Prop}
  (empty : p ∅)
  (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → s ∈ Sys → Insert.insert a s ∈ Sys → p s →
    p (Insert.insert a s)) :
    p s := by
  by_cases h : s = ∅ <;> try exact h ▸ empty
  have ⟨x, hx₁, hx₂⟩ := Accessible.accessible hs₀ h
  have h' := Finset.sdiff_insert_insert_of_mem_of_not_mem hx₁ (Finset.not_mem_empty x)
  simp only [insert_emptyc_eq, Finset.mem_sdiff, Finset.mem_singleton, Finset.sdiff_empty] at h'
  have : p (Insert.insert x (s \ {x})) := insert (by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, not_true_eq_false, and_false,
        not_false_eq_true] : x ∉ s \ {x}) hx₂ (by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, h', hs₀])
    (induction_on_accessible hx₂ empty insert)
  exact h' ▸ this
termination_by s.card
decreasing_by
  simp_wf
  rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hx₁), Finset.card_singleton]
  simp only [zero_lt_one, Nat.sub_lt (Finset.card_pos.mpr ⟨x, hx₁⟩)]

theorem construction_of_accessible {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} [Accessible Sys] (hSys : ∅ ∈ Sys)
  {s : Finset α} (hs₀ : s ∈ Sys) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s ∧ ∀ l', l' <:+ l → l'.toFinset ∈ Sys := by
  apply induction_on_accessible hs₀
  · exists []; simp only [List.nodup_nil, List.toFinset_nil, List.suffix_nil, forall_eq, hSys,
    and_self]
  · simp only [List.mem_tails, forall_exists_index, and_imp]
    intro a s ha _ hs l hl₁ hl₂ hl₃
    exists a :: l
    simp only [List.nodup_cons, hl₁, and_true, List.toFinset_cons, hl₂, true_and]
    have : a ∉ l := by simp only [← hl₂, List.mem_toFinset] at ha; exact ha
    simp only [this, not_false_eq_true, true_and]
    intro l' hl'
    rw [List.suffix_cons_iff] at hl'
    apply hl'.elim <;> intro hl'
    · simp only [hl', List.toFinset_cons, hl₂, hs]
    · exact hl₃ _ hl'

structure Greedoid (α : Type _) [DecidableEq α] [Fintype α] where
  feasibleSet : Finset (Finset α)
  containsEmpty : ∅ ∈ feasibleSet
  accessibleProperty : accessibleProperty feasibleSet
  exchangeProperty : exchangeProperty feasibleSet

section Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α]

/-- Definition of `Finset` in `Greedoid`.
    This is often called 'feasible'· -/
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

instance : Accessible G.feasibleSet := ⟨G.accessibleProperty⟩

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

@[simp]
theorem feasibleSet_nonempty : G.feasibleSet.Nonempty := ⟨∅, G.containsEmpty⟩

-- Possible typo at IV· Lemma 1.5
/-- Normal greedoid contains no loops· -/
class Normal (G : Greedoid α) where
  /-- Loops are elements of the ground set which is not contained in any feasible set· -/
  noLoops : {a : α} → ∃ s, s ∈ G ∧ a ∈ s

/-- `Greedoid` is full if the ground set is feasible· -/
class Full (G : Greedoid α) where
  /-- Full greedoids contain its ground· -/
  full : univ ∈ G

/-- The interval property is satisfied by matroids, antimatroids, and some greedoids· -/
class IntervalProperty (G : Greedoid α) where
  /-- If there are three intervals A ⊆ B ⊆ C and
      some x which A ∪ {x} and C ∪ {x} are both intervals,
      then B ∪ {x} is also an interval· -/
  intervalProperty : {A : Finset α} → A ∈ G →
                     {B : Finset α} → B ∈ G →
                     {C : Finset α} → C ∈ G →
                     A ⊆ B → B ⊆ C → {x : α} → x ∉ C →
                     insert x A ∈ G → insert x C ∈ G → insert x B ∈ G

/-- Matroid is an interval greedoid without lower bound· -/
class IntervalPropertyWithoutLowerBound (G : Greedoid α) where
  /-- If there are two intervals A ⊆ B and
      some x ∉ B which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval· -/
  intervalPropertyWOLowerBound : {A : Finset α} → A ∈ G →
                                 {B : Finset α} → B ∈ G → A ⊆ B →
                                 {x : α} → x ∉ B →
                                 insert x B ∈ G → insert x A ∈ G

instance [IntervalPropertyWithoutLowerBound G] : IntervalProperty G where
  intervalProperty := by
    intro _ _ _ hB _ hC _ h₂ _ hx _ hCx
    exact IntervalPropertyWithoutLowerBound.intervalPropertyWOLowerBound hB hC h₂ hx hCx

/-- Antimatroid is an interval greedoid without upper bound· -/
class IntervalPropertyWithoutUpperBound (G : Greedoid α) where
  /-- If there are two intervals B ⊆ A and
      some x ∉ A which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval· -/
  intervalPropertyWOUpperBound : {A : Finset α} → A ∈ G →
                                 {B : Finset α} → B ∈ G → B ⊆ A →
                                 {x : α} → x ∉ A →
                                 insert x B ∈ G → insert x A ∈ G

instance [IntervalPropertyWithoutUpperBound G] : IntervalProperty G where
  intervalProperty := by
    intro _ hA _ hB _ _ h₁ h₂ _ hx hAx _
    exact IntervalPropertyWithoutUpperBound.intervalPropertyWOUpperBound
      hB hA h₁ (fun h => hx (h₂ h)) hAx

/-- Base of a set system is the collection of feasible sets which is maximal· -/
def base (G : Greedoid α) : Finset (Finset α) :=
  G.feasibleSet.filter fun s => {a : α} → insert a s ∈ G.feasibleSet → a ∈ s

/-- Bases of a set `a` given a greedoid `G` is
    the collection of feasible sets which is maximal in `a`· -/
def bases {α : Type _} [Fintype α] [DecidableEq α] (G : Greedoid α) (s : Finset α) :=
  G.feasibleSet.filter (fun s' => s' ⊆ s ∧ ({a : α} → a ∈ s → insert a s' ∈ G.feasibleSet → a ∈ s'))

section Bases

variable {s b : Finset α} (hb : b ∈ G.bases s)

theorem base_bases_eq : G.base = G.bases univ := by
  ext s
  simp only [base, system_feasible_set_mem_mem, Finset.mem_filter, bases, subset_univ, mem_univ,
  forall_true_left, true_and]

theorem basis_mem_feasible : b ∈ G := by simp only [bases, Finset.mem_filter] at hb; exact hb.1

theorem basis_subset : b ⊆ s := by simp only [bases, Finset.mem_filter] at hb; exact hb.2.1

theorem basis_maximal {a : α} (ha₁ : a ∈ s) (ha₂ : insert a b ∈ G) :
    a ∈ b := by
  simp only [bases, Finset.mem_filter] at hb; exact hb.2.2 ha₁ ha₂

theorem exists_basis_containing_feasible_set {s' : Finset α} (hs'₁ : s' ∈ G) (hs'₂ : s' ⊆ s) :
    ∃ b ∈ G.bases s, s' ⊆ b := by
  by_cases h : ∀ x ∈ s, insert x s' ∈ G → x ∈ s'
  · exists s'
    simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter, Finset.Subset.refl,
      hs'₁, hs'₂, and_true, true_and]
    exact fun {_} => h _
  · simp only [not_forall, exists_prop, exists_and_left] at h
    have ⟨x, hx₁, hx₂, _⟩ := h
    have ⟨b, hb₁, hb₂⟩ := exists_basis_containing_feasible_set hx₂ (by
      intro y h
      simp only [mem_union, Finset.mem_singleton, mem_insert] at h
      exact h.elim (fun h => h ▸ hx₁) (fun h => hs'₂ h))
    exists b
    apply And.intro hb₁
    intro y hy
    exact hb₂ (mem_insert.mpr (Or.inr hy))
termination_by s.card - s'.card
decreasing_by
  simp_wf
  have hx₃ := ‹x ∉ s'›
  exact Nat.sub_lt_sub_left
    (card_lt_card ((ssubset_iff_of_subset hs'₂).mpr ⟨x, hx₁, hx₃⟩))
    (by simp only [hx₃, not_false_eq_true, card_insert_of_not_mem, lt_add_iff_pos_right,
      zero_lt_one])

theorem bases_nonempty (s : Finset α) :
    Nonempty (G.bases s) := by
  simp only [nonempty_subtype]
  have ⟨b, _⟩ :=
    exists_basis_containing_feasible_set G.containsEmpty (empty_subset s)
  exists b; tauto

theorem base_nonempty :
    Nonempty G.base :=
  G.base_bases_eq ▸ bases_nonempty _

theorem basis_card_eq
  {b₁ : Finset α} (hb₁ : b₁ ∈ G.bases s)
  {b₂ : Finset α} (hb₂ : b₂ ∈ G.bases s) :
    b₁.card = b₂.card := by
  by_contra h'
  apply (lt_or_gt_of_ne h').elim <;> intro h' <;> simp only [bases, Finset.mem_filter] at hb₁ hb₂
  · let ⟨x, hx₁, hx₂⟩ := G.exchangeProperty hb₂.1 hb₁.1 h'
    simp only [mem_sdiff] at hx₁
    exact hx₁.2 (hb₁.2.2 (hb₂.2.1 hx₁.1) hx₂)
  · let ⟨x, hx₁, hx₂⟩ := G.exchangeProperty hb₁.1 hb₂.1 h'
    simp only [mem_sdiff] at hx₁
    exact hx₁.2 (hb₂.2.2 (hb₁.2.1 hx₁.1) hx₂)

theorem base_card_eq
  {b₁ : Finset α} (hb₁ : b₁ ∈ G.base)
  {b₂ : Finset α} (hb₂ : b₂ ∈ G.base) :
    b₁.card = b₂.card :=
  basis_card_eq (G.base_bases_eq ▸ hb₁) (G.base_bases_eq ▸ hb₂)

theorem basis_card_le_base_card
  {b₁ b₂ : Finset α} (hb₁ : b₁ ∈ G.bases s) (hb₂ : b₂ ∈ G.base) :
    b₁.card ≤ b₂.card := by
  let ⟨b', hb'₁, hb'₂⟩ :=
    exists_basis_containing_feasible_set (G.basis_mem_feasible hb₁) (subset_univ b₁)
  rw [← base_bases_eq] at hb'₁
  rw [base_card_eq hb₂ hb'₁]
  exact card_le_card hb'₂

theorem mem_base_if_feasible_and_card_eq_basis_of_base
  {b : Finset α} (hb : b ∈ G.base)
  {a : Finset α} (ha₁ : a ∈ G) (ha₂ : a.card = b.card) :
    a ∈ G.base := by
  simp only [base_bases_eq, bases, subset_univ, mem_univ, system_feasible_set_mem_mem,
    forall_true_left, true_and, not_forall, exists_prop, Finset.mem_filter, ha₁]
  intro x hx
  have ⟨b', hb'₁, hb'₂⟩ := exists_basis_containing_feasible_set hx (subset_univ _)
  rw [base_bases_eq] at hb
  rw [basis_card_eq hb hb'₁] at ha₂
  by_contra h
  rw [subset_iff_eq_of_card_le] at hb'₂
  · simp only [← hb'₂, card_insert_of_not_mem h, self_eq_add_right] at ha₂
  · simp only [← ha₂, card_insert_of_not_mem h, le_add_iff_nonneg_right, _root_.zero_le]

theorem mem_base_iff_feasible_and_card_eq_basis_of_base
  {b : Finset α} (hb : b ∈ G.base) {a : Finset α} :
    a ∈ G.base ↔ (a ∈ G ∧ a.card = b.card) := by
  constructor <;> intro h
  · rw [base_bases_eq] at h hb
    simp only [basis_mem_feasible h, basis_card_eq h hb, and_self]
  · exact mem_base_if_feasible_and_card_eq_basis_of_base hb h.1 h.2

theorem bases_empty (h : ∅ ∈ G.bases s) :
    G.bases s = {∅} := by
  ext t; constructor <;> intro h₁ <;> simp_all
  exact card_eq_zero.mp (basis_card_eq h h₁).symm

@[simp]
theorem bases_of_empty : G.bases ∅ = {∅} := by
  ext t; constructor <;> intro h
  · rw [Finset.mem_singleton]
    simp only [bases, not_mem_empty, system_feasible_set_mem_mem, IsEmpty.forall_iff,
      implies_true, and_true, Finset.mem_filter] at h
    exact subset_empty.mp h.2
  · rw [Finset.mem_singleton] at h
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

theorem bases_empty_feasible_mem
  (hs₁ : G.bases s = {∅}) {t : Finset α} (ht₁ : t ∈ G) (ht₂ : t ⊆ s) :
    t = ∅ := by
  have ⟨_, hb₁, hb₂⟩ := exists_basis_containing_feasible_set ht₁ ht₂
  simp only [hs₁, Finset.mem_singleton] at hb₁
  simp only [hb₁, subset_empty] at hb₂
  exact hb₂

theorem bases_of_singleton {a : α} (hb : b ∈ G.bases {a}) :
    b = ∅ ∨ b = {a} :=
  subset_singleton_iff.mp (basis_subset hb)

theorem bases_singleton_of_feasible {a : α} (ha : {a} ∈ G) (hb : b ∈ G.bases {a}) :
    b = {a} := by
  apply (bases_of_singleton hb).elim _ id
  intro h
  rw [h] at hb; rw [h]
  simp only [bases, Finset.subset_singleton_iff, Finset.mem_singleton, system_feasible_set_mem_mem,
    forall_eq, Finset.mem_filter, true_or, insert_emptyc_eq, not_mem_empty, imp_false,
    true_and] at hb
  exfalso
  exact hb.2 ha

theorem basis_def {s b : Finset α} :
    b ∈ G.bases s ↔ (b ∈ G ∧ b ⊆ s ∧ (∀ a ∈ s, insert a b ∈ G → a ∈ b)) := by
  constructor <;> intro h <;>
    simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter] at * <;> exact h

theorem basis_of_full_unique [Full G] : ∃! b, b ∈ G.base := by
  exists univ
  simp only; constructor
  · simp only [base, system_feasible_set_mem_mem, Finset.mem_filter, mem_univ,
      insert_eq_of_mem, implies_true, and_true]
    exact Full.full
  · intro s hs
    apply eq_univ_of_card
    apply @basis_card_eq _ _ _ G univ <;> rw [← base_bases_eq]
    · exact hs
    · simp only [base, system_feasible_set_mem_mem, Finset.mem_filter, mem_univ,
        insert_eq_of_mem, implies_true, and_true]
      exact Full.full

theorem bases_of_full_card_eq_one [Full G] : G.base.card = 1 := by
  let ⟨_, _⟩ := (singleton_iff_unique_mem (G.base)).mpr basis_of_full_unique
  simp_all only [card_singleton]

theorem basis_max_card_of_feasible {s' : Finset α} (hs'₁ : s' ∈ G) (hs'₂ : s' ⊆ s) :
    s'.card ≤ b.card :=
  have ⟨_, h₁, h₂⟩ := exists_basis_containing_feasible_set hs'₁ hs'₂
  basis_card_eq hb h₁ ▸ card_le_card h₂

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
  · rw [Finset.mem_singleton]
    rw [mem_bases_self_iff] at hs
    exact eq_of_subset_of_card_le (basis_subset h) (by simp only [basis_card_eq h hs, le_refl])
  · rw [Finset.mem_singleton] at h
    rw [mem_bases_self_iff] at hs
    exact h ▸ hs

theorem basis_bases_subset_bases : G.bases b ⊆ G.bases s := by
  intro _ h
  simp only [bases_of_feasible_eq_singleton (basis_mem_feasible hb), Finset.mem_singleton] at h
  exact h ▸ hb

theorem basis_card_le_of_subset_bases
  {s₁ b₁ : Finset α} (h₁ : b₁ ∈ G.bases s₁)
  {s₂ b₂ : Finset α} (h₂ : b₂ ∈ G.bases s₂)
  (h₃ : s₁ ⊆ s₂) :
    b₁.card ≤ b₂.card := by
  simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter] at h₁ h₂
  by_contra h'
  rw [not_le] at h'
  have ⟨x, hx₁, hx₂⟩ := G.exchangeProperty h₁.1 h₂.1 h'
  rw [mem_sdiff] at hx₁
  exact hx₁.2 (h₂.2.2 (subset_trans h₁.2.1 h₃ hx₁.1) hx₂)

theorem basis_of_basis_card_eq_of_subset
  {b' : Finset α} (hb'₁ : b'.card = b.card) (hb'₂ : b' ⊆ s) (hb'₃ : b' ∈ G) :
    b' ∈ G.bases s := by
  simp only [basis_def, hb'₃, hb'₂, true_and]
  intro a ha₁ ha₂
  by_contra h'
  have h := basis_max_card_of_feasible hb ha₂ (by
    intro x hx
    simp only [mem_insert] at hx
    apply hx.elim _ (fun h => hb'₂ h)
    intro h; rw [h]; exact ha₁)
  simp only [h', not_false_eq_true, card_insert_of_not_mem, hb'₁, add_le_iff_nonpos_right,
    nonpos_iff_eq_zero] at h

theorem exists_subset_basis_of_subset_bases
  {s₁ b₁ : Finset α} (h₁ : b₁ ∈ G.bases s₁)
  {s₂ : Finset α} (h₂ : s₁ ⊆ s₂) :
    ∃ b₂ ∈ G.bases s₂, b₁ ⊆ b₂ := by
  by_cases h : b₁ ∈ G.bases s₂
  · exists b₁
  · have ⟨b, hb⟩ := G.bases_nonempty s₂
    have h₃: b₁.card < b.card := by
      have h₃ := subset_trans (basis_subset h₁) h₂
      by_contra h'
      simp only [not_lt] at h'
      apply h; clear h
      have h₅ := basis_card_le_of_subset_bases h₁ hb h₂
      exact basis_of_basis_card_eq_of_subset hb (Nat.le_antisymm h₅ h') h₃ (basis_mem_feasible h₁)
    have ⟨x, hx₁, hx₂⟩ := G.exchangeProperty (basis_mem_feasible hb) (basis_mem_feasible h₁) h₃
    rw [system_feasible_set_mem_mem] at hx₂
    have h₄ : x ∈ s₂ ∧ x ∉ s₁ := by
      rw [mem_sdiff] at hx₁
      constructor
      · apply basis_subset hb
        exact hx₁.1
      · intro h'
        exact hx₁.2 (basis_maximal h₁ h' hx₂)
    have h₅ : insert x b₁ ⊆ s₂ := insert_subset h₄.1 (subset_trans (basis_subset h₁) h₂)
    have ⟨b₂, hb₂⟩ := exists_subset_basis_of_subset_bases (mem_bases_self_iff.mp hx₂) h₅
    exists b₂
    simp only [hb₂, true_and]
    exact subset_trans (subset_insert x b₁) hb₂.2
termination_by s₂.card - b₁.card
decreasing_by
  simp_wf
  simp_all only [PSigma.forall, mem_sdiff, system_feasible_set_mem_mem,
    not_false_eq_true, card_insert_of_not_mem]
  rw [← Nat.sub_sub]
  apply sub_lt _ (by decide)
  rw [tsub_pos_iff_lt]
  exact lt_of_lt_of_le h₃ (card_le_card (basis_subset hb))

end Bases

/-- A cardinality of largest feasible subset of `s` in `G`· -/
def rank (G : Greedoid α) (s : Finset α) :=
  ((G.feasibleSet.filter (fun s' => s' ⊆ s)).image (fun t => t.card)).max' ⟨0, by
    simp only [system_feasible_set_mem_mem, mem_image, Finset.mem_filter, card_eq_zero,
      exists_eq_right, G.emptyset_mem, empty_subset, and_self]⟩

section Rank

variable {s t : Finset α} {x y : α}

open Nat List Finset Greedoid

theorem rank_eq_basis_card {b : Finset α} (hb : b ∈ G.bases s) :
    G.rank s = b.card := by
  apply Eq.symm (Nat.le_antisymm _ _)
  · simp only [rank]
    apply le_max'
    simp only [system_feasible_set_mem_mem, mem_image, Finset.mem_filter]
    exists b
    simp only [G.basis_mem_feasible hb, G.basis_subset hb, and_self]
  · simp only [rank]
    apply max'_le
    intro n hn
    simp only [mem_image, Finset.mem_filter] at hn
    let ⟨t, ht⟩ := hn
    rw [← ht.2]
    have ⟨b', hb'₁, hb'₂⟩ := G.exists_basis_containing_feasible_set ht.1.1 ht.1.2
    rw [G.basis_card_eq hb hb'₁]
    exact card_le_card hb'₂

@[simp]
theorem rank_of_basis_eq_card {b : Finset α} (hb : b ∈ G) :
    G.rank b = b.card :=
  rank_eq_basis_card (mem_bases_self_iff.mp hb)

@[simp]
theorem rank_of_empty : G.rank ∅ = 0 := by
  simp only [rank_eq_basis_card (mem_bases_self_iff.mp G.containsEmpty), card_empty]

theorem rank_of_singleton_le_one {a : α} : G.rank {a} ≤ 1 := by
  have ⟨_, h⟩ := G.bases_nonempty {a}
  rw [rank_eq_basis_card h]
  apply (bases_of_singleton h).elim <;> intro h <;>
    simp only [h, card_empty, card_singleton, _root_.zero_le, le_refl]

@[simp]
theorem rank_of_singleton_of_feasible {a : α} (ha : {a} ∈ G) : G.rank {a} = 1 := by
  apply (le_iff_lt_or_eq.mp (rank_of_singleton_le_one : G.rank {a} ≤ 1)).elim _ id
  intro h
  exfalso
  have ⟨_, h'⟩ := G.bases_nonempty {a}
  rw [rank_eq_basis_card h'] at h
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
  have ⟨_, h'⟩ := G.bases_nonempty {a}
  rw [rank_eq_basis_card h'] at h
  exact basis_mem_feasible (eq_of_subset_of_card_le (basis_subset h') (by
    simp only [card_singleton, h, le_refl]) ▸ h')

theorem rank_le_card (s : Finset α) : G.rank s ≤ s.card := by
  simp only [rank, filter_congr_decidable, max'_le_iff, mem_image, Finset.mem_filter,
    forall_exists_index, and_imp]
  intro _ _ _ h₂ h₃
  rw [← h₃]
  exact card_le_card h₂

theorem rank_le_of_subset (hs : s ⊆ t) : G.rank s ≤ G.rank t := by
  simp only [rank, filter_congr_decidable, max'_le_iff, mem_image, Finset.mem_filter,
    forall_exists_index, and_imp]
  intro n u h₁ h₂ h₃
  rw [← h₃]
  apply le_max'
  simp only [mem_image, Finset.mem_filter]
  exists u
  exact ⟨⟨h₁, subset_trans h₂ hs⟩, rfl⟩

theorem ssubset_of_feasible_rank (hs : s ∈ G) (h : t ⊂ s) : G.rank t < G.rank s := by
  apply (le_iff_lt_or_eq.mp (G.rank_le_of_subset (subset_of_ssubset h))).elim <;>
    try simp only [imp_self]
  intro h'
  exfalso
  have h₁ := bases_of_feasible_eq_singleton hs
  have ⟨_, hb₁⟩ := G.bases_nonempty s
  have hb₂ := rank_eq_basis_card hb₁
  rw [h₁, Finset.mem_singleton] at hb₁
  rw [hb₂, hb₁] at h'
  have h₂ : s.card ≤ t.card := h' ▸ (rank_le_card _)
  rw [ssubset_def] at h
  exact absurd ((eq_of_subset_of_card_le h.1 h₂) ▸ h.2) (by simp only [Finset.Subset.refl,
    not_true_eq_false, not_false_eq_true])

@[simp]
theorem rank_of_feasible (hs : s ∈ G) : G.rank s = s.card :=
  @induction_on_accessible α _ _ _ _ hs (fun x => G.rank x = x.card)
    rank_of_empty (by
      simp only [system_feasible_set_mem_mem]
      intro _ _ h₁ _ h₂ _
      rw [card_insert_of_not_mem h₁]
      simp only [h₁, rank_eq_basis_card (mem_bases_self_iff.mp h₂), not_false_eq_true,
        card_insert_of_not_mem])

theorem rank_of_infeasible (hs : s ∉ G) : G.rank s < s.card := by
  apply lt_of_le_of_ne (rank_le_card _)
  intro h
  apply hs
  have ⟨_, hb⟩ := G.bases_nonempty s
  exact mem_bases_self_iff.mpr (bases_of_card_eq hb (rank_eq_basis_card hb ▸ h) ▸ hb)

theorem card_le_rank (h : s.card ≤ G.rank s) : s ∈ G := by
  have := mt (@rank_of_infeasible _ _ _ G s)
  simp only [not_lt, not_not] at this
  apply this
  simp only [h, le_refl]

theorem card_feasible_subset_le_rank (hs : s ∈ G) {t : Finset α} (ht : s ⊆ t) :
    s.card ≤ G.rank t := by
  have ⟨b, hb⟩ := G.bases_nonempty t
  exact rank_eq_basis_card hb ▸ basis_max_card_of_feasible hb hs ht

def exists_basis_containing_element_if_rank_insert_increases
  (h : G.rank s < G.rank (insert x s)) :
    ∃ t ∈ G.bases (insert x s), x ∈ t := by
  by_contra h'
  simp only [not_exists, not_and] at h'
  let ⟨b, hb⟩ := G.bases_nonempty (insert x s)
  have h₁ : x ∉ b := h' _ hb
  have h₂ : b ⊆ s := by
    intro e he
    have h'' := (G.basis_subset hb) he
    rw [mem_insert] at h''
    exact h''.elim (fun h'' => False.elim (h₁ (h'' ▸ he))) (fun h'' => h'')
  have h₃ : G.rank (insert x s) ≤ G.rank s := by
    rw [rank_eq_basis_card hb]
    exact card_feasible_subset_le_rank (G.basis_mem_feasible hb) h₂
  rw [← not_lt_eq] at h₃
  exact h₃ h

theorem every_basis_contains_element_if_rank_insert_increases
  (h : G.rank s < G.rank (insert x s)) (ht : t ∈ G.bases (insert x s)) :
    x ∈ t := by
  have h₁ := (rank_eq_basis_card ht).symm
  let ⟨b, hb⟩ := G.bases_nonempty s
  have h₂ := (rank_eq_basis_card hb).symm
  have ⟨e, he₁, he₂⟩ :=
    G.exchangeProperty (basis_mem_feasible ht) (basis_mem_feasible hb) (h₂ ▸ h₁ ▸ h)
  by_contra h'
  have h₃ : e ∈ s := by
    have := basis_subset ht
    rw [mem_sdiff] at he₁
    have := this he₁.1
    rw [mem_insert] at this
    apply this.elim <;> intro h
    · rw [h] at he₁
      exact False.elim (h' he₁.1)
    · exact h
  have h₄ : (insert e b).card = G.rank s + 1 := by
    rw [mem_sdiff] at he₁
    rw [card_insert_of_not_mem he₁.2, h₂]
  have h₅ : G.rank s + 1 ≤ G.rank s := by
    rw [← h₄]
    apply card_feasible_subset_le_rank he₂
    intro _ h
    rw [mem_insert] at h
    exact h.elim (fun h => h ▸ h₃) (fun h => basis_subset hb h)
  simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at h₅

@[simp]
theorem rank_eq_card_iff_feasible : G.rank s = s.card ↔ s ∈ G :=
  Iff.intro (fun h => card_le_rank (h ▸ le_refl _)) (fun h => rank_of_feasible h)

theorem bases_subset_of_rank_eq_of_subset
  (h₁ : s ⊆ t) (h₂ : G.rank s = G.rank t) :
    G.bases s ⊆ G.bases t := by
  intro b hb
  rw [basis_def]
  simp only [basis_mem_feasible hb, subset_trans (basis_subset hb) h₁, true_and]
  intro a ha₁ ha₂
  by_contra h'
  have ⟨b', hb'⟩ := G.bases_nonempty t
  have h₃ := basis_max_card_of_feasible hb' ha₂ (by
    intro x hx
    rw [mem_insert] at hx
    apply hx.elim <;> intro h
    · rw [h]
      exact ha₁
    · exact h₁ (basis_subset hb h))
  simp only [h', not_false_eq_true, card_insert_of_not_mem, ← rank_eq_basis_card hb, ←
    rank_eq_basis_card hb'] at h₃
  simp only [h₂, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at h₃

theorem rank_eq_of_subset_of_subset {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.rank s = G.rank u) :
    G.rank s = G.rank t := by
  apply Nat.le_antisymm (rank_le_of_subset hst)
  rw [hsu]
  exact (rank_le_of_subset htu)

theorem rank_eq_of_bases_nonempty_subset_bases
  (hst : G.bases s ⊆ G.bases t) :
    G.rank s = G.rank t := by
  have ⟨b, hs⟩ := G.bases_nonempty s
  have ht := hst hs
  simp only [rank_eq_basis_card hs, rank_eq_basis_card ht]

theorem local_submodularity
  (h₁ : G.rank s = G.rank (insert x s))
  (h₂ : G.rank s = G.rank (insert y s)) :
    G.rank (insert x (insert y s)) = G.rank s := by
  have h : G.rank s ≤ G.rank (insert x (insert y s)) :=
    rank_le_of_subset (subset_trans (subset_insert y _) (subset_insert _ _))
  have h := le_iff_lt_or_eq.mp h
  symm
  by_contra h'
  simp only [mem_insert] at h'
  simp only [mem_insert, h', or_false] at h ; clear h'
  have ⟨b₁, hb₁₁⟩ := G.bases_nonempty s
  have hb₁₂ := rank_eq_basis_card hb₁₁
  have hb₁₃ := basis_mem_feasible hb₁₁
  have ⟨b₂, hb₂₁⟩ := G.bases_nonempty (insert x (insert y s))
  rw [hb₁₂, rank_eq_basis_card hb₂₁] at h
  have ⟨a, ha₁, ha₂⟩ := G.exchangeProperty (basis_mem_feasible hb₂₁) hb₁₃ h
  rw [system_feasible_set_mem_mem] at ha₂
  rw [mem_sdiff] at ha₁
  by_cases h₃ : a ∈ s
  · exact ha₁.2 (basis_maximal hb₁₁ h₃ ha₂)
  · have h₄ : a = x ∨ a = y := by
      have : a ∈ insert x (insert y s) := basis_subset hb₂₁ ha₁.1
      simp only [mem_insert, h₃, or_false] at this
      exact this
    apply h₄.elim <;> intro h₄ <;> rw [h₄] at ha₁ ha₂
    · have h₅ : (insert x b₁).card ≤ G.rank (insert x s) := by
        rw [← rank_of_feasible ha₂]
        apply rank_le_of_subset
        intro e; simp only [mem_insert]; intro he
        exact he.elim (fun h => Or.inl h) (fun h => Or.inr ((basis_subset hb₁₁) h))
      have h₆ : G.rank s < (insert x b₁).card := by
        simp only [hb₁₂, ha₁, not_false_eq_true, card_insert_of_not_mem, lt_add_iff_pos_right,
          zero_lt_one]
      have h₇ := lt_of_lt_of_le h₆ h₅
      simp only [h₁, lt_self_iff_false] at h₇
    · have h₅ : (insert y b₁).card ≤ G.rank (insert y s) := by
        rw [← rank_of_feasible ha₂]
        apply rank_le_of_subset
        intro e; simp only [mem_insert]; intro he
        exact he.elim (fun h => Or.inl h) (fun h => Or.inr ((basis_subset hb₁₁) h))
      have h₆ : G.rank s < (insert y b₁).card := by
        simp only [hb₁₂, ha₁, not_false_eq_true, card_insert_of_not_mem, lt_add_iff_pos_right,
          zero_lt_one]
      have h₇ := lt_of_lt_of_le h₆ h₅
      simp only [h₂, lt_self_iff_false] at h₇

theorem stronger_local_submodularity_left
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank (s ∪ t) = G.rank s := by
  symm
  by_contra h'
  have ⟨_, hb₁₁⟩ := G.bases_nonempty (s ∪ t)
  have ⟨b₃, hb₃₁⟩ := G.bases_nonempty (s ∩ t)
  have hb₃₂ := rank_eq_basis_card hb₃₁
  have h' := lt_of_le_of_ne (G.rank_le_of_subset (subset_union_left s t)) h'
  rw [rank_eq_basis_card hb₁₁] at h'
  have ⟨x, hx₁, hx₂⟩ := G.exchangeProperty
    (basis_mem_feasible hb₁₁) (basis_mem_feasible hb₃₁) (hb₃₂ ▸ h₁ ▸ h')
  rw [system_feasible_set_mem_mem] at hx₂
  rw [mem_sdiff] at hx₁
  apply (mem_union.mp (basis_subset hb₁₁ hx₁.1)).elim <;> intro h₃
  · have h₅ : G.rank (insert x b₃) ≤ G.rank s := by
      apply rank_le_of_subset
      intro _ ha
      exact (mem_insert.mp ha).elim
        (fun h => h ▸ h₃)
        (fun h => inter_subset_left s t (basis_subset hb₃₁ h))
    simp_all only [rank_of_basis_eq_card, not_false_eq_true, card_insert_of_not_mem,
      add_le_iff_nonpos_right, nonpos_iff_eq_zero]
  · have h₅ : G.rank (insert x b₃) ≤ G.rank t := by
      apply rank_le_of_subset
      intro _ ha
      exact (mem_insert.mp ha).elim
        (fun h => h ▸ h₃)
        (fun h => inter_subset_right s t (basis_subset hb₃₁ h))
    simp_all only [rank_of_basis_eq_card, not_false_eq_true, card_insert_of_not_mem,
      add_le_iff_nonpos_right, nonpos_iff_eq_zero]

theorem stronger_local_submodularity_right
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank (s ∪ t) = G.rank t := by
  simp only [h₂, ← h₁, stronger_local_submodularity_left h₁ h₂]

/-- List of axioms for rank of greedoid· -/
def greedoidRankAxioms (r : Finset α → ℕ) :=
  (r ∅ = 0) ∧ (∀ {s}, r s ≤ s.card) ∧ (∀ {s t}, s ⊆ t → r s ≤ r t) ∧
  (∀ {s x y}, r s = r (insert x s) → r s = r (insert y s) → r s = r (insert x (insert y s)))

end Rank

/-- Closure of `s` is the largest set which contains `s` and have the same rank with `s`· -/
def closure (G : Greedoid α) (s : Finset α) : Finset α :=
  univ.filter fun x => G.rank (insert x s) = G.rank s

set_option linter.unusedVariables false in
def feasibleContinuations (G : Greedoid α) (s : Finset α) (hs : s ∈ G) :=
  univ.filter fun x => x ∉ s ∧ insert x s ∈ G

theorem feasibleContinuations_eq {s : Finset α} (hs : s ∈ G):
    G.feasibleContinuations s hs = univ \ G.closure s := by
  simp only [feasibleContinuations, mem_univ, closure]
  ext x
  simp only [mem_univ, Finset.mem_filter, true_and, mem_sdiff]
  constructor <;> intro h
  · intro h'
    let ⟨h₁, h₂⟩ := h
    rw [← rank_eq_card_iff_feasible, h'] at h₂
    simp only [h₁, not_false_eq_true, card_insert_of_not_mem] at h₂
    have := G.rank_le_card s
    simp only [h₂, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this
  · constructor
    · intro h'; apply h; rw [insert_eq_of_mem h']
    · have h₁ := Nat.lt_of_le_of_ne (rank_le_of_subset (subset_insert _ _)) (Ne.symm h)
      rw [← rank_eq_card_iff_feasible]
      rw [← rank_eq_card_iff_feasible] at hs
      rw [hs] at h₁
      have h₂ : G.rank (insert x s) = s.card + 1 := by
        apply Nat.le_antisymm (le_trans (rank_le_card _) (card_insert_le x s))
        simp_arith at h₁
        exact h₁
      exact Nat.le_antisymm (rank_le_card _) (h₂ ▸ card_insert_le _ _)

section Closure

variable {s t : Finset α} {x y : α}

theorem mem_closure : x ∈ G.closure s ↔ G.rank (insert x s) = G.rank s :=
  ⟨fun h => by
    simp only [closure, filter_congr_decidable, Finset.mem_filter, mem_univ, true_and] at h
    exact h, fun h => by
    simp only [closure, filter_congr_decidable, Finset.mem_filter, mem_univ, true_and]
    exact h⟩

theorem rank_lt_of_insert_of_not_mem_closure {e : α} (h : e ∉ G.closure s) :
    G.rank s < G.rank (insert e s) := by
  by_contra h'
  rw [not_lt] at h'
  apply h
  exact mem_closure.mpr (_root_.le_antisymm h' (G.rank_le_of_subset (subset_insert e s)))

theorem self_subset_closure : s ⊆ G.closure s := by
  intro x hx
  simp only [mem_closure, insert_eq_of_mem hx]

@[simp]
theorem rank_of_feasible_insert_of_not_mem_closure (h₁ : s ∈ G) {e : α} (h₂ : e ∉ G.closure s) :
    G.rank (insert e s) = s.card + 1 := by
  have h₃ := rank_lt_of_insert_of_not_mem_closure h₂
  rw [rank_of_feasible h₁] at *
  apply eq_of_le_of_lt_succ h₃
  simp_arith
  rw [← @card_insert_of_not_mem _ _ e _ (fun h => h₂ (self_subset_closure h))]
  exact G.rank_le_card (insert e s)

theorem rank_of_feasible_insert_eq_card_add_one_iff_not_mem_closure (h : s ∈ G) {e : α} :
    e ∉ G.closure s ↔ G.rank (insert e s) = s.card + 1 :=
  ⟨rank_of_feasible_insert_of_not_mem_closure h,
   fun h₀ h₁ => by
    rw [mem_closure.mp h₁, rank_eq_card_iff_feasible.mpr h] at h₀
    simp only [self_eq_add_right] at h₀⟩

theorem insert_feasible_of_not_mem_closure_feasible (h₁ : s ∈ G) {e : α} (h₂ : e ∉ G.closure s) :
    insert e s ∈ G := by
  have h₃ : e ∉ s := fun h => h₂ (self_subset_closure h)
  rw [rank_of_feasible_insert_eq_card_add_one_iff_not_mem_closure h₁,
    ← card_insert_of_not_mem h₃] at h₂
  exact rank_eq_card_iff_feasible.mp h₂

theorem subset_closure_of_subset (h : s ⊆ t) : s ⊆ G.closure t := by
  intro x hx
  simp only [mem_closure, h hx, insert_eq_of_mem]

theorem mem_closure_of_insert : x ∈ G.closure (insert x s) :=
  self_subset_closure (mem_insert_self x s)

theorem subset_closure_of_insert : s ⊆ G.closure (insert x s) :=
  subset_closure_of_subset (subset_insert _ _)

@[simp]
theorem rank_closure_eq_rank_self (s : Finset α) : G.rank (G.closure s) = G.rank s := by
  symm
  by_cases h : s = G.closure s
  · rw [← h]
  · have h₁ : s.card < (G.closure s).card := by
      rw [lt_iff_le_and_ne]
      constructor
      · exact card_le_card self_subset_closure
      · exact fun h' => h (eq_of_subset_of_card_le self_subset_closure (by rw [h']))
    have ⟨x, hx⟩ : ∃ x, x ∈ G.closure s \ s := by
      by_contra h'
      simp only [mem_sdiff, not_exists, not_and, not_not] at h'
      simp only [← subset_antisymm self_subset_closure h', lt_self_iff_false] at h₁
    have h₂ := rank_closure_eq_rank_self (insert x s)
    simp only [mem_sdiff, mem_closure] at hx
    rw [← hx.1, ← h₂]
    apply congr_arg
    ext y; simp only [mem_closure]
    constructor <;> intro hy
    · rw [Insert.comm, hx.1] at hy
      have h₃ : G.rank s ≤ G.rank (insert y s) := rank_le_of_subset (subset_insert _ _)
      have h₄ : G.rank (insert y s) ≤ G.rank (insert x (insert y s)) :=
        rank_le_of_subset (subset_insert _ _)
      rw [hy] at h₄
      exact le_antisymm h₄ h₃
    · rw [local_submodularity hy.symm hx.1.symm, hx.1]
termination_by (@univ α _).card - s.card
decreasing_by
  simp_wf
  rw [mem_sdiff] at hx
  simp only [hx.2, not_false_eq_true, card_insert_of_not_mem]
  rw [← Nat.sub_sub]
  exact Nat.sub_lt (tsub_pos_iff_lt.mpr (card_lt_univ_of_not_mem hx.2)) (by decide)

theorem closure_insert_eq_iff_rank_eq :
    G.closure (insert x s) = G.closure s ↔ G.rank (insert x s) = G.rank s := by
  constructor <;> intro h
  · rw [← rank_closure_eq_rank_self s, ← rank_closure_eq_rank_self (insert x s), h]
  · ext e
    constructor <;> intro h₀
    · rw [mem_closure] at *
      apply Nat.le_antisymm _ (rank_le_of_subset (subset_insert _ _))
      rw [← h, ← h₀, Insert.comm]
      exact rank_le_of_subset (subset_insert _ _)
    · rw [mem_closure] at *
      rw [h]
      exact local_submodularity h₀.symm h.symm

theorem subset_closure_of_rank_subset_eq_rank (h₁ : s ⊆ t) (h₂ : G.rank s = G.rank t) :
    t ⊆ G.closure s := by
  intro x hx
  rw [mem_closure]
  exact Nat.le_antisymm
    (h₂.symm ▸ (rank_le_of_subset (insert_subset hx h₁)))
    (rank_le_of_subset (subset_insert _ _))

theorem subset_closure_basis (h : t ∈ G.bases s) :
    s ⊆ G.closure t :=
  G.subset_closure_of_rank_subset_eq_rank (G.basis_subset h)
    (G.rank_eq_basis_card h ▸ rank_of_basis_eq_card (basis_mem_feasible h))

theorem subset_closure_iff_rank_eq_rank_union :
    t ⊆ G.closure s ↔ G.rank s = G.rank (s ∪ t) := by
  constructor <;> intro h
  · have h₁ : G.rank (s ∪ t) ≤ G.rank (G.closure s) := by
      apply rank_le_of_subset
      exact union_subset self_subset_closure h
    rw [rank_closure_eq_rank_self] at h₁
    exact Nat.le_antisymm (rank_le_of_subset (subset_union_left _ _)) h₁
  · exact subset_trans (subset_union_right s t)
      (subset_closure_of_rank_subset_eq_rank (subset_union_left s t) h)

theorem feasible_iff_elem_notin_closure_minus_elem :
    s ∈ G ↔ ∀ x ∈ s, x ∉ G.closure (s \ {x}) := by
  constructor <;> intro h
  · intro x hx h'
    rw [mem_closure] at h'
    have h₁ := sdiff_insert_insert_of_mem_of_not_mem hx (not_mem_empty x)
    simp only [insert_emptyc_eq, mem_sdiff, Finset.mem_singleton, sdiff_empty] at h₁
    rw [h₁] at h'
    have h₃ := G.rank_le_card (s \ {x})
    rw [← h', rank_of_feasible h, card_sdiff (fun y hy => by simp_all)] at h₃
    have : s.card - 1 < s.card := sub_lt (card_pos.mpr ⟨x, hx⟩) (by decide)
    rw [lt_iff_not_ge] at this
    exact this h₃
  · by_contra h'
    have ⟨b, hb₁⟩ := G.bases_nonempty s
    have ⟨y, hy₁, hy₂⟩ : ∃ y ∈ s, y ∉ b := by
      by_contra h'
      simp only [not_exists, not_and, not_not] at h'
      rw [subset_antisymm (basis_subset hb₁) h', ← mem_bases_self_iff] at hb₁
      contradiction
    apply h y hy₁
    rw [mem_closure]
    have : insert y (s \ {y}) = s := by
      ext x; constructor <;> intro h <;>
        simp only [mem_sdiff, Finset.mem_singleton, mem_insert] at *
      · exact h.elim (fun h => h ▸ hy₁) (fun h => h.1)
      · by_cases h₁ : x = y
        · simp only [h₁, true_or]
        · simp only [h₁, h, not_false_eq_true, and_self, or_true]
    rw [this]
    apply Nat.le_antisymm _ (rank_le_of_subset (sdiff_subset _ _))
    rw [rank_eq_basis_card hb₁, ← rank_of_feasible (basis_mem_feasible hb₁)]
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
  have h₃ := Nat.le_antisymm h₁ h₂
  have h₄ := G.rank_closure_eq_rank_self s
  have h₅ := G.rank_closure_eq_rank_self t
  apply subset_antisymm <;> intro x hx
  · rw [mem_closure, ← h₃, ← h₄]
    have h₆ : G.rank t ≤ G.rank (insert x t) := rank_le_of_subset (subset_insert x t)
    rw [← h₃, ← h₄] at h₆
    exact Nat.le_antisymm (rank_le_of_subset (insert_subset hx hts)) h₆
  · rw [mem_closure, h₃, ← h₅]
    have h₆ : G.rank s ≤ G.rank (insert x s) := rank_le_of_subset (subset_insert x s)
    rw [h₃, ← h₅] at h₆
    exact Nat.le_antisymm (rank_le_of_subset (insert_subset hx hst)) h₆

@[simp]
theorem closure_basis_eq_closure_self (h : t ∈ G.bases s) :
    G.closure t = G.closure s :=
  closure_eq_of_subset_adj_closure
    (subset_closure_of_subset (basis_subset h)) (subset_closure_basis h)

@[simp]
theorem closure_idempotent : G.closure (G.closure s) = G.closure s :=
  closure_eq_of_subset_adj_closure Subset.rfl
    (Subset.trans self_subset_closure self_subset_closure)

theorem closure_exchange_property
  (hx : x ∉ s) (hy : y ∉ s) (hs : insert x s ∈ G)
  (h : x ∈ G.closure (insert y s)) :
    y ∈ G.closure (insert x s) := by
  have : G.rank (insert y (insert x s)) = G.rank (insert x s) := by
    apply Nat.le_antisymm _ (rank_le_of_subset (insert_subset _ _))
    · rw [mem_closure, Insert.comm] at h
      rw [h]
      apply le_of_le_of_eq _ (rank_eq_card_iff_feasible.mpr hs).symm
      simp only [hx, not_false_eq_true, card_insert_of_not_mem]
      apply le_of_le_of_eq (rank_le_card _)
      simp only [hy, not_false_eq_true, card_insert_of_not_mem]
    · simp only [mem_insert, Insert.comm, true_or]
    · intro _ _; simp; tauto
  exact mem_closure.mpr this

/-- `cospanning` is an equivalence relation in `2^E`· -/
def cospanning (G : Greedoid α) (s t : Finset α) := G.closure s = G.closure t

section cospanning

variable (hx₀ : x ∉ s) (hy₀ : y ∉ s)

theorem cospanning_refl : ∀ s, G.cospanning s s := by simp only [cospanning, forall_const]

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

theorem cospanning_rel_left_union (h : G.cospanning s t) : G.cospanning s (s ∪ t) := by
  simp only [cospanning] at *
  apply closure_eq_of_subset_adj_closure (G.subset_closure_of_subset (subset_union_left s t))
  intro x hx
  rw [mem_union] at hx
  exact hx.elim (fun h => self_subset_closure h) (fun h' => h.symm ▸ self_subset_closure h')

theorem cospanning_rel_right_union (h : G.cospanning s t) : G.cospanning (s ∪ t) t :=
  cospanning_trans (cospanning_symm (cospanning_rel_left_union h)) h

theorem cospanning_rel_between_subset_left {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.cospanning s u) :
    G.cospanning s t := by
  simp only [cospanning] at *
  apply closure_eq_of_subset_adj_closure (subset_trans hst self_subset_closure)
  rw [hsu]
  exact subset_trans htu self_subset_closure

theorem cospanning_rel_between_subset_right {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.cospanning s u) :
    G.cospanning t u :=
  G.cospanning_trans (cospanning_symm (cospanning_rel_between_subset_left hst htu hsu)) hsu

theorem cospanning_rel_ex
  (h₁ : G.cospanning (insert y s) (insert x (insert y s)))
  (h₂ : ¬ G.cospanning (insert x s) (insert x (insert y s))) :
    ∃ z ∈ insert x s, G.cospanning ((insert x s) \ {z}) (insert x s) := by
  simp only [mem_insert, exists_eq_or_imp, insert_sdiff_of_mem, Finset.mem_singleton]
  by_contra h'
  rw [not_or] at h'
  have h₃ : insert x s ∈ G := by
    rw [feasible_iff_elem_notin_closure_minus_elem]
    intro a ha₁ ha₂
    rw [mem_insert] at ha₁
    simp only [cospanning, mem_insert, not_exists, not_and] at h'
    apply ha₁.elim <;> intro ha₁
    · simp only [ha₁, insert_sdiff_of_mem, Finset.mem_singleton] at ha₂
      apply h'.1 (closure_eq_of_subset_adj_closure _ _)
      · intro y hy
        exact subset_closure_of_subset (subset_trans (sdiff_subset s {x}) (subset_insert x s)) hy
      · intro y hy
        rw [mem_insert] at hy
        apply hy.elim (fun h => h.symm ▸ ha₂)
        intro hy
        by_cases h₃ : y = x
        · exact h₃.symm ▸ ha₂
        · have : y ∈ s \ {x} := by simp only [mem_sdiff, hy, Finset.mem_singleton, h₃,
            not_false_eq_true, and_self]
          exact self_subset_closure this
    · apply h'.2 _ ha₁
      apply closure_eq_of_subset_adj_closure
      · intro _ hy
        exact subset_closure_of_subset (sdiff_subset _ _) hy
      · intro y hy
        by_cases h : y = a
        · simp only [h, ha₂]
        · have : y ∈ insert x s \ {a} := by
            rw [mem_insert] at hy
            simp only [mem_insert, mem_sdiff, hy, Finset.mem_singleton, h, not_false_eq_true,
              and_self]
          exact self_subset_closure this
  have h := closure_exchange_property hx₀ hy₀ h₃ (by
    rw [h₁]
    apply self_subset_closure
    simp only [mem_insert, true_or])
  apply h₂
  apply closure_eq_of_subset_adj_closure
  · have : insert x s ⊆ insert x (insert y s) := by
      intro z hz
      rw [mem_insert] at *
      apply hz.elim (fun h => Or.inl h)
      rw [mem_insert]
      exact fun h => Or.inr (Or.inr h)
    exact subset_trans this self_subset_closure
  · intro z hz
    rw [mem_insert] at hz
    apply hz.elim <;> intro hz
    · exact hz.symm ▸ mem_closure_of_insert
    · rw [mem_insert] at hz
      apply hz.elim <;> intro hz
      · exact hz ▸ h
      · exact subset_closure_of_insert hz

theorem cospanning_rel_ex'
  (h₁ : G.cospanning (insert y s) (insert x (insert y s)))
  (h₂ : ¬ G.cospanning (insert x s) (insert x (insert y s))) :
    ∃ z ∈ insert x s, G.cospanning (insert x s) ((insert x s) \ {z}) :=
  let ⟨z, hz⟩ := cospanning_rel_ex hx₀ hy₀ h₁ h₂
  ⟨z, hz.1, G.cospanning_symm hz.2⟩

end cospanning

theorem closure_union_eq_of_closure_eq_left (h : G.closure s = G.closure t) :
    G.closure (s ∪ t) = G.closure s := by
  rw [cospanning_rel_left_union h]

theorem closure_union_eq_of_closure_eq_right (h : G.closure s = G.closure t) :
    G.closure (s ∪ t) = G.closure t := by
  rw [cospanning_rel_right_union h]

theorem eq_closure_left_of_eq_closure_of_subset_of_subset
  {s t u : Finset α} (hst : s ⊆ t) (htu : t ⊆ u)
  (hsu : G.closure s = G.closure u) :
    G.closure s = G.closure t := by
  rw [cospanning_rel_between_subset_left hst htu hsu]

theorem eq_closure_right_of_eq_closure_of_subset_of_subset
  {s t u : Finset α} (hst : s ⊆ t) (htu : t ⊆ u)
  (hsu : G.closure s = G.closure u) :
    G.closure t = G.closure u := by
  rw [cospanning_rel_between_subset_right hst htu hsu]

-- TODO: change name
theorem closure_weak_exchange_property {x y : α} (hx₀ : x ∉ s) (hy₀ : y ∉ s)
  (h₁ : G.closure (insert y s) = G.closure (insert x (insert y s)))
  (h₂ : G.closure (insert x s) ≠ G.closure (insert x (insert y s))) :
    ∃ z ∈ insert x s, G.closure (insert x s \ {z}) = G.closure (insert x s) :=
  cospanning_rel_ex hx₀ hy₀ h₁ h₂

end Closure

def partialAlphabets (G : Greedoid α) : Finset (Finset α) :=
  univ.filter fun s => ∃ S : Finset (Finset α), s = S.biUnion id ∧ ∀ t ∈ S, t ∈ G

def kernelClosureOperator (G : Greedoid α) (s : Finset α) : Finset α :=
  (G.feasibleSet.filter fun t => G.rank (s ∪ t) = G.rank s).biUnion id

def kernel (G : Greedoid α) (s : Finset α) : Finset α :=
  (s.powerset.filter fun t => t ∈ G).biUnion id

section PartialAlphabets

variable {s : Finset α}

theorem mem_partialAlphabets :
    s ∈ G.partialAlphabets ↔ ∃ S, s = Finset.biUnion S id ∧ ∀ t ∈ S, t ∈ G := by
  simp only [partialAlphabets, filter_congr_decidable, Finset.mem_filter, mem_univ, true_and]

-- CRAPO, Henry. Selectors: a theory of formal languages, semimodular lattices,
-- and branching and shelling processes. Advances in Mathematics, 1984, 54.3: 233-277.

-- G.partialAlphabets is an antimatroid

end PartialAlphabets

section Kernel

variable {s : Finset α}

theorem kernelClosureOperator_def_rank :
    G.kernelClosureOperator s =
      (G.feasibleSet.filter fun t => G.rank (s ∪ t) = G.rank s).biUnion id := rfl

theorem kernelClosureOperator_def_closure :
    G.kernelClosureOperator s =
      (G.feasibleSet.filter fun t => t ⊆ G.closure s).biUnion id := by
  rw [kernelClosureOperator_def_rank]
  ext x
  simp only [system_feasible_set_mem_mem, mem_biUnion, Finset.mem_filter, id_eq]
  constructor <;> rintro ⟨t, ht₁, ht₂⟩ <;> exists t
  · let ⟨ht₁, ht₃⟩ := ht₁
    simp only [ht₁, ht₂, true_and, and_true]
    intro a ha
    rw [mem_closure]
    symm
    apply rank_eq_of_subset_of_subset (subset_insert _ _) _ ht₃.symm
    apply insert_subset_iff.mpr
    constructor <;> simp only [mem_union, ha, or_true, subset_union_left]
  · let ⟨ht₁, ht₃⟩ := ht₁
    simp only [ht₁, ht₂, true_and, and_true]
    symm
    apply rank_eq_of_subset_of_subset (subset_union_left _ _)
      (union_subset self_subset_closure ht₃)
    rw [rank_closure_eq_rank_self]

theorem mem_kernel {x : α} :
    x ∈ G.kernel s ↔ ∃ t ∈ G, t ⊆ s ∧ x ∈ t := by
  constructor <;> intro h <;> simp only [kernel, filter_congr_decidable, mem_biUnion,
    Finset.mem_filter, mem_powerset, id_eq] at * <;> let ⟨a, _⟩ := h <;> exists a <;> tauto

theorem mem_kernelClosureOperator {x : α} :
    x ∈ G.kernelClosureOperator s ↔ ∃ a, a ∈ G ∧ rank G (s ∪ a) = rank G s ∧ x ∈ a := by
  constructor <;> intro h <;> simp only [kernelClosureOperator, filter_congr_decidable, mem_biUnion,
    Finset.mem_filter, system_feasible_set_mem_mem, id_eq] at * <;> tauto

theorem kernelClosureOperator_eq_kernel_closure :
    G.kernelClosureOperator s = G.kernel (G.closure s) := by
  ext x; constructor <;> intro h
  · simp only [kernelClosureOperator_def_closure, system_feasible_set_mem_mem, mem_biUnion,
      Finset.mem_filter, id_eq] at h
    let ⟨a, ⟨ha₁, ha₂⟩, ha₃⟩ := h
    rw [mem_kernel]
    exists a
  · rw [mem_kernel] at h
    simp only [kernelClosureOperator_def_closure, system_feasible_set_mem_mem, mem_biUnion,
      Finset.mem_filter, id_eq]
    let ⟨a, _, _, _⟩ := h
    exists a

theorem kernel_subset : G.kernel s ⊆ s := by
  intro _ h
  have ⟨_, _, h₁, h₂⟩ := mem_kernel.mp h
  exact h₁ h₂

@[simp]
theorem kernel_empty : G.kernel ∅ = ∅ := subset_antisymm kernel_subset (empty_subset _)

theorem bases_subset_bases_kernel : G.bases s ⊆ G.bases (G.kernel s) := by
  intro b hb
  rw [basis_def] at *
  constructor <;> try exact hb.1
  constructor <;> intro _ hx
  · rw [mem_kernel]
    exists b
    simp only [hb, hx, and_self]
  · intro h
    let ⟨_, h'⟩ := mem_kernel.mp hx
    exact hb.2.2 _ (h'.2.1 h'.2.2) h

@[simp]
theorem rank_kernel : G.rank (G.kernel s) = G.rank s := by
  symm
  apply rank_eq_of_bases_nonempty_subset_bases
  intro _ h
  rw [basis_def]
  simp only [basis_mem_feasible h, basis_subset (bases_subset_bases_kernel h), true_and]
  intro _ h₁ h₂
  exact basis_maximal h (kernel_subset h₁) h₂

theorem kernel_eq_empty_iff : G.kernel s = ∅ ↔ G.bases s = {∅} := by
  constructor <;> intro h
  · have : G.bases (G.kernel s) = {∅} := by simp only [h, bases_of_empty]
    apply subset_antisymm (this.symm ▸ bases_subset_bases_kernel)
    simp only [← this, bases_subset_of_rank_eq_of_subset kernel_subset rank_kernel]
  · apply subset_antisymm _ (empty_subset _)
    intro _ hx
    let ⟨_, h₁, h₂, h₃⟩ := mem_kernel.mp hx
    exact bases_empty_feasible_mem h h₁ h₂ ▸ h₃

@[simp]
theorem closure_kernel_eq_closure :
    G.closure (G.kernel s) = G.closure s := by
  apply closure_eq_of_subset_adj_closure (subset_trans kernel_subset G.self_subset_closure)
  intro x hx
  simp only [mem_closure, rank_kernel]
  have h := G.rank_le_of_subset (subset_insert x (G.kernel s))
  rw [rank_kernel] at h
  exact Nat.le_antisymm (G.rank_le_of_subset (insert_subset hx G.kernel_subset)) h

theorem kernelClosureOperator_subset_closure :
    G.kernelClosureOperator s ⊆ G.closure s := by
  simp only [kernelClosureOperator_eq_kernel_closure, kernel_subset]

@[simp]
theorem closure_kernelClosureOperator_eq_closure :
    G.closure (G.kernelClosureOperator s) = G.closure s := by
  rw [kernelClosureOperator_eq_kernel_closure, closure_kernel_eq_closure, closure_idempotent]

@[simp]
theorem kernelClosureOperator_closure_eq_kernelClosureOperator :
    G.kernelClosureOperator (G.closure s) = G.kernelClosureOperator s := by
  rw [kernelClosureOperator_eq_kernel_closure, closure_idempotent,
    ← kernelClosureOperator_eq_kernel_closure]

theorem kernelClosureOperator_eq_iff_closure_eq {s t : Finset α} :
    G.kernelClosureOperator s = G.kernelClosureOperator t ↔
      G.closure s = G.closure t := by
  constructor <;> intro h
  · rw [← closure_kernelClosureOperator_eq_closure, h, closure_kernelClosureOperator_eq_closure]
  · rw [← kernelClosureOperator_closure_eq_kernelClosureOperator, h,
      kernelClosureOperator_closure_eq_kernelClosureOperator]

@[simp]
theorem rank_kernelClosureOperator :
    G.rank (G.kernelClosureOperator s) = G.rank s := by
  simp only [kernelClosureOperator_eq_kernel_closure, rank_kernel, rank_closure_eq_rank_self]

theorem subset_kernelClosureOperator_of_mem_partialAlphabets
  (h : s ∈ G.partialAlphabets) :
    s ⊆ G.kernelClosureOperator s := by
  intro x hx
  simp only [kernelClosureOperator, system_feasible_set_mem_mem, mem_biUnion, Finset.mem_filter,
    id_eq]
  simp only [partialAlphabets, mem_univ, Finset.mem_filter, true_and] at h
  let ⟨S, hS₁, hS₂⟩ := h
  simp only [hS₁, mem_biUnion, id_eq] at hx
  let ⟨t, ht₁, ht₂⟩ := hx
  exists t
  simp only [hS₂ _ ht₁, true_and, ht₂, and_true]
  congr
  rw [union_eq_left]
  intro y hy
  simp only [hS₁, mem_biUnion, id_eq]
  exists t

theorem kernelClosureOperator_eq_of_subset_adj_kernelClosureOperator {s t : Finset α}
  (hs : s ⊆ G.kernelClosureOperator t) (ht : t ⊆ G.kernelClosureOperator s) :
    G.kernelClosureOperator s = G.kernelClosureOperator t := by
  rw [kernelClosureOperator_eq_iff_closure_eq]
  exact closure_eq_of_subset_adj_closure
    (subset_trans hs kernelClosureOperator_subset_closure)
    (subset_trans ht kernelClosureOperator_subset_closure)

@[simp]
theorem kernelClosureOperator_idempotent :
    G.kernelClosureOperator (G.kernelClosureOperator s) = G.kernelClosureOperator s := by
  rw [kernelClosureOperator_eq_kernel_closure, kernelClosureOperator_eq_kernel_closure,
    closure_kernel_eq_closure, closure_idempotent]

end Kernel

def monotoneClosureOperator (G : Greedoid α) (s : Finset α) : Finset α :=
  univ.filter fun a => ∀ {t}, s ⊆ t → G.closure t = t → a ∈ t

section MonotoneClosureOperator

variable {s t : Finset α}

theorem mem_monotoneClosureOperator_iff {a : α} :
    a ∈ G.monotoneClosureOperator s ↔ (∀ {t}, s ⊆ t → G.closure t = t → a ∈ t) := by
  simp only [monotoneClosureOperator, mem_univ, Finset.mem_filter, true_and]

theorem monotoneClosureOperator_subset_closure :
    G.monotoneClosureOperator s ⊆ G.closure s := fun _ h =>
  (mem_monotoneClosureOperator_iff.mp h) self_subset_closure closure_idempotent

-- TODO: Rename.
theorem subset_closure_of_subset_monotoneClosureOperator
  (h₁ : s ⊆ G.monotoneClosureOperator t)
  {u : Finset α} (h₂ : t ⊆ u) :
    s ⊆ G.closure u := by
  intro _ he
  have h₃ := h₁ he
  rw [mem_monotoneClosureOperator_iff] at h₃
  exact h₃ (subset_trans h₂ self_subset_closure) closure_idempotent

theorem subset_monotoneClosureOperator_of_subset_closure
  (h₁ : ∀ {u}, t ⊆ u → s ⊆ G.closure u) :
    s ⊆ G.monotoneClosureOperator t := by
  intro _ he
  rw [mem_monotoneClosureOperator_iff]
  intro _ hu₁ hu₂
  exact subset_trans (h₁ hu₁) (hu₂.symm ▸ subset_rfl) he

theorem subset_monoconeClosureOperator_iff :
    s ⊆ G.monotoneClosureOperator t ↔ ∀ {u}, t ⊆ u → s ⊆ G.closure u :=
  ⟨subset_closure_of_subset_monotoneClosureOperator,
   subset_monotoneClosureOperator_of_subset_closure⟩

theorem subset_monotoneClosureOperator_self : s ⊆ G.monotoneClosureOperator s := by
  intro _ hx
  rw [mem_monotoneClosureOperator_iff]
  intro _ h _
  exact h hx

@[simp]
theorem monotoneClosureOperator_idempotent :
    G.monotoneClosureOperator (G.monotoneClosureOperator s) = G.monotoneClosureOperator s := by
  apply subset_antisymm _ subset_monotoneClosureOperator_self
  intro a ha
  rw [mem_monotoneClosureOperator_iff] at *
  intro _ ht₁ ht₂
  apply ha _ ht₂
  intro _ hx
  rw [mem_monotoneClosureOperator_iff] at hx
  exact hx ht₁ ht₂

theorem monotoneClosureOperator_subset_of_subset (h : s ⊆ t) :
    G.monotoneClosureOperator s ⊆ G.monotoneClosureOperator t := by
  intro _ ha
  rw [mem_monotoneClosureOperator_iff] at *
  intro _ h₁ h₂
  exact ha (subset_trans h h₁) h₂

end MonotoneClosureOperator

def basisRank (G : Greedoid α) (s : Finset α) : ℕ :=
  (G.feasibleSet.image fun t => (s ∩ t).card).max' (by simp)

def rankFeasible (G : Greedoid α) (s : Finset α) : Prop :=
  G.basisRank s = G.rank s

instance : DecidablePred G.rankFeasible :=
  fun s => if h : G.basisRank s = G.rank s then isTrue h else isFalse h

def rankFeasibleFamily (G : Greedoid α) : Finset (Finset α) :=
  univ.filter fun s => G.rankFeasible s

section BasisRank

variable {s : Finset α}

theorem basisRank_le_card :
    G.basisRank s ≤ s.card := by
  simp only [basisRank, max'_le_iff, mem_image, system_feasible_set_mem_mem, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  exact fun _ _ => card_le_card (inter_subset_left _ _)

theorem feasibleSet_inter_card_le_basisRank (s : Finset α) {t : Finset α} (ht : t ∈ G) :
    (s ∩ t).card ≤ G.basisRank s := by
  simp only [basisRank]
  apply le_max'
  simp only [mem_image, system_feasible_set_mem_mem]
  exists t

theorem exists_feasible_satisfying_basisRank (s : Finset α) :
    ∃ t ∈ G, G.basisRank s = (s ∩ t).card := by
  simp only [basisRank]
  have ⟨t, ht₁, ht₂⟩ :=
    G.feasibleSet.exists_max_image (fun t => (s ∩ t).card) G.feasibleSet_nonempty
  exists t
  rw [system_feasible_set_mem_mem] at ht₁
  simp only [ht₁, true_and]
  apply Nat.le_antisymm _ (feasibleSet_inter_card_le_basisRank _ ht₁)
  apply max'_le
  intro n hn
  simp only [mem_image] at hn
  let ⟨_, h₁, h₂⟩ := hn
  exact h₂ ▸ ht₂ _ h₁

theorem rank_le_basisRank : G.rank s ≤ G.basisRank s := by
  simp only [rank, filter_congr_decidable, basisRank, max'_le_iff, mem_image, Finset.mem_filter,
    system_feasible_set_mem_mem, forall_exists_index, and_imp]
  intro n t h₁ h₂ h₃
  rw [← h₃]
  apply le_max'
  simp only [mem_image, system_feasible_set_mem_mem]
  exists t
  rw [← inter_eq_right] at h₂
  simp only [h₁, h₂, and_self]

theorem basisRank_le_rank_iff : G.basisRank s ≤ G.rank s ↔ G.rankFeasible s :=
  ⟨fun h => le_antisymm h rank_le_basisRank, fun h => h ▸ le_rfl⟩

theorem mem_rankFeasibleFamily_iff :
    s ∈ G.rankFeasibleFamily ↔ G.rankFeasible s := by
  simp only [rankFeasibleFamily, mem_univ, Finset.mem_filter, true_and]

theorem rankFeasible_of_feasible (h : s ∈ G) :
    G.rankFeasible s := by
  simp only [rankFeasible]
  apply Nat.le_antisymm _ rank_le_basisRank
  simp only [basisRank, max'_le_iff, mem_image, system_feasible_set_mem_mem, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
  intro t _
  simp only [rank, system_feasible_set_mem_mem]
  apply le_max'
  simp only [system_feasible_set_mem_mem, mem_image, Finset.mem_filter]
  have ⟨l, hl₁, hl₂, hl₃⟩ := construction_of_accessible G.containsEmpty h
  simp only [system_feasible_set_mem_mem] at hl₃
  exists (l.drop (l.length - (s ∩ t).card)).toFinset
  constructor <;> try constructor
  · apply hl₃ _
    exists l.take (l.length - (s ∩ t).card)
    simp only [take_append_drop]
  · have h₀ := Sublist.subset (drop_sublist (l.length - (s ∩ t).card) l)
    have h₁ : (l.drop (l.length - (s ∩ t).card)).toFinset ⊆ l.toFinset := by
      intro _ h
      simp only [mem_toFinset] at *
      apply h₀ h
    exact hl₂ ▸ h₁
  · rw [toFinset_card_of_nodup (Nodup.sublist (drop_sublist _ _) hl₁)]
    rw [length_drop, Nat.sub_sub_self]
    rw [← toFinset_card_of_nodup hl₁]
    exact card_le_card (hl₂ ▸ inter_subset_left _ _)

theorem feasibleSet_subset_rankFeasibleFamily :
    G.feasibleSet ⊆ G.rankFeasibleFamily := by
  intro _ h
  rw [mem_rankFeasibleFamily_iff]
  exact rankFeasible_of_feasible h

@[simp]
theorem feasible_iff_rankFeasible_of_full [Full G] :
    G.feasibleSet = G.rankFeasibleFamily := by
  apply subset_antisymm feasibleSet_subset_rankFeasibleFamily
  intro s hs
  rw [mem_rankFeasibleFamily_iff] at hs
  have h₁ : G.basisRank s ≤ G.rank s := hs ▸ Nat.le_refl _
  simp only [basisRank, max'_le_iff, mem_image, system_feasible_set_mem_mem, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] at h₁
  apply card_le_rank
  have h₂ : s ∩ univ = s := inter_univ s
  apply h₂ ▸ h₁ _
  exact Full.full

-- G.rankFeasibleFamily = univ.powerset ↔ G is a matroid.

-- p.64, lemma 3.1
theorem exists_superset_feasible_satisfying_basisRank {t : Finset α} (ht₁ : t ⊆ s) (ht₂ : t ∈ G) :
    ∃ b ∈ G, t ⊆ b ∧ G.basisRank s = (s ∩ b).card := by
  have ⟨c, hc₁, hc₂⟩ := G.exists_feasible_satisfying_basisRank s
  by_cases h : c.card ≤ t.card
  · have h₁ : t.card ≤ G.basisRank s := by
      have ⟨b, hb₁, hb₂⟩ := G.exists_basis_containing_feasible_set ht₂ ht₁
      apply Nat.le_trans (card_le_card hb₂)
      simp only [basisRank]
      apply le_max'
      simp only [mem_image, system_feasible_set_mem_mem]
      exists b
      simp only [G.basis_mem_feasible hb₁, inter_eq_right.mpr (G.basis_subset hb₁), and_self]
    have h₂ : G.basisRank s ≤ c.card := hc₂ ▸ card_le_card (inter_subset_right _ _)
    have h₃ : G.basisRank s = t.card := le_antisymm (le_trans h₂ h) h₁
    exists t
    simp only [ht₂, Finset.Subset.refl, h₃, inter_eq_right.mpr ht₁, and_self]
  · simp only [not_le] at h
    have ⟨b, hb₁, hb₂, hb₃, hb₄⟩ :=
      exchangeProperty_exists_superset_of_card_le G.exchangeProperty hc₁ ht₂ (le_of_lt h) le_rfl
        (le_of_lt h)
    exists b
    apply And.intro hb₁ (And.intro hb₂ _)
    have h₁ {x y : Finset α} : (x ∩ y).card = x.card - (x \ y).card := by
      simp only [← card_sdiff_add_card_inter x y, add_tsub_cancel_left]
    have h₂ {x y : Finset α} : (x \ y).card = x.card - (x ∩ y).card := by
      simp only [← card_sdiff_add_card_inter x y, add_tsub_cancel_right]
    have h₃ {x y : Finset α} : (x \ y).card ≤ x.card := by
      simp only [h₂, tsub_le_iff_right, le_add_iff_nonneg_right, _root_.zero_le]
    have h₄ {x y z : Finset α} (h : x ⊆ z) : (x \ y).card ≤ (z \ y).card := by
      apply card_le_card
      intro _ h'
      rw [mem_sdiff] at *
      exact ⟨h h'.1, h'.2⟩
    apply Nat.le_antisymm _ (feasibleSet_inter_card_le_basisRank _ hb₁)
    rw [hc₂, inter_comm s, inter_comm s, h₁, h₁, tsub_le_iff_right, ← Nat.sub_add_comm h₃,
      le_tsub_iff_right (le_trans h₃ (Nat.le_add_right _ _))]
    simp only [hb₄, add_le_add_iff_left]
    apply le_trans (h₄ hb₃) (le_of_eq _)
    have h : (c ∪ t) \ s = c \ s := by
      ext; constructor <;> intro h
      · simp only [mem_sdiff, mem_union] at h
        let ⟨h₁, h₂⟩ := h
        simp only [mem_sdiff, h₂, not_false_eq_true, and_true]
        apply h₁.elim (fun h₁ => h₁)
        intro h₁
        exfalso
        exact h₂ (ht₁ h₁)
      · simp only [mem_sdiff] at h
        simp only [mem_sdiff, mem_union, h, true_or, not_false_eq_true, and_self]
    rw [h]

theorem rankFeasible_TFAE (G : Greedoid α) (s : Finset α) :
    TFAE [
      G.rankFeasible s,
      ∀ {t}, t ⊆ univ \ s → G.rank (s ∪ t) ≤ G.rank s + t.card,
      ∀ {b}, b ∈ G.bases s → ∀ {t}, t ⊆ univ \ s → G.rank (s ∪ t) = G.rank (b ∪ t)
    ] := by
  tfae_have 1 → 3
  {
    intro h₁ b h₂ t _
    apply Nat.le_antisymm
    · have ⟨b₀, hb₀⟩ := G.bases_nonempty (s ∪ t)
      have h₄ : b.card ≤ b₀.card := G.basis_card_le_of_subset_bases h₂ hb₀ (subset_union_left _ _)
      have ⟨b', hb'₁, hb'₂, hb'₃, hb'₄⟩ := exchangeProperty_exists_superset_of_card_le
        G.exchangeProperty (G.basis_mem_feasible hb₀) (G.basis_mem_feasible h₂) h₄ le_rfl h₄
      have h₅ : (b' ∩ s).card ≤ G.rank s := by
        rw [← h₁]
        exact (Finset.inter_comm b' s) ▸ G.feasibleSet_inter_card_le_basisRank _ hb'₁
      rw [G.rank_eq_basis_card h₂] at h₅
      have h₆ : b = b' ∩ s := by
        ext; constructor <;> intro h
        · rw [mem_inter]
          exact ⟨(hb'₂ h), G.basis_subset h₂ h⟩
        · rw [mem_inter] at h
          by_contra h'
          have : b.card < (b' ∩ s).card := by
            apply card_lt_card
            apply ssubset_def.mpr (And.intro _ _)
            · intro _ h''
              rw [mem_inter]
              exact ⟨hb'₂ h'', G.basis_subset h₂ h''⟩
            · intro h''
              apply h' (h'' _)
              rw [mem_inter]
              exact h
          have := Nat.lt_of_lt_of_le this h₅
          simp only [lt_self_iff_false] at this
      have h₇ : b' ⊆ b ∪ t := by
        intro _ h
        rw [mem_union, h₆]
        simp only [mem_inter, h, true_and]
        rw [← mem_union]
        have : b₀ ∪ b ⊆ s ∪ t := by
          exact union_subset_iff.mpr
            ⟨G.basis_subset hb₀, subset_trans (G.basis_subset h₂) (subset_union_left s t)⟩
        exact this (hb'₃ h)
      have h₈ : b'.card ≤ G.rank (b ∪ t) := by
        have ⟨d, hd₁, hd₂⟩ := G.exists_basis_containing_feasible_set hb'₁ h₇
        rw [G.rank_eq_basis_card hd₁]
        exact card_le_card hd₂
      apply le_trans _ h₈
      rw [hb'₄, G.rank_eq_basis_card hb₀]
    · apply rank_le_of_subset
      intro _ h
      simp only [mem_union] at *
      exact h.elim (fun h => Or.inl (G.basis_subset h₂ h)) (fun h => Or.inr h)
  }
  tfae_have 3 → 2
  {
    intro h₃ t ht
    let ⟨_, hb⟩ := G.bases_nonempty s
    rw [h₃ hb ht, G.rank_eq_basis_card hb]
    exact le_trans (rank_le_card _) (card_union_le _ _)
  }
  tfae_have 2 → 1
  {
    intro h
    by_contra h'
    simp only [rankFeasible, ne_iff_lt_or_gt, gt_iff_lt] at h'
    apply h'.elim <;> intro h'
    · simp only [basisRank, max'_lt_iff, mem_image, system_feasible_set_mem_mem, and_imp,
        forall_exists_index, forall_apply_eq_imp_iff₂] at h'
      have ⟨b, hb⟩ := G.bases_nonempty s
      have h' := inter_eq_right.mpr (G.basis_subset hb)
        ▸ G.rank_eq_basis_card hb
        ▸ h' b (G.basis_mem_feasible hb)
      exact (lt_self_iff_false _).mp h'
    · let ⟨t, ht⟩ := G.exists_feasible_satisfying_basisRank s
      rw [ht.2] at h'
      let u := t \ s
      have h₁ : u ⊆ univ \ s := by
        intro _ h
        simp only [lt_or_lt_iff_ne, mem_sdiff, mem_univ, true_and] at *
        exact h.2
      have h₂ : G.rank s + u.card < G.rank (s ∪ u) := by
        rw [union_sdiff_self_eq_union]
        apply Nat.lt_of_lt_of_le _ (card_feasible_subset_le_rank ht.1 (subset_union_right _ _))
        simp only [← card_sdiff_add_card_inter t s, add_comm (t \ s).card, add_lt_add_iff_right,
          inter_comm s t ▸ h']
      exact (lt_self_iff_false _).mp (lt_of_lt_of_le h₂ (h h₁))
  }
  tfae_finish

theorem basisRank_union_add_rank_inter_le_basisRank_add_basisRank (s t : Finset α) :
    G.basisRank (s ∪ t) + G.rank (s ∩ t) ≤ G.basisRank s + G.basisRank t := by
  let ⟨b₁, hb₁⟩ := G.bases_nonempty (s ∩ t)
  let ⟨u, hu₁, hu₂⟩ := G.exists_feasible_satisfying_basisRank (s ∪ t)
  let ⟨b₀, hb₀⟩ := G.bases_nonempty (s ∪ t ∪ u)
  have h₀ := G.basis_card_le_of_subset_bases hb₁ hb₀ (fun _ h => by
    simp only [union_assoc, mem_inter, mem_union] at *; exact Or.inl h.1)
  let ⟨b₂, hb₂, hb₃, hb₄, hb₅⟩ := exchangeProperty_exists_superset_of_card_le G.exchangeProperty
    (G.basis_mem_feasible hb₀) (G.basis_mem_feasible hb₁) h₀ le_rfl h₀
  apply le_trans _ (Nat.add_le_add
    (inter_comm s b₂ ▸ G.feasibleSet_inter_card_le_basisRank _ hb₂)
    (inter_comm t b₂ ▸ G.feasibleSet_inter_card_le_basisRank _ hb₂))
  rw [← card_union_add_card_inter, ← inter_distrib_left, ← inter_inter_distrib_left]
  have h₁ : b₁.card ≤ (b₂ ∩ (s ∩ t)).card := by -- Possible typo in the proof of the book
    apply card_le_card
    intro _ h'
    rw [mem_inter]
    exact And.intro (hb₃ h') (G.basis_subset hb₁ h')
  apply le_trans _ (Nat.add_le_add_left h₁ _)
  have h₂ {x y : Finset α} : (x ∩ y).card = x.card - (x \ y).card := by
    simp only [← card_sdiff_add_card_inter x y, add_tsub_cancel_left]
  have h₃ {x y : Finset α} : (x \ y).card = x.card - (x ∩ y).card := by
    simp only [← card_sdiff_add_card_inter x y, add_tsub_cancel_right]
  simp only [hu₂, G.rank_eq_basis_card hb₁, add_le_add_iff_right]
  have h₄ : b₀ ∪ b₁ ⊆ s ∪ t ∪ u := by
    have h₄ : b₀ ⊆ s ∪ t ∪ u := subset_trans (G.basis_subset hb₀) subset_rfl
    have h₅ : b₁ ⊆ s ∪ t ∪ u :=
      subset_trans (subset_trans hb₃ hb₄) (union_subset h₄ (subset_trans (G.basis_subset hb₁)
        (subset_trans inter_subset_union (subset_union_left _ u))))
    exact union_subset h₄ h₅
  have h₅ : u.card ≤ b₂.card := by
    apply G.basis_max_card_of_feasible _ hu₁ (subset_union_right (s ∪ t) u)
    exact G.basis_of_basis_card_eq_of_subset hb₀ hb₅ (subset_trans hb₄ h₄) hb₂
  have h₆ : (b₂ \ (s ∪ t)).card ≤ (u \ (s ∪ t)).card := by
    apply card_le_card
    intro _ h
    rw [← union_sdiff_right]
    apply sdiff_subset_sdiff _ subset_rfl h
    rw [union_comm u]
    exact subset_trans hb₄ h₄
  rw [inter_comm _ u, h₂, h₂, tsub_le_iff_right, ← Nat.sub_add_comm, le_tsub_iff_right]
  · exact Nat.add_le_add h₅ h₆
  · exact le_add_left h₆
  · exact h₃ ▸ sub_le _ _

theorem rankFeasibleFamily_submodular
  (s : Finset α) (hs : G.rankFeasible s) (t : Finset α) (ht : G.rankFeasible t) :
    G.rank (s ∪ t) + G.rank (s ∩ t) ≤ G.rank s + G.rank t := by
  rw [← hs, ← ht]
  apply le_trans _ (G.basisRank_union_add_rank_inter_le_basisRank_add_basisRank s t)
  simp only [add_le_add_iff_right, rank_le_basisRank]

-- Chapter V. Theorem 3.4
theorem rankFeasible_iff_subset_subset_monotoneClosure :
    G.rankFeasible s ↔ ∀ {t}, t ∈ G.bases s → s ⊆ G.monotoneClosureOperator t := by
  constructor <;> intro h
  · intro x hx
    rw [subset_monoconeClosureOperator_iff]
    intro y hy
    by_contra h'
    let ⟨b, hb⟩ := G.bases_nonempty y
    have h₁ : x.card ≤ b.card :=
      G.basis_card_le_of_subset_bases (mem_bases_self_iff.mp (G.basis_mem_feasible hx)) hb hy
    have ⟨c, hc₁, hc₂, hc₃, hc₄⟩ := exchangeProperty_exists_superset_of_card_le G.exchangeProperty
      (G.basis_mem_feasible (G.base_bases_eq ▸ hb)) (G.basis_mem_feasible hx) h₁ le_rfl h₁
    rw [system_feasible_set_mem_mem] at hc₁
    simp only [not_subset, not_and] at h'
    let ⟨e, he₁, he₂⟩ := h'; clear h'
    have h₂ : c ∈ G.bases y := by
      simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter, hc₁, true_and]
      apply And.intro (subset_trans hc₃ (union_subset (basis_subset hb) hy))
      intro a ha₁ ha₂
      have h₂ : insert a c ⊆ y := fun _ h => (mem_insert.mp h).elim
        (fun h => h ▸ ha₁) (fun h => union_subset (basis_subset hb) hy (hc₃ h))
      have h₃ := basis_max_card_of_feasible hb ha₂ h₂
      rw [← hc₄] at h₃
      by_contra h'
      rw [card_insert_of_not_mem h'] at h₃
      simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at h₃
    have h₃ : e ∉ G.closure c := by
      intro h
      apply he₂
      rw [← closure_basis_eq_closure_self h₂]
      exact h
    have h₄ : G.rank s < (s ∩ (insert e c)).card := by
      rw [rank_eq_basis_card hx, lt_iff_add_one_le,
        ← card_insert_of_not_mem (fun h => he₂ (self_subset_closure (hy h))),
        inter_insert_of_mem he₁]
      exact card_le_card (insert_subset_insert _ (subset_inter (basis_subset hx) hc₂))
    exact (lt_self_iff_false _).mp
      (lt_of_le_of_lt (h ▸ feasibleSet_inter_card_le_basisRank _
        (insert_feasible_of_not_mem_closure_feasible hc₁ h₃)) h₄)
  · rw [← basisRank_le_rank_iff, basisRank, max'_le_iff]
    intro br hbr
    simp only [mem_image, system_feasible_set_mem_mem] at hbr
    let ⟨b, hb₁, hb₂⟩ := hbr
    rw [← hb₂]; clear br hbr hb₂
    let ⟨x, hx⟩ := G.bases_nonempty s
    by_cases h₁ : b.card ≤ x.card
    · rw [rank_eq_basis_card hx]
      exact le_trans (card_le_card (inter_subset_right _ _)) h₁
    · rw [not_le] at h₁
      let ⟨a, ha₁, ha₂, ha₃, ha₄⟩ := exchangeProperty_exists_superset_of_card_le G.exchangeProperty
        hb₁ (basis_mem_feasible hx) (le_of_lt h₁) le_rfl (le_of_lt h₁)
      have h₂ : a ∩ s = x := by
        apply subset_antisymm _ (Finset.subset_inter ha₂ (basis_subset hx))
        intro e h₂
        let ⟨h₂, h₃⟩ := mem_inter.mp h₂
        by_contra h'
        let ⟨y, hy₁, hy₂, _, hy₃, hy₄⟩:=
          exchangeProperty_exists_feasible_superset_add_element_feasible G.exchangeProperty ha₁
            (basis_mem_feasible hx) ha₂ h₂ h'
        have h₄ : e ∉ G.closure y := by
          intro h₄
          rw [mem_closure, rank_eq_card_iff_feasible.mpr hy₁, rank_eq_card_iff_feasible.mpr hy₄,
            card_insert_of_not_mem hy₃] at h₄
          simp only [add_right_eq_self] at h₄
        exact h₄ ((subset_closure_of_subset_monotoneClosureOperator (h hx) hy₂) h₃)
      rw [rank_eq_basis_card hx, ← h₂, inter_comm s b]
      rw [← card_inter_add_card_sdiff a s, ← card_inter_add_card_sdiff b s] at ha₄
      rw [eq_tsub_of_add_eq ha₄, Nat.add_sub_assoc (by
        apply card_le_card
        intro e he
        simp only [mem_sdiff] at *
        simp only [he.2, not_false_eq_true, and_true]
        have h : e ∈ b ∪ x := ha₃ he.1
        rw [mem_union] at h
        apply h.elim id
        intro h
        rw [← h₂] at h
        rw [mem_inter] at h
        tauto)]
      simp only [le_add_iff_nonneg_right, _root_.zero_le]

theorem rankFeasible_iff_monotoneClosure_equal_for_all_basis :
    G.rankFeasible s ↔
    ∀ {t}, t ∈ G.bases s → G.monotoneClosureOperator s = G.monotoneClosureOperator t := by
  constructor <;> intro h
  · rw [rankFeasible_iff_subset_subset_monotoneClosure] at h
    intro b hb
    apply subset_antisymm _ (monotoneClosureOperator_subset_of_subset (basis_subset hb))
    intro _ he
    simp only [monotoneClosureOperator, filter_congr_decidable, Finset.mem_filter, mem_univ,
      true_and]
    intro _ h₁ h₂
    have := h₂ ▸ G.monotoneClosureOperator_subset_of_subset
      (subset_closure_of_subset_monotoneClosureOperator (h hb) (h₂ ▸ h₁))
    exact (h₂ ▸ subset_trans this monotoneClosureOperator_subset_closure) he
  · rw [rankFeasible_iff_subset_subset_monotoneClosure]
    intro _ ht
    exact h ht ▸ subset_monotoneClosureOperator_self

theorem rank_le_of_rankFeasible_insert_not_mem_and_kernelClosureOperator_neq
  (hs : G.rankFeasible s) {x : α} (hx : x ∉ s)
  (h : G.kernelClosureOperator s ≠ G.kernelClosureOperator (insert x s)) :
    G.rank (insert x s) = G.rank s + 1 := by
  by_contra h'
  apply h; clear h
  have h₁ : G.rank (insert x s) ≤ G.rank s + 1 := by
    have h : {x} ⊆ univ \ s := by
      simp only [singleton_subset_iff, mem_sdiff, mem_univ, hx, not_false_eq_true, and_self]
    have := ((G.rankFeasible_TFAE s).out 0 1).mp hs
    have := this h
    rw [card_singleton, union_comm, ← insert_eq] at this
    exact this
  have h₁ : G.rank (insert x s) ≤ G.rank s := by
    have h₁ := le_or_eq_of_le_succ h₁
    simp only [h', or_false] at h₁
    exact h₁
  have h₂ : G.rank s ≤ G.rank (insert x s) := G.rank_le_of_subset (subset_insert _ _)
  have h : G.rank (insert x s) = G.rank s := le_antisymm h₁ h₂
  simp_all only [self_eq_add_right, not_false_eq_true, le_add_iff_nonneg_right, _root_.zero_le,
    le_refl]
  rw [← closure_insert_eq_iff_rank_eq] at h
  rw [kernelClosureOperator_eq_kernel_closure, kernelClosureOperator_eq_kernel_closure, h]

theorem rank_eq_of_mem_kernelClosureOperator_isnert
  {x : α} (h : x ∈ G.kernelClosureOperator s) :
    G.rank (insert x s) = G.rank s := by
  let ⟨_, _, h₁, h₂⟩ := mem_kernelClosureOperator.mp h
  symm
  apply rank_eq_of_subset_of_subset (subset_insert _ _) _ h₁.symm
  intro _ h
  simp only [mem_insert, mem_union] at *
  exact h.elim (fun h => h ▸ Or.inr h₂) (fun h => Or.inl h)

-- Chapter V. Lemma 3.5.
theorem kernelClosureOperator_weak_exchange_property_over_rankFeasible
  (hs : G.rankFeasible s)
  {y : α} (hy₁ : y ∉ s) (hy₂ : G.kernelClosureOperator s ≠ G.kernelClosureOperator (insert y s))
  {z : α} (hz₁ : z ∉ s) (hz₂ : y ∈ G.kernelClosureOperator (insert z s)) :
    z ∈ G.kernelClosureOperator (insert y s) := by
  have h₁ : G.rank (insert y s) = G.rank s + 1 := by
    rw [← rank_le_of_rankFeasible_insert_not_mem_and_kernelClosureOperator_neq hs hy₁ hy₂]
  have h₂ : G.rank (insert z s) = G.rank s + 1 := by
    rw [← rank_le_of_rankFeasible_insert_not_mem_and_kernelClosureOperator_neq hs hz₁]
    have h₂ : y ∉ G.kernelClosureOperator s := by
      intro h
      simp only [kernelClosureOperator_def_closure, mem_biUnion, Finset.mem_filter,
        system_feasible_set_mem_mem, id_eq] at h
      let ⟨a₁, ⟨ha₁₁, ha₁₂⟩, ha₁₃⟩ := h
      have h := ha₁₂ ha₁₃
      simp only [mem_closure, h₁, add_right_eq_self] at h
    intro h'
    exact h₂ (h' ▸ hz₂)
  have h₃ : G.rank (insert z (insert y s)) = G.rank s + 1 := by
    have h := rank_eq_of_mem_kernelClosureOperator_isnert hz₂
    rw [Insert.comm] at h
    rw [h, h₂]
  have h₄ : G.kernelClosureOperator (insert y s) = G.kernelClosureOperator (insert z s) := by
    ext x
    simp [mem_kernelClosureOperator]
    constructor <;> intro h <;> let ⟨a, ha₁, ha₂, ha₃⟩ := h <;> clear h
    · have h₁₁ : ∀ b ∈ G.bases (insert y s), y ∈ b := by
        intro _ h
        apply G.every_basis_contains_element_if_rank_insert_increases _ h
        simp only [h₁, lt_add_iff_pos_right, zero_lt_one]
      have h₂₁ : ∀ b ∈ G.bases (insert z s), z ∈ b := by
        intro _ h
        apply G.every_basis_contains_element_if_rank_insert_increases _ h
        simp only [h₂, lt_add_iff_pos_right, zero_lt_one]
      sorry
    · sorry
  have ⟨b, hb₁, hb₂⟩ : ∃ b ∈ G.bases (insert z s), z ∈ b := by
    by_contra h'
    simp only [not_exists, not_and] at h'
    let ⟨b, hb⟩ := G.bases_nonempty (insert z s)
    have h : b ∈ G.bases s := by
      simp only [bases, system_feasible_set_mem_mem, Finset.mem_filter]
      have h : b ⊆ s := fun _ he =>
        (mem_insert.mp (basis_subset hb he)).elim (fun h => False.elim (h' _ hb (h ▸ he))) id
      simp only [basis_mem_feasible hb, true_and, h]
      intro _ ha₁ ha₂
      simp only [bases, mem_insert, system_feasible_set_mem_mem, forall_eq_or_imp,
        Finset.mem_filter] at hb
      exact hb.2.2.2 _ ha₁ ha₂
    simp only [rank_eq_basis_card hb, rank_eq_basis_card h, self_eq_add_right] at h₂
  have h₅ : s ∪ b = insert z s := by
    ext x
    constructor <;> intro h
    · rw [mem_union] at h
      apply h.elim <;> intro h
      · rw [mem_insert]
        exact Or.inr h
      · exact basis_subset hb₁ h
    · rw [mem_union]
      rw [mem_insert] at h
      exact h.elim (fun h => Or.inr (h ▸ hb₂)) (fun h => Or.inl h)
  simp only [kernelClosureOperator_def_rank, insert_union, mem_biUnion, Finset.mem_filter,
    system_feasible_set_mem_mem, id_eq]
  exists b
  simp only [basis_mem_feasible hb₁, h₅, true_and, hb₂, and_true]
  rw [Insert.comm, h₃, h₁]

-- Chapter V. Lemma 3.6.
theorem rankFeasibleFamily_accessibleProperty :
    _root_.accessibleProperty G.rankFeasibleFamily := by
  sorry

instance : Accessible G.rankFeasibleFamily := ⟨G.rankFeasibleFamily_accessibleProperty⟩

def closureFeasible (G : Greedoid α) (s : Finset α) : Prop :=
  ∀ ⦃t u : Finset α⦄, t ⊆ u → s ⊆ G.closure t → s ⊆ G.closure u

instance : DecidablePred G.closureFeasible := fun s =>
  if h : ((univ ×ˢ univ).filter fun t => t.1 ⊆ t.2).image (fun t =>
    (s ⊆ G.closure t.1 → s ⊆ G.closure t.2) : Finset α × Finset α → Bool) = { true }
  then isTrue (by
    simp only [closureFeasible]
    intro t u h₁ h₂
    have h₃ : (t, u) ∈ (univ ×ˢ univ).filter
      (fun t => t.1 ⊆ t.2) := by
      simp only [univ_product_univ, Finset.mem_filter, mem_univ, h₁, and_self]
    have h₄ : decide (s ⊆ G.closure t → s ⊆ G.closure u) ∈ image (fun t =>
        decide (s ⊆ closure G t.1 → s ⊆ closure G t.2))
        (Finset.filter (fun t ↦ t.1 ⊆ t.2) (univ ×ˢ univ)) := by
      apply Finset.mem_image_of_mem _ h₃
    rw [h] at h₄
    simp only [Finset.mem_singleton, decide_eq_true_eq] at h₄
    exact h₄ h₂)
  else isFalse (fun h' => h (by
    clear h
    ext x
    simp only [univ_product_univ, mem_image, Finset.mem_filter, mem_univ, true_and, Prod.exists,
      Finset.mem_singleton]
    simp only [closureFeasible] at h'
    constructor <;> intro h
    · let ⟨t, u, h₁, h₂⟩ := h
      rw [← h₂]
      simp only [decide_eq_true_eq]
      exact h' h₁
    · rw [h]
      exists ∅, ∅
      simp only [Finset.Subset.refl, imp_self, decide_True, and_self]))

def closureFeasibleFamily (G : Greedoid α) : Finset (Finset α) :=
  G.feasibleSet.filter fun s => G.closureFeasible s

-- Chapter V. Lemma 3.7.
theorem closureFeasibleFamily_subset_rankFeasibleFamily :
    G.closureFeasibleFamily ⊆ G.rankFeasibleFamily := by
  sorry

end BasisRank

end Greedoid
