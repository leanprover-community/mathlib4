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

structure Greedoid (α : Type _) [DecidableEq α] [Fintype α] where
  feasibleSet : Finset (Finset α)
  containsEmpty : ∅ ∈ feasibleSet
  accessible : {s : Finset α} → s ∈ feasibleSet → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ feasibleSet
  exchangeProperty : _root_.exchangeProperty feasibleSet

section Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α]

/-- Definition of `Finset` in `Greedoid`.
    This is often called 'feasible'. -/
protected def Greedoid.mem (s : Finset α) (G : Greedoid α) := s ∈ G.feasibleSet

instance {α : Type _} [Fintype α] [DecidableEq α] :
  Membership (Finset α) (Greedoid α) := ⟨Greedoid.mem⟩

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
    simp; exists G.feasibleSet; simp; exact ⟨G.containsEmpty, G.accessible, G.exchangeProperty⟩

section Membership

@[simp]
theorem system_feasible_set_mem_mem {s : Finset α} : s ∈ G.feasibleSet ↔ s ∈ G := by rfl

theorem emptyset_mem : ∅ ∈ G := G.containsEmpty

theorem mem_accessible
  {s : Finset α} (hs₁ : s ∈ G.feasibleSet) (hs₂ : s ≠ ∅) :
    ∃ x ∈ s, s \ {x} ∈ G.feasibleSet :=
  G.accessible hs₁ hs₂

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
                     A ∪ {x} ∈ G → C ∪ {x} ∈ G → B ∪ {x} ∈ G

/-- Matroid is an interval greedoid without lower bound. -/
class IntervalPropertyWithoutLowerBound (G : Greedoid α) where
  /-- If there are two intervals A ⊆ B and
      some x ∉ B which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval. -/
  intervalPropertyWOLowerBound : {A : Finset α} → A ∈ G →
                                 {B : Finset α} → B ∈ G → A ⊆ B →
                                 {x : α} → x ∉ B →
                                 B ∪ {x} ∈ G → A ∪ {x} ∈ G

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
                                 B ∪ {x} ∈ G → A ∪ {x} ∈ G

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
  simp only [rank, subset_empty, system_feasible_set_mem_mem, Finset.filter_eq']
  simp only [G.containsEmpty]
  simp only [ite_true, image_singleton, card_empty, max_singleton, WithBot.unbot_coe]

theorem rank_of_singleton_le_one {a : α} : G.rank {a} ≤ 1 := by
  have ⟨_, h⟩ : Nonempty (G.bases {a}) := G.bases_nonempty
  rw [rank_eq_bases_card h]
  apply (bases_of_singleton h).elim <;> intro h <;> simp only [h, card_empty, card_singleton]

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

theorem rank_of_feasible (hs : s ∈ G) : G.rank s = s.card := by
  sorry

theorem rank_of_infeasible (hs : s ∉ G) : G.rank s < s.card := by
  apply lt_of_le_of_ne rank_le_card
  intro h
  apply hs; clear hs
  simp only [rank, system_feasible_set_mem_mem] at h
  sorry

@[simp]
theorem rank_eq_card_iff_feasible : G.rank s = s.card ↔ s ∈ G := by
  apply Iff.intro _ (fun h => rank_of_feasible h)
  intro h
  have := mt (@rank_of_infeasible _ _ _ G s)
  simp only [not_lt, not_not] at this
  apply this
  simp only [h, le_refl]

theorem rank_insert_eq_append_basis (ht : t ∈ G.bases s) :
    G.rank (insert x t) = G.rank (insert x s) := by
  sorry

theorem local_submodularity
  (h₁ : G.rank s = G.rank (insert x s))
  (h₂ : G.rank s = G.rank (insert y s)) :
    G.rank (insert x (insert y s)) = G.rank s := by
  by_contra' h'
  have h₃ := Nat.lt_of_le_of_ne
    (rank_le_of_subset (Finset.Subset.trans (Finset.subset_insert y s) (Finset.subset_insert x _)))
    h'.symm
  have ⟨bs, hbs⟩ : Nonempty (G.bases s) := G.bases_nonempty
  have ⟨bt, hbt⟩ : Nonempty (G.bases (insert x (insert y s))) := G.bases_nonempty
  have hbs' := rank_eq_bases_card hbs
  have h : bs.card < bt.card := hbs' ▸ (rank_eq_bases_card hbt) ▸ h₃
  have ⟨z, hz₁, hz₂⟩ := G.exchangeProperty (basis_mem_feasible hbt) (basis_mem_feasible hbs) h
  simp only [mem_sdiff, system_feasible_set_mem_mem] at hz₁ hz₂
  have hzbr : G.rank (insert z bs) = G.rank s + 1 := by
    rw [rank_of_feasible hz₂]
    simp only [hz₁, card_insert_of_not_mem, hbs']
  have hzr : G.rank (insert z bs) = G.rank (insert z s) := rank_insert_eq_append_basis hbs
  have hzxy : z = x ∨ z = y := by
    sorry
  apply hzxy.elim <;> intro hzxy <;> simp_all only [mem_insert, ne_eq, add_right_eq_self, h₂]

theorem stronger_local_submodularity_left
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank s = G.rank (s ∪ t) := sorry

theorem stronger_local_submodularity_right
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank t = G.rank (s ∪ t) := by
  simp only [h₂, ← h₁, stronger_local_submodularity_left h₁ h₂]

-- TODO: Looking for better name
theorem rank_lt_succ_lt
  (hs₁ : G.rank s < G.rank (s ∪ {x}))
  (hs₂ : G.rank s < G.rank (s ∪ {y})) :
    G.rank s + 1 < G.rank (s ∪ {x, y}) := sorry

theorem ssubset_of_feasible_rank (hs : s ∈ G) (h : t ⊂ s) : G.rank t < G.rank s := sorry

/-- List of axioms for rank of greedoid. -/
def greedoidRankAxioms (r : Finset α → ℕ) :=
  (r ∅ = 0) ∧ (∀ s, r s ≤ s.card) ∧ (∀ s t, s ⊆ t → r s ≤ r t) ∧
  (∀ s x y, r s = r (s ∪ {x}) → r s = r (s ∪ {y}) → r s = r (s ∪ {x, y}))

theorem greedoidRankAxioms_unique_greedoid {r : Finset α → ℕ} (hr : greedoidRankAxioms r) :
    ∃! G : Greedoid α, G.rank = r := sorry

/-- Rank function satisfying `greedoidRankAxioms` generates a unique greedoid. -/
protected def rank.toGreedoid (r : Finset α → ℕ) (hr : greedoidRankAxioms r) : Greedoid α :=
  Fintype.choose (fun G => G.rank = r) (greedoidRankAxioms_unique_greedoid hr)

end rank

end Greedoid
