/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ProofTheory.LogicSymbol
import Mathlib.Data.Finset.Image

/-!
# Basic definitions and properties of semantics-related notions

This file defines the semantics of formulas based on Tarski's truth definitions.
Also provides a characterization of compactness.

## Main Definitions
* `Semantics`: The realization of a formula.
* `Compact`: The semantic compactness of logic.

-/

namespace ProofTheory

variable {F : Type*} [LogicalConnective F]

class Semantics (F : Type*) [LogicalConnective F] (α : outParam (Type*)) where
  realize : α → F →ˡᶜ Prop

class Vocabulary (F : Type*) [LogicalConnective F] (V : outParam (Type*)) where
  voc    : F → Set V
  verum  : voc ⊤ = ∅
  falsum : voc ⊥ = ∅
  neg    : (f : F) → voc (~f) = voc f
  and    : (f g : F) → voc (f ⋏ g) = voc f ∪ voc g
  or     : (f g : F) → voc (f ⋎ g) = voc f ∪ voc g
  imp    : (f g : F) → voc (f ⭢ g) = voc f ∪ voc g

namespace Semantics
variable {α : Type*} [𝓢 : Semantics F α]

def realizeTheory (a : α) (T : Set F) : Prop := ∀ ⦃f⦄, f ∈ T → realize a f

postfix:max " ⊧ " => realize

infix:60 " ⊧* " => realizeTheory

def consequence (T : Set F) (f : F) : Prop := ∀ ⦃a : α⦄, a ⊧* T → a ⊧ f

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
infix:55 " ⊨ " => consequence

def Valid (f : F) : Prop := ∀ ⦃a : α⦄, a ⊧ f

def ValidTheory (T : Set F) : Prop := ∀ ⦃a : α⦄, a ⊧* T

def Satisfiable (f : F) : Prop := ∃ a : α, a ⊧ f

def SatisfiableTheory (T : Set F) : Prop := ∃ a : α, a ⊧* T

lemma valid_neg_iff (f : F) : Valid (~f) ↔ ¬Satisfiable f := by simp[Valid, Satisfiable]

lemma not_satisfiable_finset [DecidableEq F] (t : Finset F) :
    ¬SatisfiableTheory (t : Set F) ↔ Valid (t.image (~·)).disj :=
  by simp[SatisfiableTheory, realizeTheory, Valid, Finset.map_disj]

lemma realizeTheory_of_subset {T U : Set F} {a : α} (h : a ⊧* U) (ss : T ⊆ U) : a ⊧* T :=
  fun _ hf => h (ss hf)

@[simp] lemma realizeTheoryEmpty {a : α} : a ⊧* (∅ : Set F) := fun p => by simp

@[simp] lemma realizeTheory_insert {T : Set F} {f : F} {a : α} :
    a ⊧* insert f T ↔ a ⊧ f ∧ a ⊧* T := by
  simp[realizeTheory]

@[simp] lemma realizeTheory_union {T U : Set F} {a : α} :
    a ⊧* T ∪ U ↔ a ⊧* T ∧ a ⊧* U := by
  simp[realizeTheory]
  exact
  ⟨fun h => ⟨fun f hf => h (Or.inl hf), fun f hf => h (Or.inr hf)⟩,
   by rintro ⟨h₁, h₂⟩ f (h | h); exact h₁ h; exact h₂ h⟩

@[simp] lemma realizeTheory_image {ι} {f : ι → F} {A : Set ι} {a : α} :
    a ⊧* f '' A ↔ ∀ i ∈ A, a ⊧ (f i) := by simp[realizeTheory]

@[simp] lemma realizeTheory_range {ι} {f : ι → F} {a : α} :
    a ⊧* Set.range f ↔ ∀ i, a ⊧ (f i) := by simp[realizeTheory]

@[simp] lemma realizeTheory_setOf {P : F → Prop} {a : α}:
    a ⊧* setOf P ↔ ∀ f, P f → a ⊧ f := by rfl

lemma SatisfiableTheory.of_subset {T U : Set F} (h : SatisfiableTheory U) (ss : T ⊆ U) :
    SatisfiableTheory T :=
  by rcases h with ⟨a, h⟩; exact ⟨a, realizeTheory_of_subset h ss⟩

lemma consequence_iff_not_satisfiable {f : F} {T : Set F} :
    T ⊨ f ↔ ¬SatisfiableTheory (insert (~f) T) :=
  ⟨by rintro hT ⟨a, ha⟩
      have : a ⊧ f := hT (realizeTheory_of_subset ha (Set.subset_insert (~f) T))
      have : ¬a ⊧ f := by simpa using ha (Set.mem_insert (~f) T)
      contradiction,
   by intro h a ha; by_contra hn
      have : SatisfiableTheory (insert (~f) T) := ⟨a, by simp[*]⟩
      contradiction⟩

lemma weakening {T U : Set F} {f} (h : T ⊨ f) (ss : T ⊆ U) : U ⊨ f :=
  fun _ hs => h (realizeTheory_of_subset hs ss)

lemma of_mem {T : Set F} {f} (h : f ∈ T) : T ⊨ f := fun _ hs => hs h

lemma consequence_iff {T : Set F} {f : F} : T ⊨ f ↔ ¬SatisfiableTheory (insert (~f) T) := by
  simp[consequence, SatisfiableTheory]; constructor
  · intro h a hf hT; have : a ⊧ f := h hT; contradiction
  · intro h a; contrapose; exact h a

def theory (a : α) : Set F := {p | a ⊧ p}

def Subtheory (T U : Set F) : Prop := ∀ {f}, T ⊨ f → U ⊨ f

def Equivalent (T U : Set F) : Prop := {f : F} → T ⊨ f ↔ U ⊨ f

namespace Subtheory

variable (T U T₁ T₂ T₃ : Set F)

@[refl] lemma refl : Subtheory T T := id

@[trans] protected lemma trans (h₁ : Subtheory T₁ T₂) (h₂ : Subtheory T₂ T₃) : Subtheory T₁ T₃ :=
  fun {f} b => h₂ (h₁ b : T₂ ⊨ f)

def ofSubset (h : T ⊆ U) : Subtheory T U := fun b => weakening b h

end Subtheory

lemma realizeTheory_of_subtheory {a : α} {T U : Set F} (h : a ⊧* U) (ss : Subtheory T U) :
    a ⊧* T := fun _ hf => (ss (of_mem hf)) h

namespace Equivalent

variable (T U T₁ T₂ T₃ : Set F)

@[refl] protected lemma refl : Equivalent T T := ⟨id, id⟩

@[symm] protected lemma symm (h : Equivalent T U) : Equivalent U T := Iff.symm h

@[trans] protected lemma trans (h₁ : Equivalent T₁ T₂) (h₂ : Equivalent T₂ T₃) : Equivalent T₁ T₃ :=
  Iff.trans h₁ h₂

end Equivalent

class Mod (a : α) (T : Set F) : Prop where
  realizeTheory : a ⊧* T

namespace Mod

variable (a : α) {T : Set F} [Mod a T]

lemma models {f : F} (hf : f ∈ T) : a ⊧ f := realizeTheory hf

lemma iff : Mod a T ↔ a ⊧* T := ⟨by rintro ⟨h⟩; exact h, fun h ↦ ⟨h⟩⟩

def of_ss {T₁ T₂ : Set F} [Mod a T₁] (ss : T₂ ⊆ T₁) : Mod a T₂ :=
  ⟨realizeTheory_of_subset realizeTheory ss⟩

def of_subtheory {T₁ T₂ : Set F} [Mod a T₁] (h : Subtheory T₂ T₁) : Mod a T₂ :=
  ⟨realizeTheory_of_subtheory realizeTheory h⟩

end Mod

lemma consequence_iff' {T : Set F} {σ : F} :
    T ⊨ σ ↔ (∀ (a : α) [Mod a T], a ⊧ σ) :=
  ⟨fun h _ hM => h hM.realizeTheory, fun H a hs => @H a ⟨hs⟩⟩

end Semantics

def Cumulative (T : ℕ → Set F) : Prop := ∀ s, T s ⊆ T (s + 1)

namespace Cumulative

lemma subset_of_le {T : ℕ → Set F} (H : Cumulative T)
    {s₁ s₂ : ℕ} (h : s₁ ≤ s₂) : T s₁ ⊆ T s₂ := by
  suffices : ∀ s d, T s ⊆ T (s + d)
  · simpa[Nat.add_sub_of_le h] using this s₁ (s₂ - s₁)
  intro s d
  induction' d with d ih
  · simp; rfl
  · simpa[Nat.add_succ] using subset_trans ih (H (s + d))

lemma finset_mem {T : ℕ → Set F}
    (H : Cumulative T) {u : Finset F} (hu : ↑u ⊆ ⋃ s, T s) : ∃ s, ↑u ⊆ T s := by
  haveI := Classical.decEq
  induction u using Finset.induction
  case empty => exact ⟨0, by simp⟩
  case insert f u _ ih =>
    simp at hu
    have : ∃ s, ↑u ⊆ T s := ih (subset_trans (Set.subset_insert _ _) hu)
    rcases this with ⟨s, hs⟩
    have : ∃ s', f ∈ T s' := by simpa using (Set.insert_subset_iff.mp hu).1
    rcases this with ⟨s', hs'⟩
    exact ⟨max s s', by
      simp; exact Set.insert_subset
        (subset_of_le H (Nat.le_max_right s s') hs')
        (subset_trans hs (subset_of_le H $ Nat.le_max_left s s'))⟩

end Cumulative

variable (F)
variable {α : Type*} [Semantics F α]

class Compact : Prop where
  compact {T : Set F} :
    Semantics.SatisfiableTheory T ↔ (∀ u : Finset F, ↑u ⊆ T → Semantics.SatisfiableTheory
    (u : Set F))

variable {F}

namespace Compact

variable [Compact F]
variable {a : α}

lemma conseq_compact [DecidableEq F] {f : F} {T : Set F}:
    T ⊨ f ↔ ∃ u : Finset F, ↑u ⊆ T ∧ u ⊨ f := by
  simp[Semantics.consequence_iff, compact (T := insert (~f) T)]
  constructor
  · intro ⟨u, ss, hu⟩
    exact ⟨Finset.erase u (~f), by simp[ss],
      by simp; intro h; exact hu (Semantics.SatisfiableTheory.of_subset h (by simp))⟩
  · intro ⟨u, ss, hu⟩
    exact ⟨insert (~f) u,
      by simpa using Set.insert_subset_insert ss, by simpa using hu⟩

lemma compact_cumulative {T : ℕ → Set F} (hT : Cumulative T) :
    Semantics.SatisfiableTheory (⋃ s, T s) ↔ ∀ s, Semantics.SatisfiableTheory (T s) :=
  ⟨by intro H s
      exact H.of_subset (Set.subset_iUnion T s),
   by intro H
      apply compact.mpr
      intro u hu
      rcases hT.finset_mem hu with ⟨s, hs⟩
      exact (H s).of_subset hs ⟩

end Compact

end ProofTheory
