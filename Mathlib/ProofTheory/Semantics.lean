/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ProofTheory.LogicSymbol
import Mathlib.Data.Finset.Image

/-!
# Basic definitions and properties of semantics-related notions

This file defines the semantics of formulas based on Tarski's truth definitions. It also provides
a characterization of compactness.

## Main Definitions
* `Semantics`: The realization of a formula.
* `Compact`: The semantic compactness of logic.

This file defines similar concepts to `ModelTheory.Semantics`, but for Tait-style formulas.

## References

* <https://plato.stanford.edu/entries/tarski-truth/>

-/

namespace ProofTheory

variable {F : Type*} [LogicalConnective F]

/-- Class `Semantics` defines how a structure realizes a formula -/
class Semantics (F : Type*) [LogicalConnective F] (α : outParam (Type*)) where
  /-- Structure realizes a formula -/
  Realize : α → F →ˡᶜ Prop

namespace Semantics

variable {α : Type*} [𝓢 : Semantics F α]

/-- `RealizeTheory` specifices that a structure realizes a theory if it realizes each formula -/
def RealizeTheory (a : α) (T : Set F) : Prop := ∀ ⦃f⦄, f ∈ T → Realize a f

/-- Postfix notation for `Realize` -/
notation a:80 " ⊧ " f:25 => Semantics.Realize a f

/-- Infix notation for `RealizeTheory` -/
notation a:80 " ⊧* " T:25 => Semantics.RealizeTheory a T

/-- `Consequence` holds if xxx -/
def Consequence (T : Set F) (f : F) : Prop := ∀ ⦃a : α⦄, (a ⊧* T) → (a ⊧ f)

-- note that ⊨ (\vDash) is *NOT* ⊧ (\models)
/-- Infix notation for `consquence` -/
infix:55 " ⊨ " => Consequence

/-- Validity for a formula -/
def Valid (f : F) : Prop := ∀ ⦃a : α⦄, a ⊧ f

/-- Validity for a theory -/
def ValidTheory (T : Set F) : Prop := ∀ ⦃a : α⦄, a ⊧* T

/-- Satisfiability for a formula -/
def Satisfiable (f : F) : Prop := ∃ a : α, a ⊧ f

/-- Satisfiability for a theory -/
def SatisfiableTheory (T : Set F) : Prop := ∃ a : α, a ⊧* T

lemma valid_neg_iff (f : F) : Valid (~f) ↔ ¬Satisfiable f := by simp [Valid, Satisfiable]

lemma not_satisfiable_finset [DecidableEq F] (t : Finset F) :
    ¬SatisfiableTheory (t : Set F) ↔ Valid (t.image (~·)).disj :=
  by simp [SatisfiableTheory, RealizeTheory, Valid, Finset.map_disj]

lemma realizeTheory_of_subset {T U : Set F} {a : α} (h : a ⊧* U) (ss : T ⊆ U) : a ⊧* T :=
  fun _ hf ↦ h (ss hf)

@[simp] lemma realizeTheory_empty {a : α} : a ⊧* (∅ : Set F) := fun p ↦ by simp

@[simp] lemma realizeTheory_insert {T : Set F} {f : F} {a : α} :
    a ⊧* insert f T ↔ (a ⊧ f) ∧ (a ⊧* T) := by
  simp [RealizeTheory]

@[simp] lemma realizeTheory_union {T U : Set F} {a : α} :
    a ⊧* T ∪ U ↔ (a ⊧* T) ∧ (a ⊧* U) := by
  simp [RealizeTheory]
  exact ⟨fun h ↦ ⟨fun f hf ↦ h (Or.inl hf), fun f hf ↦ h (Or.inr hf)⟩,
    by rintro ⟨h₁, h₂⟩ f (h | h); exact h₁ h; exact h₂ h⟩

@[simp] lemma realizeTheory_image {ι} {f : ι → F} {A : Set ι} {a : α} :
    a ⊧* f '' A ↔ ∀ i ∈ A, a ⊧ (f i) := by simp [RealizeTheory]

@[simp] lemma realizeTheory_range {ι} {f : ι → F} {a : α} :
    a ⊧* Set.range f ↔ ∀ i, a ⊧ (f i) := by simp [RealizeTheory]

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
      have : SatisfiableTheory (insert (~f) T) := ⟨a, by simp [*]⟩
      contradiction⟩

lemma weakening {T U : Set F} {f} (h : T ⊨ f) (ss : T ⊆ U) : U ⊨ f :=
  fun _ hs ↦ h (realizeTheory_of_subset hs ss)

lemma of_mem {T : Set F} {f} (h : f ∈ T) : T ⊨ f := fun _ hs ↦ hs h

lemma consequence_iff {T : Set F} {f : F} : T ⊨ f ↔ ¬SatisfiableTheory (insert (~f) T) := by
  simp [Consequence, SatisfiableTheory]; constructor
  · intro h a hf hT; have : a ⊧ f := h hT; contradiction
  · intro h a; contrapose; exact h a

/-- A `theory` is a set of formulas realizing a structure -/
def theory (a : α) : Set F := {p | a ⊧ p}

/-- A `Subtheory` is a subset of realized formulas  -/
def Subtheory (T U : Set F) : Prop := ∀ {f}, T ⊨ f → U ⊨ f

/-- Definition for the equivalence of theories -/
def Equivalent (T U : Set F) : Prop := {f : F} → T ⊨ f ↔ U ⊨ f

namespace Subtheory

variable (T U T₁ T₂ T₃ : Set F)

@[refl] lemma refl : Subtheory T T := id

@[trans] protected lemma trans (h₁ : Subtheory T₁ T₂) (h₂ : Subtheory T₂ T₃) : Subtheory T₁ T₃ :=
  fun {f} b ↦ h₂ (h₁ b : T₂ ⊨ f)

lemma ofSubset (h : T ⊆ U) : Subtheory T U := fun b ↦ weakening b h

end Subtheory

lemma realizeTheory_of_subtheory {a : α} {T U : Set F} (h : a ⊧* U) (ss : Subtheory T U) :
    a ⊧* T := fun _ hf ↦ (ss (of_mem hf)) h

namespace Equivalent

variable (T U T₁ T₂ T₃ : Set F)

@[refl] protected lemma refl : Equivalent T T := ⟨id, id⟩

@[symm] protected lemma symm (h : Equivalent T U) : Equivalent U T := Iff.symm h

@[trans] protected lemma trans (h₁ : Equivalent T₁ T₂) (h₂ : Equivalent T₂ T₃) : Equivalent T₁ T₃ :=
  Iff.trans h₁ h₂

end Equivalent

/-- Class `Models` is a model for a theory -/
class Models (a : α) (T : Set F) : Prop where
  RealizeTheory : a ⊧* T

namespace Models

variable (a : α) {T : Set F} [Models a T]

lemma models {f : F} (hf : f ∈ T) : a ⊧ f := RealizeTheory hf

lemma iff : Models a T ↔ a ⊧* T := ⟨by rintro ⟨h⟩; exact h, fun h ↦ ⟨h⟩⟩

lemma of_subset {T₁ T₂ : Set F} [Models a T₁] (ss : T₂ ⊆ T₁) : Models a T₂ :=
  ⟨realizeTheory_of_subset RealizeTheory ss⟩

lemma of_subtheory {T₁ T₂ : Set F} [Models a T₁] (h : Subtheory T₂ T₁) : Models a T₂ :=
  ⟨realizeTheory_of_subtheory RealizeTheory h⟩

end Models

lemma consequence_iff' {T : Set F} {σ : F} :
    T ⊨ σ ↔ (∀ (a : α) [Models a T], a ⊧ σ) :=
  ⟨fun h _ hM ↦ h hM.RealizeTheory, fun H a hs ↦ @H a ⟨hs⟩⟩

end Semantics

variable (F)
variable {α : Type*} [Semantics F α]

/-- A theory is satisfiable iff it is finitely satisfiable -/
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
  simp [Semantics.consequence_iff, compact (T := insert (~f) T)]
  constructor
  · intro ⟨u, ss, hu⟩
    exact ⟨Finset.erase u (~f), by simp [ss],
      by simp; intro h; exact hu (Semantics.SatisfiableTheory.of_subset h (by simp))⟩
  · intro ⟨u, ss, hu⟩
    exact ⟨insert (~f) u,
      by simpa using Set.insert_subset_insert ss, by simpa using hu⟩

end Compact

end ProofTheory
