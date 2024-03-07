/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ProofTheory.Semantics

/-!
# Basic definitions and properties of proof-related notions

This file defines a characterization of the proof/provability/calculus of formulas.
It also defines soundness and completeness.

## Main Definitions
* `Proof`: Proof system of logic.
* `Sound`: Soundness of the proof system.
* `Complete`: Completeness of the proof system.

-/

namespace ProofTheory

universe u

variable {F : Type*} [LogicalConnective F]

/-- Deduction Proof -/
class Proof (F : Type*) where
  /-- Proof of formula by a theory (a set of formulas) -/
  Prf : Set F → F → Type u
  /-- A formula is in a theory if proved by it -/
  axm : ∀ {f T}, f ∈ T → Prf T f
  /-- A theory is a weakening of another theory if it proves a subset of its formulas -/
  weakening' : ∀ {T U f}, T ⊆ U → Prf T f → Prf U f

namespace Proof

variable [𝓑 : Proof F]

instance : Turnstile F (Type u) := ⟨𝓑.Prf⟩

/-- `Provable` abbreviates that theory `T` proves formula `f` -/
abbrev Provable (T : Set F) (f : F) : Prop := Nonempty (T ⊢ f)

/-- Infix notation for `Proof.Provable` -/
infix:45 " ⊢! " => Proof.Provable

/-- `toProof` noncomputably yields a proof of any formula that is provable -/
noncomputable def Provable.toProof {T : Set F} {f : F} (h : T ⊢! f) : T ⊢ f := Classical.choice h

/-- `Unprovable` abbreviates that theory `T` does not prove formula `f` -/
abbrev Unprovable (T : Set F) (f : F) : Prop := IsEmpty (T ⊢ f)

/-- Infix notation for `Proof.Unprovable` -/
infix:45 " ⊬ " => Proof.Unprovable

/-- Theory `T` proves the set of formulas in `U` -/
def PrfTheory (T U : Set F) : Type _ := {f : F} → f ∈ U → T ⊢ f

/-- Infix notation for `Proof.PrfTheory` -/
infix:45 " ⊢* " => Proof.PrfTheory

/-- Set of formulas `U` has a `ProvableTheory` `T` -/
def ProvableTheory (T U : Set F) : Prop := Nonempty (T ⊢* U)

/-- Infix notation for `Proof.ProvableTheory` -/
infix:45 " ⊢*! " => Proof.ProvableTheory

lemma unprovable_iff_not_provable {T : Set F} {f : F} : T ⊬ f ↔ ¬T ⊢! f := by
  simp[Proof.Unprovable]

/-- A set of formulas `T` has no `ProvableTheory` if every formula is provable -/
def PrfTheoryEmpty (T : Set F) : T ⊢* ∅ := fun h => by contradiction

/-- Theory `U` is a subset of theory `T` -/
def PrfTheory.ofSubset {T U : Set F} (h : U ⊆ T) : T ⊢* U := fun hf => axm (h hf)

/-- A theory is `ProvableTheory` for itself -/
def PrfTheory.refl (T : Set F) : T ⊢* T := axm

/-- A theory is `Consistent` if it has not proof of contradiction -/
def Consistent (T : Set F) : Prop := IsEmpty (T ⊢ ⊥)

/-- Theory `T` is a `weakening` of theory `U` -/
def weakening {T U : Set F} {f : F} (b : T ⊢ f) (ss : T ⊆ U) : U ⊢ f := weakening' ss b

lemma Consistent.of_subset {T U : Set F} (h : Consistent U) (ss : T ⊆ U) : Consistent T :=
  ⟨fun b => h.false (weakening b ss)⟩

lemma inconsistent_of_proof {T : Set F} (b : T ⊢ ⊥) : ¬Consistent T := by
  simp[Consistent]; exact ⟨b⟩

lemma inconsistent_of_provable {T : Set F} (b : T ⊢! ⊥) : ¬Consistent T := by simp[Consistent]

lemma consistent_iff_unprovable {T : Set F} : Consistent T ↔ T ⊬ ⊥ := by rfl

/-- A proof system is complete -/
protected def Complete (T : Set F) : Prop := ∀ f, (T ⊢! f) ∨ (T ⊢! ~f)

/-- A formula is `Independent` of a theory if it does not prove the formula or its negation -/
def Independent (T : Set F) (f : F) : Prop := T ⊬ f ∧ T ⊬ ~f

lemma incomplete_iff_exists_independent {T : Set F} :
    ¬Proof.Complete T ↔ ∃ f, Independent T f := by simp[Proof.Complete, not_or, Independent]

/-- A `theory` is a set of formulas which are `Provable` -/
def theory (T : Set F) : Set F := {p | T ⊢! p}

@[simp] lemma subset_theory {T : Set F} : T ⊆ theory T := fun _ h ↦ ⟨Proof.axm h⟩

/-- A proof in `T` is noncomputably obtained for any formula in `T` -/
noncomputable def provableTheory_theory {T : Set F} : T ⊢* theory T := λ b ↦ b.toProof

/-- A `Subtheory` proves a subset of formulas -/
class Subtheory (T U : Set F) where
  /-- If `T` proves `f`, `U` proves `f` -/
  sub : {f : F} → T ⊢ f → U ⊢ f

/-- Infix notation for `Subtheory` -/
infix:50 " ≾ " => Subtheory

/-- Definition of equivalent theories -/
class Equivalent (T U : Set F) where
  /-- If `T` proves `f`, `U` proves `f` -/
  ofLeft : {f : F} → T ⊢ f → U ⊢ f
  /-- If `U` proves `f`, `T` proves `f` -/
  ofRight : {f : F} → U ⊢ f → T ⊢ f

namespace Subtheory

variable (T U T₁ T₂ T₃ : Set F)

@[refl] instance : T ≾ T := ⟨id⟩

/-- `Subtheory` is transitive -/
@[trans] protected def trans [T₁ ≾ T₂] [T₂ ≾ T₃] : T₁ ≾ T₃ :=
  ⟨fun {f} b => sub (sub b : T₂ ⊢ f)⟩

variable {T U}

/-- `ofSubset` holds for a `Subtheory` that is a weakening -/
def ofSubset (h : T ⊆ U) : T ≾ U := ⟨fun b => weakening b h⟩

/-- A `prfTheory` is a subset of axioms -/
def prfTheory [T ≾ U] : U ⊢* T := λ hp ↦ sub (axm hp)

end Subtheory

namespace Equivalent

variable (T U T₁ T₂ T₃ : Set F)

@[refl] instance : Equivalent T T := ⟨id, id⟩

@[symm] instance [Equivalent T U] : Equivalent U T := ⟨ofRight, ofLeft⟩

/-- `Equivalent` is transitive for theories -/
@[trans] protected def trans [Equivalent T₁ T₂] [Equivalent T₂ T₃] : Equivalent T₁ T₃ :=
  ⟨fun {f} b => ofLeft (ofLeft b : T₂ ⊢ f), fun {f} b => ofRight (ofRight b : T₂ ⊢ f)⟩

end Equivalent

end Proof

/-- A `Proof.hom` is a homomorphism preserving logical connectives-/
def Proof.hom [Proof F] {G : Type u} [LogicalConnective G] (F : G →ˡᶜ F) : Proof G where
  Prf := fun T g => F '' T ⊢ F g
  axm := fun h => Proof.axm (Set.mem_image_of_mem F h)
  weakening' := fun h => by simp; exact Proof.weakening' (Set.image_subset F h)

variable (F)
variable [LogicalConnective F] [𝓑 : Proof F] {α: Type*} [𝓢 : Semantics F α]

/-- `Sound` class definition -/
class Sound where
  sound : ∀ {T : Set F} {p : F}, T ⊢ p → T ⊨ p

/-- `SoundOn` class definition for a group of formulas -/
class SoundOn (M : Type*) (a : α) (H : Set F) where
  sound : ∀ {T : Set F} {p : F}, p ∈ H → T ⊢ p → a ⊧ p

/-- `Complete` class is sound and proves any true formula -/
class Complete extends Sound F where
  /-- `T` proves any true formula -/
  complete : ∀ {T : Set F} {p : F}, T ⊨ p → T ⊢ p

variable {F}

namespace Sound

variable [Sound F]
variable {a : α}

lemma sound! {T : Set F} {f : F} : T ⊢! f → T ⊨ f := by rintro ⟨b⟩; exact sound b

lemma not_provable_of_countermodel {T : Set F} {p : F}
    (hT : a ⊧* T) (hp : ¬a ⊧ p) : IsEmpty (T ⊢ p) :=
  ⟨fun b => by have : a ⊧ p := Sound.sound b hT; contradiction⟩

lemma consistent_of_model {T : Set F} (hT : a ⊧* T) : Proof.Consistent T :=
  not_provable_of_countermodel (p := ⊥) hT (by simp [Prop.bot_eq_false])

lemma consistent_of_satisfiable {T : Set F} :
    Semantics.SatisfiableTheory T → Proof.Consistent T := by
  rintro ⟨_, h⟩; exact consistent_of_model h

lemma models_of_proof {T : Set F} {f} (h : a ⊧* T) (b : T ⊢ f) : a ⊧ f :=
  Sound.sound b h

lemma modelsTheory_of_proofTheory {s} {T U : Set F} (h : s ⊧* T) (b : T ⊢* U) : s ⊧* U :=
  fun _ hf => models_of_proof h (b hf)

lemma modelsTheory_of_subtheory {s} {T U : Set F} [U ≾ T] (h : s ⊧* T) : s ⊧* U :=
  modelsTheory_of_proofTheory h Proof.Subtheory.prfTheory

end Sound

namespace Complete

/-- `of!` yields a proof of any formula in a `Complete` theory `T`-/
noncomputable def of! [Sound F] (H : ∀ {T : Set F} {p : F}, T ⊨ p → T ⊢! p) : Complete F where
  complete := fun h ↦ (H h).toProof

variable [Complete F]

lemma satisfiableTheory_iff_consistent {T : Set F} :
    Semantics.SatisfiableTheory T ↔ Proof.Consistent T :=
  ⟨Sound.consistent_of_satisfiable,
   by contrapose; intro h
      have : T ⊨ ⊥ := by intro a hM; have : Semantics.SatisfiableTheory T := ⟨a, hM⟩; contradiction
      have : T ⊢ ⊥ := complete this
      exact Proof.inconsistent_of_proof this⟩

lemma not_satisfiable_iff_inconsistent {T : Set F} : ¬Semantics.SatisfiableTheory T ↔ T ⊢! ⊥ := by
  simp[satisfiableTheory_iff_consistent, Proof.Consistent]

lemma consequence_iff_provable {T : Set F} {f : F} : T ⊨ f ↔ T ⊢! f :=
⟨fun h => ⟨complete h⟩, by rintro ⟨b⟩; exact Sound.sound b⟩

alias ⟨complete!, _⟩ := consequence_iff_provable

end Complete

namespace Proof

variable [ProofTheory.Complete F]

/-- A semantic `Subtheory` is a proof `Subtheory` -/
def ofSemanticsSubtheory {T U : Set F} (h : Semantics.Subtheory T U) : Proof.Subtheory T U :=
  ⟨fun hf => Complete.complete (h (Sound.sound hf))⟩

end Proof

namespace Semantics

variable [ProofTheory.Complete F]

lemma ofProofSubtheory (T₁ T₂ : Set F) [Proof.Subtheory T₁ T₂] : Semantics.Subtheory T₁ T₂ :=
  fun hf => (Sound.sound $ Proof.Subtheory.sub $ Complete.complete hf)

end Semantics

end ProofTheory
