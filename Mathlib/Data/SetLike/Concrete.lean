/-
Copyright (c) 2021 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.SetNotation
public import Mathlib.Order.CompleteLattice.Defs

/-!
...
-/

@[expose] public section

-- assert_not_exists RelIso

/- # LE # -/

-- TODO: move `IsConcreteLE` here.

/- # Bot # -/

class IsConcreteBot (A : Type*) (B : outParam Type*) [SetLike A B] [Bot A] where
  protected coe_bot' : (⊥ : A) = (⊥ : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Bot A] [IsConcreteBot A B]

@[simp] lemma coe_bot : (⊥ : A) = (⊥ : Set B) := IsConcreteBot.coe_bot'

@[simp, grind =, push]
theorem mem_bot_iff_false {x : B} : x ∈ (⊥ : A) ↔ False := by simp [← mem_coe]

theorem eq_bot_iff_forall_notMem {a : A} : a = ⊥ ↔ ∀ x, x ∉ a := by
  simp [← coe_set_eq, ← mem_coe, Set.eq_empty_iff_forall_notMem]

theorem eq_bot_of_forall_notMem {a : A} (h : ∀ x, x ∉ a) : a = ⊥ :=
  eq_bot_iff_forall_notMem.mpr h

theorem forall_mem_bot {p : B → Prop} : (∀ x ∈ (⊥ : A), p x) ↔ True := by simp

section LE

variable [LE A] [IsConcreteLE A B]

instance : OrderBot A where
  bot_le := by simp [← coe_subset_coe]

end LE


/- # Empty # -/

end SetLike

class IsConcreteEmpty (A : Type*) (B : outParam Type*) [SetLike A B] [EmptyCollection A] where
  protected coe_empty' : (∅ : A) = (∅ : Set B)

namespace SetLike

variable {A B : Type*} [setLike : SetLike A B] [EmptyCollection A] [IsConcreteEmpty A B]

@[simp] lemma coe_empty : (∅ : A) = (∅ : Set B) := IsConcreteEmpty.coe_empty'

@[simp, grind =, push]
theorem mem_empty_iff_false {x : B} : x ∈ (∅ : A) ↔ False := by simp [← mem_coe]

theorem eq_empty_iff_forall_notMem {a : A} : a = ∅ ↔ ∀ x, x ∉ a := by
  simp [← coe_set_eq, ← mem_coe, Set.eq_empty_iff_forall_notMem]

theorem eq_empty_of_forall_notMem {a : A} (h : ∀ x, x ∉ a) : a = ∅ :=
  eq_empty_iff_forall_notMem.mpr h

theorem forall_mem_empty {p : B → Prop} : (∀ x ∈ (∅ : A), p x) ↔ True := by simp

section LE

variable [LE A] [IsConcreteLE A B]

include setLike in
@[simp] theorem empty_le (a : A) : ∅ ≤ a := by simp [← coe_subset_coe]

include setLike in
@[simp, grind =]
theorem le_empty_iff {a : A} : a ≤ ∅ ↔ a = ∅ := by simp [← coe_set_eq, ← coe_subset_coe]

include setLike in
theorem eq_empty_of_le_empty {a : A} : a ≤ ∅ → a = ∅ := le_empty_iff.1

include setLike in
theorem le_eq_empty {a b : A} (h : b ≤ a) (e : a = ∅) : b = ∅ := by
  rw [← coe_set_eq] at ⊢ e
  rw [← coe_subset_coe] at h
  rw [coe_empty] at ⊢ e
  exact Set.subset_eq_empty h e

end LE

-- TODO: theorems about SetLike.nonempty once implemented

end SetLike


/- # Top # -/

class IsConcreteTop (A : Type*) (B : outParam Type*) [SetLike A B] [Top A] where
  protected coe_top' : (⊤ : A) = (⊤ : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Top A] [IsConcreteTop A B]

@[simp] lemma coe_top : (⊤ : A) = (⊤ : Set B) := IsConcreteTop.coe_top'

section Bot

variable [Bot A] [IsConcreteBot A B]

theorem bot_ne_top [Nonempty B] : (⊥ : A) ≠ ⊤ := by
  simpa [← coe_set_eq] using Set.empty_ne_univ

end Bot

theorem eq_top_iff_forall {a : A} : a = ⊤ ↔ ∀ x, x ∈ a := by
  simpa [← coe_set_eq] using! Set.eq_univ_iff_forall

theorem eq_top_of_forall {a : A} : (∀ x, x ∈ a) → a = ⊤ := eq_top_iff_forall.2

variable (B) in
theorem exists_mem_top_of_nonempty : ∀ [Nonempty B], ∃ x : B, x ∈ (⊤ : A) := by
  simp_rw [← mem_coe, coe_top]
  exact Set.exists_mem_of_nonempty B

theorem ne_top_iff_exists_notMem (a : A) : a ≠ ⊤ ↔ ∃ x, x ∉ a := by
  rw [← not_forall, ← eq_top_iff_forall]

section LE

variable [LE A] [IsConcreteLE A B]

instance : OrderTop A where
  le_top := by simp [← coe_subset_coe]

end LE

end SetLike


/- # Univ # -/

class HasConcreteUniv (A : Type*) (B : outParam Type*) [SetLike A B] where
  protected univ' : A
  protected coe_univ' : (univ' : A) = (Set.univ : Set B)

namespace SetLike

variable {A B : Type*} [setLike : SetLike A B] [HasConcreteUniv A B]

def univ : A := HasConcreteUniv.univ'

@[simp] lemma coe_univ : (SetLike.univ : A) = (Set.univ : Set B) := HasConcreteUniv.coe_univ'

section Empty

variable [EmptyCollection A] [IsConcreteEmpty A B]

theorem empty_ne_univ [Nonempty B] : (∅ : A) ≠ univ := by
  simp only [ne_eq, ← coe_set_eq, coe_empty, coe_univ]
  exact Set.empty_ne_univ

end Empty

theorem eq_univ_iff_forall {a : A} : a = univ ↔ ∀ x, x ∈ a := by
  simp only [← coe_set_eq, coe_univ]
  exact Set.eq_univ_iff_forall

theorem eq_univ_of_forall {a : A} : (∀ x, x ∈ a) → a = univ := eq_univ_iff_forall.2

variable (B) in
theorem exists_mem_of_nonempty : ∀ [Nonempty B], ∃ x : B, x ∈ (univ : A) := by
  simp_rw [← mem_coe, coe_univ]
  exact Set.exists_mem_of_nonempty B

theorem ne_univ_iff_exists_notMem (a : A) : a ≠ univ ↔ ∃ x, x ∉ a := by
  rw [← not_forall, ← eq_univ_iff_forall]

section LE

variable [LE A] [IsConcreteLE A B]

theorem not_univ_le {a : A} : ¬univ ≤ a ↔ ∃ x, x ∉ a := by
  simp only [← coe_subset_coe, coe_univ]
  exact Set.not_univ_subset

@[simp, grind ←]
theorem le_univ (a : A) : a ≤ univ := by simp [← coe_subset_coe]

@[simp, grind =]
theorem univ_le_iff {a : A} : univ ≤ a ↔ a = univ := by
  simp [← coe_subset_coe, ← coe_set_eq]

theorem eq_univ_of_le {a b : A} (h : a ≤ b) (hs : a = univ) : b = univ := by
  rw [← coe_set_eq] at ⊢ hs
  rw [← coe_subset_coe] at h
  rw [coe_univ] at ⊢ hs
  exact Set.eq_univ_of_subset h hs

end LE

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B]

theorem lt_univ_iff {a : A} : a < univ ↔ a ≠ univ := by
  simp only [← coe_ssubset_coe, coe_univ, ne_eq, ← coe_set_eq]
  exact Set.ssubset_univ_iff

end PartialOrder

-- TODO: theorems about SetLike.Nonempty once impemented

end SetLike


/- # Insert # -/

class IsConcreteInsert (A : Type*) (B : outParam Type*) [SetLike A B] [Insert B A] where
  protected coe_insert' (x : B) (s : A) : (insert x s : A) = insert x (s : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Insert B A] [IsConcreteInsert A B]
variable {x y : B} {a b : A}

@[simp] lemma coe_insert (x : B) (s : A) : (insert x s : A) = insert x (s : Set B) :=
  IsConcreteInsert.coe_insert' x s

theorem mem_insert (x : B) (a : A) : x ∈ insert x a := by simp [← mem_coe]

theorem mem_insert_of_mem {x : B} {a : A} (y : B) : x ∈ a → x ∈ insert y a := by
  simpa [← mem_coe] using Set.mem_insert_of_mem y

theorem eq_or_mem_of_mem_insert {x y : B} {a : A} : x ∈ insert y a → x = y ∨ x ∈ a := by
  simp [← mem_coe]

theorem mem_of_mem_insert_of_ne {x y : B} {a : A} : y ∈ insert x a → y ≠ x → y ∈ a := by
  simpa [← mem_coe] using Set.mem_of_mem_insert_of_ne

theorem eq_of_mem_insert_of_notMem {x y : B} {a : A} : y ∈ insert x a → y ∉ a → y = x := by
  simpa [← mem_coe] using Set.eq_of_mem_insert_of_notMem

@[simp, grind =, push]
theorem mem_insert_iff {x y : B} {a : A} : x ∈ insert y a ↔ x = y ∨ x ∈ a := by simp [← mem_coe]

@[simp]
theorem insert_eq_of_mem {x : B} {a : A} (h : x ∈ a) : insert x a = a := by simp [← coe_set_eq, h]

theorem ne_insert_of_notMem {a : A} (b : A) {x : B} : x ∉ a → a ≠ insert x b := by grind

@[simp]
theorem insert_eq_self {x : B} {a : A} : insert x a = a ↔ x ∈ a := by simp [← coe_set_eq]

theorem insert_ne_self {x : B} {a : A} : insert x a ≠ a ↔ x ∉ a := by simp [← coe_set_eq]

theorem insert_comm (x y : B) (a : A) : insert x (insert y a) = insert y (insert x a) := by
  simpa [← coe_set_eq] using Set.insert_comm x y a

theorem insert_insert (x : B) (a : A) : insert x (insert x a) = insert x a := by simp

-- -- useful in proofs by induction
-- theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x)
--     (x) (h : x ∈ s) : P x := by grind

-- theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a)
--     (x) (h : x ∈ insert a s) : P x := by grind

-- theorem exists_mem_insert {P : α → Prop} {a : α} {s : Set α} :
--     (∃ x ∈ insert a s, P x) ↔ (P a ∨ ∃ x ∈ s, P x) := by grind

-- theorem forall_mem_insert {P : α → Prop} {a : α} {s : Set α} :
--     (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x := by grind

-- /-- Inserting an element to a set is equivalent to the option type. -/
-- def subtypeInsertEquivOption
--     [DecidableEq α] {t : Set α} {x : α} (h : x ∉ t) :
--     { i // i ∈ insert x t } ≃ Option { i // i ∈ t } where
--   toFun y := if h : ↑y = x then none else some ⟨y, by grind⟩
--   invFun y := (y.elim ⟨x, mem_insert _ _⟩) fun z => ⟨z, by grind⟩
--   left_inv y := by grind
--   right_inv := by rintro (_ | y) <;> grind

section LE

variable [LE A] [IsConcreteLE A B]

@[simp]
theorem le_insert (x : B) (a : A) : a ≤ insert x a := by simp [← coe_subset_coe]

theorem insert_le_iff {x : B} {a b : A} : insert x a ≤ b ↔ x ∈ b ∧ a ≤ b := by
  simpa [← coe_subset_coe] using! Set.insert_subset_iff

theorem insert_le {x : B} {a b : A} (hx : x ∈ b) (h : a ≤ b) : insert x a ≤ b := by
  rw [← coe_subset_coe] at ⊢ h
  rw [coe_insert]
  exact Set.insert_subset hx h

@[gcongr]
theorem insert_le_insert {x : B} {a b : A} (h : a ≤ b) : insert x a ≤ insert x b := by
  rw [← coe_subset_coe] at ⊢ h
  repeat rw [coe_insert]
  exact Set.insert_subset_insert h

@[simp] theorem insert_le_insert_iff (hxa : x ∉ a) : insert x a ≤ insert x b ↔ a ≤ b := by
  simpa [← coe_subset_coe] using Set.insert_subset_insert_iff hxa

theorem le_insert_iff_of_notMem (hxa : x ∉ a) : a ≤ insert x b ↔ a ≤ b := by
  simpa [← coe_subset_coe] using Set.subset_insert_iff_of_notMem hxa

end LE

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B]

theorem lt_iff_insert : a < b ↔ ∃ x ∉ a, insert x a ≤ b := by
  simpa [← coe_ssubset_coe, ← coe_subset_coe] using! Set.ssubset_iff_insert

theorem lt_insert (h : x ∉ a) : a < insert x a := by
  simpa [← coe_ssubset_coe] using Set.ssubset_insert h

end PartialOrder

-- TODO: lemmas involving sup/inf

end SetLike


/- # Singleton # -/

class IsConcreteSingleton (A : Type*) (B : outParam Type*) [SetLike A B] [Singleton B A] where
  protected coe_singleton' (x : B) : ({x} : A) = ({x} : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Singleton B A] [IsConcreteSingleton A B]
variable {x y : B} {a b : A}

@[simp] lemma coe_singleton (x : B) : ({x} : A) = ({x} : Set B) :=
  IsConcreteSingleton.coe_singleton' x

@[simp, grind =, push]
theorem mem_singleton_iff : x ∈ ({y} : A) ↔ x = y := by simp [← mem_coe]

theorem notMem_singleton_iff : x ∉ ({y} : A) ↔ x ≠ y := by simp [← mem_coe]

-- theorem mem_singleton (a : α) : a ∈ ({a} : Set α) :=
--   @rfl _ _

-- theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
--   h

-- @[simp]
-- theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
--   Set.ext_iff.trans eq_iff_eq_cancel_left

-- theorem singleton_injective : Injective (singleton : α → Set α) := fun _ _ =>
--   singleton_eq_singleton_iff.mp

-- theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : Set α) :=
--   H

-- @[simp]
-- theorem singleton_ne_empty (a : α) : ({a} : Set α) ≠ ∅ :=
--   (singleton_nonempty _).ne_empty

-- @[simp]
-- theorem empty_ne_singleton (a : α) : ∅ ≠ ({a} : Set α) :=
--   (singleton_ne_empty a).symm

-- theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
--   (singleton_nonempty _).empty_ssubset

-- @[simp, grind =]
-- theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
--   forall_eq

-- @[gcongr]
-- theorem singleton_subset_singleton : ({a} : Set α) ⊆ {b} ↔ a = b := by simp

section LawfulSingleton

variable [EmptyCollection A] [IsConcreteEmpty A B] [Insert B A] [IsConcreteInsert A B]

instance : LawfulSingleton B A where
  insert_empty_eq := by simp [← coe_set_eq]

theorem singleton_def (x : B) : ({x} : A) = insert x ∅ := by simp

-- theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
--   union_self _

-- theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
--   union_comm _ _

-- theorem pair_eq_pair_iff {x y z w : α} :
--     ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
--   simp [subset_antisymm_iff, insert_subset_iff]; aesop

-- theorem pair_subset_iff : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by grind

-- theorem pair_subset (ha : a ∈ s) (hb : b ∈ s) : {a, b} ⊆ s :=
--   pair_subset_iff.2 ⟨ha,hb⟩

-- theorem subset_pair_iff : s ⊆ {a, b} ↔ ∀ x ∈ s, x = a ∨ x = b := by grind

-- theorem subset_pair_iff_eq {x y : α} : s ⊆ {x, y} ↔ s = ∅ ∨ s = {x} ∨ s = {y} ∨ s = {x, y} where
--   mp := by grind
--   mpr := by grind

end LawfulSingleton

section Univ

variable [HasConcreteUniv A B]

theorem univ_unique [Unique B] : (univ : A) = {default} := by
  simpa [← coe_set_eq] using Set.univ_unique

end Univ

-- TODO: add theorems

end SetLike


/- # Compl # -/

class IsConcreteCompl (A : Type*) (B : outParam Type*) [SetLike A B] [Compl A] where
  protected coe_compl' (a : A) : (aᶜ : A) = (aᶜ : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Compl A] [IsConcreteCompl A B]

@[simp] lemma coe_compl (a : A) : (aᶜ : A) = (aᶜ : Set B) := IsConcreteCompl.coe_compl' a

-- TODO: add theorems

end SetLike


/- # Min # -/

class IsConcreteMin (A : Type*) (B : outParam Type*) [SetLike A B] [Min A] where
  protected coe_min' (a b : A) : (a ⊓ b : A) = (a ∩ b : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Min A] [IsConcreteMin A B]

@[simp] lemma coe_min (a b : A) : (a ⊓ b : A) = (a ∩ b : Set B) := IsConcreteMin.coe_min' a b

alias coe_inf := coe_min

@[simp] lemma mem_min (a b : A) (x : B) : x ∈ a ⊓ b ↔ x ∈ a ∧ x ∈ b := by
  simp [← mem_coe]

alias mem_inf := mem_min

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B]

variable (A B) in
@[reducible] def _root_.SemilatticeInf.ofSetLike : SemilatticeInf A where
  inf := min
  inf_le_left := by simp [← coe_subset_coe]
  inf_le_right := by simp [← coe_subset_coe]
  le_inf a b c := by simpa only [← coe_subset_coe, coe_min] using! le_inf

end PartialOrder

-- TODO: add theorems

end SetLike


/- # sInf # -/

class IsConcreteInfSet (A : Type*) (B : outParam Type*) [SetLike A B] [InfSet A] where
  protected coe_sInf' (s : Set A) : sInf s = ⋂₀ (SetLike.coe '' s)

namespace SetLike

variable {A B : Type*} [setlike : SetLike A B] [InfSet A] [IsConcreteInfSet A B]

@[simp] lemma coe_sInf (s : Set A) : sInf s = ⋂₀ (SetLike.coe '' s) :=
  IsConcreteInfSet.coe_sInf' s

@[simp] lemma mem_sInf (s : Set A) (x : B) : x ∈ sInf s ↔ ∀ a ∈ s, x ∈ a := by
  simp [← mem_coe]

@[simp] lemma mem_iInf (s : Set A) (x : B) : x ∈ ⨅ a ∈ s, a ↔ ∀ a ∈ s, x ∈ a := by
  simp [iInf]

@[simp] lemma coe_iInf (s : Set A) : ⨅ a ∈ s, a = ⋂ a ∈ s, (a : Set B) := by
  ext x; simp

include setlike in
lemma sInf_eq_iInf (s : Set A) : sInf s = ⨅ a ∈ s, a := by
  simp [← SetLike.coe_set_eq]

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B]

variable (A B) in
@[reducible] def _root_.CompleteSemilatticeInf.ofSetLike : CompleteSemilatticeInf A where
  isGLB_sInf := by simp [isGLB_iff_le_iff, ← SetLike.coe_subset_coe, lowerBounds]

end PartialOrder

-- TODO: add theorems

end SetLike


/- # Max # -/

class IsConcreteMax (A : Type*) (B : outParam Type*) [SetLike A B] [Max A] where
  protected coe_max' (a b : A) : (a ⊔ b : A) = (a ∪ b : Set B)

namespace SetLike

variable {A B : Type*} [SetLike A B] [Max A] [IsConcreteMax A B]

@[simp] lemma coe_max (a b : A) : (a ⊔ b : A) = (a ∪ b : Set B) := IsConcreteMax.coe_max' a b

alias coe_sup := coe_max

@[simp] lemma mem_max (a b : A) (x : B) : x ∈ a ⊔ b ↔ x ∈ a ∨ x ∈ b := by
  simp [← mem_coe]

alias mem_sup := mem_max

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B]

variable (A B) in
@[reducible] def _root_.SemilatticeSup.ofSetLike : SemilatticeSup A where
  sup := max
  le_sup_left := by simp [← coe_subset_coe]
  le_sup_right := by simp [← coe_subset_coe]
  sup_le a b c := by simpa only [← coe_subset_coe, coe_max] using! sup_le

end PartialOrder

-- TODO: add theorems

end SetLike


/- # sSup # -/

class IsConcreteSupSet (A : Type*) (B : outParam Type*) [SetLike A B] [SupSet A] where
  protected coe_sSup' (s : Set A) : sSup s = ⋃₀ (SetLike.coe '' s)

namespace SetLike

variable {A B : Type*} [setlike : SetLike A B] [SupSet A] [IsConcreteSupSet A B]

@[simp] lemma coe_sSup (s : Set A) : sSup s = ⋃₀ (SetLike.coe '' s) :=
  IsConcreteSupSet.coe_sSup' s

@[simp] lemma mem_sSup (s : Set A) (x : B) : x ∈ sSup s ↔ ∃ a ∈ s, x ∈ a := by
  simp [← mem_coe]

@[simp] lemma mem_iSup (s : Set A) (x : B) : x ∈ ⨆ a ∈ s, a ↔ ∃ a ∈ s, x ∈ a := by
  simp [iSup]

@[simp] lemma coe_iSup (s : Set A) : ⨆ a ∈ s, a = ⋃ a ∈ s, (a : Set B) := by
  ext x; simp

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B]

variable (A B) in
@[reducible] def _root_.CompleteSemilatticeSup.ofSetLike : CompleteSemilatticeSup A where
  isLUB_sSup := by simp [isLUB_iff_le_iff, ← SetLike.coe_subset_coe, upperBounds]

end PartialOrder

-- TODO: add theorems

end SetLike
