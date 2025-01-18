/-
Copyright (c) 2025 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Set.Lattice

/-!
# Typeclass for lattices with a closure-adjoint embedding into a power set.

This file defines a typeclass for lattices `L` that embed nicely into a power set `Set α`,
in the sense that the closure operation `Set α → L` is adjoint to the embedding. The main purpose
of this class is to abstract the closure construction common to most algebraic substructures.

## Main definitions

* `LatticeSetLike` : class for complete lattices that have an embedding into some `Set α`
  which preserves arbitrary infima.
* `LatticeSetLike.closure` : the natural closure operation on `Set α` with respect to a
  `LatticeSetLike` embedding; that is, the map from a set to the least lattice element that
  contains it.

## Main result

* `LatticeSetLike.gi_closure` : for a `LatticeSetLike`, the operations
  `LatticeSetLike.closure` and `SetLike.coe` (the embedding) form a Galois insertion.

-/

class IsConcreteSInf (A B : Type*) [SetLike A B] [InfSet A] where
  coe_sInf' {s : Set A} : ((sInf s : A) : Set B) = ⋂ a ∈ s, ↑a

namespace IsConcreteSInf

variable {A B : Type*} [SetLike A B] [InfSet A] [IsConcreteSInf A B]

@[simp, norm_cast]
theorem coe_sInf {s : Set A} : ((sInf s : A) : Set B) = ⋂ a ∈ s, a := IsConcreteSInf.coe_sInf'

theorem mem_sInf {s : Set A} {x : B} : x ∈ sInf s ↔ ∀ a ∈ s, x ∈ a := by
  rw [← SetLike.mem_coe]; simp

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} {a : ι → A} : (↑(⨅ i, a i) : Set B) = ⋂ i, a i := by simp [iInf]

theorem mem_iInf {ι : Sort*} {a : ι → A} {x : B} : (x ∈ ⨅ i, a i) ↔ ∀ i, x ∈ a i := by
  rw [← SetLike.mem_coe]; simp

end IsConcreteSInf

class HasClosure (A B : Type*) where
  closure : Set B → A

class IsConcreteClosure (A B : Type*) [SetLike A B] [Preorder A] [HasClosure A B] where
  gi : GaloisInsertion (α := Set B) (β := A) HasClosure.closure SetLike.coe

namespace SetLike

variable (A B : Type*) [SetLike A B]

@[reducible] def toHasClosure [InfSet A] [LE A] : HasClosure A B where
  closure s := sInf {a : A | s ≤ a}

instance [CompleteLattice A] [IsConcreteSInf A B] : IsConcreteLE A B where
  coe_subset_coe' {a a'} := by
    suffices (a : Set B) ⊆ a' ↔ (sInf {a, a'}) = (a : Set B) by simpa
    rw [IsConcreteSInf.coe_sInf]; simp

/--
Construct a complete lattice on `A` on from an injection `A → Set B` that respects the ordering
and arbitrary infima.
-/
@[reducible] def toCompleteLattice
    [PartialOrder A] [IsConcreteLE A B] [InfSet A] [IsConcreteSInf A B] : CompleteLattice A :=
  completeLatticeOfInf A fun s => IsGLB.of_image IsConcreteLE.coe_subset_coe
    (by simpa [IsConcreteSInf.coe_sInf] using isGLB_biInf)

/--
Construct a complete lattice on a type `A` from an injection `A → Set B`
that reflects arbitrary intersections.
-/
@[reducible] noncomputable def toCompleteLattice_abstract
    (exists_coe_eq_iInter : ∀ {s : Set A}, ∃ a : A, (a : Set B) = ⋂ a' ∈ s, a') :
    CompleteLattice A :=
  let _ : InfSet A := ⟨fun _ => Classical.choose exists_coe_eq_iInter⟩
  @toCompleteLattice _ _ _ (toPartialOrder _ _) _ _
    ⟨fun {_} => by simpa using Classical.choose_spec exists_coe_eq_iInter⟩

variable {L α : Type*} [SetLike L α] [CompleteLattice L] [IsConcreteSInf L α]

attribute [local instance] SetLike.toHasClosure

@[simp]
theorem coe_top : ((⊤ : L) : Set α) = Set.univ := by
  suffices sInf (∅ : Set L) = (Set.univ : Set α) by simpa only [sInf_empty]
  rw [IsConcreteSInf.coe_sInf]; simp

@[simp]
theorem mem_top (x : α) : x ∈ (⊤ : L) := by
  rw [← SetLike.mem_coe]; simp

@[simp]
theorem coe_inf (l m : L) : ((l ⊓ m : L) : Set α) = (l : Set α) ∩ m := by
  suffices sInf {l, m} = (l : Set α) ∩ m by simpa
  rw [IsConcreteSInf.coe_sInf]; simp

@[simp]
theorem mem_inf {l m : L} {x : α} : x ∈ l ⊓ m ↔ x ∈ l ∧ x ∈ m := by
  rw [← SetLike.mem_coe]; simp

theorem coe_bot : ((⊥ : L) : Set α) = ⋂ l : L, l := by
  suffices ((sInf (Set.univ) : L) : Set α) = ⋂ l : L, l by simpa
  rw [IsConcreteSInf.coe_sInf]; simp

theorem mem_bot {x : α} : x ∈ (⊥ : L) ↔ ∀ l : L, x ∈ l := by
  rw [← SetLike.mem_coe, coe_bot]; simp

theorem coe_closure {s : Set α} :
  (HasClosure.closure (A := L) s : Set α) = ⋂ l ∈ {m : L | s ⊆ m}, l := IsConcreteSInf.coe_sInf

theorem mem_closure {s : Set α} {x : α} :
  x ∈ HasClosure.closure (A := L) s ↔ ∀ l : L, s ⊆ l → x ∈ l := IsConcreteSInf.mem_sInf

variable (L) in
open IsConcreteLE IsConcreteSInf in
instance : IsConcreteClosure L α where
  gi := GaloisConnection.toGaloisInsertion
    (fun _ _ =>
      ⟨fun h => Set.Subset.trans (fun _ hx => mem_closure.2 fun _ hs => hs hx) (mem_of_le_of_mem h),
      (sInf_le ·)⟩)
    fun _ => le_sInf (fun _ => coe_subset_coe.1)

@[simp, aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_closure {s : Set α} :
    s ⊆ HasClosure.closure (A := L) s := IsConcreteClosure.gi.gc.le_u_l s

@[aesop unsafe 50% apply (rule_sets := [SetLike])]
theorem mem_closure_of_mem {s : Set α} {x : α} (hx : x ∈ s) :
    x ∈ HasClosure.closure (A := L) s := subset_closure hx

theorem not_mem_of_not_mem_closure {s : Set α} {x : α} (hx : x ∉ HasClosure.closure (A := L) s) :
    x ∉ s := (hx <| subset_closure ·)

@[simp] theorem closure_le {s : Set α} {l : L} :
    HasClosure.closure s ≤ l ↔ s ⊆ l := IsConcreteClosure.gi.gc.le_iff_le

theorem closure_monotone :
    Monotone (HasClosure.closure : Set α → L) := IsConcreteClosure.gi.gc.monotone_l

@[gcongr] theorem closure_mono ⦃s t : Set α⦄ (h : s ⊆ t) :
    HasClosure.closure (A := L) s ≤ HasClosure.closure t := closure_monotone h

theorem closure_eq_of_le {s : Set α} {l : L} (h₁ : s ⊆ l) (h₂ : l ≤ HasClosure.closure s) :
    HasClosure.closure s = l := le_antisymm (closure_le.2 h₁) h₂

@[simp] theorem closure_eq (l : L) :
    HasClosure.closure (l : Set α) = l := IsConcreteClosure.gi.l_u_eq l

@[simp] theorem closure_empty :
    HasClosure.closure (∅ : Set α) = (⊥ : L) := IsConcreteClosure.gi.gc.l_bot

@[simp] theorem closure_univ :
    HasClosure.closure (Set.univ : Set α) = (⊤ : L) := IsConcreteClosure.gi.l_top

theorem closure_union (s t : Set α) :
    HasClosure.closure (A := L) (s ∪ t) = HasClosure.closure s ⊔ HasClosure.closure t :=
  IsConcreteClosure.gi.gc.l_sup

theorem closure_iUnion {ι} (s : ι → Set α) :
    HasClosure.closure (A := L) (⋃ i, s i) = ⨆ i, HasClosure.closure (s i) :=
  IsConcreteClosure.gi.gc.l_iSup

theorem closure_singleton_le_iff_mem (x : α) (l : L) :
    HasClosure.closure {x} ≤ l ↔ x ∈ l := by
  rw [closure_le, Set.singleton_subset_iff, SetLike.mem_coe]

theorem mem_iSup {ι : Sort*} (l : ι → L) {x : α} :
    (x ∈ ⨆ i, l i) ↔ ∀ m, (∀ i, l i ≤ m) → x ∈ m := by
  rw [← closure_singleton_le_iff_mem, le_iSup_iff]
  simp only [closure_singleton_le_iff_mem]

theorem iSup_eq_closure {ι : Sort*} (l : ι → L) :
    ⨆ i, l i = HasClosure.closure (⋃ i, (l i : Set α)) := by
  simp_rw [closure_iUnion, closure_eq]

end SetLike
