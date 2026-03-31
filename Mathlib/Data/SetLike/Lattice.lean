/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Closure

/-!
# Typeclass for lattices with a well-behaved set representation.

We define a typeclass for lattices with a well-behaved canonical representation as sets,
in the sense that the embedding preserves arbitrary infima. We also define the adjoint
closure operator.

## Main definitions

* `IsConcreteSInf` : class for complete lattices with a canonical embedding into a type of sets
  which preserves arbitrary infima.
* `SetLike.closure` : the natural closure operation adjoint to such an embedding.

## Main result

* `LatticeSetLike.gi` : the operations `SetLike.closure` and `SetLike.coe` (the embedding)
  form a Galois insertion.

-/

@[expose] public section

/--
A class to indicate that the canonical injection between `A` and `Set B`
preserves arbitrary infima.
-/
class IsConcreteSInf (A B : Type*) [SetLike A B] [InfSet A] where
  coe_sInf' (s : Set A) : ((sInf s : A) : Set B) = ⋂ a ∈ s, ↑a

namespace SetLike

variable {A B : Type*} [SetLike A B]

section InfSet

variable [InfSet A] [IsConcreteSInf A B]

@[simp, norm_cast]
theorem coe_sInf (s : Set A) : ((sInf s : A) : Set B) = ⋂ a ∈ s, a := IsConcreteSInf.coe_sInf' _

@[simp]
theorem mem_sInf {s : Set A} {x : B} : x ∈ sInf s ↔ ∀ a ∈ s, x ∈ a := by
  rw [← SetLike.mem_coe]; simp

@[simp]
theorem mem_iInf {ι : Sort*} {a : ι → A} {x : B} : (x ∈ ⨅ i, a i) ↔ ∀ i, x ∈ a i := by
  simp [iInf]

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} (a : ι → A) : (↑(⨅ i, a i) : Set B) = ⋂ i, a i := by
    ext; simp

end InfSet

section CompleteLattice

variable [CompleteLattice A] [IsConcreteSInf A B]

instance : IsConcreteLE A B where
  coe_subset_coe' {a a'} := by
    suffices (a : Set B) ⊆ a' ↔ (sInf {a, a'}) = (a : Set B) by simpa
    rw [coe_sInf]; simp

variable (A) in
@[simp, norm_cast]
theorem coe_top : ((⊤ : A) : Set B) = Set.univ := by
  suffices sInf (∅ : Set A) = (Set.univ : Set B) by simpa
  rw [coe_sInf]; simp

variable (A) in
@[simp]
theorem mem_top (x : B) : x ∈ (⊤ : A) := by
  rw [← SetLike.mem_coe]; simp

@[simp, norm_cast]
theorem coe_inf (a a' : A) : ((a ⊓ a' : A) : Set B) = (a : Set B) ∩ a' := by
  suffices sInf {a, a'} = (a : Set B) ∩ a' by simpa
  rw [coe_sInf]; simp

@[simp]
theorem mem_inf {a a' : A} {x : B} : x ∈ a ⊓ a' ↔ x ∈ a ∧ x ∈ a' := by
  rw [← SetLike.mem_coe]; simp

variable (A) in
theorem coe_bot : ((⊥ : A) : Set B) = ⋂ a : A, a := by
  suffices ((sInf (Set.univ) : A) : Set B) = ⋂ a : A, a by simpa
  rw [coe_sInf]; simp

theorem mem_bot {x : B} : x ∈ (⊥ : A) ↔ ∀ a : A, x ∈ a := by
  rw [← SetLike.mem_coe, coe_bot]; simp

end CompleteLattice

end SetLike

section adjoint

variable (A B : Type*) [SetLike A B]

/--
Construct a complete lattice on `A` on from an injection `A → Set B` that respects arbitrary infima.
-/
@[reducible] def CompleteLattice.ofSetLike
    [PartialOrder A] [IsConcreteLE A B] [InfSet A] [IsConcreteSInf A B] : CompleteLattice A :=
  completeLatticeOfInf A fun s => IsGLB.of_image IsConcreteLE.coe_subset_coe'
    (by simpa [SetLike.coe_sInf] using isGLB_biInf)

/--
Construct a complete lattice on a type `A` from an injection `A → Set B` that
reflects arbitrary intersections.
-/
@[reducible] noncomputable def CompleteLattice.of_exists_isGLB
    (exists_coe_eq_iInter : ∀ {s : Set A}, ∃ a : A, (a : Set B) = ⋂ b ∈ s, b) :
    CompleteLattice A :=
  let _ : InfSet A := ⟨fun _ ↦ Classical.choose exists_coe_eq_iInter⟩
  have : IsConcreteSInf A B := ⟨fun _ ↦ Classical.choose_spec exists_coe_eq_iInter⟩
  let _ : PartialOrder A := .ofSetLike ..
  .ofSetLike ..

namespace SetLike

variable {B} [CompleteLattice A] [IsConcreteSInf A B]

/- The closure operator `Set B → A` induced by a map `A → Set B` that respects arbitrary infima. -/
def closure : LowerAdjoint (SetLike.coe : A → Set B) where
  toFun := fun s ↦ sInf {a : A | s ≤ a}
  gc' := (fun _ _ =>
    ⟨fun h => Set.Subset.trans
      (fun _ hx => mem_sInf.2 (fun _ hs => (hs : _ ∈ {a : A | _ ≤ (a : Set B)}) hx))
      (mem_of_le_of_mem h),
    (sInf_le ·)⟩)

def gi : GaloisInsertion (closure A) (SetLike.coe : A → Set B) :=
  (closure A).gc.toGaloisInsertion fun _ => le_sInf (fun _ => coe_subset_coe.1)

theorem isGLB_closure {s : Set B} : IsGLB {a : A | s ⊆ a} (closure A s) := isGLB_sInf _

@[simp, aesop safe 20 (rule_sets := [SetLike])]
theorem subset_closure {s : Set B} :
    s ⊆ closure A s := (closure A).subset_closure _

@[aesop unsafe 80% (rule_sets := [SetLike])]
theorem mem_closure_of_mem {s : Set B} {x : B} (hx : x ∈ s) :
    x ∈ closure A s := subset_closure A hx

theorem not_mem_of_not_mem_closure {s : Set B} {x : B} : x ∉ closure A s → x ∉ s :=
    (closure A).notMem_of_notMem_closure

variable {A} in
@[simp] theorem closure_le {s : Set B} {a : A} : closure A s ≤ a ↔ s ⊆ a :=
  (closure A).le_iff_subset ..

variable {A} in
theorem mem_closure {s : Set B} {x : B} : x ∈ closure A s ↔ ∀ S : A, s ⊆ S → x ∈ S :=
  (closure A).mem_iff ..

theorem coe_closure (s : Set B) : (closure A s : Set B) = ⋂ l ∈ {m : A | s ⊆ m}, l := by
  ext; simpa using mem_closure

theorem closure_eq_of_le {s : Set B} {a : A} : s ⊆ a → a ≤ closure A s → closure A s = a :=
    (closure A).eq_of_le

theorem closure_monotone : Monotone (closure A) := (closure A).gc.monotone_l

@[gcongr] theorem closure_mono ⦃s t : Set B⦄ (h : s ⊆ t) : closure A s ≤ closure A t :=
  closure_monotone _ h

@[simp] theorem closure_eq (a : A) : closure A (a : Set B) = a := (gi A).l_u_eq a

@[simp] theorem closure_empty [OrderBot A] : closure A (∅ : Set B) = ⊥ := (closure A).gc.l_bot

@[simp] theorem closure_univ [OrderTop A] : closure A (Set.univ : Set B) = ⊤ := (gi A).l_top

theorem closure_singleton_le_iff_mem (x : B) (a : A) : closure _ {x} ≤ a ↔ x ∈ a := by simp

theorem closure_union (s t : Set B) : closure A (s ∪ t) = closure A s ⊔ closure A t :=
  (closure A).gc.l_sup

theorem mem_iSup {ι : Sort*} (l : ι → A) {x : B} :
    (x ∈ ⨆ i, l i) ↔ ∀ m, (∀ i, l i ≤ m) → x ∈ m := by
  simp_rw [← closure_singleton_le_iff_mem, le_iSup_iff]

@[simp] theorem closure_iUnion {ι} (s : ι → Set B) : closure A (⋃ i, s i) = ⨆ i, closure A (s i) :=
  (closure A).gc.l_iSup

theorem iSup_eq_closure {ι : Sort*} (l : ι → A) : ⨆ i, l i = closure A (⋃ i, (l i : Set B)) := by
  simp

end SetLike

end adjoint
