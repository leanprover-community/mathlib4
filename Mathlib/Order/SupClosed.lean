/-
Copyright (c) 2023 Yaël Dillies, Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Order.Closure
import Mathlib.Order.UpperLower.Basic

/-!
# Sets closed under join/meet

This file defines predicates for sets closed under `⊔` and shows that each set in a join-semilattice
generates a join-closed set and that a semilattice where every directed set has a least upper bound
is automatically complete. All dually for `⊓`.

## Main declarations

* `SupClosed`: Predicate for a set to be closed under join (`a ∈ s` and `b ∈ s` imply `a ⊔ b ∈ s`).
* `InfClosed`: Predicate for a set to be closed under meet (`a ∈ s` and `b ∈ s` imply `a ⊓ b ∈ s`).
* `supClosure`: Sup-closure. Smallest sup-closed set containing a given set.
* `infClosure`: Inf-closure. Smallest inf-closed set containing a given set.
* `SemilatticeSup.toCompleteSemilatticeSup`: A join-semilattice where every sup-closed set has a
  least upper bound is automatically complete.
* `SemilatticeInf.toCompleteSemilatticeInf`: A meet-semilattice where every inf-closed set has a
  greatest lower bound is automatically complete.
-/

variable {α : Type*}

section SemilatticeSup
variable [SemilatticeSup α]

section Set
variable {ι : Sort*} {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}
open Set

/-- A set `s` is *sup-closed* if `a ⊔ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
def SupClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊔ b ∈ s

@[simp] lemma supClosed_empty : SupClosed (∅ : Set α) := by simp [SupClosed]
@[simp] lemma supClosed_singleton : SupClosed ({a} : Set α) := by simp [SupClosed]

@[simp] lemma supClosed_univ : SupClosed (univ : Set α) := by simp [SupClosed]
lemma SupClosed.inter (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ∩ t) :=
λ _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma supClosed_sInter (hS : ∀ s ∈ S, SupClosed s) : SupClosed (⋂₀ S) :=
λ _a ha _b hb _s hs ↦ hS _ hs (ha _ hs) (hb _ hs)

lemma supClosed_iInter (hf : ∀ i, SupClosed (f i)) : SupClosed (⋂ i, f i) :=
supClosed_sInter $ forall_range_iff.2 hf

lemma SupClosed.directedOn (hs : SupClosed s) : DirectedOn (· ≤ ·) s :=
λ _a ha _b hb ↦ ⟨_, hs ha hb, le_sup_left, le_sup_right⟩

lemma IsUpperSet.supClosed (hs : IsUpperSet s) : SupClosed s := fun _a _ _b ↦ hs le_sup_right

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

lemma SupClosed.finsetSup'_mem (hs : SupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s :=
  sup'_induction _ _ hs

lemma SupClosed.finsetSup_mem [OrderBot α] (hs : SupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup f ∈ s :=
  sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht
#align finset.sup_closed_of_sup_closed SupClosed.finsetSup_mem

end Finset
end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α]

section Set
variable {ι : Sort*} {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}
open Set

/-- A set `s` is *inf-closed* if `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
def InfClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊓ b ∈ s

@[simp] lemma infClosed_empty : InfClosed (∅ : Set α) := by simp [InfClosed]
@[simp] lemma infClosed_singleton : InfClosed ({a} : Set α) := by simp [InfClosed]

@[simp] lemma infClosed_univ : InfClosed (univ : Set α) := by simp [InfClosed]
lemma InfClosed.inter (hs : InfClosed s) (ht : InfClosed t) : InfClosed (s ∩ t) :=
λ _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma infClosed_sInter (hS : ∀ s ∈ S, InfClosed s) : InfClosed (⋂₀ S) :=
λ _a ha _b hb _s hs ↦ hS _ hs (ha _ hs) (hb _ hs)

lemma infClosed_iInter (hf : ∀ i, InfClosed (f i)) : InfClosed (⋂ i, f i) :=
infClosed_sInter $ forall_range_iff.2 hf

lemma InfClosed.codirectedOn (hs : InfClosed s) : DirectedOn (· ≥ ·) s :=
λ _a ha _b hb ↦ ⟨_, hs ha hb, inf_le_left, inf_le_right⟩

lemma IsLowerSet.infClosed (hs : IsLowerSet s) :  InfClosed s := λ _a _ _b ↦ hs inf_le_right

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

lemma InfClosed.finsetInf'_mem (hs : InfClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.inf' ht f ∈ s :=
  inf'_induction _ _ hs

lemma InfClosed.finsetInf_mem [OrderTop α] (hs : InfClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.inf f ∈ s :=
  inf'_eq_inf ht f ▸ hs.finsetInf'_mem ht
#align finset.inf_closed_of_inf_closed InfClosed.finsetInf_mem

end Finset
end SemilatticeInf

open Finset OrderDual

section Lattice
variable [Lattice α]

@[simp] lemma supClosed_preimage_toDual {s : Set αᵒᵈ} : SupClosed (toDual ⁻¹' s) ↔ InfClosed s :=
Iff.rfl

@[simp] lemma infClosed_preimage_toDual {s : Set αᵒᵈ} : InfClosed (toDual ⁻¹' s) ↔ SupClosed s :=
Iff.rfl

@[simp] lemma supClosed_preimage_ofDual {s : Set α} : SupClosed (ofDual ⁻¹' s) ↔ InfClosed s :=
Iff.rfl

@[simp] lemma infClosed_preimage_ofDual {s : Set α} : InfClosed (ofDual ⁻¹' s) ↔ SupClosed s :=
Iff.rfl

alias ⟨_, InfClosed.dual⟩ := supClosed_preimage_ofDual
alias ⟨_, SupClosed.dual⟩ := infClosed_preimage_ofDual

end Lattice

section LinearOrder
variable [LinearOrder α]

@[simp] protected lemma LinearOrder.supClosed (s : Set α) : SupClosed s :=
λ a ha b hb ↦ by cases le_total a b <;> simp [*]

@[simp] protected lemma LinearOrder.infClosed (s : Set α) : InfClosed s :=
λ a ha b hb ↦ by cases le_total a b <;> simp [*]

end LinearOrder

/-! ## Closure -/

section SemilatticeSup
variable [SemilatticeSup α] {s : Set α} {a : α}

/-- Every set in a join-semilattice generates a set closed under join. -/
def supClosure : ClosureOperator (Set α) := ClosureOperator.mk₃
  (λ s ↦ {a | ∃ (t : Finset α) (ht : t.Nonempty), ↑t ⊆ s ∧ t.sup' ht id = a})
  SupClosed
  (λ s a ha ↦ ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine' ⟨_, ht.mono $ subset_union_left _ _, _, sup'_union ht hu _⟩
    rw [coe_union]
    exact Set.union_subset hts hus)
  (by rintro s₁ s₂ hs h₂ _ ⟨t, ht, hts, rfl⟩; exact h₂.finsetSup'_mem ht λ i hi ↦ hs $ hts hi)

@[simp] lemma subset_supClosure {s : Set α} : s ⊆ supClosure s := supClosure.le_closure _

@[simp] lemma supClosed_supClosure {s : Set α} : SupClosed (supClosure s) :=
ClosureOperator.closure_mem_mk₃ _

lemma supClosure_mono : Monotone (supClosure : Set α → Set α) := supClosure.monotone

@[simp] lemma supClosure_eq_self : supClosure s = s ↔ SupClosed s := ClosureOperator.mem_mk₃_closed

alias ⟨_, SupClosed.supClosure_eq⟩ := supClosure_eq_self

lemma supClosure_idem (s : Set α) : supClosure (supClosure s) = supClosure s :=
supClosure.idempotent _

@[simp] lemma supClosure_empty : supClosure (∅ : Set α) = ∅ := by simp
@[simp] lemma supClosure_singleton : supClosure {a} = {a} := by simp
@[simp] lemma supClosure_univ : supClosure (Set.univ : Set α) = Set.univ := by simp

@[simp] lemma upperBounds_supClosure (s : Set α) : upperBounds (supClosure s) = upperBounds s :=
(upperBounds_mono_set subset_supClosure).antisymm $ by
  rintro a ha _ ⟨t, ht, hts, rfl⟩
  exact sup'_le _ _ λ b hb ↦ ha $ hts hb

@[simp] lemma isLUB_supClosure : IsLUB (supClosure s) a ↔ IsLUB s a := by simp [IsLUB]

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] {s : Set α} {a : α}

/-- Every set in a join-semilattice generates a set closed under join. -/
def infClosure : ClosureOperator (Set α) := ClosureOperator.mk₃
  (λ s ↦ {a | ∃ (t : Finset α) (ht : t.Nonempty), ↑t ⊆ s ∧ t.inf' ht id = a})
  InfClosed
  (λ s a ha ↦ ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine' ⟨_, ht.mono $ subset_union_left _ _, _, inf'_union ht hu _⟩
    rw [coe_union]
    exact Set.union_subset hts hus)
  (by rintro s₁ s₂ hs h₂ _ ⟨t, ht, hts, rfl⟩; exact h₂.finsetInf'_mem ht λ i hi ↦ hs $ hts hi)

@[simp] lemma subset_infClosure {s : Set α} : s ⊆ infClosure s := infClosure.le_closure _

@[simp] lemma infClosed_infClosure {s : Set α} : InfClosed (infClosure s) :=
ClosureOperator.closure_mem_mk₃ _

lemma infClosure_mono : Monotone (infClosure : Set α → Set α) := infClosure.monotone

@[simp] lemma infClosure_eq_self : infClosure s = s ↔ InfClosed s := ClosureOperator.mem_mk₃_closed

alias ⟨_, InfClosed.infClosure_eq⟩ := infClosure_eq_self

lemma infClosure_idem (s : Set α) : infClosure (infClosure s) = infClosure s :=
infClosure.idempotent _

@[simp] lemma infClosure_empty : infClosure (∅ : Set α) = ∅ := by simp
@[simp] lemma infClosure_singleton : infClosure {a} = {a} := by simp
@[simp] lemma infClosure_univ : infClosure (Set.univ : Set α) = Set.univ := by simp

@[simp] lemma lowerBounds_infClosure (s : Set α) : lowerBounds (infClosure s) = lowerBounds s :=
(lowerBounds_mono_set subset_infClosure).antisymm $ by
  rintro a ha _ ⟨t, ht, hts, rfl⟩
  exact le_inf' _ _ λ b hb ↦ ha $ hts hb

@[simp] lemma isGLB_infClosure : IsGLB (infClosure s) a ↔ IsGLB s a := by simp [IsGLB]

end SemilatticeInf

/-- A join-semilattice where every sup-closed set has a least upper bound is automatically complete.
-/
def SemilatticeSup.toCompleteSemilatticeSup [SemilatticeSup α] (sSup : Set α → α)
    (h : ∀ s, SupClosed s → IsLUB s (sSup s)) : CompleteSemilatticeSup α where
  sSup := fun s => sSup (supClosure s)
  le_sSup s a ha := (h _ supClosed_supClosure).1 $ subset_supClosure ha
  sSup_le s a ha := (isLUB_le_iff $ h _ supClosed_supClosure).2 $ by rwa [upperBounds_supClosure]

/-- A meet-semilattice where every inf-closed set has a greatest lower bound is automatically
complete. -/
def SemilatticeInf.toCompleteSemilatticeInf [SemilatticeInf α] (sInf : Set α → α)
    (h : ∀ s, InfClosed s → IsGLB s (sInf s)) : CompleteSemilatticeInf α where
  sInf := fun s => sInf (infClosure s)
  sInf_le s a ha := (h _ infClosed_infClosure).1 $ subset_infClosure ha
  le_sInf s a ha := (le_isGLB_iff $ h _ infClosed_infClosure).2 $ by rwa [lowerBounds_infClosure]
