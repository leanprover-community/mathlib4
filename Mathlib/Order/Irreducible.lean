/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Irreducible and prime elements in an order

This file defines irreducible and prime elements in an order and shows that in a well-founded
lattice every element decomposes as a supremum of irreducible elements.

An element is sup-irreducible (resp. inf-irreducible) if it isn't `⊥` and can't be written as the
supremum of any strictly smaller elements. An element is sup-prime (resp. inf-prime) if it isn't `⊥`
and is greater than the supremum of any two elements less than it.

Primality implies irreducibility in general. The converse only holds in distributive lattices.
Both hold for all (non-minimal) elements in a linear order.

## Main declarations

* `SupIrred a`: Sup-irreducibility, `a` isn't minimal and `a = b ⊔ c → a = b ∨ a = c`
* `InfIrred a`: Inf-irreducibility, `a` isn't maximal and `a = b ⊓ c → a = b ∨ a = c`
* `SupPrime a`: Sup-primality, `a` isn't minimal and `a ≤ b ⊔ c → a ≤ b ∨ a ≤ c`
* `InfIrred a`: Inf-primality, `a` isn't maximal and `a ≥ b ⊓ c → a ≥ b ∨ a ≥ c`
* `exists_supIrred_decomposition`/`exists_infIrred_decomposition`: Decomposition into irreducibles
  in a well-founded semilattice.
-/

@[expose] public section


open Finset OrderDual

variable {ι α : Type*}

/-! ### Irreducible and prime elements -/


section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

/-- A sup-irreducible element is a non-bottom element which isn't the supremum of anything smaller.
-/
@[to_dual
/-- An inf-irreducible element is a non-top element which isn't the infimum of anything bigger. -/]
def SupIrred (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
@[to_dual
/-- An inf-irreducible element is a non-top element which isn't the infimum of anything bigger. -/]
def SupPrime (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

@[to_dual]
theorem SupIrred.not_isMin (ha : SupIrred a) : ¬IsMin a :=
  ha.1

@[to_dual]
theorem SupPrime.not_isMin (ha : SupPrime a) : ¬IsMin a :=
  ha.1

@[to_dual]
theorem IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a := fun h => h.1 ha

@[to_dual]
theorem IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a := fun h => h.1 ha

@[to_dual (attr := simp)]
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  rw [SupIrred, not_and_or]
  push Not
  rw [exists₂_congr]
  simp +contextual [@eq_comm _ _ a]

@[to_dual (attr := simp)]
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  rw [SupPrime, not_and_or]; push Not; rfl

@[to_dual]
protected theorem SupPrime.supIrred : SupPrime a → SupIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.ge

@[to_dual inf_le]
theorem SupPrime.le_sup (ha : SupPrime a) : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c :=
  ⟨fun h => ha.2 h, fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩

variable [OrderBot α] {s : Finset ι} {f : ι → α}

@[to_dual (attr := simp)]
theorem not_supIrred_bot : ¬SupIrred (⊥ : α) :=
  isMin_bot.not_supIrred

@[to_dual (attr := simp)]
theorem not_supPrime_bot : ¬SupPrime (⊥ : α) :=
  isMin_bot.not_supPrime

@[to_dual]
theorem SupIrred.ne_bot (ha : SupIrred a) : a ≠ ⊥ := by rintro rfl; exact not_supIrred_bot ha

@[to_dual]
theorem SupPrime.ne_bot (ha : SupPrime a) : a ≠ ⊥ := by rintro rfl; exact not_supPrime_bot ha

@[to_dual]
theorem SupIrred.finset_sup_eq (ha : SupIrred a) (h : s.sup f = a) : ∃ i ∈ s, f i = a := by
  classical
  induction s using Finset.induction with
  | empty => simpa [ha.ne_bot] using h.symm
  | insert i s _ ih =>
    simp only [exists_mem_insert] at ih ⊢
    rw [sup_insert] at h
    exact (ha.2 h).imp_right ih

@[to_dual finset_inf_le]
theorem SupPrime.le_finset_sup (ha : SupPrime a) : a ≤ s.sup f ↔ ∃ i ∈ s, a ≤ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp [ha.ne_bot]
  | insert i s _ ih => simp only [exists_mem_insert, sup_insert, ha.le_sup, ih]

variable [WellFoundedLT α]

/-- In a well-founded lattice, any element is the supremum of finitely many sup-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/
@[to_dual
/-- In a cowell-founded lattice, any element is the infimum of finitely many inf-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/]
theorem exists_supIrred_decomposition (a : α) :
    ∃ s : Finset α, s.sup id = a ∧ ∀ ⦃b⦄, b ∈ s → SupIrred b := by
  classical
  apply WellFoundedLT.induction a _
  clear a
  rintro a ih
  by_cases ha : SupIrred a
  · exact ⟨{a}, by simp [ha]⟩
  rw [not_supIrred] at ha
  obtain ha | ⟨b, c, rfl, hb, hc⟩ := ha
  · exact ⟨∅, by simp [ha.eq_bot]⟩
  obtain ⟨s, rfl, hs⟩ := ih _ hb
  obtain ⟨t, rfl, ht⟩ := ih _ hc
  exact ⟨s ∪ t, sup_union, forall_mem_union.2 ⟨hs, ht⟩⟩

end SemilatticeSup

section SemilatticeSup

variable [SemilatticeSup α]

@[to_dual (attr := simp)]
theorem infIrred_toDual {a : α} : InfIrred (toDual a) ↔ SupIrred a :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem infPrime_toDual {a : α} : InfPrime (toDual a) ↔ SupPrime a :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem supIrred_ofDual {a : αᵒᵈ} : SupIrred (ofDual a) ↔ InfIrred a :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem supPrime_ofDual {a : αᵒᵈ} : SupPrime (ofDual a) ↔ InfPrime a :=
  Iff.rfl

@[to_dual] alias ⟨_, SupIrred.dual⟩ := infIrred_toDual

@[to_dual] alias ⟨_, SupPrime.dual⟩ := infPrime_toDual

@[to_dual] alias ⟨_, InfIrred.ofDual⟩ := supIrred_ofDual

@[to_dual] alias ⟨_, InfPrime.ofDual⟩ := supPrime_ofDual

end SemilatticeSup

section DistribLattice

variable [DistribLattice α] {a : α}

@[to_dual (attr := simp)]
theorem supPrime_iff_supIrred : SupPrime a ↔ SupIrred a :=
  ⟨SupPrime.supIrred,
    And.imp_right fun h b c => by simp_rw [← inf_eq_left, inf_sup_left]; exact @h _ _⟩

@[to_dual] protected alias ⟨_, SupIrred.supPrime⟩ := supPrime_iff_supIrred

end DistribLattice

section LinearOrder

variable [LinearOrder α] {a : α}

@[to_dual]
theorem supPrime_iff_not_isMin : SupPrime a ↔ ¬IsMin a :=
  and_iff_left <| by simp

@[to_dual (attr := simp)]
theorem supIrred_iff_not_isMin : SupIrred a ↔ ¬IsMin a :=
  and_iff_left fun _ _ => by simpa only [max_eq_iff] using Or.imp And.left And.left

end LinearOrder
