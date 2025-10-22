/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Lattice.Fold

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


open Finset OrderDual

variable {ι α : Type*}

/-! ### Irreducible and prime elements -/


section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

/-- A sup-irreducible element is a non-bottom element which isn't the supremum of anything smaller.
-/
def SupIrred (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
def SupPrime (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

theorem SupIrred.not_isMin (ha : SupIrred a) : ¬IsMin a :=
  ha.1

theorem SupPrime.not_isMin (ha : SupPrime a) : ¬IsMin a :=
  ha.1

theorem IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a := fun h => h.1 ha

theorem IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a := fun h => h.1 ha

@[simp]
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  rw [SupIrred, not_and_or]
  push_neg
  rw [exists₂_congr]
  simp +contextual [@eq_comm _ _ a]

@[simp]
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  rw [SupPrime, not_and_or]; push_neg; rfl

protected theorem SupPrime.supIrred : SupPrime a → SupIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.ge

theorem SupPrime.le_sup (ha : SupPrime a) : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c :=
  ⟨fun h => ha.2 h, fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩

variable [OrderBot α] {s : Finset ι} {f : ι → α}

@[simp]
theorem not_supIrred_bot : ¬SupIrred (⊥ : α) :=
  isMin_bot.not_supIrred

@[simp]
theorem not_supPrime_bot : ¬SupPrime (⊥ : α) :=
  isMin_bot.not_supPrime

theorem SupIrred.ne_bot (ha : SupIrred a) : a ≠ ⊥ := by rintro rfl; exact not_supIrred_bot ha

theorem SupPrime.ne_bot (ha : SupPrime a) : a ≠ ⊥ := by rintro rfl; exact not_supPrime_bot ha

theorem SupIrred.finset_sup_eq (ha : SupIrred a) (h : s.sup f = a) : ∃ i ∈ s, f i = a := by
  classical
  induction s using Finset.induction with
  | empty => simpa [ha.ne_bot] using h.symm
  | insert i s _ ih =>
    simp only [exists_mem_insert] at ih ⊢
    rw [sup_insert] at h
    exact (ha.2 h).imp_right ih

theorem SupPrime.le_finset_sup (ha : SupPrime a) : a ≤ s.sup f ↔ ∃ i ∈ s, a ≤ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp [ha.ne_bot]
  | insert i s _ ih => simp only [exists_mem_insert, sup_insert, ha.le_sup, ih]

variable [WellFoundedLT α]

/-- In a well-founded lattice, any element is the supremum of finitely many sup-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/
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

section SemilatticeInf

variable [SemilatticeInf α] {a b c : α}

/-- An inf-irreducible element is a non-top element which isn't the infimum of anything bigger. -/
def InfIrred (a : α) : Prop :=
  ¬IsMax a ∧ ∀ ⦃b c⦄, b ⊓ c = a → b = a ∨ c = a

/-- An inf-prime element is a non-top element which isn't bigger than the infimum of anything
bigger. -/
def InfPrime (a : α) : Prop :=
  ¬IsMax a ∧ ∀ ⦃b c⦄, b ⊓ c ≤ a → b ≤ a ∨ c ≤ a

@[simp]
theorem IsMax.not_infIrred (ha : IsMax a) : ¬InfIrred a := fun h => h.1 ha

@[simp]
theorem IsMax.not_infPrime (ha : IsMax a) : ¬InfPrime a := fun h => h.1 ha

@[simp]
theorem not_infIrred : ¬InfIrred a ↔ IsMax a ∨ ∃ b c, b ⊓ c = a ∧ a < b ∧ a < c :=
  @not_supIrred αᵒᵈ _ _

@[simp]
theorem not_infPrime : ¬InfPrime a ↔ IsMax a ∨ ∃ b c, b ⊓ c ≤ a ∧ ¬b ≤ a ∧ ¬c ≤ a :=
  @not_supPrime αᵒᵈ _ _

protected theorem InfPrime.infIrred : InfPrime a → InfIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.le

theorem InfPrime.inf_le (ha : InfPrime a) : b ⊓ c ≤ a ↔ b ≤ a ∨ c ≤ a :=
  ⟨fun h => ha.2 h, fun h => h.elim inf_le_of_left_le inf_le_of_right_le⟩

variable [OrderTop α] {s : Finset ι} {f : ι → α}

theorem not_infIrred_top : ¬InfIrred (⊤ : α) :=
  isMax_top.not_infIrred

theorem not_infPrime_top : ¬InfPrime (⊤ : α) :=
  isMax_top.not_infPrime

theorem InfIrred.ne_top (ha : InfIrred a) : a ≠ ⊤ := by rintro rfl; exact not_infIrred_top ha

theorem InfPrime.ne_top (ha : InfPrime a) : a ≠ ⊤ := by rintro rfl; exact not_infPrime_top ha

theorem InfIrred.finset_inf_eq : InfIrred a → s.inf f = a → ∃ i ∈ s, f i = a :=
  @SupIrred.finset_sup_eq _ αᵒᵈ _ _ _ _ _

theorem InfPrime.finset_inf_le (ha : InfPrime a) : s.inf f ≤ a ↔ ∃ i ∈ s, f i ≤ a :=
  @SupPrime.le_finset_sup _ αᵒᵈ _ _ _ _ _ ha

variable [WellFoundedGT α]

/-- In a cowell-founded lattice, any element is the infimum of finitely many inf-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/
theorem exists_infIrred_decomposition (a : α) :
    ∃ s : Finset α, s.inf id = a ∧ ∀ ⦃b⦄, b ∈ s → InfIrred b :=
  exists_supIrred_decomposition (α := αᵒᵈ) _

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup α]

@[simp]
theorem infIrred_toDual {a : α} : InfIrred (toDual a) ↔ SupIrred a :=
  Iff.rfl

@[simp]
theorem infPrime_toDual {a : α} : InfPrime (toDual a) ↔ SupPrime a :=
  Iff.rfl

@[simp]
theorem supIrred_ofDual {a : αᵒᵈ} : SupIrred (ofDual a) ↔ InfIrred a :=
  Iff.rfl

@[simp]
theorem supPrime_ofDual {a : αᵒᵈ} : SupPrime (ofDual a) ↔ InfPrime a :=
  Iff.rfl

alias ⟨_, SupIrred.dual⟩ := infIrred_toDual

alias ⟨_, SupPrime.dual⟩ := infPrime_toDual

alias ⟨_, InfIrred.ofDual⟩ := supIrred_ofDual

alias ⟨_, InfPrime.ofDual⟩ := supPrime_ofDual

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α]

@[simp]
theorem supIrred_toDual {a : α} : SupIrred (toDual a) ↔ InfIrred a :=
  Iff.rfl

@[simp]
theorem supPrime_toDual {a : α} : SupPrime (toDual a) ↔ InfPrime a :=
  Iff.rfl

@[simp]
theorem infIrred_ofDual {a : αᵒᵈ} : InfIrred (ofDual a) ↔ SupIrred a :=
  Iff.rfl

@[simp]
theorem infPrime_ofDual {a : αᵒᵈ} : InfPrime (ofDual a) ↔ SupPrime a :=
  Iff.rfl

alias ⟨_, InfIrred.dual⟩ := supIrred_toDual

alias ⟨_, InfPrime.dual⟩ := supPrime_toDual

alias ⟨_, SupIrred.ofDual⟩ := infIrred_ofDual

alias ⟨_, SupPrime.ofDual⟩ := infPrime_ofDual

end SemilatticeInf

section DistribLattice

variable [DistribLattice α] {a : α}

@[simp]
theorem supPrime_iff_supIrred : SupPrime a ↔ SupIrred a :=
  ⟨SupPrime.supIrred,
    And.imp_right fun h b c => by simp_rw [← inf_eq_left, inf_sup_left]; exact @h _ _⟩

@[simp]
theorem infPrime_iff_infIrred : InfPrime a ↔ InfIrred a :=
  ⟨InfPrime.infIrred,
    And.imp_right fun h b c => by simp_rw [← sup_eq_left, sup_inf_left]; exact @h _ _⟩

protected alias ⟨_, SupIrred.supPrime⟩ := supPrime_iff_supIrred
protected alias ⟨_, InfIrred.infPrime⟩ := infPrime_iff_infIrred

end DistribLattice

section LinearOrder

variable [LinearOrder α] {a : α}

theorem supPrime_iff_not_isMin : SupPrime a ↔ ¬IsMin a :=
  and_iff_left <| by simp

theorem infPrime_iff_not_isMax : InfPrime a ↔ ¬IsMax a :=
  and_iff_left <| by simp

@[simp]
theorem supIrred_iff_not_isMin : SupIrred a ↔ ¬IsMin a :=
  and_iff_left fun _ _ => by simpa only [max_eq_iff] using Or.imp And.left And.left

@[simp]
theorem infIrred_iff_not_isMax : InfIrred a ↔ ¬IsMax a :=
  and_iff_left fun _ _ => by simpa only [min_eq_iff] using Or.imp And.left And.left

end LinearOrder
