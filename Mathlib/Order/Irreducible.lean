/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Lattice

#align_import order.irreducible from "leanprover-community/mathlib"@"bf2428c9486c407ca38b5b3fb10b87dad0bc99fa"

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
#align sup_irred SupIrred

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
def SupPrime (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c
#align sup_prime SupPrime

theorem SupIrred.not_isMin (ha : SupIrred a) : ¬IsMin a :=
  ha.1
#align sup_irred.not_is_min SupIrred.not_isMin

theorem SupPrime.not_isMin (ha : SupPrime a) : ¬IsMin a :=
  ha.1
#align sup_prime.not_is_min SupPrime.not_isMin

theorem IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a := fun h => h.1 ha
#align is_min.not_sup_irred IsMin.not_supIrred

theorem IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a := fun h => h.1 ha
#align is_min.not_sup_prime IsMin.not_supPrime

@[simp]
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  rw [SupIrred, not_and_or]
  push_neg
  rw [exists₂_congr]
  simp (config := { contextual := true }) [@eq_comm _ _ a]
#align not_sup_irred not_supIrred

@[simp]
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  rw [SupPrime, not_and_or]; push_neg; rfl
#align not_sup_prime not_supPrime

protected theorem SupPrime.supIrred : SupPrime a → SupIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.ge
#align sup_prime.sup_irred SupPrime.supIrred

theorem SupPrime.le_sup (ha : SupPrime a) : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c :=
  ⟨fun h => ha.2 h, fun h => h.elim le_sup_of_le_left le_sup_of_le_right⟩
#align sup_prime.le_sup SupPrime.le_sup

variable [OrderBot α] {s : Finset ι} {f : ι → α}

@[simp]
theorem not_supIrred_bot : ¬SupIrred (⊥ : α) :=
  isMin_bot.not_supIrred
#align not_sup_irred_bot not_supIrred_bot

@[simp]
theorem not_supPrime_bot : ¬SupPrime (⊥ : α) :=
  isMin_bot.not_supPrime
#align not_sup_prime_bot not_supPrime_bot

theorem SupIrred.ne_bot (ha : SupIrred a) : a ≠ ⊥ := by rintro rfl; exact not_supIrred_bot ha
#align sup_irred.ne_bot SupIrred.ne_bot

theorem SupPrime.ne_bot (ha : SupPrime a) : a ≠ ⊥ := by rintro rfl; exact not_supPrime_bot ha
#align sup_prime.ne_bot SupPrime.ne_bot

theorem SupIrred.finset_sup_eq (ha : SupIrred a) (h : s.sup f = a) : ∃ i ∈ s, f i = a := by
  classical
  induction' s using Finset.induction with i s _ ih
  · simpa [ha.ne_bot] using h.symm
  simp only [exists_prop, exists_mem_insert] at ih ⊢
  rw [sup_insert] at h
  exact (ha.2 h).imp_right ih
#align sup_irred.finset_sup_eq SupIrred.finset_sup_eq

theorem SupPrime.le_finset_sup (ha : SupPrime a) : a ≤ s.sup f ↔ ∃ i ∈ s, a ≤ f i := by
  classical
  induction' s using Finset.induction with i s _ ih
  · simp [ha.ne_bot]
  · simp only [exists_prop, exists_mem_insert, sup_insert, ha.le_sup, ih]
#align sup_prime.le_finset_sup SupPrime.le_finset_sup

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
#align exists_sup_irred_decomposition exists_supIrred_decomposition

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α] {a b c : α}

/-- An inf-irreducible element is a non-top element which isn't the infimum of anything bigger. -/
def InfIrred (a : α) : Prop :=
  ¬IsMax a ∧ ∀ ⦃b c⦄, b ⊓ c = a → b = a ∨ c = a
#align inf_irred InfIrred

/-- An inf-prime element is a non-top element which isn't bigger than the infimum of anything
bigger. -/
def InfPrime (a : α) : Prop :=
  ¬IsMax a ∧ ∀ ⦃b c⦄, b ⊓ c ≤ a → b ≤ a ∨ c ≤ a
#align inf_prime InfPrime

@[simp]
theorem IsMax.not_infIrred (ha : IsMax a) : ¬InfIrred a := fun h => h.1 ha
#align is_max.not_inf_irred IsMax.not_infIrred

@[simp]
theorem IsMax.not_infPrime (ha : IsMax a) : ¬InfPrime a := fun h => h.1 ha
#align is_max.not_inf_prime IsMax.not_infPrime

@[simp]
theorem not_infIrred : ¬InfIrred a ↔ IsMax a ∨ ∃ b c, b ⊓ c = a ∧ a < b ∧ a < c :=
  @not_supIrred αᵒᵈ _ _
#align not_inf_irred not_infIrred

@[simp]
theorem not_infPrime : ¬InfPrime a ↔ IsMax a ∨ ∃ b c, b ⊓ c ≤ a ∧ ¬b ≤ a ∧ ¬c ≤ a :=
  @not_supPrime αᵒᵈ _ _
#align not_inf_prime not_infPrime

protected theorem InfPrime.infIrred : InfPrime a → InfIrred a :=
  And.imp_right fun h b c ha => by simpa [← ha] using h ha.le
#align inf_prime.inf_irred InfPrime.infIrred

theorem InfPrime.inf_le (ha : InfPrime a) : b ⊓ c ≤ a ↔ b ≤ a ∨ c ≤ a :=
  ⟨fun h => ha.2 h, fun h => h.elim inf_le_of_left_le inf_le_of_right_le⟩
#align inf_prime.inf_le InfPrime.inf_le

variable [OrderTop α] {s : Finset ι} {f : ι → α}

-- @[simp] Porting note (#10618): simp can prove this.
theorem not_infIrred_top : ¬InfIrred (⊤ : α) :=
  isMax_top.not_infIrred
#align not_inf_irred_top not_infIrred_top

-- @[simp] Porting note (#10618): simp can prove this.
theorem not_infPrime_top : ¬InfPrime (⊤ : α) :=
  isMax_top.not_infPrime
#align not_inf_prime_top not_infPrime_top

theorem InfIrred.ne_top (ha : InfIrred a) : a ≠ ⊤ := by rintro rfl; exact not_infIrred_top ha
#align inf_irred.ne_top InfIrred.ne_top

theorem InfPrime.ne_top (ha : InfPrime a) : a ≠ ⊤ := by rintro rfl; exact not_infPrime_top ha
#align inf_prime.ne_top InfPrime.ne_top

theorem InfIrred.finset_inf_eq : InfIrred a → s.inf f = a → ∃ i ∈ s, f i = a :=
  @SupIrred.finset_sup_eq _ αᵒᵈ _ _ _ _ _
#align inf_irred.finset_inf_eq InfIrred.finset_inf_eq

theorem InfPrime.finset_inf_le (ha : InfPrime a) : s.inf f ≤ a ↔ ∃ i ∈ s, f i ≤ a :=
  @SupPrime.le_finset_sup _ αᵒᵈ _ _ _ _ _ ha
#align inf_prime.finset_inf_le InfPrime.finset_inf_le

variable [WellFoundedGT α]

/-- In a cowell-founded lattice, any element is the infimum of finitely many inf-irreducible
elements. This is the order-theoretic analogue of prime factorisation. -/
theorem exists_infIrred_decomposition (a : α) :
    ∃ s : Finset α, s.inf id = a ∧ ∀ ⦃b⦄, b ∈ s → InfIrred b :=
  @exists_supIrred_decomposition αᵒᵈ _ _ _ _
#align exists_inf_irred_decomposition exists_infIrred_decomposition

end SemilatticeInf

section SemilatticeSup

variable [SemilatticeSup α]

@[simp]
theorem infIrred_toDual {a : α} : InfIrred (toDual a) ↔ SupIrred a :=
  Iff.rfl
#align inf_irred_to_dual infIrred_toDual

@[simp]
theorem infPrime_toDual {a : α} : InfPrime (toDual a) ↔ SupPrime a :=
  Iff.rfl
#align inf_prime_to_dual infPrime_toDual

@[simp]
theorem supIrred_ofDual {a : αᵒᵈ} : SupIrred (ofDual a) ↔ InfIrred a :=
  Iff.rfl
#align sup_irred_of_dual supIrred_ofDual

@[simp]
theorem supPrime_ofDual {a : αᵒᵈ} : SupPrime (ofDual a) ↔ InfPrime a :=
  Iff.rfl
#align sup_prime_of_dual supPrime_ofDual

alias ⟨_, SupIrred.dual⟩ := infIrred_toDual
#align sup_irred.dual SupIrred.dual

alias ⟨_, SupPrime.dual⟩ := infPrime_toDual
#align sup_prime.dual SupPrime.dual

alias ⟨_, InfIrred.ofDual⟩ := supIrred_ofDual
#align inf_irred.of_dual InfIrred.ofDual

alias ⟨_, InfPrime.ofDual⟩ := supPrime_ofDual
#align inf_prime.of_dual InfPrime.ofDual

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf α]

@[simp]
theorem supIrred_toDual {a : α} : SupIrred (toDual a) ↔ InfIrred a :=
  Iff.rfl
#align sup_irred_to_dual supIrred_toDual

@[simp]
theorem supPrime_toDual {a : α} : SupPrime (toDual a) ↔ InfPrime a :=
  Iff.rfl
#align sup_prime_to_dual supPrime_toDual

@[simp]
theorem infIrred_ofDual {a : αᵒᵈ} : InfIrred (ofDual a) ↔ SupIrred a :=
  Iff.rfl
#align inf_irred_of_dual infIrred_ofDual

@[simp]
theorem infPrime_ofDual {a : αᵒᵈ} : InfPrime (ofDual a) ↔ SupPrime a :=
  Iff.rfl
#align inf_prime_of_dual infPrime_ofDual

alias ⟨_, InfIrred.dual⟩ := supIrred_toDual
#align inf_irred.dual InfIrred.dual

alias ⟨_, InfPrime.dual⟩ := supPrime_toDual
#align inf_prime.dual InfPrime.dual

alias ⟨_, SupIrred.ofDual⟩ := infIrred_ofDual
#align sup_irred.of_dual SupIrred.ofDual

alias ⟨_, SupPrime.ofDual⟩ := infPrime_ofDual
#align sup_prime.of_dual SupPrime.ofDual

end SemilatticeInf

section DistribLattice

variable [DistribLattice α] {a b c : α}

@[simp]
theorem supPrime_iff_supIrred : SupPrime a ↔ SupIrred a :=
  ⟨SupPrime.supIrred,
    And.imp_right fun h b c => by simp_rw [← inf_eq_left, inf_sup_left]; exact @h _ _⟩
#align sup_prime_iff_sup_irred supPrime_iff_supIrred

@[simp]
theorem infPrime_iff_infIrred : InfPrime a ↔ InfIrred a :=
  ⟨InfPrime.infIrred,
    And.imp_right fun h b c => by simp_rw [← sup_eq_left, sup_inf_left]; exact @h _ _⟩
#align inf_prime_iff_inf_irred infPrime_iff_infIrred

alias ⟨_, SupIrred.supPrime⟩ := supPrime_iff_supIrred
#align sup_irred.sup_prime SupIrred.supPrime

alias ⟨_, InfIrred.infPrime⟩ := infPrime_iff_infIrred
#align inf_irred.inf_prime InfIrred.infPrime

-- Porting note: was attribute [protected] SupIrred.supPrime InfIrred.infPrime

end DistribLattice

section LinearOrder

variable [LinearOrder α] {a : α}

-- @[simp] Porting note (#10618): simp can prove this
theorem supPrime_iff_not_isMin : SupPrime a ↔ ¬IsMin a :=
  and_iff_left <| by simp
#align sup_prime_iff_not_is_min supPrime_iff_not_isMin

-- @[simp] Porting note (#10618): simp can prove thisrove this
theorem infPrime_iff_not_isMax : InfPrime a ↔ ¬IsMax a :=
  and_iff_left <| by simp
#align inf_prime_iff_not_is_max infPrime_iff_not_isMax

@[simp]
theorem supIrred_iff_not_isMin : SupIrred a ↔ ¬IsMin a :=
  and_iff_left fun _ _ => by simpa only [sup_eq_max, max_eq_iff] using Or.imp And.left And.left
#align sup_irred_iff_not_is_min supIrred_iff_not_isMin

@[simp]
theorem infIrred_iff_not_isMax : InfIrred a ↔ ¬IsMax a :=
  and_iff_left fun _ _ => by simpa only [inf_eq_min, min_eq_iff] using Or.imp And.left And.left
#align inf_irred_iff_not_is_max infIrred_iff_not_isMax

end LinearOrder
