/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.DFinsupp.BigOperators
import Mathlib.Data.DFinsupp.Order

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `DFinsupp.toMultiset` the equivalence between `Π₀ a : α, ℕ` and `Multiset α`, along
with `Multiset.toDFinsupp` the reverse equivalence.
-/

open Function

variable {α : Type*}

namespace DFinsupp

/-- Non-dependent special case of `DFinsupp.addZeroClass` to help typeclass search. -/
instance addZeroClass' {β} [AddZeroClass β] : AddZeroClass (Π₀ _ : α, β) :=
  @DFinsupp.addZeroClass α (fun _ ↦ β) _

variable [DecidableEq α]

/-- A DFinsupp version of `Finsupp.toMultiset`. -/
def toMultiset : (Π₀ _ : α, ℕ) →+ Multiset α :=
  DFinsupp.sumAddHom fun a : α ↦ Multiset.replicateAddMonoidHom a

@[simp]
theorem toMultiset_single (a : α) (n : ℕ) :
    toMultiset (DFinsupp.single a n) = Multiset.replicate n a :=
  DFinsupp.sumAddHom_single _ _ _

end DFinsupp

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

/-- A DFinsupp version of `Multiset.toFinsupp`. -/
def toDFinsupp : Multiset α →+ Π₀ _ : α, ℕ where
  toFun s :=
    { toFun := fun n ↦ s.count n
      support' := Trunc.mk ⟨s, fun i ↦ (em (i ∈ s)).imp_right Multiset.count_eq_zero_of_notMem⟩ }
  map_zero' := rfl
  map_add' _ _ := DFinsupp.ext fun _ ↦ Multiset.count_add _ _ _

@[simp]
theorem toDFinsupp_apply (s : Multiset α) (a : α) : Multiset.toDFinsupp s a = s.count a :=
  rfl

@[simp]
theorem toDFinsupp_support (s : Multiset α) : s.toDFinsupp.support = s.toFinset :=
  Finset.filter_true_of_mem fun _ hx ↦ count_ne_zero.mpr <| Multiset.mem_toFinset.1 hx

@[simp]
theorem toDFinsupp_replicate (a : α) (n : ℕ) :
    toDFinsupp (Multiset.replicate n a) = DFinsupp.single a n := by
  ext i
  dsimp [toDFinsupp]
  simp [count_replicate]

@[simp]
theorem toDFinsupp_singleton (a : α) : toDFinsupp {a} = DFinsupp.single a 1 := by
  rw [← replicate_one, toDFinsupp_replicate]

/-- `Multiset.toDFinsupp` as an `AddEquiv`. -/
@[simps! apply symm_apply]
def equivDFinsupp : Multiset α ≃+ Π₀ _ : α, ℕ :=
  AddMonoidHom.toAddEquiv Multiset.toDFinsupp DFinsupp.toMultiset (by ext; simp) (by ext; simp)

@[simp]
theorem toDFinsupp_toMultiset (s : Multiset α) : DFinsupp.toMultiset (Multiset.toDFinsupp s) = s :=
  equivDFinsupp.symm_apply_apply s

theorem toDFinsupp_injective : Injective (toDFinsupp : Multiset α → Π₀ _a, ℕ) :=
  equivDFinsupp.injective

@[simp]
theorem toDFinsupp_inj : toDFinsupp s = toDFinsupp t ↔ s = t :=
  toDFinsupp_injective.eq_iff

@[simp]
theorem toDFinsupp_le_toDFinsupp : toDFinsupp s ≤ toDFinsupp t ↔ s ≤ t := by
  simp [Multiset.le_iff_count, DFinsupp.le_def]

@[simp]
theorem toDFinsupp_lt_toDFinsupp : toDFinsupp s < toDFinsupp t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' toDFinsupp_le_toDFinsupp toDFinsupp_le_toDFinsupp

@[simp]
theorem toDFinsupp_inter (s t : Multiset α) : toDFinsupp (s ∩ t) = toDFinsupp s ⊓ toDFinsupp t := by
  ext i; simp

@[simp]
theorem toDFinsupp_union (s t : Multiset α) : toDFinsupp (s ∪ t) = toDFinsupp s ⊔ toDFinsupp t := by
  ext i; simp

end Multiset


namespace DFinsupp

variable [DecidableEq α] {f g : Π₀ _a : α, ℕ}

@[simp]
theorem toMultiset_toDFinsupp (f : Π₀ _ : α, ℕ) :
    Multiset.toDFinsupp (DFinsupp.toMultiset f) = f :=
  Multiset.equivDFinsupp.apply_symm_apply f

theorem toMultiset_injective : Injective (toMultiset : (Π₀ _a, ℕ) → Multiset α) :=
  Multiset.equivDFinsupp.symm.injective

@[simp]
theorem toMultiset_inj : toMultiset f = toMultiset g ↔ f = g :=
  toMultiset_injective.eq_iff

@[simp]
theorem toMultiset_le_toMultiset : toMultiset f ≤ toMultiset g ↔ f ≤ g := by
  simp_rw [← Multiset.toDFinsupp_le_toDFinsupp, toMultiset_toDFinsupp]

@[simp]
theorem toMultiset_lt_toMultiset : toMultiset f < toMultiset g ↔ f < g := by
  simp_rw [← Multiset.toDFinsupp_lt_toDFinsupp, toMultiset_toDFinsupp]

variable (f g)

@[simp]
theorem toMultiset_inf : toMultiset (f ⊓ g) = toMultiset f ∩ toMultiset g :=
  Multiset.toDFinsupp_injective <| by simp

@[simp]
theorem toMultiset_sup : toMultiset (f ⊔ g) = toMultiset f∪ toMultiset g :=
  Multiset.toDFinsupp_injective <| by simp

end DFinsupp
