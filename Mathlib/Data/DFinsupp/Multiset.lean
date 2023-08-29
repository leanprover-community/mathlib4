/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.DFinsupp.Order

#align_import data.dfinsupp.multiset from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `DFinsupp.toMultiset` the equivalence between `Π₀ a : α, ℕ` and `Multiset α`, along
with `Multiset.toDFinsupp` the reverse equivalence.
-/

open Function

variable {α : Type*} {β : α → Type*}

namespace DFinsupp

/-- Non-dependent special case of `DFinsupp.addZeroClass` to help typeclass search. -/
instance addZeroClass' {β} [AddZeroClass β] : AddZeroClass (Π₀ _ : α, β) :=
  @DFinsupp.addZeroClass α (fun _ ↦ β) _
#align dfinsupp.add_zero_class' DFinsupp.addZeroClass'

variable [DecidableEq α] {s t : Multiset α}

/-- A DFinsupp version of `Finsupp.toMultiset`. -/
def toMultiset : (Π₀ _ : α, ℕ) →+ Multiset α :=
  DFinsupp.sumAddHom fun a : α ↦ Multiset.replicateAddMonoidHom a
#align dfinsupp.to_multiset DFinsupp.toMultiset

@[simp]
theorem toMultiset_single (a : α) (n : ℕ) :
    toMultiset (DFinsupp.single a n) = Multiset.replicate n a :=
  DFinsupp.sumAddHom_single _ _ _
#align dfinsupp.to_multiset_single DFinsupp.toMultiset_single

end DFinsupp

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

/-- A DFinsupp version of `Multiset.toFinsupp`. -/
def toDFinsupp : Multiset α →+ Π₀ _ : α, ℕ where
  toFun s :=
    { toFun := fun n ↦ s.count n
      support' := Trunc.mk ⟨s, fun i ↦ (em (i ∈ s)).imp_right Multiset.count_eq_zero_of_not_mem⟩ }
  map_zero' := rfl
  map_add' _ _ := DFinsupp.ext fun _ ↦ Multiset.count_add _ _ _
#align multiset.to_dfinsupp Multiset.toDFinsupp

@[simp]
theorem toDFinsupp_apply (s : Multiset α) (a : α) : Multiset.toDFinsupp s a = s.count a :=
  rfl
#align multiset.to_dfinsupp_apply Multiset.toDFinsupp_apply

@[simp]
theorem toDFinsupp_support (s : Multiset α) : s.toDFinsupp.support = s.toFinset :=
  (Finset.filter_eq_self _).mpr fun _ hx ↦ count_ne_zero.mpr <| Multiset.mem_toFinset.1 hx
#align multiset.to_dfinsupp_support Multiset.toDFinsupp_support

@[simp]
theorem toDFinsupp_replicate (a : α) (n : ℕ) :
    toDFinsupp (Multiset.replicate n a) = DFinsupp.single a n := by
  ext i
  -- ⊢ ↑(↑toDFinsupp (replicate n a)) i = ↑(DFinsupp.single a n) i
  dsimp [toDFinsupp]
  -- ⊢ count i (replicate n a) = ↑(DFinsupp.single a n) i
  simp [count_replicate, eq_comm]
  -- 🎉 no goals
#align multiset.to_dfinsupp_replicate Multiset.toDFinsupp_replicate

@[simp]
theorem toDFinsupp_singleton (a : α) : toDFinsupp {a} = DFinsupp.single a 1 := by
  rw [← replicate_one, toDFinsupp_replicate]
  -- 🎉 no goals
#align multiset.to_dfinsupp_singleton Multiset.toDFinsupp_singleton

/-- `Multiset.toDFinsupp` as an `AddEquiv`. -/
@[simps! apply symm_apply]
def equivDFinsupp : Multiset α ≃+ Π₀ _ : α, ℕ :=
  AddMonoidHom.toAddEquiv Multiset.toDFinsupp DFinsupp.toMultiset (by ext; simp) (by ext; simp)
                                                                      -- ⊢ count a✝ (↑(AddMonoidHom.comp DFinsupp.toMultiset toDFinsupp) {x✝}) = count  …
                                                                           -- 🎉 no goals
                                                                                     -- ⊢ ↑(↑(AddMonoidHom.comp (AddMonoidHom.comp toDFinsupp DFinsupp.toMultiset) (DF …
                                                                                          -- 🎉 no goals
#align multiset.equiv_dfinsupp Multiset.equivDFinsupp

@[simp]
theorem toDFinsupp_toMultiset (s : Multiset α) : DFinsupp.toMultiset (Multiset.toDFinsupp s) = s :=
  equivDFinsupp.symm_apply_apply s
#align multiset.to_dfinsupp_to_multiset Multiset.toDFinsupp_toMultiset

theorem toDFinsupp_injective : Injective (toDFinsupp : Multiset α → Π₀ _a, ℕ) :=
  equivDFinsupp.injective
#align multiset.to_dfinsupp_injective Multiset.toDFinsupp_injective

@[simp]
theorem toDFinsupp_inj : toDFinsupp s = toDFinsupp t ↔ s = t :=
  toDFinsupp_injective.eq_iff
#align multiset.to_dfinsupp_inj Multiset.toDFinsupp_inj

@[simp]
theorem toDFinsupp_le_toDFinsupp : toDFinsupp s ≤ toDFinsupp t ↔ s ≤ t := by
  simp [Multiset.le_iff_count, DFinsupp.le_def]
  -- 🎉 no goals
#align multiset.to_dfinsupp_le_to_dfinsupp Multiset.toDFinsupp_le_toDFinsupp

@[simp]
theorem toDFinsupp_lt_toDFinsupp : toDFinsupp s < toDFinsupp t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' toDFinsupp_le_toDFinsupp toDFinsupp_le_toDFinsupp
#align multiset.to_dfinsupp_lt_to_dfinsupp Multiset.toDFinsupp_lt_toDFinsupp

@[simp]
theorem toDFinsupp_inter (s t : Multiset α) : toDFinsupp (s ∩ t) = toDFinsupp s ⊓ toDFinsupp t := by
  ext i; simp [inf_eq_min]
  -- ⊢ ↑(↑toDFinsupp (s ∩ t)) i = ↑(↑toDFinsupp s ⊓ ↑toDFinsupp t) i
         -- 🎉 no goals
#align multiset.to_dfinsupp_inter Multiset.toDFinsupp_inter

@[simp]
theorem toDFinsupp_union (s t : Multiset α) : toDFinsupp (s ∪ t) = toDFinsupp s ⊔ toDFinsupp t := by
  ext i; simp [sup_eq_max]
  -- ⊢ ↑(↑toDFinsupp (s ∪ t)) i = ↑(↑toDFinsupp s ⊔ ↑toDFinsupp t) i
         -- 🎉 no goals
#align multiset.to_dfinsupp_union Multiset.toDFinsupp_union

end Multiset


namespace DFinsupp

variable [DecidableEq α] {f g : Π₀ _a : α, ℕ}

@[simp]
theorem toMultiset_toDFinsupp [DecidableEq α] (f : Π₀ _ : α, ℕ) :
    Multiset.toDFinsupp (DFinsupp.toMultiset f) = f :=
  Multiset.equivDFinsupp.apply_symm_apply f
#align dfinsupp.to_multiset_to_dfinsupp DFinsupp.toMultiset_toDFinsupp

theorem toMultiset_injective : Injective (toMultiset : (Π₀ _a, ℕ) → Multiset α) :=
  Multiset.equivDFinsupp.symm.injective
#align dfinsupp.to_multiset_injective DFinsupp.toMultiset_injective

@[simp]
theorem toMultiset_inj : toMultiset f = toMultiset g ↔ f = g :=
  toMultiset_injective.eq_iff
#align dfinsupp.to_multiset_inj DFinsupp.toMultiset_inj

@[simp]
theorem toMultiset_le_toMultiset : toMultiset f ≤ toMultiset g ↔ f ≤ g := by
  simp_rw [← Multiset.toDFinsupp_le_toDFinsupp, toMultiset_toDFinsupp]
  -- 🎉 no goals
#align dfinsupp.to_multiset_le_to_multiset DFinsupp.toMultiset_le_toMultiset

@[simp]
theorem toMultiset_lt_toMultiset : toMultiset f < toMultiset g ↔ f < g := by
  simp_rw [← Multiset.toDFinsupp_lt_toDFinsupp, toMultiset_toDFinsupp]
  -- 🎉 no goals
#align dfinsupp.to_multiset_lt_to_multiset DFinsupp.toMultiset_lt_toMultiset

variable (f g)

@[simp]
theorem toMultiset_inf : toMultiset (f ⊓ g) = toMultiset f ∩ toMultiset g :=
  Multiset.toDFinsupp_injective <| by simp
                                      -- 🎉 no goals
#align dfinsupp.to_multiset_inf DFinsupp.toMultiset_inf

@[simp]
theorem toMultiset_sup : toMultiset (f ⊔ g) = toMultiset f∪ toMultiset g :=
  Multiset.toDFinsupp_injective <| by simp
                                      -- 🎉 no goals
#align dfinsupp.to_multiset_sup DFinsupp.toMultiset_sup

end DFinsupp
