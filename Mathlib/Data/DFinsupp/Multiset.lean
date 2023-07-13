/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.dfinsupp.multiset
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.DFinsupp.Order

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `DFinsupp.toMultiset` the equivalence between `Π₀ a : α, ℕ` and `Multiset α`, along
with `Multiset.toDFinsupp` the reverse equivalence.

Note that this provides a computable alternative to `Finsupp.toMultiset`.
-/


variable {α : Type _} {β : α → Type _}

namespace DFinsupp

/-- Non-dependent special case of `DFinsupp.addZeroClass` to help typeclass search. -/
instance addZeroClass' {β} [AddZeroClass β] : AddZeroClass (Π₀ _ : α, β) :=
  @DFinsupp.addZeroClass α (fun _ ↦ β) _
#align dfinsupp.add_zero_class' DFinsupp.addZeroClass'

variable [DecidableEq α]

/-- A computable version of `Finsupp.toMultiset`. -/
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

variable [DecidableEq α]

/-- A computable version of `Multiset.toFinsupp`. -/
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
  dsimp [toDFinsupp]
  simp [count_replicate, eq_comm]
#align multiset.to_dfinsupp_replicate Multiset.toDFinsupp_replicate

@[simp]
theorem toDFinsupp_singleton (a : α) : toDFinsupp {a} = DFinsupp.single a 1 := by
  rw [← replicate_one, toDFinsupp_replicate]
#align multiset.to_dfinsupp_singleton Multiset.toDFinsupp_singleton

/-- `Multiset.toDFinsupp` as an `AddEquiv`. -/
@[simps! apply symm_apply]
def equivDFinsupp : Multiset α ≃+ Π₀ _ : α, ℕ :=
  AddMonoidHom.toAddEquiv Multiset.toDFinsupp DFinsupp.toMultiset (by ext; simp) (by ext; simp)
#align multiset.equiv_dfinsupp Multiset.equivDFinsupp

@[simp]
theorem toDFinsupp_toMultiset (s : Multiset α) : DFinsupp.toMultiset (Multiset.toDFinsupp s) = s :=
  equivDFinsupp.symm_apply_apply s
#align multiset.to_dfinsupp_to_multiset Multiset.toDFinsupp_toMultiset

@[simp]
theorem toDFinsupp_le_toDFinsupp (s t : Multiset α) : toDFinsupp s ≤ toDFinsupp t ↔ s ≤ t := by
  simp [Multiset.le_iff_count, DFinsupp.le_def]
#align multiset.to_dfinsupp_le_to_dfinsupp Multiset.toDFinsupp_le_toDFinsupp

end Multiset

@[simp]
theorem DFinsupp.toMultiset_toDFinsupp [DecidableEq α] (f : Π₀ _ : α, ℕ) :
    Multiset.toDFinsupp (DFinsupp.toMultiset f) = f :=
  Multiset.equivDFinsupp.apply_symm_apply f
#align dfinsupp.to_multiset_to_dfinsupp DFinsupp.toMultiset_toDFinsupp
