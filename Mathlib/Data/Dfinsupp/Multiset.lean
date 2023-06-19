/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.dfinsupp.multiset
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Dfinsupp.Order

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `Dfinsupp.toMultiset` the equivalence between `Π₀ a : α, ℕ` and `Multiset α`, along
with `Multiset.toDfinsupp` the reverse equivalence.

Note that this provides a computable alternative to `Finsupp.toMultiset`.
-/


variable {α : Type _} {β : α → Type _}

namespace Dfinsupp

/-- Non-dependent special case of `Dfinsupp.addZeroClass` to help typeclass search. -/
instance addZeroClass' {β} [AddZeroClass β] : AddZeroClass (Π₀ _ : α, β) :=
  @Dfinsupp.addZeroClass α (fun _ ↦ β) _
#align dfinsupp.add_zero_class' Dfinsupp.addZeroClass'

variable [DecidableEq α]

/-- A computable version of `Finsupp.toMultiset`. -/
def toMultiset : (Π₀ _ : α, ℕ) →+ Multiset α :=
  Dfinsupp.sumAddHom fun a : α ↦ Multiset.replicateAddMonoidHom a
#align dfinsupp.to_multiset Dfinsupp.toMultiset

@[simp]
theorem toMultiset_single (a : α) (n : ℕ) :
    toMultiset (Dfinsupp.single a n) = Multiset.replicate n a :=
  Dfinsupp.sumAddHom_single _ _ _
#align dfinsupp.to_multiset_single Dfinsupp.toMultiset_single

end Dfinsupp

namespace Multiset

variable [DecidableEq α]

/-- A computable version of `Multiset.toFinsupp`. -/
def toDfinsupp : Multiset α →+ Π₀ _ : α, ℕ where
  toFun s :=
    { toFun := fun n ↦ s.count n
      support' := Trunc.mk ⟨s, fun i ↦ (em (i ∈ s)).imp_right Multiset.count_eq_zero_of_not_mem⟩ }
  map_zero' := rfl
  map_add' _ _ := Dfinsupp.ext fun _ ↦ Multiset.count_add _ _ _
#align multiset.to_dfinsupp Multiset.toDfinsupp

@[simp]
theorem toDfinsupp_apply (s : Multiset α) (a : α) : Multiset.toDfinsupp s a = s.count a :=
  rfl
#align multiset.to_dfinsupp_apply Multiset.toDfinsupp_apply

@[simp]
theorem toDfinsupp_support (s : Multiset α) : s.toDfinsupp.support = s.toFinset :=
  (Finset.filter_eq_self _).mpr fun _ hx ↦ count_ne_zero.mpr <| Multiset.mem_toFinset.1 hx
#align multiset.to_dfinsupp_support Multiset.toDfinsupp_support

@[simp]
theorem toDfinsupp_replicate (a : α) (n : ℕ) :
    toDfinsupp (Multiset.replicate n a) = Dfinsupp.single a n := by
  ext i
  dsimp [toDfinsupp]
  simp [count_replicate, eq_comm]
#align multiset.to_dfinsupp_replicate Multiset.toDfinsupp_replicate

@[simp]
theorem toDfinsupp_singleton (a : α) : toDfinsupp {a} = Dfinsupp.single a 1 := by
  rw [← replicate_one, toDfinsupp_replicate]
#align multiset.to_dfinsupp_singleton Multiset.toDfinsupp_singleton

/-- `Multiset.toDfinsupp` as an `AddEquiv`. -/
@[simps! apply symm_apply]
def equivDfinsupp : Multiset α ≃+ Π₀ _ : α, ℕ :=
  AddMonoidHom.toAddEquiv Multiset.toDfinsupp Dfinsupp.toMultiset (by ext; simp) (by ext; simp)
#align multiset.equiv_dfinsupp Multiset.equivDfinsupp

@[simp]
theorem toDfinsupp_toMultiset (s : Multiset α) : Dfinsupp.toMultiset (Multiset.toDfinsupp s) = s :=
  equivDfinsupp.symm_apply_apply s
#align multiset.to_dfinsupp_to_multiset Multiset.toDfinsupp_toMultiset

@[simp]
theorem toDfinsupp_le_toDfinsupp (s t : Multiset α) : toDfinsupp s ≤ toDfinsupp t ↔ s ≤ t := by
  simp [Multiset.le_iff_count, Dfinsupp.le_def]
#align multiset.to_dfinsupp_le_to_dfinsupp Multiset.toDfinsupp_le_toDfinsupp

end Multiset

@[simp]
theorem Dfinsupp.toMultiset_toDfinsupp [DecidableEq α] (f : Π₀ _ : α, ℕ) :
    Multiset.toDfinsupp (Dfinsupp.toMultiset f) = f :=
  Multiset.equivDfinsupp.apply_symm_apply f
#align dfinsupp.to_multiset_to_dfinsupp Dfinsupp.toMultiset_toDfinsupp
