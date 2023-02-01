/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module data.finsupp.multiset
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Basic
import Mathbin.Data.Finsupp.Order

/-!
# Equivalence between `multiset` and `ℕ`-valued finitely supported functions

This defines `finsupp.to_multiset` the equivalence between `α →₀ ℕ` and `multiset α`, along
with `multiset.to_finsupp` the reverse equivalence and `finsupp.order_iso_multiset` the equivalence
promoted to an order isomorphism.
-/


open Finset

open BigOperators Classical

noncomputable section

variable {α β ι : Type _}

namespace Finsupp

/-- Given `f : α →₀ ℕ`, `f.to_multiset` is the multiset with multiplicities given by the values of
`f` on the elements of `α`. We define this function as an `add_equiv`. -/
def toMultiset : (α →₀ ℕ) ≃+ Multiset α
    where
  toFun f := f.Sum fun a n => n • {a}
  invFun s := ⟨s.toFinset, fun a => s.count a, fun a => by simp⟩
  left_inv f :=
    ext fun a =>
      by
      simp only [Sum, Multiset.count_sum', Multiset.count_singleton, mul_boole, coe_mk,
        mem_support_iff, Multiset.count_nsmul, Finset.sum_ite_eq, ite_not, ite_eq_right_iff]
      exact Eq.symm
  right_inv s := by simp only [Sum, coe_mk, Multiset.toFinset_sum_count_nsmul_eq]
  map_add' f g := sum_add_index' (fun a => zero_nsmul _) fun a => add_nsmul _
#align finsupp.to_multiset Finsupp.toMultiset

theorem toMultiset_zero : (0 : α →₀ ℕ).toMultiset = 0 :=
  rfl
#align finsupp.to_multiset_zero Finsupp.toMultiset_zero

theorem toMultiset_add (m n : α →₀ ℕ) : (m + n).toMultiset = m.toMultiset + n.toMultiset :=
  toMultiset.map_add m n
#align finsupp.to_multiset_add Finsupp.toMultiset_add

theorem toMultiset_apply (f : α →₀ ℕ) : f.toMultiset = f.Sum fun a n => n • {a} :=
  rfl
#align finsupp.to_multiset_apply Finsupp.toMultiset_apply

@[simp]
theorem toMultiset_symm_apply [DecidableEq α] (s : Multiset α) (x : α) :
    Finsupp.toMultiset.symm s x = s.count x := by convert rfl
#align finsupp.to_multiset_symm_apply Finsupp.toMultiset_symm_apply

@[simp]
theorem toMultiset_single (a : α) (n : ℕ) : toMultiset (single a n) = n • {a} := by
  rw [to_multiset_apply, sum_single_index] <;> apply zero_nsmul
#align finsupp.to_multiset_single Finsupp.toMultiset_single

theorem toMultiset_sum {f : ι → α →₀ ℕ} (s : Finset ι) :
    Finsupp.toMultiset (∑ i in s, f i) = ∑ i in s, Finsupp.toMultiset (f i) :=
  AddEquiv.map_sum _ _ _
#align finsupp.to_multiset_sum Finsupp.toMultiset_sum

theorem toMultiset_sum_single (s : Finset ι) (n : ℕ) :
    Finsupp.toMultiset (∑ i in s, single i n) = n • s.val := by
  simp_rw [to_multiset_sum, Finsupp.toMultiset_single, sum_nsmul, sum_multiset_singleton]
#align finsupp.to_multiset_sum_single Finsupp.toMultiset_sum_single

theorem card_toMultiset (f : α →₀ ℕ) : f.toMultiset.card = f.Sum fun a => id := by
  simp [to_multiset_apply, AddMonoidHom.map_finsupp_sum, Function.id_def]
#align finsupp.card_to_multiset Finsupp.card_toMultiset

theorem toMultiset_map (f : α →₀ ℕ) (g : α → β) : f.toMultiset.map g = (f.mapDomain g).toMultiset :=
  by
  refine' f.induction _ _
  · rw [to_multiset_zero, Multiset.map_zero, map_domain_zero, to_multiset_zero]
  · intro a n f _ _ ih
    rw [to_multiset_add, Multiset.map_add, ih, map_domain_add, map_domain_single,
      to_multiset_single, to_multiset_add, to_multiset_single, ← Multiset.coe_mapAddMonoidHom,
      (Multiset.mapAddMonoidHom g).map_nsmul]
    rfl
#align finsupp.to_multiset_map Finsupp.toMultiset_map

@[simp]
theorem prod_toMultiset [CommMonoid α] (f : α →₀ ℕ) : f.toMultiset.Prod = f.Prod fun a n => a ^ n :=
  by
  refine' f.induction _ _
  · rw [to_multiset_zero, Multiset.prod_zero, Finsupp.prod_zero_index]
  · intro a n f _ _ ih
    rw [to_multiset_add, Multiset.prod_add, ih, to_multiset_single, Multiset.prod_nsmul,
      Finsupp.prod_add_index' pow_zero pow_add, Finsupp.prod_single_index, Multiset.prod_singleton]
    · exact pow_zero a
#align finsupp.prod_to_multiset Finsupp.prod_toMultiset

@[simp]
theorem toFinset_toMultiset [DecidableEq α] (f : α →₀ ℕ) : f.toMultiset.toFinset = f.support :=
  by
  refine' f.induction _ _
  · rw [to_multiset_zero, Multiset.toFinset_zero, support_zero]
  · intro a n f ha hn ih
    rw [to_multiset_add, Multiset.toFinset_add, ih, to_multiset_single, support_add_eq,
      support_single_ne_zero _ hn, Multiset.toFinset_nsmul _ _ hn, Multiset.toFinset_singleton]
    refine' Disjoint.mono_left support_single_subset _
    rwa [Finset.disjoint_singleton_left]
#align finsupp.to_finset_to_multiset Finsupp.toFinset_toMultiset

@[simp]
theorem count_toMultiset [DecidableEq α] (f : α →₀ ℕ) (a : α) : f.toMultiset.count a = f a :=
  calc
    f.toMultiset.count a = f.Sum fun x n => (n • {x} : Multiset α).count a :=
      (Multiset.countAddMonoidHom a).map_sum _ f.support
    _ = f.Sum fun x n => n * ({x} : Multiset α).count a := by simp only [Multiset.count_nsmul]
    _ = f a * ({a} : Multiset α).count a :=
      sum_eq_single _
        (fun a' _ H => by simp only [Multiset.count_singleton, if_false, H.symm, mul_zero]) fun H =>
        by simp only [not_mem_support_iff.1 H, zero_mul]
    _ = f a := by rw [Multiset.count_singleton_self, mul_one]
    
#align finsupp.count_to_multiset Finsupp.count_toMultiset

@[simp]
theorem mem_toMultiset (f : α →₀ ℕ) (i : α) : i ∈ f.toMultiset ↔ i ∈ f.support := by
  rw [← Multiset.count_ne_zero, Finsupp.count_toMultiset, Finsupp.mem_support_iff]
#align finsupp.mem_to_multiset Finsupp.mem_toMultiset

end Finsupp

namespace Multiset

/-- Given a multiset `s`, `s.to_finsupp` returns the finitely supported function on `ℕ` given by
the multiplicities of the elements of `s`. -/
def toFinsupp : Multiset α ≃+ (α →₀ ℕ) :=
  Finsupp.toMultiset.symm
#align multiset.to_finsupp Multiset.toFinsupp

@[simp]
theorem toFinsupp_support [DecidableEq α] (s : Multiset α) : s.toFinsupp.support = s.toFinset := by
  convert rfl
#align multiset.to_finsupp_support Multiset.toFinsupp_support

@[simp]
theorem toFinsupp_apply [DecidableEq α] (s : Multiset α) (a : α) : toFinsupp s a = s.count a := by
  convert rfl
#align multiset.to_finsupp_apply Multiset.toFinsupp_apply

theorem toFinsupp_zero : toFinsupp (0 : Multiset α) = 0 :=
  AddEquiv.map_zero _
#align multiset.to_finsupp_zero Multiset.toFinsupp_zero

theorem toFinsupp_add (s t : Multiset α) : toFinsupp (s + t) = toFinsupp s + toFinsupp t :=
  toFinsupp.map_add s t
#align multiset.to_finsupp_add Multiset.toFinsupp_add

@[simp]
theorem toFinsupp_singleton (a : α) : toFinsupp ({a} : Multiset α) = Finsupp.single a 1 :=
  Finsupp.toMultiset.symm_apply_eq.2 <| by simp
#align multiset.to_finsupp_singleton Multiset.toFinsupp_singleton

@[simp]
theorem toFinsupp_toMultiset (s : Multiset α) : s.toFinsupp.toMultiset = s :=
  Finsupp.toMultiset.apply_symm_apply s
#align multiset.to_finsupp_to_multiset Multiset.toFinsupp_toMultiset

theorem toFinsupp_eq_iff {s : Multiset α} {f : α →₀ ℕ} : s.toFinsupp = f ↔ s = f.toMultiset :=
  Finsupp.toMultiset.symm_apply_eq
#align multiset.to_finsupp_eq_iff Multiset.toFinsupp_eq_iff

end Multiset

@[simp]
theorem Finsupp.toMultiset_toFinsupp (f : α →₀ ℕ) : f.toMultiset.toFinsupp = f :=
  Finsupp.toMultiset.symm_apply_apply f
#align finsupp.to_multiset_to_finsupp Finsupp.toMultiset_toFinsupp

/-! ### As an order isomorphism -/


namespace Finsupp

/-- `finsupp.to_multiset` as an order isomorphism. -/
def orderIsoMultiset : (ι →₀ ℕ) ≃o Multiset ι
    where
  toEquiv := toMultiset.toEquiv
  map_rel_iff' f g := by simp [Multiset.le_iff_count, le_def]
#align finsupp.order_iso_multiset Finsupp.orderIsoMultiset

@[simp]
theorem coe_orderIsoMultiset : ⇑(@orderIsoMultiset ι) = toMultiset :=
  rfl
#align finsupp.coe_order_iso_multiset Finsupp.coe_orderIsoMultiset

@[simp]
theorem coe_orderIsoMultiset_symm : ⇑(@orderIsoMultiset ι).symm = Multiset.toFinsupp :=
  rfl
#align finsupp.coe_order_iso_multiset_symm Finsupp.coe_orderIsoMultiset_symm

theorem toMultiset_strictMono : StrictMono (@toMultiset ι) :=
  (@orderIsoMultiset ι).StrictMono
#align finsupp.to_multiset_strict_mono Finsupp.toMultiset_strictMono

theorem sum_id_lt_of_lt (m n : ι →₀ ℕ) (h : m < n) : (m.Sum fun _ => id) < n.Sum fun _ => id :=
  by
  rw [← card_to_multiset, ← card_to_multiset]
  apply Multiset.card_lt_of_lt
  exact to_multiset_strict_mono h
#align finsupp.sum_id_lt_of_lt Finsupp.sum_id_lt_of_lt

variable (ι)

/-- The order on `ι →₀ ℕ` is well-founded. -/
theorem lt_wf : WellFounded (@LT.lt (ι →₀ ℕ) _) :=
  Subrelation.wf sum_id_lt_of_lt <| InvImage.wf _ Nat.lt_wfRel
#align finsupp.lt_wf Finsupp.lt_wf

end Finsupp

theorem Multiset.toFinsupp_strictMono : StrictMono (@Multiset.toFinsupp ι) :=
  (@Finsupp.orderIsoMultiset ι).symm.StrictMono
#align multiset.to_finsupp_strict_mono Multiset.toFinsupp_strictMono

