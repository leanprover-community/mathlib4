/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Int.ModEq
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Fintype

import Mathlib.GroupTheory.Perm.Cycle.Basic

#align_import group_theory.perm.cycle.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Cycle factors of a permutation

Let `β` be a `Fintype` and `f : Equiv.Perm β`.

* `Equiv.Perm.cycleOf`: `f.cycleOf x` is the cycle of `f` that `x` belongs to.
* `Equiv.Perm.cycleFactors`: `f.cycleFactors` is a list of disjoint cyclic permutations
  that multiply to `f`.
-/

open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-!
### `cycleOf`
-/

section CycleOf

variable [DecidableEq α] [Fintype α] {f g : Perm α} {x y : α}

/-- `f.cycleOf x` is the cycle of the permutation `f` to which `x` belongs. -/
def cycleOf (f : Perm α) (x : α) : Perm α :=
  ofSubtype (subtypePerm f fun _ => sameCycle_apply_right.symm : Perm { y // SameCycle f x y })
#align equiv.perm.cycle_of Equiv.Perm.cycleOf

theorem cycleOf_apply (f : Perm α) (x y : α) :
    cycleOf f x y = if SameCycle f x y then f y else y := by
  dsimp only [cycleOf]
  split_ifs with h
  · apply ofSubtype_apply_of_mem
    exact h
  · apply ofSubtype_apply_of_not_mem
    exact h
#align equiv.perm.cycle_of_apply Equiv.Perm.cycleOf_apply

theorem cycleOf_inv (f : Perm α) (x : α) : (cycleOf f x)⁻¹ = cycleOf f⁻¹ x :=
  Equiv.ext fun y => by
    rw [inv_eq_iff_eq, cycleOf_apply, cycleOf_apply]
    split_ifs <;> simp_all [sameCycle_inv, sameCycle_inv_apply_right]
#align equiv.perm.cycle_of_inv Equiv.Perm.cycleOf_inv

@[simp]
theorem cycleOf_pow_apply_self (f : Perm α) (x : α) : ∀ n : ℕ, (cycleOf f x ^ n) x = (f ^ n) x := by
  intro n
  induction' n with n hn
  · rfl
  · rw [pow_succ', mul_apply, cycleOf_apply, hn, if_pos, pow_succ', mul_apply]
    exact ⟨n, rfl⟩
#align equiv.perm.cycle_of_pow_apply_self Equiv.Perm.cycleOf_pow_apply_self

@[simp]
theorem cycleOf_zpow_apply_self (f : Perm α) (x : α) :
    ∀ n : ℤ, (cycleOf f x ^ n) x = (f ^ n) x := by
  intro z
  induction' z with z hz
  · exact cycleOf_pow_apply_self f x z
  · rw [zpow_negSucc, ← inv_pow, cycleOf_inv, zpow_negSucc, ← inv_pow, cycleOf_pow_apply_self]
#align equiv.perm.cycle_of_zpow_apply_self Equiv.Perm.cycleOf_zpow_apply_self

theorem SameCycle.cycleOf_apply : SameCycle f x y → cycleOf f x y = f y :=
  ofSubtype_apply_of_mem _
#align equiv.perm.same_cycle.cycle_of_apply Equiv.Perm.SameCycle.cycleOf_apply

theorem cycleOf_apply_of_not_sameCycle : ¬SameCycle f x y → cycleOf f x y = y :=
  ofSubtype_apply_of_not_mem _
#align equiv.perm.cycle_of_apply_of_not_same_cycle Equiv.Perm.cycleOf_apply_of_not_sameCycle

theorem SameCycle.cycleOf_eq (h : SameCycle f x y) : cycleOf f x = cycleOf f y := by
  ext z
  rw [Equiv.Perm.cycleOf_apply]
  split_ifs with hz
  · exact (h.symm.trans hz).cycleOf_apply.symm
  · exact (cycleOf_apply_of_not_sameCycle (mt h.trans hz)).symm
#align equiv.perm.same_cycle.cycle_of_eq Equiv.Perm.SameCycle.cycleOf_eq

@[simp]
theorem cycleOf_apply_apply_zpow_self (f : Perm α) (x : α) (k : ℤ) :
    cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x := by
  rw [SameCycle.cycleOf_apply]
  · rw [add_comm, zpow_add, zpow_one, mul_apply]
  · exact ⟨k, rfl⟩
#align equiv.perm.cycle_of_apply_apply_zpow_self Equiv.Perm.cycleOf_apply_apply_zpow_self

@[simp]
theorem cycleOf_apply_apply_pow_self (f : Perm α) (x : α) (k : ℕ) :
    cycleOf f x ((f ^ k) x) = (f ^ (k + 1) : Perm α) x := by
  convert cycleOf_apply_apply_zpow_self f x k using 1
#align equiv.perm.cycle_of_apply_apply_pow_self Equiv.Perm.cycleOf_apply_apply_pow_self

@[simp]
theorem cycleOf_apply_apply_self (f : Perm α) (x : α) : cycleOf f x (f x) = f (f x) := by
  convert cycleOf_apply_apply_pow_self f x 1 using 1
#align equiv.perm.cycle_of_apply_apply_self Equiv.Perm.cycleOf_apply_apply_self

@[simp]
theorem cycleOf_apply_self (f : Perm α) (x : α) : cycleOf f x x = f x :=
  SameCycle.rfl.cycleOf_apply
#align equiv.perm.cycle_of_apply_self Equiv.Perm.cycleOf_apply_self

theorem IsCycle.cycleOf_eq (hf : IsCycle f) (hx : f x ≠ x) : cycleOf f x = f :=
  Equiv.ext fun y =>
    if h : SameCycle f x y then by rw [h.cycleOf_apply]
    else by
      rw [cycleOf_apply_of_not_sameCycle h,
        Classical.not_not.1 (mt ((isCycle_iff_sameCycle hx).1 hf).2 h)]
#align equiv.perm.is_cycle.cycle_of_eq Equiv.Perm.IsCycle.cycleOf_eq

@[simp]
theorem cycleOf_eq_one_iff (f : Perm α) : cycleOf f x = 1 ↔ f x = x := by
  simp_rw [ext_iff, cycleOf_apply, one_apply]
  refine ⟨fun h => (if_pos (SameCycle.refl f x)).symm.trans (h x), fun h y => ?_⟩
  by_cases hy : f y = y
  · rw [hy, ite_self]
  · exact if_neg (mt SameCycle.apply_eq_self_iff (by tauto))
#align equiv.perm.cycle_of_eq_one_iff Equiv.Perm.cycleOf_eq_one_iff

@[simp]
theorem cycleOf_self_apply (f : Perm α) (x : α) : cycleOf f (f x) = cycleOf f x :=
  (sameCycle_apply_right.2 SameCycle.rfl).symm.cycleOf_eq
#align equiv.perm.cycle_of_self_apply Equiv.Perm.cycleOf_self_apply

@[simp]
theorem cycleOf_self_apply_pow (f : Perm α) (n : ℕ) (x : α) : cycleOf f ((f ^ n) x) = cycleOf f x :=
  SameCycle.rfl.pow_left.cycleOf_eq
#align equiv.perm.cycle_of_self_apply_pow Equiv.Perm.cycleOf_self_apply_pow

@[simp]
theorem cycleOf_self_apply_zpow (f : Perm α) (n : ℤ) (x : α) :
    cycleOf f ((f ^ n) x) = cycleOf f x :=
  SameCycle.rfl.zpow_left.cycleOf_eq
#align equiv.perm.cycle_of_self_apply_zpow Equiv.Perm.cycleOf_self_apply_zpow

protected theorem IsCycle.cycleOf (hf : IsCycle f) : cycleOf f x = if f x = x then 1 else f := by
  by_cases hx : f x = x
  · rwa [if_pos hx, cycleOf_eq_one_iff]
  · rwa [if_neg hx, hf.cycleOf_eq]
#align equiv.perm.is_cycle.cycle_of Equiv.Perm.IsCycle.cycleOf

theorem cycleOf_one (x : α) : cycleOf 1 x = 1 :=
  (cycleOf_eq_one_iff 1).mpr rfl
#align equiv.perm.cycle_of_one Equiv.Perm.cycleOf_one

theorem isCycle_cycleOf (f : Perm α) (hx : f x ≠ x) : IsCycle (cycleOf f x) :=
  have : cycleOf f x x ≠ x := by rwa [SameCycle.rfl.cycleOf_apply]
  (isCycle_iff_sameCycle this).2 @fun y =>
    ⟨fun h => mt h.apply_eq_self_iff.2 this, fun h =>
      if hxy : SameCycle f x y then
        let ⟨i, hi⟩ := hxy
        ⟨i, by rw [cycleOf_zpow_apply_self, hi]⟩
      else by
        rw [cycleOf_apply_of_not_sameCycle hxy] at h
        exact (h rfl).elim⟩
#align equiv.perm.is_cycle_cycle_of Equiv.Perm.isCycle_cycleOf

@[simp]
theorem two_le_card_support_cycleOf_iff : 2 ≤ card (cycleOf f x).support ↔ f x ≠ x := by
  refine ⟨fun h => ?_, fun h => by simpa using (isCycle_cycleOf _ h).two_le_card_support⟩
  contrapose! h
  rw [← cycleOf_eq_one_iff] at h
  simp [h]
#align equiv.perm.two_le_card_support_cycle_of_iff Equiv.Perm.two_le_card_support_cycleOf_iff

@[simp] lemma support_cycleOf_nonempty : (cycleOf f x).support.Nonempty ↔ f x ≠ x := by
  rw [← two_le_card_support_cycleOf_iff, ← card_pos, ← Nat.succ_le_iff]
  exact ⟨fun h => Or.resolve_left h.eq_or_lt (card_support_ne_one _).symm, zero_lt_two.trans_le⟩
#align equiv.perm.card_support_cycle_of_pos_iff Equiv.Perm.support_cycleOf_nonempty

@[deprecated support_cycleOf_nonempty (since := "2024-06-16")]
theorem card_support_cycleOf_pos_iff : 0 < card (cycleOf f x).support ↔ f x ≠ x := by
  rw [card_pos, support_cycleOf_nonempty]

theorem pow_mod_orderOf_cycleOf_apply (f : Perm α) (n : ℕ) (x : α) :
    (f ^ (n % orderOf (cycleOf f x))) x = (f ^ n) x := by
  rw [← cycleOf_pow_apply_self f, ← cycleOf_pow_apply_self f, pow_mod_orderOf]
#align equiv.perm.pow_apply_eq_pow_mod_order_of_cycle_of_apply Equiv.Perm.pow_mod_orderOf_cycleOf_apply

theorem cycleOf_mul_of_apply_right_eq_self (h : Commute f g) (x : α) (hx : g x = x) :
    (f * g).cycleOf x = f.cycleOf x := by
  ext y
  by_cases hxy : (f * g).SameCycle x y
  · obtain ⟨z, rfl⟩ := hxy
    rw [cycleOf_apply_apply_zpow_self]
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [cycleOf_apply_of_not_sameCycle hxy, cycleOf_apply_of_not_sameCycle]
    contrapose! hxy
    obtain ⟨z, rfl⟩ := hxy
    refine ⟨z, ?_⟩
    simp [h.mul_zpow, zpow_apply_eq_self_of_apply_eq_self hx]
#align equiv.perm.cycle_of_mul_of_apply_right_eq_self Equiv.Perm.cycleOf_mul_of_apply_right_eq_self

theorem Disjoint.cycleOf_mul_distrib (h : f.Disjoint g) (x : α) :
    (f * g).cycleOf x = f.cycleOf x * g.cycleOf x := by
  cases' (disjoint_iff_eq_or_eq.mp h) x with hfx hgx
  · simp [h.commute.eq, cycleOf_mul_of_apply_right_eq_self h.symm.commute, hfx]
  · simp [cycleOf_mul_of_apply_right_eq_self h.commute, hgx]
#align equiv.perm.disjoint.cycle_of_mul_distrib Equiv.Perm.Disjoint.cycleOf_mul_distrib

theorem support_cycleOf_eq_nil_iff : (f.cycleOf x).support = ∅ ↔ x ∉ f.support := by simp
#align equiv.perm.support_cycle_of_eq_nil_iff Equiv.Perm.support_cycleOf_eq_nil_iff

theorem support_cycleOf_le (f : Perm α) (x : α) : support (f.cycleOf x) ≤ support f := by
  intro y hy
  rw [mem_support, cycleOf_apply] at hy
  split_ifs at hy
  · exact mem_support.mpr hy
  · exact absurd rfl hy
#align equiv.perm.support_cycle_of_le Equiv.Perm.support_cycleOf_le

theorem mem_support_cycleOf_iff : y ∈ support (f.cycleOf x) ↔ SameCycle f x y ∧ x ∈ support f := by
  by_cases hx : f x = x
  · rw [(cycleOf_eq_one_iff _).mpr hx]
    simp [hx]
  · rw [mem_support, cycleOf_apply]
    split_ifs with hy
    · simp only [hx, hy, iff_true_iff, Ne, not_false_iff, and_self_iff, mem_support]
      rcases hy with ⟨k, rfl⟩
      rw [← not_mem_support]
      simpa using hx
    · simpa [hx] using hy
#align equiv.perm.mem_support_cycle_of_iff Equiv.Perm.mem_support_cycleOf_iff

theorem mem_support_cycleOf_iff' (hx : f x ≠ x) : y ∈ support (f.cycleOf x) ↔ SameCycle f x y := by
  rw [mem_support_cycleOf_iff, and_iff_left (mem_support.2 hx)]
#align equiv.perm.mem_support_cycle_of_iff' Equiv.Perm.mem_support_cycleOf_iff'

theorem SameCycle.mem_support_iff (h : SameCycle f x y) : x ∈ support f ↔ y ∈ support f :=
  ⟨fun hx => support_cycleOf_le f x (mem_support_cycleOf_iff.mpr ⟨h, hx⟩), fun hy =>
    support_cycleOf_le f y (mem_support_cycleOf_iff.mpr ⟨h.symm, hy⟩)⟩
#align equiv.perm.same_cycle.mem_support_iff Equiv.Perm.SameCycle.mem_support_iff

theorem pow_mod_card_support_cycleOf_self_apply (f : Perm α) (n : ℕ) (x : α) :
    (f ^ (n % (f.cycleOf x).support.card)) x = (f ^ n) x := by
  by_cases hx : f x = x
  · rw [pow_apply_eq_self_of_apply_eq_self hx, pow_apply_eq_self_of_apply_eq_self hx]
  · rw [← cycleOf_pow_apply_self, ← cycleOf_pow_apply_self f, ← (isCycle_cycleOf f hx).orderOf,
      pow_mod_orderOf]
#align equiv.perm.pow_mod_card_support_cycle_of_self_apply Equiv.Perm.pow_mod_card_support_cycleOf_self_apply

/-- `x` is in the support of `f` iff `Equiv.Perm.cycle_of f x` is a cycle. -/
theorem isCycle_cycleOf_iff (f : Perm α) : IsCycle (cycleOf f x) ↔ f x ≠ x := by
  refine ⟨fun hx => ?_, f.isCycle_cycleOf⟩
  rw [Ne, ← cycleOf_eq_one_iff f]
  exact hx.ne_one
#align equiv.perm.is_cycle_cycle_of_iff Equiv.Perm.isCycle_cycleOf_iff

theorem isCycleOn_support_cycleOf (f : Perm α) (x : α) : f.IsCycleOn (f.cycleOf x).support :=
  ⟨f.bijOn <| by
    refine fun _ ↦ ⟨fun h ↦ mem_support_cycleOf_iff.2 ?_, fun h ↦ mem_support_cycleOf_iff.2 ?_⟩
    · exact ⟨sameCycle_apply_right.1 (mem_support_cycleOf_iff.1 h).1,
      (mem_support_cycleOf_iff.1 h).2⟩
    · exact ⟨sameCycle_apply_right.2 (mem_support_cycleOf_iff.1 h).1,
      (mem_support_cycleOf_iff.1 h).2⟩
    , fun a ha b hb =>
      by
        rw [mem_coe, mem_support_cycleOf_iff] at ha hb
        exact ha.1.symm.trans hb.1⟩
#align equiv.perm.is_cycle_on_support_cycle_of Equiv.Perm.isCycleOn_support_cycleOf

theorem SameCycle.exists_pow_eq_of_mem_support (h : SameCycle f x y) (hx : x ∈ f.support) :
    ∃ i < (f.cycleOf x).support.card, (f ^ i) x = y := by
  rw [mem_support] at hx
  exact Equiv.Perm.IsCycleOn.exists_pow_eq (b := y) (f.isCycleOn_support_cycleOf x)
    (by rw [mem_support_cycleOf_iff' hx]) (by rwa [mem_support_cycleOf_iff' hx])
#align equiv.perm.same_cycle.exists_pow_eq_of_mem_support Equiv.Perm.SameCycle.exists_pow_eq_of_mem_support

theorem SameCycle.exists_pow_eq (f : Perm α) (h : SameCycle f x y) :
    ∃ i : ℕ, 0 < i ∧ i ≤ (f.cycleOf x).support.card + 1 ∧ (f ^ i) x = y := by
  by_cases hx : x ∈ f.support
  · obtain ⟨k, hk, hk'⟩ := h.exists_pow_eq_of_mem_support hx
    cases' k with k
    · refine ⟨(f.cycleOf x).support.card, ?_, self_le_add_right _ _, ?_⟩
      · refine zero_lt_one.trans (one_lt_card_support_of_ne_one ?_)
        simpa using hx
      · simp only [Nat.zero_eq, pow_zero, coe_one, id_eq] at hk'
        subst hk'
        rw [← (isCycle_cycleOf _ <| mem_support.1 hx).orderOf, ← cycleOf_pow_apply_self,
          pow_orderOf_eq_one, one_apply]
    · exact ⟨k + 1, by simp, Nat.le_succ_of_le hk.le, hk'⟩
  · refine ⟨1, zero_lt_one, by simp, ?_⟩
    obtain ⟨k, rfl⟩ := h
    rw [not_mem_support] at hx
    rw [pow_apply_eq_self_of_apply_eq_self hx, zpow_apply_eq_self_of_apply_eq_self hx]
#align equiv.perm.same_cycle.exists_pow_eq Equiv.Perm.SameCycle.exists_pow_eq

end CycleOf


/-!
### `cycleFactors`
-/

section cycleFactors

open scoped List in
/-- Given a list `l : List α` and a permutation `f : Perm α` whose nonfixed points are all in `l`,
  recursively factors `f` into cycles. -/
def cycleFactorsAux [DecidableEq α] [Fintype α] :
    ∀ (l : List α) (f : Perm α),
      (∀ {x}, f x ≠ x → x ∈ l) →
        { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } := by
  intro l f h
  exact match l with
  | [] => ⟨[], by
      { simp only [imp_false, List.Pairwise.nil, List.not_mem_nil, forall_const, and_true_iff,
          forall_prop_of_false, Classical.not_not, not_false_iff, List.prod_nil] at *
        ext
        simp [*]}⟩
  | x::l =>
    if hx : f x = x then cycleFactorsAux l f (by
        intro y hy; exact List.mem_of_ne_of_mem (fun h => hy (by rwa [h])) (h hy))
    else
      let ⟨m, hm₁, hm₂, hm₃⟩ :=
        cycleFactorsAux l ((cycleOf f x)⁻¹ * f) (by
        intro y hy
        exact List.mem_of_ne_of_mem
            (fun h : y = x => by
              rw [h, mul_apply, Ne, inv_eq_iff_eq, cycleOf_apply_self] at hy
              exact hy rfl)
            (h fun h : f y = y => by
              rw [mul_apply, h, Ne, inv_eq_iff_eq, cycleOf_apply] at hy
              split_ifs at hy <;> tauto))
      ⟨cycleOf f x::m, by
        rw [List.prod_cons, hm₁]
        simp,
        fun g hg ↦ ((List.mem_cons).1 hg).elim (fun hg => hg.symm ▸ isCycle_cycleOf _ hx) (hm₂ g),
        List.pairwise_cons.2
          ⟨fun g hg y =>
            or_iff_not_imp_left.2 fun hfy =>
              have hxy : SameCycle f x y :=
                Classical.not_not.1 (mt cycleOf_apply_of_not_sameCycle hfy)
              have hgm : (g::m.erase g) ~ m :=
                List.cons_perm_iff_perm_erase.2 ⟨hg, List.Perm.refl _⟩
              have : ∀ h ∈ m.erase g, Disjoint g h :=
                (List.pairwise_cons.1 ((hgm.pairwise_iff Disjoint.symm).2 hm₃)).1
              by_cases id fun hgy : g y ≠ y =>
                (disjoint_prod_right _ this y).resolve_right <| by
                  have hsc : SameCycle f⁻¹ x (f y) := by
                    rwa [sameCycle_inv, sameCycle_apply_right]
                  rw [disjoint_prod_perm hm₃ hgm.symm, List.prod_cons,
                      ← eq_inv_mul_iff_mul_eq] at hm₁
                  rwa [hm₁, mul_apply, mul_apply, cycleOf_inv, hsc.cycleOf_apply, inv_apply_self,
                    inv_eq_iff_eq, eq_comm],
            hm₃⟩⟩
#align equiv.perm.cycle_factors_aux Equiv.Perm.cycleFactorsAux

theorem mem_list_cycles_iff {α : Type*} [Finite α] {l : List (Perm α)}
    (h1 : ∀ σ : Perm α, σ ∈ l → σ.IsCycle) (h2 : l.Pairwise Disjoint) {σ : Perm α} :
    σ ∈ l ↔ σ.IsCycle ∧ ∀ a, σ a ≠ a → σ a = l.prod a := by
  suffices σ.IsCycle → (σ ∈ l ↔ ∀ a, σ a ≠ a → σ a = l.prod a) by
    exact ⟨fun hσ => ⟨h1 σ hσ, (this (h1 σ hσ)).mp hσ⟩, fun hσ => (this hσ.1).mpr hσ.2⟩
  intro h3
  classical
    cases nonempty_fintype α
    constructor
    · intro h a ha
      exact eq_on_support_mem_disjoint h h2 _ (mem_support.mpr ha)
    · intro h
      have hσl : σ.support ⊆ l.prod.support := by
        intro x hx
        rw [mem_support] at hx
        rwa [mem_support, ← h _ hx]
      obtain ⟨a, ha, -⟩ := id h3
      rw [← mem_support] at ha
      obtain ⟨τ, hτ, hτa⟩ := exists_mem_support_of_mem_support_prod (hσl ha)
      have hτl : ∀ x ∈ τ.support, τ x = l.prod x := eq_on_support_mem_disjoint hτ h2
      have key : ∀ x ∈ σ.support ∩ τ.support, σ x = τ x := by
        intro x hx
        rw [h x (mem_support.mp (mem_of_mem_inter_left hx)), hτl x (mem_of_mem_inter_right hx)]
      convert hτ
      refine h3.eq_on_support_inter_nonempty_congr (h1 _ hτ) key ?_ ha
      exact key a (mem_inter_of_mem ha hτa)
#align equiv.perm.mem_list_cycles_iff Equiv.Perm.mem_list_cycles_iff

open scoped List in
theorem list_cycles_perm_list_cycles {α : Type*} [Finite α] {l₁ l₂ : List (Perm α)}
    (h₀ : l₁.prod = l₂.prod) (h₁l₁ : ∀ σ : Perm α, σ ∈ l₁ → σ.IsCycle)
    (h₁l₂ : ∀ σ : Perm α, σ ∈ l₂ → σ.IsCycle) (h₂l₁ : l₁.Pairwise Disjoint)
    (h₂l₂ : l₂.Pairwise Disjoint) : l₁ ~ l₂ := by
  classical
    refine
      (List.perm_ext_iff_of_nodup (nodup_of_pairwise_disjoint_cycles h₁l₁ h₂l₁)
            (nodup_of_pairwise_disjoint_cycles h₁l₂ h₂l₂)).mpr
        fun σ => ?_
    by_cases hσ : σ.IsCycle
    · obtain _ := not_forall.mp (mt ext hσ.ne_one)
      rw [mem_list_cycles_iff h₁l₁ h₂l₁, mem_list_cycles_iff h₁l₂ h₂l₂, h₀]
    · exact iff_of_false (mt (h₁l₁ σ) hσ) (mt (h₁l₂ σ) hσ)
#align equiv.perm.list_cycles_perm_list_cycles Equiv.Perm.list_cycles_perm_list_cycles

/-- Factors a permutation `f` into a list of disjoint cyclic permutations that multiply to `f`. -/
def cycleFactors [Fintype α] [LinearOrder α] (f : Perm α) :
    { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } :=
  cycleFactorsAux (sort (α := α) (· ≤ ·) univ) f (fun {_ _} ↦ (mem_sort _).2 (mem_univ _))
#align equiv.perm.cycle_factors Equiv.Perm.cycleFactors

/-- Factors a permutation `f` into a list of disjoint cyclic permutations that multiply to `f`,
  without a linear order. -/
def truncCycleFactors [DecidableEq α] [Fintype α] (f : Perm α) :
    Trunc { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } :=
  Quotient.recOnSubsingleton (@univ α _).1 (fun l h => Trunc.mk (cycleFactorsAux l f (h _)))
    (show ∀ x, f x ≠ x → x ∈ (@univ α _).1 from fun _ _ => mem_univ _)
#align equiv.perm.trunc_cycle_factors Equiv.Perm.truncCycleFactors

section CycleFactorsFinset

variable [DecidableEq α] [Fintype α] (f : Perm α)

/-- Factors a permutation `f` into a `Finset` of disjoint cyclic permutations that multiply to `f`.
-/
def cycleFactorsFinset : Finset (Perm α) :=
  (truncCycleFactors f).lift
    (fun l : { l : List (Perm α) // l.prod = f ∧ (∀ g ∈ l, IsCycle g) ∧ l.Pairwise Disjoint } =>
      l.val.toFinset)
    fun ⟨_, hl⟩ ⟨_, hl'⟩ =>
    List.toFinset_eq_of_perm _ _
      (list_cycles_perm_list_cycles (hl'.left.symm ▸ hl.left) hl.right.left hl'.right.left
        hl.right.right hl'.right.right)
#align equiv.perm.cycle_factors_finset Equiv.Perm.cycleFactorsFinset

open scoped List in
theorem cycleFactorsFinset_eq_list_toFinset {σ : Perm α} {l : List (Perm α)} (hn : l.Nodup) :
    σ.cycleFactorsFinset = l.toFinset ↔
      (∀ f : Perm α, f ∈ l → f.IsCycle) ∧ l.Pairwise Disjoint ∧ l.prod = σ := by
  obtain ⟨⟨l', hp', hc', hd'⟩, hl⟩ := Trunc.exists_rep σ.truncCycleFactors
  have ht : cycleFactorsFinset σ = l'.toFinset := by
    rw [cycleFactorsFinset, ← hl, Trunc.lift_mk]
  rw [ht]
  constructor
  · intro h
    have hn' : l'.Nodup := nodup_of_pairwise_disjoint_cycles hc' hd'
    have hperm : l ~ l' := List.perm_of_nodup_nodup_toFinset_eq hn hn' h.symm
    refine ⟨?_, ?_, ?_⟩
    · exact fun _ h => hc' _ (hperm.subset h)
    · have := List.Perm.pairwise_iff (@Disjoint.symmetric _) hperm
      rwa [this]
    · rw [← hp', hperm.symm.prod_eq']
      refine hd'.imp ?_
      exact Disjoint.commute
  · rintro ⟨hc, hd, hp⟩
    refine List.toFinset_eq_of_perm _ _ ?_
    refine list_cycles_perm_list_cycles ?_ hc' hc hd' hd
    rw [hp, hp']
#align equiv.perm.cycle_factors_finset_eq_list_to_finset Equiv.Perm.cycleFactorsFinset_eq_list_toFinset

theorem cycleFactorsFinset_eq_finset {σ : Perm α} {s : Finset (Perm α)} :
    σ.cycleFactorsFinset = s ↔
      (∀ f : Perm α, f ∈ s → f.IsCycle) ∧
        ∃ h : (s : Set (Perm α)).Pairwise Disjoint,
          s.noncommProd id (h.mono' fun _ _ => Disjoint.commute) = σ := by
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  simp [cycleFactorsFinset_eq_list_toFinset, hl]
#align equiv.perm.cycle_factors_finset_eq_finset Equiv.Perm.cycleFactorsFinset_eq_finset

theorem cycleFactorsFinset_pairwise_disjoint :
    (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint :=
  (cycleFactorsFinset_eq_finset.mp rfl).2.choose
#align equiv.perm.cycle_factors_finset_pairwise_disjoint Equiv.Perm.cycleFactorsFinset_pairwise_disjoint

theorem cycleFactorsFinset_mem_commute : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute :=
  (cycleFactorsFinset_pairwise_disjoint _).mono' fun _ _ => Disjoint.commute
#align equiv.perm.cycle_factors_finset_mem_commute Equiv.Perm.cycleFactorsFinset_mem_commute

/-- The product of cycle factors is equal to the original `f : perm α`. -/
theorem cycleFactorsFinset_noncommProd
    (comm : (cycleFactorsFinset f : Set (Perm α)).Pairwise Commute :=
      cycleFactorsFinset_mem_commute f) :
    f.cycleFactorsFinset.noncommProd id comm = f :=
  (cycleFactorsFinset_eq_finset.mp rfl).2.choose_spec
#align equiv.perm.cycle_factors_finset_noncomm_prod Equiv.Perm.cycleFactorsFinset_noncommProd

theorem mem_cycleFactorsFinset_iff {f p : Perm α} :
    p ∈ cycleFactorsFinset f ↔ p.IsCycle ∧ ∀ a ∈ p.support, p a = f a := by
  obtain ⟨l, hl, hl'⟩ := f.cycleFactorsFinset.exists_list_nodup_eq
  rw [← hl']
  rw [eq_comm, cycleFactorsFinset_eq_list_toFinset hl] at hl'
  simpa [List.mem_toFinset, Ne, ← hl'.right.right] using
    mem_list_cycles_iff hl'.left hl'.right.left
#align equiv.perm.mem_cycle_factors_finset_iff Equiv.Perm.mem_cycleFactorsFinset_iff

theorem cycleOf_mem_cycleFactorsFinset_iff {f : Perm α} {x : α} :
    cycleOf f x ∈ cycleFactorsFinset f ↔ x ∈ f.support := by
  rw [mem_cycleFactorsFinset_iff]
  constructor
  · rintro ⟨hc, _⟩
    contrapose! hc
    rw [not_mem_support, ← cycleOf_eq_one_iff] at hc
    simp [hc]
  · intro hx
    refine ⟨isCycle_cycleOf _ (mem_support.mp hx), ?_⟩
    intro y hy
    rw [mem_support] at hy
    rw [cycleOf_apply]
    split_ifs with H
    · rfl
    · rw [cycleOf_apply_of_not_sameCycle H] at hy
      contradiction
#align equiv.perm.cycle_of_mem_cycle_factors_finset_iff Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff

theorem mem_cycleFactorsFinset_support_le {p f : Perm α} (h : p ∈ cycleFactorsFinset f) :
    p.support ≤ f.support := by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x hx
  rwa [mem_support, ← h.right x hx, ← mem_support]
#align equiv.perm.mem_cycle_factors_finset_support_le Equiv.Perm.mem_cycleFactorsFinset_support_le

theorem cycleFactorsFinset_eq_empty_iff {f : Perm α} : cycleFactorsFinset f = ∅ ↔ f = 1 := by
  simpa [cycleFactorsFinset_eq_finset] using eq_comm
#align equiv.perm.cycle_factors_finset_eq_empty_iff Equiv.Perm.cycleFactorsFinset_eq_empty_iff

@[simp]
theorem cycleFactorsFinset_one : cycleFactorsFinset (1 : Perm α) = ∅ := by
  simp [cycleFactorsFinset_eq_empty_iff]
#align equiv.perm.cycle_factors_finset_one Equiv.Perm.cycleFactorsFinset_one

@[simp]
theorem cycleFactorsFinset_eq_singleton_self_iff {f : Perm α} :
    f.cycleFactorsFinset = {f} ↔ f.IsCycle := by simp [cycleFactorsFinset_eq_finset]
#align equiv.perm.cycle_factors_finset_eq_singleton_self_iff Equiv.Perm.cycleFactorsFinset_eq_singleton_self_iff

theorem IsCycle.cycleFactorsFinset_eq_singleton {f : Perm α} (hf : IsCycle f) :
    f.cycleFactorsFinset = {f} :=
  cycleFactorsFinset_eq_singleton_self_iff.mpr hf
#align equiv.perm.is_cycle.cycle_factors_finset_eq_singleton Equiv.Perm.IsCycle.cycleFactorsFinset_eq_singleton

theorem cycleFactorsFinset_eq_singleton_iff {f g : Perm α} :
    f.cycleFactorsFinset = {g} ↔ f.IsCycle ∧ f = g := by
  suffices f = g → (g.IsCycle ↔ f.IsCycle) by
    rw [cycleFactorsFinset_eq_finset]
    simpa [eq_comm]
  rintro rfl
  exact Iff.rfl
#align equiv.perm.cycle_factors_finset_eq_singleton_iff Equiv.Perm.cycleFactorsFinset_eq_singleton_iff

/-- Two permutations `f g : Perm α` have the same cycle factors iff they are the same. -/
theorem cycleFactorsFinset_injective : Function.Injective (@cycleFactorsFinset α _ _) := by
  intro f g h
  rw [← cycleFactorsFinset_noncommProd f]
  simpa [h] using cycleFactorsFinset_noncommProd g
#align equiv.perm.cycle_factors_finset_injective Equiv.Perm.cycleFactorsFinset_injective

theorem Disjoint.disjoint_cycleFactorsFinset {f g : Perm α} (h : Disjoint f g) :
    _root_.Disjoint (cycleFactorsFinset f) (cycleFactorsFinset g) := by
  rw [disjoint_iff_disjoint_support] at h
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [mem_cycleFactorsFinset_iff, mem_support] at hx hy
  obtain ⟨⟨⟨a, ha, -⟩, hf⟩, -, hg⟩ := hx, hy
  have := h.le_bot (by simp [ha, ← hf a ha, ← hg a ha] : a ∈ f.support ∩ g.support)
  tauto
#align equiv.perm.disjoint.disjoint_cycle_factors_finset Equiv.Perm.Disjoint.disjoint_cycleFactorsFinset

theorem Disjoint.cycleFactorsFinset_mul_eq_union {f g : Perm α} (h : Disjoint f g) :
    cycleFactorsFinset (f * g) = cycleFactorsFinset f ∪ cycleFactorsFinset g := by
  rw [cycleFactorsFinset_eq_finset]
  refine ⟨?_, ?_, ?_⟩
  · simp [or_imp, mem_cycleFactorsFinset_iff, forall_swap]
  · rw [coe_union, Set.pairwise_union_of_symmetric Disjoint.symmetric]
    exact
      ⟨cycleFactorsFinset_pairwise_disjoint _, cycleFactorsFinset_pairwise_disjoint _,
        fun x hx y hy _ =>
        h.mono (mem_cycleFactorsFinset_support_le hx) (mem_cycleFactorsFinset_support_le hy)⟩
  · rw [noncommProd_union_of_disjoint h.disjoint_cycleFactorsFinset]
    rw [cycleFactorsFinset_noncommProd, cycleFactorsFinset_noncommProd]
#align equiv.perm.disjoint.cycle_factors_finset_mul_eq_union Equiv.Perm.Disjoint.cycleFactorsFinset_mul_eq_union

theorem disjoint_mul_inv_of_mem_cycleFactorsFinset {f g : Perm α} (h : f ∈ cycleFactorsFinset g) :
    Disjoint (g * f⁻¹) f := by
  rw [mem_cycleFactorsFinset_iff] at h
  intro x
  by_cases hx : f x = x
  · exact Or.inr hx
  · refine Or.inl ?_
    rw [mul_apply, ← h.right, apply_inv_self]
    rwa [← support_inv, apply_mem_support, support_inv, mem_support]
#align equiv.perm.disjoint_mul_inv_of_mem_cycle_factors_finset Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset

/-- If c is a cycle, a ∈ c.support and c is a cycle of f, then `c = f.cycleOf a` -/
theorem cycle_is_cycleOf {f c : Equiv.Perm α} {a : α} (ha : a ∈ c.support)
    (hc : c ∈ f.cycleFactorsFinset) : c = f.cycleOf a := by
  suffices f.cycleOf a = c.cycleOf a by
    rw [this]
    apply symm
    exact
      Equiv.Perm.IsCycle.cycleOf_eq (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).left
        (Equiv.Perm.mem_support.mp ha)
  let hfc := (Equiv.Perm.disjoint_mul_inv_of_mem_cycleFactorsFinset hc).symm
  let hfc2 := Perm.Disjoint.commute hfc
  rw [← Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hfc2]
  · simp only [hfc2.eq, inv_mul_cancel_right]
  -- `a` is in the support of `c`, hence it is not in the support of `g c⁻¹`
  exact
    Equiv.Perm.not_mem_support.mp
      (Finset.disjoint_left.mp (Equiv.Perm.Disjoint.disjoint_support hfc) ha)
#align equiv.perm.cycle_is_cycle_of Equiv.Perm.cycle_is_cycleOf

end CycleFactorsFinset

@[elab_as_elim]
theorem cycle_induction_on [Finite β] (P : Perm β → Prop) (σ : Perm β) (base_one : P 1)
    (base_cycles : ∀ σ : Perm β, σ.IsCycle → P σ)
    (induction_disjoint : ∀ σ τ : Perm β,
      Disjoint σ τ → IsCycle σ → P σ → P τ → P (σ * τ)) : P σ := by
  cases nonempty_fintype β
  suffices ∀ l : List (Perm β),
      (∀ τ : Perm β, τ ∈ l → τ.IsCycle) → l.Pairwise Disjoint → P l.prod by
    classical
      let x := σ.truncCycleFactors.out
      exact (congr_arg P x.2.1).mp (this x.1 x.2.2.1 x.2.2.2)
  intro l
  induction' l with σ l ih
  · exact fun _ _ => base_one
  · intro h1 h2
    rw [List.prod_cons]
    exact
      induction_disjoint σ l.prod (disjoint_prod_right _ (List.pairwise_cons.mp h2).1)
        (h1 _ (List.mem_cons_self _ _)) (base_cycles σ (h1 σ (l.mem_cons_self σ)))
        (ih (fun τ hτ => h1 τ (List.mem_cons_of_mem σ hτ)) h2.of_cons)
#align equiv.perm.cycle_induction_on Equiv.Perm.cycle_induction_on

theorem cycleFactorsFinset_mul_inv_mem_eq_sdiff [DecidableEq α] [Fintype α] {f g : Perm α}
    (h : f ∈ cycleFactorsFinset g) : cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f} := by
  revert f
  refine
    cycle_induction_on (P := fun {g : Perm α} ↦
      ∀ {f}, (f ∈ cycleFactorsFinset g)
        → cycleFactorsFinset (g * f⁻¹) = cycleFactorsFinset g \ {f}) _ ?_ ?_ ?_
  · simp
  · intro σ hσ f hf
    simp only [cycleFactorsFinset_eq_singleton_self_iff.mpr hσ, mem_singleton] at hf ⊢
    simp [hf]
  · intro σ τ hd _ hσ hτ f
    simp_rw [hd.cycleFactorsFinset_mul_eq_union, mem_union]
    -- if only `wlog` could work here...
    rintro (hf | hf)
    · rw [hd.commute.eq, union_comm, union_sdiff_distrib, sdiff_singleton_eq_erase,
        erase_eq_of_not_mem, mul_assoc, Disjoint.cycleFactorsFinset_mul_eq_union, hσ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        cases' hd.symm x with hx hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        not_mem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem hf H))
    · rw [union_sdiff_distrib, sdiff_singleton_eq_erase, erase_eq_of_not_mem, mul_assoc,
        Disjoint.cycleFactorsFinset_mul_eq_union, hτ hf]
      · rw [mem_cycleFactorsFinset_iff] at hf
        intro x
        cases' hd x with hx hx
        · exact Or.inl hx
        · refine Or.inr ?_
          by_cases hfx : f x = x
          · rw [← hfx]
            simpa [hx] using hfx.symm
          · rw [mul_apply]
            rw [← hf.right _ (mem_support.mpr hfx)] at hx
            contradiction
      · exact fun H =>
        not_mem_empty _ (hd.disjoint_cycleFactorsFinset.le_bot (mem_inter_of_mem H hf))
#align equiv.perm.cycle_factors_finset_mul_inv_mem_eq_sdiff Equiv.Perm.cycleFactorsFinset_mul_inv_mem_eq_sdiff

end cycleFactors

end Perm

end Equiv
