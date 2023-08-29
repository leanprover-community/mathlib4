/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Combinatorics.Partition
import Mathlib.Data.List.Rotate
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.NormNum.GCD

#align_import group_theory.perm.cycle.type from "leanprover-community/mathlib"@"47adfab39a11a072db552f47594bf8ed2cf8a722"

/-!
# Cycle Types

In this file we define the cycle type of a permutation.

## Main definitions

- `Equiv.Perm.cycleType σ` where `σ` is a permutation of a `Fintype`
- `Equiv.Perm.partition σ` where `σ` is a permutation of a `Fintype`

## Main results

- `sum_cycleType` : The sum of `σ.cycleType` equals `σ.support.card`
- `lcm_cycleType` : The lcm of `σ.cycleType` equals `orderOf σ`
- `isConj_iff_cycleType_eq` : Two permutations are conjugate if and only if they have the same
  cycle type.
- `exists_prime_orderOf_dvd_card`: For every prime `p` dividing the order of a finite group `G`
  there exists an element of order `p` in `G`. This is known as Cauchy's theorem.
-/


namespace Equiv.Perm

open Equiv List Multiset

variable {α : Type*} [Fintype α]

section CycleType

variable [DecidableEq α]

/-- The cycle type of a permutation -/
def cycleType (σ : Perm α) : Multiset ℕ :=
  σ.cycleFactorsFinset.1.map (Finset.card ∘ support)
#align equiv.perm.cycle_type Equiv.Perm.cycleType

theorem cycleType_def (σ : Perm α) :
    σ.cycleType = σ.cycleFactorsFinset.1.map (Finset.card ∘ support) :=
  rfl
#align equiv.perm.cycle_type_def Equiv.Perm.cycleType_def

theorem cycleType_eq' {σ : Perm α} (s : Finset (Perm α)) (h1 : ∀ f : Perm α, f ∈ s → f.IsCycle)
    (h2 : (s : Set (Perm α)).Pairwise Disjoint)
    (h0 : s.noncommProd id (h2.imp fun _ _ => Disjoint.commute) = σ) :
    σ.cycleType = s.1.map (Finset.card ∘ support) := by
  rw [cycleType_def]
  -- ⊢ map (Finset.card ∘ support) (cycleFactorsFinset σ).val = map (Finset.card ∘  …
  congr
  -- ⊢ cycleFactorsFinset σ = s
  rw [cycleFactorsFinset_eq_finset]
  -- ⊢ (∀ (f : Perm α), f ∈ s → IsCycle f) ∧ ∃ h, Finset.noncommProd s id (_ : Set. …
  exact ⟨h1, h2, h0⟩
  -- 🎉 no goals
#align equiv.perm.cycle_type_eq' Equiv.Perm.cycleType_eq'

theorem cycleType_eq {σ : Perm α} (l : List (Perm α)) (h0 : l.prod = σ)
    (h1 : ∀ σ : Perm α, σ ∈ l → σ.IsCycle) (h2 : l.Pairwise Disjoint) :
    σ.cycleType = l.map (Finset.card ∘ support) := by
  have hl : l.Nodup := nodup_of_pairwise_disjoint_cycles h1 h2
  -- ⊢ cycleType σ = ↑(List.map (Finset.card ∘ support) l)
  rw [cycleType_eq' l.toFinset]
  · simp [List.dedup_eq_self.mpr hl, (· ∘ ·)]
    -- 🎉 no goals
  · simpa using h1
    -- 🎉 no goals
  · simpa [hl] using h2
    -- 🎉 no goals
  · simp [hl, h0]
    -- 🎉 no goals
#align equiv.perm.cycle_type_eq Equiv.Perm.cycleType_eq

@[simp] -- porting note: new attr
theorem cycleType_eq_zero {σ : Perm α} : σ.cycleType = 0 ↔ σ = 1 := by
  simp [cycleType_def, cycleFactorsFinset_eq_empty_iff]
  -- 🎉 no goals
#align equiv.perm.cycle_type_eq_zero Equiv.Perm.cycleType_eq_zero

@[simp] -- porting note: new attr
theorem cycleType_one : (1 : Perm α).cycleType = 0 := cycleType_eq_zero.2 rfl
#align equiv.perm.cycle_type_one Equiv.Perm.cycleType_one

theorem card_cycleType_eq_zero {σ : Perm α} : Multiset.card σ.cycleType = 0 ↔ σ = 1 := by
  rw [card_eq_zero, cycleType_eq_zero]
  -- 🎉 no goals
#align equiv.perm.card_cycle_type_eq_zero Equiv.Perm.card_cycleType_eq_zero

theorem card_cycleType_pos {σ : Perm α} : 0 < Multiset.card σ.cycleType ↔ σ ≠ 1 :=
  pos_iff_ne_zero.trans card_cycleType_eq_zero.not

theorem two_le_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : 2 ≤ n := by
  simp only [cycleType_def, ← Finset.mem_def, Function.comp_apply, Multiset.mem_map,
    mem_cycleFactorsFinset_iff] at h
  obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h
  -- ⊢ 2 ≤ Finset.card (support w✝)
  exact hc.two_le_card_support
  -- 🎉 no goals
#align equiv.perm.two_le_of_mem_cycle_type Equiv.Perm.two_le_of_mem_cycleType

theorem one_lt_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : 1 < n :=
  two_le_of_mem_cycleType h
#align equiv.perm.one_lt_of_mem_cycle_type Equiv.Perm.one_lt_of_mem_cycleType

theorem IsCycle.cycleType {σ : Perm α} (hσ : IsCycle σ) : σ.cycleType = [σ.support.card] :=
  cycleType_eq [σ] (mul_one σ) (fun _τ hτ => (congr_arg IsCycle (List.mem_singleton.mp hτ)).mpr hσ)
    (List.pairwise_singleton Disjoint σ)
#align equiv.perm.is_cycle.cycle_type Equiv.Perm.IsCycle.cycleType

theorem card_cycleType_eq_one {σ : Perm α} : Multiset.card σ.cycleType = 1 ↔ σ.IsCycle := by
  rw [card_eq_one]
  -- ⊢ (∃ a, cycleType σ = {a}) ↔ IsCycle σ
  simp_rw [cycleType_def, Multiset.map_eq_singleton, ← Finset.singleton_val, Finset.val_inj,
    cycleFactorsFinset_eq_singleton_iff]
  constructor
  -- ⊢ (∃ a a_1, (IsCycle σ ∧ σ = a_1) ∧ (Finset.card ∘ support) a_1 = a) → IsCycle σ
  · rintro ⟨_, _, ⟨h, -⟩, -⟩
    -- ⊢ IsCycle σ
    exact h
    -- 🎉 no goals
  · intro h
    -- ⊢ ∃ a a_1, (IsCycle σ ∧ σ = a_1) ∧ (Finset.card ∘ support) a_1 = a
    use σ.support.card, σ
    -- ⊢ (IsCycle σ ∧ σ = σ) ∧ (Finset.card ∘ support) σ = Finset.card (support σ)
    simp [h]
    -- 🎉 no goals
#align equiv.perm.card_cycle_type_eq_one Equiv.Perm.card_cycleType_eq_one

theorem Disjoint.cycleType {σ τ : Perm α} (h : Disjoint σ τ) :
    (σ * τ).cycleType = σ.cycleType + τ.cycleType := by
  rw [cycleType_def, cycleType_def, cycleType_def, h.cycleFactorsFinset_mul_eq_union, ←
    Multiset.map_add, Finset.union_val, Multiset.add_eq_union_iff_disjoint.mpr _]
  exact Finset.disjoint_val.2 h.disjoint_cycleFactorsFinset
  -- 🎉 no goals
#align equiv.perm.disjoint.cycle_type Equiv.Perm.Disjoint.cycleType

@[simp] -- porting note: new attr
theorem cycleType_inv (σ : Perm α) : σ⁻¹.cycleType = σ.cycleType :=
  cycle_induction_on (P := fun τ : Perm α => τ⁻¹.cycleType = τ.cycleType) σ rfl
    (fun σ hσ => by simp only [hσ.cycleType, hσ.inv.cycleType, support_inv])
                    -- 🎉 no goals
    fun σ τ hστ _ hσ hτ => by
      simp only [mul_inv_rev, hστ.cycleType, hστ.symm.inv_left.inv_right.cycleType, hσ, hτ,
        add_comm]
#align equiv.perm.cycle_type_inv Equiv.Perm.cycleType_inv

@[simp] -- porting note: new attr
theorem cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹).cycleType = σ.cycleType := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, hσ.conj.cycleType, card_support_conj]
  | induction_disjoint σ π hd _ hσ hπ =>
    rw [← conj_mul, hd.cycleType, (hd.conj _).cycleType, hσ, hπ]
#align equiv.perm.cycle_type_conj Equiv.Perm.cycleType_conj

theorem sum_cycleType (σ : Perm α) : σ.cycleType.sum = σ.support.card := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, coe_sum, List.sum_singleton]
  | induction_disjoint σ τ hd _ hσ hτ => rw [hd.cycleType, sum_add, hσ, hτ, hd.card_support_mul]
#align equiv.perm.sum_cycle_type Equiv.Perm.sum_cycleType

theorem sign_of_cycleType' (σ : Perm α) :
    sign σ = (σ.cycleType.map fun n => -(-1 : ℤˣ) ^ n).prod := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.sign]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hσ, hτ, hd.cycleType]
#align equiv.perm.sign_of_cycle_type' Equiv.Perm.sign_of_cycleType'

theorem sign_of_cycleType (f : Perm α) :
    sign f = (-1 : ℤˣ) ^ (f.cycleType.sum + Multiset.card f.cycleType) := by
  rw [sign_of_cycleType']
  -- ⊢ prod (map (fun n => -(-1) ^ n) (cycleType f)) = (-1) ^ (sum (cycleType f) +  …
  induction' f.cycleType using Multiset.induction_on with a s ihs
  -- ⊢ prod (map (fun n => -(-1) ^ n) 0) = (-1) ^ (sum 0 + ↑card 0)
  · rfl
    -- 🎉 no goals
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons, ihs]
    -- ⊢ -(-1) ^ a * (-1) ^ (sum s + ↑card s) = (-1) ^ (a + sum s + (↑card s + 1))
    simp only [pow_add, pow_one, mul_neg_one, neg_mul, mul_neg, mul_assoc, mul_one]
    -- 🎉 no goals
#align equiv.perm.sign_of_cycle_type Equiv.Perm.sign_of_cycleType

@[simp] -- porting note: new attr
theorem lcm_cycleType (σ : Perm α) : σ.cycleType.lcm = orderOf σ := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.orderOf]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hd.cycleType, hd.orderOf, lcm_eq_nat_lcm, hσ, hτ]
#align equiv.perm.lcm_cycle_type Equiv.Perm.lcm_cycleType

theorem dvd_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : n ∣ orderOf σ := by
  rw [← lcm_cycleType]
  -- ⊢ n ∣ Multiset.lcm (cycleType σ)
  exact dvd_lcm h
  -- 🎉 no goals
#align equiv.perm.dvd_of_mem_cycle_type Equiv.Perm.dvd_of_mem_cycleType

theorem orderOf_cycleOf_dvd_orderOf (f : Perm α) (x : α) : orderOf (cycleOf f x) ∣ orderOf f := by
  by_cases hx : f x = x
  -- ⊢ orderOf (cycleOf f x) ∣ orderOf f
  · rw [← cycleOf_eq_one_iff] at hx
    -- ⊢ orderOf (cycleOf f x) ∣ orderOf f
    simp [hx]
    -- 🎉 no goals
  · refine dvd_of_mem_cycleType ?_
    -- ⊢ orderOf (cycleOf f x) ∈ cycleType f
    rw [cycleType, Multiset.mem_map]
    -- ⊢ ∃ a, a ∈ (cycleFactorsFinset f).val ∧ (Finset.card ∘ support) a = orderOf (c …
    refine' ⟨f.cycleOf x, _, _⟩
    -- ⊢ cycleOf f x ∈ (cycleFactorsFinset f).val
    · rwa [← Finset.mem_def, cycleOf_mem_cycleFactorsFinset_iff, mem_support]
      -- 🎉 no goals
    · simp [(isCycle_cycleOf _ hx).orderOf]
      -- 🎉 no goals
#align equiv.perm.order_of_cycle_of_dvd_order_of Equiv.Perm.orderOf_cycleOf_dvd_orderOf

theorem two_dvd_card_support {σ : Perm α} (hσ : σ ^ 2 = 1) : 2 ∣ σ.support.card :=
  (congr_arg (Dvd.dvd 2) σ.sum_cycleType).mp
    (Multiset.dvd_sum fun n hn => by
      rw [le_antisymm
          (Nat.le_of_dvd zero_lt_two <|
            (dvd_of_mem_cycleType hn).trans <| orderOf_dvd_of_pow_eq_one hσ)
          (two_le_of_mem_cycleType hn)])
#align equiv.perm.two_dvd_card_support Equiv.Perm.two_dvd_card_support

theorem cycleType_prime_order {σ : Perm α} (hσ : (orderOf σ).Prime) :
    ∃ n : ℕ, σ.cycleType = replicate (n + 1) (orderOf σ) := by
  refine ⟨Multiset.card σ.cycleType - 1, eq_replicate.2 ⟨?_, fun n hn ↦ ?_⟩⟩
  -- ⊢ ↑card (cycleType σ) = ↑card (cycleType σ) - 1 + 1
  · rw [tsub_add_cancel_of_le]
    -- ⊢ 1 ≤ ↑card (cycleType σ)
    rw [Nat.succ_le_iff, card_cycleType_pos, Ne.def, ← orderOf_eq_one_iff]
    -- ⊢ ¬orderOf σ = 1
    exact hσ.ne_one
    -- 🎉 no goals
  · exact (hσ.eq_one_or_self_of_dvd n (dvd_of_mem_cycleType hn)).resolve_left
      (one_lt_of_mem_cycleType hn).ne'
#align equiv.perm.cycle_type_prime_order Equiv.Perm.cycleType_prime_order

theorem isCycle_of_prime_order {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : σ.support.card < 2 * orderOf σ) : σ.IsCycle := by
  obtain ⟨n, hn⟩ := cycleType_prime_order h1
  -- ⊢ IsCycle σ
  rw [← σ.sum_cycleType, hn, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    mul_lt_mul_right (orderOf_pos σ), Nat.succ_lt_succ_iff, Nat.lt_succ_iff, le_zero_iff] at h2
  rw [← card_cycleType_eq_one, hn, card_replicate, h2]
  -- 🎉 no goals
#align equiv.perm.is_cycle_of_prime_order Equiv.Perm.isCycle_of_prime_order

theorem cycleType_le_of_mem_cycleFactorsFinset {f g : Perm α} (hf : f ∈ g.cycleFactorsFinset) :
    f.cycleType ≤ g.cycleType := by
  have hf' := mem_cycleFactorsFinset_iff.1 hf
  -- ⊢ cycleType f ≤ cycleType g
  rw [cycleType_def, cycleType_def, hf'.left.cycleFactorsFinset_eq_singleton]
  -- ⊢ map (Finset.card ∘ support) {f}.val ≤ map (Finset.card ∘ support) (cycleFact …
  refine map_le_map ?_
  -- ⊢ {f}.val ≤ (cycleFactorsFinset g).val
  simpa only [Finset.singleton_val, singleton_le, Finset.mem_val] using hf
  -- 🎉 no goals
#align equiv.perm.cycle_type_le_of_mem_cycle_factors_finset Equiv.Perm.cycleType_le_of_mem_cycleFactorsFinset

theorem cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub
    {f g : Perm α} (hf : f ∈ g.cycleFactorsFinset) :
    (g * f⁻¹).cycleType = g.cycleType - f.cycleType :=
  add_right_cancel (b := f.cycleType) <| by
    rw [← (disjoint_mul_inv_of_mem_cycleFactorsFinset hf).cycleType, inv_mul_cancel_right,
      tsub_add_cancel_of_le (cycleType_le_of_mem_cycleFactorsFinset hf)]
#align equiv.perm.cycle_type_mul_mem_cycle_factors_finset_eq_sub Equiv.Perm.cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub

theorem isConj_of_cycleType_eq {σ τ : Perm α} (h : cycleType σ = cycleType τ) : IsConj σ τ := by
  induction σ using cycle_induction_on generalizing τ with
  | base_one =>
    rw [cycleType_one, eq_comm, cycleType_eq_zero] at h
    rw [h]
  | base_cycles σ hσ =>
    have hτ := card_cycleType_eq_one.2 hσ
    rw [h, card_cycleType_eq_one] at hτ
    apply hσ.isConj hτ
    rw [hσ.cycleType, hτ.cycleType, coe_eq_coe, List.singleton_perm] at h
    exact List.singleton_injective h
  | induction_disjoint σ π hd hc hσ hπ =>
    rw [hd.cycleType] at h
    have h' : σ.support.card ∈ τ.cycleType := by
      simp [← h, hc.cycleType]
    obtain ⟨σ', hσ'l, hσ'⟩ := Multiset.mem_map.mp h'
    have key : IsConj (σ' * τ * σ'⁻¹) τ := (isConj_iff.2 ⟨σ', rfl⟩).symm
    refine' IsConj.trans _ key
    rw [mul_assoc]
    have hs : σ.cycleType = σ'.cycleType := by
      rw [← Finset.mem_def, mem_cycleFactorsFinset_iff] at hσ'l
      rw [hc.cycleType, ← hσ', hσ'l.left.cycleType]; rfl
    refine' hd.isConj_mul (hσ hs) (hπ _) _
    · rw [cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub, ← h, add_comm, hs,
        add_tsub_cancel_right]
      rwa [Finset.mem_def]
    · exact (disjoint_mul_inv_of_mem_cycleFactorsFinset hσ'l).symm
#align equiv.perm.is_conj_of_cycle_type_eq Equiv.Perm.isConj_of_cycleType_eq

theorem isConj_iff_cycleType_eq {σ τ : Perm α} : IsConj σ τ ↔ σ.cycleType = τ.cycleType :=
  ⟨fun h => by
    obtain ⟨π, rfl⟩ := isConj_iff.1 h
    -- ⊢ cycleType σ = cycleType (π * σ * π⁻¹)
    rw [cycleType_conj], isConj_of_cycleType_eq⟩
    -- 🎉 no goals
#align equiv.perm.is_conj_iff_cycle_type_eq Equiv.Perm.isConj_iff_cycleType_eq

@[simp]
theorem cycleType_extendDomain {β : Type*} [Fintype β] [DecidableEq β] {p : β → Prop}
    [DecidablePred p] (f : α ≃ Subtype p) {g : Perm α} :
    cycleType (g.extendDomain f) = cycleType g := by
  induction g using cycle_induction_on with
  | base_one => rw [extendDomain_one, cycleType_one, cycleType_one]
  | base_cycles σ hσ =>
    rw [(hσ.extendDomain f).cycleType, hσ.cycleType, card_support_extend_domain]
  | induction_disjoint σ τ hd _ hσ hτ =>
    rw [hd.cycleType, ← extendDomain_mul, (hd.extendDomain f).cycleType, hσ, hτ]
#align equiv.perm.cycle_type_extend_domain Equiv.Perm.cycleType_extendDomain

theorem cycleType_ofSubtype {p : α → Prop} [DecidablePred p] {g : Perm (Subtype p)} :
    cycleType (ofSubtype g) = cycleType g :=
  cycleType_extendDomain (Equiv.refl (Subtype p))
#align equiv.perm.cycle_type_of_subtype Equiv.Perm.cycleType_ofSubtype

theorem mem_cycleType_iff {n : ℕ} {σ : Perm α} :
    n ∈ cycleType σ ↔ ∃ c τ, σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ c.support.card = n := by
  constructor
  -- ⊢ n ∈ cycleType σ → ∃ c τ, σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ Finset.card  …
  · intro h
    -- ⊢ ∃ c τ, σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ Finset.card (support c) = n
    obtain ⟨l, rfl, hlc, hld⟩ := truncCycleFactors σ
    -- ⊢ ∃ c τ, List.prod l = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ Finset.card (support …
    rw [cycleType_eq _ rfl hlc hld, Multiset.mem_coe, List.mem_map] at h
    -- ⊢ ∃ c τ, List.prod l = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ Finset.card (support …
    obtain ⟨c, cl, rfl⟩ := h
    -- ⊢ ∃ c_1 τ, List.prod l = c_1 * τ ∧ Disjoint c_1 τ ∧ IsCycle c_1 ∧ Finset.card  …
    rw [(List.perm_cons_erase cl).pairwise_iff Disjoint.symmetric] at hld
    -- ⊢ ∃ c_1 τ, List.prod l = c_1 * τ ∧ Disjoint c_1 τ ∧ IsCycle c_1 ∧ Finset.card  …
    refine' ⟨c, (l.erase c).prod, _, _, hlc _ cl, rfl⟩
    -- ⊢ List.prod l = c * List.prod (List.erase l c)
    · rw [← List.prod_cons, (List.perm_cons_erase cl).symm.prod_eq' (hld.imp Disjoint.commute)]
      -- 🎉 no goals
    · exact disjoint_prod_right _ fun g => List.rel_of_pairwise_cons hld
      -- 🎉 no goals
  · rintro ⟨c, t, rfl, hd, hc, rfl⟩
    -- ⊢ Finset.card (support c) ∈ cycleType (c * t)
    simp [hd.cycleType, hc.cycleType]
    -- 🎉 no goals
#align equiv.perm.mem_cycle_type_iff Equiv.Perm.mem_cycleType_iff

theorem le_card_support_of_mem_cycleType {n : ℕ} {σ : Perm α} (h : n ∈ cycleType σ) :
    n ≤ σ.support.card :=
  (le_sum_of_mem h).trans (le_of_eq σ.sum_cycleType)
#align equiv.perm.le_card_support_of_mem_cycle_type Equiv.Perm.le_card_support_of_mem_cycleType

theorem cycleType_of_card_le_mem_cycleType_add_two {n : ℕ} {g : Perm α}
    (hn2 : Fintype.card α < n + 2) (hng : n ∈ g.cycleType) : g.cycleType = {n} := by
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycleType_iff.1 hng
  -- ⊢ cycleType (c * g') = {Finset.card (support c)}
  by_cases g'1 : g' = 1
  -- ⊢ cycleType (c * g') = {Finset.card (support c)}
  · rw [hd.cycleType, hc.cycleType, coe_singleton, g'1, cycleType_one, add_zero]
    -- 🎉 no goals
  contrapose! hn2
  -- ⊢ Finset.card (support c) + 2 ≤ Fintype.card α
  apply le_trans _ (c * g').support.card_le_univ
  -- ⊢ Finset.card (support c) + 2 ≤ Finset.card (support (c * g'))
  rw [hd.card_support_mul]
  -- ⊢ Finset.card (support c) + 2 ≤ Finset.card (support c) + Finset.card (support …
  exact add_le_add_left (two_le_card_support_of_ne_one g'1) _
  -- 🎉 no goals
#align equiv.perm.cycle_type_of_card_le_mem_cycle_type_add_two Equiv.Perm.cycleType_of_card_le_mem_cycleType_add_two

end CycleType

theorem card_compl_support_modEq [DecidableEq α] {p n : ℕ} [hp : Fact p.Prime] {σ : Perm α}
    (hσ : σ ^ p ^ n = 1) : σ.supportᶜ.card ≡ Fintype.card α [MOD p] := by
  rw [Nat.modEq_iff_dvd', ← Finset.card_compl, compl_compl, ← sum_cycleType]
  -- ⊢ p ∣ sum (cycleType σ)
  · refine Multiset.dvd_sum fun k hk => ?_
    -- ⊢ p ∣ k
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hσ)
    -- ⊢ p ∣ k
    obtain ⟨l, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ hm).mp (dvd_of_mem_cycleType hk))
    exact dvd_pow_self _ fun h => (one_lt_of_mem_cycleType hk).ne <| by rw [h, pow_zero]
    -- 🎉 no goals
  · exact Finset.card_le_univ _
    -- 🎉 no goals
#align equiv.perm.card_compl_support_modeq Equiv.Perm.card_compl_support_modEq

theorem exists_fixed_point_of_prime {p n : ℕ} [hp : Fact p.Prime] (hα : ¬p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) : ∃ a : α, σ a = a := by
  classical
    contrapose! hα
    simp_rw [← mem_support, ← Finset.eq_univ_iff_forall] at hα
    exact Nat.modEq_zero_iff_dvd.1 ((congr_arg _ (Finset.card_eq_zero.2 (compl_eq_bot.2 hα))).mp
      (card_compl_support_modEq hσ).symm)
#align equiv.perm.exists_fixed_point_of_prime Equiv.Perm.exists_fixed_point_of_prime

theorem exists_fixed_point_of_prime' {p n : ℕ} [hp : Fact p.Prime] (hα : p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) {a : α} (ha : σ a = a) : ∃ b : α, σ b = b ∧ b ≠ a := by
  classical
    have h : ∀ b : α, b ∈ σ.supportᶜ ↔ σ b = b := fun b => by
      rw [Finset.mem_compl, mem_support, Classical.not_not]
    obtain ⟨b, hb1, hb2⟩ := Finset.exists_ne_of_one_lt_card (hp.out.one_lt.trans_le
      (Nat.le_of_dvd (Finset.card_pos.mpr ⟨a, (h a).mpr ha⟩) (Nat.modEq_zero_iff_dvd.mp
        ((card_compl_support_modEq hσ).trans (Nat.modEq_zero_iff_dvd.mpr hα))))) a
    exact ⟨b, (h b).mp hb1, hb2⟩
#align equiv.perm.exists_fixed_point_of_prime' Equiv.Perm.exists_fixed_point_of_prime'

theorem isCycle_of_prime_order' {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : Fintype.card α < 2 * orderOf σ) : σ.IsCycle := by
  classical exact isCycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2)
  -- 🎉 no goals
#align equiv.perm.is_cycle_of_prime_order' Equiv.Perm.isCycle_of_prime_order'

theorem isCycle_of_prime_order'' {σ : Perm α} (h1 : (Fintype.card α).Prime)
    (h2 : orderOf σ = Fintype.card α) : σ.IsCycle :=
  isCycle_of_prime_order' ((congr_arg Nat.Prime h2).mpr h1) <| by
    rw [← one_mul (Fintype.card α), ← h2, mul_lt_mul_right (orderOf_pos σ)]
    -- ⊢ 1 < 2
    exact one_lt_two
    -- 🎉 no goals
#align equiv.perm.is_cycle_of_prime_order'' Equiv.Perm.isCycle_of_prime_order''

section Cauchy

variable (G : Type*) [Group G] (n : ℕ)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectorsProdEqOne : Set (Vector G n) :=
  { v | v.toList.prod = 1 }
#align equiv.perm.vectors_prod_eq_one Equiv.Perm.vectorsProdEqOne

namespace VectorsProdEqOne

theorem mem_iff {n : ℕ} (v : Vector G n) : v ∈ vectorsProdEqOne G n ↔ v.toList.prod = 1 :=
  Iff.rfl
#align equiv.perm.vectors_prod_eq_one.mem_iff Equiv.Perm.VectorsProdEqOne.mem_iff

theorem zero_eq : vectorsProdEqOne G 0 = {Vector.nil} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨Eq.refl (1 : G), fun v _ => v.eq_nil⟩
#align equiv.perm.vectors_prod_eq_one.zero_eq Equiv.Perm.VectorsProdEqOne.zero_eq

theorem one_eq : vectorsProdEqOne G 1 = {Vector.nil.cons 1} := by
  simp_rw [Set.eq_singleton_iff_unique_mem, mem_iff, Vector.toList_singleton, List.prod_singleton,
    Vector.head_cons, true_and]
  exact fun v hv => v.cons_head_tail.symm.trans (congr_arg₂ Vector.cons hv v.tail.eq_nil)
  -- 🎉 no goals
#align equiv.perm.vectors_prod_eq_one.one_eq Equiv.Perm.VectorsProdEqOne.one_eq

instance zeroUnique : Unique (vectorsProdEqOne G 0) := by
  rw [zero_eq]
  -- ⊢ Unique ↑{Vector.nil}
  exact Set.uniqueSingleton Vector.nil
  -- 🎉 no goals
#align equiv.perm.vectors_prod_eq_one.zero_unique Equiv.Perm.VectorsProdEqOne.zeroUnique

instance oneUnique : Unique (vectorsProdEqOne G 1) := by
  rw [one_eq]
  -- ⊢ Unique ↑{1 ::ᵥ Vector.nil}
  exact Set.uniqueSingleton (Vector.nil.cons 1)
  -- 🎉 no goals
#align equiv.perm.vectors_prod_eq_one.one_unique Equiv.Perm.VectorsProdEqOne.oneUnique

/-- Given a vector `v` of length `n`, make a vector of length `n + 1` whose product is `1`,
by appending the inverse of the product of `v`. -/
@[simps]
def vectorEquiv : Vector G n ≃ vectorsProdEqOne G (n + 1) where
  toFun v := ⟨v.toList.prod⁻¹ ::ᵥ v, by
    rw [mem_iff, Vector.toList_cons, List.prod_cons, inv_mul_self]⟩
    -- 🎉 no goals
  invFun v := v.1.tail
  left_inv v := v.tail_cons v.toList.prod⁻¹
  right_inv v := Subtype.ext <|
    calc
      v.1.tail.toList.prod⁻¹ ::ᵥ v.1.tail = v.1.head ::ᵥ v.1.tail :=
        congr_arg (· ::ᵥ v.1.tail) <| Eq.symm <| eq_inv_of_mul_eq_one_left <| by
          rw [← List.prod_cons, ← Vector.toList_cons, v.1.cons_head_tail]
          -- ⊢ List.prod (Vector.toList ↑v) = 1
          exact v.2
          -- 🎉 no goals
      _ = v.1 := v.1.cons_head_tail
#align equiv.perm.vectors_prod_eq_one.vector_equiv Equiv.Perm.VectorsProdEqOne.vectorEquiv

/-- Given a vector `v` of length `n` whose product is 1, make a vector of length `n - 1`,
by deleting the last entry of `v`. -/
def equivVector : ∀ n, vectorsProdEqOne G n ≃ Vector G (n - 1)
  | 0 => (equivOfUnique (vectorsProdEqOne G 0) (vectorsProdEqOne G 1)).trans (vectorEquiv G 0).symm
  | (n + 1) => (vectorEquiv G n).symm
#align equiv.perm.vectors_prod_eq_one.equiv_vector Equiv.Perm.VectorsProdEqOne.equivVector

instance [Fintype G] : Fintype (vectorsProdEqOne G n) :=
  Fintype.ofEquiv (Vector G (n - 1)) (equivVector G n).symm

theorem card [Fintype G] : Fintype.card (vectorsProdEqOne G n) = Fintype.card G ^ (n - 1) :=
  (Fintype.card_congr (equivVector G n)).trans (card_vector (n - 1))
#align equiv.perm.vectors_prod_eq_one.card Equiv.Perm.VectorsProdEqOne.card

variable {G n} {g : G}
variable (v : vectorsProdEqOne G n) (j k : ℕ)

/-- Rotate a vector whose product is 1. -/
def rotate : vectorsProdEqOne G n :=
  ⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, List.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩
#align equiv.perm.vectors_prod_eq_one.rotate Equiv.Perm.VectorsProdEqOne.rotate

theorem rotate_zero : rotate v 0 = v :=
  Subtype.ext (Subtype.ext v.1.1.rotate_zero)
#align equiv.perm.vectors_prod_eq_one.rotate_zero Equiv.Perm.VectorsProdEqOne.rotate_zero

theorem rotate_rotate : rotate (rotate v j) k = rotate v (j + k) :=
  Subtype.ext (Subtype.ext (v.1.1.rotate_rotate j k))
#align equiv.perm.vectors_prod_eq_one.rotate_rotate Equiv.Perm.VectorsProdEqOne.rotate_rotate

theorem rotate_length : rotate v n = v :=
  Subtype.ext (Subtype.ext ((congr_arg _ v.1.2.symm).trans v.1.1.rotate_length))
#align equiv.perm.vectors_prod_eq_one.rotate_length Equiv.Perm.VectorsProdEqOne.rotate_length

end VectorsProdEqOne

/-- For every prime `p` dividing the order of a finite group `G` there exists an element of order
`p` in `G`. This is known as Cauchy's theorem. -/
theorem _root_.exists_prime_orderOf_dvd_card {G : Type*} [Group G] [Fintype G] (p : ℕ)
    [hp : Fact p.Prime] (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p := by
  have hp' : p - 1 ≠ 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_lt hp.out.one_lt)
  -- ⊢ ∃ x, orderOf x = p
  have Scard :=
    calc
      p ∣ Fintype.card G ^ (p - 1) := hdvd.trans (dvd_pow (dvd_refl _) hp')
      _ = Fintype.card (vectorsProdEqOne G p) := (VectorsProdEqOne.card G p).symm
  let f : ℕ → vectorsProdEqOne G p → vectorsProdEqOne G p := fun k v =>
    VectorsProdEqOne.rotate v k
  have hf1 : ∀ v, f 0 v = v := VectorsProdEqOne.rotate_zero
  -- ⊢ ∃ x, orderOf x = p
  have hf2 : ∀ j k v, f k (f j v) = f (j + k) v := fun j k v =>
    VectorsProdEqOne.rotate_rotate v j k
  have hf3 : ∀ v, f p v = v := VectorsProdEqOne.rotate_length
  -- ⊢ ∃ x, orderOf x = p
  let σ :=
    Equiv.mk (f 1) (f (p - 1)) (fun s => by rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
      fun s => by rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]
  have hσ : ∀ k v, (σ ^ k) v = f k v := fun k v =>
    Nat.rec (hf1 v).symm (fun k hk => Eq.trans (congr_arg σ hk) (hf2 k 1 v)) k
  replace hσ : σ ^ p ^ 1 = 1 := Perm.ext fun v => by rw [pow_one, hσ, hf3, one_apply]
  -- ⊢ ∃ x, orderOf x = p
  let v₀ : vectorsProdEqOne G p :=
    ⟨Vector.replicate p 1, (List.prod_replicate p 1).trans (one_pow p)⟩
  have hv₀ : σ v₀ = v₀ := Subtype.ext (Subtype.ext (List.rotate_replicate (1 : G) p 1))
  -- ⊢ ∃ x, orderOf x = p
  obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀
  -- ⊢ ∃ x, orderOf x = p
  refine'
    Exists.imp (fun g hg => orderOf_eq_prime _ fun hg' => hv2 _)
      (List.rotate_one_eq_self_iff_eq_replicate.mp (Subtype.ext_iff.mp (Subtype.ext_iff.mp hv1)))
  · rw [← List.prod_replicate, ← v.1.2, ← hg, show v.val.val.prod = 1 from v.2]
    -- 🎉 no goals
  · rw [Subtype.ext_iff_val, Subtype.ext_iff_val, hg, hg', v.1.2]
    -- ⊢ List.replicate p 1 = ↑↑v₀
    rfl
    -- 🎉 no goals
#align exists_prime_order_of_dvd_card exists_prime_orderOf_dvd_card

/-- For every prime `p` dividing the order of a finite additive group `G` there exists an element of
order `p` in `G`. This is the additive version of Cauchy's theorem. -/
theorem _root_.exists_prime_addOrderOf_dvd_card {G : Type*} [AddGroup G] [Fintype G] (p : ℕ)
    [hp : Fact p.Prime] (hdvd : p ∣ Fintype.card G) : ∃ x : G, addOrderOf x = p :=
  @exists_prime_orderOf_dvd_card (Multiplicative G) _ _ _ _ (by convert hdvd)
                                                                -- 🎉 no goals
#align exists_prime_add_order_of_dvd_card exists_prime_addOrderOf_dvd_card

attribute [to_additive existing] exists_prime_orderOf_dvd_card

end Cauchy

theorem subgroup_eq_top_of_swap_mem [DecidableEq α] {H : Subgroup (Perm α)}
    [d : DecidablePred (· ∈ H)] {τ : Perm α} (h0 : (Fintype.card α).Prime)
    (h1 : Fintype.card α ∣ Fintype.card H) (h2 : τ ∈ H) (h3 : IsSwap τ) : H = ⊤ := by
  haveI : Fact (Fintype.card α).Prime := ⟨h0⟩
  -- ⊢ H = ⊤
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) h1
  -- ⊢ H = ⊤
  have hσ1 : orderOf (σ : Perm α) = Fintype.card α := (orderOf_subgroup σ).trans hσ
  -- ⊢ H = ⊤
  have hσ2 : IsCycle ↑σ := isCycle_of_prime_order'' h0 hσ1
  -- ⊢ H = ⊤
  have hσ3 : (σ : Perm α).support = ⊤ :=
    Finset.eq_univ_of_card (σ : Perm α).support (hσ2.orderOf.symm.trans hσ1)
  have hσ4 : Subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3
  -- ⊢ H = ⊤
  rw [eq_top_iff, ← hσ4, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  -- ⊢ ↑σ ∈ ↑H ∧ τ ∈ ↑H
  exact ⟨Subtype.mem σ, h2⟩
  -- 🎉 no goals
#align equiv.perm.subgroup_eq_top_of_swap_mem Equiv.Perm.subgroup_eq_top_of_swap_mem

section Partition

variable [DecidableEq α]

/-- The partition corresponding to a permutation -/
def partition (σ : Perm α) : (Fintype.card α).Partition where
  parts := σ.cycleType + replicate (Fintype.card α - σ.support.card) 1
  parts_pos {n hn} := by
    cases' mem_add.mp hn with hn hn
    -- ⊢ 0 < n
    · exact zero_lt_one.trans (one_lt_of_mem_cycleType hn)
      -- 🎉 no goals
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
      -- 🎉 no goals
  parts_sum := by
    rw [sum_add, sum_cycleType, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one,
      add_tsub_cancel_of_le σ.support.card_le_univ]
#align equiv.perm.partition Equiv.Perm.partition

theorem parts_partition {σ : Perm α} :
    σ.partition.parts = σ.cycleType + replicate (Fintype.card α - σ.support.card) 1 :=
  rfl
#align equiv.perm.parts_partition Equiv.Perm.parts_partition

theorem filter_parts_partition_eq_cycleType {σ : Perm α} :
    ((partition σ).parts.filter fun n => 2 ≤ n) = σ.cycleType := by
  rw [parts_partition, filter_add, Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycleType,
    Multiset.filter_eq_nil.2 fun a h => ?_, add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  -- ⊢ ¬2 ≤ 1
  decide
  -- 🎉 no goals
#align equiv.perm.filter_parts_partition_eq_cycle_type Equiv.Perm.filter_parts_partition_eq_cycleType

theorem partition_eq_of_isConj {σ τ : Perm α} : IsConj σ τ ↔ σ.partition = τ.partition := by
  rw [isConj_iff_cycleType_eq]
  -- ⊢ cycleType σ = cycleType τ ↔ partition σ = partition τ
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ partition σ = partition τ
  · rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ← sum_cycleType, ← sum_cycleType,
      h]
  · rw [← filter_parts_partition_eq_cycleType, ← filter_parts_partition_eq_cycleType, h]
    -- 🎉 no goals
#align equiv.perm.partition_eq_of_is_conj Equiv.Perm.partition_eq_of_isConj

end Partition

/-!
### 3-cycles
-/


/-- A three-cycle is a cycle of length 3. -/
def IsThreeCycle [DecidableEq α] (σ : Perm α) : Prop :=
  σ.cycleType = {3}
#align equiv.perm.is_three_cycle Equiv.Perm.IsThreeCycle

namespace IsThreeCycle

variable [DecidableEq α] {σ : Perm α}

theorem cycleType (h : IsThreeCycle σ) : σ.cycleType = {3} :=
  h
#align equiv.perm.is_three_cycle.cycle_type Equiv.Perm.IsThreeCycle.cycleType

theorem card_support (h : IsThreeCycle σ) : σ.support.card = 3 := by
  rw [← sum_cycleType, h.cycleType, Multiset.sum_singleton]
  -- 🎉 no goals
#align equiv.perm.is_three_cycle.card_support Equiv.Perm.IsThreeCycle.card_support

theorem _root_.card_support_eq_three_iff : σ.support.card = 3 ↔ σ.IsThreeCycle := by
  refine' ⟨fun h => _, IsThreeCycle.card_support⟩
  -- ⊢ IsThreeCycle σ
  by_cases h0 : σ.cycleType = 0
  -- ⊢ IsThreeCycle σ
  · rw [← sum_cycleType, h0, sum_zero] at h
    -- ⊢ IsThreeCycle σ
    exact (ne_of_lt zero_lt_three h).elim
    -- 🎉 no goals
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0
  -- ⊢ IsThreeCycle σ
  by_cases h1 : σ.cycleType.erase n = 0
  -- ⊢ IsThreeCycle σ
  · rw [← sum_cycleType, ← cons_erase hn, h1, cons_zero, Multiset.sum_singleton] at h
    -- ⊢ IsThreeCycle σ
    rw [IsThreeCycle, ← cons_erase hn, h1, h, ← cons_zero]
    -- 🎉 no goals
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1
  -- ⊢ IsThreeCycle σ
  rw [← sum_cycleType, ← cons_erase hn, ← cons_erase hm, Multiset.sum_cons, Multiset.sum_cons] at h
  -- ⊢ IsThreeCycle σ
  -- TODO: linarith [...] should solve this directly
  have : ∀ {k}, 2 ≤ m → 2 ≤ n → n + (m + k) = 3 → False := by
    intros
    linarith
  cases this (two_le_of_mem_cycleType (mem_of_mem_erase hm)) (two_le_of_mem_cycleType hn) h
  -- 🎉 no goals
#align card_support_eq_three_iff card_support_eq_three_iff

theorem isCycle (h : IsThreeCycle σ) : IsCycle σ := by
  rw [← card_cycleType_eq_one, h.cycleType, card_singleton]
  -- 🎉 no goals
#align equiv.perm.is_three_cycle.is_cycle Equiv.Perm.IsThreeCycle.isCycle

theorem sign (h : IsThreeCycle σ) : sign σ = 1 := by
  rw [Equiv.Perm.sign_of_cycleType, h.cycleType]
  -- ⊢ (-1) ^ (sum {3} + ↑card {3}) = 1
  rfl
  -- 🎉 no goals
#align equiv.perm.is_three_cycle.sign Equiv.Perm.IsThreeCycle.sign

theorem inv {f : Perm α} (h : IsThreeCycle f) : IsThreeCycle f⁻¹ := by
  rwa [IsThreeCycle, cycleType_inv]
  -- 🎉 no goals
#align equiv.perm.is_three_cycle.inv Equiv.Perm.IsThreeCycle.inv

@[simp]
theorem inv_iff {f : Perm α} : IsThreeCycle f⁻¹ ↔ IsThreeCycle f :=
  ⟨by
    rw [← inv_inv f]
    -- ⊢ IsThreeCycle f⁻¹⁻¹⁻¹ → IsThreeCycle f⁻¹⁻¹
    apply inv, inv⟩
    -- 🎉 no goals
#align equiv.perm.is_three_cycle.inv_iff Equiv.Perm.IsThreeCycle.inv_iff

theorem orderOf {g : Perm α} (ht : IsThreeCycle g) : orderOf g = 3 := by
  rw [← lcm_cycleType, ht.cycleType, Multiset.lcm_singleton, normalize_eq]
  -- 🎉 no goals
#align equiv.perm.is_three_cycle.order_of Equiv.Perm.IsThreeCycle.orderOf

theorem isThreeCycle_sq {g : Perm α} (ht : IsThreeCycle g) : IsThreeCycle (g * g) := by
  rw [← pow_two, ← card_support_eq_three_iff, support_pow_coprime, ht.card_support]
  -- ⊢ Nat.coprime 2 (_root_.orderOf g)
  rw [ht.orderOf]
  -- ⊢ Nat.coprime 2 3
  norm_num
  -- 🎉 no goals
#align equiv.perm.is_three_cycle.is_three_cycle_sq Equiv.Perm.IsThreeCycle.isThreeCycle_sq

end IsThreeCycle

section

variable [DecidableEq α]

theorem isThreeCycle_swap_mul_swap_same {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    IsThreeCycle (swap a b * swap a c) := by
  suffices h : support (swap a b * swap a c) = {a, b, c}
  -- ⊢ IsThreeCycle (swap a b * swap a c)
  · rw [← card_support_eq_three_iff, h]
    -- ⊢ Finset.card {a, b, c} = 3
    simp [ab, ac, bc]
    -- 🎉 no goals
  apply le_antisymm ((support_mul_le _ _).trans fun x => _) fun x hx => ?_
  -- ⊢ ∀ (x : α), x ∈ support (swap a b) ⊔ support (swap a c) → x ∈ {a, b, c}
  · simp [ab, ac, bc]
    -- 🎉 no goals
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    -- ⊢ x ∈ support (swap a b * swap a c)
    rw [mem_support]
    -- ⊢ ↑(swap a b * swap a c) x ≠ x
    simp only [Perm.coe_mul, Function.comp_apply, Ne.def]
    -- ⊢ ¬↑(swap a b) (↑(swap a c) x) = x
    obtain rfl | rfl | rfl := hx
    · rw [swap_apply_left, swap_apply_of_ne_of_ne ac.symm bc.symm]
      -- ⊢ ¬c = x
      exact ac.symm
      -- 🎉 no goals
    · rw [swap_apply_of_ne_of_ne ab.symm bc, swap_apply_right]
      -- ⊢ ¬a = x
      exact ab
      -- 🎉 no goals
    · rw [swap_apply_right, swap_apply_left]
      -- ⊢ ¬b = x
      exact bc
      -- 🎉 no goals
#align equiv.perm.is_three_cycle_swap_mul_swap_same Equiv.Perm.isThreeCycle_swap_mul_swap_same

open Subgroup

theorem swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
    swap a b * swap a c ∈ closure { σ : Perm α | IsThreeCycle σ } := by
  by_cases bc : b = c
  -- ⊢ swap a b * swap a c ∈ closure {σ | IsThreeCycle σ}
  · subst bc
    -- ⊢ swap a b * swap a b ∈ closure {σ | IsThreeCycle σ}
    simp [one_mem]
    -- 🎉 no goals
  exact subset_closure (isThreeCycle_swap_mul_swap_same ab ac bc)
  -- 🎉 no goals
#align equiv.perm.swap_mul_swap_same_mem_closure_three_cycles Equiv.Perm.swap_mul_swap_same_mem_closure_three_cycles

theorem IsSwap.mul_mem_closure_three_cycles {σ τ : Perm α} (hσ : IsSwap σ) (hτ : IsSwap τ) :
    σ * τ ∈ closure { σ : Perm α | IsThreeCycle σ } := by
  obtain ⟨a, b, ab, rfl⟩ := hσ
  -- ⊢ swap a b * τ ∈ closure {σ | IsThreeCycle σ}
  obtain ⟨c, d, cd, rfl⟩ := hτ
  -- ⊢ swap a b * swap c d ∈ closure {σ | IsThreeCycle σ}
  by_cases ac : a = c
  -- ⊢ swap a b * swap c d ∈ closure {σ | IsThreeCycle σ}
  · subst ac
    -- ⊢ swap a b * swap a d ∈ closure {σ | IsThreeCycle σ}
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd
    -- 🎉 no goals
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d) := by
    simp [swap_comm c a, mul_assoc]
  rw [h']
  -- ⊢ swap a b * swap a c * (swap c a * swap c d) ∈ closure {σ | IsThreeCycle σ}
  exact
    mul_mem (swap_mul_swap_same_mem_closure_three_cycles ab ac)
      (swap_mul_swap_same_mem_closure_three_cycles (Ne.symm ac) cd)
#align equiv.perm.is_swap.mul_mem_closure_three_cycles Equiv.Perm.IsSwap.mul_mem_closure_three_cycles

end

end Equiv.Perm
