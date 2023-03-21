/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module group_theory.perm.cycle.type
! leanprover-community/mathlib commit 47adfab39a11a072db552f47594bf8ed2cf8a722
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GcdMonoid.Multiset
import Mathbin.Combinatorics.Partition
import Mathbin.Data.List.Rotate
import Mathbin.GroupTheory.Perm.Cycle.Basic
import Mathbin.RingTheory.Int.Basic
import Mathbin.Tactic.Linarith.Default

/-!
# Cycle Types

In this file we define the cycle type of a permutation.

## Main definitions

- `σ.cycle_type` where `σ` is a permutation of a `fintype`
- `σ.partition` where `σ` is a permutation of a `fintype`

## Main results

- `sum_cycle_type` : The sum of `σ.cycle_type` equals `σ.support.card`
- `lcm_cycle_type` : The lcm of `σ.cycle_type` equals `order_of σ`
- `is_conj_iff_cycle_type_eq` : Two permutations are conjugate if and only if they have the same
  cycle type.
- `exists_prime_order_of_dvd_card`: For every prime `p` dividing the order of a finite group `G`
  there exists an element of order `p` in `G`. This is known as Cauchy's theorem.
-/


namespace Equiv.Perm

open Equiv List Multiset

variable {α : Type _} [Fintype α]

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
    σ.cycleType = s.1.map (Finset.card ∘ support) :=
  by
  rw [cycle_type_def]
  congr
  rw [cycle_factors_finset_eq_finset]
  exact ⟨h1, h2, h0⟩
#align equiv.perm.cycle_type_eq' Equiv.Perm.cycleType_eq'

theorem cycleType_eq {σ : Perm α} (l : List (Perm α)) (h0 : l.Prod = σ)
    (h1 : ∀ σ : Perm α, σ ∈ l → σ.IsCycle) (h2 : l.Pairwise Disjoint) :
    σ.cycleType = l.map (Finset.card ∘ support) :=
  by
  have hl : l.nodup := nodup_of_pairwise_disjoint_cycles h1 h2
  rw [cycle_type_eq' l.to_finset]
  · simp [list.dedup_eq_self.mpr hl]
  · simpa using h1
  · simpa [hl] using h0
  · simpa [list.dedup_eq_self.mpr hl] using h2.forall disjoint.symmetric
#align equiv.perm.cycle_type_eq Equiv.Perm.cycleType_eq

theorem cycleType_one : (1 : Perm α).cycleType = 0 :=
  cycleType_eq [] rfl (fun _ => False.elim) Pairwise.nil
#align equiv.perm.cycle_type_one Equiv.Perm.cycleType_one

theorem cycleType_eq_zero {σ : Perm α} : σ.cycleType = 0 ↔ σ = 1 := by
  simp [cycle_type_def, cycle_factors_finset_eq_empty_iff]
#align equiv.perm.cycle_type_eq_zero Equiv.Perm.cycleType_eq_zero

theorem card_cycleType_eq_zero {σ : Perm α} : σ.cycleType.card = 0 ↔ σ = 1 := by
  rw [card_eq_zero, cycle_type_eq_zero]
#align equiv.perm.card_cycle_type_eq_zero Equiv.Perm.card_cycleType_eq_zero

theorem two_le_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : 2 ≤ n :=
  by
  simp only [cycle_type_def, ← Finset.mem_def, Function.comp_apply, Multiset.mem_map,
    mem_cycle_factors_finset_iff] at h
  obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h
  exact hc.two_le_card_support
#align equiv.perm.two_le_of_mem_cycle_type Equiv.Perm.two_le_of_mem_cycleType

theorem one_lt_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : 1 < n :=
  two_le_of_mem_cycleType h
#align equiv.perm.one_lt_of_mem_cycle_type Equiv.Perm.one_lt_of_mem_cycleType

theorem IsCycle.cycleType {σ : Perm α} (hσ : IsCycle σ) : σ.cycleType = [σ.support.card] :=
  cycleType_eq [σ] (mul_one σ) (fun τ hτ => (congr_arg IsCycle (List.mem_singleton.mp hτ)).mpr hσ)
    (pairwise_singleton Disjoint σ)
#align equiv.perm.is_cycle.cycle_type Equiv.Perm.IsCycle.cycleType

theorem card_cycleType_eq_one {σ : Perm α} : σ.cycleType.card = 1 ↔ σ.IsCycle :=
  by
  rw [card_eq_one]
  simp_rw [cycle_type_def, Multiset.map_eq_singleton, ← Finset.singleton_val, Finset.val_inj,
    cycle_factors_finset_eq_singleton_iff]
  constructor
  · rintro ⟨_, _, ⟨h, -⟩, -⟩
    exact h
  · intro h
    use σ.support.card, σ
    simp [h]
#align equiv.perm.card_cycle_type_eq_one Equiv.Perm.card_cycleType_eq_one

theorem Disjoint.cycleType {σ τ : Perm α} (h : Disjoint σ τ) :
    (σ * τ).cycleType = σ.cycleType + τ.cycleType :=
  by
  rw [cycle_type_def, cycle_type_def, cycle_type_def, h.cycle_factors_finset_mul_eq_union, ←
    Multiset.map_add, Finset.union_val, multiset.add_eq_union_iff_disjoint.mpr _]
  exact Finset.disjoint_val.2 h.disjoint_cycle_factors_finset
#align equiv.perm.disjoint.cycle_type Equiv.Perm.Disjoint.cycleType

theorem cycleType_inv (σ : Perm α) : σ⁻¹.cycleType = σ.cycleType :=
  cycle_induction_on (fun τ : Perm α => τ⁻¹.cycleType = τ.cycleType) σ rfl
    (fun σ hσ => by rw [hσ.cycle_type, hσ.inv.cycle_type, support_inv]) fun σ τ hστ hc hσ hτ => by
    rw [mul_inv_rev, hστ.cycle_type, ← hσ, ← hτ, add_comm,
      disjoint.cycle_type fun x =>
        Or.imp (fun h : τ x = x => inv_eq_iff_eq.mpr h.symm)
          (fun h : σ x = x => inv_eq_iff_eq.mpr h.symm) (hστ x).symm]
#align equiv.perm.cycle_type_inv Equiv.Perm.cycleType_inv

theorem cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹).cycleType = σ.cycleType :=
  by
  revert τ
  apply cycle_induction_on _ σ
  · intro
    simp
  · intro σ hσ τ
    rw [hσ.cycle_type, hσ.conj.cycle_type, card_support_conj]
  · intro σ τ hd hc hσ hτ π
    rw [← conj_mul, hd.cycle_type, disjoint.cycle_type, hσ, hτ]
    intro a
    apply (hd (π⁻¹ a)).imp _ _ <;>
      · intro h
        rw [perm.mul_apply, perm.mul_apply, h, apply_inv_self]
#align equiv.perm.cycle_type_conj Equiv.Perm.cycleType_conj

theorem sum_cycleType (σ : Perm α) : σ.cycleType.Sum = σ.support.card :=
  cycle_induction_on (fun τ : Perm α => τ.cycleType.Sum = τ.support.card) σ
    (by rw [cycle_type_one, sum_zero, support_one, Finset.card_empty])
    (fun σ hσ => by rw [hσ.cycle_type, coe_sum, List.sum_singleton]) fun σ τ hστ hc hσ hτ => by
    rw [hστ.cycle_type, sum_add, hσ, hτ, hστ.card_support_mul]
#align equiv.perm.sum_cycle_type Equiv.Perm.sum_cycleType

theorem sign_of_cycle_type' (σ : Perm α) :
    sign σ = (σ.cycleType.map fun n => -(-1 : ℤˣ) ^ n).Prod :=
  cycle_induction_on (fun τ : Perm α => sign τ = (τ.cycleType.map fun n => -(-1 : ℤˣ) ^ n).Prod) σ
    (by rw [sign_one, cycle_type_one, Multiset.map_zero, prod_zero])
    (fun σ hσ => by
      rw [hσ.sign, hσ.cycle_type, coe_map, coe_prod, List.map_singleton, List.prod_singleton])
    fun σ τ hστ hc hσ hτ => by rw [sign_mul, hσ, hτ, hστ.cycle_type, Multiset.map_add, prod_add]
#align equiv.perm.sign_of_cycle_type' Equiv.Perm.sign_of_cycle_type'

theorem sign_of_cycleType (f : Perm α) :
    sign f = (-1 : ℤˣ) ^ (f.cycleType.Sum + f.cycleType.card) :=
  cycle_induction_on (fun f : Perm α => sign f = (-1 : ℤˣ) ^ (f.cycleType.Sum + f.cycleType.card)) f
    (-- base_one
    by rw [Equiv.Perm.cycleType_one, sign_one, Multiset.sum_zero, Multiset.card_zero, pow_zero])
    (-- base_cycles
    fun f hf => by
      rw [Equiv.Perm.IsCycle.cycleType hf, hf.sign, coe_sum, List.sum_cons, sum_nil, add_zero,
        coe_card, length_singleton, pow_add, pow_one, mul_comm, neg_mul,
        one_mul])-- induction_disjoint
  fun f g hfg hf Pf Pg => by
    rw [Equiv.Perm.Disjoint.cycleType hfg, Multiset.sum_add, Multiset.card_add, ← add_assoc,
      add_comm f.cycle_type.sum g.cycle_type.sum, add_assoc g.cycle_type.sum _ _,
      add_comm g.cycle_type.sum _, add_assoc, pow_add, ← Pf, ← Pg, Equiv.Perm.sign_mul]
#align equiv.perm.sign_of_cycle_type Equiv.Perm.sign_of_cycleType

theorem lcm_cycleType (σ : Perm α) : σ.cycleType.lcm = orderOf σ :=
  cycle_induction_on (fun τ : Perm α => τ.cycleType.lcm = orderOf τ) σ
    (by rw [cycle_type_one, lcm_zero, orderOf_one])
    (fun σ hσ => by rw [hσ.cycle_type, coe_singleton, lcm_singleton, hσ.order_of, normalize_eq])
    fun σ τ hστ hc hσ hτ => by rw [hστ.cycle_type, lcm_add, lcm_eq_nat_lcm, hστ.order_of, hσ, hτ]
#align equiv.perm.lcm_cycle_type Equiv.Perm.lcm_cycleType

theorem dvd_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : n ∣ orderOf σ :=
  by
  rw [← lcm_cycle_type]
  exact dvd_lcm h
#align equiv.perm.dvd_of_mem_cycle_type Equiv.Perm.dvd_of_mem_cycleType

theorem orderOf_cycleOf_dvd_orderOf (f : Perm α) (x : α) : orderOf (cycleOf f x) ∣ orderOf f :=
  by
  by_cases hx : f x = x
  · rw [← cycle_of_eq_one_iff] at hx
    simp [hx]
  · refine' dvd_of_mem_cycle_type _
    rw [cycle_type, Multiset.mem_map]
    refine' ⟨f.cycle_of x, _, _⟩
    · rwa [← Finset.mem_def, cycle_of_mem_cycle_factors_finset_iff, mem_support]
    · simp [(is_cycle_cycle_of _ hx).orderOf]
#align equiv.perm.order_of_cycle_of_dvd_order_of Equiv.Perm.orderOf_cycleOf_dvd_orderOf

theorem two_dvd_card_support {σ : Perm α} (hσ : σ ^ 2 = 1) : 2 ∣ σ.support.card :=
  (congr_arg (Dvd.Dvd 2) σ.sum_cycleType).mp
    (Multiset.dvd_sum fun n hn => by
      rw [le_antisymm
          (Nat.le_of_dvd zero_lt_two <|
            (dvd_of_mem_cycle_type hn).trans <| orderOf_dvd_of_pow_eq_one hσ)
          (two_le_of_mem_cycle_type hn)])
#align equiv.perm.two_dvd_card_support Equiv.Perm.two_dvd_card_support

theorem cycleType_prime_order {σ : Perm α} (hσ : (orderOf σ).Prime) :
    ∃ n : ℕ, σ.cycleType = replicate (n + 1) (orderOf σ) :=
  by
  rw [eq_replicate_of_mem fun n hn =>
      or_iff_not_imp_left.mp (hσ.eq_one_or_self_of_dvd n (dvd_of_mem_cycle_type hn))
        (one_lt_of_mem_cycle_type hn).ne']
  use σ.cycle_type.card - 1
  rw [tsub_add_cancel_of_le]
  rw [Nat.succ_le_iff, pos_iff_ne_zero, Ne, card_cycle_type_eq_zero]
  intro H
  rw [H, orderOf_one] at hσ
  exact hσ.ne_one rfl
#align equiv.perm.cycle_type_prime_order Equiv.Perm.cycleType_prime_order

theorem isCycle_of_prime_order {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : σ.support.card < 2 * orderOf σ) : σ.IsCycle :=
  by
  obtain ⟨n, hn⟩ := cycle_type_prime_order h1
  rw [← σ.sum_cycle_type, hn, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    mul_lt_mul_right (orderOf_pos σ), Nat.succ_lt_succ_iff, Nat.lt_succ_iff, le_zero_iff] at h2
  rw [← card_cycle_type_eq_one, hn, card_replicate, h2]
#align equiv.perm.is_cycle_of_prime_order Equiv.Perm.isCycle_of_prime_order

theorem cycleType_le_of_mem_cycleFactorsFinset {f g : Perm α} (hf : f ∈ g.cycleFactorsFinset) :
    f.cycleType ≤ g.cycleType :=
  by
  rw [mem_cycle_factors_finset_iff] at hf
  rw [cycle_type_def, cycle_type_def, hf.left.cycle_factors_finset_eq_singleton]
  refine' map_le_map _
  simpa [← Finset.mem_def, mem_cycle_factors_finset_iff] using hf
#align equiv.perm.cycle_type_le_of_mem_cycle_factors_finset Equiv.Perm.cycleType_le_of_mem_cycleFactorsFinset

theorem cycleType_mul_mem_cycleFactorsFinset_eq_sub {f g : Perm α} (hf : f ∈ g.cycleFactorsFinset) :
    (g * f⁻¹).cycleType = g.cycleType - f.cycleType :=
  by
  suffices (g * f⁻¹).cycleType + f.cycle_type = g.cycle_type - f.cycle_type + f.cycle_type
    by
    rw [tsub_add_cancel_of_le (cycle_type_le_of_mem_cycle_factors_finset hf)] at this
    simp [← this]
  simp [← (disjoint_mul_inv_of_mem_cycle_factors_finset hf).cycleType,
    tsub_add_cancel_of_le (cycle_type_le_of_mem_cycle_factors_finset hf)]
#align equiv.perm.cycle_type_mul_mem_cycle_factors_finset_eq_sub Equiv.Perm.cycleType_mul_mem_cycleFactorsFinset_eq_sub

theorem isConj_of_cycleType_eq {σ τ : Perm α} (h : cycleType σ = cycleType τ) : IsConj σ τ :=
  by
  revert τ
  apply cycle_induction_on _ σ
  · intro τ h
    rw [cycle_type_one, eq_comm, cycle_type_eq_zero] at h
    rw [h]
  · intro σ hσ τ hστ
    have hτ := card_cycle_type_eq_one.2 hσ
    rw [hστ, card_cycle_type_eq_one] at hτ
    apply hσ.is_conj hτ
    rw [hσ.cycle_type, hτ.cycle_type, coe_eq_coe, singleton_perm] at hστ
    simp only [and_true_iff, eq_self_iff_true] at hστ
    exact hστ
  · intro σ τ hστ hσ h1 h2 π hπ
    rw [hστ.cycle_type] at hπ
    · have h : σ.support.card ∈ map (Finset.card ∘ perm.support) π.cycle_factors_finset.val := by
        simp [← cycle_type_def, ← hπ, hσ.cycle_type]
      obtain ⟨σ', hσ'l, hσ'⟩ := multiset.mem_map.mp h
      have key : IsConj (σ' * (π * σ'⁻¹)) π :=
        by
        rw [isConj_iff]
        use σ'⁻¹
        simp [mul_assoc]
      refine' IsConj.trans _ key
      have hs : σ.cycle_type = σ'.cycle_type :=
        by
        rw [← Finset.mem_def, mem_cycle_factors_finset_iff] at hσ'l
        rw [hσ.cycle_type, ← hσ', hσ'l.left.cycle_type]
      refine' hστ.is_conj_mul (h1 hs) (h2 _) _
      · rw [cycle_type_mul_mem_cycle_factors_finset_eq_sub, ← hπ, add_comm, hs,
          add_tsub_cancel_right]
        rwa [Finset.mem_def]
      · exact (disjoint_mul_inv_of_mem_cycle_factors_finset hσ'l).symm
#align equiv.perm.is_conj_of_cycle_type_eq Equiv.Perm.isConj_of_cycleType_eq

theorem isConj_iff_cycleType_eq {σ τ : Perm α} : IsConj σ τ ↔ σ.cycleType = τ.cycleType :=
  ⟨fun h => by
    obtain ⟨π, rfl⟩ := isConj_iff.1 h
    rw [cycle_type_conj], isConj_of_cycleType_eq⟩
#align equiv.perm.is_conj_iff_cycle_type_eq Equiv.Perm.isConj_iff_cycleType_eq

@[simp]
theorem cycleType_extendDomain {β : Type _} [Fintype β] [DecidableEq β] {p : β → Prop}
    [DecidablePred p] (f : α ≃ Subtype p) {g : Perm α} :
    cycleType (g.extendDomain f) = cycleType g :=
  by
  apply cycle_induction_on _ g
  · rw [extend_domain_one, cycle_type_one, cycle_type_one]
  · intro σ hσ
    rw [(hσ.extend_domain f).cycleType, hσ.cycle_type, card_support_extend_domain]
  · intro σ τ hd hc hσ hτ
    rw [hd.cycle_type, ← extend_domain_mul, (hd.extend_domain f).cycleType, hσ, hτ]
#align equiv.perm.cycle_type_extend_domain Equiv.Perm.cycleType_extendDomain

theorem cycleType_ofSubtype {p : α → Prop} [DecidablePred p] {g : Perm (Subtype p)} :
    cycleType g.ofSubtype = cycleType g :=
  cycleType_extendDomain (Equiv.refl (Subtype p))
#align equiv.perm.cycle_type_of_subtype Equiv.Perm.cycleType_ofSubtype

theorem mem_cycleType_iff {n : ℕ} {σ : Perm α} :
    n ∈ cycleType σ ↔ ∃ c τ : Perm α, σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ c.support.card = n :=
  by
  constructor
  · intro h
    obtain ⟨l, rfl, hlc, hld⟩ := trunc_cycle_factors σ
    rw [cycle_type_eq _ rfl hlc hld] at h
    obtain ⟨c, cl, rfl⟩ := List.exists_of_mem_map' h
    rw [(List.perm_cons_erase cl).pairwise_iff fun _ _ hd => _] at hld
    swap
    · exact hd.symm
    refine' ⟨c, (l.erase c).Prod, _, _, hlc _ cl, rfl⟩
    ·
      rw [← List.prod_cons,
        (List.perm_cons_erase cl).symm.prod_eq' (hld.imp fun _ _ => disjoint.commute)]
    · exact disjoint_prod_right _ fun g => List.rel_of_pairwise_cons hld
  · rintro ⟨c, t, rfl, hd, hc, rfl⟩
    simp [hd.cycle_type, hc.cycle_type]
#align equiv.perm.mem_cycle_type_iff Equiv.Perm.mem_cycleType_iff

theorem le_card_support_of_mem_cycleType {n : ℕ} {σ : Perm α} (h : n ∈ cycleType σ) :
    n ≤ σ.support.card :=
  (le_sum_of_mem h).trans (le_of_eq σ.sum_cycleType)
#align equiv.perm.le_card_support_of_mem_cycle_type Equiv.Perm.le_card_support_of_mem_cycleType

theorem cycleType_of_card_le_mem_cycleType_add_two {n : ℕ} {g : Perm α}
    (hn2 : Fintype.card α < n + 2) (hng : n ∈ g.cycleType) : g.cycleType = {n} :=
  by
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycle_type_iff.1 hng
  by_cases g'1 : g' = 1
  · rw [hd.cycle_type, hc.cycle_type, coe_singleton, g'1, cycle_type_one, add_zero]
  contrapose! hn2
  apply le_trans _ (c * g').support.card_le_univ
  rw [hd.card_support_mul]
  exact add_le_add_left (two_le_card_support_of_ne_one g'1) _
#align equiv.perm.cycle_type_of_card_le_mem_cycle_type_add_two Equiv.Perm.cycleType_of_card_le_mem_cycleType_add_two

end CycleType

theorem card_compl_support_modEq [DecidableEq α] {p n : ℕ} [hp : Fact p.Prime] {σ : Perm α}
    (hσ : σ ^ p ^ n = 1) : σ.supportᶜ.card ≡ Fintype.card α [MOD p] :=
  by
  rw [Nat.modEq_iff_dvd' σ.supportᶜ.card_le_univ, ← Finset.card_compl, compl_compl]
  refine' (congr_arg _ σ.sum_cycle_type).mp (Multiset.dvd_sum fun k hk => _)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hσ)
  obtain ⟨l, -, rfl⟩ :=
    (Nat.dvd_prime_pow hp.out).mp ((congr_arg _ hm).mp (dvd_of_mem_cycle_type hk))
  exact dvd_pow_self _ fun h => (one_lt_of_mem_cycle_type hk).Ne <| by rw [h, pow_zero]
#align equiv.perm.card_compl_support_modeq Equiv.Perm.card_compl_support_modEq

theorem exists_fixed_point_of_prime {p n : ℕ} [hp : Fact p.Prime] (hα : ¬p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) : ∃ a : α, σ a = a := by
  classical
    contrapose! hα
    simp_rw [← mem_support] at hα
    exact
      nat.modeq_zero_iff_dvd.mp
        ((congr_arg _
              (finset.card_eq_zero.mpr (compl_eq_bot.mpr (finset.eq_univ_iff_forall.mpr hα)))).mp
          (card_compl_support_modeq hσ).symm)
#align equiv.perm.exists_fixed_point_of_prime Equiv.Perm.exists_fixed_point_of_prime

theorem exists_fixed_point_of_prime' {p n : ℕ} [hp : Fact p.Prime] (hα : p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) {a : α} (ha : σ a = a) : ∃ b : α, σ b = b ∧ b ≠ a := by
  classical
    have h : ∀ b : α, b ∈ σ.supportᶜ ↔ σ b = b := fun b => by
      rw [Finset.mem_compl, mem_support, Classical.not_not]
    obtain ⟨b, hb1, hb2⟩ :=
      Finset.exists_ne_of_one_lt_card
        (lt_of_lt_of_le hp.out.one_lt
          (Nat.le_of_dvd (finset.card_pos.mpr ⟨a, (h a).mpr ha⟩)
            (nat.modeq_zero_iff_dvd.mp
              ((card_compl_support_modeq hσ).trans (nat.modeq_zero_iff_dvd.mpr hα)))))
        a
    exact ⟨b, (h b).mp hb1, hb2⟩
#align equiv.perm.exists_fixed_point_of_prime' Equiv.Perm.exists_fixed_point_of_prime'

theorem isCycle_of_prime_order' {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : Fintype.card α < 2 * orderOf σ) : σ.IsCycle := by
  classical exact is_cycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2)
#align equiv.perm.is_cycle_of_prime_order' Equiv.Perm.isCycle_of_prime_order'

theorem isCycle_of_prime_order'' {σ : Perm α} (h1 : (Fintype.card α).Prime)
    (h2 : orderOf σ = Fintype.card α) : σ.IsCycle :=
  isCycle_of_prime_order' ((congr_arg Nat.Prime h2).mpr h1)
    (by
      classical
        rw [← one_mul (Fintype.card α), ← h2, mul_lt_mul_right (orderOf_pos σ)]
        exact one_lt_two)
#align equiv.perm.is_cycle_of_prime_order'' Equiv.Perm.isCycle_of_prime_order''

section Cauchy

variable (G : Type _) [Group G] (n : ℕ)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectorsProdEqOne : Set (Vector G n) :=
  { v | v.toList.Prod = 1 }
#align equiv.perm.vectors_prod_eq_one Equiv.Perm.vectorsProdEqOne

namespace VectorsProdEqOne

theorem mem_iff {n : ℕ} (v : Vector G n) : v ∈ vectorsProdEqOne G n ↔ v.toList.Prod = 1 :=
  Iff.rfl
#align equiv.perm.vectors_prod_eq_one.mem_iff Equiv.Perm.vectorsProdEqOne.mem_iff

theorem zero_eq : vectorsProdEqOne G 0 = {Vector.nil} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨Eq.refl (1 : G), fun v hv => v.eq_nil⟩
#align equiv.perm.vectors_prod_eq_one.zero_eq Equiv.Perm.vectorsProdEqOne.zero_eq

theorem one_eq : vectorsProdEqOne G 1 = {Vector.nil.cons 1} :=
  by
  simp_rw [Set.eq_singleton_iff_unique_mem, mem_iff, Vector.toList_singleton, List.prod_singleton,
    Vector.head_cons]
  exact ⟨rfl, fun v hv => v.cons_head_tail.symm.trans (congr_arg₂ Vector.cons hv v.tail.eq_nil)⟩
#align equiv.perm.vectors_prod_eq_one.one_eq Equiv.Perm.vectorsProdEqOne.one_eq

instance zeroUnique : Unique (vectorsProdEqOne G 0) :=
  by
  rw [zero_eq]
  exact Set.uniqueSingleton Vector.nil
#align equiv.perm.vectors_prod_eq_one.zero_unique Equiv.Perm.vectorsProdEqOne.zeroUnique

instance oneUnique : Unique (vectorsProdEqOne G 1) :=
  by
  rw [one_eq]
  exact Set.uniqueSingleton (vector.nil.cons 1)
#align equiv.perm.vectors_prod_eq_one.one_unique Equiv.Perm.vectorsProdEqOne.oneUnique

/-- Given a vector `v` of length `n`, make a vector of length `n + 1` whose product is `1`,
by appending the inverse of the product of `v`. -/
@[simps]
def vectorEquiv : Vector G n ≃ vectorsProdEqOne G (n + 1)
    where
  toFun v :=
    ⟨v.toList.Prod⁻¹ ::ᵥ v, by rw [mem_iff, Vector.toList_cons, List.prod_cons, inv_mul_self]⟩
  invFun v := v.1.tail
  left_inv v := v.tail_cons v.toList.Prod⁻¹
  right_inv v :=
    Subtype.ext
      ((congr_arg₂ Vector.cons
            (eq_inv_of_mul_eq_one_left
                (by
                  rw [← List.prod_cons, ← Vector.toList_cons, v.1.cons_head!_tail]
                  exact v.2)).symm
            rfl).trans
        v.1.cons_head!_tail)
#align equiv.perm.vectors_prod_eq_one.vector_equiv Equiv.Perm.vectorsProdEqOne.vectorEquiv

/-- Given a vector `v` of length `n` whose product is 1, make a vector of length `n - 1`,
by deleting the last entry of `v`. -/
def equivVector : vectorsProdEqOne G n ≃ Vector G (n - 1) :=
  ((vectorEquiv G (n - 1)).trans
      (if hn : n = 0 then
        show vectorsProdEqOne G (n - 1 + 1) ≃ vectorsProdEqOne G n
          by
          rw [hn]
          apply equiv_of_unique
      else by rw [tsub_add_cancel_of_le (Nat.pos_of_ne_zero hn).nat_succ_le])).symm
#align equiv.perm.vectors_prod_eq_one.equiv_vector Equiv.Perm.vectorsProdEqOne.equivVector

instance [Fintype G] : Fintype (vectorsProdEqOne G n) :=
  Fintype.ofEquiv (Vector G (n - 1)) (equivVector G n).symm

theorem card [Fintype G] : Fintype.card (vectorsProdEqOne G n) = Fintype.card G ^ (n - 1) :=
  (Fintype.card_congr (equivVector G n)).trans (card_vector (n - 1))
#align equiv.perm.vectors_prod_eq_one.card Equiv.Perm.vectorsProdEqOne.card

variable {G n} {g : G} (v : vectorsProdEqOne G n) (j k : ℕ)

/-- Rotate a vector whose product is 1. -/
def rotate : vectorsProdEqOne G n :=
  ⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, List.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩
#align equiv.perm.vectors_prod_eq_one.rotate Equiv.Perm.vectorsProdEqOne.rotate

theorem rotate_zero : rotate v 0 = v :=
  Subtype.ext (Subtype.ext v.1.1.rotate_zero)
#align equiv.perm.vectors_prod_eq_one.rotate_zero Equiv.Perm.vectorsProdEqOne.rotate_zero

theorem rotate_rotate : rotate (rotate v j) k = rotate v (j + k) :=
  Subtype.ext (Subtype.ext (v.1.1.rotate_rotate j k))
#align equiv.perm.vectors_prod_eq_one.rotate_rotate Equiv.Perm.vectorsProdEqOne.rotate_rotate

theorem rotate_length : rotate v n = v :=
  Subtype.ext (Subtype.ext ((congr_arg _ v.1.2.symm).trans v.1.1.rotate_length))
#align equiv.perm.vectors_prod_eq_one.rotate_length Equiv.Perm.vectorsProdEqOne.rotate_length

end VectorsProdEqOne

/-- For every prime `p` dividing the order of a finite group `G` there exists an element of order
`p` in `G`. This is known as Cauchy's theorem. -/
theorem exists_prime_orderOf_dvd_card {G : Type _} [Group G] [Fintype G] (p : ℕ) [hp : Fact p.Prime]
    (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p :=
  by
  have hp' : p - 1 ≠ 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_lt hp.out.one_lt)
  have Scard :=
    calc
      p ∣ Fintype.card G ^ (p - 1) := hdvd.trans (dvd_pow (dvd_refl _) hp')
      _ = Fintype.card (vectors_prod_eq_one G p) := (vectors_prod_eq_one.card G p).symm
      
  let f : ℕ → vectors_prod_eq_one G p → vectors_prod_eq_one G p := fun k v =>
    vectors_prod_eq_one.rotate v k
  have hf1 : ∀ v, f 0 v = v := vectors_prod_eq_one.rotate_zero
  have hf2 : ∀ j k v, f k (f j v) = f (j + k) v := fun j k v =>
    vectors_prod_eq_one.rotate_rotate v j k
  have hf3 : ∀ v, f p v = v := vectors_prod_eq_one.rotate_length
  let σ :=
    Equiv.mk (f 1) (f (p - 1)) (fun s => by rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
      fun s => by rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]
  have hσ : ∀ k v, (σ ^ k) v = f k v := fun k v =>
    Nat.rec (hf1 v).symm (fun k hk => Eq.trans (congr_arg σ hk) (hf2 k 1 v)) k
  replace hσ : σ ^ p ^ 1 = 1 := perm.ext fun v => by rw [pow_one, hσ, hf3, one_apply]
  let v₀ : vectors_prod_eq_one G p :=
    ⟨Vector.replicate p 1, (List.prod_replicate p 1).trans (one_pow p)⟩
  have hv₀ : σ v₀ = v₀ := Subtype.ext (Subtype.ext (List.rotate_replicate (1 : G) p 1))
  obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀
  refine'
    Exists.imp (fun g hg => orderOf_eq_prime _ fun hg' => hv2 _)
      (list.rotate_one_eq_self_iff_eq_replicate.mp (subtype.ext_iff.mp (subtype.ext_iff.mp hv1)))
  · rw [← List.prod_replicate, ← v.1.2, ← hg, show v.val.val.prod = 1 from v.2]
  · rw [Subtype.ext_iff_val, Subtype.ext_iff_val, hg, hg', v.1.2]
    rfl
#align exists_prime_order_of_dvd_card exists_prime_orderOf_dvd_card

/-- For every prime `p` dividing the order of a finite additive group `G` there exists an element of
order `p` in `G`. This is the additive version of Cauchy's theorem. -/
theorem exists_prime_addOrderOf_dvd_card {G : Type _} [AddGroup G] [Fintype G] (p : ℕ)
    [hp : Fact p.Prime] (hdvd : p ∣ Fintype.card G) : ∃ x : G, addOrderOf x = p :=
  @exists_prime_orderOf_dvd_card (Multiplicative G) _ _ _ _ hdvd
#align exists_prime_add_order_of_dvd_card exists_prime_addOrderOf_dvd_card

attribute [to_additive exists_prime_addOrderOf_dvd_card] exists_prime_orderOf_dvd_card

end Cauchy

theorem subgroup_eq_top_of_swap_mem [DecidableEq α] {H : Subgroup (Perm α)}
    [d : DecidablePred (· ∈ H)] {τ : Perm α} (h0 : (Fintype.card α).Prime)
    (h1 : Fintype.card α ∣ Fintype.card H) (h2 : τ ∈ H) (h3 : IsSwap τ) : H = ⊤ :=
  by
  haveI : Fact (Fintype.card α).Prime := ⟨h0⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) h1
  have hσ1 : orderOf (σ : perm α) = Fintype.card α := (orderOf_subgroup σ).trans hσ
  have hσ2 : is_cycle ↑σ := is_cycle_of_prime_order'' h0 hσ1
  have hσ3 : (σ : perm α).support = ⊤ :=
    Finset.eq_univ_of_card (σ : perm α).support (hσ2.order_of.symm.trans hσ1)
  have hσ4 : Subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3
  rw [eq_top_iff, ← hσ4, Subgroup.closure_le, Set.insert_subset, Set.singleton_subset_iff]
  exact ⟨Subtype.mem σ, h2⟩
#align equiv.perm.subgroup_eq_top_of_swap_mem Equiv.Perm.subgroup_eq_top_of_swap_mem

section Partition

variable [DecidableEq α]

/-- The partition corresponding to a permutation -/
def partition (σ : Perm α) : (Fintype.card α).partitionₓ
    where
  parts := σ.cycleType + replicate (Fintype.card α - σ.support.card) 1
  parts_pos n hn := by
    cases' mem_add.mp hn with hn hn
    · exact zero_lt_one.trans (one_lt_of_mem_cycle_type hn)
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
  parts_sum := by
    rw [sum_add, sum_cycle_type, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one,
      add_tsub_cancel_of_le σ.support.card_le_univ]
#align equiv.perm.partition Equiv.Perm.partition

theorem parts_partition {σ : Perm α} :
    σ.partitionₓ.parts = σ.cycleType + replicate (Fintype.card α - σ.support.card) 1 :=
  rfl
#align equiv.perm.parts_partition Equiv.Perm.parts_partition

theorem filter_parts_partition_eq_cycleType {σ : Perm α} :
    ((partition σ).parts.filterₓ fun n => 2 ≤ n) = σ.cycleType :=
  by
  rw [parts_partition, filter_add, Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycle_type,
    Multiset.filter_eq_nil.2 fun a h => _, add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  decide
#align equiv.perm.filter_parts_partition_eq_cycle_type Equiv.Perm.filter_parts_partition_eq_cycleType

theorem partition_eq_of_isConj {σ τ : Perm α} : IsConj σ τ ↔ σ.partitionₓ = τ.partitionₓ :=
  by
  rw [is_conj_iff_cycle_type_eq]
  refine' ⟨fun h => _, fun h => _⟩
  ·
    rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ← sum_cycle_type, ← sum_cycle_type,
      h]
  · rw [← filter_parts_partition_eq_cycle_type, ← filter_parts_partition_eq_cycle_type, h]
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
  rw [← sum_cycle_type, h.cycle_type, Multiset.sum_singleton]
#align equiv.perm.is_three_cycle.card_support Equiv.Perm.IsThreeCycle.card_support

theorem card_support_eq_three_iff : σ.support.card = 3 ↔ σ.IsThreeCycle :=
  by
  refine' ⟨fun h => _, is_three_cycle.card_support⟩
  by_cases h0 : σ.cycle_type = 0
  · rw [← sum_cycle_type, h0, sum_zero] at h
    exact (ne_of_lt zero_lt_three h).elim
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0
  by_cases h1 : σ.cycle_type.erase n = 0
  · rw [← sum_cycle_type, ← cons_erase hn, h1, cons_zero, Multiset.sum_singleton] at h
    rw [is_three_cycle, ← cons_erase hn, h1, h, ← cons_zero]
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1
  rw [← sum_cycle_type, ← cons_erase hn, ← cons_erase hm, Multiset.sum_cons, Multiset.sum_cons] at h
  -- TODO: linarith [...] should solve this directly
  have : ∀ {k}, 2 ≤ m → 2 ≤ n → n + (m + k) = 3 → False :=
    by
    intros
    linarith
  cases this (two_le_of_mem_cycle_type (mem_of_mem_erase hm)) (two_le_of_mem_cycle_type hn) h
#align card_support_eq_three_iff card_support_eq_three_iff

theorem isCycle (h : IsThreeCycle σ) : IsCycle σ := by
  rw [← card_cycle_type_eq_one, h.cycle_type, card_singleton]
#align equiv.perm.is_three_cycle.is_cycle Equiv.Perm.IsThreeCycle.isCycle

theorem sign (h : IsThreeCycle σ) : sign σ = 1 :=
  by
  rw [Equiv.Perm.sign_of_cycleType, h.cycle_type]
  rfl
#align equiv.perm.is_three_cycle.sign Equiv.Perm.IsThreeCycle.sign

theorem inv {f : Perm α} (h : IsThreeCycle f) : IsThreeCycle f⁻¹ := by
  rwa [is_three_cycle, cycle_type_inv]
#align equiv.perm.is_three_cycle.inv Equiv.Perm.IsThreeCycle.inv

@[simp]
theorem inv_iff {f : Perm α} : IsThreeCycle f⁻¹ ↔ IsThreeCycle f :=
  ⟨by
    rw [← inv_inv f]
    apply inv, inv⟩
#align equiv.perm.is_three_cycle.inv_iff Equiv.Perm.IsThreeCycle.inv_iff

theorem orderOf {g : Perm α} (ht : IsThreeCycle g) : orderOf g = 3 := by
  rw [← lcm_cycle_type, ht.cycle_type, Multiset.lcm_singleton, normalize_eq]
#align equiv.perm.is_three_cycle.order_of Equiv.Perm.IsThreeCycle.orderOf

theorem isThreeCycle_sq {g : Perm α} (ht : IsThreeCycle g) : IsThreeCycle (g * g) :=
  by
  rw [← pow_two, ← card_support_eq_three_iff, support_pow_coprime, ht.card_support]
  rw [ht.order_of, Nat.coprime_iff_gcd_eq_one]
  norm_num
#align equiv.perm.is_three_cycle.is_three_cycle_sq Equiv.Perm.IsThreeCycle.isThreeCycle_sq

end IsThreeCycle

section

variable [DecidableEq α]

theorem isThreeCycle_swap_mul_swap_same {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    IsThreeCycle (swap a b * swap a c) :=
  by
  suffices h : support (swap a b * swap a c) = {a, b, c}
  · rw [← card_support_eq_three_iff, h]
    simp [ab, ac, bc]
  apply le_antisymm ((support_mul_le _ _).trans fun x => _) fun x hx => _
  · simp [ab, ac, bc]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_support]
    simp only [perm.coe_mul, Function.comp_apply, Ne.def]
    obtain rfl | rfl | rfl := hx
    · rw [swap_apply_left, swap_apply_of_ne_of_ne ac.symm bc.symm]
      exact ac.symm
    · rw [swap_apply_of_ne_of_ne ab.symm bc, swap_apply_right]
      exact ab
    · rw [swap_apply_right, swap_apply_left]
      exact bc
#align equiv.perm.is_three_cycle_swap_mul_swap_same Equiv.Perm.isThreeCycle_swap_mul_swap_same

open Subgroup

theorem swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
    swap a b * swap a c ∈ closure { σ : Perm α | IsThreeCycle σ } :=
  by
  by_cases bc : b = c
  · subst bc
    simp [one_mem]
  exact subset_closure (is_three_cycle_swap_mul_swap_same ab ac bc)
#align equiv.perm.swap_mul_swap_same_mem_closure_three_cycles Equiv.Perm.swap_mul_swap_same_mem_closure_three_cycles

theorem IsSwap.mul_mem_closure_three_cycles {σ τ : Perm α} (hσ : IsSwap σ) (hτ : IsSwap τ) :
    σ * τ ∈ closure { σ : Perm α | IsThreeCycle σ } :=
  by
  obtain ⟨a, b, ab, rfl⟩ := hσ
  obtain ⟨c, d, cd, rfl⟩ := hτ
  by_cases ac : a = c
  · subst ac
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d) := by
    simp [swap_comm c a, mul_assoc]
  rw [h']
  exact
    mul_mem (swap_mul_swap_same_mem_closure_three_cycles ab ac)
      (swap_mul_swap_same_mem_closure_three_cycles (Ne.symm ac) cd)
#align equiv.perm.is_swap.mul_mem_closure_three_cycles Equiv.Perm.IsSwap.mul_mem_closure_three_cycles

end

end Equiv.Perm

