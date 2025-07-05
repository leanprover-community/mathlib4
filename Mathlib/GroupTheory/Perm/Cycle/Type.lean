/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Combinatorics.Enumerative.Partition
import Mathlib.Data.List.Rotate
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Tactic.NormNum.GCD

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

open scoped Finset

namespace Equiv.Perm

open List (Vector)
open Equiv List Multiset

variable {α : Type*} [Fintype α]

section CycleType

variable [DecidableEq α]

/-- The cycle type of a permutation -/
def cycleType (σ : Perm α) : Multiset ℕ :=
  σ.cycleFactorsFinset.1.map (Finset.card ∘ support)

theorem cycleType_def (σ : Perm α) :
    σ.cycleType = σ.cycleFactorsFinset.1.map (Finset.card ∘ support) :=
  rfl

theorem cycleType_eq' {σ : Perm α} (s : Finset (Perm α)) (h1 : ∀ f : Perm α, f ∈ s → f.IsCycle)
    (h2 : (s : Set (Perm α)).Pairwise Disjoint)
    (h0 : s.noncommProd id (h2.imp fun _ _ => Disjoint.commute) = σ) :
    σ.cycleType = s.1.map (Finset.card ∘ support) := by
  rw [cycleType_def]
  congr
  rw [cycleFactorsFinset_eq_finset]
  exact ⟨h1, h2, h0⟩

theorem cycleType_eq {σ : Perm α} (l : List (Perm α)) (h0 : l.prod = σ)
    (h1 : ∀ σ : Perm α, σ ∈ l → σ.IsCycle) (h2 : l.Pairwise Disjoint) :
    σ.cycleType = l.map (Finset.card ∘ support) := by
  have hl : l.Nodup := nodup_of_pairwise_disjoint_cycles h1 h2
  rw [cycleType_eq' l.toFinset]
  · simp [List.dedup_eq_self.mpr hl, Function.comp_def]
  · simpa using h1
  · simpa [hl] using h2
  · simp [hl, h0]

theorem CycleType.count_def {σ : Perm α} (n : ℕ) :
    σ.cycleType.count n =
      Fintype.card {c : σ.cycleFactorsFinset // #(c : Perm α).support = n } := by
  -- work on the LHS
  rw [cycleType, Multiset.count_eq_card_filter_eq]
  -- rewrite the `Fintype.card` as a `Finset.card`
  rw [Fintype.subtype_card, Finset.univ_eq_attach, Finset.filter_attach',
    Finset.card_map, Finset.card_attach]
  simp only [Function.comp_apply, Finset.card, Finset.filter_val,
    Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro d h
  simp only [eq_comm, Finset.mem_val.mp h, exists_const]

@[simp]
theorem cycleType_eq_zero {σ : Perm α} : σ.cycleType = 0 ↔ σ = 1 := by
  simp [cycleType_def, cycleFactorsFinset_eq_empty_iff]

@[simp]
theorem cycleType_one : (1 : Perm α).cycleType = 0 := cycleType_eq_zero.2 rfl

theorem card_cycleType_eq_zero {σ : Perm α} : Multiset.card σ.cycleType = 0 ↔ σ = 1 := by
  rw [card_eq_zero, cycleType_eq_zero]

theorem card_cycleType_pos {σ : Perm α} : 0 < Multiset.card σ.cycleType ↔ σ ≠ 1 :=
  pos_iff_ne_zero.trans card_cycleType_eq_zero.not

theorem two_le_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : 2 ≤ n := by
  simp only [cycleType_def, ← Finset.mem_def, Function.comp_apply, Multiset.mem_map,
    mem_cycleFactorsFinset_iff] at h
  obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h
  exact hc.two_le_card_support

theorem one_lt_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : 1 < n :=
  two_le_of_mem_cycleType h

theorem IsCycle.cycleType {σ : Perm α} (hσ : IsCycle σ) : σ.cycleType = {#σ.support} :=
  cycleType_eq [σ] (mul_one σ) (fun _τ hτ => (congr_arg IsCycle (List.mem_singleton.mp hτ)).mpr hσ)
    (List.pairwise_singleton Disjoint σ)

theorem card_cycleType_eq_one {σ : Perm α} : Multiset.card σ.cycleType = 1 ↔ σ.IsCycle := by
  rw [card_eq_one]
  simp_rw [cycleType_def, Multiset.map_eq_singleton, ← Finset.singleton_val, Finset.val_inj,
    cycleFactorsFinset_eq_singleton_iff]
  grind

theorem Disjoint.cycleType {σ τ : Perm α} (h : Disjoint σ τ) :
    (σ * τ).cycleType = σ.cycleType + τ.cycleType := by
  rw [cycleType_def, cycleType_def, cycleType_def, h.cycleFactorsFinset_mul_eq_union, ←
    Multiset.map_add, Finset.union_val, Multiset.add_eq_union_iff_disjoint.mpr _]
  exact Finset.disjoint_val.2 h.disjoint_cycleFactorsFinset

@[simp]
theorem cycleType_inv (σ : Perm α) : σ⁻¹.cycleType = σ.cycleType :=
  cycle_induction_on (P := fun τ : Perm α => τ⁻¹.cycleType = τ.cycleType) σ rfl
    (fun σ hσ => by simp only [hσ.cycleType, hσ.inv.cycleType, support_inv])
    fun σ τ hστ _ hσ hτ => by
      simp only [mul_inv_rev, hστ.cycleType, hστ.symm.inv_left.inv_right.cycleType, hσ, hτ,
        add_comm]

@[simp]
theorem cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹).cycleType = σ.cycleType := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, hσ.conj.cycleType, card_support_conj]
  | induction_disjoint σ π hd _ hσ hπ =>
    rw [← conj_mul, hd.cycleType, (hd.conj _).cycleType, hσ, hπ]

theorem sum_cycleType (σ : Perm α) : σ.cycleType.sum = #σ.support := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => rw [hσ.cycleType, Multiset.sum_singleton]
  | induction_disjoint σ τ hd _ hσ hτ => rw [hd.cycleType, sum_add, hσ, hτ, hd.card_support_mul]

theorem card_fixedPoints (σ : Equiv.Perm α) :
    Fintype.card (Function.fixedPoints σ) = Fintype.card α - σ.cycleType.sum := by
  rw [Equiv.Perm.sum_cycleType, ← Finset.card_compl, Fintype.card_ofFinset]
  congr; aesop

theorem sign_of_cycleType' (σ : Perm α) :
    sign σ = (σ.cycleType.map fun n => -(-1 : ℤˣ) ^ n).prod := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.sign]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hσ, hτ, hd.cycleType]

theorem sign_of_cycleType (f : Perm α) :
    sign f = (-1 : ℤˣ) ^ (f.cycleType.sum + Multiset.card f.cycleType) := by
  rw [sign_of_cycleType']
  induction f.cycleType using Multiset.induction_on with
  | empty => rfl
  | cons a s ihs =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons, ihs]
    simp only [pow_add, pow_one, neg_mul, mul_neg, mul_assoc, mul_one]

@[simp]
theorem lcm_cycleType (σ : Perm α) : σ.cycleType.lcm = orderOf σ := by
  induction σ using cycle_induction_on with
  | base_one => simp
  | base_cycles σ hσ => simp [hσ.cycleType, hσ.orderOf]
  | induction_disjoint σ τ hd _ hσ hτ => simp [hd.cycleType, hd.orderOf, lcm_eq_nat_lcm, hσ, hτ]

theorem dvd_of_mem_cycleType {σ : Perm α} {n : ℕ} (h : n ∈ σ.cycleType) : n ∣ orderOf σ := by
  rw [← lcm_cycleType]
  exact dvd_lcm h

theorem orderOf_cycleOf_dvd_orderOf (f : Perm α) (x : α) : orderOf (cycleOf f x) ∣ orderOf f := by
  by_cases hx : f x = x
  · rw [← cycleOf_eq_one_iff] at hx
    simp [hx]
  · refine dvd_of_mem_cycleType ?_
    rw [cycleType, Multiset.mem_map]
    refine ⟨f.cycleOf x, ?_, ?_⟩
    · rwa [← Finset.mem_def, cycleOf_mem_cycleFactorsFinset_iff, mem_support]
    · simp [(isCycle_cycleOf _ hx).orderOf]

theorem two_dvd_card_support {σ : Perm α} (hσ : σ ^ 2 = 1) : 2 ∣ #σ.support :=
  (congr_arg (Dvd.dvd 2) σ.sum_cycleType).mp
    (Multiset.dvd_sum fun n hn => by
      rw [_root_.le_antisymm
          (Nat.le_of_dvd zero_lt_two <|
            (dvd_of_mem_cycleType hn).trans <| orderOf_dvd_of_pow_eq_one hσ)
          (two_le_of_mem_cycleType hn)])

theorem cycleType_prime_order {σ : Perm α} (hσ : (orderOf σ).Prime) :
    ∃ n : ℕ, σ.cycleType = Multiset.replicate (n + 1) (orderOf σ) := by
  refine ⟨Multiset.card σ.cycleType - 1, eq_replicate.2 ⟨?_, fun n hn ↦ ?_⟩⟩
  · rw [tsub_add_cancel_of_le]
    rw [Nat.succ_le_iff, card_cycleType_pos, Ne, ← orderOf_eq_one_iff]
    exact hσ.ne_one
  · exact (hσ.eq_one_or_self_of_dvd n (dvd_of_mem_cycleType hn)).resolve_left
      (one_lt_of_mem_cycleType hn).ne'

theorem pow_prime_eq_one_iff {σ : Perm α} {p : ℕ} [hp : Fact (Nat.Prime p)] :
    σ ^ p = 1 ↔ ∀ c ∈ σ.cycleType, c = p := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType, Multiset.lcm_dvd]
  apply forall_congr'
  exact fun c ↦ ⟨fun hc h ↦ Or.resolve_left (hp.elim.eq_one_or_self_of_dvd c (hc h))
       (Nat.ne_of_lt' (one_lt_of_mem_cycleType h)),
     fun hc h ↦ by rw [hc h]⟩

theorem isCycle_of_prime_order {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : #σ.support < 2 * orderOf σ) : σ.IsCycle := by
  obtain ⟨n, hn⟩ := cycleType_prime_order h1
  rw [← σ.sum_cycleType, hn, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
    mul_lt_mul_right (orderOf_pos σ), Nat.succ_lt_succ_iff, Nat.lt_succ_iff, Nat.le_zero] at h2
  rw [← card_cycleType_eq_one, hn, card_replicate, h2]

theorem cycleType_le_of_mem_cycleFactorsFinset {f g : Perm α} (hf : f ∈ g.cycleFactorsFinset) :
    f.cycleType ≤ g.cycleType := by
  have hf' := mem_cycleFactorsFinset_iff.1 hf
  rw [cycleType_def, cycleType_def, hf'.left.cycleFactorsFinset_eq_singleton]
  refine map_le_map ?_
  simpa only [Finset.singleton_val, singleton_le, Finset.mem_val] using hf

theorem Disjoint.cycleType_mul {f g : Perm α} (h : f.Disjoint g) :
    (f * g).cycleType = f.cycleType + g.cycleType := by
  simp only [Perm.cycleType]
  rw [h.cycleFactorsFinset_mul_eq_union]
  simp only [Finset.union_val, Function.comp_apply]
  rw [← Multiset.add_eq_union_iff_disjoint.mpr _, Multiset.map_add]
  simp only [Finset.disjoint_val, Disjoint.disjoint_cycleFactorsFinset h]

theorem Disjoint.cycleType_noncommProd {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Disjoint (k i) (k j))
    (hs' : Set.Pairwise s fun i j ↦ Commute (k i) (k j) :=
      hs.imp (fun _ _ ↦ Perm.Disjoint.commute)) :
    (s.noncommProd k hs').cycleType = s.sum fun i ↦ (k i).cycleType := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Finset.sum_insert hi]
    rw [Equiv.Perm.Disjoint.cycleType_mul, hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]


theorem cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub
    {f g : Perm α} (hf : f ∈ g.cycleFactorsFinset) :
    (g * f⁻¹).cycleType = g.cycleType - f.cycleType :=
  add_right_cancel (b := f.cycleType) <| by
    rw [← (disjoint_mul_inv_of_mem_cycleFactorsFinset hf).cycleType, inv_mul_cancel_right,
      tsub_add_cancel_of_le (cycleType_le_of_mem_cycleFactorsFinset hf)]

theorem isConj_of_cycleType_eq {σ τ : Perm α} (h : cycleType σ = cycleType τ) : IsConj σ τ := by
  induction σ using cycle_induction_on generalizing τ with
  | base_one =>
    rw [cycleType_one, eq_comm, cycleType_eq_zero] at h
    rw [h]
  | base_cycles σ hσ =>
    have hτ := card_cycleType_eq_one.2 hσ
    rw [h, card_cycleType_eq_one] at hτ
    apply hσ.isConj hτ
    rwa [hσ.cycleType, hτ.cycleType, Multiset.singleton_inj] at h
  | induction_disjoint σ π hd hc hσ hπ =>
    rw [hd.cycleType] at h
    have h' : #σ.support ∈ τ.cycleType := by
      simp [← h, hc.cycleType]
    obtain ⟨σ', hσ'l, hσ'⟩ := Multiset.mem_map.mp h'
    have key : IsConj (σ' * τ * σ'⁻¹) τ := (isConj_iff.2 ⟨σ', rfl⟩).symm
    refine IsConj.trans ?_ key
    rw [mul_assoc]
    have hs : σ.cycleType = σ'.cycleType := by
      rw [← Finset.mem_def, mem_cycleFactorsFinset_iff] at hσ'l
      rw [hc.cycleType, ← hσ', hσ'l.left.cycleType]; rfl
    refine hd.isConj_mul (hσ hs) (hπ ?_) ?_
    · rw [cycleType_mul_inv_mem_cycleFactorsFinset_eq_sub, ← h, add_comm, hs,
        add_tsub_cancel_right]
      rwa [Finset.mem_def]
    · exact (disjoint_mul_inv_of_mem_cycleFactorsFinset hσ'l).symm

theorem isConj_iff_cycleType_eq {σ τ : Perm α} : IsConj σ τ ↔ σ.cycleType = τ.cycleType :=
  ⟨fun h => by
    obtain ⟨π, rfl⟩ := isConj_iff.1 h
    rw [cycleType_conj], isConj_of_cycleType_eq⟩

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

theorem cycleType_ofSubtype {p : α → Prop} [DecidablePred p] {g : Perm (Subtype p)} :
    cycleType (ofSubtype g) = cycleType g :=
  cycleType_extendDomain (Equiv.refl (Subtype p))

theorem mem_cycleType_iff {n : ℕ} {σ : Perm α} :
    n ∈ cycleType σ ↔ ∃ c τ, σ = c * τ ∧ Disjoint c τ ∧ IsCycle c ∧ c.support.card = n := by
  constructor
  · intro h
    obtain ⟨l, rfl, hlc, hld⟩ := truncCycleFactors σ
    rw [cycleType_eq _ rfl hlc hld, Multiset.mem_coe, List.mem_map] at h
    obtain ⟨c, cl, rfl⟩ := h
    rw [(List.perm_cons_erase cl).pairwise_iff @(Disjoint.symmetric)] at hld
    refine ⟨c, (l.erase c).prod, ?_, ?_, hlc _ cl, rfl⟩
    · rw [← List.prod_cons, (List.perm_cons_erase cl).symm.prod_eq' (hld.imp Disjoint.commute)]
    · exact disjoint_prod_right _ fun g => List.rel_of_pairwise_cons hld
  · rintro ⟨c, t, rfl, hd, hc, rfl⟩
    simp [hd.cycleType, hc.cycleType]

theorem le_card_support_of_mem_cycleType {n : ℕ} {σ : Perm α} (h : n ∈ cycleType σ) :
    n ≤ #σ.support :=
  (le_sum_of_mem h).trans (le_of_eq σ.sum_cycleType)

theorem cycleType_of_card_le_mem_cycleType_add_two {n : ℕ} {g : Perm α}
    (hn2 : Fintype.card α < n + 2) (hng : n ∈ g.cycleType) : g.cycleType = {n} := by
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycleType_iff.1 hng
  suffices g'1 : g' = 1 by
    rw [hd.cycleType, hc.cycleType, g'1, cycleType_one, add_zero]
  contrapose! hn2 with g'1
  apply le_trans _ (c * g').support.card_le_univ
  rw [hd.card_support_mul]
  exact add_le_add_left (two_le_card_support_of_ne_one g'1) _

end CycleType

theorem card_compl_support_modEq [DecidableEq α] {p n : ℕ} [hp : Fact p.Prime] {σ : Perm α}
    (hσ : σ ^ p ^ n = 1) : σ.supportᶜ.card ≡ Fintype.card α [MOD p] := by
  rw [Nat.modEq_iff_dvd', ← Finset.card_compl, compl_compl, ← sum_cycleType]
  · refine Multiset.dvd_sum fun k hk => ?_
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hσ)
    obtain ⟨l, -, rfl⟩ := (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ hm).mp (dvd_of_mem_cycleType hk))
    exact dvd_pow_self _ fun h => (one_lt_of_mem_cycleType hk).ne <| by rw [h, pow_zero]
  · exact Finset.card_le_univ _

open Function in
/-- The number of fixed points of a `p ^ n`-th root of the identity function over a finite set
and the set's cardinality have the same residue modulo `p`, where `p` is a prime. -/
theorem card_fixedPoints_modEq [DecidableEq α] {f : Function.End α} {p n : ℕ}
    [hp : Fact p.Prime] (hf : f ^ p ^ n = 1) :
    Fintype.card α ≡ Fintype.card f.fixedPoints [MOD p] := by
  let σ : α ≃ α := ⟨f, f ^ (p ^ n - 1),
    leftInverse_iff_comp.mpr ((pow_sub_mul_pow f (Nat.one_le_pow n p hp.out.pos)).trans hf),
    leftInverse_iff_comp.mpr ((pow_mul_pow_sub f (Nat.one_le_pow n p hp.out.pos)).trans hf)⟩
  have hσ : σ ^ p ^ n = 1 := by
    rw [DFunLike.ext'_iff, coe_pow]
    exact (hom_coe_pow (fun g : Function.End α ↦ g) rfl (fun g h ↦ rfl) f (p ^ n)).symm.trans hf
  suffices Fintype.card f.fixedPoints = (support σ)ᶜ.card from
    this ▸ (card_compl_support_modEq hσ).symm
  suffices f.fixedPoints = (support σ)ᶜ by
    simp only [this]; apply Fintype.card_coe
  simp [σ, Set.ext_iff, IsFixedPt]

theorem exists_fixed_point_of_prime {p n : ℕ} [hp : Fact p.Prime] (hα : ¬p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) : ∃ a : α, σ a = a := by
  classical
    contrapose! hα
    simp_rw [← mem_support, ← Finset.eq_univ_iff_forall] at hα
    exact Nat.modEq_zero_iff_dvd.1 ((congr_arg _ (Finset.card_eq_zero.2 (compl_eq_bot.2 hα))).mp
      (card_compl_support_modEq hσ).symm)

theorem exists_fixed_point_of_prime' {p n : ℕ} [hp : Fact p.Prime] (hα : p ∣ Fintype.card α)
    {σ : Perm α} (hσ : σ ^ p ^ n = 1) {a : α} (ha : σ a = a) : ∃ b : α, σ b = b ∧ b ≠ a := by
  classical
    have h : ∀ b : α, b ∈ σ.supportᶜ ↔ σ b = b := fun b => by
      rw [Finset.mem_compl, mem_support, Classical.not_not]
    obtain ⟨b, hb1, hb2⟩ := Finset.exists_ne_of_one_lt_card (hp.out.one_lt.trans_le
      (Nat.le_of_dvd (Finset.card_pos.mpr ⟨a, (h a).mpr ha⟩) (Nat.modEq_zero_iff_dvd.mp
        ((card_compl_support_modEq hσ).trans (Nat.modEq_zero_iff_dvd.mpr hα))))) a
    exact ⟨b, (h b).mp hb1, hb2⟩

theorem isCycle_of_prime_order' {σ : Perm α} (h1 : (orderOf σ).Prime)
    (h2 : Fintype.card α < 2 * orderOf σ) : σ.IsCycle := by
  classical exact isCycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2)

theorem isCycle_of_prime_order'' {σ : Perm α} (h1 : (Fintype.card α).Prime)
    (h2 : orderOf σ = Fintype.card α) : σ.IsCycle :=
  isCycle_of_prime_order' ((congr_arg Nat.Prime h2).mpr h1) <| by
    rw [← one_mul (Fintype.card α), ← h2, mul_lt_mul_right (orderOf_pos σ)]
    exact one_lt_two

section Cauchy

variable (G : Type*) [Group G] (n : ℕ)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectorsProdEqOne : Set (List.Vector G n) :=
  { v | v.toList.prod = 1 }

namespace VectorsProdEqOne

theorem mem_iff {n : ℕ} (v : List.Vector G n) : v ∈ vectorsProdEqOne G n ↔ v.toList.prod = 1 :=
  Iff.rfl

theorem zero_eq : vectorsProdEqOne G 0 = {Vector.nil} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨Eq.refl (1 : G), fun v _ => v.eq_nil⟩

theorem one_eq : vectorsProdEqOne G 1 = {Vector.nil.cons 1} := by
  simp_rw [Set.eq_singleton_iff_unique_mem, mem_iff, List.Vector.toList_singleton,
    List.prod_singleton, List.Vector.head_cons, true_and]
  exact fun v hv => v.cons_head_tail.symm.trans (congr_arg₂ Vector.cons hv v.tail.eq_nil)

instance zeroUnique : Unique (vectorsProdEqOne G 0) := by
  rw [zero_eq]
  exact Set.uniqueSingleton Vector.nil

instance oneUnique : Unique (vectorsProdEqOne G 1) := by
  rw [one_eq]
  exact Set.uniqueSingleton (Vector.nil.cons 1)

/-- Given a vector `v` of length `n`, make a vector of length `n + 1` whose product is `1`,
by appending the inverse of the product of `v`. -/
@[simps]
def vectorEquiv : List.Vector G n ≃ vectorsProdEqOne G (n + 1) where
  toFun v := ⟨v.toList.prod⁻¹ ::ᵥ v, by
    rw [mem_iff, Vector.toList_cons, List.prod_cons, inv_mul_cancel]⟩
  invFun v := v.1.tail
  left_inv v := v.tail_cons v.toList.prod⁻¹
  right_inv v := Subtype.ext <|
    calc
      v.1.tail.toList.prod⁻¹ ::ᵥ v.1.tail = v.1.head ::ᵥ v.1.tail :=
        congr_arg (· ::ᵥ v.1.tail) <| Eq.symm <| eq_inv_of_mul_eq_one_left <| by
          rw [← List.prod_cons, ← Vector.toList_cons, v.1.cons_head_tail]
          exact v.2
      _ = v.1 := v.1.cons_head_tail

/-- Given a vector `v` of length `n` whose product is 1, make a vector of length `n - 1`,
by deleting the last entry of `v`. -/
def equivVector : ∀ n, vectorsProdEqOne G n ≃ List.Vector G (n - 1)
  | 0 => (ofUnique (vectorsProdEqOne G 0) (vectorsProdEqOne G 1)).trans (vectorEquiv G 0).symm
  | (n + 1) => (vectorEquiv G n).symm

instance [Fintype G] : Fintype (vectorsProdEqOne G n) :=
  Fintype.ofEquiv (List.Vector G (n - 1)) (equivVector G n).symm

theorem card [Fintype G] : Fintype.card (vectorsProdEqOne G n) = Fintype.card G ^ (n - 1) :=
  (Fintype.card_congr (equivVector G n)).trans (card_vector (n - 1))

variable {G n} {g : G}
variable (v : vectorsProdEqOne G n) (j k : ℕ)

/-- Rotate a vector whose product is 1. -/
def rotate : vectorsProdEqOne G n :=
  ⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, List.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩

theorem rotate_zero : rotate v 0 = v :=
  Subtype.ext (Subtype.ext v.1.1.rotate_zero)

theorem rotate_rotate : rotate (rotate v j) k = rotate v (j + k) :=
  Subtype.ext (Subtype.ext (v.1.1.rotate_rotate j k))

theorem rotate_length : rotate v n = v :=
  Subtype.ext (Subtype.ext ((congr_arg _ v.1.2.symm).trans v.1.1.rotate_length))

end VectorsProdEqOne

-- TODO: Make the `Finite` version of this theorem the default
/-- For every prime `p` dividing the order of a finite group `G` there exists an element of order
`p` in `G`. This is known as Cauchy's theorem. -/
theorem _root_.exists_prime_orderOf_dvd_card {G : Type*} [Group G] [Fintype G] (p : ℕ)
    [hp : Fact p.Prime] (hdvd : p ∣ Fintype.card G) : ∃ x : G, orderOf x = p := by
  have hp' : p - 1 ≠ 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_gt hp.out.one_lt)
  have Scard :=
    calc
      p ∣ Fintype.card G ^ (p - 1) := hdvd.trans (dvd_pow (dvd_refl _) hp')
      _ = Fintype.card (vectorsProdEqOne G p) := (VectorsProdEqOne.card G p).symm
  let f : ℕ → vectorsProdEqOne G p → vectorsProdEqOne G p := fun k v =>
    VectorsProdEqOne.rotate v k
  have hf1 : ∀ v, f 0 v = v := VectorsProdEqOne.rotate_zero
  have hf2 : ∀ j k v, f k (f j v) = f (j + k) v := fun j k v =>
    VectorsProdEqOne.rotate_rotate v j k
  have hf3 : ∀ v, f p v = v := VectorsProdEqOne.rotate_length
  let σ :=
    Equiv.mk (f 1) (f (p - 1)) (fun s => by rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
      fun s => by rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]
  have hσ : ∀ k v, (σ ^ k) v = f k v := fun k =>
    Nat.rec (fun v => (hf1 v).symm) (fun k hk v => by
      rw [pow_succ, Perm.mul_apply, hk (σ v), Nat.succ_eq_one_add, ← hf2 1 k]
      simp only [σ, coe_fn_mk]) k
  replace hσ : σ ^ p ^ 1 = 1 := Perm.ext fun v => by rw [pow_one, hσ, hf3, one_apply]
  let v₀ : vectorsProdEqOne G p :=
    ⟨List.Vector.replicate p 1, (List.prod_replicate p 1).trans (one_pow p)⟩
  have hv₀ : σ v₀ = v₀ := Subtype.ext (Subtype.ext (List.rotate_replicate (1 : G) p 1))
  obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀
  refine
    Exists.imp (fun g hg => orderOf_eq_prime ?_ fun hg' => hv2 ?_)
      (List.rotate_one_eq_self_iff_eq_replicate.mp (Subtype.ext_iff.mp (Subtype.ext_iff.mp hv1)))
  · rw [← List.prod_replicate, ← v.1.2, ← hg, show v.val.val.prod = 1 from v.2]
  · rw [Subtype.ext_iff_val, Subtype.ext_iff_val, hg, hg', v.1.2]
    simp only [v₀, List.Vector.replicate]

-- TODO: Make the `Finite` version of this theorem the default
/-- For every prime `p` dividing the order of a finite additive group `G` there exists an element of
order `p` in `G`. This is the additive version of Cauchy's theorem. -/
theorem _root_.exists_prime_addOrderOf_dvd_card {G : Type*} [AddGroup G] [Fintype G] (p : ℕ)
    [Fact p.Prime] (hdvd : p ∣ Fintype.card G) : ∃ x : G, addOrderOf x = p :=
  @exists_prime_orderOf_dvd_card (Multiplicative G) _ _ _ _ (by convert hdvd)

attribute [to_additive existing] exists_prime_orderOf_dvd_card

-- TODO: Make the `Finite` version of this theorem the default
/-- For every prime `p` dividing the order of a finite group `G` there exists an element of order
`p` in `G`. This is known as Cauchy's theorem. -/
@[to_additive]
theorem _root_.exists_prime_orderOf_dvd_card' {G : Type*} [Group G] [Finite G] (p : ℕ)
    [hp : Fact p.Prime] (hdvd : p ∣ Nat.card G) : ∃ x : G, orderOf x = p := by
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card] at hdvd
  exact exists_prime_orderOf_dvd_card p hdvd

end Cauchy

theorem subgroup_eq_top_of_swap_mem [DecidableEq α] {H : Subgroup (Perm α)}
    [d : DecidablePred (· ∈ H)] {τ : Perm α} (h0 : (Fintype.card α).Prime)
    (h1 : Fintype.card α ∣ Fintype.card H) (h2 : τ ∈ H) (h3 : IsSwap τ) : H = ⊤ := by
  haveI : Fact (Fintype.card α).Prime := ⟨h0⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (Fintype.card α) h1
  have hσ1 : orderOf (σ : Perm α) = Fintype.card α := (Subgroup.orderOf_coe σ).trans hσ
  have hσ2 : IsCycle ↑σ := isCycle_of_prime_order'' h0 hσ1
  have hσ3 : (σ : Perm α).support = ⊤ :=
    Finset.eq_univ_of_card (σ : Perm α).support (hσ2.orderOf.symm.trans hσ1)
  have hσ4 : Subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3
  rw [eq_top_iff, ← hσ4, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Subtype.mem σ, h2⟩

section Partition

variable [DecidableEq α]

/-- The partition corresponding to a permutation -/
def partition (σ : Perm α) : (Fintype.card α).Partition where
  parts := σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1
  parts_pos {n hn} := by
    rcases mem_add.mp hn with hn | hn
    · exact zero_lt_one.trans (one_lt_of_mem_cycleType hn)
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
  parts_sum := by
    rw [sum_add, sum_cycleType, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one,
      add_tsub_cancel_of_le σ.support.card_le_univ]

theorem parts_partition {σ : Perm α} :
    σ.partition.parts = σ.cycleType + Multiset.replicate (Fintype.card α - #σ.support) 1 :=
  rfl

theorem filter_parts_partition_eq_cycleType {σ : Perm α} :
    ((partition σ).parts.filter fun n => 2 ≤ n) = σ.cycleType := by
  rw [parts_partition, filter_add, Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycleType,
    Multiset.filter_eq_nil.2 fun a h => ?_, add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  decide

theorem partition_eq_of_isConj {σ τ : Perm α} : IsConj σ τ ↔ σ.partition = τ.partition := by
  rw [isConj_iff_cycleType_eq]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ← sum_cycleType, ← sum_cycleType,
      h]
  · rw [← filter_parts_partition_eq_cycleType, ← filter_parts_partition_eq_cycleType, h]

end Partition

/-!
### 3-cycles
-/


/-- A three-cycle is a cycle of length 3. -/
def IsThreeCycle [DecidableEq α] (σ : Perm α) : Prop :=
  σ.cycleType = {3}

namespace IsThreeCycle

variable [DecidableEq α] {σ : Perm α}

theorem cycleType (h : IsThreeCycle σ) : σ.cycleType = {3} :=
  h

theorem card_support (h : IsThreeCycle σ) : #σ.support = 3 := by
  rw [← sum_cycleType, h.cycleType, Multiset.sum_singleton]

theorem _root_.card_support_eq_three_iff : #σ.support = 3 ↔ σ.IsThreeCycle := by
  refine ⟨fun h => ?_, IsThreeCycle.card_support⟩
  by_cases h0 : σ.cycleType = 0
  · rw [← sum_cycleType, h0, sum_zero] at h
    exact (ne_of_lt zero_lt_three h).elim
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0
  by_cases h1 : σ.cycleType.erase n = 0
  · rw [← sum_cycleType, ← cons_erase hn, h1, cons_zero, Multiset.sum_singleton] at h
    rw [IsThreeCycle, ← cons_erase hn, h1, h, ← cons_zero]
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1
  rw [← sum_cycleType, ← cons_erase hn, ← cons_erase hm, Multiset.sum_cons, Multiset.sum_cons] at h
  have : ∀ {k}, 2 ≤ m → 2 ≤ n → n + (m + k) = 3 → False := by omega
  cases this (two_le_of_mem_cycleType (mem_of_mem_erase hm)) (two_le_of_mem_cycleType hn) h

theorem isCycle (h : IsThreeCycle σ) : IsCycle σ := by
  rw [← card_cycleType_eq_one, h.cycleType, card_singleton]

theorem sign (h : IsThreeCycle σ) : sign σ = 1 := by
  rw [Equiv.Perm.sign_of_cycleType, h.cycleType]
  rfl

theorem inv {f : Perm α} (h : IsThreeCycle f) : IsThreeCycle f⁻¹ := by
  rwa [IsThreeCycle, cycleType_inv]

@[simp]
theorem inv_iff {f : Perm α} : IsThreeCycle f⁻¹ ↔ IsThreeCycle f :=
  ⟨by
    rw [← inv_inv f]
    apply inv, inv⟩

theorem orderOf {g : Perm α} (ht : IsThreeCycle g) : orderOf g = 3 := by
  rw [← lcm_cycleType, ht.cycleType, Multiset.lcm_singleton, normalize_eq]

theorem isThreeCycle_sq {g : Perm α} (ht : IsThreeCycle g) : IsThreeCycle (g * g) := by
  rw [← pow_two, ← card_support_eq_three_iff, support_pow_coprime, ht.card_support]
  rw [ht.orderOf]
  norm_num

end IsThreeCycle

section

variable [DecidableEq α]

theorem isThreeCycle_swap_mul_swap_same {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
    IsThreeCycle (swap a b * swap a c) := by
  suffices h : support (swap a b * swap a c) = {a, b, c} by
    rw [← card_support_eq_three_iff, h]
    simp [ab, ac, bc]
  apply le_antisymm ((support_mul_le _ _).trans fun x => _) fun x hx => ?_
  · simp [ab, ac]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_support]
    simp only [Perm.coe_mul, Function.comp_apply, Ne]
    obtain rfl | rfl | rfl := hx
    · rw [swap_apply_left, swap_apply_of_ne_of_ne ac.symm bc.symm]
      exact ac.symm
    · rw [swap_apply_of_ne_of_ne ab.symm bc, swap_apply_right]
      exact ab
    · rw [swap_apply_right, swap_apply_left]
      exact bc

open Subgroup

theorem swap_mul_swap_same_mem_closure_three_cycles {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
    swap a b * swap a c ∈ closure { σ : Perm α | IsThreeCycle σ } := by
  by_cases bc : b = c
  · subst bc
    simp [one_mem]
  exact subset_closure (isThreeCycle_swap_mul_swap_same ab ac bc)

theorem IsSwap.mul_mem_closure_three_cycles {σ τ : Perm α} (hσ : IsSwap σ) (hτ : IsSwap τ) :
    σ * τ ∈ closure { σ : Perm α | IsThreeCycle σ } := by
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

end

end Equiv.Perm
