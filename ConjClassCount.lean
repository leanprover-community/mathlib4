/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module conj_class_count
-/

import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupAction.Embedding
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Set.Card
-- import Jordan.NoncommCoprod
-- import Jordan.PermFibration
import Mathlib.GroupTheory.GroupAction.FixingSubgroup


/-# Centralizer of a permutation and cardinality of conjugacy classes
  # in the symmetric and alternating groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α` and `alternatingGroup α`.
Every `g : Equiv.Perm α` has a `cycleType α : Multiset ℕ`.
By `Equiv.Perm.isConj_iff_cycleType_eq`,
two permutations are conjugate in `Equiv.Perm α` iff
their cycle types are equal.
To compute the cardinality of the conjugacy classes, we could use
a purely combinatorial approach and compute the number of permutations
with given cycle type but we resorted to a more algebraic approach.

Given `g : Equiv.Perm α`, the conjugacy class of `g` is the orbit
of `g` under the action `ConjAct (Equiv.Perm α)`, and we use
the orbit-stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`)
to reduce the computation to the computation of the centralizer of `g`,
the subgroup of `Equiv.Perm α` consisting of all permutations
which commute with `g`. It is accessed here as
`MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`.

We compute this subgroup as follows.

* If `h : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`, then the action
  of `h` by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
  That induces an action of MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  on `g.cycleFactorsFinset` which is defined via
  `OnCycleFactors.subMulActionOnCycleFactors `

* This action defines a group morphism `OnCycleFactors.φ g` from
  `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  to `Equiv.Perm (g.cycleFactorsFinset)`

* `OnCycleFactors.Iφ_eq_range` shows that the range of `OnCycleFactors.φ g`
  is the subgroup `Iφ g` of `Equiv.Perm (g.cycleFactorsFinset)`
  consisting of permutations `τ` which preserve the length of the cycles.
  This is showed by constructing a right inverse `OnCycleFactors.φ'`
  in `OnCycleFactors.hφ'_is_rightInverse`.

* `OnCycleFactors.hφ_range_card` computes the cardinality of
  `range (OnCycleFactors.φ g)` as a product of factorials.
  This comes from a lengthy analysis of the subgroup of permutations
  which preserve a partition as a product type,
  starting with `Equiv.Perm.ofPartition`.
  (For the moment, this latter analysis requires `Fintype α`,
  but it should be done in greater generality.)

* For n element `z : Equiv.Perm α`, we then prove in
  `OnCycleFactors.hφ_mem_ker_iff` that `ConjAct.toConjAct z` belongs to
  the kernel of `OnCycleFactors.φ g` if and only if it permutes `g.fixedPoints`
  and it acts on each cycle of `g` as a power of that cycle.
  This gives a description of the kernel of `OnCycleFactors.φ g` as the product
  of a symmetric group and of a product of cyclic groups.
  This starts with the morphism `OnCycleFactors.ψ`,
  its injectivity `OnCycleFactors.hψ_inj`,
  its range `OnCycleFactors.hφ_ker_eq_psi_range`,
  and  its cardinality `OnCycleFactors.hψ_range_card`.

* `Equiv.Perm.conj_stabilizer_card g` computes the cardinality
  of the centralizer of `g`

* `Equiv.Perm.conj_class_card_mul_eq g` computes the cardinality
  of the conjugacy class of `g`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute the cardinality of the set of permutations `g` such that
  `g.cycleType = m`.

* `AlternatingGroup.of_cycleType_eq m`, `AlternatingGroup.of_cycleType_eq m`
  and `AlternatingGroup.card_of_cycleType m` give the same result
  in the subgroup `alternatingGroup α`

* `sign_ψ` computes the signature of the permutation induced given by `ψ`.

* We finally compute on which condition the centralizer of an even permutation
  is contained in `alternatingGroup α` and deduce the formula
  for the cardinality of the centralizers and conjugacy classes
  in `alternatingGroup α`.

-/

open scoped Pointwise

section noncommCoprod

variable {G H P : Type*} [Monoid G] [Monoid H] [Monoid P]

end noncommCoprod
section group
/-
theorem Group.is_conj_iff_inv_is_conj {G : Type _} [Group G] (a b k : G) :
    k * a * k⁻¹ = b ↔ a = k⁻¹ * b * k := by
  rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq, mul_assoc]
#align is_conj_iff_inv_is_conj Group.is_conj_iff_inv_is_conj

theorem Group.SemiConjby_comm {M : Type*} [Monoid M] (a b : M) (c : Mˣ) :
    SemiconjBy (c : M) a b ↔ SemiconjBy (c.inv : M) b a := by
  unfold SemiconjBy
  rw [← c.eq_inv_mul_iff_mul_eq, ← mul_assoc, ← c.mul_inv_eq_iff_eq_mul, eq_comm]
  rfl
-/

/-
theorem Group.commute_iff_mem_centralizer_zpowers {G : Type _} [Group G] (g k : G) :
    Commute g k ↔ k ∈ Subgroup.centralizer (Subgroup.zpowers g) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro H h
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff]
    rintro ⟨n, rfl⟩
    apply Commute.zpow_left
    exact H
  · intro H
    simp only [Commute, SemiconjBy, H g (Subgroup.mem_zpowers g)]
#align group.commute_iff_mem_centralizer_zpowers Group.commute_iff_mem_centralizer_zpowers

-/

end group

section Lists

variable {α β : Type _}

#check List.Disjoint
theorem List.disjoint_map (f : α → β) (s t : List α) (hf : Function.Injective f)
    (h : List.Disjoint s t) : List.Disjoint (s.map f) (t.map f) :=
  by
  simp only [List.Disjoint]
  intro b hbs hbt
  rw [List.mem_map] at hbs hbt
  obtain ⟨a, ha, rfl⟩ := hbs
  apply h ha
  obtain ⟨a', ha', ha''⟩ := hbt
  rw [hf ha''.symm]; exact ha'
#align list.disjoint_map List.disjoint_map

theorem List.disjoint_pmap {p : α → Prop} (f : ∀ a : α, p a → β) (s t : List α)
    (hs : ∀ a ∈ s, p a) (ht : ∀ a ∈ t, p a)
    (hf : ∀ (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' → a = a')
    (h : List.Disjoint s t) :
    List.Disjoint (List.pmap f s hs) (List.pmap f t ht) := by
  simp only [List.Disjoint]
  intro b hbs hbt
  rw [List.mem_pmap] at hbs hbt
  obtain ⟨a, ha, rfl⟩ := hbs
  apply h ha
  obtain ⟨a', ha', ha''⟩ := hbt
  rw [hf a a' (hs a ha) (ht a' ha') ha''.symm]
  exact ha'
#align list.disjoint_pmap List.disjoint_pmap

/- def List.mkSubtype {p : α → Prop} :
    ∀ (l : List α) (_ : ∀ a ∈ l, p a), List (Subtype p)
  | [] => fun _ => List.nil
  | a::l => fun hl =>
    ⟨a, hl a
      (List.mem_cons_self a l)⟩::List.mkSubtype l fun b hb => hl b (List.mem_cons_of_mem a hb)
#align list.mk_subtype List.mkSubtype

theorem List.coe_mk {p : α → Prop} (l : List α) (hl : ∀ a ∈ l,  p a) :
    List.map Subtype.val (List.mkSubtype l hl) = l := by
  induction' l with a l' hl'
  -- nil
  simp only [List.mkSubtype, List.map_nil]
  -- (a :: l)
  simp only [map, cons.injEq, true_and]
  apply hl'
#align list.coe_mk List.coe_mk

def List.mkSubtype' {p : α → Prop} (l : List α) (hl : ∀ a ∈ l, p a) :
    List (Subtype p) :=
  List.pmap (fun (a : α) (ha : p a) => (⟨a, ha⟩ : Subtype p)) l hl
#align list.mk_subtype' List.mkSubtype'

theorem List.coe_mk' {p : α → Prop} (l : List α) (hl : ∀ a ∈ l, p a) :
    List.map Subtype.val (List.mkSubtype' l hl) = l := by
  simp only [List.mkSubtype']
  rw [List.map_pmap]
  rw [List.pmap_congr]
  rw [List.pmap_eq_map]
  rw [List.map_id]
  exact hl
  intro a _ _ _
  simp only [Subtype.coe_mk, id.def]
#align list.coe_mk' List.coe_mk'

 -/
end Lists

section permutations

variable {α : Type _} [Fintype α] [DecidableEq α]

theorem Equiv.Perm.disjoint_iff_support_disjoint
    {f g : Equiv.Perm α} :
    f.Disjoint g ↔ _root_.Disjoint f.support g.support := by
  simp only [Equiv.Perm.disjoint_iff_eq_or_eq,
    Finset.disjoint_iff_inter_eq_empty, ← Equiv.Perm.not_mem_support,
    ← Finset.mem_compl, ← Finset.mem_union, ← Finset.compl_inter,
    ← Finset.compl_eq_univ_iff, ← Finset.eq_univ_iff_forall]
#align equiv.perm.disjoint_iff_support_disjoint Equiv.Perm.disjoint_iff_support_disjoint

theorem Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
    (g c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) (x : α) :
    c = g.cycleOf x ↔ x ∈ c.support := by
  constructor
  · intro hcx
    rw [Equiv.Perm.mem_support, hcx, Equiv.Perm.cycleOf_apply_self,
      Ne.def, ← Equiv.Perm.cycleOf_eq_one_iff, ← hcx]
    exact Equiv.Perm.IsCycle.ne_one (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).left
  · intro hx; exact Equiv.Perm.cycle_is_cycleOf hx hc
#align equiv.perm.is_cycle_eq_cycle_of_iff Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff


end permutations


section Ranges

/-- From `l: List ℕ`, construct `ml: List (List ℕ)` such that
  `ml.map List.length = l` and `ml.join = range l.sum` -/
def List.ranges : List ℕ → List (List ℕ)
  | [] => List.nil
  | a::l => List.range a::List.map (List.map (Nat.add a)) (List.ranges l)
#align list.ranges List.ranges

/-- The members of `l.ranges` are pairwise disjoint -/
theorem List.ranges_disjoint (l : List ℕ) :
  List.Pairwise List.Disjoint (List.ranges l) := by
  induction' l with a l hl
  -- nil
  exact List.Pairwise.nil
  -- (a :: l)
  simp only [List.ranges, List.pairwise_cons]
  constructor
  · intro s hs
    obtain ⟨s', _, rfl⟩ := List.mem_map.mp hs
    intro u hu
    rw [List.mem_map]; rintro ⟨v, _, rfl⟩
    rw [List.mem_range] at hu
    exact lt_iff_not_le.mp hu le_self_add
  · rw [List.pairwise_map]
    apply List.Pairwise.imp _ hl
    intro u v; apply List.disjoint_map _ u v _
    exact fun u v => Nat.add_left_cancel
#align list.ranges_disjoint List.ranges_disjoint

/-- The members of `l.ranges` have no duplicate -/
theorem List.ranges_nodup (l : List ℕ) :
    ∀ s ∈ List.ranges l, List.Nodup s := by
  induction' l with a l hl
  · -- nil
    intro s hs
    simp only [List.ranges, List.not_mem_nil] at hs
  · -- (a :: l)
    intro s hs
    simp only [List.ranges, List.mem_cons] at hs
    cases' hs with hs hs
    -- s = a
    rw [hs];
    exact List.nodup_range a
    -- s ∈ l
    rw [List.mem_map] at hs ;
    obtain ⟨t, ht, rfl⟩ := hs
    refine' List.Nodup.map (fun u v => Nat.add_left_cancel) (hl t ht)
#align list.ranges_nodup List.ranges_nodup

/-- The lengths of the members of `l.ranges` are those given by `l` -/
theorem List.ranges_length (l : List ℕ) :
    l.ranges.map List.length = l := by
  induction' l with a l hl
  -- nil
  simp only [List.ranges, List.map_nil]
  -- (a :: l)
  simp only [map, length_range, map_map, cons.injEq, true_and]
  conv_rhs => rw [← hl]
  apply List.map_congr
  intro s _
  simp only [Function.comp_apply, List.length_map]
#align list.ranges_length List.ranges_length

/-- Any entry of any member of `l.ranges` is strictly smaller than `l.sum`  -/
theorem List.ranges_lt (l : List ℕ) {s : List ℕ} {n : ℕ}
    (hs : s ∈ List.ranges l) (hn : n ∈ s) :
    n < l.sum := by
  revert s n
  induction' l with a l hl
  · -- nil
    intro s n hs _
    exfalso
    simp only [List.ranges] at hs
    exact List.not_mem_nil s hs
  · -- (a :: l)
    intro s n hs hn
    simp only [List.ranges, List.mem_cons] at hs
    cases' hs with hs hs
    · rw [hs, List.mem_range] at hn
      apply lt_of_lt_of_le hn
      rw [List.sum_cons]
      exact le_self_add
    · rw [List.mem_map] at hs ; obtain ⟨t, ht, rfl⟩ := hs
      rw [List.mem_map] at hn ; obtain ⟨m, hm, rfl⟩ := hn
      simp only [List.sum_cons, Nat.add_def, add_lt_add_iff_left]
      exact hl ht hm
#align list.ranges_lt List.ranges_lt

/-- For any `c: List ℕ` whose sum is at most `Fintype.card α`, we can find
`o : List (List α)` whose members have no duplicate, lengths given by `c`,
 and are pairwise disjoint -/
theorem List.exists_pw_disjoint_with_card {α : Type*} [Fintype α] [DecidableEq α]
    {c : List ℕ} (hc : c.sum ≤ Fintype.card α) :
    ∃ o : List (List α),
      List.map List.length o = c ∧
      (∀ s ∈ o, List.Nodup s) ∧
      List.Pairwise List.Disjoint o := by
  let klift  (n : ℕ) (hn : n < Fintype.card α) : Fin (Fintype.card α) :=
    (⟨n, hn⟩ : Fin (Fintype.card α))
  let klift' (l : List ℕ) (hl : ∀ a ∈ l, a < Fintype.card α) :
    List (Fin (Fintype.card α)) := List.pmap klift l hl
  have hc'_lt : ∀ l ∈ c.ranges, ∀ n ∈ l, n < Fintype.card α := by
    intro l hl n hn
    apply lt_of_lt_of_le _ hc
    apply List.ranges_lt c hl hn
  let l := List.pmap klift' (List.ranges c) hc'_lt
  have hl :  ∀ (a : List ℕ) (ha : a ∈ c.ranges),
    List.map Fin.valEmbedding (klift' a (hc'_lt a ha)) = a := by
    intro a ha
    conv_rhs => rw [← List.map_id a]
    rw [List.map_pmap]
    simp only [Fin.valEmbedding_apply, Fin.val_mk, List.pmap_eq_map, List.map_id'', List.map_id]
  use List.map (List.map (Fintype.equivFin α).symm) l
  constructor
  · -- length
    rw [← List.ranges_length c]
    simp only [map_map, map_pmap, Function.comp_apply, length_map, length_pmap, pmap_eq_map]
  constructor
  · -- nodup
    intro s
    rw [List.mem_map]
    rintro ⟨t, ht, rfl⟩
    apply List.Nodup.map (Equiv.injective _)
    simp only [List.mem_pmap] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    apply List.Nodup.of_map
    rw [hl u hu]; apply List.ranges_nodup c u hu
  · -- pairwise disjoint
    suffices : List.Pairwise List.Disjoint l
    refine' List.Pairwise.map _ _ this
    · intro s t hst
      apply List.disjoint_map
      exact Equiv.injective _
      exact hst
    · -- list.pairwise list.disjoint l,
      apply List.Pairwise.pmap (List.ranges_disjoint c)
      intro u hu v hv huv
      apply List.disjoint_pmap
      · intro a a' ha ha' h
        simpa only [Fin.mk_eq_mk] using h
      exact huv
#align list.exists_pw_disjoint_with_card List.exists_pw_disjoint_with_card

end Ranges


section ncard

theorem Set.ncard_filter_eq_count {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  (f : ι → κ) (s : Finset ι) (k : κ) :
    Set.ncard ({x ∈ s | f x = k}) = Multiset.count k (Multiset.map f s.val) := by
  induction' s using Finset.induction with a s has ih
  · simp only [Finset.empty_val, Multiset.map_zero, Multiset.not_mem_zero, not_false_eq_true,
    Multiset.count_eq_zero_of_not_mem, Finset.not_mem_empty, false_and, Set.setOf_false, Set.finite_empty,
    Set.ncard_eq_zero]
  · suffices : {x ∈ insert a s | f x = k} =
      if f a = k then insert a {x ∈ s | f x = k} else {x ∈ s | f x = k}
    rw [this]
    simp only [Finset.insert_val, Finset.mem_val, Multiset.mem_map, Multiset.mem_ndinsert, exists_eq_or_imp, Multiset.ndinsert_of_not_mem has]
    simp only [Multiset.map_cons, Multiset.mem_cons, Multiset.mem_map, Finset.mem_val,
      Multiset.nodup_cons, not_exists, not_and, ne_eq]
    rw [Multiset.count_cons]
    by_cases h : f a = k
    · rw [if_pos h, if_pos h.symm]
      rw [Set.ncard_insert_of_not_mem ?_ ?_]
      simp only [add_left_inj, ih]
      -- intro ha
      · simp only [Set.mem_setOf_eq]
        intro ha
        exact has ha.1
      · apply Set.Finite.subset s.finite_toSet
        intro x
        simp only [Set.mem_setOf_eq, Finset.mem_coe, and_imp]
        intro hx _; exact hx
    · rw [if_neg h, if_neg (ne_comm.mp h), ih, add_zero]
    ext x
    simp only [Finset.mem_insert, Set.mem_setOf_eq]
    by_cases h : f a = k
    · simp only [Set.mem_setOf_eq, if_pos h, Set.mem_insert_iff]
      aesop
    · simp only [Set.mem_setOf_eq, if_neg h, and_congr_left_iff, or_iff_right_iff_imp]
      intro hx hxa
      exfalso
      apply h
      rw [← hxa, hx]
#align fintype.card_eq_count Set.ncard_filter_eq_count

/-
theorem Set.ncard_filter_eq_count' {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (f : ι → κ) (s : Finset ι) (k : κ) :
    Set.ncard {x : s | f x = k} = Multiset.count k (Multiset.map f s.val) := by
  rw [← Set.ncard_filter_eq_count]
  apply Set.ncard_congr (fun x _ ↦ x.val)
  · rintro ⟨x, hx⟩ hx'
    exact ⟨hx, hx'⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Set.mem_setOf_eq, Subtype.mk.injEq, imp_self, implies_true]
  · rintro x ⟨hx, hx'⟩
    use! x
    use hx'
#align finset.card_eq_count' Set.ncard_filter_eq_count'
-/

/-- If a multiset has no duplicates,
  a product on its members is the product on the associated Finset -/
@[to_additive "If a multiset has no duplicates,
  a sum on its members is the sum on the associated Finset"]
theorem Multiset.prod_toFinset {α : Type _} {M : Type _} [DecidableEq α] [CommMonoid M]
    (f : α → M) {m : Multiset α} (hm : m.Nodup) :
    m.toFinset.prod f = (m.map f).prod := by
  induction' m using Multiset.induction with a m ih
  simp
  obtain ⟨not_mem, hm⟩ := Multiset.nodup_cons.mp hm
  simp [Finset.prod_insert (mt Multiset.mem_toFinset.mp not_mem), ih hm]
#align multiset.prod_to_finset Multiset.prod_toFinset
#align multiset.sum_to_finset Multiset.sum_toFinset

end ncard

section CycleTypes

variable (α : Type _) [DecidableEq α] [Fintype α]

-- Maybe that should be a type rather than a Finset
/-- The `Finset (Equiv.Perm α)` of permutations with cycle type `c`-/
def Equiv.permWithCycleType (c : Multiset ℕ) :=
  Finset.filter (fun g : Equiv.Perm α => Equiv.Perm.cycleType g = c) Finset.univ
#align equiv.perm_with_cycle_type Equiv.permWithCycleType

variable {α}

/-- If `α` has less than `c.sum` elements,
  then there is no permutation with cycle type `c` -/
theorem Equiv.permWithCycleType_empty {c : Multiset ℕ} (hc : Fintype.card α < c.sum) :
    Equiv.permWithCycleType α c = ∅ := by
  apply Finset.eq_empty_of_forall_not_mem
  intro g
  unfold Equiv.permWithCycleType
  simp only [Set.toFinset_univ, Finset.mem_filter, Finset.mem_univ, true_and_iff]
  intro hg; apply lt_iff_not_le.mp hc; rw [← hg]
  rw [Equiv.Perm.sum_cycleType]
  refine' (Equiv.Perm.support g).card_le_univ
#align equiv.perm_with_cycle_type_empty Equiv.permWithCycleType_empty

/-- There are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2. -/
theorem Equiv.permWithCycleType_nonempty_iff {m : Multiset ℕ} :
    (Equiv.permWithCycleType α m).Nonempty ↔
      (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) := by
  constructor
  · -- empty case
    intro h
    obtain ⟨g, hg⟩ := h
    simp only [Equiv.permWithCycleType, Set.toFinset_univ, Finset.mem_filter,
      Finset.mem_univ, true_and_iff] at hg
    constructor
    rw [← hg, Equiv.Perm.sum_cycleType]
    exact (Equiv.Perm.support g).card_le_univ
    intro a
    rw [← hg]
    exact Equiv.Perm.two_le_of_mem_cycleType
  · rintro ⟨hc, h2c⟩
    have hc' : m.toList.sum ≤ Fintype.card α
    · simp only [Multiset.sum_toList]
      exact hc
    obtain ⟨p, hp_length, hp_nodup, hp_disj⟩ := List.exists_pw_disjoint_with_card hc'
    use List.prod (List.map (fun l => List.formPerm l) p)
    simp only [Equiv.permWithCycleType, Finset.mem_filter, Set.toFinset_univ,
      Finset.mem_univ, true_and_iff]
    have hp2 : ∀ x ∈ p, 2 ≤ x.length :=
      by
      intro x hx
      apply h2c x.length
      rw [← Multiset.mem_toList, ← hp_length, List.mem_map]
      exact ⟨x, hx, rfl⟩
    rw [Equiv.Perm.cycleType_eq _ rfl]
    · -- lengths
      rw [← Multiset.coe_toList m]
      apply congr_arg
      rw [List.map_map]; rw [← hp_length]
      apply List.map_congr
      intro x hx; simp only [Function.comp_apply]
      rw [List.support_formPerm_of_nodup x (hp_nodup x hx)]
      ·-- length
        rw [List.toFinset_card_of_nodup (hp_nodup x hx)]
      · -- length >= 1
        intro a h
        apply Nat.not_succ_le_self 1
        conv_rhs => rw [← List.length_singleton a]; rw [← h]
        exact hp2 x hx
    · -- cycles
      intro g
      rw [List.mem_map]
      rintro ⟨x, hx, rfl⟩
      have hx_nodup : x.Nodup := hp_nodup x hx
      rw [← Cycle.formPerm_coe x hx_nodup]
      apply Cycle.isCycle_formPerm
      rw [Cycle.nontrivial_coe_nodup_iff hx_nodup]
      exact hp2 x hx
    · -- disjoint
      rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem _ hp_disj
      intro a b ha hb hab
      rw [List.formPerm_disjoint_iff (hp_nodup a ha) (hp_nodup b hb) (hp2 a ha) (hp2 b hb)]
      exact hab
#align equiv.perm_with_cycle_type_nonempty_iff Equiv.permWithCycleType_nonempty_iff

/-- `a : α` belongs to the support of `k • g` iff
  `k⁻¹ * a` belongs to the support of `g` -/
theorem Equiv.Perm.conj_support_eq (k : ConjAct (Equiv.Perm α)) (g : Equiv.Perm α) (a : α) :
    a ∈ (k • g).support ↔ ConjAct.ofConjAct k⁻¹ a ∈ g.support := by
  simp only [Equiv.Perm.mem_support, ConjAct.smul_def]
  rw [not_iff_not]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, ConjAct.ofConjAct_inv]
  apply Equiv.apply_eq_iff_eq_symm_apply
#align equiv.perm.conj_support_eq Equiv.Perm.conj_support_eq

/-- A permutation `c` is a cycle of `g` iff `k * c * k⁻¹` is a cycle of `k * g * k⁻¹` -/
theorem Equiv.Perm.mem_cycleFactorsFinset_conj (g k c : Equiv.Perm α) :
    k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  suffices imp_lemma :
    ∀ (g k c : Equiv.Perm α) (_ : c ∈ g.cycleFactorsFinset),
      k * c * k⁻¹ ∈ (k * g * k⁻¹).cycleFactorsFinset
  · constructor
    · intro h
      suffices ∀ h : Equiv.Perm α, h = k⁻¹ * (k * h * k⁻¹) * k by
        rw [this g, this c]
        apply imp_lemma
        exact h
      intro h
      group
    · apply imp_lemma g k c
  · intro g k c
    simp only [Equiv.Perm.mem_cycleFactorsFinset_iff]
    rintro ⟨hc, hc'⟩
    constructor
    exact Equiv.Perm.IsCycle.conj hc
    intro a ha
    simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
    apply hc'
    rw [Equiv.Perm.mem_support] at ha ⊢
    intro ha'; apply ha
    simp only [mul_smul, ← Equiv.Perm.smul_def] at ha' ⊢
    rw [ha']
    simp only [Equiv.Perm.smul_def, Equiv.Perm.apply_inv_self]
#align equiv.perm.mem_cycle_factors_conj Equiv.Perm.mem_cycleFactorsFinset_conj

theorem Equiv.Perm.cycleFactorsFinset_conj (g k : Equiv.Perm α) :
    (k * g * k⁻¹).cycleFactorsFinset = Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinset
       := by
  ext c
  rw [Finset.mem_map_equiv]
  rw [← Equiv.Perm.mem_cycleFactorsFinset_conj g k]
  apply iff_of_eq
  apply congr_arg₂ _ _
  rfl
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv_symm, MulAut.conj_symm_apply]
  group
#align equiv.perm.cycle_factors_conj Equiv.Perm.cycleFactorsFinset_conj

/-- A permutation `c` is a cycle of `g` iff `k • c` is a cycle of `k • g` -/
theorem Equiv.Perm.mem_cycleFactorsFinset_conj'
    (k : ConjAct (Equiv.Perm α)) (g c : Equiv.Perm α) :
    k • c ∈ (k • g).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  simp only [ConjAct.smul_def]
  apply Equiv.Perm.mem_cycleFactorsFinset_conj
#align equiv.perm.mem_cycle_factors_conj' Equiv.Perm.mem_cycleFactorsFinset_conj'

theorem Equiv.Perm.cycleFactorsFinset_conj_eq
    (k : ConjAct (Equiv.Perm α)) (g : Equiv.Perm α) :
    Equiv.Perm.cycleFactorsFinset (k • g) = k • Equiv.Perm.cycleFactorsFinset g := by
  ext c
  rw [← Equiv.Perm.mem_cycleFactorsFinset_conj' k⁻¹ (k • g) c]
  simp only [inv_smul_smul]
  exact Finset.inv_smul_mem_iff
#align equiv.perm.mem_cycle_factors_conj_eq Equiv.Perm.cycleFactorsFinset_conj_eq

/-
theorem ConjAct.mem_stabilizer_iff {G : Type*} [Group G] (k : ConjAct G) (g : G) :
    k ∈ MulAction.stabilizer (ConjAct G) g ↔
      (ConjAct.ofConjAct k) * g * (ConjAct.ofConjAct k)⁻¹ = g := by
  rfl
#align mul_action.conj_act.mem_stabilizer_iff ConjAct.mem_stabilizer_iff

theorem MulAction.ConjAct.mem_stabilizer_iff' {G : Type _} [Group G] (k : ConjAct G) (g : G) :
    k ∈ MulAction.stabilizer (ConjAct G) g ↔ Commute (ConjAct.ofConjAct k) g := by
  -- rw [MulAction.ConjAct.mem_stabilizer_iff]
  simp only [ConjAct.mem_stabilizer_iff, Commute, SemiconjBy, mul_inv_eq_iff_eq_mul]
#align mul_action.conj_act.mem_stabilizer_iff' MulAction.ConjAct.mem_stabilizer_iff'
 -/
open scoped Pointwise

/- NB. The converse of the next theorem is false. Commuting with every cycle of `g`
  means that we belong to the kernel of the action of `Equiv.Perm α` on `g.cycleFactorsFinset` -/
/-- If a permutation commutes with every cycle of `g`, then it commutes with `g` -/
theorem Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute (k g : Equiv.Perm α)
    (hk : ∀ c ∈ g.cycleFactorsFinset, Commute k c) :
    Commute k g := by
  rw [← Equiv.Perm.cycleFactorsFinset_noncommProd g (Equiv.Perm.cycleFactorsFinset_mem_commute g)]
  apply Finset.noncommProd_commute
  simp only [id.def]
  exact hk
#align equiv.perm.commute_of_mem_cycles_factors_commute Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute

/-- The cycles of a permutation commute with it -/
theorem Equiv.Perm.self_mem_cycle_factors_commute {g c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) : Commute c g := by
  apply Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute
  intro c' hc'
  by_cases hcc' : c = c'
  rw [hcc']
  apply g.cycleFactorsFinset_mem_commute hc hc'; exact hcc'
#align equiv.perm.self_mem_cycle_factors_commute Equiv.Perm.self_mem_cycle_factors_commute

/- /-- If a permutation is a cycle of `g`, then its support is invariant under `g`-/
theorem Equiv.Perm.mem_cycleFactorsFinset_support (g c : Equiv.Perm α)
    (hc : c ∈ g.cycleFactorsFinset) (a : α) : a ∈ c.support ↔ g a ∈ c.support := by
  let hc' := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
  constructor
  · intro ha
    rw [← hc'.2 a ha, Equiv.Perm.apply_mem_support]
    exact ha
  · intro ha
    rw [← Equiv.Perm.apply_mem_support]
    suffices : c a = g a
    rw [this]; exact ha
    apply Equiv.injective g
    rw [← hc'.2 (g a) ha]
    simp only [← Equiv.Perm.mul_apply]
    rw [Equiv.Perm.self_mem_cycle_factors_commute g c hc]
#align equiv.perm.mem_cycle_factors_finset_support Equiv.Perm.mem_cycleFactorsFinset_support
 -/

/-- If g and c commute, then g stabilizes the support of c -/
theorem Equiv.Perm.mem_support_of_commute {g c : Equiv.Perm α} (hgc : Commute g c) :
    ∀ x : α, x ∈ c.support ↔ g x ∈ c.support := by
  intro x
  simp only [Equiv.Perm.mem_support, not_iff_not, ← Equiv.Perm.mul_apply]
  rw [← hgc, Equiv.Perm.mul_apply]
  exact (Equiv.apply_eq_iff_eq g).symm
#align equiv.perm.mem_support_of_commute Equiv.Perm.mem_support_of_commute


/-- If `c` and `d` are cycles of `g`,
  then `d` stabilizes the support of `c` -/
theorem Equiv.Perm.mem_support_cycle_of_cycle {g d c : Equiv.Perm α}
  (hc : c ∈ g.cycleFactorsFinset) (hd : d ∈ g.cycleFactorsFinset) :
    ∀ x : α, x ∈ c.support ↔ d x ∈ c.support := by
  intro x
  simp only [Equiv.Perm.mem_support, not_iff_not]
  by_cases h : c = d
  rw [← h, EmbeddingLike.apply_eq_iff_eq]
  rw [← Equiv.Perm.mul_apply,
      Commute.eq (Equiv.Perm.cycleFactorsFinset_mem_commute g hc hd h),
      Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq]

/-- If a permutation is a cycle of `g`, then its support is invariant under `g`-/
theorem Equiv.Perm.mem_cycleFactorsFinset_support {g c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) (a : α) : a ∈ c.support ↔ g a ∈ c.support := by
  apply Equiv.Perm.mem_support_of_commute
  exact (Equiv.Perm.self_mem_cycle_factors_commute hc).symm
#align equiv.perm.mem_cycle_factors_finset_support Equiv.Perm.mem_cycleFactorsFinset_support

-- USEFUL ?
/-- If `c` is a cycle of `g`, `x` belongs to the support of `g`
  and `y` belongs to the support of `c`,
  then `c` is the cycle of `x` for `g` iff `x` and `y` belong to the same cycle. -/
theorem _root_.Equiv.Perm.eq_cycleOf_iff_sameCycle {g : Equiv.Perm α}
    {c : g.cycleFactorsFinset} {x y : α}
    (hx : x ∈ g.support) (hy : y ∈ Equiv.Perm.support c):
    c = g.cycleOf x ↔ g.SameCycle y x := by
  rw [Equiv.Perm.cycle_is_cycleOf hy c.prop]
  constructor
  · intro hx'
    apply And.left
    rw [← Equiv.Perm.mem_support_cycleOf_iff]
    rw [hx', Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]
    exact hx
  · intro hxy
    rw [Equiv.Perm.SameCycle.cycleOf_eq hxy]
#align on_cycle_factors.same_cycle_of_mem_support_iff Equiv.Perm.eq_cycleOf_iff_sameCycle

/-- If `x` and `y` are in the same cycle for `g`,
  `c` is a cycle of `g`, and `y` belongs to the support of `c`,
  then `c` is the cycle of `x` for `g`. -/
theorem _root_.Equiv.Perm.SameCycle.eq_cycleOf
    {g : Equiv.Perm α} (c : g.cycleFactorsFinset) {x y}
    (hx : g.SameCycle y x) (hy : y ∈ Equiv.Perm.support c):
    c = g.cycleOf x := by
  rw [Equiv.Perm.cycle_is_cycleOf hy c.prop, Equiv.Perm.SameCycle.cycleOf_eq hx]
#align on_cycle_factors.same_cycle.is_cycle_of Equiv.Perm.SameCycle.eq_cycleOf

theorem _root_.Equiv.Perm.sameCycle_of_mem_support
    {g : Equiv.Perm α} {x : α} (hx : x ∈ g.support) :
    ∃ c : g.cycleFactorsFinset, ∀ y ∈ Equiv.Perm.support c, g.SameCycle y x := by
  use ⟨g.cycleOf x, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx⟩
  intro y hy
  rw [← Equiv.Perm.eq_cycleOf_iff_sameCycle hx hy]
#align on_cycle_factors.same_cycle_of_mem_support Equiv.Perm.sameCycle_of_mem_support

theorem Equiv.Perm.subtypePerm_apply_pow_of_mem (g : Equiv.Perm α) (s : Finset α)
    (hs : ∀ x : α, x ∈ s ↔ g x ∈ s) (n : ℕ) (x : α) (hx : x ∈ s) :
    ((g.subtypePerm hs ^ n) (⟨x, hx⟩ : s) : α) = (g ^ n) x := by
  revert x
  induction' n with n hrec
  · -- zero case
    intro x hx
    simp only [pow_zero, Equiv.Perm.coe_one, id.def, Subtype.coe_mk]
  · -- induction case
    intro x hx
    simp only [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]
    apply hrec
#align equiv.perm.subtype_perm_apply_pow_of_mem Equiv.Perm.subtypePerm_apply_pow_of_mem

theorem Equiv.Perm.subtypePerm_apply_zpow_of_mem (g : Equiv.Perm α) (s : Finset α)
    (hs : ∀ x : α, x ∈ s ↔ g x ∈ s) (i : ℤ) (x : α) (hx : x ∈ s) :
    ((g.subtypePerm hs ^ i) (⟨x, hx⟩ : s) : α) = (g ^ i) x := by
  induction' i with i i
  -- nat case
  apply Equiv.Perm.subtypePerm_apply_pow_of_mem
  -- neg_succ case
  simp only [zpow_negSucc]
  apply Equiv.injective (g ^ (i + 1))
  simp only [Equiv.Perm.apply_inv_self]
  rw [← Equiv.Perm.subtypePerm_apply_pow_of_mem g s hs]
  rw [Finset.mk_coe, Equiv.Perm.apply_inv_self, Subtype.coe_mk]
  apply Finset.coe_mem
#align equiv.perm.subtype_perm_apply_zpow_of_mem Equiv.Perm.subtypePerm_apply_zpow_of_mem

/-- The support of a permutation is invariant -/
theorem Equiv.Perm.isInvariant_of_support_le {c : Equiv.Perm α} {s : Finset α}
    (hcs : c.support ≤ s) (x : α) : x ∈ s ↔ c x ∈ s := by
  by_cases hx' : x ∈ c.support
  · simp only [hcs hx', true_iff_iff]
    exact hcs (Equiv.Perm.apply_mem_support.mpr hx')
  rw [Equiv.Perm.not_mem_support.mp hx']
#align equiv.perm.le_support_is_invariant Equiv.Perm.isInvariant_of_support_le

/-- Restrict a permutation to its support -/
def Equiv.Perm.subtypePermOfSupport (c : Equiv.Perm α) : Equiv.Perm c.support :=
  Equiv.Perm.subtypePerm c fun _ : α => Equiv.Perm.apply_mem_support.symm
#align equiv.perm.subtype_perm_of_support Equiv.Perm.subtypePermOfSupport

/-- Restrict a permutation to a Finset containing its support -/
def Equiv.Perm.subtypePerm_of_support_le (c : Equiv.Perm α) (s : Finset α)
    (hcs : c.support ≤ s) : Equiv.Perm s :=
  Equiv.Perm.subtypePerm c (Equiv.Perm.isInvariant_of_support_le hcs)
#align equiv.perm.subtype_perm_of_support_le Equiv.Perm.subtypePerm_of_support_le

/-- Support of a cycle is nonempty -/
theorem Equiv.Perm.IsCycle.nonempty_support {g : Equiv.Perm α} (hg : g.IsCycle) :
    g.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, Ne.def, Equiv.Perm.support_eq_empty_iff]
  exact Equiv.Perm.IsCycle.ne_one hg
#align equiv.perm.support_of_cycle_nonempty Equiv.Perm.IsCycle.nonempty_support

/-- Centralizer of a cycle is a power of that cycle on the cycle -/
theorem Equiv.Perm.IsCycle.commute_iff' {g c : Equiv.Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ g x ∈ c.support,
        Equiv.Perm.subtypePerm g hc' ∈ Subgroup.zpowers c.subtypePermOfSupport := by
  constructor
  · intro hgc
    let hgc' := Equiv.Perm.mem_support_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := Equiv.Perm.IsCycle.nonempty_support hc
    suffices : c.SameCycle a (g a)
    simp only [Equiv.Perm.SameCycle] at this
    obtain ⟨i, hi⟩ := this; use i
    ext ⟨x, hx⟩
    simp only [Equiv.Perm.subtypePermOfSupport, Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.subtypePerm_apply_zpow_of_mem]
    suffices c.SameCycle a x by
      obtain ⟨j, rfl⟩ := this
      · simp only [← Equiv.Perm.mul_apply, Commute.eq (Commute.zpow_right hgc j)]
        rw [← zpow_add, add_comm i j, zpow_add]
        simp only [Equiv.Perm.mul_apply]
        simp only [EmbeddingLike.apply_eq_iff_eq]
        exact hi
    -- c.same_cycle a x,
    exact hc.sameCycle (mem_support.mp ha) (mem_support.mp hx)
    -- c.same_cycle a (g a),
    apply hc.sameCycle (mem_support.mp ha) (mem_support.mp ((hgc' a).mp ha))
  · -- converse
    rintro ⟨hc', h⟩
    obtain ⟨i, hi⟩ := h
    suffices hi' : ∀ x ∈ c.support, g x = (c ^ i) x
    · ext x
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      by_cases hx : x ∈ c.support
      · -- hx : x ∈ c.support
        rw [hi' x hx]
        rw [hi' (c x) (apply_mem_support.mpr hx)]
        simp only [← Equiv.Perm.mul_apply, ← zpow_add_one, ← zpow_one_add]
        rw [Int.add_comm 1 i]
      · -- hx : x ∉ c.support
        rw [not_mem_support.mp hx]; apply symm
        rw [← Equiv.Perm.not_mem_support]
        intro hx'; apply hx
        exact (hc' x).mpr hx'
    · -- proof of hi'
      intro x hx
      let hix := Equiv.Perm.congr_fun hi ⟨x, hx⟩
      simp only [← Subtype.coe_inj, Equiv.Perm.subtypePermOfSupport] at hix
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply,
        Equiv.Perm.subtypePerm_apply_zpow_of_mem] at hix
      exact hix.symm
#align equiv.perm.centralizer_of_cycle_on' Equiv.Perm.IsCycle.commute_iff'

lemma Equiv.Perm.ofSubtype_eq_iff {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, x ∈ s ↔  g x ∈ s) :
    Equiv.Perm.ofSubtype (g.subtypePerm hg) = c ↔
      c.support ≤ s ∧
      ∀ (hc' : ∀ x, x ∈ s ↔ c x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    suffices hc : support c ≤ s
    use hc
    intro _ a ha
    rw [← h a, ofSubtype_apply_of_mem]
    rfl
    exact ha
    · intro a ha
      by_contra ha'
      rw [Equiv.Perm.mem_support, ← h a, ofSubtype_apply_of_not_mem] at ha
      exact ha rfl
      exact ha'
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_support_le hc)
    by_cases ha : a ∈ s
    · rw [h a ha, ofSubtype_apply_of_mem]
      rfl
      exact ha
    · rw [ofSubtype_apply_of_not_mem]
      apply symm
      rw [← Equiv.Perm.not_mem_support]
      intro ha'
      exact ha (hc ha')
      exact ha

/- theorem Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff' {g c : Equiv.Perm α}
    (hc' : ∀ x, x ∈ c.support ↔ g x ∈ c.support) (n : ℤ) :
    c ^ n = Equiv.Perm.ofSubtype (g.subtypePerm hc') ↔
      c.subtypePermOfSupport ^ n = g.subtypePerm hc' := by
  constructor
  · intro h; ext ⟨x, hx⟩; let h' := Equiv.Perm.congr_fun h x
    simp only [h', Equiv.Perm.subtypePermOfSupport, Equiv.Perm.subtypePerm_apply_zpow_of_mem,
      Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    exact hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x ∈ c.support
    · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [subtypePermOfSupport, subtypePerm_zpow, subtypePerm_apply]
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      rw [← Equiv.Perm.not_mem_support]
      intro hx'; apply hx
      apply Equiv.Perm.support_zpow_le; exact hx'
      exact hx
#align equiv.perm.zpow_eq_of_subtype_subtype_perm_iff' Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff'
 -/
theorem Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff
    {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, x ∈ s ↔ g x ∈ s) (hc : c.support ⊆ s) (n : ℤ) :
    c ^ n = Equiv.Perm.ofSubtype (g.subtypePerm hg) ↔
      c.subtypePerm (Equiv.Perm.isInvariant_of_support_le hc) ^ n = g.subtypePerm hg := by
  constructor
  · intro h; ext ⟨x, hx⟩; let h' := Equiv.Perm.congr_fun h x
    simp only [h', Equiv.Perm.subtypePerm_apply_zpow_of_mem, Subtype.coe_mk,
      Equiv.Perm.subtypePerm_apply]
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
    exact hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x ∈ s
    · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [subtypePerm_zpow, subtypePerm_apply]
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      rw [← Equiv.Perm.not_mem_support]
      intro hx'
      apply hx
      apply hc; apply Equiv.Perm.support_zpow_le; exact hx'
      exact hx
#align equiv.perm.zpow_eq_of_subtype_subtype_perm_iff Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff

/-- A permutation `g` commutes with a cycle `c` if and only if
  `c.support` is invariant under `g`, and `g` acts on it as a power of `c`. -/
theorem Equiv.Perm.IsCycle.commute_iff {g c : Equiv.Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ g x ∈ c.support,
        Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm g hc') ∈ Subgroup.zpowers c := by
  rw [Equiv.Perm.IsCycle.commute_iff' hc]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro k
  unfold subtypePermOfSupport
  rw [Equiv.Perm.subtypePerm_zpow]
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  apply forall_congr'
  intro a
  by_cases ha : a ∈ c.support
  · rw [imp_iff_right ha]
    apply Eq.congr rfl
    rw [Equiv.Perm.ofSubtype_apply_of_mem]
    rfl
    exact ha
  · rw [iff_true_left _]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    rw [←Equiv.Perm.not_mem_support]
    intro ha'; apply ha
    apply Equiv.Perm.support_zpow_le
    exact ha'
    exact ha
    exact fun b => False.elim (ha b)

theorem Equiv.Perm.IsCycle.forall_commute_iff (g z : Equiv.Perm α) :
    (∀ c ∈ g.cycleFactorsFinset, Commute z c) ↔
      ∀ c ∈ g.cycleFactorsFinset,
      ∃ (hc : ∀ x : α, x ∈ c.support ↔ z x ∈ c.support),
        Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm z hc) ∈ Subgroup.zpowers c := by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  exact Equiv.Perm.IsCycle.commute_iff (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1

/-
/-- A permutation `g` commutes with a cycle `c` if and only if `g``
  stabilizes `c.support` and acts on it as a power of `c`. -/
theorem Equiv.Perm.centralizer_of_cycle_on' (g c : Equiv.Perm α) (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ g x ∈ c.support,
        Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm g hc') ∈ Subgroup.zpowers c := by
  constructor
  · intro hgc
    let hgc' := Equiv.Perm.mem_support_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := Equiv.Perm.IsCycle.nonempty_support hc
    suffices : c.SameCycle a (g a)
    simp only [Equiv.Perm.SameCycle] at this
    obtain ⟨i, hi⟩ := this; use i
    ext x
    by_cases hx : x ∈ c.support
    · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
      obtain ⟨j, rfl⟩ :=
        Equiv.Perm.IsCycle.sameCycle hc (mem_support.mp ha) (mem_support.mp hx)
      simp only [← Equiv.Perm.mul_apply]
      rw [Commute.eq (Commute.zpow_right hgc j)]
      rw [Commute.eq (Commute.zpow_zpow_self c i j)]
      simp only [Equiv.Perm.mul_apply, hi]
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      rw [← Equiv.Perm.not_mem_support]
      intro hx'; apply hx
      apply Equiv.Perm.support_zpow_le
      exact hx'
      exact hx
    -- c.same_cycle a (g a)
    apply Equiv.Perm.IsCycle.sameCycle hc (mem_support.mp ha) (mem_support.mp ((hgc' a).mp ha))
  · -- converse
    rintro ⟨hc', h⟩
    obtain ⟨i, hi⟩ := h
    suffices hi' : ∀ x ∈ c.support, g x = (c ^ i) x
    · ext x
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      by_cases hx : x ∈ c.support
      · -- hx : x ∈ c.support
        rw [hi' x hx]
        rw [hi' (c x) (apply_mem_support.mpr hx)]
        simp only [← Equiv.Perm.mul_apply, ← zpow_add_one, ← zpow_one_add]
        rw [Int.add_comm 1 i]
      · -- hx : x ∉ c.support
        rw [not_mem_support.mp hx]
        apply symm
        rw [← Equiv.Perm.not_mem_support]
        intro hx'; apply hx
        exact (hc' x).mpr hx'
    · -- proof of hi'
      intro x hx
      simp only at hi
      rw [hi]
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
      exact hx
#align equiv.perm.centralizer_of_cycle_on Equiv.Perm.centralizer_of_cycle_on
-/

/-- A permutation restricted to the support of a cycle factor is that cycle factor -/
theorem Equiv.Perm.subtypePerm_on_cycleFactorsFinset {g c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    g.subtypePerm (Equiv.Perm.mem_cycleFactorsFinset_support hc) =
      c.subtypePermOfSupport := by
  ext ⟨x, hx⟩
  simp only [subtypePerm_apply, Subtype.coe_mk, subtypePermOfSupport]
  exact ((mem_cycleFactorsFinset_iff.mp hc).2 x hx).symm
#align equiv.perm.subtype_perm_on_cycle_factor Equiv.Perm.subtypePerm_on_cycleFactorsFinset

theorem Equiv.Perm.commute_of_mem_cycleFactorsFinset_iff {g k c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    Commute k c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ k x ∈ c.support,
        k.subtypePerm hc' ∈ Subgroup.zpowers
          (g.subtypePerm (mem_cycleFactorsFinset_support hc)) := by
  rw [Equiv.Perm.IsCycle.commute_iff' (mem_cycleFactorsFinset_iff.mp hc).1]
  apply exists_congr
  intro hc'
  simp only [Subgroup.mem_zpowers_iff]
  apply exists_congr
  intro n
  unfold subtypePermOfSupport
  rw [Equiv.Perm.subtypePerm_on_cycleFactorsFinset hc]
  rfl
#align equiv.perm.centralizer_mem_cycle_factors_iff' Equiv.Perm.commute_of_mem_cycleFactorsFinset_iff

/- -- KEEP IT?
theorem Equiv.Perm.commute_of_mem_cycleFactorsFinset_iff {g k c : Equiv.Perm α}
    (hc : c ∈ g.cycleFactorsFinset) :
    Commute k c ↔
      ∃ hc' : ∀ x : α, x ∈ c.support ↔ k x ∈ c.support,
        Equiv.Perm.ofSubtype (k.subtypePerm hc') ∈ Subgroup.zpowers c := by
  rw [Equiv.Perm.IsCycle.commute_iff]
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
#align equiv.perm.centralizer_mem_cycle_factors_iff Equiv.Perm.commute_of_mem_cycleFactorsFinset_iff
 -/

theorem Equiv.Perm.zpow_mod_card_support_cycleOf_self_apply [Fintype α]
    (f : Equiv.Perm α) (n : ℤ) (x : α) :
    (f ^ (n % ((Equiv.Perm.cycleOf f x).support.card) : ℤ) : Equiv.Perm α) x =
      (f ^ n) x := by
  by_cases hx : f x = x
  · rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hx]
  · rw [← f.cycleOf_zpow_apply_self, ← f.cycleOf_zpow_apply_self,
      ← (f.isCycle_cycleOf hx).orderOf, ← zpow_eq_mod_orderOf]
#align equiv.perm.zpow_mod_card_support_cycle_of_self_apply Equiv.Perm.zpow_mod_card_support_cycleOf_self_apply

theorem Equiv.Perm.cycle_zpow_mem_support_iff {g : Equiv.Perm α}
    (hg : g.IsCycle) {n : ℤ} {x : α} (hx : g x ≠ x) :
    (g ^ n) x = x ↔ n % g.support.card = 0 := by
  let q := n / g.support.card; let r := n % g.support.card
  change _ ↔ r = 0
  have div_euc : r + g.support.card * q = n ∧ 0 ≤ r ∧ r < g.support.card := by
    rw [← Int.ediv_emod_unique _]
    constructor; rfl; rfl
    simp only [Int.coe_nat_pos]
    apply lt_of_lt_of_le _ (Equiv.Perm.IsCycle.two_le_card_support hg); norm_num
  simp only [← hg.orderOf] at div_euc
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le div_euc.2.1
  simp only [hm, Nat.cast_nonneg, Nat.cast_lt, true_and_iff] at div_euc
  simp only [hm, Nat.cast_eq_zero]
  rw [← div_euc.1, zpow_add g, zpow_mul, zpow_ofNat]
  simp only [pow_orderOf_eq_one, zpow_ofNat, one_zpow, mul_one]
  have : (g ^ m) x = x ↔ g ^ m = 1 := by
    constructor
    · intro hgm
      simp [Equiv.Perm.IsCycle.pow_eq_one_iff hg]
      use x
    · intro hgm; rw [hgm]; simp only [Equiv.Perm.coe_one, id.def]
  rw [this, div_euc.1, ← hg.orderOf, hm]
  cases' dec_em (m = 0) with hm0 hm0'
  · simp only [hm0, pow_zero, Nat.cast_zero]
  · simp only [Nat.cast_eq_zero, hm0', iff_false]
    exact pow_ne_one_of_lt_orderOf' hm0' div_euc.2
#align equiv.perm.cycle_zpow_mem_support_iff Equiv.Perm.cycle_zpow_mem_support_iff


theorem Equiv.Perm.zpow_eq_zpow_on_iff (g : Equiv.Perm α)
    (m n : ℤ) (x : α) (hx : g x ≠ x) :
    (g ^ m) x = (g ^ n) x ↔
      m % (g.cycleOf x).support.card = n % (g.cycleOf x).support.card := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  conv_lhs => rw [← Int.sub_add_cancel m n, Int.add_comm, zpow_add]
  simp only [coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq,
    EuclideanDomain.mod_eq_zero]
  rw [← Equiv.Perm.cycleOf_zpow_apply_self g x]
  rw [Equiv.Perm.cycle_zpow_mem_support_iff]
  · simp only [EuclideanDomain.mod_eq_zero]
  · exact Equiv.Perm.isCycle_cycleOf g hx
  · simp only [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]; exact hx
#align equiv.perm.zpow_eq_zpow_on_iff Equiv.Perm.zpow_eq_zpow_on_iff

instance MulAction.decidableMemFixedBy {α β : Type _}
    [Monoid α] [DecidableEq β] [MulAction α β] (a : α) :
    DecidablePred fun b : β => b ∈ MulAction.fixedBy α β a := by
  intro b
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
  infer_instance
#align mul_action.decidable_mem_fixed_by MulAction.decidableMemFixedBy

instance MulAction.decidableMemStabilizer {α β : Type _}
    [Group α] [DecidableEq β] [MulAction α β] (b : β) :
    DecidablePred fun g : α => g ∈ MulAction.stabilizer α b := by
  intro g
  simp only [mem_stabilizer_iff]
  infer_instance
#align mul_action.decidable_mem_stabilizer MulAction.decidableMemStabilizer

def Equiv.permConjStabilizerFun (g : Equiv.Perm α) :
    (Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g) ×
        ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α)) →
      Equiv.Perm α :=
  fun uv : Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g) ×
      ∀ c ∈ g.cycleFactorsFinset, Subgroup.zpowers (c : Equiv.Perm α) =>
  Equiv.Perm.ofSubtype uv.fst *
    Finset.noncommProd g.cycleFactorsFinset
      (fun c => dite (c ∈ g.cycleFactorsFinset) (fun hc => uv.snd c hc) fun hc => 1)
      fun c hc d hd h => by
      simp only [Finset.mem_coe] at hc hd
      simp only [dif_pos hd, dif_pos hc]
      obtain ⟨m, hc'⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd c hc).prop
      obtain ⟨n, hd'⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd d hd).prop
      rw [← hc', ← hd']
      apply Commute.zpow_zpow
      exact g.cycleFactorsFinset_mem_commute hc hd h
#align equiv.perm_conj_stabilizer_fun Equiv.permConjStabilizerFun

theorem commute_ofSubtype_disjoint {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, ¬(p a ∧ q a)) (x : Equiv.Perm (Subtype p)) (y : Equiv.Perm (Subtype q)) :
    Commute (Equiv.Perm.ofSubtype x) (Equiv.Perm.ofSubtype y) := by
  apply Equiv.Perm.Disjoint.commute
  intro a
  by_cases hx : p a
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem y]
    apply Or.intro_right; rfl
    exact not_and.mp (hpq a) hx
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem x hx]
    apply Or.intro_left; rfl
#align commute_of_subtype_disjoint commute_ofSubtype_disjoint
/-
example (f : Equiv.Perm α) (a : α): f.symm (f a) = a := by
  exact Equiv.symm_apply_apply f a

example (f : Equiv.Perm α) (a : α): f (f.symm a) = a := by
  exact Equiv.apply_symm_apply f a

/-- The canonical map from a product of symmetric groups
  on the fibers of a map to the ambient symmetric group -/
def Equiv.Perm.ofPartitionFun {ι : Type _} [DecidableEq ι] (p : α → ι) (s : Finset ι) :
    (∀ i ∈ s, Equiv.Perm {a | p a = i}) → Equiv.Perm α := fun f =>
  s.noncommProd (fun i => dite (i ∈ s) (fun hi => Equiv.Perm.ofSubtype (f i hi)) fun _ => 1)
    (by
      intro i hi j hj hij
      simp only [Finset.mem_coe] at hi hj
      simp only [dif_pos hi, dif_pos hj]
      -- case h : ¬ (i = j)
      convert commute_ofSubtype_disjoint _ (f i hi) (f j hj)
      intro x
      simp only [Set.mem_setOf_eq, not_and]
      intro h'i h'j; apply hij; rw [← h'i]; exact h'j)
#align equiv.perm.of_partition_fun Equiv.Perm.ofPartitionFun

/-- The canonical morphism from a product of symmetric groups
  on the fibers of a map to the ambient symmetric group -/
def Equiv.Perm.ofPartition {ι : Type _} [Fintype ι] [DecidableEq ι] (p : α → ι) :
    ((i : ι) → Equiv.Perm {a | p a = i}) →* Equiv.Perm α where
  toFun u := Equiv.Perm.ofPartitionFun p Finset.univ fun i _ => u i
  map_one' := by
    rw [← Subgroup.mem_bot]
    apply Subgroup.noncommProd_mem
    intro i hi
    simp only [dif_pos hi]
    rw [Subgroup.mem_bot]
    convert map_one Equiv.Perm.ofSubtype
  map_mul' := by
    intro f g
    simp only [Equiv.Perm.ofPartitionFun]
    rw [← Finset.noncommProd_mul_distrib]
    apply Finset.noncommProd_congr rfl
    · intro x hx
      dsimp
      simp only [if_pos hx]
      apply map_mul
    · intro x hx y hy h
      simp only [Finset.mem_coe] at hx hy
      simp only [dif_pos hx, dif_pos hy]
      apply commute_ofSubtype_disjoint
      simp only [Set.mem_setOf_eq, not_and]
      intro a h' h''; apply h; rw [← h', ← h'']
#align equiv.perm.of_partition Equiv.Perm.ofPartition

/-- Evaluation of `Equiv.Perm.ofPartition` -/
theorem Equiv.Perm.ofPartition_coe_apply' {ι : Type _} [DecidableEq ι]
    (p : α → ι) (s : Finset ι)
    (u : ∀ i ∈ s, Equiv.Perm {x | p x = i}) (i : ι) (a : {x : α | p x = i}) :
    Equiv.Perm.ofPartitionFun p s u (a : α) =
      dite (i ∈ s) (fun hi => (u i hi) a) fun _ => a := by
  simp only [Equiv.Perm.ofPartitionFun]
  induction' s using Finset.induction with j s hj ih
  -- empty
  simp only [Finset.noncommProd_empty, Equiv.Perm.coe_one, id.def, Finset.not_mem_empty, if_false]
  rw [dif_neg id]
  · -- insert
    rw [Finset.noncommProd_insert_of_not_mem s j _ _ hj]
    rw [Equiv.Perm.mul_apply]
    simp only [dif_pos (Finset.mem_insert_self j s)]
    split_ifs with h
    · rw [Finset.mem_insert] at h
      cases' h with h1 h2
      · subst h1
        suffices : Equiv.Perm.ofSubtype (u i h) a = (u i h) a
        rw [← this]
        apply congr_arg
        specialize ih fun i hi => u i (Finset.mem_insert_of_mem hi)
        simp only [dif_neg hj] at ih
        conv_rhs => rw [← ih]
        apply congr_arg₂ _ _ rfl
        apply Finset.noncommProd_congr rfl
        · intro k hk
          simp only [dif_pos hk, dif_pos (Finset.mem_insert_of_mem hk)]
        · rw [Equiv.Perm.ofSubtype_apply_of_mem]
      · specialize ih fun i hi => u i (Finset.mem_insert_of_mem hi)
        simp only [dif_pos h2] at ih
        suffices : ∀ h' : j ∈ insert j s, Equiv.Perm.ofSubtype (u j h') ((u i h) a) = (u i h) a
        rw [← this _]
        apply congr_arg
        rw [← ih]
        apply congr_arg₂ _ _ rfl
        apply Finset.noncommProd_congr rfl
        · intro k hk
          simp only [dif_pos hk, dif_pos (Finset.mem_insert_of_mem hk)]
        · intro h'
          rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
          simp only [Set.mem_setOf_eq]; intro h''
          suffices : p ((u i h) a) = i
          apply hj; rw [← h'']; rw [this]; exact h2
          exact (u i h a).prop
    · specialize ih fun i hi => u i (Finset.mem_insert_of_mem hi)
      simp only [Finset.mem_insert, not_or] at h
      simp only [dif_neg h.2] at ih
      suffices : ∀ h' : j ∈ insert j s, Equiv.Perm.ofSubtype (u j h') a = a
      convert this _
      conv_rhs => rw [← ih]
      apply congr_arg₂ _ _ rfl
      apply Finset.noncommProd_congr rfl
      · intro k hk
        simp only [dif_pos hk, dif_pos (Finset.mem_insert_of_mem hk)]
      · exact Finset.mem_insert_self j s
      · intro h'
        rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
        simp only [Set.mem_setOf_eq]
        intro h'
        suffices : p a = i; apply h.1
        rw [← h']; rw [this]
        exact a.prop
#align equiv.perm.of_partition_coe_apply' Equiv.Perm.ofPartition_coe_apply'

theorem Equiv.Perm.ofPartition_coe_apply {ι : Type _} [Fintype ι] [DecidableEq ι]
    {p : α → ι} (u : ∀ i, Equiv.Perm {x | p x = i}) (i : ι) (a : {x : α | p x = i}) :
    Equiv.Perm.ofPartition p u (a : α) = (u i) a := by
  dsimp [Equiv.Perm.ofPartition]
  rw [Equiv.Perm.ofPartition_coe_apply' p Finset.univ fun i _ => u i]
  simp only [dif_pos (Finset.mem_univ i)]
#align equiv.perm.of_partition_coe_apply Equiv.Perm.ofPartition_coe_apply

theorem Equiv.Perm.ofPartition_inj {ι : Type _} [Fintype ι] [DecidableEq ι] (p : α → ι) :
    Function.Injective (Equiv.Perm.ofPartition p) := by
  intro u v h
  ext i a
  rw [← Equiv.Perm.ofPartition_coe_apply]
  rw [h]
  rw [Equiv.Perm.ofPartition_coe_apply]
#align equiv.perm.of_partition_inj Equiv.Perm.ofPartition_inj

theorem Equiv.Perm.ofPartition_range
    {ι : Type _} [Fintype ι] [DecidableEq ι] (p : α → ι)
    (f : Equiv.Perm α) : f ∈ (Equiv.Perm.ofPartition p).range ↔ p ∘ f = p := by
  constructor
  · rintro ⟨u, rfl⟩
    ext a
    rw [Function.comp_apply, ← Subtype.coe_mk a _, Equiv.Perm.ofPartition_coe_apply u, Subtype.coe_mk]
    refine (u (p a) _).prop
    simp only [Set.mem_setOf_eq]
  · intro h
    use fun i => f.subtypePerm ?_ -- (h' i)
    ext a
    rw [← Subtype.coe_mk a _, Equiv.Perm.ofPartition_coe_apply, Subtype.coe_mk]
    simp only [Set.mem_setOf_eq, Set.coe_setOf, subtypePerm_apply]
    · rw [Set.mem_setOf_eq]
    · intro a
      simp only [Set.mem_setOf_eq]
      nth_rewrite 1 [← h]
      simp only [Function.comp_apply]
#align equiv.perm.of_partition_range Equiv.Perm.ofPartition_range
 -/

local instance {ι : Type*} :
    MulAction (Equiv.Perm α) (α → ι) :=
  arrowAction

/-- The cardinality of the subgroup of partitions preserving a fibration -/
theorem Equiv.Perm.of_partition_card {ι : Type*} [Fintype ι] [DecidableEq ι] (p : α → ι) :
    Fintype.card {f : Equiv.Perm α | p ∘ f = p} =
      Finset.univ.prod
        fun i => (Fintype.card {a | p a = i}).factorial := by
  suffices : ∀ x : Equiv.Perm α, (x ∈ MulAction.stabilizer (Equiv.Perm α) p ↔ p ∘ x = p)
  simp_rw [← this]
  suffices : Fintype.card {f | f ∈ MulAction.stabilizer (Equiv.Perm α) p} = Fintype.card (MulAction.stabilizer (Equiv.Perm α) p)
  rw [this, Fintype.card_congr (Φ p).toEquiv]
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact Fintype.card_perm
  · rw [Fintype.card_ofFinset, ← Fintype.subtype_card]
    intro x
    simp only [MulAction.mem_stabilizer_iff, Set.mem_setOf_eq, Finset.mem_univ, forall_true_left, ne_eq,
      Finset.mem_filter, true_and]
  · intro x
    simp only [MulAction.mem_stabilizer_iff]
    suffices : ∀ x : Equiv.Perm α, (x • p = p ↔ p ∘ x = p)
    simp_rw [this]
    intro x
    change p ∘ (x⁻¹ : Equiv.Perm α) = p ↔ p ∘ x = p
    rw [Equiv.Perm.inv_def, Equiv.comp_symm_eq, eq_comm]

/- /-- The cardinality of the subgroup of partitions preserving a fibration -/
theorem Equiv.Perm.of_partition_card'
    {ι : Type _} [Fintype ι] [DecidableEq ι] (p : α → ι) :
    Fintype.card {f : Equiv.Perm α | p ∘ f = p} =
      Finset.prod (⊤ : Finset ι) fun i => (Fintype.card {a | p a = i}).factorial := by
  let φ := Equiv.Perm.ofPartition p
  let hφ_inj := Equiv.Perm.ofPartition_inj p
  let hφ_range := Equiv.Perm.ofPartition_range p
  suffices : Fintype.card (∀ i : ι, Equiv.Perm {a | p a = i}) =
    Fintype.card {f : Equiv.Perm α | p ∘ f = p}
  rw [← this]
  · simp only [Set.coe_setOf, Set.mem_setOf_eq, Fintype.card_pi, Finset.top_eq_univ]
    apply Finset.prod_congr rfl
    intro i _
    exact Fintype.card_perm
  · -- rw [Fintype.card_eq]
    let φ' : (∀ i : ι, Equiv.Perm {a | p a = i}) → {f : Equiv.Perm α | p ∘ f = p} :=
      fun u => ⟨φ u, by simp only [Set.mem_setOf_eq, ← hφ_range _]; use u⟩
    have hφ' : Function.Bijective φ' := by
      constructor
      · -- injectivity
        intro u v
        simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
        apply hφ_inj
      · -- surjectivity
        rintro ⟨f, hf⟩
        simp only [Set.mem_setOf_eq, ← hφ_range] at hf
        obtain ⟨a, ha⟩ := hf
        use a
        simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
        exact ha
    apply Fintype.card_congr (Equiv.ofBijective φ' hφ')
#align equiv.perm.of_partition_card Equiv.Perm.of_partition_card
 -/

end CycleTypes

namespace OnCycleFactors

variable {α : Type _} [DecidableEq α] [Fintype α] (g : Equiv.Perm α)

/- theorem centralizer_le_stab_cycle_fact :
    MulAction.stabilizer (ConjAct (Equiv.Perm α)) g ≤
      MulAction.stabilizer (ConjAct (Equiv.Perm α)) (g.cycleFactorsFinset : Set (Equiv.Perm α)) := by
  intro k
  simp only [MulAction.mem_stabilizer_iff]
  intro hk
  rw [← Finset.coe_smul_finset k _, ← Equiv.Perm.cycleFactorsFinset_conj_eq, hk]
#align on_cycle_factors.centralizer_le_stab_cycle_fact OnCycleFactors.centralizer_le_stab_cycle_fact -/

/-- The action by conjugation of `ConjAct (Equiv.Perm α)`
  on the cycles of a given permutation -/
def subMulAction : SubMulAction
  (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) (Equiv.Perm α) where
  carrier := (g.cycleFactorsFinset : Set (Equiv.Perm α))
  smul_mem' k c hc := by
    have := Equiv.Perm.cycleFactorsFinset_conj_eq (↑k) g
    rw [MulAction.mem_stabilizer_iff.mp k.prop] at this
    rw [this, Finset.coe_smul_finset]
    exact ⟨c, hc, rfl⟩
#align on_cycle_factors.sub_mul_action_on_cycle_factors OnCycleFactors.subMulAction

/-- The action by conjugation of `ConjAct (Equiv.Perm α)`
  on the cycles of a given permutation -/
instance mulAction :
    MulAction (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
      (g.cycleFactorsFinset : Set (Equiv.Perm α)) :=
  (subMulAction g).mulAction
#align on_cycle_factors.mul_action_on_cycle_factors OnCycleFactors.mulAction

/-- The canonical morphism from `MulAction.stabilizer (ConjAct (Equiv.Perm α)) g`
  to the group of permutations of `g.cycleFactorsFinset` -/
def φ := MulAction.toPermHom (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (g.cycleFactorsFinset : Set (Equiv.Perm α))
#align on_cycle_factors.φ OnCycleFactors.φ

theorem φ_eq (k : ConjAct (Equiv.Perm α))
    (hk : k ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) :
    (φ g ⟨k, hk⟩ ⟨c, hc⟩ : Equiv.Perm α) = k • c := rfl
#align on_cycle_factors.φ_eq OnCycleFactors.φ_eq

theorem φ_eq' (k : Equiv.Perm α)
    (hk : k ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g)
    (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset) :
    (φ g ⟨ConjAct.toConjAct k, hk⟩ ⟨c, hc⟩ : Equiv.Perm α) = k * c * k⁻¹ :=  rfl
#align on_cycle_factors.φ_eq' OnCycleFactors.φ_eq'

variable {g}

structure _root_.Equiv.Perm.Basis (g : Equiv.Perm α) where
  (toFun : g.cycleFactorsFinset → α)
  (mem_support : ∀ c, toFun c ∈ (c : Equiv.Perm α).support)

theorem _root_.Equiv.Perm.existsBasis (g : Equiv.Perm α) :
    Nonempty (Equiv.Perm.Basis g) := by
  suffices hsupp_ne :
    ∀ c : g.cycleFactorsFinset, (c : Equiv.Perm α).support.Nonempty
  exact ⟨fun c ↦ (hsupp_ne c).choose, fun c ↦ (hsupp_ne c).choose_spec⟩
  · intro c
    exact Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1
#align on_cycle_factors.exists_base_points Equiv.Perm.existsBasis

-- SHOULD BE DELETED?
-- was ha
theorem _root_.Equiv.Perm.Basis.mem_support'
    (a : Equiv.Perm.Basis g) (c : g.cycleFactorsFinset) :
    a.toFun c ∈ Equiv.Perm.support g := by -- g (a.toFun c) ≠ a.toFun c := by
  rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
    ← Equiv.Perm.cycle_is_cycleOf (a.mem_support c) c.prop]
  exact c.prop
#align on_cycle_factors.ha'2 Equiv.Perm.Basis.mem_support'


/- variable (a : g.cycleFactorsFinset → α)
  (ha : ∀ c : g.cycleFactorsFinset, a c ∈ (c : Equiv.Perm α).support) -/

/-
theorem SameCycle.is_cycleOf' (c : g.cycleFactorsFinset)
    {x} (hx : g.SameCycle (a c) x) :
    g.cycleOf x = c :=
  (Equiv.Perm.SameCycle.eq_cycleOf c hx (ha c)).symm

theorem eq_cycleOf_iff_sameCycle'
    {c : g.cycleFactorsFinset} {x} (hx : x ∈ g.support) :
    c = g.cycleOf x ↔ g.SameCycle (a c) x :=
  Equiv.Perm.eq_cycleOf_iff_sameCycle hx (ha c)
#align on_cycle_factors.same_cycle_of_mem_support_iff' OnCycleFactors.eq_cycleOf_iff_sameCycle'
 -/

/-- The basic function that allows to define the inverse of `OnCycleFactors.φ`-/
def Kf (a : Equiv.Perm.Basis g) :
    Equiv.Perm g.cycleFactorsFinset → g.cycleFactorsFinset × ℤ → α :=
  fun e ⟨c, i⟩ => (g ^ i) (a.toFun (e c))
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Kf OnCycleFactors.Kf

/- -- This version would have been simpler, but doesn't work later
 -- because of the use of Function.extend which requires functions
 -- with *one* argument.
def Kf (a : Equiv.Perm.Basis g) (e : Equiv.Perm g.cycleFactorsFinset)
  (c : g.cycleFactorsFinset) (i : ℤ) : α :=
  (g ^ i) (a.toFun (e c))
-/
theorem Kf_def (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    Kf a e ⟨c, i⟩ = (g ^ i) (a.toFun (e c)) :=
  rfl
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Kf_apply OnCycleFactors.Kf_def

theorem Kf_def_zero (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} :
    Kf a e ⟨c, 0⟩ = a.toFun (e c) :=
  rfl

theorem Kf_def_one (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} :
    Kf a e ⟨c, 1⟩ = g (a.toFun (e c)) :=
  rfl

/-- The multiplicative-additive property of `OnCycleFactors.Kf` -/
theorem Kf_mul_add  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e e' : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a (e' * e) ⟨c, i + j⟩ = (g ^ i) (Kf a e' ⟨e c, j⟩) := by
  simp only [Kf_def, zpow_add, Equiv.Perm.coe_mul, Function.comp_apply]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Kf_apply' OnCycleFactors.Kf_mul_add

/-- The additive property of `OnCycleFactors.Kf` -/
theorem Kf_add  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a 1 ⟨e c, j⟩) := by
  rw [← Kf_mul_add, one_mul]

/-- The additive property of `OnCycleFactors.Kf` -/
theorem Kf_add'  (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset}
    {e : Equiv.Perm g.cycleFactorsFinset} {i j : ℤ} :
    Kf a e ⟨c, i + j⟩ = (g ^ i) (Kf a e ⟨c, j⟩) := by
  rw [← mul_one e, Kf_mul_add, mul_one]
  rfl

/- -- CAN BE DELETED
theorem ha' (c : g.cycleFactorsFinset) : g.cycleOf (a c) = (c : Equiv.Perm α) :=
  (Equiv.Perm.cycle_is_cycleOf (ha c) c.prop).symm
#align on_cycle_factors.ha' OnCycleFactors.ha'
 -/


-- was ha''
-- DELETE?
theorem _root_.Equiv.Perm.Basis.eq_cycleOf (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset} {i : ℤ} :
    c = g.cycleOf ((g ^ i) (a.toFun c)) := by
  rw [Equiv.Perm.cycleOf_self_apply_zpow,
    ← Equiv.Perm.cycle_is_cycleOf (a.mem_support c) c.prop]
#align on_cycle_factors.ha'3 Equiv.Perm.Basis.eq_cycleOf

theorem _root_.Equiv.Perm.Basis.eq_cycleOf' (a : Equiv.Perm.Basis g)
    {c : g.cycleFactorsFinset} {e : Equiv.Perm g.cycleFactorsFinset} {i : ℤ} :
    e c = g.cycleOf (Kf a e ⟨c, i⟩) := by
  rw [Kf_def, Equiv.Perm.cycleOf_self_apply_zpow,
    Equiv.Perm.cycle_is_cycleOf (a.mem_support (e c)) (e c).prop]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK1 Equiv.Perm.Basis.eq_cycleOf'

theorem _root_.Equiv.Perm.Basis.Kf_apply (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c : g.cycleFactorsFinset} {i : ℤ} :
    g (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  rw [Kf_def, Kf_def, ← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm 1 i]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK2 Equiv.Perm.Basis.Kf_apply

theorem _root_.Equiv.Perm.Basis.Kf_apply' (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c d : g.cycleFactorsFinset} {i : ℤ}
    (hd : d = e c) :
    (d : Equiv.Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i + 1⟩ := by
  -- Kf e ⟨c, i⟩ = (g ^ i) (a (e c)) appartient au cycle de e c
  rw [hd]
  change (e c : Equiv.Perm α) _ = _
  rw [Equiv.Perm.Basis.eq_cycleOf', Equiv.Perm.cycleOf_apply_self,
    Equiv.Perm.Basis.Kf_apply]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK3 Equiv.Perm.Basis.Kf_apply'

theorem _root_.Equiv.Perm.Basis.Kf_apply'' (a : Equiv.Perm.Basis g)
    {e : Equiv.Perm g.cycleFactorsFinset} {c d : g.cycleFactorsFinset} {i : ℤ}
    (hd' : d ≠ e c) :
    (d : Equiv.Perm α) (Kf a e ⟨c, i⟩) = Kf a e ⟨c, i⟩ := by
  suffices hdc : (d : Equiv.Perm α).Disjoint (e c : Equiv.Perm α)
  apply Or.resolve_right (Equiv.Perm.disjoint_iff_eq_or_eq.mp hdc (Kf a e ⟨c, i⟩))
  rw [Equiv.Perm.Basis.eq_cycleOf', Equiv.Perm.cycleOf_apply_self,
    ← Equiv.Perm.cycleOf_eq_one_iff, ← Equiv.Perm.Basis.eq_cycleOf']
  apply Equiv.Perm.IsCycle.ne_one
  refine' (Equiv.Perm.mem_cycleFactorsFinset_iff.mp _).1
  exact g
  exact (e c).prop
  apply g.cycleFactorsFinset_pairwise_disjoint d.prop (e c).prop
  rw [Function.Injective.ne_iff Subtype.coe_injective]
  exact hd'
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK4 Equiv.Perm.Basis.Kf_apply''

/-  -- CAN BE DELETED
theorem haK5 (τ : Equiv.Perm g.cycleFactorsFinset) (x : α)
    (hx : ¬(∃ cj, Kf a 1 cj = x)) :
    Function.extend (Kf a 1) (Kf a τ) id x = x := by
  simp only [Function.extend_apply' _ _ _ hx, id.def]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK5 OnCycleFactors.haK5
 -/

/- -- SHOULD BE DELETED
theorem haK6 (x : α) (hx : x ∉ g.support) (c : g.cycleFactorsFinset) :
    (c : Equiv.Perm α) x = x :=
  Equiv.Perm.not_mem_support.mp <|
    Finset.not_mem_mono
      (Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop) hx
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.haK6 OnCycleFactors.haK6
 -/

theorem _root_.Equiv.Perm.Basis.Kf_factorsThrough (a : Equiv.Perm.Basis g)
    {e e' : Equiv.Perm g.cycleFactorsFinset}
    (hee' : ∀ c : g.cycleFactorsFinset,
        (e c : Equiv.Perm α).support.card = (e' c : Equiv.Perm α).support.card) :
    (Kf a e').FactorsThrough (Kf a e) := by
  --    Kf e ci = Kf e dj → Kf e' ci = Kf e' dj,
  rintro ⟨c, i⟩ ⟨d, j⟩ He
  simp only [Kf_def] at He ⊢
  suffices hcd : c = d
  · rw [hcd] at He ⊢
    rw [g.zpow_eq_zpow_on_iff i j, ← Equiv.Perm.cycle_is_cycleOf (a.mem_support _) (e d).prop] at He
    rw [g.zpow_eq_zpow_on_iff, ← Equiv.Perm.cycle_is_cycleOf (a.mem_support _) (e' d).prop,
      ← hee' d]
    exact He
    · rw [← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
        ← Equiv.Perm.cycle_is_cycleOf (a.mem_support _) (e' d).prop]
      exact (e' d).prop
    · rw [← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff,
        ← Equiv.Perm.cycle_is_cycleOf (a.mem_support _) (e d).prop]
      exact (e d).prop
  · -- d = c
    apply Equiv.injective e
    rw [← Subtype.coe_inj, Equiv.Perm.Basis.eq_cycleOf, Equiv.Perm.Basis.eq_cycleOf, He]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.hkfg Equiv.Perm.Basis.Kf_factorsThrough

noncomputable def k (a : Equiv.Perm.Basis g) :=
  fun τ x => Function.extend (Kf a 1) (Kf a τ) id x
#align on_cycle_factors.k OnCycleFactors.k

theorem k_apply (a : Equiv.Perm.Basis g)
    (c : g.cycleFactorsFinset) (i : ℤ) {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (Kf a 1 ⟨c, i⟩) = Kf a τ ⟨c, i⟩ := by
  simp only [k]
  rw [Function.FactorsThrough.extend_apply (Equiv.Perm.Basis.Kf_factorsThrough a _) id ⟨c, i⟩]
  · intro c; simp only [← hτ c, Equiv.Perm.coe_one, id.def]
#align on_cycle_factors.k_apply OnCycleFactors.k_apply

theorem k_apply_base (a : Equiv.Perm.Basis g)
  {c : g.cycleFactorsFinset} {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (a.toFun c) = a.toFun (τ c) :=
  k_apply a c 0 hτ
#align on_cycle_factors.k_apply_base OnCycleFactors.k_apply_base

-- was k_apply'
theorem k_apply_of_not_mem_support {τ : Equiv.Perm g.cycleFactorsFinset} (x : α)
    (hx : x ∉ g.support) : k a τ x = x := by
  simp only [k]
  rw [Function.extend_apply']
  simp only [id.def]
  intro hyp
  obtain ⟨⟨c, i⟩, rfl⟩ := hyp
  apply hx
  rw [Kf_def, Equiv.Perm.zpow_apply_mem_support]
  apply Equiv.Perm.Basis.mem_support'
  -- exact ha'2 ha c
#align on_cycle_factors.k_apply_of_not_mem_support OnCycleFactors.k_apply_of_not_mem_support

theorem mem_support_iff_exists_Kf (a : Equiv.Perm.Basis g) (x : α) :
    x ∈ g.support ↔
    ∃ (c : g.cycleFactorsFinset) (i : ℤ), x = Kf a 1 ⟨c, i⟩ := by
  constructor
  · intro hx
    rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff] at hx
    use ⟨g.cycleOf x, hx⟩
    simp only [Kf_def, Equiv.Perm.coe_one, id.def]
    let ha := a.mem_support ⟨g.cycleOf x, hx⟩
    simp only [Subtype.coe_mk, Equiv.Perm.mem_support_cycleOf_iff] at ha
    obtain ⟨i, hi⟩ := ha.1.symm
    exact ⟨i, hi.symm⟩
  · rintro ⟨c, i, rfl⟩
    simp only [Kf_def, Equiv.Perm.zpow_apply_mem_support, Equiv.Perm.coe_one, id.def]
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
    apply a.mem_support
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.mem_support_iff_exists_Kf OnCycleFactors.mem_support_iff_exists_Kf

theorem k_commute_zpow {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) (j : ℤ) :
    k a τ ∘ (g ^ j : Equiv.Perm α) = (g ^ j : Equiv.Perm α) ∘ k a τ := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · rw [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [← Kf_add']
    rw [k_apply a c (j + i) hτ]
    rw [k_apply a c i hτ]
    rw [Kf_add']
  · rw [k_apply_of_not_mem_support x hx]
    rw [k_apply_of_not_mem_support ((g ^ j : Equiv.Perm α) x) _]
    rw [Equiv.Perm.zpow_apply_mem_support]
    exact hx
#align on_cycle_factors.k_commute_zpow OnCycleFactors.k_commute_zpow

theorem k_commute {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ ∘ g = g ∘ k a τ := by
  simpa only [zpow_one] using k_commute_zpow hτ 1
#align on_cycle_factors.k_commute OnCycleFactors.k_commute

theorem k_apply_gen {c : g.cycleFactorsFinset} {i : ℤ}
    {σ τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a τ (Kf a σ ⟨c, i⟩) = Kf a (τ * σ) ⟨c, i⟩ := by
  simp only [Kf_def]
  rw [← Function.comp_apply (f := k a τ), k_commute_zpow hτ, Function.comp_apply]
  apply congr_arg
  dsimp
  have : ∀ (d) (τ : Equiv.Perm g.cycleFactorsFinset),
    a.toFun (τ d) = Kf a 1 (τ d, 0) :=
    fun d τ ↦ rfl
  rw [this _ σ,
    k_apply a (σ c) 0 hτ, ← Function.comp_apply (f := τ), ← Equiv.Perm.coe_mul,
    this _ (τ * σ)]
  rfl
#align on_cycle_factors.k_apply_gen OnCycleFactors.k_apply_gen

theorem k_mul (σ : Equiv.Perm g.cycleFactorsFinset)
    (hσ : ∀ c, (σ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    (τ : Equiv.Perm g.cycleFactorsFinset)
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    k a σ ∘ k a τ = k a (σ * τ) := by
  ext x
  simp only [Function.comp_apply]
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply a c i hτ, k_apply_gen _]
    rw [k_apply_gen]
    simp only [mul_one]
    · intro c
      rw [Equiv.Perm.coe_mul, Function.comp_apply, hσ, hτ]
    exact hσ
  · simp only [k_apply_of_not_mem_support x hx]
#align on_cycle_factors.k_mul OnCycleFactors.k_mul

theorem k_one : k a (1 : Equiv.Perm g.cycleFactorsFinset) = id := by
  ext x
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨c, i, rfl⟩ := hx
    rw [k_apply]
    rfl
    intro c; rfl
  simp only [id.def, k_apply_of_not_mem_support x hx]
#align on_cycle_factors.k_one OnCycleFactors.k_one

theorem k_bij {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    Function.Bijective (k a τ) :=
  by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine' And.intro _ rfl
  rw [Function.surjective_iff_hasRightInverse]
  use k a τ⁻¹
  rw [Function.rightInverse_iff_comp]
  rw [k_mul]; rw [mul_inv_self]; rw [k_one]
  exact hτ
  intro c; rw [← hτ (τ⁻¹ c), Equiv.Perm.apply_inv_self]
#align on_cycle_factors.k_bij OnCycleFactors.k_bij

theorem k_cycle_apply {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card)
    (c : g.cycleFactorsFinset) (x : α) :
    k a τ ((c : Equiv.Perm α) x) = (τ c : Equiv.Perm α) (k a τ x) := by
  by_cases hx : x ∈ g.support
  · simp only [mem_support_iff_exists_Kf a] at hx
    obtain ⟨d, j, rfl⟩ := hx
    by_cases hcd : c = d
    · rw [hcd, Equiv.Perm.Basis.Kf_apply',
        k_apply a d _ hτ, k_apply a d _ hτ, ← Equiv.Perm.Basis.Kf_apply']
      rfl
      simp only [Equiv.Perm.coe_one, id.def]
    · rw [Equiv.Perm.Basis.Kf_apply'' a,
        k_apply a _ _ hτ, Equiv.Perm.Basis.Kf_apply'' a]
      exact (Equiv.injective τ).ne_iff.mpr hcd
      exact hcd
  · suffices : ∀ (c : g.cycleFactorsFinset), (c : Equiv.Perm α) x = x
    simp only [this, k_apply_of_not_mem_support x hx]
    · intro c
      rw [← Equiv.Perm.not_mem_support]
      apply Finset.not_mem_mono _ hx
      exact Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
#align on_cycle_factors.k_cycle_apply OnCycleFactors.k_cycle_apply

theorem hφ_eq_card_of_mem_range {τ} (hτ : τ ∈ (φ g).range) (c) :
  (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
--  rintro ⟨c, hc⟩
  obtain ⟨⟨k, hk⟩, rfl⟩ := hτ
  rw [φ_eq, ConjAct.smul_def, Equiv.Perm.support_conj]
  apply Finset.card_map
#align on_cycle_factors.hφ_eq_card_of_mem_range OnCycleFactors.hφ_eq_card_of_mem_range

noncomputable def φ'Fun (a : Equiv.Perm.Basis g)
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    Equiv.Perm α :=
  Equiv.ofBijective (k a τ) (k_bij hτ)
#align on_cycle_factors.φ'_fun OnCycleFactors.φ'Fun

theorem φ'_mem_stabilizer (a : Equiv.Perm.Basis g)
    {τ : Equiv.Perm g.cycleFactorsFinset}
    (hτ : ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card) :
    ConjAct.toConjAct (φ'Fun a hτ) ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g := by
  rw [MulAction.mem_stabilizer_iff]
  rw [ConjAct.smul_def]
  rw [ConjAct.ofConjAct_toConjAct]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Equiv.Perm.coe_mul]
  simp only [φ'Fun]
  simp only [Function.comp_apply, Equiv.ofBijective_apply]
  rw [← Function.comp_apply (f := k a τ)]
  rw [k_commute hτ]
  rfl
#align on_cycle_factors.φ'_mem_stabilizer OnCycleFactors.φ'_mem_stabilizer

variable (g)

/-- The range of `OnCycleFactors.φ` -/
def Iφ : Subgroup (Equiv.Perm g.cycleFactorsFinset) where
  carrier := {τ | ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Equiv.Perm.coe_one, id.def, eq_self_iff_true, imp_true_iff]
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Subtype.forall, Set.mem_setOf_eq, Equiv.Perm.coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ hτ
    intro c hc
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ
    simp only [Subtype.forall, Set.mem_setOf_eq]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ
    intro c hc
    rw [← hσ ]
    simp only [Finset.coe_mem, Subtype.coe_eta, Equiv.Perm.apply_inv_self]
    simp only [Finset.coe_mem]
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Iφ OnCycleFactors.Iφ

variable {g}

theorem mem_Iφ_iff {τ : Equiv.Perm g.cycleFactorsFinset} :
    τ ∈ Iφ g ↔ ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  simp only [Iφ]; rfl
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.mem_Iφ_iff OnCycleFactors.mem_Iφ_iff

/-- Given `a : Equiv.Perm.Basis g`,
  we define a right inverse of `OnCycleFactors.φ`, on `Iφ g` -/
noncomputable
def φ' (a : Equiv.Perm.Basis g) :
    Iφ g →* MulAction.stabilizer (ConjAct (Equiv.Perm α)) g  where
  toFun τhτ :=
    ⟨ConjAct.toConjAct (φ'Fun a (mem_Iφ_iff.mp τhτ.prop)),
      φ'_mem_stabilizer a (mem_Iφ_iff.mp τhτ.prop)⟩
  map_one' := by
    simp only [Subgroup.coe_one, Subgroup.mk_eq_one_iff, MulEquivClass.map_eq_one_iff]
    ext x
    simp only [φ'Fun, k_one, Equiv.ofBijective_apply, id_eq, Equiv.Perm.coe_one]
  map_mul' σ τ := by
    simp only [Subgroup.coe_mul, Submonoid.mk_mul_mk, Subtype.mk_eq_mk, ← ConjAct.toConjAct_mul]
    apply congr_arg
    ext x
    simp only [φ'Fun, ← k_mul _ σ.prop _ τ.prop,
      Equiv.ofBijective_apply, Function.comp_apply, Equiv.Perm.coe_mul]
#align on_cycle_factors.φ' OnCycleFactors.φ'

theorem hφ'_is_rightInverse (τ : Iφ g) :
    (φ g) ((φ' a) τ) = (τ : Equiv.Perm g.cycleFactorsFinset) := by
  apply Equiv.Perm.ext
  rintro ⟨c, hc⟩
  simp only [φ', φ'Fun]; dsimp
  ext x
  rw [φ_eq g, ConjAct.smul_def]
  simp only [ConjAct.ofConjAct_toConjAct]
  apply congr_fun
  dsimp
  simp only [← Equiv.Perm.coe_mul]
  apply congr_arg
  rw [mul_inv_eq_iff_eq_mul]
  ext y
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.ofBijective_apply]
  exact k_cycle_apply τ.prop ⟨c, hc⟩ y
#align on_cycle_factors.hφ'_is_right_inverse OnCycleFactors.hφ'_is_rightInverse

theorem φ'_apply' {τ} (hτ) (x) :
    (ConjAct.ofConjAct (φ' a ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))) x = k a τ x :=
  rfl
#align on_cycle_factors.φ'_apply' OnCycleFactors.φ'_apply'

theorem φ'_apply (τ : Iφ g) (x) :
    ConjAct.ofConjAct (φ' a τ : ConjAct (Equiv.Perm α)) x = k a τ.val x :=
  rfl
#align on_cycle_factors.φ'_apply OnCycleFactors.φ'_apply

theorem φ'_support_le (τ : Iφ g) :
    (ConjAct.ofConjAct (φ' a τ : ConjAct (Equiv.Perm α))).support ≤
      g.support := by
  intro x
  simp only [Equiv.Perm.mem_support]
  intro hx' hx
  apply hx'
  rw [← Equiv.Perm.not_mem_support] at hx
  exact OnCycleFactors.k_apply_of_not_mem_support x hx


theorem hφ'_equivariant (τ : Iφ g) (c : g.cycleFactorsFinset) :
    (φ' a τ  : ConjAct (Equiv.Perm α)) • (c : Equiv.Perm α) = τ.val c := by
  rw [ConjAct.smul_def]
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  exact OnCycleFactors.k_cycle_apply τ.prop c x

/- theorem coe_φ' {τ} (hτ) : k a τ = ConjAct.ofConjAct (φ' a ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α)) :=
  rfl
#align on_cycle_factors.coe_φ' OnCycleFactors.coe_φ'
 -/

theorem Iφ_eq_range : Iφ g = (φ g).range := by
  obtain ⟨a⟩ := g.existsBasis
  ext τ
  constructor
  · intro hτ
    rw [MonoidHom.mem_range]
    use (φ' a) ⟨τ, hτ⟩
    simp only [Finset.coe_sort_coe]
    rw [hφ'_is_rightInverse ⟨τ, hτ⟩, Subgroup.coe_mk]
  · rw [mem_Iφ_iff]
    exact hφ_eq_card_of_mem_range
set_option linter.uppercaseLean3 false in
#align on_cycle_factors.Iφ_eq_range OnCycleFactors.Iφ_eq_range

theorem hφ_mem_range_iff {τ} :
    τ ∈ (φ g).range ↔
      ∀ c, (τ c : Equiv.Perm α).support.card = (c : Equiv.Perm α).support.card := by
  simp only [← Iφ_eq_range, mem_Iφ_iff]
  rfl
#align on_cycle_factors.hφ_mem_range_iff OnCycleFactors.hφ_mem_range_iff

/- For the moment, we can only analyse the permutations which
  respect a fibration when there is a `Fintype` assumption on the base.
  So we have to view the lengths of the cycles
   as members of the Fintype `Fin (Fintype.card α + 1)` -/

-- FIND A BETTER NAME
/-- The lengths of the cycles, as a member of a Fintype -/
def fsc : g.cycleFactorsFinset → Fin (Fintype.card α + 1) :=
  fun c => ⟨(c : Equiv.Perm α).support.card,
    Nat.lt_succ_iff.mpr (c : Equiv.Perm α).support.card_le_univ⟩
#align on_cycle_factors.fsc OnCycleFactors.fsc

theorem hφ_range' :
    ((φ g).range : Set (Equiv.Perm (g.cycleFactorsFinset : Set (Equiv.Perm α)))) =
      {τ : Equiv.Perm g.cycleFactorsFinset | fsc ∘ τ = fsc} := by
  rw [← Iφ_eq_range]
  ext τ
  simp only [SetLike.mem_coe, mem_Iφ_iff]
  change _ ↔ fsc ∘ τ = fsc
  simp only [fsc]
  rw [Function.funext_iff]
  dsimp
  apply forall_congr'
  intro c
  rw [← Function.Injective.eq_iff Fin.val_injective]
#align on_cycle_factors.hφ_range' OnCycleFactors.hφ_range'

theorem hφ_range_card' :
    Nat.card (φ g).range =
      Fintype.card {k : Equiv.Perm g.cycleFactorsFinset | fsc ∘ k = fsc} := by
  simp_rw [← hφ_range', Nat.card_eq_fintype_card]
  rfl
#align on_cycle_factors.hφ_range_card' OnCycleFactors.hφ_range_card'

theorem hφ_range_card :
    Nat.card (φ g).range =
      (g.cycleType.dedup.map
        fun n : ℕ => (g.cycleType.count n).factorial).prod := by
  rw [hφ_range_card', Equiv.Perm.of_partition_card]
  suffices hlc :
    ∀ n, Fintype.card {a : g.cycleFactorsFinset | fsc a = n} = g.cycleType.count ↑n
  suffices hl_lt : ∀ i ∈ g.cycleType, i < Fintype.card α + 1
  simp_rw [hlc]
  rw [← Finset.prod_range fun i => (g.cycleType.count i).factorial]
  rw [← Multiset.prod_toFinset]
  apply symm
  apply Finset.prod_subset_one_on_sdiff
  · intro i hi; rw [Finset.mem_range]; apply hl_lt
    simpa only [Multiset.mem_toFinset, Multiset.mem_dedup] using hi
  · intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_range, Multiset.mem_toFinset, Multiset.mem_dedup] at hi
    rw [Multiset.count_eq_zero_of_not_mem hi.2]
    exact Nat.factorial_zero
  · exact fun i _ ↦ rfl
  exact g.cycleType.nodup_dedup
  · intro i hi
    rw [Nat.lt_succ_iff]
    apply le_trans _ (Finset.card_le_univ g.support)
    apply Equiv.Perm.le_card_support_of_mem_cycleType
    exact hi
  · rintro ⟨i, hi⟩
    rw [Equiv.Perm.cycleType_def]
    simp only [Fin.val_mk]
    rw [← Set.ncard_filter_eq_count (Finset.card ∘ Equiv.Perm.support) g.cycleFactorsFinset i]
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Function.comp_apply]
    let u : {x : g.cycleFactorsFinset | fsc x = ⟨i, hi⟩} →
        {x ∈ g.cycleFactorsFinset | (Finset.card ∘ Equiv.Perm.support) x = i} :=
      fun ⟨⟨x, hx⟩, hx'⟩ => ⟨x, by
        simp only [fsc, Fin.mk.injEq, Set.mem_setOf_eq] at hx'
        simp only [Function.comp_apply, Set.mem_setOf_eq]
        exact ⟨hx, hx'⟩⟩
    have : Function.Bijective u := by
      constructor
      rintro ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ h
      simp only [Function.comp_apply, Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq] at h
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
      exact h
      rintro ⟨x, hx⟩
      simp only [Function.comp_apply, Set.mem_setOf_eq] at hx
      use! x
      exact hx.1
      simp only [fsc, Fin.mk.injEq, Set.mem_setOf_eq]
      exact hx.2
    rw [← Set.Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    apply Fintype.card_of_bijective this
#align on_cycle_factors.hφ_range_card OnCycleFactors.hφ_range_card

/-- A permutation `z : Equiv.Perm α` belongs to the kernel of `φ g` iff
  it commutes with each cycle of `g` -/
theorem hφ_mem_ker_iff (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈ (φ g).ker.map
      (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype  ↔
        ∀ t ∈ g.cycleFactorsFinset, Commute z t := by
  constructor
  · intro hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨⟨k, hkK⟩, hk, hk'⟩ := hz
    simp only [MonoidHom.mem_ker] at hk
    intro t ht
    change z * t = t * z
    rw [← mul_inv_eq_iff_eq_mul, ← MulAut.conj_apply, ← ConjAct.ofConjAct_toConjAct z,
      ← ConjAct.smul_eq_mulAut_conj _ t, ← hk']
    simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
    simp only [← φ_eq g k hkK t ht, hk]
    rfl
  · intro H
    rw [Subgroup.mem_map]
    use! ConjAct.toConjAct z
    · rw [MulAction.mem_stabilizer_iff]
      rw [ConjAct.smul_eq_mulAut_conj]
      rw [MulAut.conj_apply]
      rw [mul_inv_eq_iff_eq_mul]
      rw [ConjAct.ofConjAct_toConjAct]
      exact Equiv.Perm.commute_of_mem_cycleFactorsFinset_commute z g H
    simp only [MonoidHom.mem_ker]
    constructor
    · ext ⟨c, hc⟩
      rw [φ_eq']
      rw [H c hc]
      simp only [mul_inv_cancel_right, Equiv.Perm.coe_one, id.def, Subtype.coe_mk]
    · simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
#align on_cycle_factors.hφ_mem_ker_iff OnCycleFactors.hφ_mem_ker_iff
/-
/-- A general function used to describe the kernel of `OnCycleFactors.φ g` -/
def ψAux (s : Finset (Equiv.Perm α)) (hs : s ⊆ g.cycleFactorsFinset) :
    (Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g) ×
        ∀ c ∈ s, Subgroup.zpowers (c : Equiv.Perm α)) →
      Equiv.Perm α :=
  fun uv : Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g) ×
      ∀ c ∈ s, Subgroup.zpowers (c : Equiv.Perm α) =>
  Equiv.Perm.ofSubtype uv.fst *
    s.noncommProd (fun c => dite (c ∈ s) (fun hc => uv.snd c hc) fun hc => 1)
      fun c hc d hd h => by
        simp only [Finset.mem_coe] at hc hd
        simp [dif_pos hc, dif_pos hd]
        obtain ⟨m, hc'⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd c hc).prop
        obtain ⟨n, hd'⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd d hd).prop
        rw [← hc', ← hd']
        apply Commute.zpow_zpow
        exact g.cycleFactorsFinset_mem_commute (hs hc) (hs hd) h
#align on_cycle_factors.ψ_aux OnCycleFactors.ψAux -/

lemma _root_.Finset.noncommProd_eq_one
    {α : Type u_3} [DecidableEq α] {β : Type u_4} [Monoid β]
    (s : Finset α) (f : α → β)
    (comm : Set.Pairwise ↑s fun a b => Commute (f a) (f b))
    (hf : ∀ a ∈ s, f a = 1) :
    s.noncommProd f comm = 1 := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]
  | insert ha hs =>
      rw [Finset.noncommProd_insert_of_not_mem _ _ _ _ ha]
      rw [hf _ (Finset.mem_insert_self _ _), one_mul]
      apply hs
      intro a ha
      exact hf _ (Finset.mem_insert_of_mem ha)

lemma _root_.Equiv.Perm.cycleOf_ne_one_iff_mem (g : Equiv.Perm α) {x : α} :
    g.cycleOf x ≠ 1 ↔ g.cycleOf x ∈ g.cycleFactorsFinset := by
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.mem_support,
        ne_eq, Equiv.Perm.cycleOf_eq_one_iff]

def θAux (g : Equiv.Perm α) (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (x : α) : α :=
  if hx : g.cycleOf x ∈ g.cycleFactorsFinset
    then (v ⟨g.cycleOf x, hx⟩ : Equiv.Perm α) x
    else Equiv.Perm.ofSubtype k x

lemma θAux_apply_of_not_mem_cycleFactorsFinset {k} {v} {x}
    (hx : g.cycleOf x ∉ g.cycleFactorsFinset) :
    θAux g k v x = Equiv.Perm.ofSubtype k x := by
  rw [θAux, dif_neg hx]

lemma θAux_apply_of_mem_fixedPoints {k} {v} {x}
    (hx : x ∈ Function.fixedPoints g) :
    θAux g k v x = Equiv.Perm.ofSubtype k x := by
  rw [θAux, dif_neg]
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support]
  exact hx

lemma θAux_apply_of_mem_fixedPoints_mem {k} {v} {x}
    (hx : x ∈ Function.fixedPoints g) :
    θAux g k v x ∈ Function.fixedPoints g := by
  rw [θAux_apply_of_mem_fixedPoints hx, Equiv.Perm.ofSubtype_apply_of_mem k hx]
  exact (k _).prop

lemma θAux_apply_of_cycleOf_eq {k} {v} {x} (c : g.cycleFactorsFinset)
    (hx : g.cycleOf x = ↑c) : θAux g k v x = (v c : Equiv.Perm α) x := by
  suffices : c = ⟨g.cycleOf x, ?_⟩
  rw [this, θAux, dif_pos]
  rw [hx]; exact c.prop
  simp only [← Subtype.coe_inj, hx]

lemma θAux_apply_of_cycleOf_eq_mem {k} {v} {x} (c : g.cycleFactorsFinset)
    (hx : g.cycleOf x = ↑c) :
    g.cycleOf (θAux g k v x) = ↑c := by
  rw [θAux_apply_of_cycleOf_eq c hx]
  obtain ⟨m, hm⟩ := (v c).prop
  dsimp only at hm
  rw [← hm, ← hx]
  simp only [Equiv.Perm.cycleOf_zpow_apply_self, Equiv.Perm.cycleOf_self_apply_zpow]

lemma θAux_cycleOf_apply_eq {k} {v} {x} :
    g.cycleOf (θAux g k v x) = g.cycleOf x := by
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl]
    obtain ⟨m, hm⟩ := (v _).prop
    dsimp only at hm
    rw [← hm]
    simp only [Equiv.Perm.cycleOf_zpow_apply_self, Equiv.Perm.cycleOf_self_apply_zpow]
  · rw [g.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [g.cycleOf_eq_one_iff.mpr hx, g.cycleOf_eq_one_iff,
      ← Function.mem_fixedPoints_iff]
    apply θAux_apply_of_mem_fixedPoints_mem
    exact hx

lemma θAux_one (x : α) :
    θAux g 1 1 x = x := by
  unfold θAux
  split_ifs
  · simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
  · simp only [map_one, Equiv.Perm.coe_one, id_eq]

lemma θAux_mul
    (k' : Equiv.Perm (Function.fixedPoints g))
    (v' : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
    (x : α) :
    (θAux g k' v') (θAux g k v x) =
      θAux g (k' * k : Equiv.Perm (Function.fixedPoints g))
        (v' * v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) x := by
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ (θAux_apply_of_cycleOf_eq_mem ⟨_, hx⟩ rfl),
      θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl,
      θAux_apply_of_cycleOf_eq ⟨g.cycleOf x, hx⟩ rfl]
    · simp only [ne_eq, Pi.mul_apply, Submonoid.coe_mul,
        Subgroup.coe_toSubmonoid, Equiv.Perm.coe_mul, Function.comp_apply]
  · have hx' : g.cycleOf (θAux g k v x) ∉ g.cycleFactorsFinset
    · rw [θAux_cycleOf_apply_eq]
      exact hx
    nth_rewrite 1 [θAux, dif_neg hx']
    simp only [θAux, dif_neg hx]
    simp only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply]

lemma θAux_inv (k) (v) :
    Function.LeftInverse (θAux g k⁻¹ v⁻¹) (θAux g k v) := by
  intro x
  rw [θAux_mul]
  simp only [mul_left_inv, θAux_one]

def θFun (g : Equiv.Perm α)
    (k : Equiv.Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) :
    Equiv.Perm α := {
  toFun := θAux g k v
  invFun := θAux g k⁻¹ v⁻¹
  left_inv := θAux_inv k v
  right_inv := θAux_inv k⁻¹ v⁻¹ }

/-- The description of the kernel of `OnCycleFactors.φ g` -/
def θ (g : Equiv.Perm α) : Equiv.Perm (Function.fixedPoints g) ×
      ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) →*
        Equiv.Perm α := {
  toFun     := fun kv ↦ θFun g kv.fst kv.snd
  map_one'  := by
    ext x
    simp only [θFun, Prod.fst_one, Prod.snd_one, Equiv.Perm.coe_one, id_eq,
      inv_one, Equiv.coe_fn_mk, θAux_one]
  map_mul'  := fun kv' kv ↦ by
    ext x
    simp only [θFun, Equiv.coe_fn_mk, Prod.fst_mul, Prod.snd_mul,
      Equiv.Perm.coe_mul, Equiv.coe_fn_mk, Function.comp_apply, θAux_mul] }
#align on_cycle_factors.ψ OnCycleFactors.θ


      /-
def ψAux1 (g : Equiv.Perm α) :
    Equiv.Perm (Function.fixedPoints g) →* Equiv.Perm α :=
  Equiv.Perm.ofSubtype

lemma ψAux1_apply (g : Equiv.Perm α) (k) (x : α) :
    ψAux1 g k x =
      if hx : x ∈ Function.fixedPoints g then ↑(k ⟨x, hx⟩) else x := by
  classical
  rw [ψAux1]
  split_ifs with hx
  rw [Equiv.Perm.ofSubtype_apply_of_mem k]
  rw [Equiv.Perm.ofSubtype_apply_of_not_mem k hx]

def ψAux2 (g : Equiv.Perm α) :
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α))
      →* Equiv.Perm α := by
  apply Subgroup.noncommPiCoprod
  rintro ⟨c, hc⟩ ⟨d, hd⟩ h _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
  dsimp
  apply Commute.zpow_zpow
  apply g.cycleFactorsFinset_mem_commute hc hd
  simp only [ne_eq, Subtype.mk.injEq] at h
  exact h

lemma range_ψAux2_le_stabilizer_cycle (g : Equiv.Perm α) (c : g.cycleFactorsFinset) :
    MonoidHom.range (ψAux2 g) ≤
      MulAction.stabilizer (Equiv.Perm α) (c : Equiv.Perm α).support := by
  rw [ψAux2, Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod_range, iSup_le_iff]
  rintro ⟨d, hd⟩
  intro k
  rintro ⟨⟨k , ⟨m, rfl⟩⟩, rfl⟩
  dsimp
  apply Subgroup.zpow_mem
  simp only [MulAction.mem_stabilizer_iff]
  ext x
  simp only [Finset.mem_smul_finset, Equiv.Perm.smul_def]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← Equiv.Perm.mem_support_cycle_of_cycle c.prop hd]
    exact hy
  · intro hx
    use d⁻¹ x
    rw [Equiv.Perm.mem_support_cycle_of_cycle c.prop hd]
    simp only [Equiv.Perm.apply_inv_self, and_true]
    exact hx

lemma range_ψAux2_le_fixingSubgroup_fixedPoints (g : Equiv.Perm α) :
    MonoidHom.range (ψAux2 g) ≤
      fixingSubgroup (Equiv.Perm α) (Function.fixedPoints g) := by
  rw [ψAux2, Subgroup.noncommPiCoprod, MonoidHom.noncommPiCoprod_range,
    iSup_le_iff]
  rintro ⟨c, hc⟩
  simp only [Subgroup.coeSubtype, Subgroup.subtype_range, Subgroup.zpowers_le]
  simp only [mem_fixingSubgroup_iff]
  intro x
  simp only [Function.mem_fixedPoints, Function.IsFixedPt, Equiv.Perm.smul_def]
  simp only [← Equiv.Perm.not_mem_support, not_imp_not]
  intro hx
  exact Equiv.Perm.mem_cycleFactorsFinset_support_le hc hx

lemma ψAux2_apply (g : Equiv.Perm α) (x : α) (c : g.cycleFactorsFinset) (hx : x ∈ (c : Equiv.Perm α).support) (v) :
    ψAux2 g v x = (v c : Equiv.Perm α) x := by
  let H : Subgroup ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) := {
    carrier := { w | ∀ x, ψAux2 g w x = (w c : Equiv.Perm α) x}
    mul_mem' := fun v w ↦ by

      sorry
    one_mem' := sorry
    inv_mem' := sorry }
  suffices : ∀ (d : g.cycleFactorsFinset),
  revert v
  suffices hc : ∀ (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) (x), x ∈ (c : Equiv.Perm α).support ↔ (v c : Equiv.Perm α) x ∈ (c : Equiv.Perm α).support
  have : (v c : Equiv.Perm α) x = (v c : Equiv.Perm α).subtypePerm hc ⟨x, hx⟩
  · simp only [Equiv.Perm.subtypePerm_apply]
  rw [this]
  suffices hc' : ∀ x, x ∈ (c : Equiv.Perm α).support ↔ (ψAux2 g v) x ∈ (c : Equiv.Perm α).support
  have : (v )


  sorry

def ψAux1comm2 (g : Equiv.Perm α)
    (m : Equiv.Perm ↑(Function.fixedPoints ↑g))
    (n : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) :
    Commute (ψAux1 g m) (ψAux2 g n) := by
  apply Equiv.Perm.Disjoint.commute
  intro a
  by_cases ha : a ∈ g.support
  · left
    rw [ψAux1_apply, dif_neg]
    simp only [Equiv.Perm.mem_support, ne_eq] at ha
    simp only [Function.mem_fixedPoints, Function.IsFixedPt]
    exact ha
  · right
    suffices : ψAux2 g n ∈ fixingSubgroup (Equiv.Perm α) (Function.fixedPoints g)
    · simp only [mem_fixingSubgroup_iff, Equiv.Perm.smul_def] at this
      apply this
      simp only [Function.mem_fixedPoints, Function.IsFixedPt, ← Equiv.Perm.not_mem_support]
      exact ha
    · apply range_ψAux2_le_fixingSubgroup_fixedPoints g
      rw [MonoidHom.mem_range]
      exact ⟨n, rfl⟩

def ψAux' (g : Equiv.Perm α) :
    (Equiv.Perm (Function.fixedPoints g)) ×
      ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) →*
        Equiv.Perm α :=
  MonoidHom.noncommCoprod (ψAux1 g) (ψAux2 g) (ψAux1comm2 g)

variable (g)

def ψ' := ψAux g.cycleFactorsFinset (Finset.Subset.refl g.cycleFactorsFinset)

/-- The description of the kernel of `OnCycleFactors.φ g` -/
def ψ : (Equiv.Perm (Function.fixedPoints g)) ×
      ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) →*
        Equiv.Perm α :=
  MonoidHom.noncommCoprod (ψAux1 g) (ψAux2 g) (ψAux1comm2 g) -/


theorem hθ_1 (uv) (x : α) (hx : x ∈ Function.fixedPoints g) :
    θ g uv x = uv.fst ⟨x, hx⟩ := by
  unfold θ; unfold θFun
  simp only [Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
  rw [θAux_apply_of_mem_fixedPoints, Equiv.Perm.ofSubtype_apply_of_mem]
  exact hx

/-
theorem hψ_1 (uv) (x : α) (hx : x ∈ MulAction.fixedBy _ α g) :
    ψ' g uv x = uv.fst ⟨x, hx⟩ := by
  simp only [ψ, ψAux, Equiv.Perm.mul_apply]

  rw [← Equiv.Perm.ofSubtype_apply_coe]
  apply congr_arg
  simp only [Subtype.coe_mk, ← Equiv.Perm.smul_def]
  rw [← MulAction.mem_stabilizer_iff]
  apply Subgroup.noncommProd_mem
  intro c hc
  obtain ⟨m, hm⟩ := (uv.snd c hc).prop
  simp only [dif_pos hc, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
    ← Equiv.Perm.not_mem_support, ← hm]
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def, ← Equiv.Perm.not_mem_support] at hx
  intro hx'
  apply hx
  apply Equiv.Perm.mem_cycleFactorsFinset_support_le hc
  apply Equiv.Perm.support_zpow_le c m
  exact hx'
#align on_cycle_factors.hψ_1 OnCycleFactors.hψ_1 -/

theorem hθ_2 (uv) (x : α) (c : g.cycleFactorsFinset)  (hx :g.cycleOf x = ↑c) :
    θ g uv x = (uv.snd c : Equiv.Perm α) x := by
  unfold θ; unfold θFun
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
  exact θAux_apply_of_cycleOf_eq c hx

theorem hθ_single (c : g.cycleFactorsFinset) :
    θ g ⟨1, (Pi.mulSingle c ⟨c, Subgroup.mem_zpowers (c : Equiv.Perm α)⟩)⟩ = c  := by
  ext x
  by_cases hx : x ∈ Function.fixedPoints g
  · simp only [hθ_1 _ x hx, Equiv.Perm.coe_one, id_eq]
    apply symm
    rw [← Equiv.Perm.not_mem_support]
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, ← Equiv.Perm.not_mem_support] at hx
    intro hx'
    apply hx
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hx'
  suffices hx' : g.cycleOf x ∈ g.cycleFactorsFinset
  rw [hθ_2 _ x ⟨g.cycleOf x, hx'⟩ rfl]
  dsimp only
  by_cases hc : c = ⟨Equiv.Perm.cycleOf g x, hx'⟩
  · rw [hc, Pi.mulSingle_eq_same, Equiv.Perm.cycleOf_apply_self]
  · rw [Pi.mulSingle_eq_of_ne' hc]
    simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
    apply symm
    rw [← Equiv.Perm.not_mem_support]
    intro hxc
    apply hc
    rw [← Subtype.coe_inj]
    dsimp only
    apply Equiv.Perm.cycle_is_cycleOf hxc c.prop
  rw [← Equiv.Perm.cycleOf_ne_one_iff_mem]
  simp only [ne_eq, Equiv.Perm.cycleOf_eq_one_iff]
  rw [Function.mem_fixedPoints_iff] at hx
  exact hx

/-
theorem hψ_2 (uv) (x : α) (c : Equiv.Perm α) (hc : c ∈ g.cycleFactorsFinset)
    (hx : c = g.cycleOf x) :
    ψ g uv x = (uv.snd c hc : Equiv.Perm α) x := by
  revert uv x c hc hx
  suffices : ∀ (s : Finset (Equiv.Perm α)) (hs : s ⊆ g.cycleFactorsFinset) (uvs)
    (x : α) (c : Equiv.Perm α) (_ : c ∈ g.cycleFactorsFinset) (_ : c = g.cycleOf x),
      ψAux s hs uvs x = if hc : c ∈ s then (uvs.snd c hc : Equiv.Perm α) x else x
  intro uv x c hc hx
  rw [ψ, this g.cycleFactorsFinset Finset.Subset.rfl uv x c hc hx, dif_pos hc]
  intro s
  induction' s using Finset.induction with d s hds ih
  · intro hs uv x c hc hx
    rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc
    simp only [ψAux, Finset.not_mem_empty, not_false_eq_true, dif_neg, Finset.noncommProd_empty, mul_one]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
    rw [← Ne.def, ← g.isCycle_cycleOf_iff, ← hx]
    exact hc.1
  · rintro hs ⟨u, v⟩ x c hc hx
    have fixes_of_ne : ∀ d ∈ g.cycleFactorsFinset, ∀ (k : Subgroup.zpowers d) (_ : c ≠ d),
      (k : Equiv.Perm α) x = x := by
      intro d hd k h
      obtain ⟨m, hm⟩ := k.prop
      rw [← hm]; rw [← Equiv.Perm.smul_def]; rw [← MulAction.mem_stabilizer_iff]
      apply Subgroup.zpow_mem
      rw [MulAction.mem_stabilizer_iff]; rw [Equiv.Perm.smul_def]
      apply Or.resolve_left
        (Equiv.Perm.disjoint_iff_eq_or_eq.mp (g.cycleFactorsFinset_pairwise_disjoint hc hd h) x)
      rw [← Ne.def]
      rw [← Equiv.Perm.mem_support]
      rw [hx]
      rw [Equiv.Perm.mem_support_cycleOf_iff]
      constructor
      exact Equiv.Perm.SameCycle.refl g x
      rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
      rw [← hx]; exact hc
    simp only [ψAux]
    rw [Finset.noncommProd_insert_of_not_mem' _ _ _ _ hds]
    simp only [dif_pos (Finset.mem_insert_self d s)]
    rw [← mul_assoc]
    rw [Equiv.Perm.mul_apply]
    suffices : ∀ x ∈ s,
      (if h : x ∈ insert d s then (v x h : Equiv.Perm α) else 1) =
        if h : x ∈ s then (v x (Finset.mem_insert_of_mem h) : Equiv.Perm α) else 1
    rw [Finset.noncommProd_congr rfl this]
    specialize
      ih (subset_trans (Finset.subset_insert d s) hs)
        ⟨u, fun x h => v x (Finset.mem_insert_of_mem h)⟩
        ((v d (Finset.mem_insert_self d s) : Equiv.Perm α) x) c hc
    simp only [ψAux] at ih
    rw [ih _]
    by_cases hcs : c ∈ s
    · simp only [dif_pos hcs, dif_pos (Finset.mem_insert_of_mem hcs)]
      apply congr_arg
      apply fixes_of_ne
      exact hs (Finset.mem_insert_self d s)
      -- c ≠ d
      intro h;
      apply hds; rw [← h]; exact hcs
    · -- by_cases : c ∉ s
      simp only [dif_neg hcs]
      by_cases hcd : c = d
      · rw [hcd]; simp only [dif_pos (Finset.mem_insert_self d s)]
      rw [dif_neg]
      apply fixes_of_ne
      exact hs (Finset.mem_insert_self d s)
      exact hcd
      -- c ∉ insert d s
      intro h;
      rw [Finset.mem_insert] at h
      cases' h with h h
      exact hcd h
      exact hcs h
    · -- c = g.cycle_of ((v d _) x)
      by_cases h : c = d
      · obtain ⟨m, hm⟩ := (v d (Finset.mem_insert_self d s)).prop
        rw [← hm]
        rw [← h]
        rw [hx]; rw [Equiv.Perm.cycleOf_zpow_apply_self]
        rw [Equiv.Perm.cycleOf_self_apply_zpow]
      rw [fixes_of_ne]
      exact hx
      exact hs (Finset.mem_insert_self d s)
      exact h
    · -- ∀ …
      intro k hks
      simp only [dif_pos hks, dif_pos (Finset.mem_insert_of_mem hks)]
#align on_cycle_factors.hψ_2 OnCycleFactors.hψ_2
 -/
-- variable (g)

/- theorem hψ_inj : Function.Injective (ψ g) := by
  intro uv uv' h
  rw [Prod.ext_iff]; constructor
  · ext ⟨x, hx⟩; rw [← hψ_1 uv x hx]; rw [← hψ_1 uv' x hx]; rw [h]
  · ext c hc x
    by_cases hx : c = g.cycleOf x
    · rw [← hψ_2 uv x c hc hx]; rw [← hψ_2 uv' x c hc hx]; rw [h]
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (uv.snd c hc).prop
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (uv'.snd c hc).prop
      rw [← hm]; rw [← hn]
      suffices ∀ n : ℤ, (c ^ n) x = x by rw [this n]; rw [this m]
      suffices c x = x by
        change c • x = x at this
        rw [← MulAction.mem_stabilizer_iff] at this
        intro n
        change c ^ n • x = x
        rw [← MulAction.mem_stabilizer_iff]
        apply Subgroup.zpow_mem _ this
      · rw [← Equiv.Perm.not_mem_support]; intro hx'
        apply hx; exact Equiv.Perm.cycle_is_cycleOf hx' hc
#align on_cycle_factors.hψ_inj OnCycleFactors.hψ_inj
 -/


theorem hθ_injective (g : Equiv.Perm α) : Function.Injective (θ g) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨u, v⟩
  unfold θ; unfold θFun
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mem_ker, Equiv.Perm.ext_iff]
  simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_one, id_eq]
  intro huv
  simp only [Subgroup.mem_bot, Prod.mk_eq_one, MonoidHom.mem_ker]
  constructor
  · ext ⟨x, hx⟩
    simp only [Equiv.Perm.coe_one, id_eq]
    conv_rhs => rw [← huv x]
    rw [θAux_apply_of_mem_fixedPoints, Equiv.Perm.ofSubtype_apply_of_mem]
    exact hx
  · ext c x
    by_cases hx : g.cycleOf x = 1
    · simp only [Equiv.Perm.cycleOf_eq_one_iff, ← Equiv.Perm.not_mem_support] at hx
      simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      obtain ⟨m, hm⟩ := (v c).prop
      rw [← hm]
      dsimp
      rw [← Equiv.Perm.not_mem_support]
      intro hx'
      suffices : ¬ x ∈ Equiv.Perm.support c
      apply this
      apply Equiv.Perm.support_zpow_le _ _ hx'
      intro hx'
      apply hx
      apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hx'
    · rw [← ne_eq, Equiv.Perm.cycleOf_ne_one_iff_mem] at hx
      simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      by_cases hc : g.cycleOf x = ↑c
      · rw [← θAux_apply_of_cycleOf_eq c hc, huv]
      · obtain ⟨m, hm⟩ := (v c).prop
        rw [← hm]
        dsimp
        rw [← Equiv.Perm.not_mem_support]
        intro hx'
        suffices : ¬ x ∈ Equiv.Perm.support c
        apply this
        apply Equiv.Perm.support_zpow_le _ _ hx'
        intro h
        exact hc (Equiv.Perm.cycle_is_cycleOf h c.prop).symm
-- #align on_cycle_factors.hψ_inj OnCycleFactors.hψ_inj


-- #align on_cycle_factors.hψ_inj OnCycleFactors.hψ_inj

/- theorem hφ_ker_eq_ψ_range (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈
        Subgroup.map (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype (φ g).ker ↔
      z ∈ Set.range (ψ g) := by
  rw [hφ_mem_ker_iff, Equiv.Perm.IsCycle.forall_commute_iff, Set.mem_range]
  constructor
  · intro Hz
    have hu : ∀ x : α,
      x ∈ MulAction.fixedBy (Equiv.Perm α) α g ↔
        z x ∈ MulAction.fixedBy (Equiv.Perm α) α g :=  by
      intro x
      simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def]
      simp only [← Equiv.Perm.not_mem_support]
      rw [not_iff_not]
      constructor
      · intro hx
        let hx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf x)
          (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx)
        rw [← Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hx⟩
      · intro hzx
        let hzx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hzx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hzx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf (z x)) hzx'
        rw [Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hzx⟩
    let u := Equiv.Perm.subtypePerm z hu
    let v : ∀ c : Equiv.Perm α, c ∈ g.cycleFactorsFinset → (Subgroup.zpowers c) := fun c hc =>
      ⟨Equiv.Perm.ofSubtype (z.subtypePerm (Classical.choose (Hz c hc))),
        Classical.choose_spec (Hz c hc)⟩
    use ⟨u, v⟩
    ext x
    by_cases hx : x ∈ g.support
    · rw [hψ_2 ⟨u, v⟩ x (g.cycleOf x) _ rfl]
      simp only [Subgroup.coe_mk]
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
      rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]; exact hx
      rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]; exact hx
    · rw [Equiv.Perm.not_mem_support, ← Equiv.Perm.smul_def, ← MulAction.mem_fixedBy] at hx
      rw [hψ_1 ⟨u, v⟩ x hx]
      simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
  · rintro ⟨⟨u, v⟩, h⟩
    intro c hc
    suffices hs' : ∀ x : α, x ∈ c.support ↔ z x ∈ c.support
    use hs'
    suffices : Equiv.Perm.ofSubtype (z.subtypePerm hs') = v c hc
    rw [this]; apply SetLike.coe_mem
    · ext x
      by_cases hx : x ∈ c.support
      · rw [Equiv.Perm.ofSubtype_apply_of_mem]
        simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
        rw [← h]
        rw [hψ_2 ⟨u, v⟩ x]
        exact Equiv.Perm.cycle_is_cycleOf hx hc
        exact hx
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
        apply symm; rw [← Equiv.Perm.not_mem_support]
        obtain ⟨m, hm⟩ := (v c hc).prop
        rw [← hm]
        intro hx'; apply hx
        exact Equiv.Perm.support_zpow_le c m hx'
        exact hx
    · intro x
      suffices :
        ∀ d ∈ g.cycleFactorsFinset, x ∈ d.support → z x ∈ d.support
      constructor
      exact this c hc
      · intro hzx
        by_cases hx : x ∈ g.support
        · have hx'' : x ∈ (g.cycleOf x).support := by
            rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]
            exact hx
          have hc' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
          suffices : c = g.cycleOf x; rw [this]; exact hx''
          specialize this (g.cycleOf x) hc' hx''
          by_contra h
          simp only [Equiv.Perm.mem_support] at this hzx
          cases' Equiv.Perm.disjoint_iff_eq_or_eq.mp
            (g.cycleFactorsFinset_pairwise_disjoint hc hc' h) (z x) with h1 h2
          exact hzx h1
          exact this h2
        · exfalso
          -- let hzx' := Equiv.Perm.mem_cycleFactorsFinset_support_le hc hzx
          apply Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hc hzx)
          simp only [Equiv.Perm.not_mem_support, ← Equiv.Perm.smul_def,
            ← MulAction.mem_fixedBy] at hx
          simp only [← Equiv.Perm.smul_def, ← MulAction.mem_fixedBy]
          rw [← h, Equiv.Perm.smul_def, hψ_1 ⟨u, v⟩ x hx]
          apply Subtype.mem
      · intro d hd
        simp only [Equiv.Perm.mem_support]
        intro hx
        rw [← h, hψ_2 ⟨u, v⟩ x d hd]
        obtain ⟨m, hm⟩ := (v d hd).prop
        rw [← hm, ← Equiv.Perm.mul_apply, Commute.self_zpow d m, Equiv.Perm.mul_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq]
        exact hx
        rw [← Equiv.Perm.mem_support] at hx
        exact Equiv.Perm.cycle_is_cycleOf hx hd
#align on_cycle_factors.hφ_ker_eq_ψ_range OnCycleFactors.hφ_ker_eq_ψ_range
 -/

theorem hφ_ker_eq_θ_range (z : Equiv.Perm α) :
    ConjAct.toConjAct z ∈
        Subgroup.map (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype (φ g).ker ↔
      z ∈ Set.range (θ g) := by
  constructor
  · rw [hφ_mem_ker_iff, Equiv.Perm.IsCycle.forall_commute_iff, Set.mem_range]
    intro Hz
    have hu : ∀ x : α,
      x ∈ Function.fixedPoints g ↔
        z x ∈ Function.fixedPoints g :=  by
      intro x
      simp only [Function.fixedPoints, Equiv.Perm.smul_def, Function.IsFixedPt]
      simp only [← Equiv.Perm.not_mem_support]
      simp only [Set.mem_setOf_eq, not_iff_not]
      constructor
      · intro hx
        let hx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf x)
          (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx)
        rw [← Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hx⟩
      · intro hzx
        let hzx' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hzx
        apply Equiv.Perm.mem_cycleFactorsFinset_support_le hzx'
        obtain ⟨Hz'⟩ := Hz (g.cycleOf (z x)) hzx'
        rw [Hz' x, Equiv.Perm.mem_support_cycleOf_iff]
        exact ⟨Equiv.Perm.SameCycle.refl _ _, hzx⟩
    let u := Equiv.Perm.subtypePerm z hu
    let v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers (c : Equiv.Perm α)) :=
      fun c => ⟨Equiv.Perm.ofSubtype
          (z.subtypePerm (Classical.choose (Hz c.val c.prop))),
            Classical.choose_spec (Hz c.val c.prop)⟩
    use ⟨u, v⟩
    ext x
    by_cases hx : g.cycleOf x = 1
    · rw [hθ_1 _ x]
      simp only [Equiv.Perm.subtypePerm_apply]
      simp only [Equiv.Perm.cycleOf_eq_one_iff] at hx
      exact hx
    · rw [hθ_2 _ x ⟨g.cycleOf x, (Equiv.Perm.cycleOf_ne_one_iff_mem g).mp hx⟩ rfl]
      change (v _ : Equiv.Perm α) x = _
      rw [Equiv.Perm.ofSubtype_apply_of_mem]
      rfl
      simp only [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ne_eq]
      simp only [Equiv.Perm.cycleOf_eq_one_iff] at hx
      exact hx

  · rintro ⟨⟨u, v⟩, h⟩
    rw [hφ_mem_ker_iff]

    rw [Equiv.Perm.IsCycle.forall_commute_iff]
    intro c hc
    suffices hc' : _
    use hc'
    suffices : Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm z hc') = v ⟨c, hc⟩
    rw [this]
    exact (v _).prop
    ext x
    by_cases hx : x ∈ c.support
    · rw [Equiv.Perm.ofSubtype_apply_of_mem, Equiv.Perm.subtypePerm_apply]
      dsimp
      rw [← h, hθ_2 _ x ⟨c, hc⟩]
      exact (Equiv.Perm.cycle_is_cycleOf hx hc).symm
      exact hx
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
      obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
      dsimp only at hm
      rw [← hm]
      apply symm
      rw [← Equiv.Perm.not_mem_support]
      intro hx'
      apply hx
      exact (Equiv.Perm.support_zpow_le c m) hx'
      exact hx
    · intro x
      simp only [← Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff g c hc]
      rw [← h]
      unfold θ; unfold θFun
      dsimp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk]
      rw [θAux_cycleOf_apply_eq]
/-
    -- previous
    intro c hc
    rw [← h]
    ext x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    by_cases hx : x ∈ Function.fixedPoints g
    · suffices hx' : ∀ x ∈ Function.fixedPoints g, (c : Equiv.Perm α) x = x
      rw [hx' x hx, hθ_1 g _ x hx, hx']
      dsimp only
      exact (u _).prop
      · simp [Function.mem_fixedPoints, Function.IsFixedPt]
        intro x
        simp only [← Equiv.Perm.not_mem_support, not_imp_not]
        exact fun hx ↦ Equiv.Perm.mem_cycleFactorsFinset_support_le hc hx
    · suffices hx' : _
      suffices hx'' : _
      rw [hθ_2 g _ x ⟨g.cycleOf x, hx'⟩ rfl]
      rw [hθ_2 g _ _ ⟨g.cycleOf _, hx''⟩ rfl]
      dsimp only
      by_cases hc : c = g.cycleOf x




    intro c hc
    suffices hs' : ∀ x : α, x ∈ c.support ↔ z x ∈ c.support
    use hs'
    suffices : Equiv.Perm.ofSubtype (z.subtypePerm hs') = v ⟨c, hc⟩
    rw [this]; apply SetLike.coe_mem
    · ext x
      by_cases hx : x ∈ c.support
      · rw [Equiv.Perm.ofSubtype_apply_of_mem]
        simp only [Subtype.coe_mk, Equiv.Perm.subtypePerm_apply]
        rw [← h]
        rw [hθ_2 ⟨u, v⟩ x]
        exact Equiv.Perm.cycle_is_cycleOf hx hc
        exact hx
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
        apply symm; rw [← Equiv.Perm.not_mem_support]
        obtain ⟨m, hm⟩ := (v c hc).prop
        rw [← hm]
        intro hx'; apply hx
        exact Equiv.Perm.support_zpow_le c m hx'
        exact hx
    · intro x
      suffices :
        ∀ d ∈ g.cycleFactorsFinset, x ∈ d.support → z x ∈ d.support
      constructor
      exact this c hc
      · intro hzx
        by_cases hx : x ∈ g.support
        · have hx'' : x ∈ (g.cycleOf x).support := by
            rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]
            exact hx
          have hc' := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx
          suffices : c = g.cycleOf x; rw [this]; exact hx''
          specialize this (g.cycleOf x) hc' hx''
          by_contra h
          simp only [Equiv.Perm.mem_support] at this hzx
          cases' Equiv.Perm.disjoint_iff_eq_or_eq.mp
            (g.cycleFactorsFinset_pairwise_disjoint hc hc' h) (z x) with h1 h2
          exact hzx h1
          exact this h2
        · exfalso
          -- let hzx' := Equiv.Perm.mem_cycleFactorsFinset_support_le hc hzx
          apply Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hc hzx)
          simp only [Equiv.Perm.not_mem_support, ← Equiv.Perm.smul_def,
            ← MulAction.mem_fixedBy] at hx
          simp only [← Equiv.Perm.smul_def, ← MulAction.mem_fixedBy]
          rw [← h, Equiv.Perm.smul_def, hψ_1 ⟨u, v⟩ x hx]
          apply Subtype.mem
      · intro d hd
        simp only [Equiv.Perm.mem_support]
        intro hx
        rw [← h, hψ_2 ⟨u, v⟩ x d hd]
        obtain ⟨m, hm⟩ := (v d hd).prop
        rw [← hm, ← Equiv.Perm.mul_apply, Commute.self_zpow d m, Equiv.Perm.mul_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq]
        exact hx
        rw [← Equiv.Perm.mem_support] at hx
        exact Equiv.Perm.cycle_is_cycleOf hx hd -/
#align on_cycle_factors.hφ_ker_eq_ψ_range OnCycleFactors.hφ_ker_eq_θ_range

theorem hψ_range_card' (g : Equiv.Perm α) :
    Fintype.card (Set.range (θ g)) = Fintype.card (φ g).ker := by
  classical
  let u : (Set.range (θ g)) → (φ g).ker := fun ⟨z, hz⟩ => by
    rw [← hφ_ker_eq_θ_range] at hz
    suffices : ConjAct.toConjAct z ∈ MulAction.stabilizer (ConjAct (Equiv.Perm α)) g
    use ⟨ConjAct.toConjAct z, this⟩
    have hK : Function.Injective (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype
    apply Subgroup.subtype_injective
    rw [← Subgroup.mem_map_iff_mem hK]
    simp only [Subgroup.coeSubtype, Subgroup.coe_mk]
    exact hz
    · obtain ⟨u, ⟨_, hu'⟩⟩ := hz
      rw [← hu']
      exact u.prop
  suffices : Function.Bijective u
  exact Fintype.card_of_bijective this
  constructor
  · -- injectivity
    rintro ⟨z, hz⟩ ⟨w, hw⟩ hzw
    simpa only [Subtype.mk_eq_mk, MulEquiv.apply_eq_iff_eq] using hzw
  · -- surjectivity
    rintro ⟨w, hw⟩
    use! ConjAct.ofConjAct ((MulAction.stabilizer (ConjAct (Equiv.Perm α)) g).subtype w)
    rw [← hφ_ker_eq_θ_range]
    simp only [Subgroup.coeSubtype, ConjAct.toConjAct_ofConjAct, Subgroup.mem_map,
      SetLike.coe_eq_coe, exists_prop, exists_eq_right, hw]
    simp only [Subgroup.coeSubtype, ConjAct.toConjAct_ofConjAct, Subtype.mk_eq_mk, SetLike.eta]
#align on_cycle_factors.hψ_range_card' OnCycleFactors.hψ_range_card'

theorem Equiv.Perm.card_fixedBy (g : Equiv.Perm α) :
    Fintype.card (MulAction.fixedBy (Equiv.Perm α) α g) =
      Fintype.card α - g.cycleType.sum := by
  rw [Equiv.Perm.sum_cycleType, ← Finset.card_compl]
  simp only [Fintype.card_ofFinset, Set.mem_compl_iff, Finset.mem_coe,
    Equiv.Perm.mem_support, Classical.not_not]
  apply congr_arg
  ext x
  simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def, Finset.mem_filter, Finset.mem_univ,
    true_and_iff, Finset.mem_compl, Equiv.Perm.mem_support, Classical.not_not]
#align on_cycle_factors.equiv.perm.card_fixed_by OnCycleFactors.Equiv.Perm.card_fixedBy

theorem Fintype.card_pfun (p : Prop) [Decidable p] (β : p → Type _) [∀ hp, Fintype (β hp)] :
    Fintype.card (∀ hp : p, β hp) = if h : p then Fintype.card (β h) else 1 := by
  by_cases hp : p
  · simp only [dif_pos hp]
    rw [Fintype.card_eq]
    apply Nonempty.intro
    refine' Equiv.piSubsingleton (fun a' : p => β a') hp
  · simp only [dif_neg hp]
    rw [Fintype.card_eq_one_iff]
    use (fun h => False.elim (hp h))
    intro u; ext h; exfalso; exact hp h
#align on_cycle_factors.fintype.card_pfun OnCycleFactors.Fintype.card_pfun

theorem hψ_range_card (g : Equiv.Perm α) :
    Fintype.card (Set.range (θ g)) =
      (Fintype.card α - g.cycleType.sum).factorial * g.cycleType.prod := by
  rw [Set.card_range_of_injective (hθ_injective g)]
  rw [Fintype.card_prod]
  rw [Fintype.card_perm]
  rw [Fintype.card_pi]
  apply congr_arg₂ (· * ·)
  · -- fixed points
    apply congr_arg
    exact Equiv.Perm.card_fixedBy g
  · rw [Equiv.Perm.cycleType]
    simp only [Finset.univ_eq_attach, Finset.attach_val, Function.comp_apply]
    rw [Finset.prod_attach (s := g.cycleFactorsFinset) (f := fun a ↦ Fintype.card (Subgroup.zpowers (a : Equiv.Perm α)))]
    rw [Finset.prod]
    apply congr_arg
    apply Multiset.map_congr rfl
    intro x hx
    rw [← orderOf_eq_card_zpowers, Equiv.Perm.IsCycle.orderOf]
    simp only [Finset.mem_val, Equiv.Perm.mem_cycleFactorsFinset_iff] at hx
    exact hx.left
#align on_cycle_factors.hψ_range_card OnCycleFactors.hψ_range_card

-- Should one parenthesize the product ?
/-- Cardinality of a centralizer in `equiv.perm α` of a given `cycle_type` -/
theorem Equiv.Perm.conj_stabilizer_card (g : Equiv.Perm α) :
    Fintype.card (MulAction.stabilizer (ConjAct (Equiv.Perm α)) g) =
      (Fintype.card α - g.cycleType.sum).factorial * g.cycleType.prod *
        (g.cycleType.dedup.map
          fun n : ℕ => (g.cycleType.count n).factorial).prod := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (φ g).ker]
  rw [Fintype.card_congr (QuotientGroup.quotientKerEquivRange (φ g)).toEquiv]
  rw [← Nat.card_eq_fintype_card, hφ_range_card]
  rw [mul_comm]
  apply congr_arg₂ (· * ·) _ rfl
  rw [← hψ_range_card]
  rw [hψ_range_card']
#align on_cycle_factors.equiv.perm.conj_stabilizer_card OnCycleFactors.Equiv.Perm.conj_stabilizer_card

theorem Group.conj_class_eq_conj_orbit {G : Type _} [Group G] (g : G) :
    {k : G | IsConj g k} = MulAction.orbit (ConjAct G) g := by
  ext k
  simp only [Set.mem_setOf_eq, isConj_iff, MulAction.mem_orbit_iff, ConjAct.smul_def]
  constructor
  rintro ⟨c, hc⟩
  use ConjAct.toConjAct c; simp only [hc, ConjAct.ofConjAct_toConjAct]
  rintro ⟨x, hx⟩
  use ConjAct.ofConjAct x
#align on_cycle_factors.group.conj_class_eq_conj_orbit OnCycleFactors.Group.conj_class_eq_conj_orbit

theorem Equiv.Perm.conj_class_card_mul_eq (g : Equiv.Perm α) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} *
      (Fintype.card α - g.cycleType.sum).factorial *
      g.cycleType.prod *
      (g.cycleType.dedup.map
        fun n : ℕ => (g.cycleType.count n).factorial).prod =
    (Fintype.card α).factorial := by
  classical
  simp_rw [Group.conj_class_eq_conj_orbit g]
  simp only [mul_assoc]
  rw [mul_comm]
  simp only [← mul_assoc]
  rw [← Equiv.Perm.conj_stabilizer_card g]
  rw [mul_comm]
  rw [MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Equiv.Perm α)) g]
  rw [ConjAct.card, Fintype.card_perm]
#align on_cycle_factors.equiv.perm.conj_class_card_mul_eq OnCycleFactors.Equiv.Perm.conj_class_card_mul_eq

theorem Multiset.prod_pos {R : Type _} [StrictOrderedCommSemiring R] [Nontrivial R] (m : Multiset R)
    (h : ∀ a ∈ m, (0 : R) < a) : 0 < m.prod :=
  by
  induction' m using Multiset.induction with a m ih
  · simp
  · rw [Multiset.prod_cons]
    exact
      mul_pos (h _ <| Multiset.mem_cons_self _ _)
        (ih fun a ha => h a <| Multiset.mem_cons_of_mem ha)
#align on_cycle_factors.multiset.prod_pos OnCycleFactors.Multiset.prod_pos

/-- Cardinality of a conjugacy class in `Equiv.Perm α` of a given `cycleType` -/
theorem Equiv.Perm.conj_class_card (g : Equiv.Perm α) :
    Fintype.card {h : Equiv.Perm α | IsConj g h} =
      (Fintype.card α).factorial /
        ((Fintype.card α - g.cycleType.sum).factorial *
          g.cycleType.prod *
          (g.cycleType.dedup.map
            fun n : ℕ => (g.cycleType.count n).factorial).prod) := by
  rw [← Equiv.Perm.conj_class_card_mul_eq g]
  rw [Nat.div_eq_of_eq_mul_left _]
  simp only [← mul_assoc]
  -- This is the cardinal of the centralizer
  rw [← Equiv.Perm.conj_stabilizer_card g]
  refine' Fintype.card_pos
#align on_cycle_factors.equiv.perm.conj_class_card OnCycleFactors.Equiv.Perm.conj_class_card

variable (α)

theorem Equiv.Perm.card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card *
        ((Fintype.card α - m.sum).factorial * m.prod *
          (m.dedup.map fun n : ℕ => (m.count n).factorial).prod) =
      ite (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) (Fintype.card α).factorial 0 := by
  split_ifs with hm
  · -- nonempty case
    obtain ⟨g, hg⟩ := Equiv.permWithCycleType_nonempty_iff.mpr hm
    suffices :
      (Finset.univ.filter fun h : Equiv.Perm α => h.cycleType = m) =
        Finset.univ.filter fun h : Equiv.Perm α => IsConj g h
    rw [this]
    rw [← Fintype.card_coe]
    simp only [Equiv.permWithCycleType, Finset.mem_filter] at hg
    rw [← Equiv.Perm.conj_class_card_mul_eq g]
    simp only [Fintype.card_coe, ← Set.toFinset_card, mul_assoc]
    apply congr_arg₂ _
    · apply congr_arg
      ext σ
      simp only [isConj_iff, Finset.mem_univ, forall_true_left, Finset.univ_filter_exists,
        Finset.mem_image, true_and, Set.toFinset_setOf]
    rw [hg.2]
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, Set.mem_toFinset, Set.mem_setOf_eq]
    rw [isConj_comm]; rw [Equiv.Perm.isConj_iff_cycleType_eq]
    simp only [Equiv.permWithCycleType, Finset.mem_filter] at hg
    rw [hg.2]
  · convert MulZeroClass.zero_mul _
    rw [Finset.card_eq_zero]
    rw [← Finset.isEmpty_coe_sort]
    rw [← not_nonempty_iff]
    intro h; apply hm
    simp only [Finset.nonempty_coe_sort] at h
    rw [← Equiv.permWithCycleType_nonempty_iff]
    exact h
#align on_cycle_factors.equiv.perm.card_of_cycle_type_mul_eq
  OnCycleFactors.Equiv.Perm.card_of_cycleType_mul_eq

/-- Cardinality of the set of `equiv.perm α` of given `cycle_type` -/
theorem Equiv.Perm.card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : Equiv.Perm α => g.cycleType = m).card =
      if m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α).factorial /
          ((Fintype.card α - m.sum).factorial * m.prod *
            (m.dedup.map fun n : ℕ => (m.count n).factorial).prod)
      else 0 := by
  split_ifs with hm
  · -- nonempty case
    obtain ⟨g, hg⟩ := Equiv.permWithCycleType_nonempty_iff.mpr hm
    simp only [Equiv.permWithCycleType, Finset.mem_filter] at hg
    -- rw [← Equiv.Perm.card_of_cycleType_mul_eq m]
    rw [← Equiv.Perm.conj_class_card_mul_eq g]
    simp only [mul_assoc]
    simp only [Fintype.card_coe, ← Set.toFinset_card, mul_assoc]
    rw [Nat.div_eq_of_eq_mul_left _]
    apply congr_arg₂
    · apply congr_arg
      ext h
      simp only [Set.toFinset_setOf, Finset.mem_univ, forall_true_left,
        Finset.univ_filter_exists, Finset.mem_image, true_and, Finset.mem_filter]
      rw [isConj_comm, Equiv.Perm.isConj_iff_cycleType_eq, hg.2]
    rw [hg.2]
    · apply Nat.mul_pos
      exact Nat.factorial_pos (Fintype.card α - Multiset.sum m)
      apply Nat.mul_pos
      · apply Multiset.prod_pos
        intro a ha
        exact lt_of_lt_of_le (by norm_num) (hm.2 a ha)
      · apply Multiset.prod_pos
        intro a
        rw [Multiset.mem_map]
        rintro ⟨b, _, rfl⟩
        apply Nat.factorial_pos
  · rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
    rw [← Equiv.permWithCycleType_nonempty_iff] at hm
    exact hm
#align on_cycle_factors.equiv.perm.card_of_cycle_type OnCycleFactors.Equiv.Perm.card_of_cycleType

theorem AlternatingGroup.of_cycleType_eq (m : Multiset ℕ) :
    Finset.map ⟨Subgroup.subtype (alternatingGroup α), Subgroup.subtype_injective _⟩
        (Finset.univ.filter fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m) =
      if Even (m.sum + Multiset.card m)
        then Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m
        else ∅ := by
  split_ifs with hm
  · ext g
    -- split,
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · intro hg; rw [Finset.mem_map] at hg
      obtain ⟨⟨k, hk⟩, hk', rfl⟩ := hg
      apply And.intro (Finset.mem_univ _)
      simp only [Finset.mem_filter, Finset.mem_univ, Subgroup.coe_mk, true_and_iff] at hk'
      simp only [Subgroup.coeSubtype, Function.Embedding.coeFn_mk, Subgroup.coe_mk]
      exact hk'
    · rintro ⟨_, hg⟩
      simp only [Subgroup.coeSubtype, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and_iff, Function.Embedding.coeFn_mk, exists_prop]
      use! g
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hg, Even.neg_one_pow hm]
      -- exact ⟨hg, rfl⟩
  · rw [Finset.eq_empty_iff_forall_not_mem]
    intro g hg
    simp only [Subgroup.coeSubtype, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and_iff, Function.Embedding.coeFn_mk, exists_prop] at hg
    obtain ⟨⟨k, hk⟩, hkm, rfl⟩ := hg
    rw [← Nat.odd_iff_not_even] at hm
    simp only [Subgroup.coe_mk] at hkm
    simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType, hkm, Odd.neg_one_pow hm, ← Units.eq_iff] at hk
    norm_num at hk
#align on_cycle_factors.alternating_group.of_cycle_type_eq OnCycleFactors.AlternatingGroup.of_cycleType_eq

theorem AlternatingGroup.card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card *
        ((Fintype.card α - m.sum).factorial *
          (m.prod * (m.dedup.map fun n : ℕ => (m.count n).factorial).prod)) =
      if ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m))
        then (Fintype.card α).factorial
        else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map]
    rw [AlternatingGroup.of_cycleType_eq]
    rw [if_pos]
    have := Equiv.Perm.card_of_cycleType_mul_eq α m
    simp only [mul_assoc] at this
    rw [this]
    rw [if_pos]
    exact hm.1
    exact hm.2
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]
    rw [AlternatingGroup.of_cycleType_eq]
    rw [apply_ite Finset.card]
    rw [Finset.card_empty]
    rw [not_and_or] at hm
    by_cases hm' : Even (m.sum + Multiset.card m)
    rw [if_pos]
    rw [Equiv.Perm.card_of_cycleType]
    rw [if_neg]
    exact MulZeroClass.zero_mul _
    cases' hm with hm hm; exact hm; exfalso; exact hm hm'
    exact hm'
    rw [if_neg]; exact MulZeroClass.zero_mul _; exact hm'
#align on_cycle_factors.alternating_group.card_of_cycle_type_mul_eq OnCycleFactors.AlternatingGroup.card_of_cycleType_mul_eq

theorem AlternatingGroup.card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m) then
        (Fintype.card α).factorial /
          ((Fintype.card α - m.sum).factorial *
            (m.prod * (m.dedup.map fun n : ℕ => (m.count n).factorial).prod))
      else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map]
    rw [AlternatingGroup.of_cycleType_eq]
    rw [if_pos]
    rw [Equiv.Perm.card_of_cycleType α m]
    rw [if_pos]
    simp only [mul_assoc]
    exact hm.1
    exact hm.2
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map]
    rw [AlternatingGroup.of_cycleType_eq]
    rw [apply_ite Finset.card]
    rw [Finset.card_empty]
    rw [not_and_or] at hm
    by_cases hm' : Even (m.sum + Multiset.card m)
    rw [if_pos]
    rw [Equiv.Perm.card_of_cycleType]
    rw [if_neg]
    cases' hm with hm hm; exact hm; exfalso; exact hm hm'
    exact hm'
    rw [if_neg]; exact hm'
#align on_cycle_factors.alternating_group.card_of_cycle_type OnCycleFactors.AlternatingGroup.card_of_cycleType

variable {α}

lemma θ_apply_fst
    (k : Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g)) :
    θ g ⟨k, 1⟩ = Equiv.Perm.ofSubtype k := by
  ext x
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [hθ_2 _ x ⟨g.cycleOf x, hx⟩ rfl]
    simp only [Pi.one_apply, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
    simp only [MulAction.mem_fixedBy, Equiv.Perm.smul_def, ← Equiv.Perm.mem_support, ← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
    exact hx
  · rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [hθ_1 _ x hx]
    dsimp only
    rw [Equiv.Perm.ofSubtype_apply_of_mem]

lemma θ_apply_single
    (c : g.cycleFactorsFinset)
    (vc : Subgroup.zpowers (c : Equiv.Perm α)) :
    θ g ⟨1, Pi.mulSingle c vc⟩ = (vc : Equiv.Perm α) := by
  ext x
  by_cases hx : g.cycleOf x ∈ g.cycleFactorsFinset
  · rw [hθ_2 _ x ⟨g.cycleOf x, hx⟩ rfl]
    by_cases hc : g.cycleOf x = c
    · suffices : c = ⟨g.cycleOf x, hx⟩
      rw [← this]
      simp only [Pi.mulSingle_eq_same]
      rw [← Subtype.coe_inj, ← hc]
    · simp only [ne_eq]
      rw [Pi.mulSingle_eq_of_ne]
      simp only [OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      apply symm
      obtain ⟨m, hm⟩ := vc.prop
      dsimp at hm
      rw [← hm, ← Equiv.Perm.not_mem_support]
      intro hx'
      apply hc
      apply symm
      apply Equiv.Perm.cycle_is_cycleOf
      apply Equiv.Perm.support_zpow_le _ _ hx'
      exact c.prop
      intro hc'
      apply hc
      rw [← hc']
  · rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, Equiv.Perm.not_mem_support] at hx
    rw [hθ_1 _ x hx]
    dsimp only [Equiv.Perm.coe_one, id_eq]
    obtain ⟨m, hm⟩ := vc.prop
    dsimp only at hm
    rw [← hm]
    apply symm
    rw [← Equiv.Perm.not_mem_support] at hx ⊢
    intro hx'
    apply hx
    apply Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop
    apply Equiv.Perm.support_zpow_le _ _ hx'

example (α β : Type*) [Group α] [Group β]:
   α →* α × β := by
  exact MonoidHom.inl α β

theorem sign_ψ
    (k : Equiv.Perm (MulAction.fixedBy (Equiv.Perm α) α g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Equiv.Perm α)) :
    Equiv.Perm.sign (θ g ⟨k, v⟩) =
      Equiv.Perm.sign k *
        Finset.univ.prod fun c =>
          Equiv.Perm.sign (v c : Equiv.Perm α) :=  by
  rw [← Prod.fst_mul_snd ⟨k, v⟩]
  simp only [map_mul]
  apply congr_arg₂
  · rw [θ_apply_fst, Equiv.Perm.sign_ofSubtype]
  · rw [← MonoidHom.inr_apply, ← MonoidHom.comp_apply]
    conv_lhs => rw [← Finset.noncommProd_mul_single v]
    simp only [Finset.noncommProd_map]
    rw [Finset.noncommProd_eq_prod]
    apply Finset.prod_congr rfl
    intro c _
    simp only [MonoidHom.inr_apply, MonoidHom.coe_comp, Function.comp_apply, θ_apply_single]
#align on_cycle_factors.sign_ψ OnCycleFactors.sign_ψ

theorem odd_of_mem_kerφ
    (h : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g ≤ alternatingGroup α) :
    ∀ i ∈ g.cycleType, Odd i := by
  intro i hi
  rw [Equiv.Perm.cycleType_def g, Multiset.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  rw [← Finset.mem_def] at hc
  suffices Equiv.Perm.sign c = 1 by
    rw [Equiv.Perm.IsCycle.sign _, neg_eq_iff_eq_neg] at this
    rw [Nat.odd_iff_not_even, Function.comp_apply]
    rw [← neg_one_pow_eq_one_iff_even (R := ℤˣ) _, this, ← Units.eq_iff]
    norm_num
    simp only [ne_eq, ← Units.eq_iff]
    rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc
    exact hc.left
  suffices c = θ g ⟨1, Pi.mulSingle ⟨c, hc⟩ ⟨c, Subgroup.mem_zpowers c⟩⟩ by
    rw [this]
    apply h
    change ConjAct.toConjAct _ ∈ _
    apply Subgroup.map_subtype_le
    rw [OnCycleFactors.hφ_ker_eq_θ_range]
    exact Set.mem_range_self _
  rw [θ_apply_single]

theorem card_le_of_mem_kerφ
    (h : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g ≤ alternatingGroup α) :
    Fintype.card α ≤ g.cycleType.sum + 1 := by
  rw [← not_lt]
  intro hm
  rw [Nat.lt_iff_add_one_le, add_assoc] at hm
  change g.cycleType.sum + 2 ≤ _ at hm
  suffices 1 < Fintype.card (MulAction.fixedBy (Equiv.Perm α) α g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices : Equiv.Perm.sign (θ g ⟨Equiv.swap a b, 1⟩) ≠ 1
    · apply this
      apply h
      change ConjAct.toConjAct _ ∈ _
      apply Subgroup.map_subtype_le
      rw [OnCycleFactors.hφ_ker_eq_θ_range]
      exact Set.mem_range_self _
    rw [θ_apply_fst]
    simp only [Equiv.Perm.ofSubtype_swap_eq,
      Equiv.Perm.sign_swap', ne_eq, ite_eq_left_iff,
      Int.neg_units_ne_self, not_forall, exists_prop, and_true]
    rw [Subtype.coe_inj]
    exact hab
  · rw [OnCycleFactors.Equiv.Perm.card_fixedBy g]
    rw [add_comm] at hm
    rw [Nat.lt_iff_add_one_le, Nat.le_sub_iff_right _]
    exact hm
    rw [Equiv.Perm.sum_cycleType]
    exact Finset.card_le_univ _

theorem count_le_one_of_mem_kerφ
    (h : MulAction.stabilizer (ConjAct (Equiv.Perm α)) g ≤ alternatingGroup α) :
    ∀ i, g.cycleType.count i ≤ 1 := by
  rw [← Multiset.nodup_iff_count_le_one, Equiv.Perm.cycleType_def]
  rw [Multiset.nodup_map_iff_inj_on g.cycleFactorsFinset.nodup]
  simp only [Function.comp_apply, ← Finset.mem_def]
  by_contra hm
  push_neg at hm
  obtain ⟨c, hc, d, hd, hm, hm'⟩ := hm
  let τ : Equiv.Perm g.cycleFactorsFinset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
  obtain ⟨a⟩ := g.existsBasis
  suffices hτ : τ ∈ OnCycleFactors.Iφ g
--  let kk := OnCycleFactors.φ' a ⟨τ, hτ⟩
  let k : Equiv.Perm α :=
    ConjAct.ofConjAct (φ' a ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))
  have hk2 : ∀ c : g.cycleFactorsFinset, ConjAct.toConjAct k • (c : Equiv.Perm α) = τ c := by
    intro c
    rw [ConjAct.smul_def]
    simp only [ConjAct.ofConjAct_toConjAct]
    rw [mul_inv_eq_iff_eq_mul]
    ext x
    exact OnCycleFactors.k_cycle_apply hτ c x
  have hksup : k.support ≤ g.support := by
    intro x
    simp only [Equiv.Perm.mem_support]
    intro hx' hx; apply hx'
    rw [← Equiv.Perm.not_mem_support] at hx
    exact OnCycleFactors.k_apply_of_not_mem_support x hx
  suffices hsign_k : Equiv.Perm.sign k = -1
  · rw [h _, ← Units.eq_iff] at hsign_k
    exact Int.noConfusion hsign_k
    exact (φ' a ⟨τ, hτ⟩).prop
  · /- to prove that `sign k = -1`,
      we could prove that it is the product
      of the transpositions with disjoint supports
      [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
      which are in odd number by `odd_of_mem_kerφ`,
      but it will be sufficient to observe that `k ^ 2 = 1`
      (which implies that `k.cycleType` is of the form (2,2,…))
      and to control its support. -/
    suffices k.cycleType = Multiset.replicate c.support.card 2 by
      rw [Equiv.Perm.sign_of_cycleType]; rw [this]
      simp only [Multiset.sum_replicate, Algebra.id.smul_eq_mul, Multiset.card_replicate]
      rw [Odd.neg_one_pow]
      rw [Nat.odd_add']
      simp only [odd_of_mem_kerφ h c.support.card
        (by rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
            exact ⟨c, hc, rfl⟩),
        true_iff_iff]
      rw [mul_comm]; apply even_two_mul
    -- on_cycle_count.same_cycle_of_mem_support
    have hk_apply :
      ∀ (c : g.cycleFactorsFinset) (m n : ℕ),
        (k ^ m) ((g ^ n : Equiv.Perm α) (a.toFun c)) = (g ^ n) (a.toFun ((τ ^ m) c)) := by
      suffices : ∀ m n : ℕ, Commute (k ^ m) (g ^ n)
      intro c m n
      simp only [Commute, SemiconjBy] at this
      rw [← Equiv.Perm.mul_apply, this, Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq]
      induction' m with m hrec
      · simp only [pow_zero, Equiv.Perm.coe_one, id.def]
      · rw [pow_succ, Equiv.Perm.mul_apply]
        rw [hrec]
        rw [OnCycleFactors.φ'_apply ⟨τ, hτ⟩]
        rw [OnCycleFactors.k_apply_base _ hτ]
        rw [pow_succ]; rw [Equiv.Perm.coe_mul]
        rfl
      apply Commute.pow_pow
      rw [Commute, SemiconjBy, ← mul_inv_eq_iff_eq_mul]
      exact (OnCycleFactors.φ' a ⟨τ, hτ⟩).prop
    suffices ∀ i ∈ k.cycleType, i = 2 by
      rw [← Multiset.eq_replicate_card] at this
      rw [this]
      congr
      --
      suffices this' : Multiset.sum (Equiv.Perm.cycleType k) = Finset.card (Equiv.Perm.support k)

      rw [this] at this'
      simp only [Multiset.sum_replicate, Algebra.id.smul_eq_mul] at this'
      rw [← mul_left_inj']
      rw [this']
      suffices this2 : k.support = c.support ∪ d.support
      rw [this2]; rw [Finset.card_union_eq _]
      suffices this3 : d.support.card = c.support.card
      rw [this3]; rw [mul_two]
      exact hm.symm
      rw [← Equiv.Perm.disjoint_iff_disjoint_support]
      by_contra hcd; apply hm'
      exact Set.Pairwise.eq g.cycleFactorsFinset_pairwise_disjoint hc hd hcd
      · -- k.support = c.support ∪ d.support
        ext x
        constructor
        · intro hx
          obtain ⟨cx, hcx⟩ := Equiv.Perm.sameCycle_of_mem_support (hksup hx)
          have hxcx : x ∈ (cx : Equiv.Perm α).support := by
            rw [Equiv.Perm.SameCycle.eq_cycleOf cx
                (hcx (a.toFun cx) (a.mem_support cx)) (a.mem_support cx),
              Equiv.Perm.mem_support_cycleOf_iff]
            constructor; rfl; exact hksup hx
          suffices : c = cx ∨ d = cx
          rw [Finset.mem_union]
          cases' this with hccx hdcx
          · apply Or.intro_left; rw [hccx]; exact hxcx
          · apply Or.intro_right; rw [hdcx]; exact hxcx
          · obtain ⟨n, _, hnx⟩ := (hcx (a.toFun cx) (a.mem_support cx)).exists_pow_eq'
            rw [Equiv.Perm.mem_support, ← hnx] at hx
            specialize hk_apply cx 1
            simp only [pow_one] at hk_apply
            rw [hk_apply] at hx
            rw [Function.Injective.ne_iff (Equiv.injective _)] at hx
            have hx' : τ cx ≠ cx := ne_of_apply_ne a.toFun hx
            rw [← Equiv.Perm.mem_support] at hx'
            -- simp only [τ] at hx'
            rw [Equiv.Perm.support_swap _] at hx'
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
            cases' hx' with hx' hx'
            · apply Or.intro_left
              rw [hx']
            · apply Or.intro_right
              rw [hx']
            intro h; rw [← Subtype.coe_inj] at h ; apply hm'; exact h
        · intro hx
          -- obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x _,
          suffices hx' : Equiv.Perm.cycleOf g x = c ∨ Equiv.Perm.cycleOf g x = d
          obtain ⟨cx, hcx⟩ := Equiv.Perm.sameCycle_of_mem_support (x := x) ?_
          have hcx' := Equiv.Perm.SameCycle.eq_cycleOf cx
            (hcx (a.toFun cx) (a.mem_support cx)) (a.mem_support cx)
          obtain ⟨n, _, hnx⟩ := Equiv.Perm.SameCycle.exists_pow_eq'
            (hcx (a.toFun cx) (a.mem_support cx))
          specialize hk_apply cx 1
          simp only [pow_one] at hk_apply
          rw [← hnx, Equiv.Perm.mem_support, hk_apply]
          rw [Function.Injective.ne_iff (Equiv.injective _)]
          intro haτcx_eq_acx
          have : ¬Equiv.Perm.Disjoint (cx : Equiv.Perm α) (τ cx : Equiv.Perm α) := by
            rw [Equiv.Perm.disjoint_iff_support_disjoint]
            rw [Finset.not_disjoint_iff]
            use a.toFun cx
            apply And.intro (a.mem_support cx)
            rw [← haτcx_eq_acx]; exact a.mem_support (τ cx)
          have this' := (Set.Pairwise.eq
            g.cycleFactorsFinset_pairwise_disjoint cx.prop
            (τ cx).prop this).symm
          rw [Subtype.coe_inj] at this'
          rw [← Equiv.Perm.not_mem_support] at this'
          rw [Equiv.Perm.support_swap _] at this'
          simp only [Finset.mem_insert, Finset.mem_singleton] at this'
          apply this'
          simp only [← Subtype.coe_inj, Subtype.coe_mk, ← hcx']
          rw [Finset.mem_union] at hx
          rw [hcx']
          exact hx'
          · intro h
            simp only [← Subtype.coe_inj, Subtype.coe_mk] at h
            exact hm' h
          · simp only [Finset.mem_union] at hx
            cases hx with
            | inl hx =>
              apply Or.intro_left
              exact (Equiv.Perm.cycle_is_cycleOf hx hc).symm
            | inr hx =>
              apply Or.intro_right
              exact (Equiv.Perm.cycle_is_cycleOf hx hd).symm
      · norm_num
      · apply Equiv.Perm.sum_cycleType
    · rw [← Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff]
      cases' hx' with hxc hxd
      · rw [hxc]
        exact hc
      · rw [hxd]
        exact hd
    -- ∀ i ∈ k.cycle_type, i = 2
    suffices hk2 : orderOf k = 2
    · have hk2' : Nat.Prime (orderOf k); rw [hk2]; exact Nat.prime_two
      obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hk2'
      intro i hi
      rw [hn, hk2, Multiset.mem_replicate] at hi
      exact hi.right
    apply orderOf_eq_prime
    · -- k ^ 2 = 1,
      ext x
      simp only [Equiv.Perm.coe_one, id.def]
      by_cases hx : x ∈ g.support
      · -- obtain ⟨cx, hcx, hcx'⟩ := hsame_cycle x hx,
        obtain ⟨cx, hcx⟩ := Equiv.Perm.sameCycle_of_mem_support hx
        -- have hcx' := on_cycle_factors.same_cycle.is_cycle_of ha cx hcx,
        obtain ⟨n, _, rfl⟩ := (hcx (a.toFun cx) (a.mem_support cx)).exists_pow_eq'
        rw [hk_apply cx 2 n]
        apply congr_arg
        apply congr_arg
        suffices hτ2 : τ ^ 2 = 1
        rw [hτ2, Equiv.Perm.coe_one, id.def]
        rw [pow_two]; rw [Equiv.swap_mul_self]
      · -- lorsque x ∉ g.support
        rw [← Equiv.Perm.not_mem_support]
        intro hx'; apply hx
        apply hksup
        apply Equiv.Perm.support_pow_le k 2
        exact hx'
    intro hk
    specialize hk2 ⟨c, hc⟩
    simp only [hk, ConjAct.toConjAct_one, Subtype.coe_mk, one_smul,
      Equiv.swap_apply_left] at hk2
    exact hm' hk2
  · intro x
    by_cases hx : x = ⟨c, hc⟩
    · rw [hx, Equiv.swap_apply_left]; exact hm.symm
    by_cases hx' : x = ⟨d, hd⟩
    · rw [hx', Equiv.swap_apply_right]; exact hm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']

theorem kerφ_le_alternating_iff :
    MulAction.stabilizer (ConjAct (Equiv.Perm α)) g ≤ alternatingGroup α ↔
      (∀ i ∈ g.cycleType, Odd i) ∧
        Fintype.card α ≤ g.cycleType.sum + 1 ∧
          ∀ i, g.cycleType.count i ≤ 1 :=  by
  rw [SetLike.le_def]
  -- simp_rw [Equiv.Perm.mem_alternatingGroup]
  constructor
  · intro h
    constructor
    exact odd_of_mem_kerφ h
    constructor
    exact card_le_of_mem_kerφ h
    exact count_le_one_of_mem_kerφ h
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    suffices hx' : x ∈ Set.range (θ g)
    obtain ⟨⟨y, uv⟩, rfl⟩ := Set.mem_range.mp hx'
    rw [Equiv.Perm.mem_alternatingGroup, OnCycleFactors.sign_ψ]
    convert mul_one _
    · apply Finset.prod_eq_one
      rintro ⟨c, hc⟩ _
      obtain ⟨k, hk⟩ := (uv _).prop
      rw [← hk, map_zpow]
      convert one_zpow k
      simp only
      rw [Equiv.Perm.IsCycle.sign, Odd.neg_one_pow, neg_neg]
      apply h_odd
      rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
      use c
      exact ⟨hc, rfl⟩
      rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc
      exact hc.left

    · apply symm
      convert Equiv.Perm.sign_one
      rw [← Equiv.Perm.card_support_le_one]
      apply le_trans (Finset.card_le_univ _)
      change Fintype.card (MulAction.fixedBy (Equiv.Perm α) α g) ≤ 1
      rw [OnCycleFactors.Equiv.Perm.card_fixedBy g, tsub_le_iff_left]
      exact h_fixed
    -- x ∈ set.range (on_cycle_factors.ψ g)
    suffices : (OnCycleFactors.φ g).ker = ⊤
    rw [← OnCycleFactors.hφ_ker_eq_θ_range, this]
    simp only [Subgroup.coeSubtype, Subgroup.mem_map, Subgroup.mem_top, true_and]
    exact ⟨⟨x, hx⟩, rfl⟩

    -- (OnCycleFactors.φ g).ker = ⊤
    rw [eq_top_iff]
    intro y _
    suffices (OnCycleFactors.φ g).range = ⊥ by
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← this, MonoidHom.mem_range]
      exact ⟨y, rfl⟩
    rw [eq_bot_iff]
    intro z
    rw [← OnCycleFactors.Iφ_eq_range, Subgroup.mem_bot]
    intro hz
    apply Equiv.ext
    intro c
    rw [← Multiset.nodup_iff_count_le_one, Equiv.Perm.cycleType_def,
      Multiset.nodup_map_iff_inj_on (Equiv.Perm.cycleFactorsFinset g).nodup]
      at h_count
    rw [Equiv.Perm.coe_one, id.def, ← Subtype.coe_inj]
    exact h_count (z c) (z c).prop c c.prop (hz c)
#align kerφ_le_alternating_iff OnCycleFactors.kerφ_le_alternating_iff


end OnCycleFactors
