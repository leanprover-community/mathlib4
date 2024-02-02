/-
Copyright (c) 2024 Emilie Burgun, Laurent Bartholdi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun, Laurent Bartholdi
-/

import Mathlib.Topology.Separation
import Mathlib.Topology.Algebra.Group.LocallyDense
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.Topology.Sets.RegularOpens
import Mathlib.Topology.Algebra.Group.Rubin.RegularSupport
import Mathlib.Topology.Algebra.Group.Rubin.Disjoint

/-!
# Isomorphism between regular supports and algebraic supports

In this file, we construct the order-preserving isomorphism between the algebraic support basis
and the regular support basis, which is used to prove Rubin's theorem.
-/

namespace Rubin

open Topology
open TopologicalSpace (RegularOpens)
open MulAction
open Pointwise

variable {G : Type*} (α : Type*) [Group G] [MulAction G α] [TopologicalSpace α] [T2Space α]
variable [ContinuousConstSMul G α] [LocallyDenseSMul G α] [FaithfulSMul G α] [NoIsolatedPoints α]

theorem movingSubgroup_regularSupport_le_algSupport (g : G) :
    G•[(RegularSupport α g : Set α)ᶜ] ≤ AlgSupport g := by
  intro h h_in_fixing
  apply Subgroup.mem_centralizer_iff.mpr
  intro i' ⟨i, i_disj, i_eq⟩

  apply Commute.symm <| Commute.eq _
  apply commute_of_fixingSubgroup_compl_of_disjoint _ h_in_fixing
  rw [← i_eq]
  apply Set.disjoint_of_subset_left _ (Disjoint.closure_left i_disj.disjoint_movedBy
    <| isOpen_compl_iff.mpr (isClosed_fixedBy α _))
  rw [RegularSupport, RegularOpens.coe_fromSet]
  nth_rw 2 [← IsOpen.closure_interior_closure_eq_closure
    <| isOpen_compl_iff.mpr (isClosed_fixedBy α g)]
  exact subset_closure

theorem movingSubgroup_regularSupport_eq_algSupport (g : G) :
    G•[(RegularSupport α g : Set α)ᶜ] = AlgSupport g := by
  apply le_antisymm (movingSubgroup_regularSupport_le_algSupport α g)
  intro h h_in_supp
  by_contra h_notin_fixing
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at h_notin_fixing

  let ⟨s, s_open, s_nonempty, s_subset, s_disj⟩ := disjoint_open_subset_of_not_subset_regularOpen
    (isOpen_compl_iff.mpr <| isClosed_fixedBy _ _) (RegularOpens.regularOpen _) h_notin_fixing
  let ⟨x, x_in_s⟩ := s_nonempty

  let ⟨t, t_open, x_in_t, t_subset_s, disj_t⟩ := t2_separation_smul_subset s_open x_in_s
    (s_subset x_in_s)

  have exp_eq_zero := LocallyMovingSMul.exponent_fixingSubgroup_eq_zero G t_open ⟨x, x_in_t⟩
  rw [Monoid.exponent_eq_zero_iff_forall_pow_ne_one] at exp_eq_zero

  let ⟨⟨i, i_in_fixing⟩, ipow_ne_one⟩ := exp_eq_zero 12 (Nat.succ_pos _)
  simp only [SubmonoidClass.mk_pow, ne_eq, Subgroup.mk_eq_one_iff] at ipow_ne_one

  -- We can now derive a contradiction: `i ^ 12` and `h` cannot commute since `i ∈ G•[tᶜ]` and
  -- `Disjoint t (h • t)`, but `i ^ 12` is algebraically disjoint from `g` and `h` must commute with
  -- every element that is algebraically disjoint from `g`.

  apply not_commute_of_disjoint_movedBy_preimage (α := α) ipow_ne_one
  · show Disjoint _ (h • _)
    have h₁ : (fixedBy α (i ^ 12))ᶜ ⊆ t := by
      rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at i_in_fixing
      apply subset_trans _ i_in_fixing
      rw [Set.compl_subset_compl]
      convert fixedBy_subset_fixedBy_zpow α i (12 : ℕ) using 2
      rw [zpow_ofNat]
    exact Set.disjoint_of_subset h₁ (Set.smul_set_mono h₁) disj_t
  · apply h_in_supp
    refine ⟨i, ?alg_disj, rfl⟩
    apply IsAlgDisjoint.of_disjoint_movedBy (α := α)
    apply Set.disjoint_of_subset
    · exact RegularOpens.subset_fromSet_of_isOpen (isOpen_compl_iff.mpr <| isClosed_fixedBy _ _)
    · exact subset_trans ((mem_fixingSubgroup_compl_iff_movedBy_subset _).mp i_in_fixing) t_subset_s
    · exact s_disj.symm

variable (G) in
/--
Applying `G•[·ᶜ]` to a `RegularSupportBasis` element yields an `AlgSupportBasis` element.

This is an auxiliary function, later used in `supportBasis_orderIso`
-/
def supportBasis_orderIso_aux (b : RegularSupportBasis G α) : AlgSupportBasis G := ⟨
  LocallyMovingSMul.movingSubgroup_orderEmbedding G α ⟨b.val, RegularSupportBasis.regularOpen b⟩,
  by
    let ⟨s, s_finite, s_eq⟩ := b.prop
    refine ⟨s, s_finite, ?eq⟩
    rw [LocallyMovingSMul.movingSubgroup_orderEmbedding, RelEmbedding.coe_mk,
      Function.Embedding.coeFn_mk, RegularOpens.coe_mk, s_eq]
    simp_rw [Set.compl_iInter, fixingSubgroup_iUnion,
      movingSubgroup_regularSupport_eq_algSupport]⟩

lemma _root_.OrderEmbedding.injective {α β : Type*} [PartialOrder α] [Preorder β] (f : α ↪o β) :
    Function.Injective f := by
  intro a b eq
  apply le_antisymm <;> rw [← f.map_rel_iff]
  · exact eq.le
  · exact eq.ge

variable (G) in
theorem supportBasis_orderIso_aux_bijective :
    Function.Bijective (supportBasis_orderIso_aux G α) := by
  constructor
  · intro b₁ b₂ eq
    rw [supportBasis_orderIso_aux, supportBasis_orderIso_aux, Subtype.mk_eq_mk] at eq
    convert (LocallyMovingSMul.movingSubgroup_orderEmbedding G α).injective eq using 1
    simp only [RegularOpens.mk.injEq, Subtype.val_inj]
  · intro b
    let ⟨s, s_finite, s_eq⟩ := b.prop
    use RegularSupportBasis.ofFinite α s s_finite
    rw [← Subtype.val_inj]
    simp_rw [s_eq, supportBasis_orderIso_aux, LocallyMovingSMul.movingSubgroup_orderEmbedding]
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk]
    change G•[(RegularSupportBasis.ofFinite α s s_finite : Set α)ᶜ] = _
    simp_rw [RegularSupportBasis.coe_ofFinite, Set.compl_iInter, fixingSubgroup_iUnion,
      movingSubgroup_regularSupport_eq_algSupport]

variable {α} in
/--
One of the two key constructions in Rubin's theorem: one can construct an order-preserving
isomorphism between elements of the regular support basis (which forms a topological basis),
and the algebraic support basis (which is purely defined in terms of `G`).
-/
noncomputable def supportBasis_orderIso : RegularSupportBasis G α ≃o AlgSupportBasis G where
  toEquiv := Equiv.ofBijective _ <| supportBasis_orderIso_aux_bijective G α
  map_rel_iff' := by
    intro b₁ b₂
    simp_rw [Equiv.ofBijective_apply, supportBasis_orderIso_aux]
    rw [Subtype.mk_le_mk, (LocallyMovingSMul.movingSubgroup_orderEmbedding G α).map_rel_iff]
    rfl

theorem supportBasis_orderIso_apply {b : RegularSupportBasis G α} :
    (supportBasis_orderIso b).val = G•[(b : Set α)ᶜ] := rfl

/--
The rubin action induces that the `AlgSupportBasis G` must contain a bottom element.
Note that the requirements for this instance could be weakened.
-/
def AlgSupportBasis.orderBot : OrderBot (AlgSupportBasis G) where
  bot := ⟨
    ⊥,
    by
      use {1}
      simp only [Set.finite_singleton, Set.mem_singleton_iff, iInf_iInf_eq_left, true_and]
      rw [← movingSubgroup_regularSupport_eq_algSupport (α := α)]
      simp only [RegularSupport, fixedBy_one_eq_univ, Set.compl_univ,
        RegularOpens.coe_fromSet, closure_empty, interior_empty, Set.compl_empty,
        fixingSubgroup_univ]
  ⟩
  bot_le := fun b => (bot_le : ⊥ ≤ b.val)

end Rubin
