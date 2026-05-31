/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Some lemmas pertaining to the action of `ConjAct (Perm α)` on `Perm α`

We prove some lemmas related to the action of `ConjAct (Perm α)` on `Perm α`:

Let `α` be a decidable fintype.

* `conj_support_eq` relates the support of `k • g` with that of `g`

* `cycleFactorsFinset_conj_eq`, `mem_cycleFactorsFinset_conj'`
  and `cycleFactorsFinset_conj` relate the set of cycles of `g`, `g.cycleFactorsFinset`,
  with that for `k • g`

-/

public section

namespace Equiv.Perm

open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `a : α` belongs to the support of `k • g` iff
  `k⁻¹ * a` belongs to the support of `g` -/
theorem mem_conj_support (k : ConjAct (Perm α)) (g : Perm α) (a : α) :
    a ∈ (k • g).support ↔ ConjAct.ofConjAct k⁻¹ a ∈ g.support := by
  simp only [mem_support, ConjAct.smul_def, not_iff_not, coe_mul,
    Function.comp_apply, ConjAct.ofConjAct_inv]
  apply Equiv.apply_eq_iff_eq_symm_apply

theorem support_conj_eq_smul_support (k : ConjAct (Perm α)) (g : Equiv.Perm α) :
    (k • g).support = k.ofConjAct • g.support := by
  ext
  rw [mem_conj_support, ← Perm.smul_def, ConjAct.ofConjAct_inv, Finset.inv_smul_mem_iff]

theorem support_toConjAct_eq_smul_support (k g : Perm α) :
    (ConjAct.toConjAct k • g).support = k • g.support := by
  rw [Equiv.Perm.support_conj_eq_smul_support, ConjAct.ofConjAct_toConjAct]

theorem cycleFactorsFinset_conj (g k : Perm α) :
    (ConjAct.toConjAct k • g).cycleFactorsFinset =
      Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinset := by
  ext c
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, Finset.mem_map_equiv,
    ← mem_cycleFactorsFinset_conj g k]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  simp [mul_assoc]

/-- A permutation `c` is a cycle of `g` iff `k • c` is a cycle of `k • g` -/
@[simp]
theorem mem_cycleFactorsFinset_conj'
    (k : ConjAct (Perm α)) (g c : Perm α) :
    k • c ∈ (k • g).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  simp only [ConjAct.smul_def]
  apply mem_cycleFactorsFinset_conj g k

theorem cycleFactorsFinset_conj_eq
    (k : ConjAct (Perm α)) (g : Perm α) :
    cycleFactorsFinset (k • g) = k • cycleFactorsFinset g := by
  ext c
  rw [← mem_cycleFactorsFinset_conj' k⁻¹ (k • g) c]
  simp only [inv_smul_smul]
  exact Finset.inv_smul_mem_iff

omit [Fintype α] in
theorem conj_smul_range_ofSubtype [Finite α] (g : Perm α) (s : Finset α) :
    ConjAct.toConjAct g • (ofSubtype (p := (· ∈ s))).range =
      (ofSubtype (p := (· ∈ g • s))).range := by
  have : Fintype α := Fintype.ofFinite α
  ext k
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_range_ofSubtype_iff]
  simp [support_conj_eq_smul_support, Set.subset_smul_set_iff]

end Equiv.Perm
