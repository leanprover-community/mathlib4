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

We prove some lemmas related to the conjugation action of `Perm α` on `Perm α`:

Let `α` be a decidable fintype.

* `supportFinset_conj_eq_smul_supportFinset` relates the support of `MulAut.conj k g`
  with that of `g`.

* `cycleFactorsFinset_conj_eq`, `mem_cycleFactorsFinset_conj'`
  and `cycleFactorsFinset_conj` relate the set of cycles of `g`, `g.cycleFactorsFinset`,
  with that for `MulAut.conj k g`.
-/

public section

namespace Equiv.Perm

open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `a : α` belongs to the support of `MulAut.conj k g` iff
  `k⁻¹ a` belongs to the support of `g` -/
theorem mem_conj_supportFinset (k g : Perm α) (a : α) :
    a ∈ (MulAut.conj k g).supportFinset ↔ k⁻¹ a ∈ g.supportFinset := by
  simp

@[deprecated (since := "2026-11-16")] alias mem_conj_support := mem_conj_supportFinset

theorem supportFinset_conj_eq_smul_supportFinset (k g : Perm α) :
    (MulAut.conj k g).supportFinset = k • g.supportFinset := by
  ext
  rw [mem_conj_supportFinset, ← Perm.smul_def, Finset.inv_smul_mem_iff]

@[deprecated (since := "2026-11-16")] alias support_conj_eq_smul_support :=
    supportFinset_conj_eq_smul_supportFinset

@[deprecated (since := "2026-09-21")] alias support_toConjAct_eq_smul_support :=
  supportFinset_conj_eq_smul_supportFinset

theorem cycleFactorsFinset_conj (g k : Perm α) :
    (MulAut.conj k g).cycleFactorsFinset =
      Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinset := by
  ext c
  simp [← mem_cycleFactorsFinset_conj g k, mul_assoc]

/-- A permutation `c` is a cycle of `g` iff `k • c` is a cycle of `k • g` -/
theorem mem_cycleFactorsFinset_conj' (k g c : Perm α) :
    MulAut.conj k c ∈ (MulAut.conj k g).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  apply mem_cycleFactorsFinset_conj g k

theorem cycleFactorsFinset_conj_eq (k g : Perm α) :
    cycleFactorsFinset (MulAut.conj k g) = MulAut.conj k • cycleFactorsFinset g := by
  rw [cycleFactorsFinset_conj]
  apply Finset.map_eq_image

omit [Fintype α] in
theorem conj_smul_range_ofSubtype [Finite α] (g : Perm α) (s : Finset α) :
    MulAut.conj g • (ofSubtype (p := (· ∈ s))).range = (ofSubtype (p := (· ∈ g • s))).range := by
  have : Fintype α := Fintype.ofFinite α
  simp_rw [← eq_inv_smul_iff, Subgroup.ext_iff, Subgroup.mem_inv_pointwise_smul_iff,
    mem_range_ofSubtype_iff, MulAut.smul_def, supportFinset_conj_eq_smul_supportFinset]
  simp

end Equiv.Perm
