/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Subgroup.Simple

/-! # Iwasawa criterion for simplicity

- `IwasawaStructure` : the structure underlying the Iwasawa criterion
For a group `G`, this consists of an action of `G` on a type `α` and,
for every `a : α`, of a subgroup `T a`, such that the following properties hold:
  - for all `a`, `T a` is commutative
  - for all `g : G` and `a : α`, `T (g • a) = MulAut.conj g • T a
  - the subgroups `T a` generate `G`

We then prove two versions of the Iwasawa criterion when
there is an Iwasawa structure.

- `IwasawaStructure.commutator_le` asserts that if the action of `G` on `α`
is quasiprimitive, then every normal subgroup that acts nontrivially
contains `commutator G`

- `IwasawaStructure.isSimpleGroup` : the Iwasawa criterion for simplicity
If the action of `G` on `α` is quasiprimitive and faithful,
and `G` is nontrivial and perfect, then `G` is simple.

## TODO

Additivize. The issue is that it requires to additivize `commutator`
(which, moreover, lives in the root namespace)
-/

namespace MulAction

open scoped BigOperators Pointwise

variable (M : Type*) [Group M] (α : Type*) [MulAction M α]

/-- The structure underlying the Iwasawa criterion -/
structure IwasawaStructure where
  /-- The subgroups of the Iwasawa structure -/
  T : α → Subgroup M
  /-- The commutativity property of the subgroups -/
  is_comm : ∀ x : α, IsMulCommutative (T x)
  /-- The conjugacy property of the subgroups -/
  is_conj : ∀ g : M, ∀ x : α, T (g • x) = MulAut.conj g • T x
  /-- The subgroups generate the group -/
  is_generator : iSup T = ⊤

variable {M α}

namespace IwasawaStructure

/-- The Iwasawa criterion : If a quasiprimitive action of a group G on X
  has an Iwasawa structure, then any normal subgroup that acts nontrivially
  contains the group of commutators. -/
theorem commutator_le (IwaS : IwasawaStructure M α) [IsQuasiPreprimitive M α]
    (N : Subgroup M) [nN : N.Normal] (hNX : MulAction.fixedPoints N α ≠ .univ) :
    commutator M ≤ N := by
  have is_transN := IsQuasiPreprimitive.isPretransitive_of_normal hNX
  have ntα : Nontrivial α := nontrivial_of_fixedPoints_ne_univ hNX
  obtain a : α := Nontrivial.to_nonempty.some
  apply nN.commutator_le_of_self_sup_commutative_eq_top ?_ (IwaS.is_comm a)
  -- We have to prove that N ⊔ IwaS.T x = ⊤
  rw [eq_top_iff, ← IwaS.is_generator, iSup_le_iff]
  intro x
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq N a x
  rw [Subgroup.smul_def, IwaS.is_conj g a]
  rintro _ ⟨k, hk, rfl⟩
  have hg' : ↑g ∈ N ⊔ IwaS.T a := Subgroup.mem_sup_left (Subtype.mem g)
  have hk' : k ∈ N ⊔ IwaS.T a := Subgroup.mem_sup_right hk
  exact (N ⊔ IwaS.T a).mul_mem ((N ⊔ IwaS.T a).mul_mem hg' hk') ((N ⊔ IwaS.T a).inv_mem hg')

/-- The Iwasawa criterion for simplicity -/
theorem isSimpleGroup [Nontrivial M] (is_perfect : commutator M = ⊤)
    [IsQuasiPreprimitive M α] (IwaS : IwasawaStructure M α) (is_faithful : FaithfulSMul M α) :
    IsSimpleGroup M := by
  apply IsSimpleGroup.mk
  intro N nN
  cases or_iff_not_imp_left.mpr (IwaS.commutator_le N) with
  | inl h =>
    refine Or.inl (N.eq_bot_iff_forall.mpr fun n hn => ?_)
    apply is_faithful.eq_of_smul_eq_smul
    intro x
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp h x ⟨n, hn⟩
  | inr h => exact Or.inr (top_le_iff.mp (le_trans (ge_of_eq is_perfect) h))

end MulAction.IwasawaStructure
