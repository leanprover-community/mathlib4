/-
Copyright (c) 2018 Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison, Chris Hughes, Andrew Yang,
  Christian Merten, Antoine Chambert-Loir, Thomas Browning
-/
module

public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Modules of rank zero

In this file we characterize modules of rank zero.
A vector space has dimension zero if and only if it's trivial.
This fact generalizes to modules in at least two incompatible ways:

- a torsion-free module over a domain;
- a free module over a nontrivial semiring.

In order to avoid stating each corollary in 2 cases,
we introduce a class `Module.RankZeroSubsingleton` saying that a module of rank zero is trivial,
then use this typeclass as an assumption in `Module.rank_eq_zero_iff_subsingleton`
and its corollaries.

We provide two instances of this typeclass corresponding to the two cases above,
with nontriviality condition removed (it's needed for the other implication only).

## Main definitions and results

We prove that a module over a (semi)ring has rank zero iff every element is torsion.

* `Module.rank_eq_zero_iff_not_injective`: a version for semirings,
  with RHS saying that `(· • x : R → M)` is not injective for all `x : M`.
* `Module.rank_eq_zero_iff_forall_exists_smul_eq_zero`: a version for rings,
  with RHS saying that each `x : M` admits `a : R`, `a ≠ 0`, such that `a • x = 0`.

We also introduce the typeclass `Module.RankZeroSubsingleton` described above,
provide two instances for this typeclass, and prove immediate corollaries.

* `Module.rank_eq_zero_iff_subsingleton`, `Module.rank_pos_iff_nontrivial`:
  if `R` is nontrivial, then a module satisfying `Module.RankZeroSubsingleton R M` has rank zero
  iff it's trivial, and has a positive rank iff it's nontrivial.

* `Module.rank_pos`: a nontrivial module satisfying `Module.RankZeroSubsingleton`
  has a positive rank. Note that this version does not explicitly assume that `R` is nontrivial,
  but it follows from nontriviality of `M` anyway.

## TODO

Many of the lemmas in this files used to live in the root namespace.
When they were moved to this file, they were also moved to the `Module` namespace.
This created some name clashes between the deprecated aliases in the root namespace
and new names in the `Module` namespace.
As a temporary workaround, the `Module.*` versions are `protected` for now.
Drop `protected` from these lemmas once the deprecated in the root namespace
are removed from Mathlib.

* `Module.exists_mem_ne_zero_of_rank_pos`
* `Module.rank_pos`
* `Module.rank_pos_iff_nontrivial`
* `Module.rank_pos_iff_exists_ne_zero`
-/

@[expose] public section

open Cardinal Function

universe u v

namespace Module

section Semiring

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A module over a semiring has rank `0` iff each element is in torsion,
i.e., the scalar multiplication `(· • x : R → M)` is not injective for all `x : M`.

This is a version of `Module.rank_eq_zero_iff_forall_exists_smul_eq_zero`
that works for semirings. -/
lemma rank_eq_zero_iff_not_injective :
    Module.rank R M = 0 ↔ ∀ x : M, ¬Injective (· • x : R → M) := by
  simp_rw [Module.rank_def, ← le_zero_iff, ciSup_le_iff' bddAbove_of_small, Subtype.forall,
    le_zero_iff, Cardinal.mk_eq_zero_iff, Set.isEmpty_coe_sort,
    ← linearIndepOn_singleton_iff_injective (v := (·))]
  constructor
  · intro h x hx
    simpa using h _ hx
  · intro h s
    contrapose! h
    rcases h with ⟨hs, x, hx⟩
    exact ⟨x, hs.mono <| Set.singleton_subset_iff.mpr hx⟩

theorem rank_eq_zero_of_not_faithfulSMul (h : ¬ FaithfulSMul R M) : Module.rank R M = 0 := by
  contrapose! h
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h
  exact ⟨fun {x y} hxy ↦ hf (by simpa [← map_smul] using hxy (f 1))⟩

variable (R M) in
/-- A typeclass saying that a module of rank zero is trivial.

This is true for a torsion free module over a ring with no zero divisors
and for a free module over any semiring.
More generally, it is true whenever `(· • x : R → M)` is injective for all nonzero `x : M`,
see `rank_eq_zero_iff_not_injective`.

Note that over a trivial semiring `R`, any module `M` is trivial and has `Module.rank R M = 1`,
so the reverse implication requires `Nontrivial R`,
see `rank_subsingleton` and `Module.rank_eq_zero_iff_subsingleton`. -/
class RankZeroSubsingleton : Prop where
  subsingleton_of_rank_zero : Module.rank R M = 0 → Subsingleton M

/-- A module of rank zero is trivial, provided that `Module.RankZeroSubsingleton R M` holds,
e.g., if `M` is a free module or a torsion free module over a ring with no zero divisors. -/
theorem subsingleton_of_rank_zero [RankZeroSubsingleton R M] (h : Module.rank R M = 0) :
    Subsingleton M :=
  RankZeroSubsingleton.subsingleton_of_rank_zero h

instance (priority := 100) Free.rankZeroSubsingleton [Module.Free R M] :
    RankZeroSubsingleton R M where
  subsingleton_of_rank_zero h := by
    cases subsingleton_or_nontrivial R
    · exact Module.subsingleton R M
    have b := Free.chooseBasis R M
    have := b.linearIndependent.cardinal_lift_le_rank
    rw [h, lift_zero, le_zero_iff, lift_eq_zero, mk_eq_zero_iff] at this
    exact b.repr.subsingleton

protected lemma exists_mem_ne_zero_of_rank_pos [Nontrivial R] {s : Submodule R M}
    (h : 0 < Module.rank R s) : ∃ b : M, b ∈ s ∧ b ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact h.false

variable [RankZeroSubsingleton R M]

/-- See `Submodule.rank_eq_zero` for a version about submodules. -/
lemma _root_.Submodule.bot_eq_top_of_rank_eq_zero (h : Module.rank R M = 0) :
    (⊥ : Submodule R M) = ⊤ :=
  have := subsingleton_of_rank_zero h
  Subsingleton.elim _ _

protected theorem rank_pos [Nontrivial M] : 0 < Module.rank R M :=
  pos_iff_ne_zero.2 fun h ↦ not_subsingleton M (subsingleton_of_rank_zero h)

variable [Nontrivial R]

/-- A module of rank zero is trivial, provided that `R` is nontrivial
and `Module.RankZeroSubsingleton R M` holds,
e.g., if `M` is a free module or a torsion free module over a domain.

In case of a trivial (semi)ring `R`, `M` has to be trivial as well,
while `Module.rank R M = 1`, so the forward implication is true but the backward implication fails.
-/
theorem rank_eq_zero_iff_subsingleton : Module.rank R M = 0 ↔ Subsingleton M :=
  ⟨subsingleton_of_rank_zero, fun _ ↦ rank_subsingleton' R M⟩

theorem rank_eq_zero_iff_forall_zero : Module.rank R M = 0 ↔ ∀ x : M, x = 0 :=
  rank_eq_zero_iff_subsingleton.trans (subsingleton_iff_forall_eq 0)

protected theorem rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M := by
  rw [pos_iff_ne_zero, ne_eq, rank_eq_zero_iff_subsingleton, not_subsingleton_iff_nontrivial]

protected theorem rank_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ ∃ x : M, x ≠ 0 :=
  Module.rank_pos_iff_nontrivial.trans (nontrivial_iff_exists_ne 0)

omit [RankZeroSubsingleton R M] in
/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed. -/
@[simp]
theorem _root_.Submodule.rank_eq_zero {S : Submodule R M} [RankZeroSubsingleton R S] :
    Module.rank R S = 0 ↔ S = ⊥ := by
  rw [rank_eq_zero_iff_subsingleton, Submodule.subsingleton_iff_eq_bot]

end Semiring

section Ring

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- See `Module.rank_eq_zero_iff_subsingleton` for a stronger version
with `Module.IsTorsionFree R M`. -/
lemma rank_eq_zero_iff_forall_exists_smul_eq_zero :
    Module.rank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by
  simp [rank_eq_zero_iff_not_injective, smul_left_injective_iff_smul_eq_zero, and_comm]

instance (priority := 100) IsTorsionFree.rankZeroSubsingleton [IsCancelMulZero R]
    [Module.IsTorsionFree R M] : Module.RankZeroSubsingleton R M where
  subsingleton_of_rank_zero h := by
    rw [rank_eq_zero_iff_not_injective] at h
    exact (subsingleton_iff_forall_eq 0).2 fun x ↦ by_contra fun hx ↦ h x (smul_left_injective R hx)

end Ring

@[deprecated (since := "2026-11-16")] alias rank_pos_of_free := Module.rank_pos
@[deprecated (since := "2026-11-16")] alias rank_pos_iff_of_free := Module.rank_pos_iff_nontrivial
@[deprecated (since := "2026-11-16")] alias rank_zero_iff_of_free := rank_eq_zero_iff_subsingleton

end Module

@[deprecated (since := "2026-11-16")] alias rank_eq_zero_iff :=
  Module.rank_eq_zero_iff_forall_exists_smul_eq_zero
@[deprecated (since := "2026-11-16")] alias exists_mem_ne_zero_of_rank_pos :=
  Module.exists_mem_ne_zero_of_rank_pos
@[deprecated (since := "2026-11-16")] alias rank_zero_iff := Module.rank_eq_zero_iff_subsingleton
@[deprecated (since := "2026-11-16")] alias rank_zero_iff_forall_zero :=
  Module.rank_eq_zero_iff_forall_zero
@[deprecated (since := "2026-11-16")] alias rank_pos := Module.rank_pos
@[deprecated (since := "2026-11-16")] alias rank_pos_iff_nontrivial :=
  Module.rank_pos_iff_nontrivial
@[deprecated (since := "2026-11-16")] alias rank_pos_iff_exists_ne_zero :=
  Module.rank_pos_iff_exists_ne_zero
