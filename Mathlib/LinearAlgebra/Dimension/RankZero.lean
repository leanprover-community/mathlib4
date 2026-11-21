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

## Main definitions and results

* `rank_eq_zero_iff_not_injective`: a module over a semiring has rank zero
  iff `(· • x : R → M)` is not injective for all `x : M`.
* `rank_eq_zero_iff`: a module over a ring has rank zero iff every element is torsion.
* `Module.RankZeroSubsingleton`: a typeclass saying that a module of rank zero is trivial.
  We provide instances for torsion free modules over a ring with no zero divisors
  and for free modules over an arbitrary semiring.
* `rank_zero_iff`, `rank_pos_iff_nontrivial`, `rank_pos`: corollaries of the above.
-/

@[expose] public section

open Cardinal Function

universe u v

section Semiring

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A module over a semiring has rank `0` iff each element is in torsion,
i.e., the scalar multiplication `(· • x : R → M)` is not injective for all `x : M`.

This is a version of `rank_eq_zero_iff` that works for semirings. -/
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

theorem Module.rank_eq_zero_of_not_faithfulSMul (h : ¬ FaithfulSMul R M) : Module.rank R M = 0 := by
  contrapose! h
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h
  exact ⟨fun {x y} hxy ↦ hf (by simpa [← map_smul] using hxy (f 1))⟩

namespace Module

variable (R M) in
/-- A typeclass saying that a module of rank zero is trivial.

This is true for a torsion free module over a ring with no zero divisors
and for a free module over any semiring.
More generally, it is true whenever `(· • x : R → M)` is injective for all nonzero `x : M`,
see `rank_eq_zero_iff_not_injective`.

Note that over a trivial semiring `R`, any module `M` is trivial and has `Module.rank R M = 1`,
so the reverse implication requires `Nontrivial R`, see `rank_subsingleton` and `rank_zero_iff`. -/
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

end Module

open Module

variable [RankZeroSubsingleton R M]

/-- See `Submodule.rank_eq_zero` for a version about submodules. -/
lemma Submodule.bot_eq_top_of_rank_eq_zero (h : Module.rank R M = 0) :
    (⊥ : Submodule R M) = ⊤ :=
  have := subsingleton_of_rank_zero h
  Subsingleton.elim _ _

theorem rank_pos [Nontrivial M] : 0 < Module.rank R M :=
  pos_iff_ne_zero.2 fun h ↦ not_subsingleton M (subsingleton_of_rank_zero h)

variable [Nontrivial R]

/-- A module of rank zero is trivial, provided that `R` is nontrivial
and `Module.RankZeroSubsingleton R M` holds,
e.g., if `M` is a free module or a torsion free module over a domain.

In case of a trivial (semi)ring `R`, `M` has to be trivial as well,
while `Module.rank R M = 1`, so the forward implication is true but the backward implication fails.
-/
theorem rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  ⟨subsingleton_of_rank_zero, fun _ ↦ rank_subsingleton' R M⟩

theorem rank_zero_iff_forall_zero : Module.rank R M = 0 ↔ ∀ x : M, x = 0 :=
  rank_zero_iff.trans (subsingleton_iff_forall_eq 0)

theorem rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M := by
  rw [pos_iff_ne_zero, ne_eq, rank_zero_iff, not_subsingleton_iff_nontrivial]

theorem rank_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ ∃ x : M, x ≠ 0 :=
  rank_pos_iff_nontrivial.trans (nontrivial_iff_exists_ne 0)

omit [RankZeroSubsingleton R M] in
lemma exists_mem_ne_zero_of_rank_pos {s : Submodule R M} (h : 0 < Module.rank R s) :
    ∃ b : M, b ∈ s ∧ b ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact h.false

omit [RankZeroSubsingleton R M] in
/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed. -/
@[simp]
theorem Submodule.rank_eq_zero {S : Submodule R M} [RankZeroSubsingleton R S] :
    Module.rank R S = 0 ↔ S = ⊥ := by
  rw [rank_zero_iff, Submodule.subsingleton_iff_eq_bot]

namespace Module

@[deprecated (since := "2026-11-15")] alias rank_pos_of_free := rank_pos
@[deprecated (since := "2026-11-15")] alias rank_pos_iff_of_free := rank_pos_iff_nontrivial
@[deprecated (since := "2026-11-15")] alias rank_zero_iff_of_free := rank_zero_iff

end Module

end Semiring

section Ring

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- See `rank_zero_iff` for a stronger version with `Module.IsTorsionFree R M`. -/
lemma rank_eq_zero_iff : Module.rank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by
  simp [rank_eq_zero_iff_not_injective, smul_left_injective_iff_smul_eq_zero, and_comm]

instance (priority := 100) Module.IsTorsionFree.rankZeroSubsingleton [IsCancelMulZero R]
    [Module.IsTorsionFree R M] : Module.RankZeroSubsingleton R M where
  subsingleton_of_rank_zero h := by
    rw [rank_eq_zero_iff_not_injective] at h
    exact (subsingleton_iff_forall_eq 0).2 fun x ↦ by_contra fun hx ↦ h x (smul_left_injective R hx)

end Ring
