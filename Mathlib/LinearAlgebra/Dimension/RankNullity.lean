/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!

# The rank nullity theorem

In this file we provide the rank nullity theorem as a typeclass, and prove various corollaries
of the theorem. The main definition is `HasRankNullity.{u} R`, which states that
1. Every `R`-module `M : Type u` has a linear independent subset of cardinality `Module.rank R M`.
2. `rank (M ⧸ N) + rank N = rank M` for every `R`-module `M : Type u` and every `N : Submodule R M`.

The following instances are provided in mathlib:
1. `DivisionRing.hasRankNullity` for division rings in `LinearAlgebra/Dimension/DivisionRing.lean`.
2. `IsDomain.hasRankNullity` for commutative domains in `LinearAlgebra/Dimension/Localization.lean`.

TODO: prove the rank-nullity theorem for `[Ring R] [IsDomain R] [StrongRankCondition R]`.
See `nonempty_oreSet_of_strongRankCondition` for a start.
-/
universe u v

open Function Set Cardinal

variable {R} {M M₁ M₂ M₃ : Type u} {M' : Type v} [Ring R]
variable [AddCommGroup M] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M']
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M']

/--
`HasRankNullity.{u}` is a class of rings satisfying
1. Every `R`-module `M : Type u` has a linear independent subset of cardinality `Module.rank R M`.
2. `rank (M ⧸ N) + rank N = rank M` for every `R`-module `M : Type u` and every `N : Submodule R M`.

Usually such a ring satisfies `HasRankNullity.{w}` for all universes `w`, and the universe
argument is there because of technical limitations to universe polymorphism.

See `DivisionRing.hasRankNullity` and `IsDomain.hasRankNullity`.
-/
@[pp_with_univ]
class HasRankNullity (R : Type v) [inst : Ring R] : Prop where
  exists_set_linearIndependent : ∀ (M : Type u) [AddCommGroup M] [Module R M],
    ∃ s : Set M, #s = Module.rank R M ∧ LinearIndependent (ι := s) R Subtype.val
  rank_quotient_add_rank : ∀ {M : Type u} [AddCommGroup M] [Module R M] (N : Submodule R M),
    Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M

variable [HasRankNullity.{u} R]

lemma rank_quotient_add_rank (N : Submodule R M) :
    Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M :=
  HasRankNullity.rank_quotient_add_rank N
#align rank_quotient_add_rank rank_quotient_add_rank

variable (R M) in
lemma exists_set_linearIndependent :
    ∃ s : Set M, #s = Module.rank R M ∧ LinearIndependent (ι := s) R Subtype.val :=
  HasRankNullity.exists_set_linearIndependent M

variable (R) in
instance (priority := 100) : Nontrivial R := by
  refine (subsingleton_or_nontrivial R).resolve_left fun H ↦ ?_
  have := rank_quotient_add_rank (R := R) (M := PUnit) ⊥
  simp [one_add_one_eq_two] at this

theorem lift_rank_range_add_rank_ker (f : M →ₗ[R] M') :
    lift.{u} (Module.rank R (LinearMap.range f)) + lift.{v} (Module.rank R (LinearMap.ker f)) =
      lift.{v} (Module.rank R M) := by
  haveI := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.lift_rank_eq, ← lift_add, rank_quotient_add_rank]

/-- The **rank-nullity theorem** -/
theorem rank_range_add_rank_ker (f : M →ₗ[R] M₁) :
    Module.rank R (LinearMap.range f) + Module.rank R (LinearMap.ker f) = Module.rank R M := by
  haveI := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.rank_eq, rank_quotient_add_rank]
#align rank_range_add_rank_ker rank_range_add_rank_ker

theorem lift_rank_eq_of_surjective {f : M →ₗ[R] M'} (h : Surjective f) :
    lift.{v} (Module.rank R M) =
      lift.{u} (Module.rank R M') + lift.{v} (Module.rank R (LinearMap.ker f)) := by
  rw [← lift_rank_range_add_rank_ker f, ← rank_range_of_surjective f h]

theorem rank_eq_of_surjective {f : M →ₗ[R] M₁} (h : Surjective f) :
    Module.rank R M = Module.rank R M₁ + Module.rank R (LinearMap.ker f) := by
  rw [← rank_range_add_rank_ker f, ← rank_range_of_surjective f h]
#align rank_eq_of_surjective rank_eq_of_surjective

theorem exists_linearIndependent_of_lt_rank [StrongRankCondition R]
    {s : Set M} (hs : LinearIndependent (ι := s) R Subtype.val) :
    ∃ t, s ⊆ t ∧ #t = Module.rank R M ∧ LinearIndependent (ι := t) R Subtype.val := by
  obtain ⟨t, ht, ht'⟩ := exists_set_linearIndependent R (M ⧸ Submodule.span R s)
  choose sec hsec using Submodule.Quotient.mk_surjective (Submodule.span R s)
  have hsec' : Submodule.Quotient.mk ∘ sec = id := funext hsec
  have hst : Disjoint s (sec '' t) := by
    rw [Set.disjoint_iff]
    rintro _ ⟨hxs, ⟨x, hxt, rfl⟩⟩
    apply ht'.ne_zero ⟨x, hxt⟩
    rw [Subtype.coe_mk, ← hsec x, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span hxs
  refine ⟨s ∪ sec '' t, subset_union_left _ _, ?_, ?_⟩
  · rw [Cardinal.mk_union_of_disjoint hst, Cardinal.mk_image_eq, ht,
      ← rank_quotient_add_rank (Submodule.span R s), add_comm, rank_span_set hs]
    exact HasLeftInverse.injective ⟨Submodule.Quotient.mk, hsec⟩
  · apply LinearIndependent.union_of_quotient Submodule.subset_span hs
    rwa [Function.comp, linearIndependent_image ((hsec'.symm ▸ injective_id).injOn t).image_of_comp,
      ← image_comp, hsec', image_id]

/-- Given a family of `n` linearly independent vectors in a space of dimension `> n`, one may extend
the family by another vector while retaining linear independence. -/
theorem exists_linearIndependent_cons_of_lt_rank [StrongRankCondition R] {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent R v) (h : n < Module.rank R M) :
    ∃ (x : M), LinearIndependent R (Fin.cons x v) := by
  obtain ⟨t, h₁, h₂, h₃⟩ := exists_linearIndependent_of_lt_rank hv.to_subtype_range
  have : range v ≠ t := by
    refine fun e ↦ h.ne ?_
    rw [← e, ← lift_injective.eq_iff, mk_range_eq_of_injective hv.injective] at h₂
    simpa only [mk_fintype, Fintype.card_fin, lift_natCast, lift_id'] using h₂
  obtain ⟨x, hx, hx'⟩ := nonempty_of_ssubset (h₁.ssubset_of_ne this)
  exact ⟨x, (linearIndependent_subtype_range (Fin.cons_injective_iff.mpr ⟨hx', hv.injective⟩)).mp
    (h₃.mono (Fin.range_cons x v ▸ insert_subset hx h₁))⟩

/-- Given a family of `n` linearly independent vectors in a space of dimension `> n`, one may extend
the family by another vector while retaining linear independence. -/
theorem exists_linearIndependent_snoc_of_lt_rank [StrongRankCondition R] {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent R v) (h : n < Module.rank R M) :
    ∃ (x : M), LinearIndependent R (Fin.snoc v x) := by
  simp only [Fin.snoc_eq_cons_rotate]
  have ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_rank hv h
  exact ⟨x, hx.comp _ (finRotate _).injective⟩

/-- Given a nonzero vector in a space of dimension `> 1`, one may find another vector linearly
independent of the first one. -/
theorem exists_linearIndependent_pair_of_one_lt_rank [StrongRankCondition R]
    [NoZeroSMulDivisors R M] (h : 1 < Module.rank R M) {x : M} (hx : x ≠ 0) :
    ∃ y, LinearIndependent R ![x, y] := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_rank (linearIndependent_unique ![x] hx) h
  have : Fin.snoc ![x] y = ![x, y] := Iff.mp List.ofFn_inj rfl
  rw [this] at hy
  exact ⟨y, hy⟩

theorem exists_smul_not_mem_of_rank_lt {N : Submodule R M} (h : Module.rank R N < Module.rank R M) :
    ∃ m : M, ∀ r : R, r ≠ 0 → r • m ∉ N := by
  have : Module.rank R (M ⧸ N) ≠ 0 := by
    intro e
    rw [← rank_quotient_add_rank N, e, zero_add] at h
    exact h.ne rfl
  rw [ne_eq, rank_eq_zero_iff, (Submodule.Quotient.mk_surjective N).forall] at this
  push_neg at this
  simp_rw [← N.mkQ_apply, ← map_smul, N.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero] at this
  exact this

open BigOperators Cardinal Basis Submodule Function Set LinearMap

theorem Submodule.rank_sup_add_rank_inf_eq (s t : Submodule R M) :
    Module.rank R (s ⊔ t : Submodule R M) + Module.rank R (s ⊓ t : Submodule R M) =
    Module.rank R s + Module.rank R t := by
  conv_rhs => enter [2]; rw [show t = (s ⊔ t) ⊓ t by simp]
  rw [← rank_quotient_add_rank ((s ⊓ t).comap s.subtype),
    ← rank_quotient_add_rank (t.comap (s ⊔ t).subtype),
    (quotientInfEquivSupQuotient s t).rank_eq,
    (equivSubtypeMap s (comap _ (s ⊓ t))).rank_eq, Submodule.map_comap_subtype,
    (equivSubtypeMap (s ⊔ t) (comap _ t)).rank_eq, Submodule.map_comap_subtype,
    ← inf_assoc, inf_idem, add_right_comm]
#align submodule.rank_sup_add_rank_inf_eq Submodule.rank_sup_add_rank_inf_eq

theorem Submodule.rank_add_le_rank_add_rank (s t : Submodule R M) :
    Module.rank R (s ⊔ t : Submodule R M) ≤ Module.rank R s + Module.rank R t := by
  rw [← Submodule.rank_sup_add_rank_inf_eq]
  exact self_le_add_right _ _
#align submodule.rank_add_le_rank_add_rank Submodule.rank_add_le_rank_add_rank

section Finrank

open Submodule FiniteDimensional

variable [StrongRankCondition R]

/-- Given a family of `n` linearly independent vectors in a finite-dimensional space of
dimension `> n`, one may extend the family by another vector while retaining linear independence. -/
theorem exists_linearIndependent_snoc_of_lt_finrank {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent R v) (h : n < finrank R M) :
    ∃ (x : M), LinearIndependent R (Fin.snoc v x) :=
  exists_linearIndependent_snoc_of_lt_rank hv (lt_rank_of_lt_finrank h)

/-- Given a family of `n` linearly independent vectors in a finite-dimensional space of
dimension `> n`, one may extend the family by another vector while retaining linear independence. -/
theorem exists_linearIndependent_cons_of_lt_finrank {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent R v) (h : n < finrank R M) :
    ∃ (x : M), LinearIndependent R (Fin.cons x v) :=
  exists_linearIndependent_cons_of_lt_rank hv (lt_rank_of_lt_finrank h)

/-- Given a nonzero vector in a finite-dimensional space of dimension `> 1`, one may find another
vector linearly independent of the first one. -/
theorem exists_linearIndependent_pair_of_one_lt_finrank [NoZeroSMulDivisors R M]
    (h : 1 < finrank R M) {x : M} (hx : x ≠ 0) :
    ∃ y, LinearIndependent R ![x, y] :=
  exists_linearIndependent_pair_of_one_lt_rank (one_lt_rank_of_one_lt_finrank h) hx

end Finrank
