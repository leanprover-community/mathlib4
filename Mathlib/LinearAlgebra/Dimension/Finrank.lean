/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Anne Baanen
-/
import Mathlib.LinearAlgebra.Dimension.Subsingleton
import Mathlib.SetTheory.Cardinal.ToNat

/-!
# Finite dimension of vector spaces

Definition of the rank of a module, or dimension of a vector space, as a natural number.

## Main definitions

Defined is `Module.finrank`, the dimension of a finite dimensional space, returning a
`Nat`, as opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite
dimension, its `finrank` is by convention set to `0`.

The definition of `finrank` does not assume a `FiniteDimensional` instance, but lemmas might.
Import `LinearAlgebra.FiniteDimensional` to get access to these additional lemmas.

Formulas for the dimension are given for linear equivs, in `LinearEquiv.finrank_eq`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `Dimension.lean`. Not all results have been ported yet.

You should not assume that there has been any effort to state lemmas as generally as possible.
-/


universe u v w

open Cardinal Submodule Module Function

variable {R : Type u} {M : Type v} {N : Type w}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Module

section Semiring

/-- The rank of a module as a natural number.

For a finite-dimensional vector space `V` over a field `k`, `Module.finrank k V` is equal to
the dimension of `V` over `k`.

For a general module `M` over a ring `R`, `Module.finrank R M` is defined to be the supremum of the
cardinalities of the `R`-linearly independent subsets of `M`, if this supremum is finite. It is
defined by convention to be `0` if this supremum is infinite. See `Module.rank` for a
cardinal-valued version where infinite rank modules have rank an infinite cardinal.

Note that if `R` is not a field then there can exist modules `M` with `¬(Module.Finite R M)` but
`finrank R M ≠ 0`. For example `ℚ` has `finrank` equal to `1` over `ℤ`, because the nonempty
`ℤ`-linearly independent subsets of `ℚ` are precisely the nonzero singletons. -/
noncomputable def finrank (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] : ℕ :=
  Cardinal.toNat (Module.rank R M)

@[simp] theorem finrank_subsingleton [Subsingleton R] : finrank R M = 1 := by
  rw [finrank, rank_subsingleton, map_one]

theorem finrank_eq_of_rank_eq {n : ℕ} (h : Module.rank R M = ↑n) : finrank R M = n := by
  simp [finrank, h]

lemma rank_eq_one_iff_finrank_eq_one : Module.rank R M = 1 ↔ finrank R M = 1 :=
  Cardinal.toNat_eq_one.symm

/-- This is like `rank_eq_one_iff_finrank_eq_one` but works for `2`, `3`, `4`, ... -/
lemma rank_eq_ofNat_iff_finrank_eq_ofNat (n : ℕ) [Nat.AtLeastTwo n] :
    Module.rank R M = OfNat.ofNat n ↔ finrank R M = OfNat.ofNat n :=
  Cardinal.toNat_eq_ofNat.symm

theorem finrank_le_of_rank_le {n : ℕ} (h : Module.rank R M ≤ ↑n) : finrank R M ≤ n := by
  rwa [← Cardinal.toNat_le_iff_le_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans_lt (nat_lt_aleph0 n)
  · exact nat_lt_aleph0 n

theorem finrank_lt_of_rank_lt {n : ℕ} (h : Module.rank R M < ↑n) : finrank R M < n := by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast] at h
  · exact h.trans (nat_lt_aleph0 n)
  · exact nat_lt_aleph0 n

theorem lt_rank_of_lt_finrank {n : ℕ} (h : n < finrank R M) : ↑n < Module.rank R M := by
  rwa [← Cardinal.toNat_lt_iff_lt_of_lt_aleph0, toNat_natCast]
  · exact nat_lt_aleph0 n
  · contrapose! h
    rw [finrank, Cardinal.toNat_apply_of_aleph0_le h]
    exact n.zero_le

theorem one_lt_rank_of_one_lt_finrank (h : 1 < finrank R M) : 1 < Module.rank R M := by
  simpa using lt_rank_of_lt_finrank h

theorem finrank_le_finrank_of_rank_le_rank
    (h : lift.{w} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R N))
    (h' : Module.rank R N < ℵ₀) : finrank R M ≤ finrank R N := by
  simpa only [toNat_lift] using toNat_le_toNat h (lift_lt_aleph0.mpr h')

end Semiring

end Module

open Module

namespace LinearEquiv

/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
theorem finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finrank R N := by
  unfold finrank
  rw [← Cardinal.toNat_lift, f.lift_rank_eq, Cardinal.toNat_lift]

/-- Pushforwards of finite-dimensional submodules along a `LinearEquiv` have the same finrank. -/
theorem finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodule R M) :
    finrank R (p.map (f : M →ₗ[R] N)) = finrank R p :=
  (f.submoduleMap p).finrank_eq.symm

end LinearEquiv

/-- The dimensions of the domain and range of an injective linear map are equal. -/
theorem LinearMap.finrank_range_of_inj {f : M →ₗ[R] N} (hf : Function.Injective f) :
    finrank R (LinearMap.range f) = finrank R M := by rw [(LinearEquiv.ofInjective f hf).finrank_eq]

@[simp]
theorem Submodule.finrank_map_subtype_eq (p : Submodule R M) (q : Submodule R p) :
    finrank R (q.map p.subtype) = finrank R q :=
  (Submodule.equivSubtypeMap p q).symm.finrank_eq

variable (R M)

@[simp]
theorem finrank_top : finrank R (⊤ : Submodule R M) = finrank R M := by
  unfold finrank
  simp

namespace Algebra

/-- If `S₀ / R₀` and `S₁ / R₁` are algebras, `i : R₀ ≃+* R₁` and `j : S₀ ≃+* S₁` are
ring isomorphisms, such that `R₀ → R₁ → S₁` and `R₀ → S₀ → S₁` commute,
then the finrank of `S₀ / R₀` is equal to the finrank of `S₁ / R₁`. -/
theorem finrank_eq_of_equiv_equiv {R₀ S₀ : Type*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀]
    {R₁ S₁ : Type*} [CommSemiring R₁] [Semiring S₁] [Algebra R₁ S₁] (i : R₀ ≃+* R₁) (j : S₀ ≃+* S₁)
    (hc : (algebraMap R₁ S₁).comp i.toRingHom = j.toRingHom.comp (algebraMap R₀ S₀)) :
    Module.finrank R₀ S₀ = Module.finrank R₁ S₁ := by
  simpa using (congr_arg Cardinal.toNat (lift_rank_eq_of_equiv_equiv i j hc))

end Algebra
