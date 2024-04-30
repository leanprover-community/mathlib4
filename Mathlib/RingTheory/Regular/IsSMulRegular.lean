/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Ideal.Operations

/-!
# Lemmas about the `IsSmulRegular` Predicate

For modules over a ring the proposition `IsSmulRegular r M` is equivalent to
`r` being a *non zero-divisor*, i.e. `r • x = 0` only if `x = 0` for `x ∈ M`.
This specific result is `isSMulRegular_iff_smul_eq_zero_imp_eq_zero`.
Lots of results starting from this, especially ones about quotients (which
don't make sense without some algebraic assumptions), are in this file.
We don't pollute the `Mathlib.Algebra.Regular.SMul` file with these because
it's supposed to import a minimal amount of the algebraic hierarchy.

## Tags

module, regular element, commutative algebra
-/

section Congr

lemma LinearEquiv.isSMulRegular_congr' {R S M N} [Semiring R] [Semiring S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
    (e : M ≃ₛₗ[σ] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N (σ r) :=
  e.toEquiv.isSMulRegular_congr (e.map_smul' r)

lemma LinearEquiv.isSMulRegular_congr {R M N} [Semiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) (r : R) :
    IsSMulRegular M r ↔ IsSMulRegular N r := e.isSMulRegular_congr' r

end Congr

namespace IsSMulRegular

lemma isSMulRegular_on_submodule_of_isSMulRegular {R : Type*} [Semiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] (N : Submodule R M) (r : R)
    (h : IsSMulRegular M r) : IsSMulRegular N r :=
  isSMulRegular_of_injective_of_isSMulRegular N.subtype N.injective_subtype h

variable {R : Type*} (M : Type*)

section Ring

variable {M' M'' : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

lemma isSMulRegular_iff_smul_eq_zero_imp_eq_zero (r : R) :
    IsSMulRegular M r ↔ ∀ x : M, r • x = 0 → x = 0 :=
  Iff.trans (Module.toAddMonoidEnd R M r).ker_eq_bot_iff.symm
    <| AddSubgroup.eq_bot_iff_forall _

variable {M}

lemma isSMulRegular_of_smul_eq_zero_imp_eq_zero {r : R}
    (h : ∀ x : M, r • x = 0 → x = 0) : IsSMulRegular M r :=
  (isSMulRegular_iff_smul_eq_zero_imp_eq_zero M r).mpr h

lemma isSMulRegular_on_submodule_iff_mem_imp_smul_eq_zero_imp_eq_zero
    (N : Submodule R M) (r : R) :
    IsSMulRegular N r ↔ ∀ x ∈ N, r • x = 0 → x = 0 :=
  Iff.trans (isSMulRegular_iff_smul_eq_zero_imp_eq_zero N r) <|
    Iff.trans Subtype.forall <| by
      simp only [SetLike.mk_smul_mk, AddSubmonoid.mk_eq_zero]

lemma isSMulRegular_on_quot_iff_smul_mem_implies_mem
    (N : Submodule R M) (r : R) :
    IsSMulRegular (M⧸N) r ↔ ∀ x : M, r • x ∈ N → x ∈ N :=
  Iff.trans (isSMulRegular_iff_smul_eq_zero_imp_eq_zero _ r) <|
    Iff.trans N.mkQ_surjective.forall <| by
      simp_rw [← map_smul, N.mkQ_apply, Submodule.Quotient.mk_eq_zero]

lemma mem_of_isSMulRegular_on_quot_of_smul_mem {N : Submodule R M}
    {r : R} {x : M} (h1 : IsSMulRegular (M⧸N) r) (h2 : r • x ∈ N) : x ∈ N :=
  (isSMulRegular_on_quot_iff_smul_mem_implies_mem N r).mp h1 x h2

/-- Given a left exact sequence `0 → M → M' → M''`, if `r` is regular on both
`M` and `M''` it's regular `M'` too. -/
lemma isSMulRegular_of_range_eq_ker {r : R} {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hf : Function.Injective f) (h : LinearMap.range f = LinearMap.ker g)
    (h1 : IsSMulRegular M r) (h2 : IsSMulRegular M'' r) :
    IsSMulRegular M' r := by
  refine isSMulRegular_of_smul_eq_zero_imp_eq_zero ?_
  intro x hx
  obtain ⟨y, ⟨⟩⟩ := (congrArg (x ∈ ·) h).mpr <| h2.eq_zero_of_smul_eq_zero <|
    Eq.trans (g.map_smul r x).symm <| Eq.trans (congrArg _ hx) g.map_zero
  refine Eq.trans (congrArg f (h1.eq_zero_of_smul_eq_zero ?_)) f.map_zero
  exact hf <| Eq.trans (f.map_smul r y) <| Eq.trans hx f.map_zero.symm

lemma isSMulRegular_of_isSMulRegular_on_submodule_on_quotient {r : R}
    {N : Submodule R M} (h1 : IsSMulRegular N r) (h2 : IsSMulRegular (M⧸N) r) :
    IsSMulRegular M r :=
  isSMulRegular_of_range_eq_ker N.injective_subtype
    (Eq.trans N.range_subtype N.ker_mkQ.symm) h1 h2

end Ring

variable [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (N : Submodule R M) (r : R)

lemma isSMulRegular_iff_ker_smul_eq_bot :
    IsSMulRegular M r ↔ LinearMap.ker (DistribMulAction.toLinearMap R M r) = ⊥ :=
  isSMulRegular_iff_torsionBy_top_eq_bot M r

lemma isSMulRegular_iff_isSMulRegular_over_quotient_by_torsion_ideal
    (hI : Module.IsTorsionBySet R M I) :
      letI := hI.module
      IsSMulRegular M r ↔ IsSMulRegular M (Ideal.Quotient.mk I r) :=
  letI := hI.module; (Equiv.refl M).isSMulRegular_congr fun _ => rfl

variable (I)

lemma isSMulRegular_on_quotient_ideal_smul_iff_isSMulRegular_over_quotient :
    IsSMulRegular (M⧸I•(⊤ : Submodule R M)) r ↔
      IsSMulRegular (M⧸I•(⊤ : Submodule R M)) (Ideal.Quotient.mk I r) :=
  (Equiv.refl _).isSMulRegular_congr fun _ => rfl

variable {M}

lemma isSMulRegular_on_submodule_iff_disjoint_ker_smul_submodule :
    IsSMulRegular N r ↔
      Disjoint (LinearMap.ker (DistribMulAction.toLinearMap R M r)) N :=
  Iff.trans (isSMulRegular_on_submodule_iff_mem_imp_smul_eq_zero_imp_eq_zero N r) <|
    Iff.symm <| Iff.trans disjoint_comm Submodule.disjoint_def

lemma isSMulRegular_on_quot_iff_smul_comap_le :
    IsSMulRegular (M⧸N) r ↔ N.comap (DistribMulAction.toLinearMap R M r) ≤ N :=
  isSMulRegular_on_quot_iff_smul_mem_implies_mem N r

end IsSMulRegular
