/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime
import Mathlib.RingTheory.QuotSMulTop

/-!
# Lemmas about the `IsSMulRegular` Predicate

For modules over a ring the proposition `IsSMulRegular r M` is equivalent to
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

variable {R S M N} [Semiring R] [Semiring S] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [AddCommMonoid M] [Module R M]

lemma LinearEquiv.isSMulRegular_congr' [AddCommMonoid N] [Module S N]
    (e : M ≃ₛₗ[σ] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N (σ r) :=
  e.toEquiv.isSMulRegular_congr (e.map_smul' r)

lemma LinearEquiv.isSMulRegular_congr [AddCommMonoid N] [Module R N]
    (e : M ≃ₗ[R] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N r :=
  e.isSMulRegular_congr' r

end Congr

namespace IsSMulRegular

open Submodule
open scoped Pointwise TensorProduct

variable {R : Type*} (S M : Type*) {M' M'' : Type*}

lemma isSMulRegular_algebraMap_iff [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] (r : R) :
    IsSMulRegular M (algebraMap R S r) ↔ IsSMulRegular M r :=
  (Equiv.refl M).isSMulRegular_congr (algebraMap_smul S r)

variable {S M}

lemma submodule [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (r : R) (h : IsSMulRegular M r) : IsSMulRegular N r :=
  h.of_injective N.subtype N.injective_subtype

section Ring

variable (M) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    (N : Submodule R M) (r : R)

lemma isSMulRegular_iff_smul_eq_zero_imp_eq_zero :
    IsSMulRegular M r ↔ ∀ x : M, r • x = 0 → x = 0 :=
  Iff.trans (Module.toAddMonoidEnd R M r).ker_eq_bot_iff.symm
    <| AddSubgroup.eq_bot_iff_forall _

lemma isSMulRegular_iff_mem_nonZeroSMulDivisors :
    IsSMulRegular M r ↔ r ∈ nonZeroSMulDivisors R M :=
  isSMulRegular_iff_smul_eq_zero_imp_eq_zero M r

variable {M r}

lemma isSMulRegular_of_smul_eq_zero_imp_eq_zero
    (h : ∀ x : M, r • x = 0 → x = 0) : IsSMulRegular M r :=
  (isSMulRegular_iff_smul_eq_zero_imp_eq_zero M r).mpr h

variable (r)

lemma isSMulRegular_on_submodule_iff_mem_imp_smul_eq_zero_imp_eq_zero :
    IsSMulRegular N r ↔ ∀ x ∈ N, r • x = 0 → x = 0 :=
  Iff.trans (isSMulRegular_iff_smul_eq_zero_imp_eq_zero N r) <|
    Iff.trans Subtype.forall <| by
      simp only [SetLike.mk_smul_mk, AddSubmonoid.mk_eq_zero]

lemma isSMulRegular_on_quot_iff_smul_mem_implies_mem :
    IsSMulRegular (M ⧸ N) r ↔ ∀ x : M, r • x ∈ N → x ∈ N :=
  Iff.trans (isSMulRegular_iff_smul_eq_zero_imp_eq_zero _ r) <|
    Iff.trans N.mkQ_surjective.forall <| by
      simp_rw [← map_smul, N.mkQ_apply, Quotient.mk_eq_zero]

variable {N r}

lemma mem_of_isSMulRegular_on_quot_of_smul_mem (h1 : IsSMulRegular (M ⧸ N) r)
    {x : M} (h2 : r • x ∈ N) : x ∈ N :=
  (isSMulRegular_on_quot_iff_smul_mem_implies_mem N r).mp h1 x h2

/-- Given a left exact sequence `0 → M → M' → M''`, if `r` is regular on both
`M` and `M''` it's regular `M'` too. -/
lemma isSMulRegular_of_range_eq_ker {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (h1 : IsSMulRegular M r) (h2 : IsSMulRegular M'' r) :
    IsSMulRegular M' r := by
  refine isSMulRegular_of_smul_eq_zero_imp_eq_zero ?_
  intro x hx
  obtain ⟨y, ⟨⟩⟩ := (congrArg (x ∈ ·) hfg).mpr <| h2.eq_zero_of_smul_eq_zero <|
    Eq.trans (g.map_smul r x).symm <| Eq.trans (congrArg _ hx) g.map_zero
  refine Eq.trans (congrArg f (h1.eq_zero_of_smul_eq_zero ?_)) f.map_zero
  exact hf <| Eq.trans (f.map_smul r y) <| Eq.trans hx f.map_zero.symm

lemma isSMulRegular_of_isSMulRegular_on_submodule_on_quotient
    (h1 : IsSMulRegular N r) (h2 : IsSMulRegular (M ⧸ N) r) : IsSMulRegular M r :=
  isSMulRegular_of_range_eq_ker N.injective_subtype
    (Eq.trans N.range_subtype N.ker_mkQ.symm) h1 h2

end Ring

variable (R M) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    {I : Ideal R} (N : Submodule R M) (r : R)

lemma biUnion_associatedPrimes_eq_compl_regular [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R M, p = { r : R | IsSMulRegular M r }ᶜ :=
  Eq.trans (biUnion_associatedPrimes_eq_zero_divisors R M) <| by
    simp_rw [Set.compl_setOf, isSMulRegular_iff_smul_eq_zero_imp_eq_zero,
      not_forall, exists_prop, and_comm]

variable {R} (I)

lemma isSMulRegular_iff_ker_lsmul_eq_bot :
    IsSMulRegular M r ↔ LinearMap.ker (LinearMap.lsmul R M r) = ⊥ :=
  isSMulRegular_iff_torsionBy_eq_bot M r

variable {M}

lemma isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule :
    IsSMulRegular N r ↔ Disjoint (LinearMap.ker (LinearMap.lsmul R M r)) N :=
  Iff.trans (isSMulRegular_on_submodule_iff_mem_imp_smul_eq_zero_imp_eq_zero N r) <|
    Iff.symm <| Iff.trans disjoint_comm disjoint_def

lemma isSMulRegular_on_quot_iff_lsmul_comap_le :
    IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) ≤ N :=
  isSMulRegular_on_quot_iff_smul_mem_implies_mem N r

lemma isSMulRegular_on_quot_iff_lsmul_comap_eq :
    IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) = N :=
  Iff.trans (isSMulRegular_on_quot_iff_lsmul_comap_le N r) <|
    LE.le.le_iff_eq (fun _ => N.smul_mem r)

variable {r}

lemma isSMulRegular_on_quot_iff_smul_top_inf_eq_smul_of_isSMulRegular :
    IsSMulRegular M r → (IsSMulRegular (M ⧸ N) r ↔ r • ⊤ ⊓ N ≤ r • N) := by
  intro (h : Function.Injective (DistribMulAction.toLinearMap R M r))
  rw [isSMulRegular_on_quot_iff_lsmul_comap_le, ← map_le_map_iff_of_injective h,
    ← LinearMap.lsmul_eq_DistribMulAction_toLinearMap,
    map_comap_eq, LinearMap.range_eq_map]; rfl

lemma isSMulRegular_of_ker_lsmul_eq_bot
    (h : LinearMap.ker (LinearMap.lsmul R M r) = ⊥) :
    IsSMulRegular M r :=
  (isSMulRegular_iff_ker_lsmul_eq_bot M r).mpr h

variable {N}

lemma smul_top_inf_eq_smul_of_isSMulRegular_on_quot :
    IsSMulRegular (M ⧸ N) r → r • ⊤ ⊓ N ≤ r • N := by
  convert map_mono ∘ (isSMulRegular_on_quot_iff_lsmul_comap_le N r).mp using 2
  exact Eq.trans (congrArg (· ⊓ N) (map_top _)) (map_comap_eq _ _).symm

-- Who knew this didn't rely on exactness at the right!?
open Function IsSMulRegular in
lemma _root_.QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    {M'''} [AddCommGroup M'''] [Module R M''']
    {r : R} {f₁ : M →ₗ[R] M'} {f₂ : M' →ₗ[R] M''} {f₃ : M'' →ₗ[R] M'''}
    (h₁₂ : Exact f₁ f₂) (h₂₃ : Exact f₂ f₃) (h : IsSMulRegular M''' r) :
    Exact (QuotSMulTop.map r f₁) (QuotSMulTop.map r f₂) :=
  suffices IsSMulRegular (M'' ⧸ LinearMap.range f₂) r by
    dsimp [QuotSMulTop.map, mapQLinear]
    rw [Exact.exact_mapQ_iff h₁₂, map_pointwise_smul, Submodule.map_top, inf_comm]
    exact smul_top_inf_eq_smul_of_isSMulRegular_on_quot this
  h.of_injective _ <| LinearMap.ker_eq_bot.mp <|
    ker_liftQ_eq_bot' _ _ h₂₃.linearMap_ker_eq.symm

variable (M)

lemma lTensor [Module.Flat R M] (h : IsSMulRegular M' r) :
    IsSMulRegular (M ⊗[R] M') r :=
  have h1 := congrArg DFunLike.coe (LinearMap.lTensor_smul_action M M' r)
  h1.subst (Module.Flat.lTensor_preserves_injective_linearMap _ h)

lemma rTensor [Module.Flat R M] (h : IsSMulRegular M' r) :
    IsSMulRegular (M' ⊗[R] M) r :=
  have h1 := congrArg DFunLike.coe (LinearMap.rTensor_smul_action M M' r)
  h1.subst (Module.Flat.rTensor_preserves_injective_linearMap _ h)

end IsSMulRegular
