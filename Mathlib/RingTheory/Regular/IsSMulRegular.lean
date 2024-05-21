/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

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

variable {R : Type*} (M M' M'' : Type*)

section Ring

variable {M' M''} [Ring R] [AddCommGroup M] [Module R M]
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
    {r : R} (h1 : IsSMulRegular (M⧸N) r) {x : M} (h2 : r • x ∈ N) : x ∈ N :=
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
    [AddCommGroup M'] [Module R M'] {I : Ideal R} (N : Submodule R M) (r : R)

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

open scoped TensorProduct in
lemma isSMulRegular_lTensor [Module.Flat R M] (h : IsSMulRegular M' r) :
    IsSMulRegular (M ⊗[R] M') r :=
  have h1 := congrArg DFunLike.coe (LinearMap.lTensor_smul_action M M' r)
  Eq.mp (congrArg Function.Injective h1) <|
    Module.Flat.lTensor_preserves_injective_linearMap _ h

open scoped TensorProduct in
lemma isSMulRegular_rTensor [Module.Flat R M] (h : IsSMulRegular M' r) :
    IsSMulRegular (M' ⊗[R] M) r :=
  have h1 := congrArg DFunLike.coe (LinearMap.rTensor_smul_action M M' r)
  Eq.mp (congrArg (Function.Injective) h1) <|
    Module.Flat.rTensor_preserves_injective_linearMap _ h

variable {M}

lemma isSMulRegular_on_submodule_iff_disjoint_ker_smul_submodule :
    IsSMulRegular N r ↔
      Disjoint (LinearMap.ker (DistribMulAction.toLinearMap R M r)) N :=
  Iff.trans (isSMulRegular_on_submodule_iff_mem_imp_smul_eq_zero_imp_eq_zero N r) <|
    Iff.symm <| Iff.trans disjoint_comm Submodule.disjoint_def

lemma isSMulRegular_on_quot_iff_smul_comap_le :
    IsSMulRegular (M⧸N) r ↔ N.comap (DistribMulAction.toLinearMap R M r) ≤ N :=
  isSMulRegular_on_quot_iff_smul_mem_implies_mem N r

lemma isSMulRegular_on_quot_iff_smul_comap_eq :
    IsSMulRegular (M⧸N) r ↔ N.comap (DistribMulAction.toLinearMap R M r) = N :=
  Iff.trans (isSMulRegular_on_quot_iff_smul_comap_le N r) <|
    LE.le.le_iff_eq (fun _ => N.smul_mem r)

variable {r}

open Submodule Pointwise in
lemma isSMulRegular_on_quot_iff_smul_top_inf_eq_smul_of_isSMulRegular :
    IsSMulRegular M r → (IsSMulRegular (M⧸N) r ↔ r • ⊤ ⊓ N ≤ r • N) := by
  intro (h : Function.Injective (DistribMulAction.toLinearMap R M r))
  rw [isSMulRegular_on_quot_iff_smul_comap_le, ← map_le_map_iff_of_injective h,
    map_comap_eq, LinearMap.range_eq_map]; rfl

variable {N}

open Submodule Pointwise in
lemma smul_top_inf_eq_smul_of_isSMulRegular_on_quot :
    IsSMulRegular (M⧸N) r → r • ⊤ ⊓ N ≤ r • N := by
  convert map_mono ∘ (isSMulRegular_on_quot_iff_smul_comap_le N r).mp using 2
  exact Eq.trans (congrArg (· ⊓ N) (Submodule.map_top _)) (map_comap_eq _ _).symm

variable (R r)

lemma biUnion_associatedPrimes_eq_non_regular [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R M, p = { r : R | ¬ IsSMulRegular M r } :=
  Eq.trans (biUnion_associatedPrimes_eq_zero_divisors R M) <| by
    simp_rw [isSMulRegular_iff_smul_eq_zero_imp_eq_zero,
      not_forall, exists_prop, and_comm]

end IsSMulRegular


-- Probably these should be moved
section

open scoped Pointwise

variable {R} (M : Type*) {M' M''} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']

/-- An abbreviation for `M⧸rM` that keeps us from having to write
`(⊤ : Submodule R M)` over and over to satisfy the typechecker. -/
abbrev ModSMulBy (r : R) := M ⧸ r • (⊤ : Submodule R M)

namespace ModSMulBy

open Submodule Function

open TensorProduct in
/-- Reducing a module modulo `r` is the same as left tensoring with `R/(r)`. -/
noncomputable def equiv_lTensor_ring_mod (r : R) :
    ModSMulBy M r ≃ₗ[R] (R⧸Ideal.span {r}) ⊗[R] M :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
   (lTensor_ring_mod_ideal_equiv_mod_ideal_smul M _).symm

open TensorProduct in
/-- Reducing a module modulo `r` is the same as right tensoring with `R/(r)`. -/
noncomputable def equiv_rTensor_ring_mod (r : R) :
    ModSMulBy M r ≃ₗ[R] M ⊗[R] (R⧸Ideal.span {r}) :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
   (rTensor_ring_mod_ideal_equiv_mod_ideal_smul M _).symm

variable {M}

/-- The action of the functor `ModSMulBy · r` on morphisms. -/
def map (r : R) : (M →ₗ[R] M') →ₗ[R] ModSMulBy M r →ₗ[R] ModSMulBy M' r :=
  Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
    map_le_iff_le_comap.mp <| le_of_eq_of_le (map_element_smul _ _ _) <|
      smul_mono_right r le_top

@[simp]
lemma map_apply_apply (r : R) (f : M →ₗ[R] M') (x : M) :
    map r f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f x) : ModSMulBy M' r) := rfl

lemma map_comp_mkQ (r : R) (f : M →ₗ[R] M') :
    map r f ∘ₗ mkQ (r • ⊤) = mkQ (r • ⊤) ∘ₗ f := rfl

variable (M)

@[simp]
lemma map_id (r : R) : map r (LinearMap.id : M →ₗ[R] M) = .id :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

variable {M}

@[simp]
lemma map_comp (r : R) (g : M' →ₗ[R] M'') (f : M →ₗ[R] M') :
    map r (g ∘ₗ f) = map r g ∘ₗ map r f :=
  DFunLike.ext _ _ <| (mkQ_surjective _).forall.mpr fun _ => rfl

lemma equiv_lTensor_ring_mod_naturality_apply (r : R) (f : M →ₗ[R] M') (x : M) :
    equiv_lTensor_ring_mod M' r (map r f (Submodule.Quotient.mk x)) =
      f.lTensor (R⧸Ideal.span {r})
        (equiv_lTensor_ring_mod M r (Submodule.Quotient.mk x)) := by
  simp only [equiv_lTensor_ring_mod, map_apply_apply, LinearEquiv.trans_apply,
    quotEquivOfEq_mk, lTensor_ring_mod_ideal_equiv_mod_ideal_smul_symm_apply,
    LinearMap.lTensor_tmul]

lemma equiv_lTensor_ring_mod_naturality (r : R) (f : M →ₗ[R] M') :
    equiv_lTensor_ring_mod M' r ∘ₗ map r f =
      f.lTensor (R⧸Ideal.span {r}) ∘ₗ equiv_lTensor_ring_mod M r := by
  ext x; exact equiv_lTensor_ring_mod_naturality_apply r f x

lemma equiv_rTensor_ring_mod_naturality_apply (r : R) (f : M →ₗ[R] M') (x : M) :
    equiv_rTensor_ring_mod M' r (map r f (Submodule.Quotient.mk x)) =
      f.rTensor (R⧸Ideal.span {r})
        (equiv_rTensor_ring_mod M r (Submodule.Quotient.mk x)) := by
  simp only [equiv_rTensor_ring_mod, map_apply_apply, LinearEquiv.trans_apply,
    quotEquivOfEq_mk, rTensor_ring_mod_ideal_equiv_mod_ideal_smul_symm_apply,
    LinearMap.rTensor_tmul]

lemma equiv_rTensor_ring_mod_naturality (r : R) (f : M →ₗ[R] M') :
    equiv_rTensor_ring_mod M' r ∘ₗ map r f =
      f.rTensor (R⧸Ideal.span {r}) ∘ₗ equiv_rTensor_ring_mod M r := by
  ext x; exact equiv_rTensor_ring_mod_naturality_apply r f x

lemma map_surjective (r : R) {f : M →ₗ[R] M'} (hf : Surjective f) :
    Surjective (map r f) :=
  @Surjective.of_comp _ _ _ _ (mkQ (r • ⊤)) <|
    show Surjective ⇑(map r f ∘ₗ mkQ (r • ⊤)) from
    Eq.mpr (congrArg (Surjective ∘ DFunLike.coe) (liftQ_mkQ _ _ _)) <|
      (mkQ_surjective _).comp hf

lemma map_exact (r : R) {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Exact f g) (hg : Surjective g) : Exact (map r f) (map r g) :=
  (Exact.iff_of_ladder_linear_equiv (equiv_lTensor_ring_mod_naturality r f).symm
                             (equiv_lTensor_ring_mod_naturality r g).symm).mp
    (lTensor_exact (R⧸Ideal.span {r}) hfg hg)

-- Who knew this didn't rely on exactness at the right!?
open IsSMulRegular LinearMap in
lemma map_first_exact_on_four_term_exact_of_isSMulRegular_last {M₂ M₃}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    {r : R} {f₁ : M →ₗ[R] M'} {f₂ : M' →ₗ[R] M₂} {f₃ : M₂ →ₗ[R] M₃}
    (h₁₂ : Exact f₁ f₂) (h₂₃ : Exact f₂ f₃) (h : IsSMulRegular M₃ r) :
    Exact (map r f₁) (map r f₂) := by
  dsimp [map, mapQLinear]
  refine (Exact.descends_to_quotient_iff h₁₂ _ _).mpr ?_
  rw [map_element_smul, Submodule.map_top, inf_comm]
  refine smul_top_inf_eq_smul_of_isSMulRegular_on_quot ?_
  have := ker_liftQ_eq_bot' _ _ h₂₃.linearMap_ker_eq.symm
  exact h.isSMulRegular_of_injective_of_isSMulRegular _ <| ker_eq_bot.mp this

variable (M M')

open scoped TensorProduct

/-- Tensoring on the left and applying `ModSMulBy · r` commute. -/
noncomputable def lTensor_ModSMulBy_equiv_ModSMulBy (r : R) :
    M ⊗[R] ModSMulBy M' r ≃ₗ[R] ModSMulBy (M ⊗[R] M') r :=
  (equiv_rTensor_ring_mod M' r).lTensor M ≪≫ₗ
    (TensorProduct.assoc R M M' (R⧸Ideal.span {r})).symm ≪≫ₗ
      (equiv_rTensor_ring_mod (M ⊗[R] M') r).symm

/-- Tensoring on the right and applying `ModSMulBy · r` commute. -/
noncomputable def rTensor_ModSMulBy_equiv_ModSMulBy (r : R) :
    ModSMulBy M' r ⊗[R] M ≃ₗ[R] ModSMulBy (M' ⊗[R] M) r :=
  (equiv_lTensor_ring_mod M' r).rTensor M ≪≫ₗ
    TensorProduct.assoc R (R⧸Ideal.span {r}) M' M ≪≫ₗ
      (equiv_lTensor_ring_mod (M' ⊗[R] M) r).symm

end ModSMulBy

end
