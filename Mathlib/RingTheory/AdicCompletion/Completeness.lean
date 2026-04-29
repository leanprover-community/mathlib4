/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Completeness of the Adic Completion for Finitely Generated Ideals

This file establishes that `AdicCompletion I M` is itself `I`-adically complete
when the ideal `I` is finitely generated.

## Main definitions

* `AdicCompletion.ofPowSMul`: The canonical inclusion between adic completions
  induced by the inclusion from `I ^ n • M` to `M`.

* `AdicCompletion.ofValEqZero`: Given `x` in `AdicCompletion I M` projecting to zero
  in `M / I ^ n • M`, `ofValEqZero` constructs the corresponding element in
  the adic completion of `I ^ n • M`.

## Main results

* `AdicCompletion.pow_smul_top_eq_ker_eval`: `I ^ n • AdicCompletion I M` is exactly the kernel
  of the evaluation map `eval I M n` when `I` is finitely generated.

* `AdicCompletion.isAdicComplete`: `AdicCompletion I M` is `I`-adically complete if `I` is
  finitely generated.

* `MvPowerSeries.isAdicComplete`: Multivariate power series is adic complete with respect to
  the ideal spanned by all variables when the index is finite.

-/

public section

noncomputable section

open Submodule Finsupp

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {a b c : ℕ}

namespace AdicCompletion

variable (M) in
/-- The canonical inclusion from the adic completion of `I ^ n • M` to
the adic completion of `M`. -/
abbrev ofPowSMul (n : ℕ) : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)
    →ₗ[AdicCompletion I R] AdicCompletion I M := map I (I ^ n • ⊤ : Submodule R M).subtype

theorem ofPowSMul_val_apply (h : c = b + a) {x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)} :
    (ofPowSMul I M a x).val c = powSMulQuotInclusion I M h ⊤ (x.val b) := by
  rw [← x.prop (show b ≤ c by lia), map_val_apply]
  refine Quotient.induction_on _ (x.val c) fun z ↦ ?_
  simp [powSMulQuotInclusion]

theorem ofPowSMul_val_apply_eq_zero (h : a ≤ b)
    {x : AdicCompletion I ↥(I ^ b • ⊤ : Submodule R M)} : (ofPowSMul I M b x).val a = 0 := by
  rw [map_val_apply]
  refine Quotient.induction_on _ (x.val a) fun z ↦ ?_
  simpa using pow_smul_top_le _ _ h z.prop

theorem ofPowSMul_injective (n : ℕ) : Function.Injective (ofPowSMul I M n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [ofPowSMul_val_apply I (by rw [add_comm]),
    LinearMap.map_eq_zero_iff _ (powSMulQuotInclusion_injective ..)] at hx
  simp [hx]

private lemma ofValEqZeroAux_exists {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : ∃ t, powSMulQuotInclusion I M h ⊤ t = x.val c := by
  simpa [← LinearMap.mem_range, range_powSMulQuotInclusion] using
    (val_apply_mem_smul_top_iff I (show a ≤ c by lia)).mpr ha

/-- An auxiliary lift function used in the definition of `ofValEqZero`.
Use `ofValEqZero` instead. -/
def ofValEqZeroAux {x : AdicCompletion I M} (h : c = b + a) (ha : x.val a = 0) :
    ↥(I ^ a • ⊤ : Submodule R M) ⧸ I ^ b • (⊤ : Submodule R ↥(I ^ a • ⊤ : Submodule R M)) :=
  Exists.choose (ofValEqZeroAux_exists I h ha)

private lemma ofValEqZeroAux_prop {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : (powSMulQuotInclusion I M h ⊤) (ofValEqZeroAux I h ha) = x.val c :=
  Exists.choose_spec (ofValEqZeroAux_exists I h ha)

/-- Given an element `x` in the adic completion of `M` whose projection to `M / I ^ n • M` is zero,
`ofValEqZero` constructs the corresponding element in the adic completion of `I ^ n • M`. -/
@[no_expose]
def ofValEqZero {n : ℕ} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    AdicCompletion I ↥(I ^ n • (⊤ : Submodule R M)) where
  val i := ofValEqZeroAux I (Eq.refl (i + n)) hxn
  property {i j} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← (powSMulQuotInclusion_injective I (by rfl) ⊤).eq_iff, ofValEqZeroAux_prop,
      ← LinearMap.comp_apply, ← factorPow_comp_powSMulQuotInclusion I (by rfl)
      (show i + k + n = k + (i + n) by ring), LinearMap.comp_apply, ofValEqZeroAux_prop]
    exact x.prop (by lia)

@[simp]
theorem ofPowSMul_ofValEqZero {n : ℕ} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    ofPowSMul I M n (ofValEqZero I hxn) = x := by
  ext i; by_cases! h : n ≤ i
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [ofPowSMul_val_apply _ (by rfl), ofValEqZero, ofValEqZeroAux_prop]
  rw [ofPowSMul_val_apply_eq_zero _ h.le, ← x.prop h.le, hxn, _root_.map_zero]

theorem restrictScalars_range_ofPowSMul_eq_ker_eval {n : ℕ} :
    (ofPowSMul I M n).range.restrictScalars R = (eval I M n).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker, eval_apply, ofPowSMul_val_apply_eq_zero _ (by rfl)]
  simp only [LinearMap.mem_ker, coe_eval] at hx
  use ofValEqZero I hx; simp

/- An intermediate helper lemma for the theorem below to avoid introducing
`AdicCompletion.finsuppSum` (the `Finsupp` version of `AdicCompletion.sum`).
It proves the equality of two linear maps:

The LHS evaluates a linear combination with coefficients `f i` on
the direct sum of the completed modules `AdicCompletion I M`.

The RHS first commutes the direct sum and the completion via `sumEquivOfFintype`,
and then applies the completion of the standard linear combination operator on `M`. -/
private lemma lsum_smul_comp_finsuppLEquivDirectSum_symm {ι : Type*} [DecidableEq ι] [Fintype ι]
    (f : ι → R) : ((lsum (AdicCompletion I R))
      fun i ↦ ((algebraMap R (AdicCompletion I R)) (f i) • .id :
        AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I M)) ∘ₗ
      (finsuppLEquivDirectSum (AdicCompletion I R) (AdicCompletion I M) ι).symm.toLinearMap =
    (map I (lsum R fun i ↦ f i • .id) ∘ₗ map I (finsuppLEquivDirectSum R M ι).symm.toLinearMap) ∘ₗ
      (sumEquivOfFintype I (fun _ : ι ↦ M)) := by
  ext
  -- simp [-algebraMap_smul, algebraMap_apply, -smul_eq_mul]
  simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, LinearMap.coe_comp,
    coe_lsum, LinearMap.coe_smul, LinearMap.id_coe, LinearEquiv.coe_coe, Function.comp_apply,
    finsuppLEquivDirectSum_symm_lof, Pi.smul_apply, id_eq, smul_zero, sum_single_index, smul_eval,
    mapQ_eq_factor, factor_eq_factor, of_apply, mkQ_apply, Ideal.Quotient.mk_eq_mk, mk_apply_coe,
    sumEquivOfFintype_apply, sum_lof, map_mk, AdicCauchySequence.map_apply_coe, map_smul]
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]

variable {I} in
@[stacks 05GG "(2)"]
theorem pow_smul_top_eq_ker_eval {n : ℕ} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker := by
  classical
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  replace h := Ideal.FG.pow (n := n) h
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M),
    ← restrictScalars_image_smul_eq (R := AdicCompletion I R),
    ← restrictScalars_range_ofPowSMul_eq_ker_eval, restrictScalars_le,
    image_smul_top_eq_range_lsum]
  simp only [SetLike.coe_sort_coe]
  rw [← LinearMap.range_comp_of_range_eq_top (f := (finsuppLEquivDirectSum ..).symm.toLinearMap)
    _ (by simp), lsum_smul_comp_finsuppLEquivDirectSum_symm,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
      Function.RightInverse.surjective (g := map I (finsuppLEquivDirectSum R M s)) (fun _ ↦ by
      simp [← LinearMap.comp_apply, map_comp]))]
  rintro _ ⟨x, rfl⟩
  have : Function.Surjective ((lsum R fun i : s ↦ i.val • (LinearMap.id : M →ₗ[R] M)).codRestrict
    (I ^ n • ⊤) (fun _ ↦ by simp [← hs, span_smul_eq, smul_top_eq_range_lsum])) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, ← hs, span_smul_eq,
      smul_top_eq_range_lsum]
    simp
  rcases map_surjective I this x with ⟨x, rfl⟩
  exact ⟨x, by rw [← LinearMap.comp_apply, map_comp, LinearMap.subtype_comp_codRestrict]⟩

variable {I} in
/-- `AdicCompletion I M` is adic complete when `I` is finitely generated. -/
@[stacks 05GG "(1)"]
theorem isAdicComplete (h : I.FG) : IsAdicComplete I (AdicCompletion I M) where
  prec' x hx := by
    let L : AdicCompletion I M := {
      val i := (x i).val i
      property {m n} h' := by
        simp only [transitionMap_comp_eval_apply]
        specialize hx h'
        rwa [SModEq.sub_mem, pow_smul_top_eq_ker_eval h, LinearMap.mem_ker, _root_.map_sub,
          sub_eq_zero, eval_apply, eval_apply, eq_comm] at hx
    }
    use L; intro i
    rw [SModEq.sub_mem, pow_smul_top_eq_ker_eval h]
    simp [L]

end AdicCompletion

namespace MvPowerSeries

instance {σ : Type*} [Finite σ] :
    IsAdicComplete (.span (.range X) : Ideal (MvPowerSeries σ R)) (MvPowerSeries σ R) := by
  have : Ideal.map (toAdicCompletionAlgEquiv σ R).toRingEquiv (Ideal.span (Set.range X)) =
    (MvPolynomial.idealOfVars σ R).map (algebraMap ..):= by
    simp_rw [Ideal.map_span, ← Set.range_comp]
    congr 2; ext1
    simp [AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X, toAdicCompletion_coe]
  rw [← IsAdicComplete.congr_ringEquiv _ (toAdicCompletionAlgEquiv σ R).toRingEquiv, this,
    IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (MvPolynomial.idealOfVars_fg σ R)

end MvPowerSeries

namespace PowerSeries

instance : IsAdicComplete (.span {X} : Ideal (PowerSeries R)) (PowerSeries R) := by
  have : IsAdicComplete (.span (.range MvPowerSeries.X) : Ideal (MvPowerSeries Unit R))
    (MvPowerSeries Unit R) := inferInstance
  rwa [Set.range_unique] at this

end PowerSeries
