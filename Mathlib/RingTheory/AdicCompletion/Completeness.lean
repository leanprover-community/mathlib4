/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Data.Finsupp.Pointwise

/-!
# Completeness of the Adic Completion for Finitely Generated Ideals

This file establishes that `AdicCompletion I M` is itself `I`-adically complete
when the ideal `I` is finitely generated.

## Main definitions

* `AdicCompletion.ofPowSmul`: The canonical inclusion between adic completions
  induced by the inclusion from `I ^ n • M` to `M`.

* `AdicCompletion.liftOfValZero`: Given `x` in `AdicCompletion I M` projecting to zero
  in `M / I ^ n • M`, `liftOfValZero` constructs the corresponding element in
  the adic completion of `I ^ m • M`.

## Main results

* `AdicCompletion.pow_smul_top_eq_eval_ker`: `I ^ n • AdicCompletion I M` is exactly the kernel
  of the evaluation map `eval I M n` when `I` is finitely generated.

* `AdicCompletion.isAdicComplete`: `AdicCompletion I M` is `I`-adically complete if `I` is
  finitely generated.

-/

public section

noncomputable section

open Submodule Finsupp

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]

namespace AdicCompletion

variable (M) in
/-- The canonical inclusion from the adic completion of `I ^ n • M` to
the adic completion of `M`. -/
def ofPowSmul (n : ℕ) : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)
    →ₗ[AdicCompletion I R] AdicCompletion I M := map I (I ^ n • ⊤ : Submodule R M).subtype

theorem ofPowSmul_val_apply {a b c : ℕ} (h : c = b + a)
    {x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)} : (ofPowSmul I M a x).val c =
      powSmulQuotInclusion I M h ⊤ (x.val b) := by
  rw [← x.prop (show b ≤ c by lia), ofPowSmul, map_val_apply]
  refine Quotient.induction_on _ (x.val c) fun z ↦ ?_
  simp [powSmulQuotInclusion]

theorem ofPowSmul_val_apply_eq_zero {n i : ℕ} (h : i ≤ n)
    {x : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)} : (ofPowSmul I M n x).val i = 0 := by
  rw [ofPowSmul, map_val_apply]
  refine Quotient.induction_on _ (x.val i) fun z ↦ ?_
  simpa using pow_smul_top_le _ _ h z.prop

theorem ofPowSmul_injective (n : ℕ) : Function.Injective (ofPowSmul I M n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [ofPowSmul_val_apply I (by rw [add_comm]),
    LinearMap.map_eq_zero_iff _ (powSmulQuotInclusion_injective ..)] at hx
  simp [hx]

private lemma liftOfValZeroAux_exists {a b c : ℕ} {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : ∃ t, powSmulQuotInclusion I M h ⊤ t = x.val c := by
  simpa [← LinearMap.mem_range, powSmulQuotInclusion_range] using
    (val_apply_mem_smul_top_iff I (show a ≤ c by lia)).mpr ha

/-- An auxillary lift function used in the definition of `liftOfValZero`.
Use `liftOfValZero` instead. -/
def liftOfValZeroAux {a b c : ℕ} {x : AdicCompletion I M} (h : c = b + a) (ha : x.val a = 0) :
    ↥(I ^ a • ⊤ : Submodule R M) ⧸ I ^ b • (⊤ : Submodule R ↥(I ^ a • ⊤ : Submodule R M)) :=
  Exists.choose (liftOfValZeroAux_exists I h ha)

private lemma liftOfValZeroAux_prop {a b c : ℕ} {x : AdicCompletion I M} (h : c = b + a)
    (ha : x.val a = 0) : (powSmulQuotInclusion I M h ⊤) (liftOfValZeroAux I h ha) = x.val c :=
  Exists.choose_spec (liftOfValZeroAux_exists I h ha)

/-- Given an element `x` in the adic completion of `M` whose projection to `M / I ^ n • M` is zero,
`liftOfValZero` constructs the corresponding element in the adic completion of `I ^ n • M`. -/
@[no_expose]
def liftOfValZero {n : ℕ} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    AdicCompletion I ↥(I ^ n • (⊤ : Submodule R M)) where
  val i := liftOfValZeroAux I (Eq.refl (i + n)) hxn
  property {i j} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← (powSmulQuotInclusion_injective I (by rfl) ⊤).eq_iff, liftOfValZeroAux_prop,
      ← LinearMap.comp_apply, ← factorPow_powSmulQuotInclusion_comm I (by rfl)
      (show i + k + n = k + (i + n) by ring), LinearMap.comp_apply, liftOfValZeroAux_prop]
    exact x.prop (by lia)

@[simp]
theorem ofPowSmul_liftOfValZero {n : ℕ} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    ofPowSmul I M n (liftOfValZero I hxn) = x := by
  ext i; by_cases h : n ≤ i
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [ofPowSmul_val_apply _ (by rfl), liftOfValZero, liftOfValZeroAux_prop]
  replace h : i ≤ n := by lia
  rw [ofPowSmul_val_apply_eq_zero _ h, ← x.prop h, hxn, _root_.map_zero]

theorem restrictScalars_ofPowSmul_range_eq_eval_ker {n : ℕ} :
    (ofPowSmul I M n).range.restrictScalars R = (eval I M n).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker, eval_apply, ofPowSmul_val_apply_eq_zero _ (by rfl)]
  simp only [LinearMap.mem_ker, coe_eval] at hx
  use liftOfValZero I hx; simp

lemma map_lsum_comp_finsuppSum_eq_lsum_map {ι : Type*} (f : ι → R) :
    map I (lsum R fun i ↦ f i • .id) ∘ₗ (finsupp_sum ι I M) =
      (lsum (AdicCompletion I R)) fun i ↦ ((of I R) (f i) • .id :
    AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I M) := by
  ext
  -- simp [finsupp_sum]
  simp only [finsupp_sum, LinearMap.coe_comp, coe_lsum, Function.comp_apply, lsingle_apply,
    _root_.map_zero, sum_single_index, map_mk, mk_apply_coe, AdicCauchySequence.map_apply_coe,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul, mkQ_apply, lsum_comp_lsingle,
    smul_eval, smul_eq_mul, of_apply, Ideal.Quotient.mk_eq_mk]
  rfl

variable {I} in
@[stacks 05GG "(2)"]
theorem pow_smul_top_eq_eval_ker {n : ℕ} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker := by
  classical
  refine le_antisymm (pow_smul_top_le_eval_ker ..) ?_
  replace h := Ideal.FG.pow (n := n) h
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M),
    ← restrictScalars_image_smul_eq_smul_restrictScalars (R := AdicCompletion I R), show
    ⇑(algebraMap R (AdicCompletion I R)) = of I R by rfl,
    ← restrictScalars_ofPowSmul_range_eq_eval_ker, restrictScalars_le,
    image_smul_top_eq_range_lsum]
  simp only [SetLike.coe_sort_coe, ← map_lsum_comp_finsuppSum_eq_lsum_map]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
    Function.RightInverse.surjective (g := finsupp_sumInv ..) (fun _ ↦ by
      rw [← LinearMap.comp_apply, finsupp_sum_comp_sumInv, LinearMap.id_apply]))]
  rintro _ ⟨x, rfl⟩
  have : Function.Surjective ((lsum R fun i : s ↦ i.val • (LinearMap.id : M →ₗ[R] M)).codRestrict
    (I ^ n • ⊤) (fun _ ↦ by simp [← hs, span_smul_eq, smul_top_eq_range_lsum])) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, ← hs, span_smul_eq,
      smul_top_eq_range_lsum]
    simp
  rcases map_surjective I this x with ⟨x, rfl⟩
  exact ⟨x, by rw [ofPowSmul, ← LinearMap.comp_apply, map_comp]; rfl⟩

variable {I} in
/-- `AdicCompletion I M` is adic complete when `I` is finitely generated. -/
theorem isAdicComplete (h : I.FG) : IsAdicComplete I (AdicCompletion I M) where
  prec' x hx := by
    let L : AdicCompletion I M := {
      val i := (x i).val i
      property {m n} h' := by
        simp only [transitionMap_comp_eval_apply]
        specialize hx h'
        rwa [SModEq.sub_mem, pow_smul_top_eq_eval_ker h, LinearMap.mem_ker, _root_.map_sub,
          sub_eq_zero, eval_apply, eval_apply, eq_comm] at hx
    }
    use L; intro i
    rw [SModEq.sub_mem, pow_smul_top_eq_eval_ker h]
    simp [L]

end AdicCompletion
