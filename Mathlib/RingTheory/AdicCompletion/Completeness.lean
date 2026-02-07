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

/-!
# Completeness of the Adic Completion for Finitely Generated Ideals

This file establishes that `AdicCompletion I M` is itself `I`-adically complete
when the ideal `I` is finitely generated.

## Main definitions

* `AdicCompletion.powSmulTopInclusion`: The canonical inclusion between adic completions
  induced by the inclusion from `I ^ n • M` to `M`.

* `AdicCompletion.liftOfValZero`: Given `x` in `AdicCompletion I M` projecting to zero
  in `M / I ^ n • M`, `liftOfValZero` constructs the corresponding element in
  the adic completion of `I ^ m • M`.

## Main results

* `AdicCompletion.pow_smul_top_eq_eval_ker`: `I ^ n • AdicCompletion I M` is exactly the kernel
  of the evaluation map `eval I M n` when `I` is finitely generated.

* `AdicCompletion.IsAdicComplete`: `AdicCompletion I M` is `I`-adically complete if `I` is
  finitely generated.

-/

public section

noncomputable section

section preliminary

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

namespace Submodule

open Pointwise Classical in
theorem image_smul_top_eq_range_directSum {σ : Type*} (s : Set σ) (f : σ → R) :
    (f '' s • ⊤ : Submodule R M) =
      (DirectSum.toModule R s M (fun r ↦ LinearMap.lsmul R M (f r.val))).range := by
  refine Submodule.ext (fun m ↦ ⟨fun h ↦ LinearMap.mem_range.mpr ?_, fun ⟨c, h⟩ ↦ ?_⟩)
  · refine set_smul_inductionOn m h ?_ ?_ ?_ ⟨0, by simp⟩
    · rintro _ m ⟨i, i_in, rfl⟩ _
      use DirectSum.lof R s (fun (i : s) ↦ M) ⟨i, i_in⟩ m
      simp
    · intro r m m_in ⟨a, ha⟩
      use r • a; simp [ha]
    · intro m1 m2 _ _ ⟨a, ha⟩ ⟨b, hb⟩
      use a + b; simp [ha, hb]
  · rw [← h]; apply DirectSum.induction_lon (R := R) c
    · simp
    · intro ⟨r, r_in⟩ x
      simpa using mem_set_smul_of_mem_mem (Set.mem_image_of_mem _ r_in) mem_top
    · intro _ _ h h'
      simpa using add_mem h h'

open Pointwise Classical in
theorem smul_top_eq_range_directSum (s : Set R) : (s • ⊤ : Submodule R M) =
    (DirectSum.toModule R s M (fun r ↦ LinearMap.lsmul R M r.val)).range := by
  simpa using image_smul_top_eq_range_directSum (M := M) s id

variable (R) in
open scoped Pointwise in
theorem smul_top_eq_restrictScalars_image_smul_top {S : Type*} [CommSemiring S] [Module S M]
    [Algebra S R] [IsScalarTower S R M] (s : Set S) : (s • ⊤ : Submodule S M) =
        ((algebraMap S R) '' s • ⊤ : Submodule R M).restrictScalars S := by
  refine le_antisymm (set_smul_le _ _ _ fun r x r_in _ ↦ ?_) ?_
  · rw [restrictScalars_mem, ← IsScalarTower.algebraMap_smul R r]
    exact mem_set_smul_of_mem_mem (Set.mem_image_of_mem _ r_in) mem_top
  intro x x_in
  rw [restrictScalars_mem] at x_in
  refine set_smul_inductionOn x x_in ?_ ?_ (fun _ _ _ _ h h' ↦  add_mem h h') (zero_mem _)
  · rintro _ x ⟨r, r_in, rfl⟩ _
    rw [IsScalarTower.algebraMap_smul R r]
    exact mem_set_smul_of_mem_mem r_in mem_top
  · intro r x h h'
    obtain ⟨c, c_supp, hc⟩ := (mem_set_smul ..).mp <| smul_mem _ r h
    simp only [hc, Finsupp.sum, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    refine sum_mem fun u u_in ↦ ?_
    obtain ⟨u, u_in', rfl⟩ := c_supp (Finset.mem_coe.mpr u_in)
    rw [IsScalarTower.algebraMap_smul]
    exact mem_set_smul_of_mem_mem u_in' mem_top

end Submodule

end preliminary

section completeness

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]

namespace AdicCompletion

open Submodule

variable (M) in
/-- The canonical inclusion from the adic completion of `I ^ n • M` to
the adic completion of `M`. -/
def powSmulTopInclusion (n : ℕ) := (AdicCompletion.map I (topEquiv.toLinearMap ∘ₗ
    ((I ^ n • (⊤ : Submodule R M)).inclusion le_top)))

theorem powSmulTopInclusion_val_apply {a b c : ℕ} (h : c = a + b)
    {x : AdicCompletion I ↥(I ^ a • ⊤ : Submodule R M)} : (powSmulTopInclusion I M a x).val c =
      powSmulQuotInclusion I M h (x.val b) := by
  rw [← x.prop (show b ≤ c by lia), powSmulTopInclusion, map_val_apply]
  refine Quotient.induction_on _ (x.val c) fun z ↦ ?_
  simp [powSmulQuotInclusion]

theorem powSmulTopInclusion_val_apply_eq_zero {n i : ℕ} (h : i ≤ n)
    {x : AdicCompletion I ↥(I ^ n • ⊤ : Submodule R M)} :
      (powSmulTopInclusion I M n x).val i = 0 := by
  rw [powSmulTopInclusion, map_val_apply]
  refine Quotient.induction_on _ (x.val i) fun z ↦ ?_
  simpa using pow_smul_top_le _ _ h z.prop

theorem powSmulTopInclusion_injective (n : ℕ) :
    Function.Injective (powSmulTopInclusion I M n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx; ext i
  simp only [AdicCompletion.ext_iff, val_zero, Pi.zero_apply] at hx
  specialize hx (i + n)
  rw [powSmulTopInclusion_val_apply I (by rw [add_comm]),
    LinearMap.map_eq_zero_iff _ (powSmulQuotInclusion_injective ..)] at hx
  simp [hx]

private lemma liftOfValZeroAux_exists {a b c : ℕ} {x : AdicCompletion I M} (h : c = a + b)
    (ha : x.val a = 0) : ∃ t, powSmulQuotInclusion I M h t = x.val c := by
  simpa [← LinearMap.mem_range, powSmulQuotInclusion_range] using
    (val_apply_mem_smul_top_iff I (show a ≤ c by lia)).mpr ha

/-- An auxillary lift function used in the definition of `liftOfValZero`.
Use `liftOfValZero` instead. -/
def liftOfValZeroAux {a b c : ℕ} {x : AdicCompletion I M} (h : c = a + b) (ha : x.val a = 0) :
    ↥(I ^ a • ⊤ : Submodule R M) ⧸ I ^ b • (⊤ : Submodule R ↥(I ^ a • ⊤ : Submodule R M)) :=
  Exists.choose (liftOfValZeroAux_exists I h ha)

private lemma liftOfValZeroAux_prop {a b c : ℕ} {x : AdicCompletion I M} (h : c = a + b)
    (ha : x.val a = 0) : (powSmulQuotInclusion I M h) (liftOfValZeroAux I h ha) = x.val c :=
  Exists.choose_spec (liftOfValZeroAux_exists I h ha)

/-- Given an element `x` in the adic completion of `M` whose projection to `M / I ^ n • M` is zero,
`liftOfValZero` constructs the corresponding element in the adic completion of `I ^ n • M`. -/
@[no_expose]
def liftOfValZero {n : ℕ} {x : AdicCompletion I M} (hxn : x.val n = 0) :
    AdicCompletion I ↥(I ^ n • (⊤ : Submodule R M)) where
  val i := liftOfValZeroAux I (Eq.refl (n + i)) hxn
  property {i j} h := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← (powSmulQuotInclusion_injective I (by rfl)).eq_iff, liftOfValZeroAux_prop,
      ← LinearMap.comp_apply, ← factorPow_powSmulQuotInclusion_comm I (by rfl)
      (show n + (i + k) = n + i + k by ring), LinearMap.comp_apply, liftOfValZeroAux_prop]
    exact x.prop (by lia)

@[simp]
theorem powSmulTopInclusion_liftOfValZero_apply {n : ℕ} {x : AdicCompletion I M}
    (hxn : x.val n = 0) : powSmulTopInclusion I M n (liftOfValZero I hxn) = x := by
  ext i; by_cases h : n ≤ i
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [powSmulTopInclusion_val_apply _ (by rfl), liftOfValZero, liftOfValZeroAux_prop]
  replace h : i ≤ n := by lia
  rw [powSmulTopInclusion_val_apply_eq_zero _ h, ← x.prop h, hxn, _root_.map_zero]

theorem powSmulTopInclusion_range_eq_eval_ker {n : ℕ} :
    (powSmulTopInclusion I M n).range.restrictScalars R = (eval I M n).ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases hx with ⟨y, rfl⟩
    rw [LinearMap.mem_ker, eval_apply, powSmulTopInclusion_val_apply_eq_zero _ (by rfl)]
  simp only [LinearMap.mem_ker, coe_eval] at hx
  use liftOfValZero I hx; simp

theorem map_toModule_sum_eq_toModule_map {ι N : Type*} (P : ι → Type*) [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] [AddCommGroup N] [Module R N] (φ : ∀ i, P i →ₗ[R] N)
      [DecidableEq ι] : (map I (DirectSum.toModule R ι N φ)) ∘ₗ (sum I P) =
        DirectSum.toModule (AdicCompletion I R) ι (AdicCompletion I N) (fun i ↦ map I (φ i)) := by
  ext; simp

theorem map_lsmul_eq_lsmul_of (r : R) : map I (LinearMap.lsmul R M r) =
    LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) (of I R r) := by rfl

variable {I} in
@[stacks 05GG "(2)"]
theorem pow_smul_top_eq_eval_ker {n : ℕ} (h : I.FG) : I ^ n • ⊤ = (eval I M n).ker := by
  classical
  refine le_antisymm (pow_smul_top_le_eval_ker ..) ?_
  replace h := Ideal.FG.pow (n := n) h
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [smul_top_eq_restrictScalars_image_smul_top (AdicCompletion I R), show
    ⇑(algebraMap R (AdicCompletion I R)) = of I R by rfl, ← powSmulTopInclusion_range_eq_eval_ker,
    restrictScalars_le, image_smul_top_eq_range_directSum]
  simp only [SetLike.coe_sort_coe, ← map_lsmul_eq_lsmul_of, ← map_toModule_sum_eq_toModule_map]
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
    Function.RightInverse.surjective (g := sumInv I fun i ↦ M) (fun _ ↦ by
      rw [← LinearMap.comp_apply, sum_comp_sumInv, LinearMap.id_apply]))]
  rintro _ ⟨x, rfl⟩
  have : Function.Surjective ((DirectSum.toModule R s M fun r ↦ LinearMap.lsmul R M r).codRestrict
    (I ^ n • ⊤) (fun _ ↦ by simp [← hs, span_smul_eq, smul_top_eq_range_directSum])) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, ← hs, span_smul_eq,
      smul_top_eq_range_directSum]
    simp
  rcases map_surjective I this x with ⟨u, rfl⟩
  exact ⟨u, by rw [powSmulTopInclusion, ← LinearMap.comp_apply, map_comp]; rfl⟩

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

end completeness
