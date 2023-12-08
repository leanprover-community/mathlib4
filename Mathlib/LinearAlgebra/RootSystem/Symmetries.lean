/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.RootSystem.FindHome

/-!
# Symmetries and reflections

Hmm, does this definitely belong in the `RootSystem` directory? Maybe could go one level up?

## Implementation details

Explain point is that we don't assume existence of inner product

## TODO

Show symmetries arise from inner product spaces

-/

open Set Function Pointwise
open Module hiding Finite
open Submodule (span)

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- TODO -/
def toPreSymmetry (x : M) (f : Dual R M) : End R M :=
  LinearMap.id - dualTensorHom R M M (f ⊗ₜ x)

lemma toPreSymmetry_apply (x y : M) (f : Dual R M) :
    toPreSymmetry x f y = y - (f y) • x := by
  simp [toPreSymmetry]

lemma toPreSymmetry_apply_self {x : M} {f : Dual R M} (h : f x = 2) :
    toPreSymmetry x f x = - x := by
  rw [toPreSymmetry_apply, h, two_smul]; abel

lemma involutive_toPreSymmetry {x : M} {f : Dual R M} (h : f x = 2) :
    Involutive (toPreSymmetry x f) :=
  fun y ↦ by simp [h, smul_sub, two_smul, toPreSymmetry_apply]

/-- TODO -/
def toSymmetry {x : M} {f : Dual R M} (h : f x = 2) : M ≃ₗ[R] M :=
  LinearEquiv.ofBijective (toPreSymmetry x f) (involutive_toPreSymmetry h).bijective

lemma toSymmetry_apply {x : M} (y : M) {f : Dual R M} (h : f x = 2) :
    toSymmetry h y = y - (f y) • x :=
  toPreSymmetry_apply x y f

lemma toSymmetry_apply_self {x : M} {f : Dual R M} (h : f x = 2) :
    toSymmetry h x = - x :=
  toPreSymmetry_apply_self h

lemma LinearEquiv.apply_toPreSymmetry {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (x : M) (f : Dual R M) :
    e ∘ₗ toPreSymmetry x f = toPreSymmetry (e x) (e.symm.dualMap f) ∘ₗ e := by
  ext; simp [toPreSymmetry_apply]

lemma toPreSymmetry_toPreSymmetry (a b : M) (f g : Dual R M) (h : f a = 2) :
    toPreSymmetry (toPreSymmetry a f b) (toPreSymmetry f (Dual.eval R M a) g) =
    (toPreSymmetry a f) ∘ₗ (toPreSymmetry b g) ∘ₗ (toPreSymmetry a f) := by
  ext m
  simp only [h, toPreSymmetry_apply, mul_comm (g a) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

lemma eq_of_toPreSymmetry_image_eq [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0)
    {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤)
    {f g : Dual R M} (hf₁ : f x = 2) (hf₂ : toPreSymmetry x f '' Φ = Φ)
                     (hg₁ : g x = 2) (hg₂ : toPreSymmetry x g '' Φ = Φ) :
    f = g := by
  let u := toSymmetry hg₁ * toSymmetry hf₁
  suffices IsOfFinOrder u by
    have hu : u = LinearMap.id (R := R) (M := M) + dualTensorHom R M M ((f - g) ⊗ₜ x) := by
      ext y
      simp only [toSymmetry, LinearEquiv.coe_mul, LinearMap.mul_apply, LinearEquiv.coe_coe,
        LinearEquiv.ofBijective_apply, toPreSymmetry_apply, map_sub, map_smul, hg₁, two_smul,
        sub_add_cancel', smul_neg, sub_neg_eq_add, LinearMap.add_apply, LinearMap.id_coe, id.def,
        dualTensorHom_apply, LinearMap.sub_apply, sub_smul]
      abel
    replace hu : ∀ (n : ℕ), ↑(u^n) = LinearMap.id (R := R) (M := M) + (n : R) • dualTensorHom R M M ((f - g) ⊗ₜ x) := by
      intros n
      induction' n with n ih; simp
      have aux : (dualTensorHom R M M ((f - g) ⊗ₜ[R] x)).comp
        ((n : R) • dualTensorHom R M M ((f - g) ⊗ₜ[R] x)) = 0 := by ext v; simp [hf₁, hg₁]
      rw [pow_succ, LinearEquiv.coe_mul, ih, hu, add_mul, mul_add, mul_add]
      simp only [LinearMap.mul_eq_comp, LinearMap.id_comp, LinearMap.comp_id, Nat.cast_succ,
        aux, add_zero, add_smul, one_smul, add_assoc]
    obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp this
    replace hn₁ : (↑(u ^ n) : M →ₗ[R] M) = LinearMap.id := LinearEquiv.toLinearMap_inj.mpr hn₁
    simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hu n
  suffices IsOfFinOrder u.toLinearMap by
    have hf : Injective (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := R) (M := M)) :=
      LinearEquiv.toLinearMap_injective
    exact hf.isOfFinOrder_iff.mp this
  refine isOfFinOrder_of_finite_of_span_eq_top_of_image_eq hΦ₁ hΦ₂ ?_
  change (toPreSymmetry x g ∘ toPreSymmetry x f '' Φ) = Φ
  rw [image_comp, hf₂, hg₂]

-- TODO Replace the lemma above with this (more generally use `⊆` instead of `=` in corresponding
-- hypotheses across all relevant lemmas)
lemma eq_of_toPreSymmetry_image_eq_fixed [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0)
    {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤)
    {f g : Dual R M} (hf₁ : f x = 2) (hf₂ : toPreSymmetry x f '' Φ ⊆ Φ)
                     (hg₁ : g x = 2) (hg₂ : toPreSymmetry x g '' Φ ⊆ Φ) :
    f = g := by
  change (toSymmetry hf₁).toEquiv '' Φ ⊆ Φ at hf₂
  rw [← hΦ₁.equiv_image_eq_iff_subset] at hf₂
  change (toSymmetry hg₁).toEquiv '' Φ ⊆ Φ at hg₂
  rw [← hΦ₁.equiv_image_eq_iff_subset] at hg₂
  exact eq_of_toPreSymmetry_image_eq hx hΦ₁ hΦ₂ hf₁ hf₂ hg₁ hg₂

lemma eq_of_toPreSymmetry_image_eq' [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0)
    {Φ : Set M} (hΦ₁ : Φ.Finite) (hx' : x ∈ span R Φ)
    {f g : Dual R M} (hf₁ : f x = 2) (hf₂ : toPreSymmetry x f '' Φ = Φ)
                     (hg₁ : g x = 2) (hg₂ : toPreSymmetry x g '' Φ = Φ) :
    (span R Φ).subtype.dualMap f = (span R Φ).subtype.dualMap g := by
  let Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  have hΦ'₁ : Φ'.Finite := by
    rw [← finite_coe_iff] at hΦ₁; exact finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by simp
  let x' : span R Φ := ⟨x, hx'⟩
  have hx' : x' ≠ 0 := Subtype.ne_of_val_ne hx
  let f' := (span R Φ).subtype.dualMap f
  let g' := (span R Φ).subtype.dualMap g
  replace hf₂ : toPreSymmetry x' f' '' Φ' = Φ' := by
    ext ⟨y, hy⟩
    -- Fix (and abstract) this 🤢🤮 proof
    simp only [toPreSymmetry_apply, LinearMap.dualMap_apply, Submodule.coeSubtype,
      SetLike.mk_smul_mk, range_inclusion, SetLike.coe_sort_coe, mem_image, mem_setOf_eq,
      Subtype.exists, exists_and_left]
    simp_rw [Subtype.ext_iff]
    simp only [AddSubgroupClass.coe_sub, exists_prop]
    simp_rw [← toPreSymmetry_apply]
    conv_rhs => rw [← hf₂]
    simp only [mem_image]
    refine exists_congr fun z ↦ ?_
    simp only [and_congr_right_iff, and_iff_right_iff_imp]
    exact fun hz _ ↦ Submodule.subset_span hz
  replace hg₂ : toPreSymmetry x' g' '' Φ' = Φ' := by
    ext ⟨y, hy⟩
    -- Fix (and abstract) this 🤢🤮 proof
    simp only [toPreSymmetry_apply, LinearMap.dualMap_apply, Submodule.coeSubtype,
      SetLike.mk_smul_mk, range_inclusion, SetLike.coe_sort_coe, mem_image, mem_setOf_eq,
      Subtype.exists, exists_and_left]
    simp_rw [Subtype.ext_iff]
    simp only [AddSubgroupClass.coe_sub, exists_prop]
    simp_rw [← toPreSymmetry_apply]
    conv_rhs => rw [← hg₂]
    simp only [mem_image]
    refine exists_congr fun z ↦ ?_
    simp only [and_congr_right_iff, and_iff_right_iff_imp]
    exact fun hz _ ↦ Submodule.subset_span hz
  exact eq_of_toPreSymmetry_image_eq hx' hΦ'₁ hΦ'₂ (f := f') (g := g') hf₁ hf₂ hg₁ hg₂
