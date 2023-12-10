/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.RootSystem.FindHome

/-!
# Reflections in linear algebra

Given an element `x` in a module `M` together with a linear form `f` on `M` such that `f x = 2`, the
map `y ↦ y - (f y) • x` is an involutive endomorphism of `M`, such that:
 1. the kernel of `f` is fixed,
 2. the point `x ↦ -x`.

Such endomorphisms are often called reflections of the module `M`. When `M` carries a inner product
for which `x` is perpendicular to the kernel of `f`, then (with mild assumptions) the endomorphism
is characterised by properties 1 and 2 above, and is a linear isometry.

## Main definitions / results:

 * `Module.preReflection`: the definition of the map `y ↦ y - (f y) • x`. Its main utility lies in
   the fact that it does not require the assumption `f x = 2`, giving the user freedom to defer
   discharging this proof obligation.
 * `Module.reflection`: the definition of the map `y ↦ y - (f y) • x`. This requires the assumption
   that `f x = 2` but by way of compensation it produces a linear equivalence rather than a mere
   linear map.
 * `Module.Dual.eq_of_preReflection_image_subset`: a uniqueness result about reflections preserving
   finite spanning sets that is useful in the theory of root data / systems.

## TODO

Related definitions of reflection exists elsewhere in the library. These more specialised
definitions, which require an ambient `InnerProductSpace` structure, are `reflection` (of type
`LinearIsometryEquiv`) and `EuclideanGeometry.reflection` (of type `AffineIsometryEquiv`). We
should connect (or unify) these definitions with `Module.reflecton` defined here.

-/

open Set Function Pointwise
open Module hiding Finite
open Submodule (span)

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x y : M) (f : Dual R M)

namespace Module

/-- Given an element `x` in a module `M` and a linear form `f` on `M`, we define the endomorphism
of `M` for which `y ↦ y - (f y) • x`.

One is typically interested in this endomorphism when `f x = 2`; this definition exists to allow the
user defer discharging this proof obligation. See also `Module.reflection`. -/
def preReflection : End R M :=
  LinearMap.id - f.smulRight x

lemma preReflection_apply :
    preReflection x f y = y - (f y) • x := by
  simp [preReflection]

variable {x f}

lemma preReflection_apply_self (h : f x = 2) :
    preReflection x f x = - x := by
  rw [preReflection_apply, h, two_smul]; abel

lemma involutive_preReflection (h : f x = 2) :
    Involutive (preReflection x f) :=
  fun y ↦ by simp [h, smul_sub, two_smul, preReflection_apply]

lemma preReflection_preReflection (g : Dual R M) (h : f x = 2) :
    preReflection (preReflection x f y) (preReflection f (Dual.eval R M x) g) =
    (preReflection x f) ∘ₗ (preReflection y g) ∘ₗ (preReflection x f) := by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

/-- Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define
the endomorphism of `M` for which `y ↦ y - (f y) • x`.

It is an involutive endomorphism of `M` fixing the kernel of `f` for which `x ↦ -x`. -/
def reflection (h : f x = 2) : M ≃ₗ[R] M :=
  LinearEquiv.ofBijective (preReflection x f) (involutive_preReflection h).bijective

lemma reflection_apply (h : f x = 2) :
    reflection h y = y - (f y) • x :=
  preReflection_apply x y f

@[simp]
lemma reflection_apply_self (h : f x = 2) :
    reflection h x = - x :=
  preReflection_apply_self h

lemma involutive_reflection (h : f x = 2) :
    Involutive (reflection h) :=
  involutive_preReflection h

@[simp]
lemma reflection_symm (h : f x = 2) :
    (reflection h).symm = reflection h := by
  ext m
  rw [LinearEquiv.symm_apply_eq]
  exact (involutive_reflection h m).symm

/-- See also `Module.Dual.eq_of_preReflection_image_subset'` for a variant of this lemma which
applies when `Φ` does not span. -/
lemma Dual.eq_of_preReflection_image_subset [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0) {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : preReflection x f '' Φ ⊆ Φ)
    (hg₁ : g x = 2) (hg₂ : preReflection x g '' Φ ⊆ Φ) :
    f = g := by
  let u := reflection hg₁ * reflection hf₁
  have hu : u = LinearMap.id (R := R) (M := M) + (f - g).smulRight x := by
    ext y
    simp only [reflection_apply, hg₁, two_smul, LinearEquiv.coe_mul, LinearEquiv.coe_coe,
      LinearMap.mul_apply, LinearMap.add_apply, LinearMap.id_coe, id_eq, LinearMap.coe_smulRight,
      LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel', smul_neg, sub_neg_eq_add, sub_smul]
    abel
  replace hu : ∀ (n : ℕ),
      ↑(u ^ n) = LinearMap.id (R := R) (M := M) + (n : R) • (f - g).smulRight x := by
    intros n
    induction' n with n ih; simp
    have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by ext; simp [hf₁, hg₁]
    rw [pow_succ, LinearEquiv.coe_mul, ih, hu, add_mul, mul_add, mul_add]
    simp_rw [LinearMap.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero, add_assoc,
      Nat.cast_succ, add_smul, one_smul]
  suffices IsOfFinOrder u by
    obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp this
    replace hn₁ : (↑(u ^ n) : M →ₗ[R] M) = LinearMap.id := LinearEquiv.toLinearMap_inj.mpr hn₁
    simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hu n
  suffices IsOfFinOrder u.toLinearMap by
    have hf : Injective (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := R) (M := M)) :=
      LinearEquiv.toLinearMap_injective
    exact hf.isOfFinOrder_iff.mp this
  refine isOfFinOrder_of_finite_of_span_eq_top_of_image_eq hΦ₁ hΦ₂ <|
    (hΦ₁.equiv_image_eq_iff_subset u.toEquiv).mpr ?_
  simpa only [← image_comp] using (image_mono hf₂).trans hg₂

lemma Dual.eq_of_preReflection_image_subset' [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0) {Φ : Set M} (hΦ₁ : Φ.Finite) (hx' : x ∈ span R Φ) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : preReflection x f '' Φ ⊆ Φ)
    (hg₁ : g x = 2) (hg₂ : preReflection x g '' Φ ⊆ Φ) :
    (span R Φ).subtype.dualMap f = (span R Φ).subtype.dualMap g := by
  set Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  rw [← finite_coe_iff] at hΦ₁
  have hΦ'₁ : Φ'.Finite := finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by simp
  let x' : span R Φ := ⟨x, hx'⟩
  have hx' : x' ≠ 0 := Subtype.ne_of_val_ne hx
  have : ∀ (F : Dual R M) (y : span R Φ),
      (preReflection x' ((span R Φ).subtype.dualMap F) y : M) = preReflection x F (y : M) :=
    fun F y ↦ rfl
  replace this : ∀ {F : Dual R M}, preReflection x F '' Φ ⊆ Φ →
      preReflection x' ((span R Φ).subtype.dualMap F) '' Φ' ⊆ Φ' := by
    intro F hF ⟨y, hy⟩ hy'
    simp_rw [mem_image, Subtype.ext_iff, this, range_inclusion] at hy'
    obtain ⟨z, hz, -, rfl⟩ := hy'
    simpa using hF (mem_image_of_mem _ hz)
  exact eq_of_preReflection_image_subset hx' hΦ'₁ hΦ'₂ hf₁ (this hf₂) hg₁ (this hg₂)

end Module
