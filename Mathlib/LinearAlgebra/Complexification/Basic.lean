/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.LinearAlgebra.Complex.Module

/-! # Complexification of spaces.

In this file we define the complexificatin of spaces. We essentially extend a real space to
a complex space, and extend operators to its complexification so we can use `ℂ`-results.
This is realised as a product space, where the first component is the "real part" and the second
is the "imaginary part".
This way, we can informally think of `(x, y) : Complexification M` as `x + I • y`.

In particular, `ℂ`-scalar multiplication is given by
`α • (x, y) = (ℜ α • x - ℑ α • y, ℜ α • y + ℑ α • x)`.

We also define multiplication and star structures on complexifications.

## Implementation details

We use products to describe complexifications as opposed to tensor products so that we can
complexify normed spaces, C⋆-algebras, etc. With tensor products, this poses a slight problem.

We will show the equivalence between the complexification defined here and its tensor product
description soon.

## References

[Steven Roman, *Advanced linear algebra*][roman_advanced_linear_algebra]

-/

public section

/-- The complexification of a space. -/
@[ext]
structure Complexification (M : Type*) where
  /-- The real part of a complexification. -/
  re : M
  /-- The imaginary part of a complexification. -/
  im : M

open Lean.PrettyPrinter.Delaborator in
/-- This prevents `mk x.re y.im` being printed as `{ re := x.re, im := x.im }` by
`delabStructureInstance`. -/
@[app_delab Complexification.mk]
meta def Complexification.delabMk : Delab := delabApp

namespace Complexification
variable {M : Type*}

@[simp] lemma mk_re_im (x : Complexification M) : mk x.re x.im = x := rfl
@[simp] lemma re_mk (x y : M) : (mk x y).re = x := rfl
@[simp] lemma im_mk (x y : M) : (mk x y).im = y := rfl

/-- The canonical equivalence between `Complexification M` and `M × M`. -/
@[expose, simps apply symm_apply] def equivProd : Complexification M ≃ M × M where
  toFun x := (x.re, x.im)
  invFun x := mk x.fst x.snd

instance [AddMonoid M] : AddMonoid (Complexification M) := equivProd.addMonoid
instance [AddGroup M] : AddGroup (Complexification M) := equivProd.addGroup
instance [AddCommMonoid M] : AddCommMonoid (Complexification M) := equivProd.addCommMonoid
instance [AddCommGroup M] : AddCommGroup (Complexification M) := equivProd.addCommGroup

variable [AddMonoid M]

@[simp] lemma re_zero : (0 : Complexification M).re = 0 := rfl
@[simp] lemma im_zero : (0 : Complexification M).im = 0 := rfl
@[simp] lemma re_add (v w : Complexification M) : (v + w).re = v.re + w.re := rfl
@[simp] lemma im_add (v w : Complexification M) : (v + w).im = v.im + w.im := rfl
@[simp] lemma mk_zero_zero : mk (0 : M) 0 = 0 := rfl

variable {V : Type*} [AddCommGroup V]

@[simp] lemma re_sub (v w : Complexification V) : (v - w).re = v.re - w.re := rfl
@[simp] lemma im_sub (v w : Complexification V) : (v - w).im = v.im - w.im := rfl
@[simp] lemma re_neg (v : Complexification V) : (-v).re = -v.re := rfl
@[simp] lemma im_neg (v : Complexification V) : (-v).im = -v.im := rfl
@[simp] lemma neg_mk (x y : V) : -mk x y = mk (-x) (-y) := rfl

@[simp] lemma mk_add_mk (x y z w : M) : mk x y + mk z w = mk (x + z) (y + w) := rfl
@[simp] lemma mk_sub_mk (x y z w : V) : mk x y - mk z w = mk (x - z) (y - w) := rfl

variable [Module ℝ V]

instance : SMul ℂ (Complexification V) where
  smul z v := .mk (z.re • v.re - z.im • v.im) (z.im • v.re + z.re • v.im)

lemma smul_def (z : ℂ) (v : Complexification V) :
    z • v = .mk (z.re • v.re - z.im • v.im) (z.im • v.re + z.re • v.im) := rfl

@[simp] lemma re_smul (z : ℂ) (v : Complexification V) :
    (z • v).re = z.re • v.re - z.im • v.im := rfl
@[simp] lemma im_smul (z : ℂ) (v : Complexification V) :
    (z • v).im = z.im • v.re + z.re • v.im := rfl

instance : Module ℂ (Complexification V) where
  one_smul _ := by ext <;> simp
  mul_smul _ _ _ := by ext <;> simp <;> module
  smul_zero _ := by ext <;> simp
  smul_add _ _ _ := by ext <;> simp <;> grind
  add_smul _ _ _ := by ext <;> simp <;> module
  zero_smul _ := by ext <;> simp

@[simp] lemma re_real_smul (r : ℝ) (v : Complexification V) : (r • v).re = r • v.re := by
  simp [← Complex.coe_smul]
@[simp] lemma im_real_smul (r : ℝ) (v : Complexification V) : (r • v).im = r • v.im := by
  simp [← Complex.coe_smul]

@[simp] lemma I_smul (v : Complexification V) : Complex.I • v = mk (-v.im) v.re := by
  ext <;> simp

lemma I_smul_mk (x y : V) : Complex.I • mk x y = mk (-y) x := I_smul _

/-- `(x, y) = (x, 0) + I • (y, 0)`. -/
lemma mk_eq_add_I_smul (x y : V) : mk x y = mk x 0 + Complex.I • mk y 0 := by simp

variable (V) in
/-- The real part of a complexification of a real space as a real linear map. -/
@[expose, simps] def reₗ : Complexification V →ₗ[ℝ] V where
  toFun x := x.re
  map_add' := by simp
  map_smul' := by simp

variable (V) in
/-- The imaginary part of a complexification of a real space as a real linear map. -/
@[expose, simps] def imₗ : Complexification V →ₗ[ℝ] V where
  toFun x := x.im
  map_add' := by simp
  map_smul' := by simp

variable (V) in
/-- Conjugation on the complexification space, given by `(x, y) ↦ (x, -y)`. -/
@[expose, simps -isSimp apply] def conj : Complexification V ≃ₗ⋆[ℂ] Complexification V where
  toFun v := .mk v.re (-v.im)
  invFun v := .mk v.re (-v.im)
  map_add' := by simp [add_comm]
  map_smul' _ _ := by ext <;> simp [add_comm]
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] lemma re_conj (x) : (conj V x).re = x.re := rfl
@[simp] lemma im_conj (x) : (conj V x).im = -x.im := rfl
@[simp] lemma symm_conj : (conj V).symm = conj V := rfl
@[simp] lemma conj_conj (x) : conj V (conj V x) = x := by simp [conj_apply]
@[simp] lemma conj_mk (x y : V) : conj V (.mk x y) = .mk x (-y) := rfl

lemma conj_I_smul (x) : conj V (Complex.I • x) = -Complex.I • conj V x := by simp [conj_apply]

@[simp] lemma conj_eq_self_iff {x} : conj V x = x ↔ x.im = 0 := by
  simp [Complexification.ext_iff, neg_eq_iff_add_eq_zero, ← two_smul ℝ]

/-- The complexification of `ℝ` is equivalent to `ℂ`. -/
@[expose, simps apply symm_apply]
def realLinearEquivComplex : Complexification ℝ ≃ₗ[ℂ] ℂ where
  toFun x := x.re + x.im * Complex.I
  invFun x := .mk x.re x.im
  map_add' _ _ := by simp [add_mul]; grind
  map_smul' z _ := by
    rw [← Complex.re_add_im z]
    simp [add_mul, mul_add, -Complex.re_add_im, mul_mul_mul_comm _ Complex.I]
    grind
  left_inv _ := by simp
  right_inv _ := by simp

/-- Complexification of a submodule, i.e., `(a, b) ∈ K.complexification ↔ a ∈ K ∧ b ∈ K`. -/
@[expose]
def _root_.Submodule.complexification (K : Submodule ℝ V) : Submodule ℂ (Complexification V) where
  carrier := { v | v.re ∈ K ∧ v.im ∈ K }
  add_mem' := by aesop
  zero_mem' := by simp
  smul_mem' := by aesop

@[simp] lemma _root_.Submodule.mem_complexification {K : Submodule ℝ V} {x : Complexification V} :
    x ∈ K.complexification ↔ x.re ∈ K ∧ x.im ∈ K := .rfl

variable (V) in
/-- The inclusion map of a space into its complexification as a linear map, given by
`x ↦ (x, 0)`. -/
@[expose, simps apply] def inclusion : V →ₗ[ℝ] Complexification V where
  toFun x := .mk x 0
  map_add' := by simp
  map_smul' _ _ := by ext <;> simp

lemma _root_.Submodule.complexification_le_iff {K : Submodule ℝ V}
    {U : Submodule ℂ (Complexification V)} :
    K.complexification ≤ U ↔ K ≤ (U.restrictScalars ℝ).comap (inclusion V) := by
  refine ⟨fun h y hy ↦ by simpa using h (by simp [hy]), fun h x hx ↦ ?_⟩
  rw [Submodule.mem_complexification] at hx
  rw [← mk_re_im x, mk_eq_add_I_smul]
  exact add_mem (by simpa using h hx.1) (U.smul_mem _ (by simpa using h hx.2))

lemma _root_.Submodule.complexification_gc :
    GaloisConnection (Submodule.complexification (V := V))
      fun U ↦ (U.restrictScalars ℝ).comap (inclusion V) :=
  fun _ _ ↦ Submodule.complexification_le_iff

@[simp] lemma _root_.Submodule.comap_inclusion_complexification (K : Submodule ℝ V) :
    (K.complexification.restrictScalars ℝ).comap (inclusion V) = K := by ext; simp

@[gcongr] lemma _root_.Submodule.complexification_mono {K L : Submodule ℝ V} (h : K ≤ L) :
    K.complexification ≤ L.complexification := Submodule.complexification_gc.monotone_l h

@[simp] lemma _root_.Submodule.complexification_le_complexification {K L : Submodule ℝ V} :
    K.complexification ≤ L.complexification ↔ K ≤ L := by simp [Submodule.complexification_le_iff]

@[simp] lemma _root_.Submodule.complexification_bot : (⊥ : Submodule ℝ V).complexification = ⊥ :=
  Submodule.complexification_gc.l_bot

@[simp] lemma _root_.Submodule.complexification_top :
    (⊤ : Submodule ℝ V).complexification = ⊤ := by ext; simp

lemma _root_.Submodule.complexification_sup (K L : Submodule ℝ V) :
    (K ⊔ L).complexification = K.complexification ⊔ L.complexification :=
  Submodule.complexification_gc.l_sup

lemma _root_.Submodule.complexification_inf (K L : Submodule ℝ V) :
    (K ⊓ L).complexification = K.complexification ⊓ L.complexification := by
  ext; simp [and_and_and_comm]

@[simp] lemma _root_.Submodule.complexification_inj {K L : Submodule ℝ V} :
    K.complexification = L.complexification ↔ K = L := by simp [le_antisymm_iff]

lemma _root_.Submodule.complexification_comap_inclusion {U : Submodule ℂ (Complexification V)}
    (h : ∀ v ∈ U, conj V v ∈ U) :
    ((U.restrictScalars ℝ).comap (inclusion V)).complexification = U := by
  ext x
  simp only [Submodule.mem_complexification, Submodule.mem_comap, inclusion_apply,
    Submodule.restrictScalars_mem]
  refine ⟨fun h2 ↦ ?_, fun h2 ↦ ⟨?_, ?_⟩⟩ <;> rw [← mk_re_im x, mk_eq_add_I_smul]
  · exact add_mem h2.1 (Submodule.smul_mem _ _ h2.2)
  · convert Submodule.smul_mem _ (2 : ℂ)⁻¹ (add_mem h2 (h _ h2))
    simp [conj_apply, Complexification.ext_iff, ← two_smul ℝ]
  · convert Submodule.smul_mem _ (2 * Complex.I)⁻¹ (sub_mem h2 (h _ h2))
    simp [Complexification.ext_iff, conj_apply, ← two_smul ℝ]

/-- A submodule `U` over the complexification of a real space is a complexified submodule
(i.e., there exists a real submodule `S` such that `S.complexification = U`)
iff `U` is closed under conjugation.

This is Chapter 1, Exercise 26 in [roman_advanced_linear_algebra]. -/
lemma _root_.Submodule.exists_complexification_eq_iff {U : Submodule ℂ (Complexification V)} :
    (∃ S : Submodule ℝ V, S.complexification = U) ↔ ∀ v ∈ U, conj V v ∈ U := by
  refine ⟨fun ⟨S, hS⟩ v hv ↦ by simpa [← hS] using hv, fun h ↦ ?_⟩
  exact ⟨_, Submodule.complexification_comap_inclusion h⟩

section NonUnitalNonAssocRing
variable {A : Type*} [NonUnitalNonAssocRing A]

instance : Mul (Complexification A) where
  mul x y := mk (x.re * y.re - x.im * y.im) (x.re * y.im + x.im * y.re)

lemma mul_def (x y : Complexification A) :
    x * y = mk (x.re * y.re - x.im * y.im) (x.re * y.im + x.im * y.re) := rfl

@[simp] lemma re_mul (x y : Complexification A) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] lemma im_mul (x y : Complexification A) : (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] lemma mk_mul_mk (a b c d : A) : mk a b * mk c d = mk (a * c - b * d) (a * d + b * c) := rfl

instance : NonUnitalNonAssocRing (Complexification A) where
  left_distrib := by simp [mul_def, mul_add]; grind
  right_distrib := by simp [mul_def, add_mul]; grind
  zero_mul := by simp [mul_def]
  mul_zero := by simp [mul_def]

instance [Module ℝ A] [IsScalarTower ℝ A A] :
    IsScalarTower ℂ (Complexification A) (Complexification A) where
  smul_assoc _ _ _ := by ext <;> simp [smul_sub, sub_mul, add_mul, smul_mul_assoc] <;> grind

instance [Module ℝ A] [SMulCommClass ℝ A A] :
    SMulCommClass ℂ (Complexification A) (Complexification A) where
  smul_comm _ _ _ := by ext <;> simp [smul_sub, mul_sub, mul_add, mul_smul_comm] <;> grind

end NonUnitalNonAssocRing

instance {A : Type*} [NonUnitalRing A] : NonUnitalRing (Complexification A) where
  mul_assoc _ _ _ := by simp [mul_def, mul_add, add_mul, sub_mul, mul_sub]; grind

instance {A : Type*} [NonUnitalNonAssocCommRing A] :
    NonUnitalNonAssocCommRing (Complexification A) where
  mul_comm _ _ := by ext <;> simp <;> grind [mul_comm]

instance {A : Type*} [NonUnitalCommRing A] : NonUnitalCommRing (Complexification A) where

section
variable {A : Type*} [NonAssocRing A]

instance : One (Complexification A) where one := mk 1 0

lemma one_def : (1 : Complexification A) = mk 1 0 := rfl
@[simp] lemma re_one : (1 : Complexification A).re = 1 := rfl
@[simp] lemma im_one : (1 : Complexification A).im = 0 := rfl

instance : NonAssocRing (Complexification A) where
  one_mul _ := by ext <;> simp
  mul_one _ := by ext <;> simp

instance {A : Type*} [NonAssocCommRing A] : NonAssocCommRing (Complexification A) where
instance {A : Type*} [Ring A] : Ring (Complexification A) where
instance {A : Type*} [CommRing A] : CommRing (Complexification A) where

instance {A : Type*} [Ring A] [Algebra ℝ A] : Algebra ℂ (Complexification A) :=
  .ofModule' (by simp) (by simp)

lemma algebraMap_apply {A : Type*} [Ring A] [Algebra ℝ A] (x : ℂ) :
    algebraMap ℂ (Complexification A) x = .mk (algebraMap ℝ A x.re) (algebraMap ℝ A x.im) := by
  ext <;> simp [Algebra.algebraMap_eq_smul_one]

end

section star
variable {A : Type*} [NonUnitalNonAssocRing A] [StarRing A]

instance : Star (Complexification A) where star x := mk (star x.re) (-star x.im)

lemma star_def (x : Complexification A) : star x = mk (star x.re) (-star x.im) := rfl
@[simp] lemma re_star (x : Complexification A) : (star x).re = star x.re := rfl
@[simp] lemma im_star (x : Complexification A) : (star x).im = -star x.im := rfl
@[simp] lemma star_mk (a b : A) : star (mk a b) = mk (star a) (-star b) := rfl

instance : InvolutiveStar (Complexification A) where star_involutive _ := by simp [star_def]
instance instStarMul : StarMul (Complexification A) where star_mul := by simp [mul_def]
instance instStarAddMonoid : StarAddMonoid (Complexification A) where
  star_add := by simp [star_def, add_comm]
instance : StarRing (Complexification A) where __ := instStarAddMonoid; __ := instStarMul

instance [Module ℝ A] [StarModule ℝ A] : StarModule ℂ (Complexification A) where
  star_smul _ _ := by ext <;> simp [add_comm]

lemma star_I_smul [Module ℝ A] (x : Complexification A) :
    star (Complex.I • x) = -(Complex.I • star x) := by simp

@[simp] lemma star_conj [Module ℝ A] (x : Complexification A) :
    star (conj A x) = conj A (star x) := by simp [star_def, conj_apply]

end star

end Complexification
