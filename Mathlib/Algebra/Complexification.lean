/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum

/-! # Complexification of spaces.

In this file we define the complexificatin of spaces. We essentially extend a real space to
a complex space, and extend operators to its complexification so we can use `ℂ`-results.
This is realised as a product space, where the first component is the "real part" and the second
is the "imaginary part".
This way, we can informally think of `(x, y) : Complexification M` as `x + I • y`.

In particular, `ℂ`-scalar multiplication is given by
`α • (x, y) = (ℜ α • x - ℑ α • y, ℜ α • y + ℑ α • x)`.

We also define multiplication and star structures on complexifications.

### Implementation details

We use products to describe complexifications as opposed to tensor products so that we can easily
use "real" and "imaginary" parts.
We will show the equivalence between the complexification defined here and its tensor product
description soon.

## References

[Steven Roman, *Advanced linear algebra*][roman_advanced_linear_algebra]

-/

public section

/-- The complexification of a space. -/
structure Complexification (M : Type*) where
  /-- The real part of a complexification. -/
  re : M
  /-- The imaginary part of a complexification. -/
  im : M

open Lean.PrettyPrinter.Delaborator in
/-- This prevents `mk x` being printed as `{ re := x.re, im := x.im }` by
`delabStructureInstance`. -/
@[app_delab Complexification.mk]
meta def Complexification.delabMk : Delab := delabApp

namespace Complexification
variable {R M : Type*}

/-- The canonical function from the complexification of a space to its product
given by `x ↦ (x.re, x.im)`. -/
@[expose, simps] def toProd (x : Complexification M) : M × M := (x.re, x.im)

@[simp] lemma mk_re_im (x : Complexification M) : mk x.re x.im = x := rfl
@[simp] lemma re_mk (x y : M) : (mk x y).re = x := rfl
@[simp] lemma im_mk (x y : M) : (mk x y).im = y := rfl

/-- The canonical equivalence between `Complexification M` and `M × M`. -/
@[expose, simps apply symm_apply] def equiv : Complexification M ≃ M × M where
  toFun := toProd
  invFun x := mk x.fst x.snd

lemma toProd_injective : (toProd : Complexification M → M × M).Injective := equiv.injective
lemma toProd_surjective : (toProd : Complexification M → M × M).Surjective := equiv.surjective
lemma toProd_bijective : (toProd : Complexification M → M × M).Bijective := equiv.bijective

@[simp] lemma toProd_inj_iff {x y : Complexification M} : toProd x = toProd y ↔ x = y :=
  toProd_injective.eq_iff

@[ext] lemma ext {x y : Complexification M} (h₁ : x.re = y.re) (h₂ : x.im = y.im) : x = y := by
  rw [← mk_re_im x, ← mk_re_im y, h₁, h₂]

instance [AddMonoid M] : AddMonoid (Complexification M) := equiv.addMonoid
instance [AddGroup M] : AddGroup (Complexification M) := equiv.addGroup
instance [AddCommMonoid M] : AddCommMonoid (Complexification M) := equiv.addCommMonoid
instance [AddCommGroup M] : AddCommGroup (Complexification M) := equiv.addCommGroup

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

instance instSMul : SMul ℂ (Complexification V) where
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
/-- The imaginary part of a complexification of a real space as a real continuous linear map. -/
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

@[simp] lemma symm_conj : (conj V).symm = conj V := rfl
@[simp] lemma conj_conj (x) : conj V (conj V x) = x := by simp [conj_apply]
@[simp] lemma conj_mk (x y : V) : conj V (.mk x y) = .mk x (-y) := rfl

lemma conj_I_smul (x) : conj V (Complex.I • x) = -Complex.I • conj V x := by simp [conj_apply]

@[simp] lemma conj_eq_self_iff {x} : conj V x = x ↔ x.im = 0 := by
  simp only [conj_apply, Complexification.ext_iff, true_and]
  rw [eq_comm, ← sub_eq_zero]
  simp [← two_smul ℝ]

/-- The complexification of `ℝ` is equivalent to `ℂ`. -/
@[expose, simps apply symm_apply]
def realLinearIsometryEquivComplex : Complexification ℝ ≃ₗ[ℂ] ℂ where
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
  carrier := { v | v.re ∈ K } ∩ { v | v.im ∈ K }
  add_mem' := by aesop
  zero_mem' := by simp
  smul_mem' := by aesop

@[simp] lemma _root_.Submodule.mem_complexification {K : Submodule ℝ V} (x : Complexification V) :
    x ∈ K.complexification ↔ x.re ∈ K ∧ x.im ∈ K := by simp [Submodule.complexification]

variable (V) in
/-- The inclusion map of a space into its complexification as a linear isometry, given by
`x ↦ (x, 0)`. -/
@[expose, simps apply] def inclusion : V →ₗ[ℝ] Complexification V where
  toFun x := .mk x 0
  map_add' := by simp
  map_smul' _ _ := by ext <;> simp

/-- A submodule `U` over the complexificationn of a real space is a complexified submodule
(i.e., there exists a real submodule `S` such that `S.complexification = U`)
iff `U` is closed under conjugation.

This is Chapter 1, Exercise 26 in [roman_advanced_linear_algebra]. -/
lemma _root_.Submodule.exists_complexification_eq_iff (U : Submodule ℂ (Complexification V)) :
    (∃ S : Submodule ℝ V, S.complexification = U) ↔ ∀ v ∈ U, conj V v ∈ U := by
  refine ⟨fun ⟨S, hS⟩ v hv ↦ by simpa [← hS, conj_apply] using hv, fun h ↦ ?_⟩
  refine ⟨(U.restrictScalars ℝ).comap (inclusion V), Submodule.ext fun x ↦ ?_⟩
  simp only [Submodule.mem_complexification, Submodule.mem_comap, inclusion_apply,
    Submodule.restrictScalars_mem]
  refine ⟨fun h2 ↦ ?_, fun h2 ↦ ⟨?_, ?_⟩⟩ <;> rw [← mk_re_im x, mk_eq_add_I_smul]
  · exact add_mem h2.1 (Submodule.smul_mem _ _ h2.2)
  · convert Submodule.smul_mem _ (2 : ℂ)⁻¹ (add_mem h2 (h _ h2))
    simp [conj_apply, Complexification.ext_iff, ← two_smul ℝ]
  · convert Submodule.smul_mem _ (2 * Complex.I)⁻¹ (sub_mem h2 (h _ h2))
    simp [Complexification.ext_iff, conj_apply, ← two_smul ℝ]

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

namespace LinearMap
variable {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [Module ℝ E] [Module ℝ F] [Module ℝ G]

open Complexification

/-- Complexification of a continuous linear map between inner product spaces. -/
@[expose, simps apply] def toComplexification (T : E →ₗ[ℝ] F) :
    Complexification E →ₗ[ℂ] Complexification F where
  toFun v := .mk (T v.re) (T v.im)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

@[simp] lemma toComplexification_id : (.id : E →ₗ[ℝ] E).toComplexification = .id := rfl
@[simp] lemma toComplexification_one : (1 : E →ₗ[ℝ] E).toComplexification = 1 := rfl

@[simp] lemma toComplexification_comp (S : F →ₗ[ℝ] G) (T : E →ₗ[ℝ] F) :
    (S.comp T).toComplexification = S.toComplexification.comp T.toComplexification := rfl

@[simp] lemma toComplexification_mul (S T : E →ₗ[ℝ] E) :
    (S * T).toComplexification = S.toComplexification * T.toComplexification := rfl

lemma toComplexification_injective :
    Function.Injective (toComplexification (E := E) (F := F)) := fun S T h ↦ by
  ext x; simpa using congr(($h (.mk x 0)).re)

@[simp] lemma toComplexification_inj {S T : E →ₗ[ℝ] F} :
    S.toComplexification = T.toComplexification ↔ S = T :=
  toComplexification_injective.eq_iff

@[simp] lemma isIdempotentElem_toComplexification_iff {S : E →ₗ[ℝ] E} :
    IsIdempotentElem S.toComplexification ↔ IsIdempotentElem S := by
  simp [IsIdempotentElem, ← toComplexification_mul]

alias ⟨_, _root_.IsIdempotentElem.toComplexification⟩ := isIdempotentElem_toComplexification_iff

@[simp] lemma injective_toComplexification_iff {T : E →ₗ[ℝ] F} :
    Function.Injective T.toComplexification ↔ Function.Injective T := by
  refine ⟨fun h x y hxy ↦ ?_, fun h x y hxy ↦ ?_⟩
  · simpa using congr(($(h (a₁ := .mk x 0) (a₂ := .mk y 0)
      (by ext <;> simp [hxy]))).re)
  · have := by simpa [h.eq_iff] using congr(($hxy).re)
    have := by simpa [h.eq_iff] using congr(($hxy).im)
    simp_all [Complexification.ext_iff]

@[simp] lemma surjective_toComplexification_iff {T : E →ₗ[ℝ] F} :
    Function.Surjective T.toComplexification ↔ Function.Surjective T := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨v, hv⟩ := h (.mk x 0)
    exact ⟨v.re, by simpa using congr(($hv).re)⟩
  · obtain ⟨v, hv⟩ := h x.re
    obtain ⟨w, hw⟩ := h x.im
    exact ⟨.mk v w, by simp [hv, hw]⟩

@[simp] lemma bijective_toComplexification_iff {T : E →ₗ[ℝ] F} :
    Function.Bijective T.toComplexification ↔ Function.Bijective T := by
  simp [Function.Bijective]

@[simp] lemma ker_toComplexification (T : E →ₗ[ℝ] F) :
    T.toComplexification.ker = T.ker.complexification := by
  ext; simp [Complexification.ext_iff]

@[simp] lemma range_toComplexification (T : E →ₗ[ℝ] F) :
   T.toComplexification.range = T.range.complexification := by
  ext x
  simp only [LinearMap.mem_range, toComplexification_apply,
    Complexification.ext_iff, Submodule.mem_complexification]
  exact ⟨by grind, fun ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ ↦ ⟨.mk y z, by simp [hy, hz]⟩⟩

/-- Conjugation of a complexified operator given by `T ↦ conj ∘ T ∘ conj`.

An opeartor is equal to its conjugate iff it is a complexified operator
(see `exists_toComplexification_eq_iff`). -/
@[expose, simps! apply_apply] noncomputable def conjugate :
    (Complexification E →ₗ[ℂ] Complexification F) ≃ₗ⋆[ℂ]
      (Complexification E →ₗ[ℂ] Complexification F) :=
  (conj E).arrowCongr (conj F)

@[simp] lemma conjugate_conjugate (T : Complexification E →ₗ[ℂ] Complexification F) :
    T.conjugate.conjugate = T := by ext <;> simp

@[simp] lemma symm_conjugate : conjugate (E := E) (F := F).symm = conjugate := rfl

@[simp] lemma conjugate_id : (.id : Complexification E →ₗ[ℂ] _).conjugate = .id := by ext1; simp
@[simp] lemma conjugate_one : (1 : Complexification E →ₗ[ℂ] Complexification E).conjugate = 1 :=
  conjugate_id

@[simp] lemma conjugate_comp (S : Complexification F →ₗ[ℂ] Complexification G)
    (T : Complexification E →ₗ[ℂ] Complexification F) :
    (S ∘ₛₗ T).conjugate = S.conjugate ∘ₛₗ T.conjugate := by ext1; simp

@[simp] lemma conjugate_mul (S T : Complexification E →ₗ[ℂ] Complexification E) :
    (S * T).conjugate = S.conjugate * T.conjugate := conjugate_comp _ _

@[simp] lemma conjugate_toComplexification (S : E →ₗ[ℝ] F) :
    S.toComplexification.conjugate = S.toComplexification := by ext1; simp [conj_apply]

/-- Decomplexifying an operator on complexifications given that it commutes with
the complexification of `algebraMapCLM 𝕜 _ RCLike.I`. -/
@[expose, simps!]
noncomputable def ofComplexification (T : Complexification E →ₗ[ℂ] Complexification F) :
    E →ₗ[ℝ] F :=
  reₗ F ∘ₛₗ T.restrictScalars ℝ ∘ₛₗ inclusion E

@[simp] lemma ofComplexification_zero :
    (0 : Complexification E →ₗ[ℂ] Complexification F).ofComplexification = 0 := rfl

@[simp] lemma ofComplexification_id :
    (.id : Complexification E →ₗ[ℂ] Complexification E).ofComplexification = .id := rfl

@[simp] lemma ofComplexification_one :
    (1 : Complexification E →ₗ[ℂ] Complexification E).ofComplexification = 1 := rfl

@[simp] lemma ofComplexification_toComplexification (T : E →ₗ[ℝ] F) :
    T.toComplexification.ofComplexification = T := by ext; simp

lemma toComplexification_ofComplexification
    {T : Complexification E →ₗ[ℂ] Complexification F} (hT : T.conjugate = T) :
    T.ofComplexification.toComplexification = T := by
  ext1 v
  conv_rhs => rw [← mk_re_im v, mk_eq_add_I_smul]
  simp only [map_add, map_smul]
  have (x : E) : T (.mk x 0) = .mk (T (.mk x 0)).re 0 := by
    refine Complexification.ext rfl ?_
    simp only [← conj_eq_self_iff]
    conv_rhs => rw [← hT]
    simp
  simp +singlePass only [this]
  ext <;> simp

/-- An operator `T` on a complexification space of a real space is a complexified operator
(i.e., there exists an operator `S` such that `S.toComplexification = T`) iff `T.conjugate = T`
and it commutes with the complexification of `algebraMapCLM 𝕜 _ RCLike.I`.

This is Chapter 2, Exercise 32 in [roman_advanced_linear_algebra]. -/
lemma exists_toComplexification_eq_iff {T : Complexification E →ₗ[ℂ] Complexification F} :
    (∃ S : E →ₗ[ℝ] F, S.toComplexification = T) ↔ T.conjugate = T :=
  ⟨fun ⟨S, hS⟩ ↦ by simp [← hS], fun h ↦ ⟨_, toComplexification_ofComplexification h⟩⟩

@[simp] lemma isUnit_toComplexification_iff {T : E →ₗ[ℝ] E} :
    IsUnit T.toComplexification ↔ IsUnit T := by simp [Module.End.isUnit_iff]

@[simp] lemma spectrum_toComplexification (T : E →ₗ[ℝ] E) :
    spectrum ℝ T.toComplexification = spectrum ℝ T := by
  ext r
  simp only [spectrum.mem_iff, not_iff_not]
  conv_rhs => rw [← isUnit_toComplexification_iff]
  congr! 1
  simp [Algebra.algebraMap_eq_smul_one, LinearMap.ext_iff, Complexification.ext_iff]

@[simp] lemma quasispectrum_toComplexification (T : E →ₗ[ℝ] E) :
    quasispectrum ℝ T.toComplexification = quasispectrum ℝ T := by
  simp [quasispectrum_eq_spectrum_union_zero]

end LinearMap
