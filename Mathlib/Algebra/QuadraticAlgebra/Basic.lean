/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Algebra.Star.Unitary

/-! # Quadratic algebras : involution and norm.

Let `R` be a commutative ring.

-/

namespace QuadraticAlgebra

variable {R : Type*} {a b : R}

section omega

section

variable [Zero R] [One R]

/-- The representative of the root in the quadratic algebra -/
def ω : QuadraticAlgebra R a b :=
  ⟨0, 1⟩

@[simp]
theorem re_omega : (ω : QuadraticAlgebra R a b).re = 0 :=
  rfl

@[simp]
theorem im_omega : (ω : QuadraticAlgebra R a b).im = 1 :=
  rfl

end

variable [CommSemiring R]

theorem omega_mul_omega :
    (ω : QuadraticAlgebra R a b) * (ω) = ⟨a, b⟩ := by
  ext <;> simp

theorem omega_mul_omega_eq :
    (ω : QuadraticAlgebra R a b) * (ω) = a • 1 + b • (ω) := by
  ext <;> simp

@[simp]
theorem omega_mul (x y : R) :
    (ω : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨a * y, x + b * y⟩ := by
  ext <;> simp

@[simp]
theorem omega_mul_coe_mul (n x y : R) :
    (ω : QuadraticAlgebra R a b) * (↑n) * ⟨x, y⟩ = ⟨a * n * y, n * x + n * b * y⟩ := by
  ext <;> simp; ring

theorem omega_prop : (ω) * (ω) =
    (b : QuadraticAlgebra R a b) * (ω : QuadraticAlgebra R a b) + (a : QuadraticAlgebra R a b) := by
  ext <;> simp

theorem omega_prop' : (ω : QuadraticAlgebra R a b) * (ω) =
    b • (ω) + a • 1 := by
  simp [omega_prop, ← QuadraticAlgebra.coe_mul_eq_smul]

theorem mk_eq_add_smul_omega {x y : R} :
    (⟨x, y⟩ : QuadraticAlgebra R a b) = x + y • (ω : QuadraticAlgebra R a b) := by
  ext <;> simp

variable {A : Type*} [Ring A] [Algebra R A]

@[ext]
theorem hom_ext {f g : QuadraticAlgebra R a b →ₐ[R] A}
    (h : f (ω) = g (ω)) : f = g := by
  ext ⟨x, y⟩
  simp only [mk_eq_add_smul_omega, map_add, map_smul, h, add_left_inj]
  change f (algebraMap R _ x) = g (algebraMap R _ x)
  simp only [AlgHom.commutes]

/-- The unique `AlgHom` from `QuadraticAlgebra R a b` to an `R`-algebra `A`,
constructed by replacing `ω` with the provided root.
Conversely, this associates to every algebra morphism `QuadraticAlgebra R a b →ₐ[R] A`
a value of `ω` in `A`. -/
@[simps]
def lift : { u : A // u * u = b • u + a • 1 } ≃ (QuadraticAlgebra R a b →ₐ[R] A) where
  toFun u :=
    { toFun z := z.re • 1 + z.im • u
      map_zero' := by simp
      map_add' z w := by
        simp only [re_add, im_add, add_smul, ← add_assoc]
        congr 1
        simp only [add_assoc]
        congr 1
        rw [add_comm]
      map_one' := by simp
      map_mul' z w := by
        symm
        calc
          (z.re • (1 : A) + z.im • ↑u) * (w.re • 1 + w.im • ↑u) =
            (z.re * w.re) • (1 : A) + (z.re * w.im) • u +
              (z.im * w.re) • u + (z.im * w.im) • (u * u) := by
              simp only [mul_add, mul_one, add_mul, one_mul, ← add_assoc, smul_mul_smul]
              apply add_add_add_comm'
          _ = (z.re * w.re) • (1 : A) + (z.re * w.im+ z.im * w.re) • u +
                (z.im * w.im) • (u * u) := by
              congr 1
              simp only [add_assoc]
              rw [← add_smul]
          _ = (z.re * w.re) • 1 + (z.re * w.im + z.im * w.re) • u +
                (z.im * w.im) • (b • u + a • 1) := by
              simp [u.prop]
          _ = (z.re * w.re + a * z.im * w.im) • 1 +
                (z.re * w.im + z.im * w.re + b * z.im * w.im) • u := by
              simp only [smul_add]
              module
            _ = (z * w).re • 1 + (z * w).im • u := by
              simp
      commutes' r := by
        simp [← Algebra.algebraMap_eq_smul_one] }
  invFun f := ⟨f (ω), by
    simp [← map_mul, omega_mul_omega_eq, add_comm]
    ⟩
  left_inv r := by
    simp
  right_inv f := by
    ext
    simp

end omega

section omega'

variable [Ring R]

/-- The representative of the “other” root in the quadratic algebra.

One has omega R a b + omega' R a b = b -/
def ω' : QuadraticAlgebra R a b :=
  ⟨b, -1⟩

@[simp]
theorem re_omega' : (ω' : QuadraticAlgebra R a b).re = b :=
  rfl

@[simp]
theorem im_omega' : (ω' : QuadraticAlgebra R a b).im = -1 :=
  rfl

theorem omega_add_omega' :
    (ω : QuadraticAlgebra R a b) + (ω' : QuadraticAlgebra R a b) = (b : R) := by
  ext <;> simp

theorem omega_mul_omega' :
    (ω : QuadraticAlgebra R a b) * (ω' : QuadraticAlgebra R a b) = (-a : R) := by
  ext <;> simp

end omega'

section star

variable [CommRing R]

/-- Conjugation in `QuadraticAlgebra R a b`.
The conjugate of `x + y ω` is `x + y ω' = (x - a * y) - y ω`. -/
instance : Star (QuadraticAlgebra R a b) where
  star z := ⟨z.re + b * z.im, -z.im⟩

@[simp]
theorem star_mk (x y : R) :
    star (⟨x, y⟩ : QuadraticAlgebra R a b) = ⟨x + b * y, -y⟩ :=
  rfl

theorem star_omega : star (ω : QuadraticAlgebra R a b) = (ω') := by
  simp [star, ω, ω']

theorem star_omega' : star (ω' : QuadraticAlgebra R a b) = (ω) := by
  simp [star, ω, ω']

@[simp]
theorem star_re (z : QuadraticAlgebra R a b) :
    (star z).re = z.re + b * z.im :=
  rfl

@[simp]
theorem star_im (z : QuadraticAlgebra R a b) :
    (star z).im = -z.im :=
  rfl

theorem mul_star {x y : R} :
    (⟨x, y⟩ * star ⟨x, y⟩ : QuadraticAlgebra R a b) =
      x * x + b * x * y - a * y * y := by
  ext <;> simp <;> ring

instance : StarRing (QuadraticAlgebra R a b) where
  star_involutive _ := by
    refine QuadraticAlgebra.ext (by simp) (neg_neg _)
  star_mul a b := by ext <;> simp <;> ring
  star_add _ _ := QuadraticAlgebra.ext (by simp [star_re]; ring) (neg_add _ _)

/-
@[simp]
theorem nsmul_val (n : ℕ) (x y : ℤ) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

@[simp]
theorem smul_val (n x y : ℤ) :
    (n : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨n * x, n * y⟩ := by
  ext <;> simp

@[simp]
theorem smul_re (r : R) (z : QuadraticAlgebra R a b) :
    (r • z).re = r * z.re := by
  simp

@[simp]
theorem smul_im (r : R) (z : QuadraticAlgebra R a b) :
    (r • z).im = r * z.im := by
  simp
-/

end star

section norm

variable [CommRing R]

/-- The norm of an element of `QuadraticAlgebra R a b`. -/
def norm (z : QuadraticAlgebra R a b) : R :=
  z.re * z.re + b * z.re * z.im - a * z.im * z.im

theorem norm_def (z : QuadraticAlgebra R a b) :
    z.norm = z.re * z.re + b * z.re * z.im - a * z.im * z.im :=
  rfl

@[simp]
theorem norm_zero : norm (0 : QuadraticAlgebra R a b) = 0 := by simp [norm]

@[simp]
theorem norm_one : norm (1 : QuadraticAlgebra R a b) = 1 := by simp [norm]

@[simp]
theorem norm_coe (r : R) : norm (r : QuadraticAlgebra R a b) = r * r := by simp [norm_def]

@[simp]
theorem norm_natCast (n : ℕ) : norm (n : QuadraticAlgebra R a b) = n * n :=
  by simp [norm_def]

@[simp]
theorem norm_intCast (n : ℤ) : norm (n : QuadraticAlgebra R a b) = n * n :=
  by simp [norm_def]

@[simp]
theorem norm_mul (z w : QuadraticAlgebra R a b) :
    norm (z * w) = norm z * norm w := by
  simp [norm_def]; ring

/-- `norm` as a `MonoidHom`. -/
def normMonoidHom : QuadraticAlgebra R a b →* R where
  toFun := norm
  map_mul' := norm_mul
  map_one' := norm_one

theorem normMonoidHom_apply (r : QuadraticAlgebra R a b) :
    normMonoidHom r = norm r := rfl

theorem coe_norm_eq_mul_conj (z : QuadraticAlgebra R a b) :
    ((norm z : R) : QuadraticAlgebra R a b) = z * star z := by
  ext <;> simp [norm, star, mul_comm] <;> ring

@[simp]
theorem norm_neg (x : QuadraticAlgebra R a b) : (-x).norm = x.norm := by
  simp [norm]

@[simp]
theorem norm_conj (x : QuadraticAlgebra R a b) : (star x).norm = x.norm := by
  simp [norm]; ring

theorem isUnit_iff_norm_isUnit {x : QuadraticAlgebra R a b} :
    IsUnit x ↔ IsUnit (x.norm) := by
  constructor
  · exact IsUnit.map normMonoidHom
  · simp only [isUnit_iff_exists]
    rintro ⟨r, hr, hr'⟩
    rw [← coe_inj (R := R) (a := a) (b := b), coe_mul,
      coe_norm_eq_mul_conj , mul_assoc, coe_one] at hr
    refine ⟨_, hr, ?_⟩
    rw [mul_comm, hr]

/-- An element of `QuadraticAlgebra R a b` has norm equal to `1`
if and only if it is contained in the submonoid of unitary elements. -/
theorem norm_eq_one_iff_mem_unitary {z : QuadraticAlgebra R a b} :
    z.norm = 1 ↔ z ∈ unitary (QuadraticAlgebra R a b) := by
  rw [unitary.mem_iff_self_mul_star, ← coe_norm_eq_mul_conj, coe_eq_one_iff]

/-- The kernel of the norm map on `QuadraticAlgebra R a b` equals
the submonoid of unitary elements. -/
theorem mker_norm_eq_unitary :
    MonoidHom.mker (@normMonoidHom R a b _) = unitary (QuadraticAlgebra R a b) :=
  Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

theorem coe_mem_nonZeroDivisors_iff {r : R} :
    (r : QuadraticAlgebra R a b) ∈ nonZeroDivisors _ ↔ r ∈ nonZeroDivisors R := by
  simp only [mem_nonZeroDivisors_iff_right]
  constructor
  · intro H x hxr
    rw [← coe_inj, coe_zero]
    apply H
    rw [← coe_mul, hxr, coe_zero]
  · intro h z hz
    rw [QuadraticAlgebra.ext_iff, re_zero, im_zero] at hz
    simp only [re_mul, re_coe, im_coe, mul_zero, add_zero, im_mul, zero_add] at hz
    simp [QuadraticAlgebra.ext_iff, re_zero, im_zero, h _ hz.left, h _ hz.right]

theorem conj_mem_nonZeroDivisors {z : QuadraticAlgebra R a b}
    (hz : z ∈ nonZeroDivisors _) : star z ∈ nonZeroDivisors _ :=  by
  rw [mem_nonZeroDivisors_iff_right] at hz ⊢
  intro w hw
  apply star_involutive.injective
  rw [star_zero]
  apply hz
  rw [← star_involutive z, ← star_mul, mul_comm, hw, star_zero]

theorem conj_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    star z ∈ nonZeroDivisors _ ↔ z ∈ nonZeroDivisors _ := by
  refine ⟨fun h ↦ ?_, conj_mem_nonZeroDivisors⟩
  rw [← star_involutive z]
  exact conj_mem_nonZeroDivisors h

theorem norm_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    z.norm ∈ nonZeroDivisors R ↔ z ∈ nonZeroDivisors _ := by
  constructor
  · simp only [mem_nonZeroDivisors_iff_right]
    intro h w hw
    have : norm z • w = 0 := by
      rw [← coe_mul_eq_smul, coe_norm_eq_mul_conj, mul_comm, ← mul_assoc, hw, zero_mul]
    simp only [QuadraticAlgebra.ext_iff, re_smul, smul_eq_mul, mul_comm, re_zero, im_smul,
      im_zero] at this
    ext <;> simp [h _ this.left, h _ this.right]
  · intro hz
    rw [← coe_mem_nonZeroDivisors_iff, coe_norm_eq_mul_conj]
    exact Submonoid.mul_mem _ hz (conj_mem_nonZeroDivisors hz)

end norm

end QuadraticAlgebra
