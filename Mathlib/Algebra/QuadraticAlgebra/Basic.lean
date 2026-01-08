/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Defs
public import Mathlib.Algebra.Star.Unitary

/-! # Quadratic algebras : involution and norm.

Let `R` be a commutative ring. We define:

* `QuadraticAlgebra.star` : the quadratic involution

* `QuadraticAlgebra.norm` : the norm

We prove :

* `QuadraticAlgebra.isUnit_iff_norm_isUnit`:
  `w : QuadraticAlgebra R a b` is a unit iff `w.norm` is a unit in `R`.

* `QuadraticAlgebra.norm_mem_nonZero_divisors_iff`:
  `w : QuadraticAlgebra R a b` isn't a zero divisor iff
  `w.norm` isn't a zero divisor in `R`.

* If `R` is a field, and `∀ r, r ^ 2 ≠ a + b * r`, then `QuadraticAlgebra R a b` is a field.

## Warning
If you are working over `ℚ`, note the existence of the diamond explained in
`Mathlib.Algebra.QuadraticAlgebra.Defs`.

-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} {a b : R}

section omega

section

variable [Zero R] [One R]

/-- The representative of the root in the quadratic algebra -/
def omega : QuadraticAlgebra R a b :=
  ⟨0, 1⟩

/-- the canonical element `⟨0, 1⟩` in a quadratic algebra `QuadraticAlgebra R a b`. -/
scoped notation "ω" => omega

@[simp]
theorem omega_re : (ω : QuadraticAlgebra R a b).re = 0 :=
  rfl

@[simp]
theorem omega_im : (ω : QuadraticAlgebra R a b).im = 1 :=
  rfl

end

variable [CommSemiring R]

theorem omega_mul_omega_eq_mk : (ω : QuadraticAlgebra R a b) * ω = ⟨a, b⟩ := by
  ext <;> simp

theorem omega_mul_omega_eq_add :
    (ω : QuadraticAlgebra R a b) * ω = a • 1 + b • ω := by
  ext <;> simp

@[simp]
theorem omega_mul_mk (x y : R) : (ω : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨a * y, x + b * y⟩ := by
  ext <;> simp

@[simp]
theorem omega_mul_algebraMap_mul_mk (n x y : R) :
    (ω : QuadraticAlgebra R a b) * algebraMap _ _ n * ⟨x, y⟩ = ⟨a * n * y, n * x + n * b * y⟩ := by
  ext <;> simp; ring

@[deprecated (since := "2025-12-15")] alias omega_mul_coe_mul_mk := omega_mul_algebraMap_mul_mk

theorem mk_eq_add_smul_omega (x y : R) :
    (⟨x, y⟩ : QuadraticAlgebra R a b) = algebraMap _ _ x + y • ω := by
  ext <;> simp

variable {A : Type*} [Ring A] [Algebra R A]

@[ext]
theorem algHom_ext {f g : QuadraticAlgebra R a b →ₐ[R] A}
    (h : f ω = g ω) : f = g := by
  ext ⟨x, y⟩
  simp [mk_eq_add_smul_omega, h]

/-- The unique `AlgHom` from `QuadraticAlgebra R a b` to an `R`-algebra `A`,
constructed by replacing `ω` with the provided root.
Conversely, this associates to every algebra morphism `QuadraticAlgebra R a b →ₐ[R] A`
a value of `ω` in `A`. -/
@[simps]
def lift : { u : A // u * u = a • 1 + b • u } ≃ (QuadraticAlgebra R a b →ₐ[R] A) where
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
          _ = (z.re * w.re) • (1 : A) + (z.re * w.im + z.im * w.re) • u +
                (z.im * w.im) • (u * u) := by
              congr 1
              simp only [add_assoc]
              rw [← add_smul]
          _ = (z.re * w.re) • 1 + (z.re * w.im + z.im * w.re) • u +
                (z.im * w.im) • (a • 1 + b • u) := by
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
    simp [← map_mul, omega_mul_omega_eq_add]
    ⟩
  left_inv r := by
    simp
  right_inv f := by
    ext
    simp

end omega

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

@[simp]
theorem re_star (z : QuadraticAlgebra R a b) :
    (star z).re = z.re + b * z.im :=
  rfl

@[simp]
theorem im_star (z : QuadraticAlgebra R a b) :
    (star z).im = -z.im :=
  rfl

theorem mul_star (x y : R) :
    (⟨x, y⟩ * star ⟨x, y⟩ : QuadraticAlgebra R a b) = (algebraMap _ _ x) * (algebraMap _ _ x) +
      (algebraMap _ _ b) * (algebraMap _ _ x) * (algebraMap _ _ y) - (algebraMap _ _ a) *
      (algebraMap _ _ y) * (algebraMap _ _ y) := by
  ext <;> simp <;> ring

instance : StarRing (QuadraticAlgebra R a b) where
  star_involutive _ := by
    refine QuadraticAlgebra.ext (by simp) (neg_neg _)
  star_mul a b := by ext <;>
    simp only [re_star, re_mul, im_mul, im_star, mul_neg, neg_mul, neg_neg] <;> ring
  star_add _ _ := QuadraticAlgebra.ext (by simp only [re_star, re_add, im_add]; ring) (neg_add _ _)

end star

section norm

variable [CommRing R]

/-- the norm in a quadratic algebra, as a `MonoidHom`. -/
def norm : QuadraticAlgebra R a b →* R where
  toFun z := z.re * z.re + b * z.re * z.im - a * z.im * z.im
  map_mul' z w := by simp only [re_mul, im_mul]; ring
  map_one' := by simp

theorem norm_def (z : QuadraticAlgebra R a b) :
    z.norm = z.re * z.re + b * z.re * z.im - a * z.im * z.im :=
  rfl

@[simp]
theorem norm_zero : norm (0 : QuadraticAlgebra R a b) = 0 := by simp [norm]

@[simp]
theorem norm_one : norm (1 : QuadraticAlgebra R a b) = 1 := by simp [norm]

@[simp]
theorem norm_algebraMap (r : R) : norm (algebraMap R (QuadraticAlgebra R a b) r) = r ^ 2 := by
  simp [norm_def, pow_two]

@[deprecated (since := "2025-12-15")] alias norm_coe := norm_algebraMap

@[simp]
theorem norm_natCast (n : ℕ) : norm (n : QuadraticAlgebra R a b) = n ^ 2 := by
  simp [norm_def, pow_two]

@[simp]
theorem norm_intCast (n : ℤ) : norm (n : QuadraticAlgebra R a b) = n ^ 2 := by
  simp [norm_def, pow_two]

theorem algebraMap_norm_eq_mul_star (z : QuadraticAlgebra R a b) :
    (algebraMap R _ (norm z : R)) = z * star z := by
  ext <;> simp [norm, star, mul_comm] <;> ring

@[deprecated (since := "2025-12-15")] alias coe_norm_eq_mul_star := algebraMap_norm_eq_mul_star

@[simp]
theorem norm_neg (x : QuadraticAlgebra R a b) : (-x).norm = x.norm := by
  simp [norm]

@[simp]
theorem norm_star (x : QuadraticAlgebra R a b) : (star x).norm = x.norm := by
  simp only [norm, MonoidHom.coe_mk, OneHom.coe_mk, re_star, im_star, mul_neg, neg_mul, neg_neg,
    sub_left_inj]
  ring

theorem isUnit_iff_norm_isUnit {x : QuadraticAlgebra R a b} :
    IsUnit x ↔ IsUnit (x.norm) := by
  constructor
  · exact IsUnit.map norm
  · simp only [isUnit_iff_exists]
    rintro ⟨r, hr, hr'⟩
    rw [← C_inj (R := R) (a := a) (b := b), C_mul, C_eq_algebraMap, algebraMap_norm_eq_mul_star,
      mul_assoc, map_one] at hr
    refine ⟨_, hr, ?_⟩
    rw [mul_comm, hr]

/-- An element of `QuadraticAlgebra R a b` has norm equal to `1`
if and only if it is contained in the submonoid of unitary elements. -/
theorem norm_eq_one_iff_mem_unitary {z : QuadraticAlgebra R a b} :
    z.norm = 1 ↔ z ∈ unitary (QuadraticAlgebra R a b) := by
  rw [Unitary.mem_iff_self_mul_star, ← algebraMap_norm_eq_mul_star]
  simp [← algebraMap_inj (R := R) (a := a) (b := b)]

alias ⟨mem_unitary, norm_eq_one⟩ := norm_eq_one_iff_mem_unitary

/-- The kernel of the norm map on `QuadraticAlgebra R a b` equals
the submonoid of unitary elements. -/
theorem mker_norm_eq_unitary :
    MonoidHom.mker (@norm R a b _) = unitary (QuadraticAlgebra R a b) :=
  Submonoid.ext fun _ => norm_eq_one_iff_mem_unitary

open nonZeroDivisors

theorem algebraMap_mem_nonZeroDivisors_iff {r : R} :
    algebraMap R (QuadraticAlgebra R a b) r ∈ (QuadraticAlgebra R a b)⁰ ↔ r ∈ R⁰ := by
  simp only [mem_nonZeroDivisors_iff_right]
  constructor
  · intro H x hxr
    rw [← algebraMap_inj, map_zero]
    apply H
    rw [← map_mul, hxr, map_zero]
  · intro h z hz
    rw [QuadraticAlgebra.ext_iff, re_zero, im_zero] at hz
    simp only [re_mul, algebraMap_re, algebraMap_im, mul_zero, add_zero, im_mul, zero_add] at hz
    simp [QuadraticAlgebra.ext_iff, re_zero, im_zero, h _ hz.left, h _ hz.right]

@[deprecated (since := "2025-12-15")]
alias coe_mem_nonZeroDivisors_iff := algebraMap_mem_nonZeroDivisors_iff

theorem star_mem_nonZeroDivisors {z : QuadraticAlgebra R a b}
    (hz : z ∈ (QuadraticAlgebra R a b)⁰) :
    star z ∈ (QuadraticAlgebra R a b)⁰ := by
  rw [mem_nonZeroDivisors_iff_right] at hz ⊢
  intro w hw
  apply star_involutive.injective
  rw [star_zero]
  apply hz
  rw [← star_involutive z, ← star_mul, mul_comm, hw, star_zero]

theorem star_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    star z ∈ (QuadraticAlgebra R a b)⁰ ↔ z ∈ (QuadraticAlgebra R a b)⁰ := by
  refine ⟨fun h ↦ ?_, star_mem_nonZeroDivisors⟩
  rw [← star_involutive z]
  exact star_mem_nonZeroDivisors h

theorem norm_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    z.norm ∈ R⁰ ↔ z ∈ (QuadraticAlgebra R a b)⁰ := by
  constructor
  · simp only [mem_nonZeroDivisors_iff_right]
    intro h w hw
    have : norm z • w = 0 := by
      rw [← C_mul_eq_smul, C_eq_algebraMap, algebraMap_norm_eq_mul_star, mul_comm, ← mul_assoc, hw,
        zero_mul]
    simp only [QuadraticAlgebra.ext_iff, re_smul, smul_eq_mul, mul_comm, re_zero, im_smul,
      im_zero] at this
    ext <;> simp [h _ this.left, h _ this.right]
  · intro hz
    rw [← algebraMap_mem_nonZeroDivisors_iff, algebraMap_norm_eq_mul_star]
    exact Submonoid.mul_mem _ hz (star_mem_nonZeroDivisors hz)

end norm

section field

variable [Field R] [Hab : Fact (∀ r, r ^ 2 ≠ a + b * r)]

lemma norm_eq_zero_iff_eq_zero {z : QuadraticAlgebra R a b} :
    norm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    rw [norm_def] at hz
    by_cases h : z.im = 0
    · simp [h] at hz
      aesop
    · exfalso
      rw [← pow_two, sub_eq_zero, ← eq_sub_iff_add_eq] at hz
      apply Hab.out (-z.re / z.im)
      grind
  · intro hz
    simp [hz]

/-- If `R` is a field and there is no `r : R` such that `r ^ 2 = a + b * r`,
then `QuadraticAlgebra R a b` is a field. -/
instance : Field (QuadraticAlgebra R a b) where
  inv z := (norm z)⁻¹ • star z
  mul_inv_cancel z hz := by
    rw [ne_eq, ← norm_eq_zero_iff_eq_zero] at hz
    simp only [Algebra.mul_smul_comm]
    rw [← C_mul_eq_smul, C_eq_algebraMap, ← algebraMap_norm_eq_mul_star, ← map_mul,
      inv_mul_cancel₀ hz, map_one]
  inv_zero := by simp
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end field

end QuadraticAlgebra
