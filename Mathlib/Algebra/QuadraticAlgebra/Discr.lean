/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.LinearAlgebra.Determinant

/-!
# Discriminant of a quadratic algebra

For `QuadraticAlgebra R a b` (with convention `ω² = a + b·ω`), we define its discriminant
`discr a b = b ^ 2 + 4 * a`, the discriminant of the polynomial `X ^ 2 - b * X - a`.

We study how the discriminant transforms under a change of generator `ω ↦ u • ω + k`
(`QuadraticAlgebra.map` / `QuadraticAlgebra.mapEquiv`), showing `discr` is multiplied
by `u ^ 2`, and deduce that the discriminant classifies quadratic algebras up to isomorphism:
modulo squares of units when `2` is invertible, and exactly over `ℤ`.

We also characterise, when `2 ≠ 0`, when `QuadraticAlgebra K a b` is a field over a
field `K`, namely when `discr a b` is not a square.

This is **false in characteristic `2`**: over `𝔽₂` the parameters `(0, 1)` and `(1, 1)` share
discriminant `1`, yet `X² − X` splits (giving `𝔽₂ × 𝔽₂`) while `X² + X + 1` is irreducible
(giving `𝔽₄`); the correct invariant there is the Artin–Schreier class.

For `u` not a unit, `map` is the inclusion of an order of conductor `u`, with discriminant
multiplied by `u ^ 2` (e.g. `ℤ[√d] ⊂ ℤ[(1+√d)/2]` for `d ≡ 1 mod 4` is `u = 2`, `k = -1`).
Note `discr d 0 = 4 * d`, not `d`, matching the discriminant `4d` of `ℤ[√d]`.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*}

section discr

/-- The discriminant of the quadratic algebra `QuadraticAlgebra R a b`, that is, the
discriminant `b ^ 2 + 4 * a` of the polynomial `X ^ 2 - b * X - a`. -/
def discr [CommSemiring R] (a b : R) : R := b ^ 2 + 4 * a

theorem discr_def [CommSemiring R] (a b : R) : discr a b = b ^ 2 + 4 * a := rfl

/-- `z.im ^ 2` times the discriminant of the algebra equals `trace z ^ 2 - 4 * norm z`. -/
theorem im_sq_mul_discr [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) :
    z.im ^ 2 * discr a b = trace z ^ 2 - 4 * norm z := by
  rw [trace_apply, norm_def, discr_def]; ring

-- The `a = 1` case of `Mathlib.Algebra.QuadraticDiscriminant`, reproved to avoid its heavy
-- transitive import of `Mathlib.Order.Filter.AtTopBot.Field`.
/-- If `2` is invertible, the polynomial `X ^ 2 - b * X - a` has a root if and only if the
discriminant is a square. -/
theorem exists_sq_eq_iff_isSquare_discr [CommRing R] [Invertible (2 : R)] {a b : R} :
    (∃ r : R, r ^ 2 = a + b * r) ↔ IsSquare (discr a b) := by
  rw [isSquare_iff_exists_sq]
  have h2 := mul_invOf_self (2 : R)
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨2 * r - b, by rw [discr_def]; grind⟩, fun ⟨s, hs⟩ ↦ ⟨⅟2 * (b + s), ?_⟩⟩
  rw [discr_def] at hs
  grind

end discr

section map

variable [CommRing R]

-- The quadratic relation satisfied by the new generator `u • ω + k`; this is what makes
-- `map` well defined. Stated with `x * x` rather than `x ^ 2` to match the shape of the
-- subtype condition of `lift` (`{ u // u * u = a • 1 + b • u }`), so it feeds `map` verbatim.
private theorem map_relation (a b u k : R) :
    (u • ω + algebraMap R (QuadraticAlgebra R a b) k) *
        (u • ω + algebraMap R (QuadraticAlgebra R a b) k) =
      (u ^ 2 * a - u * b * k - k ^ 2) • 1 +
        (u * b + 2 * k) • (u • ω + algebraMap R (QuadraticAlgebra R a b) k) := by
  ext <;> simp <;> ring

/-- The `R`-algebra map induced by the change of generator `ω ↦ u • ω + k`, see `map_omega`. -/
@[simps!]
def map (a b u k : R) {a' b' : R} (ha : a' = u ^ 2 * a - u * b * k - k ^ 2)
    (hb : b' = u * b + 2 * k) :
    QuadraticAlgebra R a' b' →ₐ[R] QuadraticAlgebra R a b :=
  lift ⟨u • ω + algebraMap R _ k, by rw [ha, hb]; exact map_relation a b u k⟩

@[simp]
theorem map_omega (a b u k : R) {a' b' : R} (ha : a' = u ^ 2 * a - u * b * k - k ^ 2)
    (hb : b' = u * b + 2 * k) :
    map a b u k ha hb ω = u • ω + algebraMap R (QuadraticAlgebra R a b) k := by
  ext <;> simp

theorem injective_map (a b u k : R) {a' b' : R} (ha : a' = u ^ 2 * a - u * b * k - k ^ 2)
    (hb : b' = u * b + 2 * k) (hu : IsRegular u) :
    Function.Injective (map a b u k ha hb) := by
  intro z w h
  have hy : z.im = w.im := hu.right <| by simpa using congr_arg im h
  exact QuadraticAlgebra.ext (by simpa [hy] using congr_arg re h) hy

theorem discr_map (a b u k : R) :
    discr (u ^ 2 * a - u * b * k - k ^ 2) (u * b + 2 * k) = u ^ 2 * discr a b := by
  rw [discr_def, discr_def]
  ring

/-- `map` along a unit `u`, as an isomorphism. -/
@[simps! apply symm_apply]
def mapEquiv (a b : R) (u : Rˣ) (k : R) {a' b' : R}
    (ha : a' = (u : R) ^ 2 * a - (u : R) * b * k - k ^ 2)
    (hb : b' = (u : R) * b + 2 * k) :
    QuadraticAlgebra R a' b' ≃ₐ[R] QuadraticAlgebra R a b where
  __ := map a b u k ha hb
  invFun := map a' b' (u⁻¹ : Rˣ) (-(u⁻¹ : Rˣ) * k)
    (by simp only [sq, ha, mul_assoc, mul_sub, Units.inv_mul_cancel_left, hb, mul_add, neg_mul,
        mul_neg, sub_neg_eq_add, neg_neg]; ring)
    (by simp only [hb, mul_add, Units.inv_mul_cancel_left, neg_mul, mul_neg]; ring)
  left_inv _ := by ext <;> simp [mul_assoc]
  right_inv _ := by ext <;> simp [mul_assoc]

end map

section classification

variable [CommRing R] {a b a' b' : R} (f : QuadraticAlgebra R a' b' →ₐ[R] QuadraticAlgebra R a b)

private theorem smul_omega_sub_eq :
    (trace (f ω) - b') • f ω = algebraMap R _ (norm (f ω)) + a' • 1 := by
  rw [sub_smul, ← sub_neg_eq_add, sub_eq_sub_iff_sub_eq_sub, ← sq_eq_trace_smul_sub_norm,
    sub_neg_eq_add, ← map_pow, sq, omega_mul_omega_eq_add, map_add, map_smul, map_smul, map_one,
    add_comm]

/-- If `(f ω).im` is regular, an algebra map sends `ω` to an element of trace `b'`. -/
theorem trace_map_omega (h : IsRegular (f ω).im) :
    trace (f ω) = b' := by
  simpa [h.right.mul_right_eq_zero_iff, sub_eq_zero] using congr_arg im (smul_omega_sub_eq f)

/-- If `(f ω).im` is regular, an algebra map sends `ω` to an element of norm `-a'`. -/
theorem norm_map_omega (h : IsRegular (f ω).im) :
    norm (f ω) = -a' := by
  simpa [trace_map_omega f h, ← Algebra.algebraMap_eq_smul_one, add_eq_zero_iff_eq_neg,
    ← map_neg] using (smul_omega_sub_eq f).symm

/-- The transformation law in the case when `(f ω).im` is regular. -/
theorem discr_eq_im_sq_mul_discr (h : IsRegular (f ω).im) :
    discr a' b' = (f ω).im ^ 2 * discr a b := by
  rw [im_sq_mul_discr (f ω), trace_map_omega f h, norm_map_omega f h, discr_def]
  ring

/-- Any `R`-algebra isomorphism between quadratic algebras sends `ω` to an element
whose imaginary part is a unit. -/
theorem isUnit_im_omega_of_algEquiv (e : QuadraticAlgebra R a' b' ≃ₐ[R] QuadraticAlgebra R a b) :
    IsUnit (e ω).im := by
  simpa [Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply] using
    (basis a b).isUnit_det ((basis a' b').map e.toLinearEquiv)

/-- `discr_eq_im_sq_mul_discr` for an `R`-algebra isomorphism `e`, for which `(e ω).im` is
automatically a unit (`isUnit_im_omega_of_algEquiv`). -/
theorem discr_eq_im_sq_mul_discr' (e : QuadraticAlgebra R a' b' ≃ₐ[R] QuadraticAlgebra R a b) :
    discr a' b' = (e ω).im ^ 2 * discr a b := by
  rw [discr_eq_im_sq_mul_discr e.toAlgHom, AlgEquiv.toAlgHom_apply]
  exact (isUnit_im_omega_of_algEquiv e).isRegular

/-- If `2` is regular, `QuadraticAlgebra R a b` and `QuadraticAlgebra R a' b'` are isomorphic
iff `discr a b = u ^ 2 * discr a' b'` for some unit `u` with `2 ∣ b - u * b'`. -/
theorem nonempty_algEquiv_iff (h : IsRegular (2 : R)) :
    Nonempty (QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') ↔
      ∃ u : Rˣ, discr a b = (u : R) ^ 2 * discr a' b' ∧ 2 ∣ (b - u * b') := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨u, hu, ⟨k, hk⟩⟩ ↦ ⟨mapEquiv a' b' u k ?_ (by grind)⟩⟩
  · refine ⟨(isUnit_im_omega_of_algEquiv e).unit,
      by rw [discr_eq_im_sq_mul_discr' e, IsUnit.unit_spec], ⟨(e ω).re, ?_⟩⟩
    rw [IsUnit.unit_spec, sub_eq_iff_eq_add', add_comm, mul_comm _ b', ← trace_apply, eq_comm]
    exact trace_map_omega e.toAlgHom (isUnit_im_omega_of_algEquiv e).isRegular
  · rw [discr_def, discr_def] at hu
    rw [← h.left.eq_iff, mul_sub, mul_sub, ← mul_rotate, ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← hk, ← h.left.eq_iff, mul_sub, ← mul_assoc, ← mul_assoc, ← pow_two, ← mul_pow, ← hk]
    grind

/-- If `2` is invertible, the discriminant classifies quadratic algebras up to
isomorphism, modulo squares of units. -/
theorem nonempty_algEquiv_iff_of_invertible_two [Invertible (2 : R)] :
    Nonempty (QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') ↔
      ∃ u : Rˣ, discr a b = (u : R) ^ 2 * discr a' b' := by
  rw [nonempty_algEquiv_iff (isUnit_of_invertible (2 : R)).isRegular]
  simp [(isUnit_of_invertible (2 : R)).dvd]

/-- Over `ℤ` the discriminant is a complete invariant of quadratic algebras up to
isomorphism. -/
theorem nonempty_algEquiv_int_iff {a b a' b' : ℤ} :
    Nonempty (QuadraticAlgebra ℤ a b ≃ₐ[ℤ] QuadraticAlgebra ℤ a' b') ↔
      discr a b = discr a' b' := by
  rw [nonempty_algEquiv_iff (IsRegular.of_ne_zero two_ne_zero)]
  refine ⟨fun ⟨u, hu, _⟩ ↦ by rwa [Int.isUnit_sq u.isUnit, one_mul] at hu, fun h ↦ ?_⟩
  obtain _ | _ : 2 ∣ (b + b') ∨ 2 ∣ (b - b') := by
    rw [← Prime.dvd_mul (by exact Nat.prime_iff_prime_int.mp Nat.prime_two), ← sq_sub_sq]
    refine ⟨2 * a' - 2 * a, ?_⟩
    rwa [mul_sub, ← mul_assoc, ← mul_assoc, show (2 : ℤ) * 2 = 4 by norm_num,
      sub_eq_sub_iff_add_eq_add, ← discr_def, add_comm, ← discr_def]
  · exact ⟨-1, by simpa, by simpa⟩
  · exact ⟨1, by simpa, by simpa⟩

end classification

section field

/-- Bridge instance for `b = 0`: no hypothesis on the characteristic is needed. -/
instance {K : Type*} [Field K] {a : K} [Fact (¬ IsSquare a)] :
    Fact (∀ r : K, r ^ 2 ≠ a + 0 * r) :=
  ⟨fun r hr ↦ Fact.out (p := ¬ IsSquare a) ⟨r, by simpa [sq] using hr.symm⟩⟩

/-- Bridge instance in general, when `2` is invertible. -/
instance {K : Type*} [Field K] {a b : K} [NeZero (2 : K)] [Fact (¬ IsSquare (discr a b))] :
    Fact (∀ r : K, r ^ 2 ≠ a + b * r) :=
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  ⟨not_exists.mp <| exists_sq_eq_iff_isSquare_discr.not.mpr Fact.out⟩

variable {K : Type*} [Field K]

/-- If `discr a b` is a square, `QuadraticAlgebra K a b` is not a field. -/
theorem not_isField_of_isSquare_discr [NeZero (2 : K)] {a b : K}
    (h : IsSquare (discr a b)) : ¬ IsField (QuadraticAlgebra K a b) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨r, hr⟩ := exists_sq_eq_iff_isSquare_discr.mpr h
  intro hfield
  let := hfield.toField
  have : (⟨r, -1⟩ : QuadraticAlgebra K a b) ∈ nonZeroDivisors (QuadraticAlgebra K a b) := by
    simp [mem_nonZeroDivisors_iff_ne_zero, QuadraticAlgebra.ext_iff]
  rw [← norm_mem_nonZeroDivisors_iff, show norm ⟨r, -1⟩ = 0 by rw [norm_def]; grind] at this
  exact zero_notMem_nonZeroDivisors this

/-- If `2 ≠ 0` in the field `K`, `QuadraticAlgebra K a b` is a field iff `discr a b` is
not a square. -/
theorem isField_iff_not_isSquare_discr [NeZero (2 : K)] {a b : K} :
    IsField (QuadraticAlgebra K a b) ↔ ¬ IsSquare (discr a b) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  refine ⟨fun hfield h ↦ not_isField_of_isSquare_discr h hfield, fun h ↦ ?_⟩
  have : Fact (¬ IsSquare (discr a b)) := ⟨h⟩
  exact Field.toIsField (QuadraticAlgebra K a b)

-- The `b = 0` bridge makes the `Field` instance inferable from `¬ IsSquare a` alone.
example {a : K} [Fact (¬ IsSquare a)] : Field (QuadraticAlgebra K a 0) := inferInstance

-- The general bridge makes the `Field` instance inferable from `¬ IsSquare (discr a b)`
-- if `2 ≠ 0` in the field.
example {a b : ℚ} [Fact (¬ IsSquare (discr a b))] : Field (QuadraticAlgebra ℚ a b) := inferInstance

end field

end QuadraticAlgebra
