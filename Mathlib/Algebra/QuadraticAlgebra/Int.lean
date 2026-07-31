/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discr

/-!
# Quadratic algebras over `ℤ`

Over `ℤ`, the discriminant is a complete invariant: it sets up a bijection between the
isomorphism classes of quadratic algebras and the integers `D ≡ 0, 1 mod 4`. We do not bundle
this bijection into a single `Equiv`; it is witnessed by `nonempty_algEquiv_int_iff` (two
algebras are isomorphic iff they have the same discriminant), `discr_ofDiscr` (every such `D`
is realised by the canonical representative `ofDiscr D`) and `algEquivOfDiscr` (every algebra
is isomorphic to `ofDiscr` of its discriminant).

## Main definitions

* `QuadraticAlgebra.Int.ofDiscr`: the quadratic ring `QuadraticAlgebra ℤ m σ` of discriminant
  `D`, where `σ = D % 4 ∈ {0, 1}` and `m = (D - σ) / 4`.

## Main results

* `QuadraticAlgebra.Int.discr_ofDiscr`: the discriminant of `ofDiscr D` is `D`, for
  `D ≡ 0, 1 mod 4`.
* `QuadraticAlgebra.Int.algEquivOfDiscr`: every `QuadraticAlgebra ℤ a b` is isomorphic to
  `ofDiscr (discr a b)`.
-/

@[expose] public section

namespace QuadraticAlgebra.Int

/-- The quadratic ring of discriminant `D`: `QuadraticAlgebra ℤ m σ` with `σ = D % 4 ∈ {0, 1}`
and `m = (D - σ) / 4` so that, for `D ≡ 0, 1 mod 4`, its discriminant is `D`,
see `discr_ofDiscr`. -/
abbrev ofDiscr (D : ℤ) : Type := QuadraticAlgebra ℤ (D / 4) (D % 4)

/-- For `D ≡ 0, 1 mod 4`, the discriminant of the quadratic ring `ofDiscr D` is `D`. -/
theorem discr_ofDiscr {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    discr (D / 4) (D % 4) = D := by
  grind [discr_def]

/-- Every quadratic algebra over `ℤ` is isomorphic to the quadratic ring of its discriminant,
obtained by translating `ω` by the integer `⌊b / 2⌋`. -/
@[simps!]
noncomputable def algEquivOfDiscr (a b : ℤ) :
    QuadraticAlgebra ℤ a b ≃ₐ[ℤ] ofDiscr (discr a b) :=
  mapEquiv (discr a b / 4) (discr a b % 4) 1 (b / 2)
    (by
      rw [discr_def]
      have : (b % 2) * (b / 2) = b ^ 2 / 4 - (b / 2) ^ 2 := by
        obtain ⟨k, rfl | rfl⟩ := b.even_or_odd'
        · rw [Int.mul_emod_right, zero_mul]
          grind
        · rw [Int.mul_add_emod_self_left, Int.one_emod_two, one_mul]
          grind
      grind [Units.val_one, Int.mul_ediv_cancel_left _ (NeZero.ne 4), Int.add_mul_emod_self_left,
        Int.sq_emod_four])
    (by simpa [discr_def, Int.sq_emod_four, add_comm] using (Int.mul_ediv_add_emod b 2).symm)

@[simp]
theorem algEquivOfDiscr_omega (a b : ℤ) :
    algEquivOfDiscr a b ω = (b / 2) • 1 + ω := by
  ext <;> simp

end QuadraticAlgebra.Int
