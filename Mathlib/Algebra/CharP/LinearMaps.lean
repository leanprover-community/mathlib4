/-
Copyright (c) 2024 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Huanyu Zheng
-/
import Mathlib.Algebra.CharP.Subring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- For a commutative semiring `R` and a `R`-module `M`, if `M` contains an
  element `x` that can eliminate `r` in `r • x = 0` (finding such element usually
  depends on specific `•`), then the characteristic of `R` is equal to the
  characteristic of `R`-linear endomorphism of `M`.-/
theorem char_eq_if {p : ℕ} [hchar : CharP R p]
  (hreduction : ∃ x : M, ∀ r : R, r • x = 0 → r = 0) : CharP (M →ₗ[R] M) p where
  cast_eq_zero_iff' := by
    intro n
    replace hchar := hchar.1 n
    have reduce : (n : M →ₗ[R] M) = (n : R) • 1 := by
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [reduce, LinearMap.ext_iff, hchar.symm]
    refine ⟨fun h ↦ Exists.casesOn hreduction fun x hx ↦ hx n (h x),
      fun h ↦ (congrArg (fun t ↦ ∀ x, t • x = 0) h).mpr fun x ↦ zero_smul R x⟩

/-- For a division ring `D` and its center `k`, `k`-linear endomorphism
  of `D` has the same characteristic as `D`-/
instance {D : Type*} [DivisionRing D] {p : ℕ} [CharP D p] :
  CharP (D →ₗ[(Subring.center D)] D) p :=
    charP_of_injective_ringHom (RingHom.injective
      (Algebra.lmul ((Subring.center D)) D).toRingHom) p
