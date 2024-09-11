/-
Copyright (c) 2024 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Huanyu Zheng
-/
import Mathlib.Algebra.CharP.Algebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- For a commutative semiring `R` and a `R`-module `M`, if `M` contains an
  element `x` that can eliminate `r` in `r • x = 0` (finding such element usually
  depends on specific `•`), then the characteristic of `R` is equal to the
  characteristic of `R`-linear endomorphism of `M`.-/
instance char_eq_if {p : ℕ} [hchar : CharP R p]
  (hreduction : ∃ x : M, ∀ r : R, r • x = 0 → r = 0) : CharP (M →ₗ[R] M) p where
  cast_eq_zero_iff' := by
    intro n
    replace hchar := hchar.1 n
    have reduce : (n : M →ₗ[R] M) = (n : R) • 1 := by
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [reduce, LinearMap.ext_iff, hchar.symm]
    simp only [LinearMap.smul_apply, LinearMap.one_apply, LinearMap.zero_apply]
    refine ⟨fun h ↦ Exists.casesOn hreduction fun x hx ↦ hx (n : R) (h x),
      fun h ↦ (congrArg (fun t ↦ ∀ (x : M), t • x = 0) h).mpr fun x ↦ zero_smul R x⟩

variable {D : Type*} [DivisionRing D]
local notation "k" => (Subring.center D)

instance : Algebra k D := Algebra.ofModule smul_mul_assoc mul_smul_comm

/--The characteristic of a division ring is equal to the characteristic of its
  center-/
theorem center_char_iff {p : ℕ} : CharP D p ↔ CharP k p :=
  (@RingHom.charP_iff k D _ _ (algebraMap k D)
    (NoZeroSMulDivisors.algebraMap_injective k D) p).symm

instance {p : ℕ} [hchar : CharP D p] : CharP (D →ₗ[k] D) p := by
  letI : CharP k p := center_char_iff.1 hchar
  refine char_eq_if (p := p) (R := k) (M := D) ⟨1, ?_⟩
  intro r hr
  have : r • (1 : D) = r := by
    simp [(· • ·), SMul.smul]
  exact ZeroMemClass.coe_eq_zero.mp <| this ▸ hr
