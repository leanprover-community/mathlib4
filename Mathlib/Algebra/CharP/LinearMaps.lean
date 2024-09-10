/-
Copyright (c) 2024 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Huanyu Zheng
-/
import Mathlib.Algebra.CharP.Algebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoidWithOne M] [Module R M]

/-- For a commutative semiring `R` and a `R`-module `M` (which is also
  an additive commutative monoid with one), if `R` satisfies reduction condition,
  then the characteristic of `R` is equal to the characteristic of `R`-linear
  endomorphism of `M`.-/
instance char_eq_if {p : ℕ} [hchar : CharP R p]
  (hreduction : ∀ (r : R), r • (1 : M) = 0 → r = 0) : CharP (M →ₗ[R] M) p where
  cast_eq_zero_iff' := by
    intro n
    replace hchar := hchar.1 n
    have reduce : (n : M →ₗ[R] M) = (n : R) • 1 := by
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [reduce, LinearMap.ext_iff, hchar.symm]
    simp only [LinearMap.smul_apply, LinearMap.one_apply, LinearMap.zero_apply]
    refine ⟨fun h ↦ hreduction n <| h 1,
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
  refine char_eq_if (p := p) (R := k) (M := D) ?_
  intro r hr
  have : r • (1 : D) = r := by
    simp [(· • ·), SMul.smul]
  rw [this] at hr
  exact ZeroMemClass.coe_eq_zero.mp hr

/-
instance {p : ℕ} [CharP D p] : CharP (D →ₗ[k] D) p :=
  let f : D →+* (D →ₗ[k] D) := {
      toFun := fun a => {
        toFun := fun x => a * x
        map_add' := fun x y ↦ LeftDistribClass.left_distrib a x y
        map_smul' := fun m x ↦ mul_smul_comm m a x
      }
      map_one' := LinearMap.ext fun x ↦ one_mul x
      map_mul' := fun x y => LinearMap.ext fun z ↦ mul_assoc x y z
      map_zero' := LinearMap.ext fun x ↦ zero_mul x
      map_add' := fun x y => LinearMap.ext fun z ↦ add_mul x y z
    }
  have inj : Function.Injective f := by
    intros x y h
    have eq : ∀ x : D, (f x) 1 = x := fun x => by
      simp only [Subring.center_toSubsemiring, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk, mul_one, f]
    rw [← eq x, ← eq y]
    exact congrFun (congrArg DFunLike.coe h) 1
  charP_of_injective_ringHom inj p
  -/
