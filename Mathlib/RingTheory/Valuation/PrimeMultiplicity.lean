/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes, Daniel Weber
-/
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.Algebra.Squarefree.Basic

/-!
# `multiplicity` of a prime in an integral domain as an additive valuation
-/

variable {R : Type*} [CommRing R] [IsDomain R] {p : R}

namespace AddValuation

/-- `multiplicity` of a prime in an integral domain as an additive valuation to `ℕ∞`. -/
noncomputable def multiplicity (hp : Prime p) : AddValuation R ℕ∞ :=
  AddValuation.of (emultiplicity p) (emultiplicity_zero _) (emultiplicity_of_one_right hp.not_unit)
    (fun _ _ => min_le_emultiplicity_add) fun _ _ => emultiplicity_mul hp

@[simp]
theorem multiplicity_apply {hp : Prime p} {r : R} :
    multiplicity hp r = emultiplicity p r :=
  rfl

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [UniqueFactorizationMonoid R]
variable (p : R) [hp : Fact (Prime p)]

noncomputable def adicValuation : AddValuation K (WithTop ℤ) :=
  ofValuation <|
    (toValuation <| (multiplicity hp.out).map (AddMonoidHom.withTopMap (Nat.castAddMonoidHom ℤ)) rfl
    (by simp [Nat.mono_cast])).extendToLocalization (S := nonZeroDivisors R) (B := K) <| by
      intro v hv
      apply Set.mem_compl
      intro nh
      simp only [SetLike.mem_coe, Valuation.mem_supp_iff, toValuation_apply] at nh
      apply_fun Multiplicative.toAdd at nh
      apply_fun OrderDual.ofDual at nh
      simp only [map_apply, AddMonoidHom.withTopMap_apply, Nat.coe_castAddMonoidHom, toAdd_ofAdd,
        OrderDual.ofDual_toDual] at nh
      change _ = ⊤ at nh
      simp only [WithTop.map_eq_top_iff] at nh
      exact multiplicity.finite_prime_left Fact.out (nonZeroDivisors.ne_zero hv)
        |>.emultiplicity_ne_top nh

@[simp]
theorem adicValuation_coe (r : R) :
    adicValuation K p (algebraMap R K r) = (emultiplicity p r).map (↑) := by
  simp [adicValuation]
  rfl

@[simp]
theorem adicValuation_coe_nonneg (r : R) :
    0 ≤ adicValuation K p (algebraMap R K r) := by
  simp
  cases emultiplicity p r
  · rw [WithTop.map_top]
    simp
  · erw [WithTop.map_coe]
    simp

end AddValuation
