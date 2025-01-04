/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes, Daniel Weber
-/
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.Algebra.UniqueFactorizationDomain.Multiplicity

/-!
# `multiplicity` of a prime in an integral domain as an additive valuation
-/

variable {R : Type*} [CommRing R] [IsDomain R] {p : R}

namespace AddValuation

/-- `multiplicity` of a prime in an integral domain as an additive valuation to `ℕ∞`. -/
noncomputable def multiplicity (hp : Prime p) : AddValuation R ℕ∞ :=
  AddValuation.of (emultiplicity p) (emultiplicity_zero _) (emultiplicity_of_one_right hp.not_unit)
    (fun _ _ => min_le_emultiplicity_add) fun _ _ => emultiplicity_mul hp

@[deprecated (since := "2024-11-07")]
alias _root_.multiplicity_addValuation := multiplicity

@[simp]
theorem multiplicity_apply {hp : Prime p} {r : R} :
    multiplicity hp r = emultiplicity p r :=
  rfl

@[deprecated (since := "2024-11-07")]
alias _root_.multiplicity_addValuation_apply := multiplicity_apply

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [UniqueFactorizationMonoid R]
variable (p : R) [hp : Fact (Prime p)]

/--
The valuation on a fraction ring to `WithTop ℤ` given by a prime.
-/
noncomputable def adicValuation : AddValuation K (WithTop ℤ) :=
  ofValuation <|
    (toValuation <|
      (multiplicity hp.out).map (AddMonoidHom.ENatMap (Nat.castAddMonoidHom ℤ)) rfl
        (by simp [Nat.mono_cast, Monotone.comp, OrderHomClass.mono]))
      |>.extendToLocalization (S := nonZeroDivisors R) (B := K) <| by
      intro v hv
      apply Set.mem_compl
      intro nh
      simp only [SetLike.mem_coe, Valuation.mem_supp_iff, toValuation_apply, map_apply,
        multiplicity_apply, AddMonoidHom.ENatMap_apply, Nat.coe_castAddMonoidHom,
        ofAdd_toDual_eq_zero_iff, ENat.map_eq_top_iff, emultiplicity_eq_top] at nh
      exact nh (.of_prime_left Fact.out (nonZeroDivisors.ne_zero hv))

@[simp]
theorem adicValuation_coe (r : R) :
    adicValuation p (algebraMap R K r) = (emultiplicity p r).map (↑) := by
  simp [adicValuation]

variable {β : Type*} [Zero β]

lemma adicValuation_coe_pos_iff (a : R) :
    0 < adicValuation p (algebraMap R K a) ↔ p ∣ a := by
  simp [lt_iff_le_and_ne, ENat.zero_eq_map_iff, emultiplicity_eq_zero]


open IsFractionRing

lemma adicValuation_pos_iff (a : K) :
    0 < adicValuation p a ↔ p ∣ num R a := by
  nth_rw 1 [← mk'_num_den' (A := R) a]
  simp only [map_div, adicValuation_coe, LinearOrderedAddCommGroupWithTop.sub_pos,
    ENat.map_eq_top_iff, emultiplicity_eq_top]
  have : FiniteMultiplicity p (den R a) := .of_prime_left hp.out (by simp)
  simp only [this, not_true_eq_false, or_false]
  rw [(ENat.strictMono_map_iff.mpr Nat.strictMono_cast).lt_iff_lt]
  constructor
  · exact fun h ↦ emultiplicity_ne_zero.mp (ENat.not_lt_zero _ <| · ▸ h)
  · intro h
    convert emultiplicity_pos_of_dvd h
    exact emultiplicity_eq_zero.mpr <| hp.out.not_unit ∘ num_den_reduced _ _ h

lemma adicValuation_neg_iff (a : K) :
    adicValuation p a < 0 ↔ p ∣ den R a := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, not_top_lt, false_iff]
    exact hp.out.not_unit ∘ (isUnit_of_dvd_unit · isUnit_den_zero)
  convert adicValuation_pos_iff p a⁻¹ using 1
  · simp only [map_inv]
    cases h : adicValuation p a
    · simp [ha] at h
    norm_cast
    exact Left.neg_pos_iff.symm
  · exact (associated_den_num_inv a ha).dvd_iff_dvd_right

end AddValuation
