/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module ring_theory.quotient_nilpotent
! leanprover-community/mathlib commit da420a8c6dd5bdfb85c4ced85c34388f633bc6ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Nilpotent
import Mathlib.RingTheory.Ideal.QuotientOperations

/-!
# Nilpotent elements in quotient rings
-/

-- Porting note: failed to synth RingHomClass (R →+* R ⧸ I) R (R ⧸ I)
set_option synthInstance.etaExperiment true in
theorem Ideal.isRadical_iff_quotient_reduced {R : Type _} [CommRing R] (I : Ideal R) :
    I.IsRadical ↔ IsReduced (R ⧸ I) := by
  conv_lhs => rw [← @Ideal.mk_ker R _ I]
  exact RingHom.ker_isRadical_iff_reduced_of_surjective (@Ideal.Quotient.mk_surjective R _ I)
#align ideal.is_radical_iff_quotient_reduced Ideal.isRadical_iff_quotient_reduced

variable {R S : Type _} [CommSemiring R] [CommRing S] [Algebra R S] (I : Ideal S)


/-- Let `P` be a property on ideals. If `P` holds for square-zero ideals, and if
  `P I → P (J ⧸ I) → P J`, then `P` holds for all nilpotent ideals. -/
theorem Ideal.IsNilpotent.induction_on (hI : IsNilpotent I)
    {P : ∀ ⦃S : Type _⦄ [CommRing S], ∀ _I : Ideal S, Prop}
    (h₁ : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I : Ideal S, I ^ 2 = ⊥ → P I)
    (h₂ : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I J : Ideal S, I ≤ J → P I →
    -- Porting note: etaExperiment fixes this but times out Zero (Ideal S) in IsNilpotent I
        P (@Ideal.map S (S ⧸ I) (S →+* S ⧸ I) (_) (_)
          RingHom.instRingHomClassRingHom (Ideal.Quotient.mk I) J) → P J) :
    P I := by
-- Porting note: linarith misbehaving below
  have bound (m : ℕ) : m + 1 + 1 ≤ 2 * (m + 1) := by linarith
-- Porting note: failed to synth RingHomClass (R →+* R ⧸ I) R (R ⧸ I)
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI
  revert S
  -- Porting note: lean could previously figure out the motive
  apply Nat.strong_induction_on n (p := fun n =>
    ∀ {S : Type u_1} [CommRing S] [Algebra R S] (I : Ideal S), I ^ n = ⊥ → P I)
  clear n
  intro n H S _ _ I hI
  by_cases hI' : I = ⊥
  · subst hI'
    apply h₁
    rw [← Ideal.zero_eq_bot, zero_pow]
    exact zero_lt_two
  cases' n with n
  · rw [pow_zero, Ideal.one_eq_top] at hI
    haveI := subsingleton_of_bot_eq_top hI.symm
    exact (hI' (Subsingleton.elim _ _)).elim
  cases' n with n
  · rw [pow_one] at hI
    exact (hI' hI).elim
  apply h₂ (I ^ 2) _ (Ideal.pow_le_self two_ne_zero)
  · apply H n.succ _ (I ^ 2)
    · rw [← pow_mul, eq_bot_iff, ← hI, Nat.succ_eq_add_one, Nat.succ_eq_add_one]
      -- Porting note: linarith wants AddGroup (Ideal S) to solve (n:ℕ)+1+1 ≤ 2*(n+1) 🤯
      apply Ideal.pow_le_pow <| bound n
    · exact le_refl n.succ.succ
  · apply h₁
    -- Porting note: cannot synth RingHomClass and etaExperiment causes linarith to fail in bound
    rw [← @Ideal.map_pow S (S ⧸ I^2) (S →+* S ⧸ I^2) _ _ RingHom.instRingHomClassRingHom,
      Ideal.map_quotient_self]
#align ideal.is_nilpotent.induction_on Ideal.IsNilpotent.induction_on

example (m : ℕ) : m + 1 + 1 ≤ 2 * (m + 1) := by linarith
theorem IsNilpotent.isUnit_quotient_mk_iff {R : Type _} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) {x : R} : IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x := by
-- Porting note: cannot synth RingHomClass
set_option synthInstance.etaExperiment true in
  refine' ⟨_, fun h => h.map <| Ideal.Quotient.mk I⟩
  revert x
  apply Ideal.IsNilpotent.induction_on (R := R) (S := R) I hI <;> clear hI I
  swap
  · introv e h₁ h₂ h₃
    apply h₁
    apply h₂
    exact
      h₃.map
        ((DoubleQuot.quotQuotEquivQuotSup I J).trans
              (Ideal.quotEquivOfEq (sup_eq_right.mpr e))).symm.toRingHom
  · introv e H
    skip
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑H.unit⁻¹ : S ⧸ I)
    have : Ideal.Quotient.mk I (x * y) = Ideal.Quotient.mk I 1 := by
      rw [map_one, _root_.map_mul, hy, IsUnit.mul_val_inv]
    rw [Ideal.Quotient.eq] at this
    have : (x * y - 1) ^ 2 = 0 := by
      rw [← Ideal.mem_bot, ← e]
      exact Ideal.pow_mem_pow this _
    have : x * (y * (2 - x * y)) = 1 := by
      rw [eq_comm, ← sub_eq_zero, ← this]
      ring
    exact isUnit_of_mul_eq_one _ _ this
#align is_nilpotent.is_unit_quotient_mk_iff IsNilpotent.isUnit_quotient_mk_iff

