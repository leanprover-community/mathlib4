/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.RingTheory.Nilpotent
import Mathlib.RingTheory.Ideal.QuotientOperations

#align_import ring_theory.quotient_nilpotent from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Nilpotent elements in quotient rings
-/

theorem Ideal.isRadical_iff_quotient_reduced {R : Type*} [CommRing R] (I : Ideal R) :
    I.IsRadical ↔ IsReduced (R ⧸ I) := by
  conv_lhs => rw [← @Ideal.mk_ker R _ I]
  -- ⊢ IsRadical (RingHom.ker (Quotient.mk I)) ↔ IsReduced (R ⧸ I)
  exact RingHom.ker_isRadical_iff_reduced_of_surjective (@Ideal.Quotient.mk_surjective R _ I)
  -- 🎉 no goals
#align ideal.is_radical_iff_quotient_reduced Ideal.isRadical_iff_quotient_reduced

variable {R S : Type*} [CommSemiring R] [CommRing S] [Algebra R S] (I : Ideal S)


/-- Let `P` be a property on ideals. If `P` holds for square-zero ideals, and if
  `P I → P (J ⧸ I) → P J`, then `P` holds for all nilpotent ideals. -/
theorem Ideal.IsNilpotent.induction_on (hI : IsNilpotent I)
    {P : ∀ ⦃S : Type _⦄ [CommRing S], ∀ _I : Ideal S, Prop}
    (h₁ : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I : Ideal S, I ^ 2 = ⊥ → P I)
    (h₂ : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I J : Ideal S, I ≤ J → P I →
      P (J.map (Ideal.Quotient.mk I)) → P J) :
    P I := by
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI
  -- ⊢ P I
  induction' n using Nat.strong_induction_on with n H generalizing S
  -- ⊢ P I
  by_cases hI' : I = ⊥
  -- ⊢ P I
  · subst hI'
    -- ⊢ P ⊥
    apply h₁
    -- ⊢ ⊥ ^ 2 = ⊥
    rw [← Ideal.zero_eq_bot, zero_pow]
    -- ⊢ 0 < 2
    exact zero_lt_two
    -- 🎉 no goals
  cases' n with n
  -- ⊢ P I
  · rw [pow_zero, Ideal.one_eq_top] at hI
    -- ⊢ P I
    haveI := subsingleton_of_bot_eq_top hI.symm
    -- ⊢ P I
    exact (hI' (Subsingleton.elim _ _)).elim
    -- 🎉 no goals
  cases' n with n
  -- ⊢ P I
  · rw [pow_one] at hI
    -- ⊢ P I
    exact (hI' hI).elim
    -- 🎉 no goals
  apply h₂ (I ^ 2) _ (Ideal.pow_le_self two_ne_zero)
  -- ⊢ P (I ^ 2)
  · apply H n.succ _ (I ^ 2)
    -- ⊢ (I ^ 2) ^ Nat.succ n = ⊥
    · rw [← pow_mul, eq_bot_iff, ← hI, Nat.succ_eq_add_one, Nat.succ_eq_add_one]
      -- ⊢ I ^ (2 * (n + 1)) ≤ I ^ (n + 1 + 1)
      apply Ideal.pow_le_pow (by linarith)
      -- 🎉 no goals
    · exact n.succ.lt_succ_self
      -- 🎉 no goals
  · apply h₁
    -- ⊢ map (Quotient.mk (I ^ 2)) I ^ 2 = ⊥
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
    -- 🎉 no goals
#align ideal.is_nilpotent.induction_on Ideal.IsNilpotent.induction_on

theorem IsNilpotent.isUnit_quotient_mk_iff {R : Type*} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) {x : R} : IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x := by
  refine' ⟨_, fun h => h.map <| Ideal.Quotient.mk I⟩
  -- ⊢ IsUnit (↑(Ideal.Quotient.mk I) x) → IsUnit x
  revert x
  -- ⊢ ∀ {x : R}, IsUnit (↑(Ideal.Quotient.mk I) x) → IsUnit x
  apply Ideal.IsNilpotent.induction_on (R := R) (S := R) I hI <;> clear hI I
  -- ⊢ ∀ ⦃S : Type u_3⦄ [inst : CommRing S] (I : Ideal S), I ^ 2 = ⊥ → ∀ {x : S}, I …
                                                                  -- ⊢ ∀ ⦃S : Type u_3⦄ [inst : CommRing S] (I : Ideal S), I ^ 2 = ⊥ → ∀ {x : S}, I …
                                                                  -- ⊢ ∀ ⦃S : Type u_3⦄ [inst : CommRing S] (I J : Ideal S), I ≤ J → (∀ {x : S}, Is …
  swap
  -- ⊢ ∀ ⦃S : Type u_3⦄ [inst : CommRing S] (I J : Ideal S), I ≤ J → (∀ {x : S}, Is …
  · introv e h₁ h₂ h₃
    -- ⊢ IsUnit x
    apply h₁
    -- ⊢ IsUnit (↑(Ideal.Quotient.mk I) x)
    apply h₂
    -- ⊢ IsUnit (↑(Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk I) J)) (↑(Ideal.Qu …
    exact
      h₃.map
        ((DoubleQuot.quotQuotEquivQuotSup I J).trans
              (Ideal.quotEquivOfEq (sup_eq_right.mpr e))).symm.toRingHom
  · introv e H
    -- ⊢ IsUnit x
    skip
    -- ⊢ IsUnit x
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑H.unit⁻¹ : S ⧸ I)
    -- ⊢ IsUnit x
    have : Ideal.Quotient.mk I (x * y) = Ideal.Quotient.mk I 1 := by
      rw [map_one, _root_.map_mul, hy, IsUnit.mul_val_inv]
    rw [Ideal.Quotient.eq] at this
    -- ⊢ IsUnit x
    have : (x * y - 1) ^ 2 = 0 := by
      rw [← Ideal.mem_bot, ← e]
      exact Ideal.pow_mem_pow this _
    have : x * (y * (2 - x * y)) = 1 := by
      rw [eq_comm, ← sub_eq_zero, ← this]
      ring
    exact isUnit_of_mul_eq_one _ _ this
    -- 🎉 no goals
#align is_nilpotent.is_unit_quotient_mk_iff IsNilpotent.isUnit_quotient_mk_iff
