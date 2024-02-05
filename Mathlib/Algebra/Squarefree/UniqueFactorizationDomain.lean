/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain

/-!
# Square-free elements in decomposition monoids

## Main results:
 * `squarefree_mul_iff`: `x * y` is square-free iff `x` and `y` have no common factors and are
   themselves square-free.

-/


-- ? TODO: rename the file to Squarefree/DecompositionMonoid ..

variable {R : Type*} [CancelCommMonoidWithZero R] {x y p d : R}

open UniqueFactorizationMonoid

namespace Squarefree

theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right {k : ℕ}
    (hx : Squarefree x) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ y := by
  by_cases hxp : p ∣ x
  · obtain ⟨x', rfl⟩ := hxp
    have hx' : ¬ p ∣ x' := fun contra ↦ hp.not_unit <| hx p (mul_dvd_mul_left p contra)
    replace h : p ^ k ∣ x' * y := by
      rw [pow_succ, mul_assoc] at h
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp h
    exact hp.pow_dvd_of_dvd_mul_left _ hx' h
  · exact (pow_dvd_pow _ k.le_succ).trans (hp.pow_dvd_of_dvd_mul_left _ hxp h)

theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left {k : ℕ}
    (hy : Squarefree y) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ x := by
  rw [mul_comm] at h
  exact pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hy hp h

end Squarefree

variable [UniqueFactorizationMonoid R]

-- TODO: WfDvdMonoid (or even atomic) is enough if Prime is replaced by Irreducible
theorem squarefree_iff (hx₀ : x ≠ 0) : Squarefree x ↔ ∀ p, Prime p → ¬ (p * p ∣ x) := by
  refine ⟨fun h p hp hp' ↦ hp.not_unit (h p hp'), fun h d hd ↦ by_contra fun hdu ↦ ?_⟩
  have hd₀ : d ≠ 0 := ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero hx₀ hd) (dvd_mul_left d d)
  obtain ⟨p, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd₀
  exact h p (irreducible_iff_prime.mp irr) ((mul_dvd_mul dvd dvd).trans hd)

namespace Squarefree

-- TODO: generalize to DecompositionMonoid; same for the next.
theorem dvd_of_squarefree_of_mul_dvd_mul_right
    (hx : Squarefree x) (h : d * d ∣ x * y) :
    d ∣ y := by
  nontriviality R
  rcases eq_or_ne x 0 with rfl | hx₀
  · have := not_squarefree_zero hx; contradiction
  induction' d using induction_on_coprime with u hu p k hp a b hab' ha hb
  · simpa [hx₀] using h
  · exact hu.dvd
  · cases' k with k; · simp
    apply pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right hx hp
    rw [← pow_add] at h
    suffices p ^ ((k + 1) + 1) ∣ p ^ ((k + 1) + (k + 1)) from dvd_trans this h
    apply pow_dvd_pow
    omega
  · rw [mul_mul_mul_comm] at h
    exact mul_dvd_of_coprime hab' (ha <| dvd_of_mul_right_dvd h) (hb <| dvd_of_mul_left_dvd h)

theorem dvd_of_squarefree_of_mul_dvd_mul_left
    (hy : Squarefree y) (h : d * d ∣ x * y) :
    d ∣ x := by
  rw [mul_comm x y] at h
  exact dvd_of_squarefree_of_mul_dvd_mul_right hy h

end Squarefree

-- TODO: generalize to DecompositionMonoid
-- then `exists_squarefree_dvd_pow_of_ne_zero` below
-- automatically generalizes to DecompositionMonoid + WfDvdMonoid, but that's equivalent to UFM
theorem squarefree_mul_iff :
    Squarefree (x * y) ↔ (∀ d, d ∣ x → d ∣ y → IsUnit d) ∧ Squarefree x ∧ Squarefree y := by
  nontriviality R
  refine ⟨fun h ↦ ⟨fun d hx hy ↦ h d (mul_dvd_mul hx hy),
    h.of_mul_left, h.of_mul_right⟩, fun ⟨hxy, hx, hy⟩ ↦ ?_⟩
  intro d
  induction' d using induction_on_prime with _ hu _ p _ hp _
  · simp [hx.ne_zero, hy.ne_zero]
  · exact fun _ ↦ hu
  · intro contra
    exfalso
    apply hp.not_unit
    suffices p ∣ x ∧ p ∣ y from hxy p this.1 this.2
    replace contra : p * p ∣ x * y := by
      rw [mul_mul_mul_comm] at contra; exact dvd_of_mul_right_dvd contra
    exact ⟨hy.dvd_of_squarefree_of_mul_dvd_mul_left contra,
      hx.dvd_of_squarefree_of_mul_dvd_mul_right contra⟩

lemma exists_squarefree_dvd_pow_of_ne_zero (hx : x ≠ 0) :
    ∃ (y : R) (n : ℕ), Squarefree y ∧ y ∣ x ∧ x ∣ y ^ n := by
  induction' x using WfDvdMonoid.induction_on_irreducible with u hu z p hz hp ih
  · contradiction
  · exact ⟨1, 0, squarefree_one, one_dvd u, hu.dvd⟩
  · obtain ⟨y, n, hy, hyx, hy'⟩ := ih hz
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨p, 1, hp.squarefree, dvd_mul_right p z, by simp [isUnit_of_dvd_one (pow_zero y ▸ hy')]⟩
    by_cases hp' : p ∣ y
    · exact ⟨y, n + 1, hy, dvd_mul_of_dvd_right hyx _,
        mul_comm p z ▸ pow_succ' y n ▸ mul_dvd_mul hy' hp'⟩
    · suffices Squarefree (p * y) from ⟨p * y, n, this,
        mul_dvd_mul_left p hyx, mul_pow p y n ▸ mul_dvd_mul (dvd_pow_self p hn.ne') hy'⟩
      exact squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hp', hp.squarefree, hy⟩
