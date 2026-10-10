/-
Copyright (c) 2026 LegaSage. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LegaSage
-/
module

public import Mathlib.RingTheory.Derivation.Basic

/-!
# Locally nilpotent derivations

This file introduces locally nilpotent derivations and proves that, over a
characteristic-zero domain, an element dividing its derivative under a locally
nilpotent derivation belongs to the kernel of that derivation.
-/

@[expose] public section

namespace Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A derivation is locally nilpotent if every element is killed by some iterate. -/
def IsLocallyNilpotent (D : Derivation R A A) : Prop :=
  ∀ x : A, ∃ n : ℕ, D.toLinearMap^[n] x = 0

/-- The iterated Leibniz rule, indexed by the antidiagonal. -/
theorem iterate_mul_antidiagonal (D : Derivation R A A) (n : ℕ) (x y : A) :
    D.toLinearMap^[n] (x * y) =
      ∑ ij ∈ Finset.antidiagonal n, n.choose ij.1 •
        (D.toLinearMap^[ij.1] x * D.toLinearMap^[ij.2] y) := by
  have hleib (a b : A) :
      D.toLinearMap (a * b) = a * D.toLinearMap b + b * D.toLinearMap a := by
    change D (a * b) = a * D b + b * D a
    rw [D.leibniz]
    simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (M := A) (fun i j => D.toLinearMap^[i] x * D.toLinearMap^[j] y) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul]
    simp only [hleib, mul_add, Finset.sum_add_distrib, Algebra.smul_def]
    apply congrArg₂ (· + ·)
    · refine Finset.sum_congr rfl fun ij hij => ?_
      ring
    · refine Finset.sum_congr rfl fun ij hij => ?_
      rw [n.choose_symm_of_eq_add (Finset.mem_antidiagonal.1 hij).symm]
      ring

/-- The iterated Leibniz rule, indexed by one exponent. -/
theorem iterate_mul (D : Derivation R A A) (n : ℕ) (x y : A) :
    D.toLinearMap^[n] (x * y) =
      ∑ k ∈ Finset.range (n + 1), n.choose k •
        (D.toLinearMap^[k] x * D.toLinearMap^[n - k] y) := by
  rw [iterate_mul_antidiagonal D n x y]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => n.choose i • (D.toLinearMap^[i] x * D.toLinearMap^[j] y)) n

/-- Once an iterate vanishes, all later iterates vanish. -/
theorem iterate_eq_zero_of_le (D : Derivation R A A) {x : A} {m n : ℕ}
    (hmn : m ≤ n) (hx : D.toLinearMap^[m] x = 0) :
    D.toLinearMap^[n] x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_comm, Function.iterate_add_apply, hx]
  simp

/-- Only the top nonvanishing derivatives contribute to the corresponding
iterate of a product. -/
theorem iterate_mul_at_top (D : Derivation R A A) (x y : A) (m n : ℕ)
    (hx : D.toLinearMap^[m + 1] x = 0)
    (hy : D.toLinearMap^[n + 1] y = 0) :
    D.toLinearMap^[m + n] (x * y) =
      (m + n).choose m • (D.toLinearMap^[m] x * D.toLinearMap^[n] y) := by
  rw [iterate_mul_antidiagonal]
  apply Finset.sum_eq_single (m, n)
  · rintro ⟨a, b⟩ hab hab_ne
    have hab_sum : a + b = m + n := Finset.mem_antidiagonal.mp hab
    have hne : a ≠ m ∨ b ≠ n := by
      by_cases ha : a = m
      · right
        intro hb
        exact hab_ne (Prod.ext ha hb)
      · exact Or.inl ha
    by_cases ham : a ≤ m
    · have hn : n + 1 ≤ b := by omega
      have hz := iterate_eq_zero_of_le D hn hy
      rw [hz, mul_zero]
      simp
    · have hm : m + 1 ≤ a := by omega
      have hz := iterate_eq_zero_of_le D hm hx
      rw [hz, zero_mul]
      simp
  · simp

/-- The least exponent whose iterate kills an element. -/
noncomputable def nilpotenceIndex (D : Derivation R A A) (hD : IsLocallyNilpotent D)
    (x : A) : ℕ :=
  @Nat.find _ (Classical.decPred _) (hD x)

theorem iterate_nilpotenceIndex (D : Derivation R A A) (hD : IsLocallyNilpotent D)
    (x : A) : D.toLinearMap^[nilpotenceIndex D hD x] x = 0 :=
  @Nat.find_spec _ (Classical.decPred _) (hD x)

theorem nilpotenceIndex_pos (D : Derivation R A A) (hD : IsLocallyNilpotent D)
    {x : A} (hx : x ≠ 0) : 0 < nilpotenceIndex D hD x := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have h := iterate_nilpotenceIndex D hD x
  have : x = 0 := by simpa [hzero] using h
  exact hx this

theorem iterate_pred_nilpotenceIndex_ne_zero (D : Derivation R A A)
    (hD : IsLocallyNilpotent D) {x : A} (hx : x ≠ 0) :
    D.toLinearMap^[nilpotenceIndex D hD x - 1] x ≠ 0 := by
  classical
  apply Nat.find_min (hD x)
  exact Nat.sub_lt (nilpotenceIndex_pos D hD hx) (by decide)

namespace IsLocallyNilpotent

/-- In a characteristic-zero domain, an element which divides its derivative under a locally
nilpotent derivation belongs to the kernel of that derivation. -/
theorem apply_eq_zero_of_dvd [IsDomain A] [CharZero A]
    {D : Derivation R A A} (hD : D.IsLocallyNilpotent) {f : A}
    (hdiv : f ∣ D f) : D f = 0 := by
  rcases hdiv with ⟨g, hg⟩
  by_cases hf : f = 0
  · subst f
    simp
  by_cases hgz : g = 0
  · simpa [hgz] using hg
  let m := nilpotenceIndex D hD f - 1
  let n := nilpotenceIndex D hD g - 1
  have hm_succ : m + 1 = nilpotenceIndex D hD f := by
    dsimp [m]
    exact Nat.sub_add_cancel (nilpotenceIndex_pos D hD hf)
  have hn_succ : n + 1 = nilpotenceIndex D hD g := by
    dsimp [n]
    exact Nat.sub_add_cancel (nilpotenceIndex_pos D hD hgz)
  have hfm : D.toLinearMap^[m] f ≠ 0 := by
    simpa [m] using iterate_pred_nilpotenceIndex_ne_zero D hD hf
  have hgn : D.toLinearMap^[n] g ≠ 0 := by
    simpa [n] using iterate_pred_nilpotenceIndex_ne_zero D hD hgz
  have hf_succ : D.toLinearMap^[m + 1] f = 0 := by
    rw [hm_succ]
    exact iterate_nilpotenceIndex D hD f
  have hg_succ : D.toLinearMap^[n + 1] g = 0 := by
    rw [hn_succ]
    exact iterate_nilpotenceIndex D hD g
  have htop : D.toLinearMap^[m + n] (f * g) ≠ 0 := by
    rw [iterate_mul_at_top D f g m n hf_succ hg_succ]
    rw [nsmul_eq_mul]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right m n)).ne')
      (mul_ne_zero hfm hgn)
  have hleft : D.toLinearMap^[m + n] (D f) = 0 := by
    change D.toLinearMap^[m + n] (D.toLinearMap f) = 0
    rw [← Function.iterate_succ_apply]
    exact iterate_eq_zero_of_le D (by omega) hf_succ
  exact (htop ((congrArg (D.toLinearMap^[m + n]) hg).symm.trans hleft)).elim

end IsLocallyNilpotent

end Derivation
