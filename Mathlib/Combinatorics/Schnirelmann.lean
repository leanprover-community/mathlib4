/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Doga Can Sertbas
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Finset.Nat

/-!
# Schnirelmann density

We define the Schnirelmann density of a set `A` of natural numbers as
$inf_{n > 0} |A ∩ {1,...,n}| / n$. As this density is very sensitive to changes in small values,
we must exclude `0` from the infimum, and from the intersection.

## Main statements

* Simple bounds on the Schnirelmann density, that it is between 0 and 1 are given in
  `schnirelmannDensity_nonneg` and `schnirelmannDensity_le_one`.
* `schnirelmannDensity_le_of_not_mem`: If `k ∉ A`, the density can be easily upper-bounded by
  `1 - k⁻¹`

## Implementation notes

Despite the definition being noncomputable, we include a decidable instance argument, since this
makes the definition easier to use in explicit cases.
Further, we use `Finset.Ioc` rather than a set intersection since the set is finite by construction,
which reduces the proof obligations later that would arise with `Nat.card`.

## TODO
* Give other calculations of the density, for example powers and their sumsets.
* Define other densities like the lower and upper asymptotic density, and the natural density,
  and show how these relate to the Schnirelmann density.
* Show that if the sum of two densities is at least one, the sumset covers the positive naturals.
* Prove Schnirelmann's theorem and Mann's theorem on the subadditivity of this density.

## References

* [Ruzsa, Imre, *Sumsets and structure*][ruzsa2009]
-/

open Finset

/-- The Schnirelmann density is defined as the infimum of |A ∩ {1, ..., n}| / n as n ranges over
the positive naturals. -/
noncomputable def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  ⨅ n : {n : ℕ // 0 < n}, ((Ioc (0 : ℕ) n).filter (· ∈ A)).card / n

section

variable {A : Set ℕ} [DecidablePred (· ∈ A)]

lemma schnirelmannDensity_nonneg : 0 ≤ schnirelmannDensity A :=
  Real.iInf_nonneg (fun _ => by positivity)

lemma schnirelmannDensity_le_div {n : ℕ} (hn : n ≠ 0) :
    schnirelmannDensity A ≤ ((Ioc 0 n).filter (· ∈ A)).card / n :=
  ciInf_le ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ (⟨n, hn.bot_lt⟩ : {n : ℕ // 0 < n})

/--
For any natural `n`, the Schnirelmann density multiplied by `n` is bounded by `|A ∩ {1, ..., n}|`.
Note this property fails for the natural density.
-/
lemma schnirelmannDensity_mul_le_card_filter {n : ℕ} :
    schnirelmannDensity A * n ≤ ((Ioc 0 n).filter (· ∈ A)).card := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (le_div_iff (by positivity)).1 (schnirelmannDensity_le_div hn)

/--
To show the Schnirelmann density is upper bounded by `x`, it suffices to show
`|A ∩ {1, ..., n}| / n ≤ x`, for any chosen positive value of `n`.

We provide `n` explicitly here to make this lemma more easily usable in `apply` or `refine`.
This lemma is analogous to `ciInf_le_of_le`.
-/
lemma schnirelmannDensity_le_of_le {x : ℝ} (n : ℕ) (hn : n ≠ 0)
    (hx : ((Ioc 0 n).filter (· ∈ A)).card / n ≤ x) : schnirelmannDensity A ≤ x :=
  (schnirelmannDensity_le_div hn).trans hx

lemma schnirelmannDensity_le_one : schnirelmannDensity A ≤ 1 :=
  schnirelmannDensity_le_of_le 1 one_ne_zero <|
    by rw [Nat.cast_one, div_one, Nat.cast_le_one]; exact card_filter_le _ _

/--
If `k` is omitted from the set, its Schnirelmann density is upper bounded by `1 - k⁻¹`.
-/
lemma schnirelmannDensity_le_of_not_mem {k : ℕ} (hk : k ∉ A) :
    schnirelmannDensity A ≤ 1 - (k⁻¹ : ℝ) := by
  rcases k.eq_zero_or_pos with rfl | hk'
  · simpa using schnirelmannDensity_le_one
  apply schnirelmannDensity_le_of_le k hk'.ne'
  rw [← one_div, one_sub_div (Nat.cast_pos.2 hk').ne']
  gcongr
  rw [← Nat.cast_pred hk', Nat.cast_le]
  suffices (Ioc 0 k).filter (· ∈ A) ⊆ Ioo 0 k from (card_le_card this).trans_eq (by simp)
  rw [← Ioo_insert_right hk', filter_insert, if_neg hk]
  exact filter_subset _ _

/-- The Schnirelmann density of a set not containing `1` is `0`. -/
lemma schnirelmannDensity_eq_zero_of_one_not_mem (h : 1 ∉ A) : schnirelmannDensity A = 0 :=
  ((schnirelmannDensity_le_of_not_mem h).trans (by simp)).antisymm schnirelmannDensity_nonneg

/-- The Schnirelmann density is increasing with the set. -/
lemma schnirelmannDensity_le_of_subset {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A ⊆ B) :
    schnirelmannDensity A ≤ schnirelmannDensity B :=
  ciInf_mono ⟨0, fun _ ⟨_, hx⟩ ↦ hx ▸ by positivity⟩ fun _ ↦ by
    gcongr; exact monotone_filter_right _ h

/-- The Schnirelmann density of `A` is `1` if and only if `A` contains all the positive naturals. -/
lemma schnirelmannDensity_eq_one_iff : schnirelmannDensity A = 1 ↔ {0}ᶜ ⊆ A := by
  rw [le_antisymm_iff, and_iff_right schnirelmannDensity_le_one]
  constructor
  · rw [← not_imp_not, not_le]
    simp only [Set.not_subset, forall_exists_index, true_and, and_imp, Set.mem_singleton_iff]
    intro x hx hx'
    apply (schnirelmannDensity_le_of_not_mem hx').trans_lt
    simpa only [one_div, sub_lt_self_iff, inv_pos, Nat.cast_pos, pos_iff_ne_zero] using hx
  · intro h
    refine le_ciInf fun ⟨n, hn⟩ => ?_
    rw [one_le_div (Nat.cast_pos.2 hn), Nat.cast_le, filter_true_of_mem, Nat.card_Ioc, Nat.sub_zero]
    rintro x hx
    exact h (mem_Ioc.1 hx).1.ne'

/-- The Schnirelmann density of `A` containing `0` is `1` if and only if `A` is the naturals. -/
lemma schnirelmannDensity_eq_one_iff_of_zero_mem (hA : 0 ∈ A) :
    schnirelmannDensity A = 1 ↔ A = Set.univ := by
  rw [schnirelmannDensity_eq_one_iff]
  constructor
  · refine fun h => Set.eq_univ_of_forall fun x => ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact hA
    · exact h hx
  · rintro rfl
    exact Set.subset_univ {0}ᶜ

lemma le_schnirelmannDensity_iff {x : ℝ} :
    x ≤ schnirelmannDensity A ↔ ∀ n : ℕ, 0 < n → x ≤ ((Ioc 0 n).filter (· ∈ A)).card / n :=
  (le_ciInf_iff ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩).trans Subtype.forall

lemma schnirelmannDensity_lt_iff {x : ℝ} :
    schnirelmannDensity A < x ↔ ∃ n : ℕ, 0 < n ∧ ((Ioc 0 n).filter (· ∈ A)).card / n < x := by
  rw [← not_le, le_schnirelmannDensity_iff]; simp

lemma schnirelmannDensity_le_iff_forall {x : ℝ} :
    schnirelmannDensity A ≤ x ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ((Ioc 0 n).filter (· ∈ A)).card / n < x + ε := by
  rw [le_iff_forall_pos_lt_add]
  simp only [schnirelmannDensity_lt_iff]

lemma schnirelmannDensity_congr' {B : Set ℕ} [DecidablePred (· ∈ B)]
    (h : ∀ n > 0, n ∈ A ↔ n ∈ B) : schnirelmannDensity A = schnirelmannDensity B := by
  rw [schnirelmannDensity, schnirelmannDensity]; congr; ext ⟨n, hn⟩; congr 3; ext x; aesop

/-- The Schnirelmann density is unaffected by adding `0`. -/
@[simp] lemma schnirelmannDensity_insert_zero [DecidablePred (· ∈ insert 0 A)] :
    schnirelmannDensity (insert 0 A) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)

/-- The Schnirelmann density is unaffected by removing `0`. -/
lemma schnirelmannDensity_diff_singleton_zero [DecidablePred (· ∈ A \ {0})] :
    schnirelmannDensity (A \ {0}) = schnirelmannDensity A :=
  schnirelmannDensity_congr' (by aesop)

lemma schnirelmannDensity_congr {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A = B) :
    schnirelmannDensity A = schnirelmannDensity B :=
  schnirelmannDensity_congr' (by aesop)

/--
If the Schnirelmann density is `0`, there is a positive natural for which
`|A ∩ {1, ..., n}| / n < ε`, for any positive `ε`.
Note this cannot be improved to `∃ᶠ n : ℕ in atTop`, as can be seen by `A = {1}ᶜ`.
-/
lemma exists_of_schnirelmannDensity_eq_zero {ε : ℝ} (hε : 0 < ε) (hA : schnirelmannDensity A = 0) :
    ∃ n, 0 < n ∧ ((Ioc 0 n).filter (· ∈ A)).card / n < ε := by
  by_contra! h
  rw [← le_schnirelmannDensity_iff] at h
  linarith

end

@[simp] lemma schnirelmannDensity_empty : schnirelmannDensity ∅ = 0 :=
  schnirelmannDensity_eq_zero_of_one_not_mem (by simp)

/-- The Schnirelmann density of any finset is `0`. -/
lemma schnirelmannDensity_finset (A : Finset ℕ) : schnirelmannDensity A = 0 := by
  refine le_antisymm ?_ schnirelmannDensity_nonneg
  simp only [schnirelmannDensity_le_iff_forall, zero_add]
  intro ε hε
  wlog hε₁ : ε ≤ 1 generalizing ε
  · obtain ⟨n, hn, hn'⟩ := this 1 zero_lt_one le_rfl
    exact ⟨n, hn, hn'.trans_le (le_of_not_le hε₁)⟩
  let n : ℕ := ⌊A.card / ε⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  use n, hn
  rw [div_lt_iff (Nat.cast_pos.2 hn), ← div_lt_iff' hε, Nat.cast_add_one]
  exact (Nat.lt_floor_add_one _).trans_le' <| by gcongr; simp [subset_iff]

/-- The Schnirelmann density of any finite set is `0`. -/
lemma schnirelmannDensity_finite {A : Set ℕ} [DecidablePred (· ∈ A)] (hA : A.Finite) :
    schnirelmannDensity A = 0 := by simpa using schnirelmannDensity_finset hA.toFinset

@[simp] lemma schnirelmannDensity_univ : schnirelmannDensity Set.univ = 1 :=
  (schnirelmannDensity_eq_one_iff_of_zero_mem (by simp)).2 (by simp)

lemma schnirelmannDensity_setOf_even : schnirelmannDensity (setOf Even) = 0 :=
  schnirelmannDensity_eq_zero_of_one_not_mem <| by simp

lemma schnirelmannDensity_setOf_prime : schnirelmannDensity (setOf Nat.Prime) = 0 :=
  schnirelmannDensity_eq_zero_of_one_not_mem <| by simp [Nat.not_prime_one]

/--
The Schnirelmann density of the set of naturals which are `1 mod m` is `m⁻¹`, for any `m ≠ 1`.

Note that if `m = 1`, this set is empty.
-/
lemma schnirelmannDensity_setOf_mod_eq_one {m : ℕ} (hm : m ≠ 1) :
    schnirelmannDensity {n | n % m = 1} = (m⁻¹ : ℝ) := by
  rcases m.eq_zero_or_pos with rfl | hm'
  · simp only [Nat.cast_zero, inv_zero]
    refine schnirelmannDensity_finite ?_
    simp
  apply le_antisymm (schnirelmannDensity_le_of_le m hm'.ne' _) _
  · rw [← one_div, ← @Nat.cast_one ℝ]
    gcongr
    simp only [Set.mem_setOf_eq, card_le_one_iff_subset_singleton, subset_iff,
      mem_filter, mem_Ioc, mem_singleton, and_imp]
    use 1
    intro x _ hxm h
    rcases eq_or_lt_of_le hxm with rfl | hxm'
    · simp at h
    rwa [Nat.mod_eq_of_lt hxm'] at h
  rw [le_schnirelmannDensity_iff]
  intro n hn
  simp only [Set.mem_setOf_eq]
  have : (Icc 0 ((n - 1) / m)).image (· * m + 1) ⊆ (Ioc 0 n).filter (· % m = 1) := by
    simp only [subset_iff, mem_image, forall_exists_index, mem_filter, mem_Ioc, mem_Icc, and_imp]
    rintro _ y _ hy' rfl
    have hm : 2 ≤ m := hm.lt_of_le' hm'
    simp only [Nat.mul_add_mod', Nat.mod_eq_of_lt hm, add_pos_iff, or_true, and_true, true_and,
      ← Nat.le_sub_iff_add_le hn, zero_lt_one]
    exact Nat.mul_le_of_le_div _ _ _ hy'
  rw [le_div_iff (Nat.cast_pos.2 hn), mul_comm, ← div_eq_mul_inv]
  apply (Nat.cast_le.2 (card_le_card this)).trans'
  rw [card_image_of_injective, Nat.card_Icc, Nat.sub_zero, div_le_iff (Nat.cast_pos.2 hm'),
    ← Nat.cast_mul, Nat.cast_le, add_one_mul (α := ℕ)]
  · have := @Nat.lt_div_mul_add n.pred m hm'
    rwa [← Nat.succ_le, Nat.succ_pred hn.ne'] at this
  intro a b
  simp [hm'.ne']

lemma schnirelmannDensity_setOf_modeq_one {m : ℕ} :
    schnirelmannDensity {n | n ≡ 1 [MOD m]} = (m⁻¹ : ℝ) := by
  rcases eq_or_ne m 1 with rfl | hm
  · simp [Nat.modEq_one]
  rw [← schnirelmannDensity_setOf_mod_eq_one hm]
  apply schnirelmannDensity_congr
  ext n
  simp only [Set.mem_setOf_eq, Nat.ModEq, Nat.one_mod_of_ne_one hm]

lemma schnirelmannDensity_setOf_Odd : schnirelmannDensity (setOf Odd) = 2⁻¹ := by
  have h : setOf Odd = {n | n % 2 = 1} := Set.ext fun _ => Nat.odd_iff
  simp only [h]
  rw [schnirelmannDensity_setOf_mod_eq_one (by norm_num1), Nat.cast_two]
