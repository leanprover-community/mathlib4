/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Doga Can Sertbas
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

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
  ⨅ n : {n : ℕ // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n

section

variable {A : Set ℕ} [DecidablePred (· ∈ A)]

lemma schnirelmannDensity_nonneg : 0 ≤ schnirelmannDensity A :=
  Real.iInf_nonneg (fun _ => by positivity)

lemma schnirelmannDensity_le_div {n : ℕ} (hn : n ≠ 0) :
    schnirelmannDensity A ≤ #{a ∈ Ioc 0 n | a ∈ A} / n :=
  ciInf_le ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩ (⟨n, hn.bot_lt⟩ : {n : ℕ // 0 < n})

/--
For any natural `n`, the Schnirelmann density multiplied by `n` is bounded by `|A ∩ {1, ..., n}|`.
Note this property fails for the natural density.
-/
lemma schnirelmannDensity_mul_le_card_filter {n : ℕ} :
    schnirelmannDensity A * n ≤ #{a ∈ Ioc 0 n | a ∈ A} := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact (le_div_iff₀ (by positivity)).1 (schnirelmannDensity_le_div hn)

/--
To show the Schnirelmann density is upper bounded by `x`, it suffices to show
`|A ∩ {1, ..., n}| / n ≤ x`, for any chosen positive value of `n`.

We provide `n` explicitly here to make this lemma more easily usable in `apply` or `refine`.
This lemma is analogous to `ciInf_le_of_le`.
-/
lemma schnirelmannDensity_le_of_le {x : ℝ} (n : ℕ) (hn : n ≠ 0)
    (hx : #{a ∈ Ioc 0 n | a ∈ A} / n ≤ x) : schnirelmannDensity A ≤ x :=
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
  suffices {a ∈ Ioc 0 k | a ∈ A} ⊆ Ioo 0 k from (card_le_card this).trans_eq (by simp)
  rw [← Ioo_insert_right hk', filter_insert, if_neg hk]
  exact filter_subset _ _

/-- The Schnirelmann density of a set not containing `1` is `0`. -/
lemma schnirelmannDensity_eq_zero_of_one_not_mem (h : 1 ∉ A) : schnirelmannDensity A = 0 :=
  ((schnirelmannDensity_le_of_not_mem h).trans (by simp)).antisymm schnirelmannDensity_nonneg

/-- The Schnirelmann density is increasing with the set. -/
lemma schnirelmannDensity_le_of_subset {B : Set ℕ} [DecidablePred (· ∈ B)] (h : A ⊆ B) :
    schnirelmannDensity A ≤ schnirelmannDensity B :=
  ciInf_mono ⟨0, fun _ ⟨_, hx⟩ ↦ hx ▸ by positivity⟩ fun _ ↦ by
    gcongr; exact h

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
    x ≤ schnirelmannDensity A ↔ ∀ n : ℕ, 0 < n → x ≤ #{a ∈ Ioc 0 n | a ∈ A} / n :=
  (le_ciInf_iff ⟨0, fun _ ⟨_, hx⟩ => hx ▸ by positivity⟩).trans Subtype.forall

lemma schnirelmannDensity_lt_iff {x : ℝ} :
    schnirelmannDensity A < x ↔ ∃ n : ℕ, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < x := by
  rw [← not_le, le_schnirelmannDensity_iff]; simp

lemma schnirelmannDensity_le_iff_forall {x : ℝ} :
    schnirelmannDensity A ≤ x ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < x + ε := by
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

@[simp] lemma schnirelmannDensity_congr_decidable {A : Set ℕ} (h : DecidablePred (· ∈ A))
    [DecidablePred (· ∈ A)] :
    @schnirelmannDensity A h = schnirelmannDensity A := by congr

/--
If the Schnirelmann density is `0`, there is a positive natural for which
`|A ∩ {1, ..., n}| / n < ε`, for any positive `ε`.
Note this cannot be improved to `∃ᶠ n : ℕ in atTop`, as can be seen by `A = {1}ᶜ`.
-/
lemma exists_of_schnirelmannDensity_eq_zero {ε : ℝ} (hε : 0 < ε) (hA : schnirelmannDensity A = 0) :
    ∃ n, 0 < n ∧ #{a ∈ Ioc 0 n | a ∈ A} / n < ε := by
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
  let n : ℕ := ⌊#A / ε⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  use n, hn
  rw [div_lt_iff₀ (Nat.cast_pos.2 hn), ← div_lt_iff₀' hε, Nat.cast_add_one]
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
  have : (Icc 0 ((n - 1) / m)).image (· * m + 1) ⊆ {x ∈ Ioc 0 n | x % m = 1} := by
    simp only [subset_iff, mem_image, forall_exists_index, mem_filter, mem_Ioc, mem_Icc, and_imp]
    rintro _ y _ hy' rfl
    have hm : 2 ≤ m := hm.lt_of_le' hm'
    simp only [Nat.mul_add_mod', Nat.mod_eq_of_lt hm, add_pos_iff, or_true, and_true, true_and,
      ← Nat.le_sub_iff_add_le hn, zero_lt_one]
    exact Nat.mul_le_of_le_div _ _ _ hy'
  rw [le_div_iff₀ (Nat.cast_pos.2 hn), mul_comm, ← div_eq_mul_inv]
  apply (Nat.cast_le.2 (card_le_card this)).trans'
  rw [card_image_of_injective, Nat.card_Icc, Nat.sub_zero, div_le_iff₀ (Nat.cast_pos.2 hm'),
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
  simp only [Set.mem_setOf_eq, Nat.ModEq, Nat.one_mod_eq_one.mpr hm]

lemma schnirelmannDensity_setOf_Odd : schnirelmannDensity (setOf Odd) = 2⁻¹ := by
  have h : setOf Odd = {n | n % 2 = 1} := Set.ext fun _ => Nat.odd_iff
  simp only [h]
  rw [schnirelmannDensity_setOf_mod_eq_one (by norm_num1), Nat.cast_two]

open scoped Pointwise

section

variable {α : Type*} [OrderedAddCommMonoid α] [CanonicallyOrderedAdd α]
  {a : α} {A B : Set α} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]

instance [AddLeftReflectLE α] [Sub α] [OrderedSub α] [DecidableRel (· ≤ · : α → α → Prop)] :
    DecidablePred (· ∈ a +ᵥ B) := fun x =>
  decidable_of_iff (a ≤ x ∧ x - a ∈ B) <| by aesop (add simp Set.mem_vadd_set)

instance [LocallyFiniteOrderBot α] [DecidableEq α] :
    DecidablePred (· ∈ a +ᵥ B) := fun x =>
  decidable_of_iff (∃ b ∈ Finset.Iic x, b ∈ B ∧ a + b = x) <| by aesop (add simp Set.mem_vadd_set)

instance [LocallyFiniteOrderBot α] [DecidableEq α] :
    DecidablePred (· ∈ A + B) := fun x =>
  decidable_of_iff' (∃ a ∈ Finset.Iic x, a ∈ A ∧ x ∈ a +ᵥ B) <| by
    simp only [← vadd_eq_add, ← Set.iUnion_vadd_set, Set.mem_iUnion₂, exists_prop, mem_Iic]
    constructor
    case mp =>
      rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨_, le_self_add, ha, Set.vadd_mem_vadd_set hb⟩
    case mpr =>
      rintro ⟨a, _, ha', ha''⟩
      exact ⟨a, ha', ha''⟩

end

lemma add_max'_add {α : Type*} [LinearOrder α] [Add α] [AddLeftMono α] [AddRightMono α]
    {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + B).max' (hA.add hB) = A.max' hA + B.max' hB := by
  refine le_antisymm ?_ ?_
  next =>
    refine Finset.max'_le _ _ _ ?_
    simp only [mem_add, forall_exists_index, and_imp]
    rintro _ a ha b hb rfl
    exact add_le_add (Finset.le_max' _ _ ha) (Finset.le_max' _ _ hb)
  next => exact Finset.le_max' _ _ (Finset.add_mem_add (Finset.max'_mem _ _) (Finset.max'_mem _ _))

lemma add_min'_add {α : Type*} [LinearOrder α] [Add α] [AddLeftMono α] [AddRightMono α]
    {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A + B).min' (hA.add hB) = A.min' hA + B.min' hB :=
  add_max'_add (α := αᵒᵈ) hA hB

-- lemma max'_vadd_finset_not_subset {α : Type*} [LinearOrder α] [OrderBot α] [Add α]
--     {A B : Finset α} (hA : A.Nonempty)
--     (hB0 : ∃ b ∈ B, b ≠ ⊥) :
--     ¬ A.max' hA +ᵥ B ⊆ A := by
--   intro hi
--   obtain ⟨b, hb, hb0⟩ := hB0
--   have : A.max' hA + b ≤ A.max' hA := Finset.le_max' _ _ (hi (vadd_mem_vadd_finset hb))
--   simp? at this

example {α : Type*} [DecidableEq α] [Add α] {A B C : Finset α} :
    (∀ x ∈ A, x +ᵥ B ⊆ C) ↔ A + B ⊆ C := by
  rw [@add_subset_iff_left]
  -- aesop (add simp [subset_iff, mem_vadd_finset, mem_add])

#exit

lemma max'_vadd_finset_not_subset {A B : Finset ℕ} (hA : A.Nonempty) (hB0 : ∃ b ∈ B, b ≠ 0) :
    ¬ A.max' hA +ᵥ B ⊆ A := by
  intro hi
  obtain ⟨b, hb, hb0⟩ := hB0
  have : A.max' hA + b ≤ A.max' hA := Finset.le_max' _ _ (hi (vadd_mem_vadd_finset hb))
  omega

lemma add_sdiff_nonempty {α : Type*}
    [AddCancelMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α] [DecidableEq α]
    {A B : Finset α} (hA : A.Nonempty) (hB0 : (B \ {0}).Nonempty) :
    ((A + B) \ A).Nonempty := by
  obtain ⟨a, ha, ha'⟩ := Finset.exists_maximal A hA
  simp only [Finset.Nonempty, mem_sdiff, mem_singleton] at hB0
  obtain ⟨b, hb, hb0⟩ := hB0
  rw [sdiff_nonempty]
  intro h
  exact ha' _ (h (add_mem_add ha hb)) (lt_add_of_pos_right a (pos_iff_ne_zero.2 hb0))

lemma add_subset_left_iff {α : Type*}
    [AddCancelMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α] [DecidableEq α]
    {A B : Finset α} :
    A + B ⊆ A ↔ A = ∅ ∨ B ⊆ {0} := by
  constructor
  · contrapose!
    rintro ⟨hA, hB⟩
    rw [← sdiff_nonempty] at hB ⊢
    exact add_sdiff_nonempty (nonempty_iff_ne_empty.2 hA) hB
  · rintro (rfl | h)
    · simp
    · exact (add_subset_add_left h).trans (by simp [singleton_zero])

example {A B : Finset ℕ} :
    ((A + B) \ A).Nonempty ↔ ∃ a ∈ A, ((a +ᵥ B) \ A).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    simp only [mem_sdiff, mem_add] at hx
    obtain ⟨⟨x, hx, y, hy, rfl⟩, hA⟩ := hx
    refine ⟨x, hx, x + y, ?_⟩
    simp only [mem_sdiff]
    constructor
    · apply vadd_mem_vadd_finset hy
    · exact hA
  · rintro ⟨a, ha, x, hx⟩
    simp only [mem_sdiff, mem_vadd_finset] at hx
    obtain ⟨⟨b, hb, rfl⟩, hA⟩ := hx
    refine ⟨a +ᵥ b, ?_⟩
    simp only [mem_sdiff, hA, not_false_iff, and_true]
    exact add_mem_add ha hb

@[to_additive]
lemma Finset.card_smul_finset' {α : Type*} [DecidableEq α] [Monoid α] [IsLeftCancelMul α]
    (a : α) (s : Finset α) : (a • s).card = s.card :=
  card_image_of_injective _ <| fun _ _ h => mul_left_cancel h

theorem extracted_4 {σ : ℝ} (n : ℕ) {A A' B B' B'' : Finset ℕ}
    (h : ∀ m ∈ Ioc 0 n, σ * m ≤ (Ioc 0 m ∩ A).card + (Ioc 0 m ∩ B).card) (a : ℕ)
    (hA' : A' = Icc 0 n ∩ (A ∪ (a +ᵥ B'')))
    (hB' : B' = filter (fun x ↦ a + x ∈ A) B)
    (hB'' : B'' = B \ B')
    (m : ℕ)
    (hm : m ∈ Ioc 0 n)
    (h' : Ioc 0 m ∩ B ∩ Ioc (m - a) m = ∅) :
    σ * m ≤ (Ioc 0 m ∩ A').card + (Ioc 0 m ∩ B').card := by
  have : a +ᵥ (Ioc 0 m ∩ B'') ⊆ Ioc 0 m ∩ (a +ᵥ B'') := by
    simp only [hB'', subset_iff, mem_vadd_finset, mem_inter, mem_Ioc, mem_sdiff, vadd_eq_add,
      forall_exists_index, and_imp]
    rintro _ b hb0 hbm hb hb' rfl
    refine ⟨⟨by omega, ?_⟩, b, ⟨hb, hb'⟩, rfl⟩
    simp only [eq_empty_iff_forall_not_mem, mem_inter, not_and, and_imp, mem_Ioc] at h'
    by_contra! h''
    exact h' b hb0 hbm hb (by omega) hbm
  calc σ * m ≤ (Ioc 0 m ∩ A).card + (Ioc 0 m ∩ B).card := h _ hm
    _ = (Ioc 0 m ∩ A).card + ((Ioc 0 m ∩ B').card + (Ioc 0 m ∩ B'').card) := ?g1
    _ = (Ioc 0 m ∩ A).card + (Ioc 0 m ∩ B'').card + (Ioc 0 m ∩ B').card := by ring
    _ = (Ioc 0 m ∩ A).card + (a +ᵥ (Ioc 0 m ∩ B'')).card + (Ioc 0 m ∩ B').card := by
          rw [card_vadd_finset']
    _ ≤ (Ioc 0 m ∩ A).card + (Ioc 0 m ∩ (a +ᵥ B'')).card + (Ioc 0 m ∩ B').card := by gcongr
    _ = _ := ?g2
  case g1 =>
    rw [add_right_inj, ←Nat.cast_add, Nat.cast_inj, hB'', hB', ←card_union_of_disjoint,
      ←inter_union_distrib_left, union_sdiff_of_subset (filter_subset _ _)]
    exact disjoint_sdiff.mono inter_subset_right inter_subset_right
  case g2 =>
    rw [add_left_inj, ←Nat.cast_add, Nat.cast_inj, ←card_union_of_disjoint,
      ←inter_union_distrib_left, hA', inter_left_comm, eq_comm]
    · congr 1
      simp only [inter_eq_right, Finset.subset_iff, mem_Ioc, mem_Icc, mem_inter, and_imp] at hm ⊢
      rintro i hi₁ hi₂ -
      omega
    · have : Disjoint A (a +ᵥ B'') := by
        simp only [hB'', hB', ← filter_not, disjoint_left, mem_vadd_finset, mem_filter, vadd_eq_add,
          not_exists, not_and, and_imp]
        rintro _ ha' b _ hab rfl
        exact hab ha'
      exact this.mono inter_subset_right inter_subset_right

lemma vadd_Icc {a b c : ℕ} : a +ᵥ Icc b c = Icc (a + b) (a + c) := by
  ext i
  simp only [mem_Icc, mem_vadd_finset, vadd_eq_add]
  exact ⟨by omega, fun _ => ⟨i - a, by omega⟩⟩

lemma Nat.Ioc_sub_one_left {a b : ℕ} : Ioc a (b - 1) = Ioo a b := by
  ext i
  simp only [mem_Ioc, mem_Ioo, and_congr_right_iff]
  omega

lemma Ioo_union_Icc_eq_Ioc {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] {a b c : α}
    (h₁ : a < b) (h₂ : b ≤ c) : Ioo a b ∪ Icc b c = Ioc a c :=
  Finset.coe_injective (by simp [Set.Ioo_union_Icc_eq_Ioc h₁ h₂])

lemma disjoint_Ioo_Icc {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] {a b c : α} :
    Disjoint (Ioo a b) (Icc b c) := by
  refine disjoint_left.2 ?_
  intro i hi hi'
  simp only [mem_Ioo, mem_Icc] at hi hi'
  exact hi.2.not_le hi'.1

theorem extracted_5 {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) (n : ℕ)
    (ih : ∀ n' < n, ∀ {A B : Finset ℕ},
      A ⊆ Icc 0 n' → B ⊆ Icc 0 n' → 0 ∈ A → 0 ∈ B →
      (∀ m ∈ Ioc 0 n', σ * m ≤ (Ioc 0 m ∩ A).card + (Ioc 0 m ∩ B).card) →
      ∀ {m : ℕ}, m ∈ Ioc 0 n' → σ * m ≤ (Ioc 0 m ∩ (A + B)).card)
    {A A' B B' B'' : Finset ℕ}
    (hAn : A ⊆ Icc 0 n) (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (h : ∀ m ∈ Ioc 0 n, σ * m ≤ (Ioc 0 m ∩ A).card + (Ioc 0 m ∩ B).card)
     (a : ℕ)
    (ha''' : ∀ a' ∈ A, a' < a → a' +ᵥ B ⊆ A)
    (hA' : A' = Icc 0 n ∩ (A ∪ (a +ᵥ B'')))
    (m : ℕ)
    (ih' : ∀ m' < m, m' ∈ Ioc 0 n → σ * m' ≤ (Ioc 0 m' ∩ A').card + (Ioc 0 m' ∩ B').card)
    (hm : m ∈ Ioc 0 n)
    (h' : (Ioc 0 m ∩ B ∩ Ioc (m - a) m).Nonempty) :
    σ * m ≤ (Ioc 0 m ∩ A').card + (Ioc 0 m ∩ B').card := by
  let b := Finset.min' _ h'
  have hb₁ : 0 < b ∧ b ≤ m ∧ b ∈ B ∧ m - a < b := by
    have : b ∈ _ := Finset.min'_mem _ h'
    simp at this
    tauto
  have hb₂ : m - b < a := by omega
  have h₁ : m - b < n := by
    simp only [mem_Ioc] at hm
    omega
  have h₂ : σ * (m - b) ≤ (Ioc 0 (m - b) ∩ (Icc 0 (m - b) ∩ A + Icc 0 (m - b) ∩ B)).card := by
    rw [←Nat.cast_sub hb₁.2.1]
    rcases le_or_lt m b with h1 | h1
    · simp [h1]
    refine ih _ (by omega) inter_subset_left inter_subset_left (by simp [hA0])
      (by simp [hB0]) (fun m' hm' => ?_) (by simp [h1])
    simp only [mem_Ioc] at hm'
    have : Ioc 0 m' ∩ Icc 0 (m - b) = Ioc 0 m' :=
      inter_eq_left.2 (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hm'.2))
    rw [←inter_assoc, ←inter_assoc, this]
    refine h _ ?_
    simp only [mem_Ioc]
    omega
  replace h₂ : σ * (m - b) ≤ (Ioc 0 (m - b) ∩ (A + B)).card := by
    refine h₂.trans ?_
    gcongr Nat.cast (Finset.card ?_)
    simp only [Finset.subset_inter_iff, inter_subset_left, true_and]
    exact inter_subset_right.trans (add_subset_add inter_subset_right inter_subset_right)
  have h₃ : ((Icc 0 (m - b) ∩ (A + B)).card : ℝ) ≤ (Icc 0 (m - b) ∩ A).card := by
    gcongr Nat.cast (Finset.card ?_)
    simp only [Finset.subset_inter_iff, inter_subset_left, true_and]
    intro i
    simp only [mem_inter, mem_Icc, zero_le, true_and, and_imp, mem_add, forall_exists_index]
    rintro hi a' ha' b' hb' rfl
    exact ha''' a' ha' (by omega) (by simp [mem_vadd_finset, hb'])
  have h_eq : b +ᵥ (Icc 0 (m - b) ∩ A) = Icc b m ∩ (b +ᵥ A) := by
    ext i
    simp only [mem_vadd_finset, mem_inter, mem_Icc, zero_le, true_and, vadd_eq_add]
    constructor
    case mp =>
      rintro ⟨i, ⟨hi, hi'⟩, rfl⟩
      exact ⟨by omega, i, hi', rfl⟩
    case mpr =>
      rintro ⟨_, j, hj, rfl⟩
      exact ⟨j, ⟨by omega, hj⟩, rfl⟩
  have h₄ : ((Icc 0 (m - b) ∩ A).card : ℝ) = (Icc b m ∩ (b +ᵥ A)).card := by
    rw [←h_eq, ←card_vadd_finset' b]
  have h₅ : ((Ioc 0 (m - b) ∩ (A + B)).card : ℝ) + 1 = (Icc 0 (m - b) ∩ (A + B)).card := by
    rw [←Ioc_insert_left (by omega), insert_inter_of_mem, card_insert_of_not_mem (by simp),
      Nat.cast_add_one]
    exact mem_add.2 ⟨0, hA0, 0, hB0, by simp⟩
  have h₇ : ((Icc b m ∩ (b +ᵥ A)).card : ℝ) ≤ (Icc b m ∩ A).card := by
    rw [←h_eq]
    gcongr Nat.cast (Finset.card ?_)
    intro i
    simp only [mem_vadd_finset, mem_inter, mem_Icc, zero_le, true_and, vadd_eq_add,
      forall_exists_index, and_imp]
    rintro i hi hi' rfl
    refine ⟨by omega, ha''' _ hi' (by omega) ?_⟩
    rw [mem_vadd_finset]
    exact ⟨b, hb₁.2.2.1, add_comm _ _⟩
  have h₈ : σ * (m - b) + 1 ≤ (Icc b m ∩ A').card + (Icc b m ∩ B').card := by
    have : ((Icc b m ∩ A).card : ℝ) ≤ (Icc b m ∩ A').card := by
      gcongr Nat.cast ((Icc b m ∩ ?_).card)
      simp [hA', subset_inter_iff, subset_union_left, hAn]
    linarith
  have h₉ : σ * (b - 1) ≤ (Ioc 0 (b - 1) ∩ A').card + (Ioc 0 (b - 1) ∩ B').card := by
    rcases le_or_lt b 1 with hb1 | hb1
    case inl =>
      simp only [hb1, tsub_eq_zero_of_le, le_refl, Ioc_eq_empty_of_le, empty_inter, card_empty,
        Nat.cast_zero, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hσ₀.le (by simpa)
    case inr =>
      have : b - 1 ∈ Ioc 0 n := by
        simp only [mem_Ioc] at hm ⊢
        omega
      refine (ih' (b - 1) (by omega) this).trans_eq' ?_
      rw [Nat.cast_sub (by omega), Nat.cast_one]
  have : ∀ C, ((Ioc 0 m ∩ C).card : ℝ) = (Ioc 0 (b - 1) ∩ C).card + (Icc b m ∩ C).card := by
    intro C
    rw [←Nat.cast_add, Nat.Ioc_sub_one_left, ←card_union_of_disjoint, ←union_inter_distrib_right]
    · congr 3
      rw [Ioo_union_Icc_eq_Ioc (by omega) (by omega)]
    · exact Disjoint.mono inter_subset_left inter_subset_left disjoint_Ioo_Icc
  rw [this, this]
  linarith

theorem extracted_1 {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) (n : ℕ)
    (ih : ∀ n' < n, ∀ {A B : Finset ℕ},
      A ⊆ Icc 0 n' → B ⊆ Icc 0 n' → 0 ∈ A → 0 ∈ B →
      (∀ m ∈ Ioc 0 n', σ * ↑m ≤ ↑(Ioc 0 m ∩ A).card + ↑(Ioc 0 m ∩ B).card) →
      ∀ {m : ℕ}, m ∈ Ioc 0 n' → σ * ↑m ≤ ↑(Ioc 0 m ∩ (A + B)).card)
     {A A' B B' B'' : Finset ℕ}
    (hAn : A ⊆ Icc 0 n)  (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (h : ∀ m ∈ Ioc 0 n, σ * m ≤ (Ioc 0 m ∩ A).card + (Ioc 0 m ∩ B).card)
    (a : ℕ)
    (ha''' : ∀ a' ∈ A, a' < a → a' +ᵥ B ⊆ A)
    (hA' : A' = Icc 0 n ∩ (A ∪ (a +ᵥ B'')))
    (hB' : B' = B.filter (a + · ∈ A))
    (hB'' : B'' = B \ B')
    (m : ℕ) (hm : m ∈ Ioc 0 n) :
    σ * m ≤ (Ioc 0 m ∩ A').card + (Ioc 0 m ∩ B').card := by
  induction m using Nat.strongRecOn
  case ind m ih' =>
  rcases eq_empty_or_nonempty (Ioc 0 m ∩ B ∩ Ioc (m - a) m)
  case inl h' => exact extracted_4 n h a hA' hB' hB'' m hm h'
  case inr h' => exact extracted_5 hσ₀ hσ₁ _ ih hAn hA0 hB0 h _ ha''' hA' _ ih' hm h'

theorem dyson_mann' {σ : ℝ} {n : ℕ} {A B : Finset ℕ}
    (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1)
    (hAn : A ⊆ Icc 0 n) (hBn : B ⊆ Icc 0 n)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (h : ∀ m ∈ Ioc 0 n, σ * m ≤ (Ioc 0 m ∩ A).card + (Ioc 0 m ∩ B).card)
    {m : ℕ}
    (hm : m ∈ Ioc 0 n) :
    σ * m ≤ (Ioc 0 m ∩ (A + B)).card := by
  induction n using Nat.strongRecOn generalizing A B m
  case ind n ih =>
  generalize hb : B.card = b
  induction b using Nat.strongRecOn generalizing A B
  case ind b ih' =>
  wlog hB : ∃ b ∈ B, b ≠ 0 generalizing
  · have : B ⊆ {0} := by simpa [-subset_singleton_iff, subset_iff] using hB
    obtain rfl : B = {0} := this.antisymm (by simp [hB0])
    rw [singleton_zero]
    simpa [filter_eq'] using h m hm
  have : (A.filter (¬ · +ᵥ B ⊆ A)).Nonempty := by
    sorry
    -- ⟨A.max' ⟨0, hA0⟩, mem_filter.2 ⟨max'_mem _ _, max'_vadd_finset_not_subset _ hB⟩⟩
  let a := min' _ this
  obtain ⟨ha, ha'⟩ : a ∈ A ∧ ¬ a +ᵥ B ⊆ A := by simpa using Finset.min'_mem _ this
  have ha'' : ∀ a' ∈ A, a' < a → a' +ᵥ B ⊆ A := by
    intro a' ha ha'
    contrapose! ha'
    exact min'_le _ _ (by simp [ha, ha'])
  let B' := B.filter (a + · ∈ A)
  let A' := Icc 0 n ∩ (A ∪ (a +ᵥ B \ B'))
  have hA' : 0 ∈ A' := by simp [A', hA0]
  have hB' : 0 ∈ B' := by simp [B', hB0, ha]
  have : B'.card < B.card := by
    refine card_lt_card ?_
    rw [filter_ssubset]
    simp only [subset_iff, Finset.mem_vadd_finset, vadd_eq_add, not_forall] at ha'
    obtain ⟨a, ⟨b, hb, rfl⟩, hab⟩ := ha'
    exact ⟨b, hb, hab⟩
  have : A' + B' ⊆ A + B := by
    simp only [inter_union_distrib_left, ← filter_not, union_add, union_subset_iff,
      inter_subset_right, filter_subset, add_subset_add, true_and, A', B']
    simp only [subset_iff, mem_add, mem_inter, mem_Icc, zero_le, true_and, mem_vadd_finset,
      mem_filter, vadd_eq_add, forall_exists_index, and_imp]
    rintro _ a' ha b hb _ rfl b' _ hab' rfl
    exact ⟨a + b', hab', b, hb, add_right_comm _ _ _⟩
  have : ((Ioc 0 m ∩ (A' + B')).card : ℝ) ≤ (Ioc 0 m ∩ (A + B)).card := by gcongr
  refine this.trans' ?_
  refine ih' B'.card (by omega) inter_subset_left ((filter_subset _ _).trans hBn) hA' hB' ?_ rfl
  exact extracted_1 hσ₀ hσ₁ n ih hAn hA0 hB0 h _ ha'' rfl rfl rfl

theorem dyson_mann {σ : ℝ} {n : ℕ} {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (h : ∀ m ∈ Ioc 0 n, σ * m ≤ ((Ioc 0 m).filter (· ∈ A)).card + ((Ioc 0 m).filter (· ∈ B)).card)
    {m : ℕ} (hm : m ∈ Ioc 0 n) :
    σ * m ≤ ((Ioc 0 m).filter (· ∈ A + B)).card := by
  simp only [mem_Ioc, and_imp] at hm
  have h' : ∀ m ∈ Ioc 0 n, ∀ p : ℕ → Prop, ∀ h : DecidablePred p,
      Ioc 0 m ∩ (Icc 0 n).filter p = (Ioc 0 m).filter p := by
    intro m hm p hp
    ext i
    simp at hm ⊢
    omega
  refine (dyson_mann' (n := n) hσ₀ hσ₁ (filter_subset (· ∈ A) _) (filter_subset (· ∈ B) _)
    (by simp [hA0]) (by simp [hB0]) ?g1 (by simp [*])).trans ?g2
  case g1 =>
    intro m hm
    rw [h' m hm, h' m hm]
    exact h m hm
  case g2 =>
    gcongr (Finset.card ?_ : ℝ)
    simp only [Finset.subset_iff, mem_inter, mem_Ioc, and_imp, mem_filter, Set.mem_add, mem_Icc,
      zero_le, true_and, forall_exists_index, mem_add]
    rintro i hi hi' a _ ha b _ hb rfl
    exact ⟨⟨hi, hi'⟩, a, ha, b, hb, rfl⟩

theorem mann_aux {σA σB : ℝ} {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hσA0 : 0 ≤ σA) (hσA1 : σA ≤ 1)
    (hσB0 : 0 ≤ σB) (hσB1 : σB ≤ 1)
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B)
    (hA : ∀ n ≥ 1, σA * n ≤ ((Ioc 0 n).filter (· ∈ A)).card)
    (hB : ∀ n ≥ 1, σB * n ≤ ((Ioc 0 n).filter (· ∈ B)).card) :
    ∀ n ≥ 1, min (σA + σB) 1 * n ≤ ((Ioc 0 n).filter (· ∈ A + B)).card := by
  intro n hn
  have hn' : n ∈ Ioc 0 n := by simpa using hn
  rcases eq_or_lt_of_le hσA0 with rfl | hσA0'
  case inl =>
    simp only [zero_add, hσB1, min_eq_left]
    refine (hB _ hn).trans ?_
    gcongr
    intro i hi
    rw [Set.mem_add]
    exact ⟨0, hA0, i, hi, zero_add _⟩
  case inr =>
  have : 0 < σA + σB := add_pos_of_pos_of_nonneg hσA0' hσB0
  refine dyson_mann (lt_min this zero_lt_one) (min_le_right _ _) hA0 hB0 ?_ hn'
  intro m hm
  rw [min_mul_of_nonneg _ _ (by positivity), add_mul]
  refine min_le_of_left_le ?_
  simp only [mem_Ioc] at hm
  exact add_le_add (hA _ (by omega)) (hB _ (by omega))

theorem mann {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hA0 : 0 ∈ A) (hB0 : 0 ∈ B) :
    min (schnirelmannDensity A + schnirelmannDensity B) 1 ≤ schnirelmannDensity (A + B) :=
  le_schnirelmannDensity_iff.2 fun n hn =>
    (le_div_iff₀ (by positivity)).2 <|
      mann_aux schnirelmannDensity_nonneg schnirelmannDensity_le_one
        schnirelmannDensity_nonneg schnirelmannDensity_le_one hA0 hB0
        (fun n _ => schnirelmannDensity_mul_le_card_filter)
        (fun n _ => schnirelmannDensity_mul_le_card_filter) _ hn

theorem add_eq_univ_of_one_le {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hA : 0 ∈ A) (hB : 0 ∈ B)
    (h : 1 ≤ schnirelmannDensity A + schnirelmannDensity B) :
    A + B = Set.univ := by
  rw [←schnirelmannDensity_eq_one_iff_of_zero_mem]
  · exact le_antisymm schnirelmannDensity_le_one ((mann hA hB).trans' (by simpa))
  · rw [←zero_add 0]
    exact Set.add_mem_add hA hB
