/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.RingTheory.UniqueFactorizationDomain

#align_import algebra.squarefree from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `Data.Nat.Squarefree`.

## Main Definitions
 - `Squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
 - `multiplicity.squarefree_iff_multiplicity_le_one`: `x` is `Squarefree` iff for every `y`, either
  `multiplicity y x ≤ 1` or `IsUnit y`.
 - `UniqueFactorizationMonoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
 factorization monoid is squarefree iff `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/


variable {R : Type*}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x
#align squarefree Squarefree

@[simp]
theorem IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit x) : Squarefree x := fun _ hdvd =>
  isUnit_of_mul_isUnit_left (isUnit_of_dvd_unit hdvd h)
#align is_unit.squarefree IsUnit.squarefree

-- @[simp] -- Porting note: simp can prove this
theorem squarefree_one [CommMonoid R] : Squarefree (1 : R) :=
  isUnit_one.squarefree
#align squarefree_one squarefree_one

@[simp]
theorem not_squarefree_zero [MonoidWithZero R] [Nontrivial R] : ¬Squarefree (0 : R) := by
  erw [not_forall]
  -- ⊢ ∃ x, ¬(x * x ∣ 0 → IsUnit x)
  exact ⟨0, by simp⟩
  -- 🎉 no goals
#align not_squarefree_zero not_squarefree_zero

theorem Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R] {m : R} (hm : Squarefree (m : R)) :
    m ≠ 0 := by
  rintro rfl
  -- ⊢ False
  exact not_squarefree_zero hm
  -- 🎉 no goals
#align squarefree.ne_zero Squarefree.ne_zero

@[simp]
theorem Irreducible.squarefree [CommMonoid R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  -- ⊢ IsUnit y
  rw [mul_assoc] at hz
  -- ⊢ IsUnit y
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  -- ⊢ IsUnit y
  · exact hu
    -- 🎉 no goals
  · apply isUnit_of_mul_isUnit_left hu
    -- 🎉 no goals
#align irreducible.squarefree Irreducible.squarefree

@[simp]
theorem Prime.squarefree [CancelCommMonoidWithZero R] {x : R} (h : Prime x) : Squarefree x :=
  h.irreducible.squarefree
#align prime.squarefree Prime.squarefree

theorem Squarefree.of_mul_left [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m :=
  fun p hp => hmn p (dvd_mul_of_dvd_left hp n)
#align squarefree.of_mul_left Squarefree.of_mul_left

theorem Squarefree.of_mul_right [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)) :
    Squarefree n := fun p hp => hmn p (dvd_mul_of_dvd_right hp m)
#align squarefree.of_mul_right Squarefree.of_mul_right

theorem Squarefree.squarefree_of_dvd [CommMonoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) :
    Squarefree x := fun _ h => hsq _ (h.trans hdvd)
#align squarefree.squarefree_of_dvd Squarefree.squarefree_of_dvd

section SquarefreeGcdOfSquarefree

variable {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α]

theorem Squarefree.gcd_right (a : α) {b : α} (hb : Squarefree b) : Squarefree (gcd a b) :=
  hb.squarefree_of_dvd (gcd_dvd_right _ _)
#align squarefree.gcd_right Squarefree.gcd_right

theorem Squarefree.gcd_left {a : α} (b : α) (ha : Squarefree a) : Squarefree (gcd a b) :=
  ha.squarefree_of_dvd (gcd_dvd_left _ _)
#align squarefree.gcd_left Squarefree.gcd_left

end SquarefreeGcdOfSquarefree

namespace multiplicity

section CommMonoid

variable [CommMonoid R] [DecidableRel (Dvd.dvd : R → R → Prop)]

theorem squarefree_iff_multiplicity_le_one (r : R) :
    Squarefree r ↔ ∀ x : R, multiplicity x r ≤ 1 ∨ IsUnit x := by
  refine' forall_congr' fun a => _
  -- ⊢ a * a ∣ r → IsUnit a ↔ multiplicity a r ≤ 1 ∨ IsUnit a
  rw [← sq, pow_dvd_iff_le_multiplicity, or_iff_not_imp_left, not_le, imp_congr _ Iff.rfl]
  -- ⊢ ↑2 ≤ multiplicity a r ↔ 1 < multiplicity a r
  rw [←one_add_one_eq_two]
  -- ⊢ ↑(1 + 1) ≤ multiplicity a r ↔ 1 < multiplicity a r
  simpa using PartENat.add_one_le_iff_lt (PartENat.natCast_ne_top 1)
  -- 🎉 no goals
#align multiplicity.squarefree_iff_multiplicity_le_one multiplicity.squarefree_iff_multiplicity_le_one

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero R] [WfDvdMonoid R]

theorem finite_prime_left {a b : R} (ha : Prime a) (hb : b ≠ 0) : multiplicity.Finite a b := by
  classical
    revert hb
    refine'
      WfDvdMonoid.induction_on_irreducible b (fun c => c.irrefl.elim) (fun u hu _ => _)
        fun b p hb hp ih _ => _
    · rw [multiplicity.finite_iff_dom, multiplicity.isUnit_right ha.not_unit hu]
      exact PartENat.dom_natCast 0
    · refine'
        multiplicity.finite_mul ha
          (multiplicity.finite_iff_dom.mpr
            (PartENat.dom_of_le_natCast (show multiplicity a p ≤ ↑1 from _)))
          (ih hb)
      norm_cast
      exact
        ((multiplicity.squarefree_iff_multiplicity_le_one p).mp hp.squarefree a).resolve_right
          ha.not_unit
#align multiplicity.finite_prime_left multiplicity.finite_prime_left

end CancelCommMonoidWithZero

end multiplicity

section Irreducible

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (∀ x : R, Irreducible x → ¬x * x ∣ r) ↔ (r = 0 ∧ ∀ x : R, ¬Irreducible x) ∨ Squarefree r := by
  symm
  -- ⊢ (r = 0 ∧ ∀ (x : R), ¬Irreducible x) ∨ Squarefree r ↔ ∀ (x : R), Irreducible  …
  constructor
  -- ⊢ (r = 0 ∧ ∀ (x : R), ¬Irreducible x) ∨ Squarefree r → ∀ (x : R), Irreducible  …
  · rintro (⟨rfl, h⟩ | h)
    -- ⊢ ∀ (x : R), Irreducible x → ¬x * x ∣ 0
    · simpa using h
      -- 🎉 no goals
    intro x hx t
    -- ⊢ False
    exact hx.not_unit (h x t)
    -- 🎉 no goals
  intro h
  -- ⊢ (r = 0 ∧ ∀ (x : R), ¬Irreducible x) ∨ Squarefree r
  rcases eq_or_ne r 0 with (rfl | hr)
  -- ⊢ (0 = 0 ∧ ∀ (x : R), ¬Irreducible x) ∨ Squarefree 0
  · exact Or.inl (by simpa using h)
    -- 🎉 no goals
  right
  -- ⊢ Squarefree r
  intro x hx
  -- ⊢ IsUnit x
  by_contra i
  -- ⊢ False
  have : x ≠ 0 := by
    rintro rfl
    apply hr
    simpa only [zero_dvd_iff, mul_zero] using hx
  obtain ⟨j, hj₁, hj₂⟩ := WfDvdMonoid.exists_irreducible_factor i this
  -- ⊢ False
  exact h _ hj₁ ((mul_dvd_mul hj₂ hj₂).trans hx)
  -- 🎉 no goals
#align irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree

theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r ≠ 0) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm
  -- 🎉 no goals
#align squarefree_iff_irreducible_sq_not_dvd_of_ne_zero squarefree_iff_irreducible_sq_not_dvd_of_ne_zero

theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R}
    (hr : ∃ x : R, Irreducible x) : Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ← not_exists]
  -- ⊢ Squarefree r ↔ (r = 0 ∧ ¬∃ x, Irreducible x) ∨ Squarefree r
  simp only [hr, not_true, false_or_iff, and_false_iff]
  -- 🎉 no goals
#align squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible

end Irreducible

section IsRadical

variable [CancelCommMonoidWithZero R]

theorem IsRadical.squarefree {x : R} (h0 : x ≠ 0) (h : IsRadical x) : Squarefree x := by
  rintro z ⟨w, rfl⟩
  -- ⊢ IsUnit z
  specialize h 2 (z * w) ⟨w, by simp_rw [pow_two, mul_left_comm, ← mul_assoc]⟩
  -- ⊢ IsUnit z
  rwa [← one_mul (z * w), mul_assoc, mul_dvd_mul_iff_right, ← isUnit_iff_dvd_one] at h
  -- ⊢ z * w ≠ 0
  rw [mul_assoc, mul_ne_zero_iff] at h0; exact h0.2
  -- ⊢ z * w ≠ 0
                                         -- 🎉 no goals
#align is_radical.squarefree IsRadical.squarefree

variable [GCDMonoid R]

theorem Squarefree.isRadical {x : R} (hx : Squarefree x) : IsRadical x :=
  (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy =>
    And.right <|
      (dvd_gcd_iff x x y).1
        (by
          by_cases gcd x y = 0
          -- ⊢ x ∣ gcd x y
          -- ⊢ x ∣ gcd x y
          · rw [h]
            -- ⊢ x ∣ 0
            apply dvd_zero
            -- 🎉 no goals
          replace hy := ((dvd_gcd_iff x x _).2 ⟨dvd_rfl, hy⟩).trans gcd_pow_right_dvd_pow_gcd
          -- ⊢ x ∣ gcd x y
          obtain ⟨z, hz⟩ := gcd_dvd_left x y
          -- ⊢ x ∣ gcd x y
          nth_rw 1 [hz] at hy ⊢
          -- ⊢ gcd x y * z ∣ gcd x y
          rw [pow_two, mul_dvd_mul_iff_left h] at hy
          -- ⊢ gcd x y * z ∣ gcd x y
          obtain ⟨w, hw⟩ := hy
          -- ⊢ gcd x y * z ∣ gcd x y
          exact (hx z ⟨w, by rwa [mul_right_comm, ← hw]⟩).mul_right_dvd.2 dvd_rfl)
          -- 🎉 no goals
#align squarefree.is_radical Squarefree.isRadical

theorem isRadical_iff_squarefree_or_zero {x : R} : IsRadical x ↔ Squarefree x ∨ x = 0 :=
  ⟨fun hx => (em <| x = 0).elim Or.inr fun h => Or.inl <| hx.squarefree h,
    Or.rec Squarefree.isRadical <| by
      rintro rfl
      -- ⊢ IsRadical 0
      rw [zero_isRadical_iff]
      -- ⊢ IsReduced R
      infer_instance⟩
      -- 🎉 no goals
#align is_radical_iff_squarefree_or_zero isRadical_iff_squarefree_or_zero

theorem isRadical_iff_squarefree_of_ne_zero {x : R} (h : x ≠ 0) : IsRadical x ↔ Squarefree x :=
  ⟨IsRadical.squarefree h, Squarefree.isRadical⟩
#align is_radical_iff_squarefree_of_ne_zero isRadical_iff_squarefree_of_ne_zero

end IsRadical

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

theorem squarefree_iff_nodup_normalizedFactors [NormalizationMonoid R] [DecidableEq R] {x : R}
    (x0 : x ≠ 0) : Squarefree x ↔ Multiset.Nodup (normalizedFactors x) := by
  have drel : DecidableRel (Dvd.dvd : R → R → Prop) := by classical infer_instance
  -- ⊢ Squarefree x ↔ Multiset.Nodup (normalizedFactors x)
  rw [multiplicity.squarefree_iff_multiplicity_le_one, Multiset.nodup_iff_count_le_one]
  -- ⊢ (∀ (x_1 : R), multiplicity x_1 x ≤ 1 ∨ IsUnit x_1) ↔ ∀ (a : R), Multiset.cou …
  haveI := nontrivial_of_ne x 0 x0
  -- ⊢ (∀ (x_1 : R), multiplicity x_1 x ≤ 1 ∨ IsUnit x_1) ↔ ∀ (a : R), Multiset.cou …
  constructor <;> intro h a
  -- ⊢ (∀ (x_1 : R), multiplicity x_1 x ≤ 1 ∨ IsUnit x_1) → ∀ (a : R), Multiset.cou …
                  -- ⊢ Multiset.count a (normalizedFactors x) ≤ 1
                  -- ⊢ multiplicity a x ≤ 1 ∨ IsUnit a
  · by_cases hmem : a ∈ normalizedFactors x
    -- ⊢ Multiset.count a (normalizedFactors x) ≤ 1
    · have ha := irreducible_of_normalized_factor _ hmem
      -- ⊢ Multiset.count a (normalizedFactors x) ≤ 1
      rcases h a with (h | h)
      -- ⊢ Multiset.count a (normalizedFactors x) ≤ 1
      · rw [← normalize_normalized_factor _ hmem]
        -- ⊢ Multiset.count (↑normalize a) (normalizedFactors x) ≤ 1
        rw [multiplicity_eq_count_normalizedFactors ha x0] at h
        -- ⊢ Multiset.count (↑normalize a) (normalizedFactors x) ≤ 1
        assumption_mod_cast
        -- 🎉 no goals
      · have := ha.1
        -- ⊢ Multiset.count a (normalizedFactors x) ≤ 1
        contradiction
        -- 🎉 no goals
    · simp [Multiset.count_eq_zero_of_not_mem hmem]
      -- 🎉 no goals
  · rw [or_iff_not_imp_right]
    -- ⊢ ¬IsUnit a → multiplicity a x ≤ 1
    intro hu
    -- ⊢ multiplicity a x ≤ 1
    by_cases h0 : a = 0
    -- ⊢ multiplicity a x ≤ 1
    · simp [h0, x0]
      -- 🎉 no goals
    rcases WfDvdMonoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩
    -- ⊢ multiplicity a x ≤ 1
    apply le_trans (multiplicity.multiplicity_le_multiplicity_of_dvd_left hdvd)
    -- ⊢ multiplicity b x ≤ 1
    rw [multiplicity_eq_count_normalizedFactors hib x0]
    -- ⊢ ↑(Multiset.count (↑normalize b) (normalizedFactors x)) ≤ 1
    specialize h (normalize b)
    -- ⊢ ↑(Multiset.count (↑normalize b) (normalizedFactors x)) ≤ 1
    assumption_mod_cast
    -- 🎉 no goals
#align unique_factorization_monoid.squarefree_iff_nodup_normalized_factors UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors

theorem dvd_pow_iff_dvd_of_squarefree {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) :
    x ∣ y ^ n ↔ x ∣ y := by
  classical
    haveI := UniqueFactorizationMonoid.toGCDMonoid R
    exact ⟨hsq.isRadical n y, fun h => h.pow h0⟩
#align unique_factorization_monoid.dvd_pow_iff_dvd_of_squarefree UniqueFactorizationMonoid.dvd_pow_iff_dvd_of_squarefree

end UniqueFactorizationMonoid

namespace Int

@[simp]
theorem squarefree_natAbs {n : ℤ} : Squarefree n.natAbs ↔ Squarefree n := by
  simp_rw [Squarefree, natAbs_surjective.forall, ← natAbs_mul, natAbs_dvd_natAbs,
    isUnit_iff_natAbs_eq, Nat.isUnit_iff]
#align int.squarefree_nat_abs Int.squarefree_natAbs

@[simp]
theorem squarefree_coe_nat {n : ℕ} : Squarefree (n : ℤ) ↔ Squarefree n := by
  rw [← squarefree_natAbs, natAbs_ofNat]
  -- 🎉 no goals
#align int.squarefree_coe_nat Int.squarefree_coe_nat

end Int
