/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.Data.Finite.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Dihedral Groups

We define the dihedral groups `DihedralGroup n`, with elements `r i` and `sr i` for `i : ZMod n`.

For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/

assert_not_exists Ideal TwoSidedIdeal

/-- For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of
the `n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/
inductive DihedralGroup (n : ℕ) : Type
  | r : ZMod n → DihedralGroup n
  | sr : ZMod n → DihedralGroup n
  deriving DecidableEq

namespace DihedralGroup

variable {n : ℕ}

/-- Multiplication of the dihedral group.
-/
private def mul : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

/-- The identity `1` is the rotation by `0`.
-/
private def one : DihedralGroup n :=
  r 0

instance : Inhabited (DihedralGroup n) :=
  ⟨one⟩

/-- The inverse of an element of the dihedral group.
-/
private def inv : DihedralGroup n → DihedralGroup n
  | r i => r (-i)
  | sr i => sr i

/-- The group structure on `DihedralGroup n`.
-/
instance : Group (DihedralGroup n) where
  mul := mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul] <;> ring_nf
  one := one
  one_mul := by
    rintro (a | a)
    · exact congr_arg r (zero_add a)
    · exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    · exact congr_arg r (add_zero a)
    · exact congr_arg sr (add_zero a)
  inv := inv
  inv_mul_cancel := by
    rintro (a | a)
    · exact congr_arg r (neg_add_cancel a)
    · exact congr_arg r (sub_self a)

@[simp]
theorem r_mul_r (i j : ZMod n) : r i * r j = r (i + j) :=
  rfl

@[simp]
theorem r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i) :=
  rfl

@[simp]
theorem sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j) :=
  rfl

@[simp]
theorem sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i) :=
  rfl

@[simp]
theorem inv_r (i : ZMod n) : (r i)⁻¹ = r (-i) :=
  rfl

@[simp]
theorem inv_sr (i : ZMod n) : (sr i)⁻¹ = sr i :=
  rfl

@[simp]
theorem r_zero : r 0 = (1 : DihedralGroup n) :=
  rfl

theorem one_def : (1 : DihedralGroup n) = r 0 :=
  rfl

@[simp]
theorem r_pow (i : ZMod n) (k : ℕ) : (r i)^k = r (i * k : ZMod n) := by
  induction k with
  | zero => simp only [pow_zero, Nat.cast_zero, mul_zero, r_zero]
  | succ k IH =>
    rw [pow_add, pow_one, IH, r_mul_r, Nat.cast_add, Nat.cast_one, r.injEq, mul_add, mul_one]

@[simp]
theorem r_zpow (i : ZMod n) (k : ℤ) : (r i)^k = r (i * k : ZMod n) := by
  cases k <;> simp [r_pow, neg_mul_eq_mul_neg]

private def fintypeHelper : (ZMod n) ⊕ (ZMod n) ≃ DihedralGroup n where
  invFun
    | r j => .inl j
    | sr j => .inr j
  toFun
    | .inl j => r j
    | .inr j => sr j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- If `0 < n`, then `DihedralGroup n` is a finite group.
-/
instance [NeZero n] : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

instance : Infinite (DihedralGroup 0) :=
  DihedralGroup.fintypeHelper.infinite_iff.mp inferInstance

instance : Nontrivial (DihedralGroup n) :=
  ⟨⟨r 0, sr 0, by simp_rw [ne_eq, reduceCtorEq, not_false_eq_true]⟩⟩

/-- If `0 < n`, then `DihedralGroup n` has `2n` elements.
-/
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩, Fintype.card_sum, ZMod.card, two_mul]

theorem nat_card : Nat.card (DihedralGroup n) = 2 * n := by
  cases n
  · rw [Nat.card_eq_zero_of_infinite]
  · rw [Nat.card_eq_fintype_card, card]

theorem r_one_pow (k : ℕ) : (r 1 : DihedralGroup n) ^ k = r k := by
  simp only [r_pow, one_mul]

theorem r_one_zpow (k : ℤ) : (r 1 : DihedralGroup n) ^ k = r k := by
  simp only [r_zpow, one_mul]

theorem r_one_pow_n : r (1 : ZMod n) ^ n = 1 := by
  simp

theorem sr_mul_self (i : ZMod n) : sr i * sr i = 1 := by
  simp

/-- If `0 < n`, then `sr i` has order 2.
-/
@[simp]
theorem orderOf_sr (i : ZMod n) : orderOf (sr i) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, sr_mul_self]
  · simp [← r_zero]

/-- If `0 < n`, then `r 1` has order `n`.
-/
@[simp]
theorem orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · rw [orderOf_eq_zero_iff']
    intro n hn
    rw [r_one_pow, one_def]
    apply mt r.inj
    simpa using hn.ne'
  · apply (Nat.le_of_dvd (NeZero.pos n) <|
      orderOf_dvd_of_pow_eq_one <| @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt h] at h2
    exact absurd h2.symm (orderOf_pos _).ne

/-- If `0 < n`, then `i : ZMod n` has order `n / gcd n i`.
-/
theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← r_one_pow, orderOf_pow, orderOf_r_one]

theorem exponent : Monoid.exponent (DihedralGroup n) = lcm n 2 := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · exact Monoid.exponent_eq_zero_of_order_zero orderOf_r_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_r]
      refine Nat.dvd_trans ⟨gcd n m.val, ?_⟩ (dvd_lcm_left n 2)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_sr]
      exact dvd_lcm_right n 2
  · apply lcm_dvd
    · convert Monoid.order_dvd_exponent (r (1 : ZMod n))
      exact orderOf_r_one.symm
    · convert Monoid.order_dvd_exponent (sr (0 : ZMod n))
      exact (orderOf_sr 0).symm

lemma not_commutative : ∀ {n : ℕ}, n ≠ 1 → n ≠ 2 →
    ¬Std.Commutative fun (x y : DihedralGroup n) => x * y
  | 0, _, _ => fun ⟨h'⟩ ↦ by simpa using h' (r 1) (sr 0)
  | n + 3, _, _ => by
    rintro ⟨h'⟩
    specialize h' (r 1) (sr 0)
    rw [r_mul_sr, zero_sub, sr_mul_r, zero_add, sr.injEq, neg_eq_iff_add_eq_zero,
      one_add_one_eq_two, ← ZMod.val_eq_zero, ZMod.val_two_eq_two_mod] at h'
    simpa using Nat.le_of_dvd Nat.zero_lt_two <| Nat.dvd_of_mod_eq_zero h'

lemma commutative_iff : Std.Commutative (fun x y : DihedralGroup n ↦ x * y) ↔ n = 1 ∨ n = 2 where
  mp := by contrapose!; rintro ⟨h1, h2⟩; exact not_commutative h1 h2
  mpr := by rintro (rfl | rfl) <;> exact ⟨by decide⟩

lemma not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n) := fun h => by
  by_cases h2 : n = 2
  · simpa [exponent, card, h2] using h.exponent_eq_card
  · exact not_commutative h1 h2 h.commutative

lemma isCyclic_iff : IsCyclic (DihedralGroup n) ↔ n = 1 where
  mp := not_imp_not.mp not_isCyclic
  mpr h := h ▸ isCyclic_of_prime_card (p := 2) nat_card

instance : IsKleinFour (DihedralGroup 2) where
  card_four := DihedralGroup.nat_card
  exponent_two := DihedralGroup.exponent

/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs (represented as
$n + n + n + n*n$) of commuting elements. -/
@[simps]
def oddCommuteEquiv (hn : Odd n) : { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } ≃
    ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n × ZMod n :=
  let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat)
  have hu : ∀ a : ZMod n, a + a = 0 ↔ a = 0 := fun _ => ZMod.add_self_eq_zero_iff_eq_zero hn
  { toFun := fun
      | ⟨⟨sr i, r _⟩, _⟩ => Sum.inl i
      | ⟨⟨r _, sr j⟩, _⟩ => Sum.inr (Sum.inl j)
      | ⟨⟨sr i, sr j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inl (i + j)))
      | ⟨⟨r i, r j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩))
    invFun := fun
      | .inl i => ⟨⟨sr i, r 0⟩, congrArg sr ((add_zero i).trans (sub_zero i).symm)⟩
      | .inr (.inl j) => ⟨⟨r 0, sr j⟩, congrArg sr ((sub_zero j).trans (add_zero j).symm)⟩
      | .inr (.inr (.inl k)) => ⟨⟨sr (u⁻¹ * k), sr (u⁻¹ * k)⟩, rfl⟩
      | .inr (.inr (.inr ⟨i, j⟩)) => ⟨⟨r i, r j⟩, congrArg r (add_comm i j)⟩
    left_inv := fun
      | ⟨⟨r _, r _⟩, _⟩ => rfl
      | ⟨⟨r i, sr j⟩, h⟩ => by
        simpa [- r_zero, sub_eq_add_neg, neg_eq_iff_add_eq_zero, hu, eq_comm (a := i) (b := 0)]
          using h.eq
      | ⟨⟨sr i, r j⟩, h⟩ => by
        simpa [- r_zero, sub_eq_add_neg, eq_neg_iff_add_eq_zero, hu, eq_comm (a := j) (b := 0)]
          using h.eq
      | ⟨⟨sr i, sr j⟩, h⟩ => by
        replace h := r.inj h
        rw [← neg_sub, neg_eq_iff_add_eq_zero, hu, sub_eq_zero] at h
        rw [Subtype.ext_iff, Prod.ext_iff, sr.injEq, sr.injEq, h, and_self, ← two_mul]
        exact u.inv_mul_cancel_left j
    right_inv := fun
      | .inl _ => rfl
      | .inr (.inl _) => rfl
      | .inr (.inr (.inl k)) =>
        congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) <| two_mul (u⁻¹ * k) ▸ u.mul_inv_cancel_left k
      | .inr (.inr (.inr ⟨_, _⟩)) => rfl }

@[deprecated (since := "2025-05-07")] alias OddCommuteEquiv := oddCommuteEquiv

@[deprecated (since := "2025-05-07")] alias
OddCommuteEquiv_apply := DihedralGroup.oddCommuteEquiv_apply
@[deprecated (since := "2025-05-07")] alias
OddCommuteEquiv_symm_apply := DihedralGroup.oddCommuteEquiv_symm_apply

/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs of commuting elements. -/
lemma card_commute_odd (hn : Odd n) :
    Nat.card { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 3) := by
  have hn' : NeZero n := ⟨hn.pos.ne'⟩
  simp_rw [Nat.card_congr (oddCommuteEquiv hn), Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  ring

lemma card_conjClasses_odd (hn : Odd n) :
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 3) / 2 := by
  rw [← Nat.mul_div_mul_left _ 2 hn.pos, ← card_commute_odd hn, mul_comm,
    card_comm_eq_card_conjClasses_mul_card, nat_card, Nat.mul_div_left _ (mul_pos two_pos hn.pos)]


end DihedralGroup
