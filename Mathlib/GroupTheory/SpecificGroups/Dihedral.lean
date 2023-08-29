/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Exponent

#align_import group_theory.specific_groups.dihedral from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Dihedral Groups

We define the dihedral groups `DihedralGroup n`, with elements `r i` and `sr i` for `i : ZMod n`.

For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/


/-- For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of
the `n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/
inductive DihedralGroup (n : ℕ) : Type
  | r : ZMod n → DihedralGroup n
  | sr : ZMod n → DihedralGroup n
  deriving DecidableEq
#align dihedral_group DihedralGroup

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
                                                     -- ⊢ r (a + b + c) = r (a + (b + c))
                                                     -- ⊢ sr (c - (a + b)) = sr (c - b - a)
                                                     -- ⊢ sr (b - a + c) = sr (b + c - a)
                                                     -- ⊢ r (c - (b - a)) = r (a + (c - b))
                                                     -- ⊢ sr (a + b + c) = sr (a + (b + c))
                                                     -- ⊢ r (c - (a + b)) = r (c - b - a)
                                                     -- ⊢ r (b - a + c) = r (b + c - a)
                                                     -- ⊢ sr (c - (b - a)) = sr (a + (c - b))
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals
  one := one
  one_mul := by
    rintro (a | a)
    -- ⊢ 1 * r a = r a
    exact congr_arg r (zero_add a)
    -- ⊢ 1 * sr a = sr a
    exact congr_arg sr (sub_zero a)
    -- 🎉 no goals
  mul_one := by
    rintro (a | a)
    -- ⊢ r a * 1 = r a
    exact congr_arg r (add_zero a)
    -- ⊢ sr a * 1 = sr a
    exact congr_arg sr (add_zero a)
    -- 🎉 no goals
  inv := inv
  mul_left_inv := by
    rintro (a | a)
    -- ⊢ (r a)⁻¹ * r a = 1
    exact congr_arg r (neg_add_self a)
    -- ⊢ (sr a)⁻¹ * sr a = 1
    exact congr_arg r (sub_self a)
    -- 🎉 no goals

@[simp]
theorem r_mul_r (i j : ZMod n) : r i * r j = r (i + j) :=
  rfl
#align dihedral_group.r_mul_r DihedralGroup.r_mul_r

@[simp]
theorem r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i) :=
  rfl
#align dihedral_group.r_mul_sr DihedralGroup.r_mul_sr

@[simp]
theorem sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j) :=
  rfl
#align dihedral_group.sr_mul_r DihedralGroup.sr_mul_r

@[simp]
theorem sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i) :=
  rfl
#align dihedral_group.sr_mul_sr DihedralGroup.sr_mul_sr

theorem one_def : (1 : DihedralGroup n) = r 0 :=
  rfl
#align dihedral_group.one_def DihedralGroup.one_def

private def fintypeHelper : Sum (ZMod n) (ZMod n) ≃ DihedralGroup n where
  invFun i := match i with
    | r j => Sum.inl j
    | sr j => Sum.inr j
  toFun i := match i with
    | Sum.inl j => r j
    | Sum.inr j => sr j
  left_inv := by rintro (x | x) <;> rfl
                                    -- 🎉 no goals
                                    -- 🎉 no goals
  right_inv := by rintro (x | x) <;> rfl
                                     -- 🎉 no goals
                                     -- 🎉 no goals

/-- If `0 < n`, then `DihedralGroup n` is a finite group.
-/
instance [NeZero n] : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

instance : Infinite (DihedralGroup 0) :=
  DihedralGroup.fintypeHelper.infinite_iff.mp inferInstance

instance : Nontrivial (DihedralGroup n) :=
  ⟨⟨r 0, sr 0, by simp_rw [ne_eq]⟩⟩
                  -- 🎉 no goals

/-- If `0 < n`, then `DihedralGroup n` has `2n` elements.
-/
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩, Fintype.card_sum, ZMod.card, two_mul]
  -- 🎉 no goals
#align dihedral_group.card DihedralGroup.card

theorem nat_card : Nat.card (DihedralGroup n) = 2 * n := by
  cases n
  -- ⊢ Nat.card (DihedralGroup Nat.zero) = 2 * Nat.zero
  · rw [Nat.card_eq_zero_of_infinite]
    -- 🎉 no goals
  · rw [Nat.card_eq_fintype_card, card]
    -- 🎉 no goals

@[simp]
theorem r_one_pow (k : ℕ) : (r 1 : DihedralGroup n) ^ k = r k := by
  induction' k with k IH
  -- ⊢ r 1 ^ Nat.zero = r ↑Nat.zero
  · rw [Nat.cast_zero]
    -- ⊢ r 1 ^ Nat.zero = r 0
    rfl
    -- 🎉 no goals
  · rw [pow_succ, IH, r_mul_r]
    -- ⊢ r (1 + ↑k) = r ↑(Nat.succ k)
    congr 1
    -- ⊢ 1 + ↑k = ↑(Nat.succ k)
    norm_cast
    -- ⊢ ↑(1 + k) = ↑(Nat.succ k)
    rw [Nat.one_add]
    -- 🎉 no goals
#align dihedral_group.r_one_pow DihedralGroup.r_one_pow

-- @[simp] -- Porting note: simp changes the goal to `r 0 = 1`. `r_one_pow_n` is no longer useful.
theorem r_one_pow_n : r (1 : ZMod n) ^ n = 1 := by
  rw [r_one_pow, one_def]
  -- ⊢ r ↑n = r 0
  congr 1
  -- ⊢ ↑n = 0
  exact ZMod.nat_cast_self _
  -- 🎉 no goals
#align dihedral_group.r_one_pow_n DihedralGroup.r_one_pow_n

-- @[simp] -- Porting note: simp changes the goal to `r 0 = 1`. `sr_mul_self` is no longer useful.
theorem sr_mul_self (i : ZMod n) : sr i * sr i = 1 := by rw [sr_mul_sr, sub_self, one_def]
                                                         -- 🎉 no goals
#align dihedral_group.sr_mul_self DihedralGroup.sr_mul_self

/-- If `0 < n`, then `sr i` has order 2.
-/
@[simp]
theorem orderOf_sr (i : ZMod n) : orderOf (sr i) = 2 := by
  apply orderOf_eq_prime
  -- ⊢ sr i ^ 2 = 1
  · rw [sq, sr_mul_self]
    -- 🎉 no goals
  · -- Porting note: Previous proof was `decide`
    revert n
    -- ⊢ ∀ {n : ℕ} (i : ZMod n), sr i ≠ 1
    simp_rw [one_def, ne_eq, forall_const]
    -- 🎉 no goals
#align dihedral_group.order_of_sr DihedralGroup.orderOf_sr

/-- If `0 < n`, then `r 1` has order `n`.
-/
@[simp]
theorem orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  -- ⊢ orderOf (r 1) = 0
  · rw [orderOf_eq_zero_iff']
    -- ⊢ ∀ (n : ℕ), 0 < n → r 1 ^ n ≠ 1
    intro n hn
    -- ⊢ r 1 ^ n ≠ 1
    rw [r_one_pow, one_def]
    -- ⊢ r ↑n ≠ r 0
    apply mt r.inj
    -- ⊢ ¬↑n = 0
    simpa using hn.ne'
    -- 🎉 no goals
  · apply (Nat.le_of_dvd (NeZero.pos n) <|
      orderOf_dvd_of_pow_eq_one <| @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    -- ⊢ False
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    -- ⊢ False
    rw [r_one_pow] at h1
    -- ⊢ False
    injection h1 with h2
    -- ⊢ False
    rw [← ZMod.val_eq_zero, ZMod.val_nat_cast, Nat.mod_eq_of_lt h] at h2
    -- ⊢ False
    exact absurd h2.symm (orderOf_pos _).ne
    -- 🎉 no goals
#align dihedral_group.order_of_r_one DihedralGroup.orderOf_r_one

/-- If `0 < n`, then `i : ZMod n` has order `n / gcd n i`.
-/
theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val := by
  conv_lhs => rw [← ZMod.nat_cast_zmod_val i]
  -- ⊢ orderOf (r ↑(ZMod.val i)) = n / Nat.gcd n (ZMod.val i)
  rw [← r_one_pow, orderOf_pow, orderOf_r_one]
  -- 🎉 no goals
#align dihedral_group.order_of_r DihedralGroup.orderOf_r

theorem exponent : Monoid.exponent (DihedralGroup n) = lcm n 2 := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  -- ⊢ Monoid.exponent (DihedralGroup 0) = lcm 0 2
  · exact Monoid.exponent_eq_zero_of_order_zero orderOf_r_one
    -- 🎉 no goals
  apply Nat.dvd_antisymm
  -- ⊢ Monoid.exponent (DihedralGroup n) ∣ lcm n 2
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    -- ⊢ ∀ (g : DihedralGroup n), g ^ lcm n 2 = 1
    rintro (m | m)
    -- ⊢ r m ^ lcm n 2 = 1
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_r]
      -- ⊢ n / Nat.gcd n (ZMod.val m) ∣ lcm n 2
      refine' Nat.dvd_trans ⟨gcd n m.val, _⟩ (dvd_lcm_left n 2)
      -- ⊢ n = n / Nat.gcd n (ZMod.val m) * gcd n (ZMod.val m)
      · exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
        -- 🎉 no goals
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_sr]
      -- ⊢ 2 ∣ lcm n 2
      exact dvd_lcm_right n 2
      -- 🎉 no goals
  · apply lcm_dvd
    -- ⊢ n ∣ Monoid.exponent (DihedralGroup n)
    · convert Monoid.order_dvd_exponent (r (1 : ZMod n))
      -- ⊢ n = orderOf (r 1)
      exact orderOf_r_one.symm
      -- 🎉 no goals
    · convert Monoid.order_dvd_exponent (sr (0 : ZMod n))
      -- ⊢ 2 = orderOf (sr 0)
      exact (orderOf_sr 0).symm
      -- 🎉 no goals
#align dihedral_group.exponent DihedralGroup.exponent

/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs (represented as
$n + n + n + n*n$) of commuting elements. -/
@[simps]
def OddCommuteEquiv (hn : Odd n) : { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } ≃
    ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n × ZMod n :=
  let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat)
  have hu : ∀ a : ZMod n, a + a = 0 ↔ a = 0 := fun a => ZMod.add_self_eq_zero_iff_eq_zero hn
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
      | ⟨⟨r i, r j⟩, h⟩ => rfl
      | ⟨⟨r i, sr j⟩, h⟩ => by
        simpa [sub_eq_add_neg, neg_eq_iff_add_eq_zero, hu, eq_comm (a := i) (b := 0)] using h.eq
        -- 🎉 no goals
      | ⟨⟨sr i, r j⟩, h⟩ => by
        simpa [sub_eq_add_neg, eq_neg_iff_add_eq_zero, hu, eq_comm (a := j) (b := 0)] using h.eq
        -- 🎉 no goals
      | ⟨⟨sr i, sr j⟩, h⟩ => by
        replace h := r.inj h
        -- ⊢ (fun x =>
        rw [←neg_sub, neg_eq_iff_add_eq_zero, hu, sub_eq_zero] at h
        -- ⊢ (fun x =>
        rw [Subtype.ext_iff, Prod.ext_iff, sr.injEq, sr.injEq, h, and_self, ←two_mul]
        -- ⊢ ↑u⁻¹ * (2 * j) = j
        exact u.inv_mul_cancel_left j
        -- 🎉 no goals
    right_inv := fun
      | .inl i => rfl
      | .inr (.inl j) => rfl
      | .inr (.inr (.inl k)) =>
        congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) $ two_mul (u⁻¹ * k) ▸ u.mul_inv_cancel_left k
      | .inr (.inr (.inr ⟨i, j⟩)) => rfl }

/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs of commuting elements. -/
lemma card_commute_odd (hn : Odd n) :
    Nat.card { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 3) := by
  have hn' : NeZero n := ⟨hn.pos.ne'⟩
  -- ⊢ Nat.card { p // Commute p.fst p.snd } = n * (n + 3)
  simp_rw [Nat.card_congr (OddCommuteEquiv hn), Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  -- ⊢ n + (n + (n + n * n)) = n * (n + 3)
  ring
  -- 🎉 no goals

lemma card_conjClasses_odd (hn : Odd n) :
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 3) / 2 := by
  rw [←Nat.mul_div_mul_left _ 2 hn.pos, ← card_commute_odd hn, mul_comm,
    card_comm_eq_card_conjClasses_mul_card, nat_card, Nat.mul_div_left _ (mul_pos two_pos hn.pos)]


end DihedralGroup
