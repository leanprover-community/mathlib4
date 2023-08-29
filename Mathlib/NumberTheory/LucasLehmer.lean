/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison, Ainsley Pahljina
-/
import Mathlib.Data.Nat.Parity
import Mathlib.Data.PNat.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Fintype
import Mathlib.Tactic.IntervalCases

#align_import number_theory.lucas_lehmer from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# The Lucas-Lehmer test for Mersenne primes.

We define `lucasLehmerResidue : Π p : ℕ, ZMod (2^p - 1)`, and
prove `lucasLehmerResidue p = 0 → Prime (mersenne p)`.

We construct a `norm_num` extension to calculate this residue to certify primality of Mersenne
primes using `lucas_lehmer_sufficiency`.


## TODO

- Show reverse implication.
- Speed up the calculations using `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]`.
- Find some bigger primes!

## History

This development began as a student project by Ainsley Pahljina,
and was then cleaned up for mathlib by Scott Morrison.
The tactic for certified computation of Lucas-Lehmer residues was provided by Mario Carneiro.
This tactic was ported by Thomas Murrills to Lean 4, and then it was converted to a `norm_num`
extension and made to use kernel reductions by Kyle Miller.
-/


/-- The Mersenne numbers, 2^p - 1. -/
def mersenne (p : ℕ) : ℕ :=
  2 ^ p - 1
#align mersenne mersenne

theorem mersenne_pos {p : ℕ} (h : 0 < p) : 0 < mersenne p := by
  dsimp [mersenne]
  -- ⊢ 0 < 2 ^ p - 1
  calc
    0 < 2 ^ 1 - 1 := by norm_num
    _ ≤ 2 ^ p - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_of_le_right (Nat.succ_pos 1) h) 1
#align mersenne_pos mersenne_pos

theorem one_lt_mersenne {p : ℕ} (hp : 1 < p) : 1 < mersenne p :=
  lt_tsub_iff_right.2 <|
    calc 1 + 1 = 2 ^ 1 := by rw [one_add_one_eq_two, pow_one]
                             -- 🎉 no goals
    _ < 2 ^ p := Nat.pow_lt_pow_of_lt_right one_lt_two hp

@[simp]
theorem succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k := by
  rw [mersenne, tsub_add_cancel_of_le]
  -- ⊢ 1 ≤ 2 ^ k
  exact one_le_pow_of_one_le (by norm_num) k
  -- 🎉 no goals
#align succ_mersenne succ_mersenne

namespace LucasLehmer

open Nat

/-!
We now define three(!) different versions of the recurrence
`s (i+1) = (s i)^2 - 2`.

These versions take values either in `ℤ`, in `ZMod (2^p - 1)`, or
in `ℤ` but applying `% (2^p - 1)` at each step.

They are each useful at different points in the proof,
so we take a moment setting up the lemmas relating them.
-/

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `ℤ`. -/
def s : ℕ → ℤ
  | 0 => 4
  | i + 1 => s i ^ 2 - 2
#align lucas_lehmer.s LucasLehmer.s

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `ZMod (2^p - 1)`. -/
def sZMod (p : ℕ) : ℕ → ZMod (2 ^ p - 1)
  | 0 => 4
  | i + 1 => sZMod p i ^ 2 - 2
#align lucas_lehmer.s_zmod LucasLehmer.sZMod

/-- The recurrence `s (i+1) = ((s i)^2 - 2) % (2^p - 1)` in `ℤ`. -/
def sMod (p : ℕ) : ℕ → ℤ
  | 0 => 4 % (2 ^ p - 1)
  | i + 1 => (sMod p i ^ 2 - 2) % (2 ^ p - 1)
#align lucas_lehmer.s_mod LucasLehmer.sMod

theorem mersenne_int_pos {p : ℕ} (hp : 0 < p) : (0 : ℤ) < 2 ^ p - 1 :=
  sub_pos.2 <| by exact_mod_cast Nat.one_lt_two_pow p hp
                  -- 🎉 no goals

theorem mersenne_int_ne_zero (p : ℕ) (w : 0 < p) : (2 ^ p - 1 : ℤ) ≠ 0 :=
  (mersenne_int_pos w).ne'
#align lucas_lehmer.mersenne_int_ne_zero LucasLehmer.mersenne_int_ne_zero

theorem sMod_nonneg (p : ℕ) (w : 0 < p) (i : ℕ) : 0 ≤ sMod p i := by
  cases i <;> dsimp [sMod]
  -- ⊢ 0 ≤ sMod p zero
              -- ⊢ 0 ≤ 4 % (2 ^ p - 1)
              -- ⊢ 0 ≤ (sMod p n✝ ^ 2 - 2) % (2 ^ p - 1)
  · exact sup_eq_right.mp rfl
    -- 🎉 no goals
  · apply Int.emod_nonneg
    -- ⊢ 2 ^ p - 1 ≠ 0
    exact mersenne_int_ne_zero p w
    -- 🎉 no goals
#align lucas_lehmer.s_mod_nonneg LucasLehmer.sMod_nonneg

theorem sMod_mod (p i : ℕ) : sMod p i % (2 ^ p - 1) = sMod p i := by cases i <;> simp [sMod]
                                                                     -- ⊢ sMod p zero % (2 ^ p - 1) = sMod p zero
                                                                                 -- 🎉 no goals
                                                                                 -- 🎉 no goals
#align lucas_lehmer.s_mod_mod LucasLehmer.sMod_mod

theorem sMod_lt (p : ℕ) (w : 0 < p) (i : ℕ) : sMod p i < 2 ^ p - 1 := by
  rw [← sMod_mod]
  -- ⊢ sMod p i % (2 ^ p - 1) < 2 ^ p - 1
  refine (Int.emod_lt _ (mersenne_int_ne_zero p w)).trans_eq ?_
  -- ⊢ |2 ^ p - 1| = 2 ^ p - 1
  exact abs_of_nonneg (mersenne_int_pos w).le
  -- 🎉 no goals
#align lucas_lehmer.s_mod_lt LucasLehmer.sMod_lt

theorem sZMod_eq_s (p' : ℕ) (i : ℕ) : sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' + 2) - 1)) := by
  induction' i with i ih
  -- ⊢ sZMod (p' + 2) zero = ↑(s zero)
  · dsimp [s, sZMod]
    -- ⊢ 4 = ↑4
    norm_num
    -- 🎉 no goals
  · push_cast [s, sZMod, ih]; rfl
    -- ⊢ ↑(s i) ^ 2 - 2 = ↑(s i) ^ 2 - 2
                              -- 🎉 no goals
#align lucas_lehmer.s_zmod_eq_s LucasLehmer.sZMod_eq_s

-- These next two don't make good `norm_cast` lemmas.
theorem Int.coe_nat_pow_pred (b p : ℕ) (w : 0 < b) : ((b ^ p - 1 : ℕ) : ℤ) = (b : ℤ) ^ p - 1 := by
  have : 1 ≤ b ^ p := Nat.one_le_pow p b w
  -- ⊢ ↑(b ^ p - 1) = ↑b ^ p - 1
  norm_cast
  -- 🎉 no goals
#align lucas_lehmer.int.coe_nat_pow_pred LucasLehmer.Int.coe_nat_pow_pred

theorem Int.coe_nat_two_pow_pred (p : ℕ) : ((2 ^ p - 1 : ℕ) : ℤ) = (2 ^ p - 1 : ℤ) :=
  Int.coe_nat_pow_pred 2 p (by decide)
                               -- 🎉 no goals
#align lucas_lehmer.int.coe_nat_two_pow_pred LucasLehmer.Int.coe_nat_two_pow_pred

theorem sZMod_eq_sMod (p : ℕ) (i : ℕ) : sZMod p i = (sMod p i : ZMod (2 ^ p - 1)) := by
  induction i <;> push_cast [← Int.coe_nat_two_pow_pred p, sMod, sZMod, *] <;> rfl
  -- ⊢ sZMod p zero = ↑(sMod p zero)
                  -- ⊢ 4 = 4
                  -- ⊢ ↑(sMod p n✝) ^ 2 - 2 = ↑(sMod p n✝) ^ 2 - 2
                                                                               -- 🎉 no goals
                                                                               -- 🎉 no goals
#align lucas_lehmer.s_zmod_eq_s_mod LucasLehmer.sZMod_eq_sMod

/-- The Lucas-Lehmer residue is `s p (p-2)` in `ZMod (2^p - 1)`. -/
def lucasLehmerResidue (p : ℕ) : ZMod (2 ^ p - 1) :=
  sZMod p (p - 2)
#align lucas_lehmer.lucas_lehmer_residue LucasLehmer.lucasLehmerResidue

theorem residue_eq_zero_iff_sMod_eq_zero (p : ℕ) (w : 1 < p) :
    lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0 := by
  dsimp [lucasLehmerResidue]
  -- ⊢ sZMod p (p - 2) = 0 ↔ sMod p (p - 2) = 0
  rw [sZMod_eq_sMod p]
  -- ⊢ ↑(sMod p (p - 2)) = 0 ↔ sMod p (p - 2) = 0
  constructor
  -- ⊢ ↑(sMod p (p - 2)) = 0 → sMod p (p - 2) = 0
  · -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h
    -- ⊢ sMod p (p - 2) = 0
    simp [ZMod.int_cast_zmod_eq_zero_iff_dvd] at h
    -- ⊢ sMod p (p - 2) = 0
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _ h <;> clear h
    -- ⊢ 0 ≤ sMod p (p - 2)
                                                       -- ⊢ 0 ≤ sMod p (p - 2)
                                                       -- ⊢ sMod p (p - 2) < 2 ^ p - 1
    · apply sMod_nonneg _ (Nat.lt_of_succ_lt w)
      -- 🎉 no goals
    · exact sMod_lt _ (Nat.lt_of_succ_lt w) (p - 2)
      -- 🎉 no goals
  · intro h
    -- ⊢ ↑(sMod p (p - 2)) = 0
    rw [h]
    -- ⊢ ↑0 = 0
    simp
    -- 🎉 no goals
#align lucas_lehmer.residue_eq_zero_iff_s_mod_eq_zero LucasLehmer.residue_eq_zero_iff_sMod_eq_zero

/-- A Mersenne number `2^p-1` is prime if and only if
the Lucas-Lehmer residue `s p (p-2) % (2^p - 1)` is zero.
-/
def LucasLehmerTest (p : ℕ) : Prop :=
  lucasLehmerResidue p = 0
#align lucas_lehmer.lucas_lehmer_test LucasLehmer.LucasLehmerTest

-- Porting note: We have a fast `norm_num` extension, and we would rather use that than accidentally
-- have `simp` use `decide`!
/-
instance : DecidablePred LucasLehmerTest :=
  inferInstanceAs (DecidablePred (lucasLehmerResidue · = 0))
-/

/-- `q` is defined as the minimum factor of `mersenne p`, bundled as an `ℕ+`. -/
def q (p : ℕ) : ℕ+ :=
  ⟨Nat.minFac (mersenne p), Nat.minFac_pos (mersenne p)⟩
#align lucas_lehmer.q LucasLehmer.q

-- It would be nice to define this as (ℤ/qℤ)[x] / (x^2 - 3),
-- obtaining the ring structure for free,
-- but that seems to be more trouble than it's worth;
-- if it were easy to make the definition,
-- cardinality calculations would be somewhat more involved, too.
/-- We construct the ring `X q` as ℤ/qℤ + √3 ℤ/qℤ. -/
def X (q : ℕ+) : Type :=
  ZMod q × ZMod q
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X LucasLehmer.X

namespace X

variable {q : ℕ+}

instance : Inhabited (X q) := inferInstanceAs (Inhabited (ZMod q × ZMod q))
instance : Fintype (X q) := inferInstanceAs (Fintype (ZMod q × ZMod q))
instance : DecidableEq (X q) := inferInstanceAs (DecidableEq (ZMod q × ZMod q))
instance : AddCommGroup (X q) := inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

@[ext]
theorem ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x; cases y; congr
  -- ⊢ (fst✝, snd✝) = y
           -- ⊢ (fst✝¹, snd✝¹) = (fst✝, snd✝)
                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.ext LucasLehmer.X.ext

@[simp] theorem zero_fst : (0 : X q).1 = 0 := rfl
@[simp] theorem zero_snd : (0 : X q).2 = 0 := rfl

@[simp]
theorem add_fst (x y : X q) : (x + y).1 = x.1 + y.1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.add_fst LucasLehmer.X.add_fst

@[simp]
theorem add_snd (x y : X q) : (x + y).2 = x.2 + y.2 :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.add_snd LucasLehmer.X.add_snd

@[simp]
theorem neg_fst (x : X q) : (-x).1 = -x.1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.neg_fst LucasLehmer.X.neg_fst

@[simp]
theorem neg_snd (x : X q) : (-x).2 = -x.2 :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.neg_snd LucasLehmer.X.neg_snd

instance : Mul (X q) where mul x y := (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp]
theorem mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.mul_fst LucasLehmer.X.mul_fst

@[simp]
theorem mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.mul_snd LucasLehmer.X.mul_snd

instance : One (X q) where one := ⟨1, 0⟩

@[simp]
theorem one_fst : (1 : X q).1 = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.one_fst LucasLehmer.X.one_fst

@[simp]
theorem one_snd : (1 : X q).2 = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.one_snd LucasLehmer.X.one_snd

#noalign lucas_lehmer.X.bit0_fst
#noalign lucas_lehmer.X.bit0_snd
#noalign lucas_lehmer.X.bit1_fst
#noalign lucas_lehmer.X.bit1_snd

instance : Monoid (X q) :=
  { inferInstanceAs (Mul (X q)), inferInstanceAs (One (X q)) with
    mul_assoc := fun x y z => by ext <;> dsimp <;> ring
                                 -- ⊢ (x * y * z).fst = (x * (y * z)).fst
                                         -- ⊢ (x.fst * y.fst + 3 * x.snd * y.snd) * z.fst + 3 * (x.fst * y.snd + x.snd * y …
                                         -- ⊢ (x.fst * y.fst + 3 * x.snd * y.snd) * z.snd + (x.fst * y.snd + x.snd * y.fst …
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
    one_mul := fun x => by ext <;> simp
                           -- ⊢ (1 * x).fst = x.fst
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    mul_one := fun x => by ext <;> simp }
                           -- ⊢ (x * 1).fst = x.fst
                                   -- 🎉 no goals
                                   -- 🎉 no goals

instance : NatCast (X q) where
    natCast := fun n => ⟨n, 0⟩

@[simp] theorem nat_coe_fst (n : ℕ) : (n : X q).fst = (n : ZMod q) := rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.nat_coe_fst LucasLehmer.X.nat_coe_fst

@[simp] theorem nat_coe_snd (n : ℕ) : (n : X q).snd = (0 : ZMod q) := rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.nat_coe_snd LucasLehmer.X.nat_coe_snd

@[simp] theorem ofNat_fst (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : X q).fst = OfNat.ofNat n :=
  rfl

@[simp] theorem ofNat_snd (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : X q).snd = 0 :=
  rfl

instance : AddGroupWithOne (X q) :=
  { inferInstanceAs (Monoid (X q)), inferInstanceAs (AddCommGroup (X q)),
      inferInstanceAs (NatCast (X q)) with
    natCast_zero := by ext <;> simp
                       -- ⊢ (NatCast.natCast 0).fst = 0.fst
                               -- 🎉 no goals
                               -- 🎉 no goals
    natCast_succ := fun _ ↦ by ext <;> simp
                               -- ⊢ (NatCast.natCast (x✝ + 1)).fst = (NatCast.natCast x✝ + 1).fst
                                       -- 🎉 no goals
                                       -- 🎉 no goals
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun n => by ext <;> simp
                                 -- ⊢ (IntCast.intCast ↑n).fst = (↑n).fst
                                         -- 🎉 no goals
                                         -- 🎉 no goals
    intCast_negSucc := fun n => by ext <;> simp }
                                   -- ⊢ (IntCast.intCast (Int.negSucc n)).fst = (-↑(n + 1)).fst
                                           -- 🎉 no goals
                                           -- 🎉 no goals

theorem left_distrib (x y z : X q) : x * (y + z) = x * y + x * z := by
  ext <;> dsimp <;> ring
  -- ⊢ (x * (y + z)).fst = (x * y + x * z).fst
          -- ⊢ x.fst * (y.fst + z.fst) + 3 * x.snd * (y.snd + z.snd) = x.fst * y.fst + 3 *  …
          -- ⊢ x.fst * (y.snd + z.snd) + x.snd * (y.fst + z.fst) = x.fst * y.snd + x.snd *  …
                    -- 🎉 no goals
                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.left_distrib LucasLehmer.X.left_distrib

theorem right_distrib (x y z : X q) : (x + y) * z = x * z + y * z := by
  ext <;> dsimp <;> ring
  -- ⊢ ((x + y) * z).fst = (x * z + y * z).fst
          -- ⊢ (x.fst + y.fst) * z.fst + 3 * (x.snd + y.snd) * z.snd = x.fst * z.fst + 3 *  …
          -- ⊢ (x.fst + y.fst) * z.snd + (x.snd + y.snd) * z.fst = x.fst * z.snd + x.snd *  …
                    -- 🎉 no goals
                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.right_distrib LucasLehmer.X.right_distrib

instance : Ring (X q) :=
  { inferInstanceAs (AddGroupWithOne (X q)), inferInstanceAs (AddCommGroup (X q)),
      inferInstanceAs (Monoid (X q)) with
    left_distrib := left_distrib
    right_distrib := right_distrib
    mul_zero := fun _ ↦ by ext <;> simp
                           -- ⊢ (x✝ * 0).fst = 0.fst
                           -- ⊢ (0 * x✝).fst = 0.fst
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    zero_mul := fun _ ↦ by ext <;> simp }

instance : CommRing (X q) :=
  { inferInstanceAs (Ring (X q)) with
    mul_comm := fun _ _ ↦ by ext <;> dsimp <;> ring }
                             -- ⊢ (x✝¹ * x✝).fst = (x✝ * x✝¹).fst
                                     -- ⊢ x✝¹.fst * x✝.fst + 3 * x✝¹.snd * x✝.snd = x✝.fst * x✝¹.fst + 3 * x✝.snd * x✝ …
                                     -- ⊢ x✝¹.fst * x✝.snd + x✝¹.snd * x✝.fst = x✝.fst * x✝¹.snd + x✝.snd * x✝¹.fst
                                               -- 🎉 no goals
                                               -- 🎉 no goals

instance [Fact (1 < (q : ℕ))] : Nontrivial (X q) :=
  ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

@[simp]
theorem int_coe_fst (n : ℤ) : (n : X q).fst = (n : ZMod q) :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.int_coe_fst LucasLehmer.X.int_coe_fst

@[simp]
theorem int_coe_snd (n : ℤ) : (n : X q).snd = (0 : ZMod q) :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.int_coe_snd LucasLehmer.X.int_coe_snd

@[norm_cast]
theorem coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) := by ext <;> simp
                                                                              -- ⊢ (↑(n * m)).fst = (↑n * ↑m).fst
                                                                                      -- 🎉 no goals
                                                                                      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.coe_mul LucasLehmer.X.coe_mul

@[norm_cast]
theorem coe_nat (n : ℕ) : ((n : ℤ) : X q) = (n : X q) := by ext <;> simp
                                                            -- ⊢ (↑↑n).fst = (↑n).fst
                                                                    -- 🎉 no goals
                                                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.coe_nat LucasLehmer.X.coe_nat

/-- The cardinality of `X` is `q^2`. -/
theorem card_eq : Fintype.card (X q) = q ^ 2 := by
  dsimp [X]
  -- ⊢ Fintype.card (ZMod ↑q × ZMod ↑q) = ↑q ^ 2
  rw [Fintype.card_prod, ZMod.card q, sq]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.X_card LucasLehmer.X.card_eq

/-- There are strictly fewer than `q^2` units, since `0` is not a unit. -/
nonrec theorem card_units_lt (w : 1 < q) : Fintype.card (X q)ˣ < q ^ 2 := by
  have : Fact (1 < (q : ℕ)) := ⟨w⟩
  -- ⊢ Fintype.card (X q)ˣ < ↑q ^ 2
  convert card_units_lt (X q)
  -- ⊢ ↑q ^ 2 = Fintype.card (X q)
  rw [card_eq]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.units_card LucasLehmer.X.card_units_lt

/-- We define `ω = 2 + √3`. -/
def ω : X q := (2, 1)
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.ω LucasLehmer.X.ω

/-- We define `ωb = 2 - √3`, which is the inverse of `ω`. -/
def ωb : X q := (2, -1)
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.ωb LucasLehmer.X.ωb

theorem ω_mul_ωb (q : ℕ+) : (ω : X q) * ωb = 1 := by
  dsimp [ω, ωb]
  -- ⊢ (2, 1) * (2, -1) = 1
  ext <;> simp; ring
  -- ⊢ ((2, 1) * (2, -1)).fst = 1.fst
          -- ⊢ 2 * 2 + -3 = 1
          -- 🎉 no goals
                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.ω_mul_ωb LucasLehmer.X.ω_mul_ωb

theorem ωb_mul_ω (q : ℕ+) : (ωb : X q) * ω = 1 := by
  rw [mul_comm, ω_mul_ωb]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.ωb_mul_ω LucasLehmer.X.ωb_mul_ω

/-- A closed form for the recurrence relation. -/
theorem closed_form (i : ℕ) : (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i := by
  induction' i with i ih
  -- ⊢ ↑(s zero) = ω ^ 2 ^ zero + ωb ^ 2 ^ zero
  · dsimp [s, ω, ωb]
    -- ⊢ ↑4 = (2, 1) ^ 1 + (2, -1) ^ 1
    ext <;> norm_num
    -- ⊢ (↑4).fst = ((2, 1) ^ 1 + (2, -1) ^ 1).fst
            -- 🎉 no goals
            -- 🎉 no goals
  · calc
      (s (i + 1) : X q) = (s i ^ 2 - 2 : ℤ) := rfl
      _ = (s i : X q) ^ 2 - 2 := by push_cast; rfl
      _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by rw [ih]
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 + 2 * (ωb ^ 2 ^ i * ω ^ 2 ^ i) - 2 := by ring
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 := by
        rw [← mul_pow ωb ω, ωb_mul_ω, one_pow, mul_one, add_sub_cancel]
      _ = ω ^ 2 ^ (i + 1) + ωb ^ 2 ^ (i + 1) := by rw [← pow_mul, ← pow_mul, _root_.pow_succ']
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.closed_form LucasLehmer.X.closed_form

end X

open X

/-!
Here and below, we introduce `p' = p - 2`, in order to avoid using subtraction in `ℕ`.
-/

/-- If `1 < p`, then `q p`, the smallest prime factor of `mersenne p`, is more than 2. -/
theorem two_lt_q (p' : ℕ) : 2 < q (p' + 2) := by
  refine (minFac_prime (one_lt_mersenne ?_).ne').two_le.lt_of_ne' ?_
  -- ⊢ 1 < p' + 2
  · exact le_add_left _ _
    -- 🎉 no goals
  · rw [Ne.def, minFac_eq_two_iff, mersenne, Nat.pow_succ']
    -- ⊢ ¬2 ∣ 2 * 2 ^ (p' + 1) - 1
    exact Nat.two_not_dvd_two_mul_sub_one (Nat.one_le_two_pow _)
    -- 🎉 no goals
#align lucas_lehmer.two_lt_q LucasLehmer.two_lt_q

theorem ω_pow_formula (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    ∃ k : ℤ,
      (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) =
        k * mersenne (p' + 2) * (ω : X (q (p' + 2))) ^ 2 ^ p' - 1 := by
  dsimp [lucasLehmerResidue] at h
  -- ⊢ ∃ k, ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  rw [sZMod_eq_s p'] at h
  -- ⊢ ∃ k, ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  simp [ZMod.int_cast_zmod_eq_zero_iff_dvd] at h
  -- ⊢ ∃ k, ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  cases' h with k h
  -- ⊢ ∃ k, ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  use k
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  replace h := congr_arg (fun n : ℤ => (n : X (q (p' + 2)))) h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  -- coercion from ℤ to X q
  dsimp at h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  rw [closed_form] at h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  replace h := congr_arg (fun x => ω ^ 2 ^ p' * x) h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  dsimp at h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  have t : 2 ^ p' + 2 ^ p' = 2 ^ (p' + 1) := by ring
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  rw [mul_add, ← pow_add ω, t, ← mul_pow ω ωb (2 ^ p'), ω_mul_ωb, one_pow] at h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  rw [mul_comm, coe_mul] at h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  rw [mul_comm _ (k : X (q (p' + 2)))] at h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  replace h := eq_sub_of_add_eq h
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  have : 1 ≤ 2 ^ (p' + 2) := Nat.one_le_pow _ _ (by decide)
  -- ⊢ ω ^ 2 ^ (p' + 1) = ↑k * ↑(mersenne (p' + 2)) * ω ^ 2 ^ p' - 1
  exact_mod_cast h
  -- 🎉 no goals
#align lucas_lehmer.ω_pow_formula LucasLehmer.ω_pow_formula

/-- `q` is the minimum factor of `mersenne p`, so `M p = 0` in `X q`. -/
theorem mersenne_coe_X (p : ℕ) : (mersenne p : X (q p)) = 0 := by
  ext <;> simp [mersenne, q, ZMod.nat_cast_zmod_eq_zero_iff_dvd, -pow_pos]
  -- ⊢ (↑(mersenne p)).fst = 0.fst
          -- ⊢ minFac (2 ^ p - 1) ∣ 2 ^ p - 1
          -- 🎉 no goals
  apply Nat.minFac_dvd
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.mersenne_coe_X LucasLehmer.mersenne_coe_X

theorem ω_pow_eq_neg_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) = -1 := by
  cases' ω_pow_formula p' h with k w
  -- ⊢ ω ^ 2 ^ (p' + 1) = -1
  rw [mersenne_coe_X] at w
  -- ⊢ ω ^ 2 ^ (p' + 1) = -1
  simpa using w
  -- 🎉 no goals
#align lucas_lehmer.ω_pow_eq_neg_one LucasLehmer.ω_pow_eq_neg_one

theorem ω_pow_eq_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = 1 :=
  calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul, ← Nat.pow_succ]
      -- 🎉 no goals
    _ = (-1) ^ 2 := by rw [ω_pow_eq_neg_one p' h]
                       -- 🎉 no goals
    _ = 1 := by simp
                -- 🎉 no goals
#align lucas_lehmer.ω_pow_eq_one LucasLehmer.ω_pow_eq_one

/-- `ω` as an element of the group of units. -/
def ωUnit (p : ℕ) : Units (X (q p)) where
  val := ω
  inv := ωb
  val_inv := ω_mul_ωb _
  inv_val := ωb_mul_ω _
#align lucas_lehmer.ω_unit LucasLehmer.ωUnit

@[simp]
theorem ωUnit_coe (p : ℕ) : (ωUnit p : X (q p)) = ω :=
  rfl
#align lucas_lehmer.ω_unit_coe LucasLehmer.ωUnit_coe

/-- The order of `ω` in the unit group is exactly `2^p`. -/
theorem order_ω (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    orderOf (ωUnit (p' + 2)) = 2 ^ (p' + 2) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  -- the order of ω divides 2^p
  · exact Nat.prime_two
    -- 🎉 no goals
  · intro o
    -- ⊢ False
    have ω_pow := orderOf_dvd_iff_pow_eq_one.1 o
    -- ⊢ False
    replace ω_pow :=
      congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) → X (q (p' + 2))) ω_pow
    simp at ω_pow
    -- ⊢ False
    have h : (1 : ZMod (q (p' + 2))) = -1 :=
      congr_arg Prod.fst (ω_pow.symm.trans (ω_pow_eq_neg_one p' h))
    haveI : Fact (2 < (q (p' + 2) : ℕ)) := ⟨two_lt_q _⟩
    -- ⊢ False
    apply ZMod.neg_one_ne_one h.symm
    -- 🎉 no goals
  · apply orderOf_dvd_iff_pow_eq_one.2
    -- ⊢ ωUnit (p' + 2) ^ 2 ^ (p' + 1 + 1) = 1
    apply Units.ext
    -- ⊢ ↑(ωUnit (p' + 2) ^ 2 ^ (p' + 1 + 1)) = ↑1
    push_cast
    -- ⊢ ↑(ωUnit (p' + 2)) ^ 2 ^ (p' + 1 + 1) = 1
    exact ω_pow_eq_one p' h
    -- 🎉 no goals
#align lucas_lehmer.order_ω LucasLehmer.order_ω

theorem order_ineq (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    2 ^ (p' + 2) < (q (p' + 2) : ℕ) ^ 2 :=
  calc
    2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := (order_ω p' h).symm
    _ ≤ Fintype.card (X (q (p' + 2)))ˣ := orderOf_le_card_univ
    _ < (q (p' + 2) : ℕ) ^ 2 := card_units_lt (Nat.lt_of_succ_lt (two_lt_q _))
#align lucas_lehmer.order_ineq LucasLehmer.order_ineq

end LucasLehmer

export LucasLehmer (LucasLehmerTest lucasLehmerResidue)

open LucasLehmer

theorem lucas_lehmer_sufficiency (p : ℕ) (w : 1 < p) : LucasLehmerTest p → (mersenne p).Prime := by
  let p' := p - 2
  -- ⊢ LucasLehmerTest p → Nat.Prime (mersenne p)
  have z : p = p' + 2 := (tsub_eq_iff_eq_add_of_le w.nat_succ_le).mp rfl
  -- ⊢ LucasLehmerTest p → Nat.Prime (mersenne p)
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succ rfl
  -- ⊢ LucasLehmerTest p → Nat.Prime (mersenne p)
  contrapose
  -- ⊢ ¬Nat.Prime (mersenne p) → ¬LucasLehmerTest p
  intro a t
  -- ⊢ False
  rw [z] at a
  -- ⊢ False
  rw [z] at t
  -- ⊢ False
  have h₁ := order_ineq p' t
  -- ⊢ False
  have h₂ := Nat.minFac_sq_le_self (mersenne_pos (Nat.lt_of_succ_lt w)) a
  -- ⊢ False
  have h := lt_of_lt_of_le h₁ h₂
  -- ⊢ False
  exact not_lt_of_ge (Nat.sub_le _ _) h
  -- 🎉 no goals
#align lucas_lehmer_sufficiency lucas_lehmer_sufficiency

namespace LucasLehmer

/-!
### `norm_num` extension

Next we define a `norm_num` extension that calculates `LucasLehmerTest p` for `1 < p`.
It makes use of a version of `sMod` that is specifically written to be reducible by the
Lean 4 kernel, which has the capability of efficiently reducing natural number expressions.
With this reduction in hand, it's a simple matter of applying the lemma
`LucasLehmer.residue_eq_zero_iff_sMod_eq_zero`.

See [Archive/Examples/MersennePrimes.lean] for certifications of all Mersenne primes
up through `mersenne 4423`.
-/

namespace norm_num_ext
open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/-- Version of `sMod` that is `ℕ`-valued. One should have `q = 2 ^ p - 1`.
This can be reduced by the kernel. -/
def sMod' (q : ℕ) : ℕ → ℕ
  | 0 => 4 % q
  | i + 1 => (sMod' q i ^ 2 + (q - 2)) % q

theorem sMod'_eq_sMod (p k : ℕ) (hp : 2 ≤ p) : (sMod' (2 ^ p - 1) k : ℤ) = sMod p k := by
  have h1 := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ p := Nat.pow_le_pow_of_le_right (by norm_num) hp
  have h2 : 1 ≤ 2 ^ p := by linarith
  -- ⊢ ↑(sMod' (2 ^ p - 1) k) = sMod p k
  induction k with
  | zero =>
    rw [sMod', sMod, Int.ofNat_emod]
    simp [h2]
  | succ k ih =>
    rw [sMod', sMod, ← ih]
    have h3 : 2 ≤ 2 ^ p - 1 := by
      zify [h2]
      calc
        (2 : Int) ≤ 4 - 1 := by norm_num
        _         ≤ 2 ^ p - 1 := by zify at h1; exact Int.sub_le_sub_right h1 _
    zify [h2, h3]
    rw [← add_sub_assoc, sub_eq_add_neg, add_assoc, add_comm _ (-2), ← add_assoc,
      Int.add_emod_self, ← sub_eq_add_neg]

lemma testTrueHelper (p : ℕ) (hp : Nat.blt 1 p = true) (h : sMod' (2 ^ p - 1) (p - 2) = 0) :
    LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  -- ⊢ LucasLehmerTest p
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sMod'_eq_sMod p _ hp, h]
  -- ⊢ ↑0 = 0
  rfl
  -- 🎉 no goals

lemma testFalseHelper (p : ℕ) (hp : Nat.blt 1 p = true)
    (h : Nat.ble 1 (sMod' (2 ^ p - 1) (p - 2))) : ¬ LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  -- ⊢ ¬LucasLehmerTest p
  rw [Nat.ble_eq, Nat.succ_le, Nat.pos_iff_ne_zero] at h
  -- ⊢ ¬LucasLehmerTest p
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sMod'_eq_sMod p _ hp]
  -- ⊢ ¬↑(sMod' (2 ^ p - 1) (p - 2)) = 0
  simpa using h
  -- 🎉 no goals

theorem isNat_lucasLehmerTest : {p np : ℕ} →
    IsNat p np → LucasLehmerTest np → LucasLehmerTest p
  | _, _, ⟨rfl⟩, h => h

theorem isNat_not_lucasLehmerTest : {p np : ℕ} →
    IsNat p np → ¬ LucasLehmerTest np → ¬ LucasLehmerTest p
  | _, _, ⟨rfl⟩, h => h

/-- Calculate `LucasLehmer.LucasLehmerTest p` for `2 ≤ p` by using kernel reduction for the
`sMod'` function. -/
@[norm_num LucasLehmer.LucasLehmerTest (_ : ℕ)]
def evalLucasLehmerTest : NormNumExt where eval {u α} e := do
  let .app _ (p : Q(ℕ)) ← Meta.whnfR e | failure
  let ⟨ep, hp⟩ ← deriveNat p _
  let np := ep.natLit!
  unless 1 < np do
    failure
  haveI' h1ltp : Nat.blt 1 $ep =Q true := ⟨⟩
  if sMod' (2 ^ np - 1) (np - 2) = 0 then
    haveI' hs : sMod' (2 ^ $ep - 1) ($ep - 2) =Q 0 := ⟨⟩
    have pf : Q(LucasLehmerTest $ep) := q(testTrueHelper $ep $h1ltp $hs)
    have pf' : Q(LucasLehmerTest $p) := q(isNat_lucasLehmerTest $hp $pf)
    return .isTrue pf'
  else
    haveI' hs : Nat.ble 1 (sMod' (2 ^ $ep - 1) ($ep - 2)) =Q true := ⟨⟩
    have pf : Q(¬ LucasLehmerTest $ep) := q(testFalseHelper $ep $h1ltp $hs)
    have pf' : Q(¬ LucasLehmerTest $p) := q(isNat_not_lucasLehmerTest $hp $pf)
    return .isFalse pf'

end norm_num_ext

end LucasLehmer

/-!
This implementation works successfully to prove `(2^4423 - 1).Prime`,
and all the Mersenne primes up to this point appear in [Archive/Examples/MersennePrimes.lean].
These can be calculated nearly instantly, and `(2^9689 - 1).Prime` only fails due to deep
recursion.

(Note by kmill: the following notes were for the Lean 3 version. They seem like they could still
be useful, so I'm leaving them here.)

There's still low hanging fruit available to do faster computations
based on the formula
```
n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]
```
and the fact that `% 2^p` and `/ 2^p` can be very efficient on the binary representation.
Someone should do this, too!
-/

theorem modEq_mersenne (n k : ℕ) : k ≡ k / 2 ^ n + k % 2 ^ n [MOD 2 ^ n - 1] :=
  -- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446
  calc
    k = 2 ^ n * (k / 2 ^ n) + k % 2 ^ n := (Nat.div_add_mod k (2 ^ n)).symm
    _ ≡ 1 * (k / 2 ^ n) + k % 2 ^ n [MOD 2 ^ n - 1] :=
      ((Nat.modEq_sub <| Nat.succ_le_of_lt <| pow_pos zero_lt_two _).mul_right _).add_right _
    _ = k / 2 ^ n + k % 2 ^ n := by rw [one_mul]
                                    -- 🎉 no goals
#align modeq_mersenne modEq_mersenne

-- It's hard to know what the limiting factor for large Mersenne primes would be.
-- In the purely computational world, I think it's the squaring operation in `s`.
