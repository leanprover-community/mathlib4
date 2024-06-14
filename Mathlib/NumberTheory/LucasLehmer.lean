/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison, Ainsley Pahljina
-/
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.Nat
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

theorem strictMono_mersenne : StrictMono mersenne := fun m n h ↦
  (Nat.sub_lt_sub_iff_right <| Nat.one_le_pow _ _ two_pos).2 <| by gcongr; norm_num1

@[simp]
theorem mersenne_lt_mersenne {p q : ℕ} : mersenne p < mersenne q ↔ p < q :=
  strictMono_mersenne.lt_iff_lt

@[gcongr] protected alias ⟨_, GCongr.mersenne_lt_mersenne⟩ := mersenne_lt_mersenne

@[simp]
theorem mersenne_le_mersenne {p q : ℕ} : mersenne p ≤ mersenne q ↔ p ≤ q :=
  strictMono_mersenne.le_iff_le

@[gcongr] protected alias ⟨_, GCongr.mersenne_le_mersenne⟩ := mersenne_le_mersenne

@[simp] theorem mersenne_zero : mersenne 0 = 0 := rfl

@[simp] theorem mersenne_pos {p : ℕ} : 0 < mersenne p ↔ 0 < p := mersenne_lt_mersenne (p := 0)
#align mersenne_pos mersenne_pos

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

alias ⟨_, mersenne_pos_of_pos⟩ := mersenne_pos

/-- Extension for the `positivity` tactic: `mersenne`. -/
@[positivity mersenne _]
def evalMersenne : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(mersenne $a) =>
    let ra ← core q(inferInstance) q(inferInstance) a
    assertInstancesCommute
    match ra with
    | .positive pa => pure (.positive q(mersenne_pos_of_pos $pa))
    | _ => pure (.nonnegative q(Nat.zero_le (mersenne $a)))
  | _, _, _ => throwError "not mersenne"

end Mathlib.Meta.Positivity

@[simp]
theorem one_lt_mersenne {p : ℕ} : 1 < mersenne p ↔ 1 < p :=
  mersenne_lt_mersenne (p := 1)

@[simp]
theorem succ_mersenne (k : ℕ) : mersenne k + 1 = 2 ^ k := by
  rw [mersenne, tsub_add_cancel_of_le]
  exact one_le_pow_of_one_le (by norm_num) k
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

theorem mersenne_int_pos {p : ℕ} (hp : p ≠ 0) : (0 : ℤ) < 2 ^ p - 1 :=
  sub_pos.2 <| mod_cast Nat.one_lt_two_pow hp

theorem mersenne_int_ne_zero (p : ℕ) (hp : p ≠ 0) : (2 ^ p - 1 : ℤ) ≠ 0 :=
  (mersenne_int_pos hp).ne'
#align lucas_lehmer.mersenne_int_ne_zero LucasLehmer.mersenne_int_ne_zero

theorem sMod_nonneg (p : ℕ) (hp : p ≠ 0) (i : ℕ) : 0 ≤ sMod p i := by
  cases i <;> dsimp [sMod]
  · exact sup_eq_right.mp rfl
  · apply Int.emod_nonneg
    exact mersenne_int_ne_zero p hp
#align lucas_lehmer.s_mod_nonneg LucasLehmer.sMod_nonneg

theorem sMod_mod (p i : ℕ) : sMod p i % (2 ^ p - 1) = sMod p i := by cases i <;> simp [sMod]
#align lucas_lehmer.s_mod_mod LucasLehmer.sMod_mod

theorem sMod_lt (p : ℕ) (hp : p ≠ 0) (i : ℕ) : sMod p i < 2 ^ p - 1 := by
  rw [← sMod_mod]
  refine (Int.emod_lt _ (mersenne_int_ne_zero p hp)).trans_eq ?_
  exact abs_of_nonneg (mersenne_int_pos hp).le
#align lucas_lehmer.s_mod_lt LucasLehmer.sMod_lt

theorem sZMod_eq_s (p' : ℕ) (i : ℕ) : sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' + 2) - 1)) := by
  induction' i with i ih
  · dsimp [s, sZMod]
    norm_num
  · push_cast [s, sZMod, ih]; rfl
#align lucas_lehmer.s_zmod_eq_s LucasLehmer.sZMod_eq_s

-- These next two don't make good `norm_cast` lemmas.
theorem Int.natCast_pow_pred (b p : ℕ) (w : 0 < b) : ((b ^ p - 1 : ℕ) : ℤ) = (b : ℤ) ^ p - 1 := by
  have : 1 ≤ b ^ p := Nat.one_le_pow p b w
  norm_cast
#align lucas_lehmer.int.coe_nat_pow_pred LucasLehmer.Int.natCast_pow_pred

@[deprecated (since := "2024-05-25")] alias Int.coe_nat_pow_pred := Int.natCast_pow_pred

theorem Int.coe_nat_two_pow_pred (p : ℕ) : ((2 ^ p - 1 : ℕ) : ℤ) = (2 ^ p - 1 : ℤ) :=
  Int.natCast_pow_pred 2 p (by decide)
#align lucas_lehmer.int.coe_nat_two_pow_pred LucasLehmer.Int.coe_nat_two_pow_pred

theorem sZMod_eq_sMod (p : ℕ) (i : ℕ) : sZMod p i = (sMod p i : ZMod (2 ^ p - 1)) := by
  induction i <;> push_cast [← Int.coe_nat_two_pow_pred p, sMod, sZMod, *] <;> rfl
#align lucas_lehmer.s_zmod_eq_s_mod LucasLehmer.sZMod_eq_sMod

/-- The Lucas-Lehmer residue is `s p (p-2)` in `ZMod (2^p - 1)`. -/
def lucasLehmerResidue (p : ℕ) : ZMod (2 ^ p - 1) :=
  sZMod p (p - 2)
#align lucas_lehmer.lucas_lehmer_residue LucasLehmer.lucasLehmerResidue

theorem residue_eq_zero_iff_sMod_eq_zero (p : ℕ) (w : 1 < p) :
    lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0 := by
  dsimp [lucasLehmerResidue]
  rw [sZMod_eq_sMod p]
  constructor
  · -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h
    simp? [ZMod.intCast_zmod_eq_zero_iff_dvd] at h says
      simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, gt_iff_lt, ofNat_pos, pow_pos, cast_pred,
        cast_pow, cast_ofNat] at h
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _ h <;> clear h
    · exact sMod_nonneg _ (by positivity) _
    · exact sMod_lt _ (by positivity) _
  · intro h
    rw [h]
    simp
#align lucas_lehmer.residue_eq_zero_iff_s_mod_eq_zero LucasLehmer.residue_eq_zero_iff_sMod_eq_zero

/-- **Lucas-Lehmer Test**: a Mersenne number `2^p-1` is prime if and only if
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
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp }

instance : NatCast (X q) where
    natCast := fun n => ⟨n, 0⟩

@[simp] theorem fst_natCast (n : ℕ) : (n : X q).fst = (n : ZMod q) := rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.nat_coe_fst LucasLehmer.X.fst_natCast

@[simp] theorem snd_natCast (n : ℕ) : (n : X q).snd = (0 : ZMod q) := rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.nat_coe_snd LucasLehmer.X.snd_natCast

-- See note [no_index around OfNat.ofNat]
@[simp] theorem ofNat_fst (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : X q).fst = OfNat.ofNat n :=
  rfl

-- See note [no_index around OfNat.ofNat]
@[simp] theorem ofNat_snd (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : X q).snd = 0 :=
  rfl

instance : AddGroupWithOne (X q) :=
  { inferInstanceAs (Monoid (X q)), inferInstanceAs (AddCommGroup (X q)),
      inferInstanceAs (NatCast (X q)) with
    natCast_zero := by ext <;> simp
    natCast_succ := fun _ ↦ by ext <;> simp
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun n => by ext <;> simp
    intCast_negSucc := fun n => by ext <;> simp }

theorem left_distrib (x y z : X q) : x * (y + z) = x * y + x * z := by
  ext <;> dsimp <;> ring
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.left_distrib LucasLehmer.X.left_distrib

theorem right_distrib (x y z : X q) : (x + y) * z = x * z + y * z := by
  ext <;> dsimp <;> ring
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.right_distrib LucasLehmer.X.right_distrib

instance : Ring (X q) :=
  { inferInstanceAs (AddGroupWithOne (X q)), inferInstanceAs (AddCommGroup (X q)),
      inferInstanceAs (Monoid (X q)) with
    left_distrib := left_distrib
    right_distrib := right_distrib
    mul_zero := fun _ ↦ by ext <;> simp
    zero_mul := fun _ ↦ by ext <;> simp }

instance : CommRing (X q) :=
  { inferInstanceAs (Ring (X q)) with
    mul_comm := fun _ _ ↦ by ext <;> dsimp <;> ring }

instance [Fact (1 < (q : ℕ))] : Nontrivial (X q) :=
  ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

@[simp]
theorem fst_intCast (n : ℤ) : (n : X q).fst = (n : ZMod q) :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.int_coe_fst LucasLehmer.X.fst_intCast

@[simp]
theorem snd_intCast (n : ℤ) : (n : X q).snd = (0 : ZMod q) :=
  rfl
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.int_coe_snd LucasLehmer.X.snd_intCast

@[deprecated (since := "2024-05-25")] alias nat_coe_fst := fst_natCast
@[deprecated (since := "2024-05-25")] alias nat_coe_snd := snd_natCast
@[deprecated (since := "2024-05-25")] alias int_coe_fst := fst_intCast
@[deprecated (since := "2024-05-25")] alias int_coe_snd := snd_intCast

@[norm_cast]
theorem coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) := by ext <;> simp
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.coe_mul LucasLehmer.X.coe_mul

@[norm_cast]
theorem coe_natCast (n : ℕ) : ((n : ℤ) : X q) = (n : X q) := by ext <;> simp
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.coe_nat LucasLehmer.X.coe_natCast

@[deprecated (since := "2024-04-05")] alias coe_nat := coe_natCast

/-- The cardinality of `X` is `q^2`. -/
theorem card_eq : Fintype.card (X q) = q ^ 2 := by
  dsimp [X]
  rw [Fintype.card_prod, ZMod.card q, sq]
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.X_card LucasLehmer.X.card_eq

/-- There are strictly fewer than `q^2` units, since `0` is not a unit. -/
nonrec theorem card_units_lt (w : 1 < q) : Fintype.card (X q)ˣ < q ^ 2 := by
  have : Fact (1 < (q : ℕ)) := ⟨w⟩
  convert card_units_lt (X q)
  rw [card_eq]
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
  ext <;> simp; ring
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.ω_mul_ωb LucasLehmer.X.ω_mul_ωb

theorem ωb_mul_ω (q : ℕ+) : (ωb : X q) * ω = 1 := by
  rw [mul_comm, ω_mul_ωb]
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.ωb_mul_ω LucasLehmer.X.ωb_mul_ω

/-- A closed form for the recurrence relation. -/
theorem closed_form (i : ℕ) : (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i := by
  induction' i with i ih
  · dsimp [s, ω, ωb]
    ext <;> norm_num
  · calc
      (s (i + 1) : X q) = (s i ^ 2 - 2 : ℤ) := rfl
      _ = (s i : X q) ^ 2 - 2 := by push_cast; rfl
      _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by rw [ih]
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 + 2 * (ωb ^ 2 ^ i * ω ^ 2 ^ i) - 2 := by ring
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 := by
        rw [← mul_pow ωb ω, ωb_mul_ω, one_pow, mul_one, add_sub_cancel_right]
      _ = ω ^ 2 ^ (i + 1) + ωb ^ 2 ^ (i + 1) := by rw [← pow_mul, ← pow_mul, _root_.pow_succ]
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.X.closed_form LucasLehmer.X.closed_form

end X

open X

/-!
Here and below, we introduce `p' = p - 2`, in order to avoid using subtraction in `ℕ`.
-/

/-- If `1 < p`, then `q p`, the smallest prime factor of `mersenne p`, is more than 2. -/
theorem two_lt_q (p' : ℕ) : 2 < q (p' + 2) := by
  refine (minFac_prime (one_lt_mersenne.2 ?_).ne').two_le.lt_of_ne' ?_
  · exact le_add_left _ _
  · rw [Ne, minFac_eq_two_iff, mersenne, Nat.pow_succ']
    exact Nat.two_not_dvd_two_mul_sub_one Nat.one_le_two_pow
#align lucas_lehmer.two_lt_q LucasLehmer.two_lt_q

theorem ω_pow_formula (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    ∃ k : ℤ,
      (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) =
        k * mersenne (p' + 2) * (ω : X (q (p' + 2))) ^ 2 ^ p' - 1 := by
  dsimp [lucasLehmerResidue] at h
  rw [sZMod_eq_s p'] at h
  simp? [ZMod.intCast_zmod_eq_zero_iff_dvd] at h says
    simp only [add_tsub_cancel_right, ZMod.intCast_zmod_eq_zero_iff_dvd, gt_iff_lt, ofNat_pos,
      pow_pos, cast_pred, cast_pow, cast_ofNat] at h
  cases' h with k h
  use k
  replace h := congr_arg (fun n : ℤ => (n : X (q (p' + 2)))) h
  -- coercion from ℤ to X q
  dsimp at h
  rw [closed_form] at h
  replace h := congr_arg (fun x => ω ^ 2 ^ p' * x) h
  dsimp at h
  have t : 2 ^ p' + 2 ^ p' = 2 ^ (p' + 1) := by ring
  rw [mul_add, ← pow_add ω, t, ← mul_pow ω ωb (2 ^ p'), ω_mul_ωb, one_pow] at h
  rw [mul_comm, coe_mul] at h
  rw [mul_comm _ (k : X (q (p' + 2)))] at h
  replace h := eq_sub_of_add_eq h
  have : 1 ≤ 2 ^ (p' + 2) := Nat.one_le_pow _ _ (by decide)
  exact mod_cast h
#align lucas_lehmer.ω_pow_formula LucasLehmer.ω_pow_formula

/-- `q` is the minimum factor of `mersenne p`, so `M p = 0` in `X q`. -/
theorem mersenne_coe_X (p : ℕ) : (mersenne p : X (q p)) = 0 := by
  ext <;> simp [mersenne, q, ZMod.natCast_zmod_eq_zero_iff_dvd, -pow_pos]
  apply Nat.minFac_dvd
set_option linter.uppercaseLean3 false in
#align lucas_lehmer.mersenne_coe_X LucasLehmer.mersenne_coe_X

theorem ω_pow_eq_neg_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) = -1 := by
  cases' ω_pow_formula p' h with k w
  rw [mersenne_coe_X] at w
  simpa using w
#align lucas_lehmer.ω_pow_eq_neg_one LucasLehmer.ω_pow_eq_neg_one

theorem ω_pow_eq_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = 1 :=
  calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul, ← Nat.pow_succ]
    _ = (-1) ^ 2 := by rw [ω_pow_eq_neg_one p' h]
    _ = 1 := by simp
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
  · intro o
    have ω_pow := orderOf_dvd_iff_pow_eq_one.1 o
    replace ω_pow :=
      congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) → X (q (p' + 2))) ω_pow
    simp? at ω_pow says simp only [map_pow, Units.coeHom_apply, ωUnit_coe, map_one] at ω_pow
    have h : (1 : ZMod (q (p' + 2))) = -1 :=
      congr_arg Prod.fst (ω_pow.symm.trans (ω_pow_eq_neg_one p' h))
    haveI : Fact (2 < (q (p' + 2) : ℕ)) := ⟨two_lt_q _⟩
    apply ZMod.neg_one_ne_one h.symm
  · apply orderOf_dvd_iff_pow_eq_one.2
    apply Units.ext
    push_cast
    exact ω_pow_eq_one p' h
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
  have z : p = p' + 2 := (tsub_eq_iff_eq_add_of_le w.nat_succ_le).mp rfl
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succ rfl
  contrapose
  intro a t
  rw [z] at a
  rw [z] at t
  have h₁ := order_ineq p' t
  have h₂ := Nat.minFac_sq_le_self (mersenne_pos.2 (Nat.lt_of_succ_lt w)) a
  have h := lt_of_lt_of_le h₁ h₂
  exact not_lt_of_ge (Nat.sub_le _ _) h
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
  have h2 : 1 ≤ 2 ^ p := by omega
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
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sMod'_eq_sMod p _ hp, h]
  rfl

lemma testFalseHelper (p : ℕ) (hp : Nat.blt 1 p = true)
    (h : Nat.ble 1 (sMod' (2 ^ p - 1) (p - 2))) : ¬ LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [Nat.ble_eq, Nat.succ_le, Nat.pos_iff_ne_zero] at h
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sMod'_eq_sMod p _ hp]
  simpa using h

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
#align modeq_mersenne modEq_mersenne

-- It's hard to know what the limiting factor for large Mersenne primes would be.
-- In the purely computational world, I think it's the squaring operation in `s`.
