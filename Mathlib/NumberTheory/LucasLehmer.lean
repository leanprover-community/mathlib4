/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Alastair Irving, Kim Morrison, Ainsley Pahljina
-/
import Mathlib.NumberTheory.Fermat
import Mathlib.RingTheory.Fintype

/-!
# The Lucas-Lehmer test for Mersenne primes

We define `lucasLehmerResidue : Π p : ℕ, ZMod (2^p - 1)`, and
prove `lucasLehmerResidue p = 0 ↔ Prime (mersenne p)`.

We construct a `norm_num` extension to calculate this residue to certify primality of Mersenne
primes using `lucas_lehmer_sufficiency`.


## TODO

- Speed up the calculations using `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]`.
- Find some bigger primes!

## History

This development began as a student project by Ainsley Pahljina,
and was then cleaned up for mathlib by Kim Morrison.
The tactic for certified computation of Lucas-Lehmer residues was provided by Mario Carneiro.
This tactic was ported by Thomas Murrills to Lean 4, and then it was converted to a `norm_num`
extension and made to use kernel reductions by Kyle Miller.
-/

/-- The Mersenne numbers, 2^p - 1. -/
def mersenne (p : ℕ) : ℕ :=
  2 ^ p - 1

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

@[simp] lemma mersenne_odd : ∀ {p : ℕ}, Odd (mersenne p) ↔ p ≠ 0
  | 0 => by simp
  | p + 1 => by
    simpa using Nat.Even.sub_odd (one_le_pow₀ one_le_two)
      (even_two.pow_of_ne_zero p.succ_ne_zero) odd_one

@[simp] theorem mersenne_pos {p : ℕ} : 0 < mersenne p ↔ 0 < p := mersenne_lt_mersenne (p := 0)

lemma mersenne_succ (n : ℕ) : mersenne (n + 1) = 2 * mersenne n + 1 := by
  dsimp [mersenne]
  have := Nat.one_le_pow n 2 two_pos
  omega

/-- If `2 ^ p - 1` is prime, then `p` is prime. -/
lemma Nat.Prime.of_mersenne {p : ℕ} (h : (mersenne p).Prime) : Nat.Prime p := by
  apply Nat.prime_of_pow_sub_one_prime _ h |>.2
  rintro rfl
  apply Nat.not_prime_one h

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
  exact one_le_pow₀ (by simp)

lemma mersenne_mod_four {n : ℕ} (h : 2 ≤ n) : mersenne n % 4 = 3 := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; omega

lemma mersenne_mod_three {n : ℕ} (odd : Odd n) (h : 3 ≤ n) : mersenne n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := odd
  replace h : 1 ≤ k := by omega
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ j _ _ =>
    rw [mersenne_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by omega, mersenne_succ]
    omega

lemma mersenne_mod_eight {n : ℕ} (h : 3 ≤ n) : mersenne n % 8 = 7 := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ _ _ _ => rw [mersenne_succ]; omega

/-- If `2^p - 1` is prime then 2 is a square mod `2^p - 1`. -/
lemma legendreSym_mersenne_two {p : ℕ} [Fact (mersenne p).Prime] (hp : 3 ≤ p) :
    legendreSym (mersenne p) 2 = 1 := by
  have := mersenne_mod_eight hp
  rw [legendreSym.at_two (by omega), ZMod.χ₈_nat_eq_if_mod_eight]
  omega

/-- If `2^p - 1` is prime then 3 is not a square mod `2^p - 1`. -/
lemma legendreSym_mersenne_three {p : ℕ} [Fact (mersenne p).Prime] (hp : 3 ≤ p) (odd : Odd p) :
    legendreSym (mersenne p) 3 = -1 := by
  rw [(by rfl : (3 : ℤ) = (3 : ℕ)), legendreSym.quadratic_reciprocity_three_mod_four (by norm_num)
    (mersenne_mod_four (by omega)),
    legendreSym.mod]
  rw_mod_cast [mersenne_mod_three odd hp]
  simp

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

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `ZMod (2^p - 1)`. -/
def sZMod (p : ℕ) : ℕ → ZMod (2 ^ p - 1)
  | 0 => 4
  | i + 1 => sZMod p i ^ 2 - 2

/-- The recurrence `s (i+1) = ((s i)^2 - 2) % (2^p - 1)` in `ℤ`. -/
def sMod (p : ℕ) : ℕ → ℤ
  | 0 => 4 % (2 ^ p - 1)
  | i + 1 => (sMod p i ^ 2 - 2) % (2 ^ p - 1)

theorem mersenne_int_pos {p : ℕ} (hp : p ≠ 0) : (0 : ℤ) < 2 ^ p - 1 :=
  sub_pos.2 <| mod_cast Nat.one_lt_two_pow hp

theorem mersenne_int_ne_zero (p : ℕ) (hp : p ≠ 0) : (2 ^ p - 1 : ℤ) ≠ 0 :=
  (mersenne_int_pos hp).ne'

theorem sMod_nonneg (p : ℕ) (hp : p ≠ 0) (i : ℕ) : 0 ≤ sMod p i := by
  cases i <;> dsimp [sMod]
  · exact sup_eq_right.mp rfl
  · apply Int.emod_nonneg
    exact mersenne_int_ne_zero p hp

theorem sMod_mod (p i : ℕ) : sMod p i % (2 ^ p - 1) = sMod p i := by cases i <;> simp [sMod]

theorem sMod_lt (p : ℕ) (hp : p ≠ 0) (i : ℕ) : sMod p i < 2 ^ p - 1 := by
  rw [← sMod_mod]
  refine (Int.emod_lt_abs _ (mersenne_int_ne_zero p hp)).trans_eq ?_
  exact abs_of_nonneg (mersenne_int_pos hp).le

theorem sZMod_eq_s (p' : ℕ) (i : ℕ) : sZMod (p' + 2) i = (s i : ZMod (2 ^ (p' + 2) - 1)) := by
  induction i with
  | zero => dsimp [s, sZMod]; simp
  | succ i ih => push_cast [s, sZMod, ih]; rfl

-- These next two don't make good `norm_cast` lemmas.
theorem Int.natCast_pow_pred (b p : ℕ) (w : 0 < b) : ((b ^ p - 1 : ℕ) : ℤ) = (b : ℤ) ^ p - 1 := by
  have : 1 ≤ b ^ p := Nat.one_le_pow p b w
  norm_cast

theorem Int.coe_nat_two_pow_pred (p : ℕ) : ((2 ^ p - 1 : ℕ) : ℤ) = (2 ^ p - 1 : ℤ) :=
  Int.natCast_pow_pred 2 p (by decide)

theorem sZMod_eq_sMod (p : ℕ) (i : ℕ) : sZMod p i = (sMod p i : ZMod (2 ^ p - 1)) := by
  induction i <;> push_cast [← Int.coe_nat_two_pow_pred p, sMod, sZMod, *] <;> rfl

/-- The Lucas-Lehmer residue is `s p (p-2)` in `ZMod (2^p - 1)`. -/
def lucasLehmerResidue (p : ℕ) : ZMod (2 ^ p - 1) :=
  sZMod p (p - 2)

theorem residue_eq_zero_iff_sMod_eq_zero (p : ℕ) (w : 1 < p) :
    lucasLehmerResidue p = 0 ↔ sMod p (p - 2) = 0 := by
  dsimp [lucasLehmerResidue]
  rw [sZMod_eq_sMod p]
  constructor
  · -- We want to use that fact that `0 ≤ s_mod p (p-2) < 2^p - 1`
    -- and `lucas_lehmer_residue p = 0 → 2^p - 1 ∣ s_mod p (p-2)`.
    intro h
    apply Int.eq_zero_of_dvd_of_nonneg_of_lt _ _
      (by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h) <;> clear h
    · exact sMod_nonneg _ (by positivity) _
    · exact sMod_lt _ (by positivity) _
  · intro h
    rw [h]
    simp

/-- **Lucas-Lehmer Test**: a Mersenne number `2^p-1` is prime if and only if
the Lucas-Lehmer residue `s p (p-2) % (2^p - 1)` is zero.
-/
def LucasLehmerTest (p : ℕ) : Prop :=
  lucasLehmerResidue p = 0

/-- `q` is defined as the minimum factor of `mersenne p`, bundled as an `ℕ+`. -/
def q (p : ℕ) : ℕ+ :=
  ⟨Nat.minFac (mersenne p), Nat.minFac_pos (mersenne p)⟩

-- It would be nice to define this as (ℤ/qℤ)[x] / (x^2 - 3),
-- obtaining the ring structure for free,
-- but that seems to be more trouble than it's worth;
-- if it were easy to make the definition,
-- cardinality calculations would be somewhat more involved, too.
/-- We construct the ring `X q` as ℤ/qℤ + √3 ℤ/qℤ. -/
def X (q : ℕ) : Type :=
  ZMod q × ZMod q

namespace X

variable {q : ℕ}

instance : Inhabited (X q) := inferInstanceAs (Inhabited (ZMod q × ZMod q))
instance : DecidableEq (X q) := inferInstanceAs (DecidableEq (ZMod q × ZMod q))
instance : AddCommGroup (X q) := inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

@[ext]
theorem ext {x y : X q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x; cases y; congr

@[simp] theorem zero_fst : (0 : X q).1 = 0 := rfl
@[simp] theorem zero_snd : (0 : X q).2 = 0 := rfl

@[simp]
theorem add_fst (x y : X q) : (x + y).1 = x.1 + y.1 :=
  rfl

@[simp]
theorem add_snd (x y : X q) : (x + y).2 = x.2 + y.2 :=
  rfl

@[simp]
theorem neg_fst (x : X q) : (-x).1 = -x.1 :=
  rfl

@[simp]
theorem neg_snd (x : X q) : (-x).2 = -x.2 :=
  rfl

instance : Mul (X q) where mul x y := (x.1 * y.1 + 3 * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp]
theorem mul_fst (x y : X q) : (x * y).1 = x.1 * y.1 + 3 * x.2 * y.2 :=
  rfl

@[simp]
theorem mul_snd (x y : X q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 :=
  rfl

instance : One (X q) where one := ⟨1, 0⟩

@[simp]
theorem one_fst : (1 : X q).1 = 1 :=
  rfl

@[simp]
theorem one_snd : (1 : X q).2 = 0 :=
  rfl

instance : Monoid (X q) :=
  { inferInstanceAs (Mul (X q)), inferInstanceAs (One (X q)) with
    mul_assoc := fun x y z => by ext <;> dsimp <;> ring
    one_mul := fun x => by ext <;> simp
    mul_one := fun x => by ext <;> simp }

instance : NatCast (X q) where
    natCast := fun n => ⟨n, 0⟩

@[simp] theorem fst_natCast (n : ℕ) : (n : X q).fst = (n : ZMod q) := rfl

@[simp] theorem snd_natCast (n : ℕ) : (n : X q).snd = (0 : ZMod q) := rfl

@[simp] theorem ofNat_fst (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : X q).fst = OfNat.ofNat n :=
  rfl

@[simp] theorem ofNat_snd (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : X q).snd = 0 :=
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

theorem right_distrib (x y z : X q) : (x + y) * z = x * z + y * z := by
  ext <;> dsimp <;> ring

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

@[simp]
theorem snd_intCast (n : ℤ) : (n : X q).snd = (0 : ZMod q) :=
  rfl

@[norm_cast]
theorem coe_mul (n m : ℤ) : ((n * m : ℤ) : X q) = (n : X q) * (m : X q) := by ext <;> simp

@[norm_cast]
theorem coe_natCast (n : ℕ) : ((n : ℤ) : X q) = (n : X q) := by ext <;> simp

/-- We define `ω = 2 + √3`. -/
def ω : X q := (2, 1)

/-- We define `ωb = 2 - √3`, which is the inverse of `ω`. -/
def ωb : X q := (2, -1)

theorem ω_mul_ωb : (ω : X q) * ωb = 1 := by
  dsimp [ω, ωb]
  ext <;> simp; ring

theorem ωb_mul_ω : (ωb : X q) * ω = 1 := by
  rw [mul_comm, ω_mul_ωb]

/-- A closed form for the recurrence relation. -/
theorem closed_form (i : ℕ) : (s i : X q) = (ω : X q) ^ 2 ^ i + (ωb : X q) ^ 2 ^ i := by
  induction i with
  | zero =>
    dsimp [s, ω, ωb]
    ext <;> norm_num
  | succ i ih =>
    calc
      (s (i + 1) : X q) = (s i ^ 2 - 2 : ℤ) := rfl
      _ = (s i : X q) ^ 2 - 2 := by push_cast; rfl
      _ = (ω ^ 2 ^ i + ωb ^ 2 ^ i) ^ 2 - 2 := by rw [ih]
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 + 2 * (ωb ^ 2 ^ i * ω ^ 2 ^ i) - 2 := by ring
      _ = (ω ^ 2 ^ i) ^ 2 + (ωb ^ 2 ^ i) ^ 2 := by
        rw [← mul_pow ωb ω, ωb_mul_ω, one_pow, mul_one, add_sub_cancel_right]
      _ = ω ^ 2 ^ (i + 1) + ωb ^ 2 ^ (i + 1) := by rw [← pow_mul, ← pow_mul, _root_.pow_succ]

/-- We define `α = √3`. -/
def α : X q := (0, 1)

@[simp] lemma α_sq : (α ^ 2 : X q) = 3 := by
  ext <;> simp [α, sq]

@[simp] lemma one_add_α_sq : ((1 + α) ^ 2 : X q) = 2 * ω := by
  ext <;> simpa [α, ω, sq] using by norm_num

lemma α_pow (i : ℕ) : (α : X q) ^ (2 * i + 1) = 3 ^ i * α := by
  rw [pow_succ, pow_mul, α_sq]

/-! We show that `X q` has characteristic `q`, so that we can apply the binomial theorem. -/

instance : CharP (X q) q where
  cast_eq_zero_iff x := by
    convert ZMod.natCast_eq_zero_iff _ _
    exact ⟨congr_arg Prod.fst, fun hx ↦ ext hx (by simp)⟩

instance : Coe (ZMod ↑q) (X q) where
  coe := ZMod.castHom dvd_rfl (X q)

/-- If `3` is not a square mod `q` then `(1 + α) ^ q = 1 - α` -/
lemma one_add_α_pow_q [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (1 + α : X q) ^ q = 1 - α := by
  obtain ⟨k, rfl⟩ := odd
  let q := 2 * k + 1
  have : (3 ^ k : ZMod q) = -1 := by
    simpa [leg3, mul_add_div, eq_comm] using legendreSym.eq_pow (2 * k + 1) 3
  rw [add_pow_expChar, α_pow, show (3 : X q) = (3 : ZMod q) by rw [map_ofNat], ← map_pow, this,
    map_neg]
  simp [sub_eq_add_neg]

/-- If `3` is not a square then `(1 + α) ^ (q + 1) = -2`. -/
lemma one_add_α_pow_q_succ [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (1 + α : X q) ^ (q + 1) = -2 := by
  rw [pow_succ, one_add_α_pow_q odd leg3, mul_comm, ← _root_.sq_sub_sq, α_sq]
  norm_num

/-- If `3` is not a square then `(2 * ω) ^ ((q + 1) / 2) = -2`. -/
lemma two_mul_ω_pow [Fact q.Prime] (odd : Odd q) (leg3 : legendreSym q 3 = -1) :
    (2 * ω : X q) ^ ((q + 1) / 2) = -2 := by
  rw [← one_add_α_sq, ← pow_mul]
  have : 2 * ((q + 1) / 2) = q + 1 := by
    apply Nat.mul_div_cancel'
    rw [← even_iff_two_dvd]
    exact Odd.add_one odd
  rw [this, one_add_α_pow_q_succ odd leg3]

/-- If 3 is not a square and 2 is square then $\omega^{(q+1)/2}=-1$. -/
lemma pow_ω [Fact q.Prime] (odd : Odd q)
    (leg3 : legendreSym q 3 = -1)
    (leg2 : legendreSym q 2 = 1) :
    (ω : X q) ^ ((q + 1) / 2) = -1 := by
  have pow2 : (2 : ZMod q) ^ ((q + 1) / 2) = 2 := by
    obtain ⟨_, _⟩ := odd
    rw [(by omega : (q + 1) / 2 = q / 2 + 1), pow_succ]
    have leg := legendreSym.eq_pow q 2
    have : (2 : ZMod q) = ((2 : ℤ) : ZMod q) := by norm_cast
    rw [this, ← leg, leg2]
    ring
  have := two_mul_ω_pow odd leg3
  rw [mul_pow] at this
  have coe : (2 : X q) = (2 : ZMod q) := by rw [map_ofNat]
  rw [coe, ← RingHom.map_pow, pow2, ← coe,
    (by ring : (-2 : X q) = 2 * -1)] at this
  refine (isUnit_of_mul_eq_one (2 : X q) ((q + 1) / 2 : ℕ) ?_).mul_left_cancel this
  norm_cast
  simp [Nat.mul_div_cancel' odd.add_one.two_dvd]

/-- The final evaluation needed to establish the Lucas-Lehmer necessity. -/
lemma ω_pow_trace [Fact q.Prime] (odd : Odd q)
    (leg3 : legendreSym q 3 = -1)
    (leg2 : legendreSym q 2 = 1)
    (hq4 : 4 ∣ q + 1) :
    (ω : X q) ^ ((q + 1) / 4) + ωb ^ ((q + 1) / 4) = 0 := by
  have : (ω : X q) ^ ((q + 1) / 2) * ωb ^ ((q + 1) / 4) = -ωb ^ ((q + 1) / 4) := by
    rw [pow_ω odd leg3 leg2]
    ring
  have div4 : (q + 1) / 2 = (q + 1) / 4 + (q + 1) / 4 := by rcases hq4 with ⟨k, hk⟩; omega
  rw [div4, pow_add, mul_assoc, ← mul_pow, ω_mul_ωb, one_pow, mul_one] at this
  rw [this]
  ring

variable [NeZero q]

instance : Fintype (X q) := inferInstanceAs (Fintype (ZMod q × ZMod q))

/-- The cardinality of `X` is `q^2`. -/
theorem card_eq : Fintype.card (X q) = q ^ 2 := by
  dsimp [X]
  rw [Fintype.card_prod, ZMod.card q, sq]

/-- There are strictly fewer than `q^2` units, since `0` is not a unit. -/
nonrec theorem card_units_lt (w : 1 < q) : Fintype.card (X q)ˣ < q ^ 2 := by
  have : Fact (1 < (q : ℕ)) := ⟨w⟩
  convert card_units_lt (X q)
  rw [card_eq]

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

theorem ω_pow_formula (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    ∃ k : ℤ,
      (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) =
        k * mersenne (p' + 2) * (ω : X (q (p' + 2))) ^ 2 ^ p' - 1 := by
  dsimp [lucasLehmerResidue] at h
  rw [sZMod_eq_s p'] at h
  replace h : 2 ^ (p' + 2) - 1 ∣ s p' := by simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h
  obtain ⟨k, h⟩ := h
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

/-- `q` is the minimum factor of `mersenne p`, so `M p = 0` in `X q`. -/
theorem mersenne_coe_X (p : ℕ) : (mersenne p : X (q p)) = 0 := by
  ext <;> simp [mersenne, q, ZMod.natCast_eq_zero_iff, -pow_pos]
  apply Nat.minFac_dvd

theorem ω_pow_eq_neg_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 1) = -1 := by
  obtain ⟨k, w⟩ := ω_pow_formula p' h
  rw [mersenne_coe_X] at w
  simpa using w

theorem ω_pow_eq_one (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = 1 :=
  calc
    (ω : X (q (p' + 2))) ^ 2 ^ (p' + 2) = (ω ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul, ← Nat.pow_succ]
    _ = (-1) ^ 2 := by rw [ω_pow_eq_neg_one p' h]
    _ = 1 := by simp

/-- `ω` as an element of the group of units. -/
def ωUnit (p : ℕ) : Units (X (q p)) where
  val := ω
  inv := ωb
  val_inv := ω_mul_ωb
  inv_val := ωb_mul_ω

@[simp]
theorem ωUnit_coe (p : ℕ) : (ωUnit p : X (q p)) = ω :=
  rfl

/-- The order of `ω` in the unit group is exactly `2^p`. -/
theorem order_ω (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    orderOf (ωUnit (p' + 2)) = 2 ^ (p' + 2) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  -- the order of ω divides 2^p
  · exact Nat.prime_two
  · intro o
    have ω_pow :=
      congr_arg (Units.coeHom (X (q (p' + 2))) : Units (X (q (p' + 2))) → X (q (p' + 2))) <|
        orderOf_dvd_iff_pow_eq_one.1 o
    have h : (1 : ZMod (q (p' + 2))) = -1 :=
      congr_arg Prod.fst (ω_pow.symm.trans (ω_pow_eq_neg_one p' h))
    haveI : Fact (2 < (q (p' + 2) : ℕ)) := ⟨two_lt_q _⟩
    apply ZMod.neg_one_ne_one h.symm
  · apply orderOf_dvd_iff_pow_eq_one.2
    apply Units.ext
    push_cast
    exact ω_pow_eq_one p' h

theorem order_ineq (p' : ℕ) (h : lucasLehmerResidue (p' + 2) = 0) :
    2 ^ (p' + 2) < (q (p' + 2) : ℕ) ^ 2 :=
  calc
    2 ^ (p' + 2) = orderOf (ωUnit (p' + 2)) := (order_ω p' h).symm
    _ ≤ Fintype.card (X (q (p' + 2)))ˣ := orderOf_le_card_univ
    _ < q (p' + 2) ^ 2 := card_units_lt (Nat.lt_of_succ_lt (two_lt_q _))

end LucasLehmer

export LucasLehmer (LucasLehmerTest lucasLehmerResidue)

open LucasLehmer

theorem lucas_lehmer_sufficiency (p : ℕ) (w : 1 < p) : LucasLehmerTest p → (mersenne p).Prime := by
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by omega
  have w : 1 < p' + 2 := Nat.lt_of_sub_eq_succ rfl
  contrapose
  intro a t
  have h₁ := order_ineq p' t
  have h₂ := Nat.minFac_sq_le_self (mersenne_pos.2 (Nat.lt_of_succ_lt w)) a
  have h := lt_of_lt_of_le h₁ h₂
  exact not_lt_of_ge (Nat.sub_le _ _) h

/-- If `2^p-1` is prime then the Lucas-Lehmer test holds, `s(p-2) % (2^p-1) = 0. -/
theorem lucas_lehmer_necessity (p : ℕ) (w : 3 ≤ p) (hp : (mersenne p).Prime) :
    LucasLehmerTest p := by
  have : Fact (mersenne p).Prime := ⟨‹_›⟩
  set p' := p - 2 with hp'
  clear_value p'
  obtain rfl : p = p' + 2 := by omega
  dsimp [LucasLehmerTest, lucasLehmerResidue]
  rw [sZMod_eq_s p', ← X.fst_intCast, X.closed_form, add_tsub_cancel_right]
  have := X.ω_pow_trace (q := mersenne (p' + 2)) (by simp)
    (legendreSym_mersenne_three w <| hp.of_mersenne.odd_of_ne_two (by omega))
    (legendreSym_mersenne_two w) (by simp [pow_add])
  rw [succ_mersenne, pow_add, show 2 ^ 2 = 4 by norm_num, mul_div_cancel_right₀ _ (by norm_num)]
    at this
  simp [this]

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
def sModNat (q : ℕ) : ℕ → ℕ
  | 0 => 4 % q
  | i + 1 => (sModNat q i ^ 2 + (q - 2)) % q

theorem sModNat_eq_sMod (p k : ℕ) (hp : 2 ≤ p) : (sModNat (2 ^ p - 1) k : ℤ) = sMod p k := by
  have h1 := calc
    4 = 2 ^ 2 := by simp
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by simp) hp
  have h2 : 1 ≤ 2 ^ p := by omega
  induction k with
  | zero =>
    rw [sModNat, sMod, Int.natCast_emod]
    simp [h2]
  | succ k ih =>
    rw [sModNat, sMod, ← ih]
    have h3 : 2 ≤ 2 ^ p - 1 := by
      zify [h2]
      calc
        (2 : Int) ≤ 4 - 1 := by simp
        _         ≤ 2 ^ p - 1 := by zify at h1; exact Int.sub_le_sub_right h1 _
    zify [h2, h3]
    rw [← add_sub_assoc, sub_eq_add_neg, add_assoc, add_comm _ (-2), ← add_assoc,
      Int.add_emod_right, ← sub_eq_add_neg]

/-- Tail-recursive version of `sModNat`. -/
def sModNatTR (q k : ℕ) : ℕ :=
  go k (4 % q)
where
  /-- Helper function for `sMod''`. -/
  go : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => go n ((acc ^ 2 + (q - 2)) % q)

/--
Generalization of `sModNat` with arbitrary base case,
useful for proving `sModNatTR` and `sModNat` agree.
-/
def sModNat_aux (b q : ℕ) : ℕ → ℕ
  | 0 => b
  | i + 1 => (sModNat_aux b q i ^ 2 + (q - 2)) % q

theorem sModNat_aux_eq (q k : ℕ) : sModNat_aux (4 % q) q k = sModNat q k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sModNat_aux, ih, sModNat, ← ih]

theorem sModNatTR_eq_sModNat (q i : ℕ) : sModNatTR q i = sModNat q i := by
  rw [sModNatTR, helper, sModNat_aux_eq]
where
  helper b q k : sModNatTR.go q k b = sModNat_aux b q k := by
    induction k generalizing b with
    | zero => rfl
    | succ k ih =>
      rw [sModNatTR.go, ih, sModNat_aux]
      clear ih
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [sModNat_aux, ih, sModNat_aux]

lemma testTrueHelper (p : ℕ) (hp : Nat.blt 1 p = true) (h : sModNatTR (2 ^ p - 1) (p - 2) = 0) :
    LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sModNat_eq_sMod p _ hp,
    ← sModNatTR_eq_sModNat, h]
  rfl

lemma testFalseHelper (p : ℕ) (hp : Nat.blt 1 p = true)
    (h : Nat.ble 1 (sModNatTR (2 ^ p - 1) (p - 2))) : ¬ LucasLehmerTest p := by
  rw [Nat.blt_eq] at hp
  rw [Nat.ble_eq, Nat.succ_le, Nat.pos_iff_ne_zero] at h
  rw [LucasLehmerTest, LucasLehmer.residue_eq_zero_iff_sMod_eq_zero p hp, ← sModNat_eq_sMod p _ hp,
    ← sModNatTR_eq_sModNat]
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
def evalLucasLehmerTest : NormNumExt where eval {_ _} e := do
  let .app _ (p : Q(ℕ)) ← Meta.whnfR e | failure
  let ⟨ep, hp⟩ ← deriveNat p _
  let np := ep.natLit!
  unless 1 < np do
    failure
  haveI' h1ltp : Nat.blt 1 $ep =Q true := ⟨⟩
  if sModNatTR (2 ^ np - 1) (np - 2) = 0 then
    haveI' hs : sModNatTR (2 ^ $ep - 1) ($ep - 2) =Q 0 := ⟨⟩
    have pf : Q(LucasLehmerTest $ep) := q(testTrueHelper $ep $h1ltp $hs)
    have pf' : Q(LucasLehmerTest $p) := q(isNat_lucasLehmerTest $hp $pf)
    return .isTrue pf'
  else
    haveI' hs : Nat.ble 1 (sModNatTR (2 ^ $ep - 1) ($ep - 2)) =Q true := ⟨⟩
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

-- It's hard to know what the limiting factor for large Mersenne primes would be.
-- In the purely computational world, I think it's the squaring operation in `s`.
