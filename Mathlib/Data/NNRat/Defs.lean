/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Set.Operations
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.GaloisConnection.Defs

/-!
# Nonnegative rationals

This file defines the nonnegative rationals as a subtype of `Rat` and provides its basic algebraic
order structure.

Note that `NNRat` is not declared as a `Semifield` here. See `Mathlib/Algebra/Field/Rat.lean` for
that instance.

We also define an instance `CanLift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `NNRat` in scope `NNRat`.

## Huge warning

Whenever you state a lemma about the coercion `ℚ≥0 → ℚ`, check that Lean inserts `NNRat.cast`, not
`Subtype.val`. Else your lemma will never apply.
-/

assert_not_exists CompleteLattice OrderedCommMonoid

library_note "specialised high priority simp lemma" /--
It sometimes happens that a `@[simp]` lemma declared early in the library can be proved by `simp`
using later, more general simp lemmas. In that case, the following reasons might be arguments for
the early lemma to be tagged `@[simp high]` (rather than `@[simp, nolint simpNF]` or
un``@[simp]``ed):
1. There is a significant portion of the library which needs the early lemma to be available via
  `simp` and which doesn't have access to the more general lemmas.
2. The more general lemmas have more complicated typeclass assumptions, causing rewrites with them
  to be slower.
-/

open Function

instance Rat.instZeroLEOneClass : ZeroLEOneClass ℚ where
  zero_le_one := rfl

instance Rat.instPosMulMono : PosMulMono ℚ where
  elim := fun r p q h => by
    simp only [mul_comm]
    simpa [sub_mul, sub_nonneg] using Rat.mul_nonneg (sub_nonneg.2 h) r.2

deriving instance CommSemiring for NNRat
deriving instance LinearOrder for NNRat
deriving instance Sub for NNRat
deriving instance Inhabited for NNRat

namespace NNRat

variable {p q : ℚ≥0}

instance instNontrivial : Nontrivial ℚ≥0 where exists_pair_ne := ⟨1, 0, by decide⟩
instance instOrderBot : OrderBot ℚ≥0 where
  bot := 0
  bot_le q := q.2

@[simp] lemma val_eq_cast (q : ℚ≥0) : q.1 = q := rfl

instance instCharZero : CharZero ℚ≥0 where
  cast_injective a b hab := by simpa using congr_arg num hab

instance canLift : CanLift ℚ ℚ≥0 (↑) fun q ↦ 0 ≤ q where
  prf q hq := ⟨⟨q, hq⟩, rfl⟩

@[ext]
theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
  Subtype.ext

protected theorem coe_injective : Injective ((↑) : ℚ≥0 → ℚ) :=
  Subtype.coe_injective

-- See note [specialised high priority simp lemma]
@[simp high, norm_cast]
theorem coe_inj : (p : ℚ) = q ↔ p = q :=
  Subtype.coe_inj

theorem ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
  NNRat.coe_inj.not

-- TODO: We have to write `NNRat.cast` explicitly, else the statement picks up `Subtype.val` instead
@[simp, norm_cast] lemma coe_mk (q : ℚ) (hq) : NNRat.cast ⟨q, hq⟩ = q := rfl

lemma «forall» {p : ℚ≥0 → Prop} : (∀ q, p q) ↔ ∀ q hq, p ⟨q, hq⟩ := Subtype.forall
lemma «exists» {p : ℚ≥0 → Prop} : (∃ q, p q) ↔ ∃ q hq, p ⟨q, hq⟩ := Subtype.exists

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def _root_.Rat.toNNRat (q : ℚ) : ℚ≥0 :=
  ⟨max q 0, le_max_right _ _⟩

theorem _root_.Rat.coe_toNNRat (q : ℚ) (hq : 0 ≤ q) : (q.toNNRat : ℚ) = q :=
  max_eq_left hq

theorem _root_.Rat.le_coe_toNNRat (q : ℚ) : q ≤ q.toNNRat :=
  le_max_left _ _

open Rat (toNNRat)

@[simp]
theorem coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q :=
  q.2

@[simp, norm_cast] lemma coe_zero : ((0 : ℚ≥0) : ℚ) = 0 := rfl
@[simp] lemma num_zero : num 0 = 0 := rfl
@[simp] lemma den_zero : den 0 = 1 := rfl

@[simp, norm_cast] lemma coe_one : ((1 : ℚ≥0) : ℚ) = 1 := rfl
@[simp] lemma num_one : num 1 = 1 := rfl
@[simp] lemma den_one : den 1 = 1 := rfl

@[simp, norm_cast]
theorem coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q :=
  rfl

@[simp, norm_cast]
theorem coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q :=
  rfl

@[simp, norm_cast] lemma coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = (q : ℚ) ^ n :=
  rfl

@[simp] lemma num_pow (q : ℚ≥0) (n : ℕ) : (q ^ n).num = q.num ^ n := by simp [num, Int.natAbs_pow]
@[simp] lemma den_pow (q : ℚ≥0) (n : ℕ) : (q ^ n).den = q.den ^ n := rfl

@[simp, norm_cast]
theorem coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
  max_eq_left <| le_sub_comm.2 <| by rwa [sub_zero]

-- See note [specialised high priority simp lemma]
@[simp high]
theorem coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast

theorem coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 :=
  coe_eq_zero.not

@[norm_cast]
theorem coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[norm_cast]
theorem coe_lt_coe : (p : ℚ) < q ↔ p < q :=
  Iff.rfl

@[norm_cast]
theorem coe_pos : (0 : ℚ) < q ↔ 0 < q :=
  Iff.rfl

theorem coe_mono : Monotone ((↑) : ℚ≥0 → ℚ) :=
  fun _ _ ↦ coe_le_coe.2

theorem toNNRat_mono : Monotone toNNRat :=
  fun _ _ h ↦ max_le_max h le_rfl

@[simp]
theorem toNNRat_coe (q : ℚ≥0) : toNNRat q = q :=
  ext <| max_eq_left q.2

@[simp]
theorem toNNRat_coe_nat (n : ℕ) : toNNRat n = n :=
  ext <| by simp only [Nat.cast_nonneg', Rat.coe_toNNRat]; rfl

/-- `toNNRat` and `(↑) : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : GaloisInsertion toNNRat (↑) :=
  GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe

/-- Coercion `ℚ≥0 → ℚ` as a `RingHom`. -/
def coeHom : ℚ≥0 →+* ℚ where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero
  map_add' := coe_add

@[simp, norm_cast] lemma coe_natCast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n := rfl

@[simp]
theorem mk_natCast (n : ℕ) : @Eq ℚ≥0 (⟨(n : ℚ), Nat.cast_nonneg' n⟩ : ℚ≥0) n :=
  rfl

@[simp]
theorem coe_coeHom : ⇑coeHom = ((↑) : ℚ≥0 → ℚ) :=
  rfl

@[norm_cast]
theorem nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
  coeHom.toAddMonoidHom.map_nsmul _ _

theorem bddAbove_coe {s : Set ℚ≥0} : BddAbove ((↑) '' s : Set ℚ) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ ↦
    ⟨toNNRat b, fun ⟨y, _⟩ hys ↦
      show y ≤ max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans <| le_max_left _ _⟩,
    fun ⟨b, hb⟩ ↦ ⟨b, fun _ ⟨_, hx, Eq⟩ ↦ Eq ▸ hb hx⟩⟩

theorem bddBelow_coe (s : Set ℚ≥0) : BddBelow (((↑) : ℚ≥0 → ℚ) '' s) :=
  ⟨0, fun _ ⟨q, _, h⟩ ↦ h ▸ q.2⟩

@[norm_cast]
theorem coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
  coe_mono.map_max

@[norm_cast]
theorem coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
  coe_mono.map_min

theorem sub_def (p q : ℚ≥0) : p - q = toNNRat (p - q) :=
  rfl

@[simp]
theorem abs_coe (q : ℚ≥0) : |(q : ℚ)| = q :=
  abs_of_nonneg q.2

-- See note [specialised high priority simp lemma]
@[simp high]
theorem nonpos_iff_eq_zero (q : ℚ≥0) : q ≤ 0 ↔ q = 0 :=
  ⟨fun h => le_antisymm h q.2, fun h => h.symm ▸ q.2⟩

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

@[simp]
theorem toNNRat_zero : toNNRat 0 = 0 := rfl

@[simp]
theorem toNNRat_one : toNNRat 1 = 1 := rfl

@[simp]
theorem toNNRat_pos : 0 < toNNRat q ↔ 0 < q := by simp [toNNRat, ← coe_lt_coe]

@[simp]
theorem toNNRat_eq_zero : toNNRat q = 0 ↔ q ≤ 0 := by
  simpa [-toNNRat_pos] using (@toNNRat_pos q).not

alias ⟨_, toNNRat_of_nonpos⟩ := toNNRat_eq_zero

@[simp]
theorem toNNRat_le_toNNRat_iff (hp : 0 ≤ p) : toNNRat q ≤ toNNRat p ↔ q ≤ p := by
  simp [← coe_le_coe, toNNRat, hp]

@[simp]
theorem toNNRat_lt_toNNRat_iff' : toNNRat q < toNNRat p ↔ q < p ∧ 0 < p := by
  simp [← coe_lt_coe, toNNRat]

theorem toNNRat_lt_toNNRat_iff (h : 0 < p) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)

theorem toNNRat_lt_toNNRat_iff_of_nonneg (hq : 0 ≤ q) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h ↦ ⟨h, hq.trans_lt h⟩⟩

@[simp]
theorem toNNRat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : toNNRat (q + p) = toNNRat q + toNNRat p :=
  NNRat.ext <| by simp [toNNRat, hq, hp, add_nonneg]

theorem toNNRat_add_le : toNNRat (q + p) ≤ toNNRat q + toNNRat p :=
  coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) <| coe_nonneg _

theorem toNNRat_le_iff_le_coe {p : ℚ≥0} : toNNRat q ≤ p ↔ q ≤ ↑p :=
  NNRat.gi.gc q p

theorem le_toNNRat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ toNNRat p ↔ ↑q ≤ p := by
  rw [← coe_le_coe, Rat.coe_toNNRat p hp]

theorem le_toNNRat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ toNNRat p ↔ ↑q ≤ p :=
  (le_or_gt 0 p).elim le_toNNRat_iff_coe_le fun hp ↦ by
    simp only [(hp.trans_le q.coe_nonneg).not_ge, toNNRat_eq_zero.2 hp.le, hq.not_ge]

theorem toNNRat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : toNNRat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe, Rat.coe_toNNRat q hq]

theorem lt_toNNRat_iff_coe_lt {q : ℚ≥0} : q < toNNRat p ↔ ↑q < p :=
  NNRat.gi.gc.lt_iff_lt

theorem toNNRat_mul (hp : 0 ≤ p) : toNNRat (p * q) = toNNRat p * toNNRat q := by
  rcases le_total 0 q with hq | hq
  · ext; simp [toNNRat, hp, hq, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [toNNRat_eq_zero.2 hq, toNNRat_eq_zero.2 hpq, mul_zero]

end Rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot]
def Rat.nnabs (x : ℚ) : ℚ≥0 :=
  ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp]
theorem Rat.coe_nnabs (x : ℚ) : (Rat.nnabs x : ℚ) = abs x := rfl

/-! ### Numerator and denominator -/


namespace NNRat

variable {p q : ℚ≥0}

@[norm_cast] lemma num_coe (q : ℚ≥0) : (q : ℚ).num = q.num := by
  simp only [num, Int.natCast_natAbs, Rat.num_nonneg, coe_nonneg, abs_of_nonneg]

theorem natAbs_num_coe : (q : ℚ).num.natAbs = q.num := rfl

@[norm_cast] lemma den_coe : (q : ℚ).den = q.den := rfl

@[simp] lemma num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := by simp [num]
@[simp] lemma num_pos : 0 < q.num ↔ 0 < q := by
  simpa [num, -nonpos_iff_eq_zero] using nonpos_iff_eq_zero _ |>.not.symm
@[simp] lemma den_pos (q : ℚ≥0) : 0 < q.den := Rat.den_pos _
@[simp] lemma den_ne_zero (q : ℚ≥0) : q.den ≠ 0 := Rat.den_ne_zero _

lemma coprime_num_den (q : ℚ≥0) : q.num.Coprime q.den := by simpa [num, den] using Rat.reduced _

-- TODO: Rename `Rat.coe_nat_num`, `Rat.intCast_den`, `Rat.ofNat_num`, `Rat.ofNat_den`
@[simp, norm_cast] lemma num_natCast (n : ℕ) : num n = n := rfl
@[simp, norm_cast] lemma den_natCast (n : ℕ) : den n = 1 := rfl

@[simp] lemma num_ofNat (n : ℕ) [n.AtLeastTwo] : num ofNat(n) = OfNat.ofNat n :=
  rfl
@[simp] lemma den_ofNat (n : ℕ) [n.AtLeastTwo] : den ofNat(n) = 1 := rfl

theorem ext_num_den (hn : p.num = q.num) (hd : p.den = q.den) : p = q := by
  refine ext <| Rat.ext ?_ hd
  simpa [num_coe]

theorem ext_num_den_iff : p = q ↔ p.num = q.num ∧ p.den = q.den :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun h ↦ ext_num_den h.1 h.2⟩

/-- Form the quotient `n / d` where `n d : ℕ`.

See also `Rat.divInt` and `mkRat`. -/
def divNat (n d : ℕ) : ℚ≥0 :=
  ⟨.divInt n d, Rat.divInt_nonneg (Int.ofNat_zero_le n) (Int.ofNat_zero_le d)⟩

variable {n₁ n₂ d₁ d₂ : ℕ}

@[simp, norm_cast] lemma coe_divNat (n d : ℕ) : (divNat n d : ℚ) = .divInt n d := rfl

lemma mk_divInt (n d : ℕ) :
    ⟨.divInt n d, Rat.divInt_nonneg (Int.ofNat_zero_le n) (Int.ofNat_zero_le d)⟩ = divNat n d := rfl

lemma divNat_inj (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) : divNat n₁ d₁ = divNat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rw [← coe_inj]; simp [Rat.mkRat_eq_iff, h₁, h₂]; norm_cast

@[simp] lemma divNat_zero (n : ℕ) : divNat n 0 = 0 := by simp [divNat]; rfl

@[simp] lemma num_divNat_den (q : ℚ≥0) : divNat q.num q.den = q :=
  ext <| by rw [← (q : ℚ).mkRat_num_den']; simp [num_coe, den_coe]

lemma natCast_eq_divNat (n : ℕ) : (n : ℚ≥0) = divNat n 1 := (num_divNat_den _).symm

lemma divNat_mul_divNat (n₁ n₂ : ℕ) {d₁ d₂} :
    divNat n₁ d₁ * divNat n₂ d₂ = divNat (n₁ * n₂) (d₁ * d₂) := by
  ext; push_cast; exact Rat.divInt_mul_divInt _ _

lemma divNat_mul_left {a : ℕ} (ha : a ≠ 0) (n d : ℕ) : divNat (a * n) (a * d) = divNat n d := by
  ext; push_cast; exact Rat.divInt_mul_left (mod_cast ha)

lemma divNat_mul_right {a : ℕ} (ha : a ≠ 0) (n d : ℕ) : divNat (n * a) (d * a) = divNat n d := by
  ext; push_cast; exact Rat.divInt_mul_right (mod_cast ha)

@[simp] lemma mul_den_eq_num (q : ℚ≥0) : q * q.den = q.num := by
  ext
  push_cast
  rw [← Int.cast_natCast, ← den_coe, ← Int.cast_natCast q.num, ← num_coe]
  exact Rat.mul_den_eq_num _

@[simp] lemma den_mul_eq_num (q : ℚ≥0) : q.den * q = q.num := by rw [mul_comm, mul_den_eq_num]

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with nonnegative rational
numbers of the form `n / d` with `d ≠ 0` and `n`, `d` coprime. -/
@[elab_as_elim]
def numDenCasesOn.{u} {C : ℚ≥0 → Sort u} (q) (H : ∀ n d, d ≠ 0 → n.Coprime d → C (divNat n d)) :
    C q := by rw [← q.num_divNat_den]; exact H _ _ q.den_ne_zero q.coprime_num_den

lemma add_def (q r : ℚ≥0) : q + r = divNat (q.num * r.den + r.num * q.den) (q.den * r.den) := by
  ext; simp [Rat.add_def', Rat.mkRat_eq_divInt, num_coe, den_coe]

lemma mul_def (q r : ℚ≥0) : q * r = divNat (q.num * r.num) (q.den * r.den) := by
  ext; simp [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, num_coe, den_coe]

theorem lt_def {p q : ℚ≥0} : p < q ↔ p.num * q.den < q.num * p.den := by
  rw [← NNRat.coe_lt_coe, Rat.lt_def]; norm_cast

theorem le_def {p q : ℚ≥0} : p ≤ q ↔ p.num * q.den ≤ q.num * p.den := by
  rw [← NNRat.coe_le_coe, Rat.le_def]; norm_cast

end NNRat

namespace Mathlib.Tactic.Qify

@[qify_simps] lemma nnratCast_eq (a b : ℚ≥0) : a = b ↔ (a : ℚ) = (b : ℚ) := NNRat.coe_inj.symm
@[qify_simps] lemma nnratCast_le (a b : ℚ≥0) : a ≤ b ↔ (a : ℚ) ≤ (b : ℚ) := NNRat.coe_le_coe.symm
@[qify_simps] lemma nnratCast_lt (a b : ℚ≥0) : a < b ↔ (a : ℚ) < (b : ℚ) := NNRat.coe_lt_coe.symm
@[qify_simps] lemma nnratCast_ne (a b : ℚ≥0) : a ≠ b ↔ (a : ℚ) ≠ (b : ℚ) := NNRat.ne_iff.symm

end Mathlib.Tactic.Qify
