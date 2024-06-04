/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Int.Lemmas

#align_import data.rat.nnrat from "leanprover-community/mathlib"@"b3f4f007a962e3787aa0f3b5c7942a1317f7d88e"

/-!
# Nonnegative rationals

This file defines the nonnegative rationals as a subtype of `Rat` and provides its basic algebraic
order structure.

Note that `NNRat` is not declared as a `Field` here. See `Data.NNRat.Lemmas` for that instance.

We also define an instance `CanLift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `NNRat` in locale `NNRat`.

## Huge warning

Whenever you state a lemma about the coercion `ℚ≥0 → ℚ`, check that Lean inserts `NNRat.cast`, not
`Subtype.val`. Else your lemma will never apply.
-/


open Function

deriving instance CanonicallyOrderedCommSemiring for NNRat
deriving instance CanonicallyLinearOrderedAddCommMonoid for NNRat
deriving instance Sub for NNRat
deriving instance Inhabited for NNRat

-- TODO: `deriving instance OrderedSub for NNRat` doesn't work yet, so we add the instance manually
instance NNRat.instOrderedSub : OrderedSub ℚ≥0 := Nonneg.orderedSub

namespace NNRat

variable {α : Type*} {p q : ℚ≥0}

@[simp] lemma val_eq_cast (q : ℚ≥0) : q.1 = q := rfl
#align nnrat.val_eq_coe NNRat.val_eq_cast

instance canLift : CanLift ℚ ℚ≥0 (↑) fun q ↦ 0 ≤ q where
  prf q hq := ⟨⟨q, hq⟩, rfl⟩
#align nnrat.can_lift NNRat.canLift

@[ext]
theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
  Subtype.ext
#align nnrat.ext NNRat.ext

protected theorem coe_injective : Injective ((↑) : ℚ≥0 → ℚ) :=
  Subtype.coe_injective
#align nnrat.coe_injective NNRat.coe_injective

@[simp, norm_cast]
theorem coe_inj : (p : ℚ) = q ↔ p = q :=
  Subtype.coe_inj
#align nnrat.coe_inj NNRat.coe_inj

theorem ext_iff : p = q ↔ (p : ℚ) = q :=
  Subtype.ext_iff
#align nnrat.ext_iff NNRat.ext_iff

theorem ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
  NNRat.coe_inj.not
#align nnrat.ne_iff NNRat.ne_iff

-- TODO: We have to write `NNRat.cast` explicitly, else the statement picks up `Subtype.val` instead
@[simp, norm_cast] lemma coe_mk (q : ℚ) (hq) : NNRat.cast ⟨q, hq⟩ = q := rfl
#align nnrat.coe_mk NNRat.coe_mk

lemma «forall» {p : ℚ≥0 → Prop} : (∀ q, p q) ↔ ∀ q hq, p ⟨q, hq⟩ := Subtype.forall
lemma «exists» {p : ℚ≥0 → Prop} : (∃ q, p q) ↔ ∃ q hq, p ⟨q, hq⟩ := Subtype.exists

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def _root_.Rat.toNNRat (q : ℚ) : ℚ≥0 :=
  ⟨max q 0, le_max_right _ _⟩
#align rat.to_nnrat Rat.toNNRat

theorem _root_.Rat.coe_toNNRat (q : ℚ) (hq : 0 ≤ q) : (q.toNNRat : ℚ) = q :=
  max_eq_left hq
#align rat.coe_to_nnrat Rat.coe_toNNRat

theorem _root_.Rat.le_coe_toNNRat (q : ℚ) : q ≤ q.toNNRat :=
  le_max_left _ _
#align rat.le_coe_to_nnrat Rat.le_coe_toNNRat

open Rat (toNNRat)

@[simp]
theorem coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q :=
  q.2
#align nnrat.coe_nonneg NNRat.coe_nonneg

-- eligible for dsimp
@[simp, nolint simpNF, norm_cast] lemma coe_zero : ((0 : ℚ≥0) : ℚ) = 0 := rfl
#align nnrat.coe_zero NNRat.coe_zero

-- eligible for dsimp
@[simp, nolint simpNF, norm_cast] lemma coe_one : ((1 : ℚ≥0) : ℚ) = 1 := rfl
#align nnrat.coe_one NNRat.coe_one

@[simp, norm_cast]
theorem coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q :=
  rfl
#align nnrat.coe_add NNRat.coe_add

@[simp, norm_cast]
theorem coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q :=
  rfl
#align nnrat.coe_mul NNRat.coe_mul

-- eligible for dsimp
@[simp, nolint simpNF, norm_cast] lemma coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = (q : ℚ) ^ n :=
  rfl
#align nnrat.coe_pow NNRat.coe_pow

@[simp] lemma num_pow (q : ℚ≥0) (n : ℕ) : (q ^ n).num = q.num ^ n := by simp [num, Int.natAbs_pow]
@[simp] lemma den_pow (q : ℚ≥0) (n : ℕ) : (q ^ n).den = q.den ^ n := rfl

-- Porting note: `bit0` `bit1` are deprecated, so remove these theorems.
#noalign nnrat.coe_bit0
#noalign nnrat.coe_bit1

@[simp, norm_cast]
theorem coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
  max_eq_left <| le_sub_comm.2 <| by rwa [sub_zero]
#align nnrat.coe_sub NNRat.coe_sub

@[simp]
theorem coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast
#align nnrat.coe_eq_zero NNRat.coe_eq_zero

theorem coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 :=
  coe_eq_zero.not
#align nnrat.coe_ne_zero NNRat.coe_ne_zero

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align nnrat.coe_le_coe NNRat.coe_le_coe

@[norm_cast] -- Porting note (#10618): simp can prove this
theorem coe_lt_coe : (p : ℚ) < q ↔ p < q :=
  Iff.rfl
#align nnrat.coe_lt_coe NNRat.coe_lt_coe

@[simp, norm_cast]
theorem coe_pos : (0 : ℚ) < q ↔ 0 < q :=
  Iff.rfl
#align nnrat.coe_pos NNRat.coe_pos

theorem coe_mono : Monotone ((↑) : ℚ≥0 → ℚ) :=
  fun _ _ ↦ coe_le_coe.2
#align nnrat.coe_mono NNRat.coe_mono

theorem toNNRat_mono : Monotone toNNRat :=
  fun _ _ h ↦ max_le_max h le_rfl
#align nnrat.to_nnrat_mono NNRat.toNNRat_mono

@[simp]
theorem toNNRat_coe (q : ℚ≥0) : toNNRat q = q :=
  ext <| max_eq_left q.2
#align nnrat.to_nnrat_coe NNRat.toNNRat_coe

@[simp]
theorem toNNRat_coe_nat (n : ℕ) : toNNRat n = n :=
  ext <| by simp only [Nat.cast_nonneg, Rat.coe_toNNRat]; rfl
#align nnrat.to_nnrat_coe_nat NNRat.toNNRat_coe_nat

/-- `toNNRat` and `(↑) : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : GaloisInsertion toNNRat (↑) :=
  GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe
#align nnrat.gi NNRat.gi

/-- Coercion `ℚ≥0 → ℚ` as a `RingHom`. -/
def coeHom : ℚ≥0 →+* ℚ where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero
  map_add' := coe_add
#align nnrat.coe_hom NNRat.coeHom

-- eligible for dsimp
@[simp, nolint simpNF, norm_cast] lemma coe_natCast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n := rfl
#align nnrat.coe_nat_cast NNRat.coe_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem mk_natCast (n : ℕ) : @Eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
  rfl
#align nnrat.mk_coe_nat NNRat.mk_natCast

@[deprecated] alias mk_coe_nat := mk_natCast -- 2024-04-05

@[simp]
theorem coe_coeHom : ⇑coeHom = ((↑) : ℚ≥0 → ℚ) :=
  rfl
#align nnrat.coe_coe_hom NNRat.coe_coeHom

@[norm_cast]
theorem nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
  coeHom.toAddMonoidHom.map_nsmul _ _
#align nnrat.nsmul_coe NNRat.nsmul_coe

theorem bddAbove_coe {s : Set ℚ≥0} : BddAbove ((↑) '' s : Set ℚ) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ ↦
    ⟨toNNRat b, fun ⟨y, _⟩ hys ↦
      show y ≤ max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans <| le_max_left _ _⟩,
    fun ⟨b, hb⟩ ↦ ⟨b, fun _ ⟨_, hx, Eq⟩ ↦ Eq ▸ hb hx⟩⟩
#align nnrat.bdd_above_coe NNRat.bddAbove_coe

theorem bddBelow_coe (s : Set ℚ≥0) : BddBelow (((↑) : ℚ≥0 → ℚ) '' s) :=
  ⟨0, fun _ ⟨q, _, h⟩ ↦ h ▸ q.2⟩
#align nnrat.bdd_below_coe NNRat.bddBelow_coe

@[simp, norm_cast]
theorem coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
  coe_mono.map_max
#align nnrat.coe_max NNRat.coe_max

@[simp, norm_cast]
theorem coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
  coe_mono.map_min
#align nnrat.coe_min NNRat.coe_min

theorem sub_def (p q : ℚ≥0) : p - q = toNNRat (p - q) :=
  rfl
#align nnrat.sub_def NNRat.sub_def

@[simp]
theorem abs_coe (q : ℚ≥0) : |(q : ℚ)| = q :=
  abs_of_nonneg q.2
#align nnrat.abs_coe NNRat.abs_coe

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

@[simp]
theorem toNNRat_zero : toNNRat 0 = 0 := rfl
#align rat.to_nnrat_zero Rat.toNNRat_zero

@[simp]
theorem toNNRat_one : toNNRat 1 = 1 := rfl
#align rat.to_nnrat_one Rat.toNNRat_one

@[simp]
theorem toNNRat_pos : 0 < toNNRat q ↔ 0 < q := by simp [toNNRat, ← coe_lt_coe]
#align rat.to_nnrat_pos Rat.toNNRat_pos

@[simp]
theorem toNNRat_eq_zero : toNNRat q = 0 ↔ q ≤ 0 := by
  simpa [-toNNRat_pos] using (@toNNRat_pos q).not
#align rat.to_nnrat_eq_zero Rat.toNNRat_eq_zero

alias ⟨_, toNNRat_of_nonpos⟩ := toNNRat_eq_zero
#align rat.to_nnrat_of_nonpos Rat.toNNRat_of_nonpos

@[simp]
theorem toNNRat_le_toNNRat_iff (hp : 0 ≤ p) : toNNRat q ≤ toNNRat p ↔ q ≤ p := by
  simp [← coe_le_coe, toNNRat, hp]
#align rat.to_nnrat_le_to_nnrat_iff Rat.toNNRat_le_toNNRat_iff

@[simp]
theorem toNNRat_lt_toNNRat_iff' : toNNRat q < toNNRat p ↔ q < p ∧ 0 < p := by
  simp [← coe_lt_coe, toNNRat, lt_irrefl]
#align rat.to_nnrat_lt_to_nnrat_iff' Rat.toNNRat_lt_toNNRat_iff'

theorem toNNRat_lt_toNNRat_iff (h : 0 < p) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)
#align rat.to_nnrat_lt_to_nnrat_iff Rat.toNNRat_lt_toNNRat_iff

theorem toNNRat_lt_toNNRat_iff_of_nonneg (hq : 0 ≤ q) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h ↦ ⟨h, hq.trans_lt h⟩⟩
#align rat.to_nnrat_lt_to_nnrat_iff_of_nonneg Rat.toNNRat_lt_toNNRat_iff_of_nonneg

@[simp]
theorem toNNRat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : toNNRat (q + p) = toNNRat q + toNNRat p :=
  NNRat.ext <| by simp [toNNRat, hq, hp, add_nonneg]
#align rat.to_nnrat_add Rat.toNNRat_add

theorem toNNRat_add_le : toNNRat (q + p) ≤ toNNRat q + toNNRat p :=
  coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) <| coe_nonneg _
#align rat.to_nnrat_add_le Rat.toNNRat_add_le

theorem toNNRat_le_iff_le_coe {p : ℚ≥0} : toNNRat q ≤ p ↔ q ≤ ↑p :=
  NNRat.gi.gc q p
#align rat.to_nnrat_le_iff_le_coe Rat.toNNRat_le_iff_le_coe

theorem le_toNNRat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ toNNRat p ↔ ↑q ≤ p := by
  rw [← coe_le_coe, Rat.coe_toNNRat p hp]
#align rat.le_to_nnrat_iff_coe_le Rat.le_toNNRat_iff_coe_le

theorem le_toNNRat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ toNNRat p ↔ ↑q ≤ p :=
  (le_or_lt 0 p).elim le_toNNRat_iff_coe_le fun hp ↦ by
    simp only [(hp.trans_le q.coe_nonneg).not_le, toNNRat_eq_zero.2 hp.le, hq.not_le]
#align rat.le_to_nnrat_iff_coe_le' Rat.le_toNNRat_iff_coe_le'

theorem toNNRat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : toNNRat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe, Rat.coe_toNNRat q hq]
#align rat.to_nnrat_lt_iff_lt_coe Rat.toNNRat_lt_iff_lt_coe

theorem lt_toNNRat_iff_coe_lt {q : ℚ≥0} : q < toNNRat p ↔ ↑q < p :=
  NNRat.gi.gc.lt_iff_lt
#align rat.lt_to_nnrat_iff_coe_lt Rat.lt_toNNRat_iff_coe_lt

-- Porting note: `bit0` `bit1` are deprecated, so remove these theorems.
#noalign rat.to_nnrat_bit0
#noalign rat.to_nnrat_bit1

theorem toNNRat_mul (hp : 0 ≤ p) : toNNRat (p * q) = toNNRat p * toNNRat q := by
  rcases le_total 0 q with hq | hq
  · ext; simp [toNNRat, hp, hq, max_eq_left, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [toNNRat_eq_zero.2 hq, toNNRat_eq_zero.2 hpq, mul_zero]
#align rat.to_nnrat_mul Rat.toNNRat_mul

end Rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
--@[pp_nodot]  -- Porting note: Commented out.
def Rat.nnabs (x : ℚ) : ℚ≥0 :=
  ⟨abs x, abs_nonneg x⟩
#align rat.nnabs Rat.nnabs

@[norm_cast, simp]
theorem Rat.coe_nnabs (x : ℚ) : (Rat.nnabs x : ℚ) = abs x := rfl
#align rat.coe_nnabs Rat.coe_nnabs

/-! ### Numerator and denominator -/


namespace NNRat

variable {p q : ℚ≥0}

@[norm_cast] lemma num_coe (q : ℚ≥0) : (q : ℚ).num = q.num := by
  simp [num, abs_of_nonneg, Rat.num_nonneg, q.2]

theorem natAbs_num_coe : (q : ℚ).num.natAbs = q.num := rfl
#align nnrat.nat_abs_num_coe NNRat.natAbs_num_coe

@[norm_cast] lemma den_coe : (q : ℚ).den = q.den := rfl
#align nnrat.denom_coe NNRat.den_coe

@[simp] lemma num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := by simp [num]
@[simp] lemma num_pos : 0 < q.num ↔ 0 < q := by simp [pos_iff_ne_zero]
@[simp] lemma den_pos (q : ℚ≥0) : 0 < q.den := Rat.den_pos _
@[simp] lemma den_ne_zero (q : ℚ≥0) : q.den ≠ 0 := Rat.den_ne_zero _

lemma coprime_num_den (q : ℚ≥0) : q.num.Coprime q.den := by simpa [num, den] using Rat.reduced _

-- TODO: Rename `Rat.coe_nat_num`, `Rat.intCast_den`, `Rat.ofNat_num`, `Rat.ofNat_den`
@[simp, norm_cast] lemma num_natCast (n : ℕ) : num n = n := rfl
@[simp, norm_cast] lemma den_natCast (n : ℕ) : den n = 1 := rfl

-- See note [no_index around OfNat.ofNat]
@[simp] lemma num_ofNat (n : ℕ) [n.AtLeastTwo] : num (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  rfl
@[simp] lemma den_ofNat (n : ℕ) [n.AtLeastTwo] : den (no_index (OfNat.ofNat n)) = 1 := rfl

theorem ext_num_den (hn : p.num = q.num) (hd : p.den = q.den) : p = q := by
  refine ext <| Rat.ext ?_ ?_
  · apply (Int.natAbs_inj_of_nonneg_of_nonneg _ _).1 hn
    · exact Rat.num_nonneg.2 p.2
    · exact Rat.num_nonneg.2 q.2
  · exact hd
#align nnrat.ext_num_denom NNRat.ext_num_den

theorem ext_num_den_iff : p = q ↔ p.num = q.num ∧ p.den = q.den :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun h ↦ ext_num_den h.1 h.2⟩
#align nnrat.ext_num_denom_iff NNRat.ext_num_den_iff

/-- Form the quotient `n / d` where `n d : ℕ`.

See also `Rat.divInt` and `mkRat`. -/
def divNat (n d : ℕ) : ℚ≥0 := ⟨.divInt n d, Rat.divInt_nonneg n.cast_nonneg d.cast_nonneg⟩

variable {n₁ n₂ d₁ d₂ d : ℕ}

@[simp, norm_cast] lemma coe_divNat (n d : ℕ) : (divNat n d : ℚ) = .divInt n d := rfl

lemma mk_divInt (n d : ℕ) :
    ⟨.divInt n d, Rat.divInt_nonneg n.cast_nonneg d.cast_nonneg⟩ = divNat n d := rfl

lemma divNat_inj (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) : divNat n₁ d₁ = divNat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rw [← coe_inj]; simp [Rat.mkRat_eq_iff, h₁, h₂]; norm_cast

@[simp] lemma divNat_zero (n : ℕ) : divNat n 0 = 0 := by simp [divNat]; rfl

@[simp] lemma num_divNat_den (q : ℚ≥0) : divNat q.num q.den = q :=
  ext $ by rw [← (q : ℚ).mkRat_num_den']; simp [num_coe, den_coe]

lemma natCast_eq_divNat (n : ℕ) : (n : ℚ≥0) = divNat n 1 := (num_divNat_den _).symm

lemma divNat_mul_divNat (n₁ n₂ : ℕ) {d₁ d₂} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    divNat n₁ d₁ * divNat n₂ d₂ = divNat (n₁ * n₂) (d₁ * d₂) := by
  ext; push_cast; exact Rat.divInt_mul_divInt _ _ (mod_cast hd₁) (mod_cast hd₂)

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

end NNRat
