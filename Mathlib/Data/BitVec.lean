/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Alex Keizer
-/
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.ZMod.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors which can only be stated in Mathlib or downstream
because they refer to other notions defined in Mathlib.

Please do not extend this file further: material about BitVec needed in downstream projects
can either be PR'd to Lean, or kept downstream if it also relies on Mathlib.
-/

namespace BitVec

variable {w : Nat}

/-!
## Injectivity
-/

theorem toNat_injective {n : Nat} : Function.Injective (BitVec.toNat : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toFin_injective {n : Nat} : Function.Injective (toFin : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-!
## Scalar Multiplication and Powers
Having instance of `SMul ℕ`, `SMul ℤ` and `Pow` are prerequisites for a `CommRing` instance
-/

instance : SMul ℕ (BitVec w) := ⟨fun x y => ofFin <| x • y.toFin⟩
instance : SMul ℤ (BitVec w) := ⟨fun x y => ofFin <| x • y.toFin⟩
lemma toFin_nsmul (n : ℕ) (x : BitVec w)  : toFin (n • x) = n • x.toFin := rfl
lemma toFin_zsmul (z : ℤ) (x : BitVec w)  : toFin (z • x) = z • x.toFin := rfl
lemma toFin_pow (x : BitVec w) (n : ℕ)    : toFin (x ^ n) = x.toFin ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, BitVec.pow_succ, pow_succ]

/-!
## Ring
-/

-- Verify that the `HPow` instance from Lean agrees definitionally with the instance via `Monoid`.
example : @instHPow (Fin (2 ^ w)) ℕ Monoid.toNatPow = Lean.Grind.Fin.instHPowFinNatOfNeZero := rfl

instance : CommSemiring (BitVec w) :=
  toFin_injective.commSemiring _
    rfl /- toFin_zero -/
    rfl /- toFin_one -/
    toFin_add
    toFin_mul
    toFin_nsmul
    (by convert toFin_pow)
    (fun _ => rfl) /- toFin_natCast -/
-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`

@[simp] theorem ofFin_neg {x : Fin (2 ^ w)} : ofFin (-x) = -(ofFin x) := by
  rfl

@[simp, norm_cast] theorem ofFin_natCast (n : ℕ) : ofFin (n : Fin (2^w)) = (n : BitVec w) := by
  rfl

@[simp, norm_cast] theorem toFin_natCast (n : ℕ) : toFin (n : BitVec w) = (n : Fin (2^w)) := by
  rfl

@[simp] theorem toInt_ofFin {w : Nat} (x : Fin (2^w)) :
    (BitVec.ofFin x).toInt = Int.bmod x (2^w) := by
  simp [toInt_eq_toNat_bmod]

@[simp] theorem toNat_intCast {w : Nat} (x : Int) : (x : BitVec w).toNat = (x % 2^w).toNat := by
  change (BitVec.ofInt w x).toNat = _
  simp

@[simp] theorem toInt_intCast {w : Nat} (x : Int) : (x : BitVec w).toInt = Int.bmod x (2^w) := by
  rw [toInt_eq_toNat_bmod, toNat_intCast, Int.natCast_toNat_eq_self.mpr]
  · have h : (2 ^ w : Int) = (2 ^ w : Nat) := by simp
    rw [h, Int.emod_bmod]
  · apply Int.emod_nonneg
    exact pow_ne_zero w (by decide)

theorem _root_.Fin.intCast_def {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n) = if 0 ≤ x then Fin.ofNat' n x.natAbs else -Fin.ofNat' n x.natAbs := rfl

theorem _root_.Int.emod_natAbs_of_nonneg {x : Int} (h : 0 ≤ x) {n : Nat} :
    x.natAbs % n = (x % n).toNat := by
  match x, h with
  | (x : ℕ), _ => rw [Int.natAbs_natCast, Int.ofNat_mod_ofNat, Int.toNat_natCast]

theorem _root_.Int.emod_natAbs_of_neg {x : Int} (h : x < 0) {n : Nat} (w : n ≠ 0) :
    x.natAbs % n = if (n : Int) ∣ x then 0 else n - (x % n).toNat := by
  match x, h with
  | -(x + 1 : ℕ), _ =>
    rw [Int.natAbs_neg]
    rw [Int.natAbs_cast]
    rw [Int.neg_emod]
    simp only [Int.dvd_neg]
    simp only [Int.natCast_dvd_natCast]
    split <;> rename_i h
    · rw [Nat.mod_eq_zero_of_dvd h]
    · rw [← Int.natCast_emod]
      simp only [Int.natAbs_natCast]
      have : (x + 1) % n < n := Nat.mod_lt (x + 1) (by omega)
      omega

theorem _root_.Fin.val_neg {n : Nat} [NeZero n] (x : Fin n) :
    (-x).val = if x = 0 then 0 else n - x.val := by
  change (n - ↑x) % n = _
  split <;> rename_i h
  · simp_all
  · rw [Nat.mod_eq_of_lt]
    have := Fin.val_ne_zero_iff.mpr h
    omega

@[simp] theorem _root_.Fin.val_intCast {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n).val = (x % n).toNat := by
  rw [Fin.intCast_def]
  split <;> rename_i h
  · simp [Int.emod_natAbs_of_nonneg h]
  · simp only [Fin.ofNat'_eq_cast, Fin.val_neg, Fin.natCast_eq_zero, Fin.val_natCast]
    split <;> rename_i h
    · rw [← Int.natCast_dvd] at h
      rw [Int.emod_eq_zero_of_dvd h, Int.toNat_zero]
    · rw [Int.emod_natAbs_of_neg (by omega) (NeZero.ne n), if_neg (by rwa [← Int.natCast_dvd] at h)]
      have : x % n < n := Int.emod_lt_of_pos x (by have := NeZero.ne n; omega)
      omega

theorem ofFin_intCast (z : ℤ) : ofFin (z : Fin (2^w)) = ↑z := by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    apply BitVec.eq_of_toInt_eq
    rw [toInt_ofFin, Fin.val_intCast, Int.natCast_pow, Nat.cast_ofNat, Int.ofNat_toNat,
      toInt_intCast]
    rw [Int.max_eq_left]
    · have h : (2 ^ (w + 1) : Int) = (2 ^ (w + 1) : Nat) := by simp
      rw [h, Int.emod_bmod]
    · refine Int.emod_nonneg z ?_
      exact pow_ne_zero (w + 1) (by decide)

theorem toFin_intCast (z : ℤ) : toFin (z : BitVec w) = z := by
  apply toFin_inj.mpr <| (ofFin_intCast z).symm

instance : CommRing (BitVec w) :=
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg toFin_sub
    toFin_nsmul toFin_zsmul toFin_pow toFin_natCast toFin_intCast

/-- The ring `BitVec m` is isomorphic to `Fin (2 ^ m)`. -/
@[simps]
def equivFin {m : ℕ} : BitVec m ≃+* Fin (2 ^ m) where
  toFun a := a.toFin
  invFun a := ofFin a
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end BitVec
