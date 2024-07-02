/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Alex Keizer
-/
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Data.ZMod.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors which can only be stated in Mathlib or downstream
because they refer to other notions defined in Mathlib.

Please do not extend this file further: material about BitVec needed in downstream projects
can either be PR'd to Lean, or kept downstream if it also relies on Mathlib.
-/

namespace BitVec

variable {w v : Nat}

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
instance : Pow (BitVec w) ℕ  := ⟨fun x n => ofFin <| x.toFin ^ n⟩

lemma toFin_nsmul (n : ℕ) (x : BitVec w)  : toFin (n • x) = n • x.toFin := rfl
lemma toFin_zsmul (z : ℤ) (x : BitVec w)  : toFin (z • x) = z • x.toFin := rfl
lemma toFin_pow (x : BitVec w) (n : ℕ)    : toFin (x ^ n) = x.toFin ^ n := rfl

/-!
## Ring
-/

instance : CommSemiring (BitVec w) :=
  toFin_injective.commSemiring _
    rfl /- toFin_zero -/
    rfl /- toFin_one -/
    toFin_add
    toFin_mul
    toFin_nsmul
    toFin_pow
    (fun _ => rfl) /- toFin_natCast -/

#align bitvec BitVec
#align bitvec.zero BitVec.zero
#noalign bitvec.one
#align bitvec.cong BitVec.cast
#align bitvec.append BitVec.append
#align bitvec.shl BitVec.shiftLeft
#align bitvec.ushr BitVec.ushiftRight
#align bitvec.sshr BitVec.sshiftRight
#align bitvec.not BitVec.not
#align bitvec.and BitVec.and
#align bitvec.or BitVec.or
#align bitvec.xor BitVec.xor
#align bitvec.neg BitVec.neg
#align bitvec.adc BitVec.adc
#align bitvec.add BitVec.add
#noalign bitvec.sbb
#align bitvec.sub BitVec.sub
#align bitvec.mul BitVec.mul
#align bitvec.uborrow BitVec.ult
#align bitvec.ult BitVec.ult
#noalign bitvec.ugt
#align bitvec.ule BitVec.ule
#noalign bitvec.uge
#align bitvec.sborrow BitVec.slt
#align bitvec.slt BitVec.slt
#noalign bitvec.sgt
#align bitvec.sle BitVec.sle
#noalign bitvec.sge
#align bitvec.of_nat BitVec.ofNat
#noalign bitvec.add_lsb
#noalign bitvec.bits_to_nat
#align bitvec.to_nat BitVec.toNat
#align bitvec.of_fin BitVec.ofFin
#align bitvec.to_fin BitVec.toFin
#align bitvec.to_int BitVec.toInt
#noalign bitvec.bits_to_nat_to_list
#noalign bitvec.to_nat_append
#noalign bitvec.bits_to_nat_to_bool
-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`
#noalign bitvec.of_nat_succ
#align bitvec.to_nat_of_nat BitVec.toNat_ofNat
#noalign bitvec.of_fin_val
#noalign bitvec.add_lsb_eq_twice_add_one
#noalign bitvec.to_nat_eq_foldr_reverse
#align bitvec.to_nat_lt BitVec.toNat_lt
#noalign bitvec.add_lsb_div_two
#noalign bitvec.to_bool_add_lsb_mod_two
#noalign bitvec.to_fin_val
#noalign bitvec.to_fin_le_to_fin_of_le
#noalign bitvec.of_fin_le_of_fin_of_le
#noalign bitvec.to_fin_of_fin
#noalign bitvec.of_fin_to_fin

end BitVec
