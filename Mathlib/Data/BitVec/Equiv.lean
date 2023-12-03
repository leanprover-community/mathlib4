/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.BitVec.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
This file shows various equivalences of bitvectors.
-/

namespace Std.BitVec

variable {w : ℕ}

/-- Equivalence between `BitVec w` and `Fin (2 ^ w)` -/
def finEquiv : BitVec w ≃ Fin (2 ^ w) where
  toFun     := toFin
  invFun    := ofFin
  left_inv  := ofFin_toFin
  right_inv := toFin_ofFin

/-- Equivalence between `BitVec w` and `Fin w → Bool`, composed from existing equivalences,
rather than defined through `Std.BitVec.getLsb'` and `Std.BitVec.ofLEFn` -/
def finFunctionEquiv : BitVec w ≃ (Fin w → Bool) := calc
  BitVec w  ≃ (Fin (2 ^ w))     := finEquiv
  _         ≃ (Fin w -> Fin 2)  := finFunctionFinEquiv.symm
  _         ≃ (Fin w -> Bool)   := Equiv.arrowCongr (.refl _) finTwoEquiv

-- TODO: I think this lemma exists in some PR already
@[simp] lemma val_toFin (x : BitVec w) : x.toFin.val = x.toNat := rfl

/-- Create a bitvector from a function that maps index `i` to the `i`-th least significant bit -/
def ofLEFn {w} (f : Fin w → Bool) : BitVec w :=
  match w with
  | 0   => .nil
  | w+1 => .concat (ofLEFn <| Fin.tail f) (f ⟨0, Nat.succ_pos w⟩)

@[simp] lemma ofLEFn_zero (f : Fin 0 → Bool) : ofLEFn f = nil := rfl

@[simp] lemma ofLEFn_cons {w} (b : Bool) (f : Fin w → Bool) :
    ofLEFn (Fin.cons b f) = concat (ofLEFn f) b :=
  rfl

theorem coe_finFunctionEquiv_eq_getLsb' :
    (finFunctionEquiv : BitVec w → Fin w → Bool) = getLsb' := by
  funext x i
  simp only [finFunctionEquiv, finEquiv, finFunctionFinEquiv, ← Nat.shiftRight_eq_div_pow,
    Equiv.instTransSortSortSortEquivEquivEquiv_trans, finTwoEquiv, Matrix.vecCons, Matrix.vecEmpty,
    Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.ofRightInverseOfCardLE_symm_apply, val_toFin,
    Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp.right_id,
    Function.comp_apply, getLsb', getLsb, Nat.testBit, Nat.and_one_is_mod]
  cases (x.toNat >>> i.val).mod_two_eq_zero_or_one
  next h => simp only [h, Fin.zero_eta, Fin.cons_zero, bne_self_eq_false]
  next h => simp only [h, Fin.mk_one, Fin.cons_one, Fin.cons_zero]; rfl

private theorem Bool.val_rec_eq_toNat (b : Bool) :
    (Fin.val (n:=2) <| Bool.rec 0 1 b) = b.toNat := by
  cases b <;> rfl

set_option linter.deprecated false in
private theorem Nat.mul_two_eq_bit (x : ℕ) :
    x * 2 = Nat.bit false x := by
  simp only [mul_two, Nat.bit_false, bit0]

theorem Bool.toNat_eq_bit_zero (b : Bool) : b.toNat = Nat.bit b 0 := by
  cases b <;> rfl

theorem coe_symm_finFunctionEquiv_eq_ofLEFn :
    (finFunctionEquiv.symm : (Fin w → Bool) → BitVec w) = ofLEFn := by
  funext f
  induction' f using Fin.consInduction with w x₀ f ih
  · rw [ofLEFn_zero]; rfl
  · simp only [finFunctionEquiv, finEquiv, finFunctionFinEquiv, Fin.univ_succ,
      Finset.cons_eq_insert, Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Fin.exists_succ_eq_iff, ne_eq, not_true_eq_false, not_false_eq_true, Finset.sum_insert,
      Fin.val_zero, pow_zero, mul_one, Finset.sum_map, Fin.val_succ, pow_succ,
      Equiv.instTransSortSortSortEquivEquivEquiv_trans, finTwoEquiv, Equiv.symm_trans_apply,
      Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.symm_symm, Equiv.ofRightInverseOfCardLE_apply,
      Equiv.arrowCongr_apply, Equiv.coe_fn_symm_mk, Equiv.coe_refl, Function.comp.right_id,
      Function.comp_apply, Fin.cons_zero, Bool.val_rec_eq_toNat, Fin.cons_succ,
      Nat.add_comm x₀.toNat, ofLEFn_cons, concat, HAppend.hAppend, append, HOr.hOr, OrOp.or,
      BitVec.or, shiftLeftZeroExtend, ← ih, toNat_ofFin, Nat.shiftLeft_eq_mul_pow,
      zeroExtend', toNat_ofBool, ofFin.injEq, Fin.mk.injEq, Finset.sum_mul]
    rw [Nat.add_eq_lor_of_and_eq_zero ?_]
    · congr! 2; ring
    · have (i) : (f i).toNat * (2 * 2 ^ i.val) = (f i).toNat * 2 ^ i.val * 2 := by ring
      simp only [this, ← Finset.sum_mul]
      simp only [Bool.toNat_eq_bit_zero, Nat.mul_two_eq_bit, Nat.land_bit, Bool.false_and,
        Nat.and_zero, Nat.bit_eq_zero, and_self]

@[simp]
theorem ofLEFn_getLsb' (x : BitVec w) : ofLEFn (x.getLsb') = x := by
  simp [← coe_symm_finFunctionEquiv_eq_ofLEFn, ← coe_finFunctionEquiv_eq_getLsb']

@[simp]
theorem getLsb'_ofLEFn (f : Fin w → Bool) : getLsb' (ofLEFn f) = f := by
  simp [← coe_symm_finFunctionEquiv_eq_ofLEFn, ← coe_finFunctionEquiv_eq_getLsb']



end Std.BitVec
