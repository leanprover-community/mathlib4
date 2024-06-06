/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic.FinCases

#align_import data.zmod.basic from "leanprover-community/mathlib"@"74ad1c88c77e799d2fea62801d1dbbd698cff1b7"

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `ZMod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivalence class

* `valMinAbs` returns the integer closest to zero in the equivalence class.

* A coercion `cast` is defined from `ZMod n` into any ring.
This is a ring hom if the ring has characteristic dividing `n`

-/

assert_not_exists Submodule

open Function

namespace ZMod

instance charZero : CharZero (ZMod 0) := inferInstanceAs (CharZero ℤ)

/-- `val a` is a natural number defined as:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivalence class

See `ZMod.valMinAbs` for a variant that takes values in the integers.
-/
def val : ∀ {n : ℕ}, ZMod n → ℕ
  | 0 => Int.natAbs
  | n + 1 => ((↑) : Fin (n + 1) → ℕ)
#align zmod.val ZMod.val

theorem val_lt {n : ℕ} [NeZero n] (a : ZMod n) : a.val < n := by
  cases n
  · cases NeZero.ne 0 rfl
  exact Fin.is_lt a
#align zmod.val_lt ZMod.val_lt

theorem val_le {n : ℕ} [NeZero n] (a : ZMod n) : a.val ≤ n :=
  a.val_lt.le
#align zmod.val_le ZMod.val_le

@[simp]
theorem val_zero : ∀ {n}, (0 : ZMod n).val = 0
  | 0 => rfl
  | _ + 1 => rfl
#align zmod.val_zero ZMod.val_zero

@[simp]
theorem val_one' : (1 : ZMod 0).val = 1 :=
  rfl
#align zmod.val_one' ZMod.val_one'

@[simp]
theorem val_neg' {n : ZMod 0} : (-n).val = n.val :=
  Int.natAbs_neg n
#align zmod.val_neg' ZMod.val_neg'

@[simp]
theorem val_mul' {m n : ZMod 0} : (m * n).val = m.val * n.val :=
  Int.natAbs_mul m n
#align zmod.val_mul' ZMod.val_mul'

@[simp]
theorem val_natCast {n : ℕ} (a : ℕ) : (a : ZMod n).val = a % n := by
  cases n
  · rw [Nat.mod_zero]
    exact Int.natAbs_ofNat a
  · apply Fin.val_natCast
#align zmod.val_nat_cast ZMod.val_natCast

@[deprecated (since := "2024-04-17")]
alias val_nat_cast := val_natCast

theorem val_unit' {n : ZMod 0} : IsUnit n ↔ n.val = 1 := by
  simp only [val]
  rw [Int.isUnit_iff, Int.natAbs_eq_iff, Nat.cast_one]

lemma eq_one_of_isUnit_natCast {n : ℕ} (h : IsUnit (n : ZMod 0)) : n = 1 := by
  rw [← Nat.mod_zero n, ← val_natCast, val_unit'.mp h]

theorem val_natCast_of_lt {n a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rwa [val_natCast, Nat.mod_eq_of_lt]

@[deprecated (since := "2024-04-17")]
alias val_nat_cast_of_lt := val_natCast_of_lt

instance charP (n : ℕ) : CharP (ZMod n) n where
  cast_eq_zero_iff' := by
    intro k
    cases' n with n
    · simp [zero_dvd_iff, Int.natCast_eq_zero, Nat.zero_eq]
    · exact Fin.natCast_eq_zero

@[simp]
theorem addOrderOf_one (n : ℕ) : addOrderOf (1 : ZMod n) = n :=
  CharP.eq _ (CharP.addOrderOf_one _) (ZMod.charP n)
#align zmod.add_order_of_one ZMod.addOrderOf_one

/-- This lemma works in the case in which `ZMod n` is not infinite, i.e. `n ≠ 0`.  The version
where `a ≠ 0` is `addOrderOf_coe'`. -/
@[simp]
theorem addOrderOf_coe (a : ℕ) {n : ℕ} (n0 : n ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  cases' a with a
  · simp only [Nat.zero_eq, Nat.cast_zero, addOrderOf_zero, Nat.gcd_zero_right,
      Nat.pos_of_ne_zero n0, Nat.div_self]
  rw [← Nat.smul_one_eq_cast, addOrderOf_nsmul' _ a.succ_ne_zero, ZMod.addOrderOf_one]
#align zmod.add_order_of_coe ZMod.addOrderOf_coe

/-- This lemma works in the case in which `a ≠ 0`.  The version where
 `ZMod n` is not infinite, i.e. `n ≠ 0`, is `addOrderOf_coe`. -/
@[simp]
theorem addOrderOf_coe' {a : ℕ} (n : ℕ) (a0 : a ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rw [← Nat.smul_one_eq_cast, addOrderOf_nsmul' _ a0, ZMod.addOrderOf_one]
#align zmod.add_order_of_coe' ZMod.addOrderOf_coe'

/-- We have that `ringChar (ZMod n) = n`. -/
theorem ringChar_zmod_n (n : ℕ) : ringChar (ZMod n) = n := by
  rw [ringChar.eq_iff]
  exact ZMod.charP n
#align zmod.ring_char_zmod_n ZMod.ringChar_zmod_n

-- @[simp] -- Porting note (#10618): simp can prove this
theorem natCast_self (n : ℕ) : (n : ZMod n) = 0 :=
  CharP.cast_eq_zero (ZMod n) n
#align zmod.nat_cast_self ZMod.natCast_self

@[deprecated (since := "2024-04-17")]
alias nat_cast_self := natCast_self

@[simp]
theorem natCast_self' (n : ℕ) : (n + 1 : ZMod (n + 1)) = 0 := by
  rw [← Nat.cast_add_one, natCast_self (n + 1)]
#align zmod.nat_cast_self' ZMod.natCast_self'

@[deprecated (since := "2024-04-17")]
alias nat_cast_self' := natCast_self'

section UniversalProperty

variable {n : ℕ} {R : Type*}

section

variable [AddGroupWithOne R]

/-- Cast an integer modulo `n` to another semiring.
This function is a morphism if the characteristic of `R` divides `n`.
See `ZMod.castHom` for a bundled version. -/
def cast : ∀ {n : ℕ}, ZMod n → R
  | 0 => Int.cast
  | _ + 1 => fun i => i.val
#align zmod.cast ZMod.cast


@[simp]
theorem cast_zero : (cast (0 : ZMod n) : R) = 0 := by
  delta ZMod.cast
  cases n
  · exact Int.cast_zero
  · simp
#align zmod.cast_zero ZMod.cast_zero

theorem cast_eq_val [NeZero n] (a : ZMod n) : (cast a : R) = a.val := by
  cases n
  · cases NeZero.ne 0 rfl
  rfl
#align zmod.cast_eq_val ZMod.cast_eq_val

variable {S : Type*} [AddGroupWithOne S]

@[simp]
theorem _root_.Prod.fst_zmod_cast (a : ZMod n) : (cast a : R × S).fst = cast a := by
  cases n
  · rfl
  · simp [ZMod.cast]
#align prod.fst_zmod_cast Prod.fst_zmod_cast

@[simp]
theorem _root_.Prod.snd_zmod_cast (a : ZMod n) : (cast a : R × S).snd = cast a := by
  cases n
  · rfl
  · simp [ZMod.cast]
#align prod.snd_zmod_cast Prod.snd_zmod_cast

end

/-- So-named because the coercion is `Nat.cast` into `ZMod`. For `Nat.cast` into an arbitrary ring,
see `ZMod.natCast_val`. -/
theorem natCast_zmod_val {n : ℕ} [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.cast_val_eq_self
#align zmod.nat_cast_zmod_val ZMod.natCast_zmod_val

@[deprecated (since := "2024-04-17")]
alias nat_cast_zmod_val := natCast_zmod_val

theorem natCast_rightInverse [NeZero n] : Function.RightInverse val ((↑) : ℕ → ZMod n) :=
  natCast_zmod_val
#align zmod.nat_cast_right_inverse ZMod.natCast_rightInverse

@[deprecated (since := "2024-04-17")]
alias nat_cast_rightInverse := natCast_rightInverse

theorem natCast_zmod_surjective [NeZero n] : Function.Surjective ((↑) : ℕ → ZMod n) :=
  natCast_rightInverse.surjective
#align zmod.nat_cast_zmod_surjective ZMod.natCast_zmod_surjective

@[deprecated (since := "2024-04-17")]
alias nat_cast_zmod_surjective := natCast_zmod_surjective

/-- So-named because the outer coercion is `Int.cast` into `ZMod`. For `Int.cast` into an arbitrary
ring, see `ZMod.intCast_cast`. -/
@[norm_cast]
theorem intCast_zmod_cast (a : ZMod n) : ((cast a : ℤ) : ZMod n) = a := by
  cases n
  · simp [ZMod.cast, ZMod]
  · dsimp [ZMod.cast, ZMod]
    erw [Int.cast_natCast, Fin.cast_val_eq_self]
#align zmod.int_cast_zmod_cast ZMod.intCast_zmod_cast

@[deprecated (since := "2024-04-17")]
alias int_cast_zmod_cast := intCast_zmod_cast

theorem intCast_rightInverse : Function.RightInverse (cast : ZMod n → ℤ) ((↑) : ℤ → ZMod n) :=
  intCast_zmod_cast
#align zmod.int_cast_right_inverse ZMod.intCast_rightInverse

@[deprecated (since := "2024-04-17")]
alias int_cast_rightInverse := intCast_rightInverse

theorem intCast_surjective : Function.Surjective ((↑) : ℤ → ZMod n) :=
  intCast_rightInverse.surjective
#align zmod.int_cast_surjective ZMod.intCast_surjective

@[deprecated (since := "2024-04-17")]
alias int_cast_surjective := intCast_surjective

theorem cast_id : ∀ (n) (i : ZMod n), (ZMod.cast i : ZMod n) = i
  | 0, _ => Int.cast_id
  | _ + 1, i => natCast_zmod_val i
#align zmod.cast_id ZMod.cast_id

@[simp]
theorem cast_id' : (ZMod.cast : ZMod n → ZMod n) = id :=
  funext (cast_id n)
#align zmod.cast_id' ZMod.cast_id'

variable (R) [Ring R]

/-- The coercions are respectively `Nat.cast` and `ZMod.cast`. -/
@[simp]
theorem natCast_comp_val [NeZero n] : ((↑) : ℕ → R) ∘ (val : ZMod n → ℕ) = cast := by
  cases n
  · cases NeZero.ne 0 rfl
  rfl
#align zmod.nat_cast_comp_val ZMod.natCast_comp_val

@[deprecated (since := "2024-04-17")]
alias nat_cast_comp_val := natCast_comp_val

/-- The coercions are respectively `Int.cast`, `ZMod.cast`, and `ZMod.cast`. -/
@[simp]
theorem intCast_comp_cast : ((↑) : ℤ → R) ∘ (cast : ZMod n → ℤ) = cast := by
  cases n
  · exact congr_arg (Int.cast ∘ ·) ZMod.cast_id'
  · ext
    simp [ZMod, ZMod.cast]
#align zmod.int_cast_comp_cast ZMod.intCast_comp_cast

@[deprecated (since := "2024-04-17")]
alias int_cast_comp_cast := intCast_comp_cast

variable {R}

@[simp]
theorem natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = cast i :=
  congr_fun (natCast_comp_val R) i
#align zmod.nat_cast_val ZMod.natCast_val

@[deprecated (since := "2024-04-17")]
alias nat_cast_val := natCast_val

@[simp]
theorem intCast_cast (i : ZMod n) : ((cast i : ℤ) : R) = cast i :=
  congr_fun (intCast_comp_cast R) i
#align zmod.int_cast_cast ZMod.intCast_cast

@[deprecated (since := "2024-04-17")]
alias int_cast_cast := intCast_cast

theorem cast_add_eq_ite {n : ℕ} (a b : ZMod n) :
    (cast (a + b) : ℤ) =
      if (n : ℤ) ≤ cast a + cast b then (cast a + cast b - n : ℤ) else cast a + cast b := by
  cases' n with n
  · simp; rfl
  change Fin (n + 1) at a b
  change ((((a + b) : Fin (n + 1)) : ℕ) : ℤ) = if ((n + 1 : ℕ) : ℤ) ≤ (a : ℕ) + b then _ else _
  simp only [Fin.val_add_eq_ite, Int.ofNat_succ, Int.ofNat_le]
  norm_cast
  split_ifs with h
  · rw [Nat.cast_sub h]
    congr
  · rfl
#align zmod.coe_add_eq_ite ZMod.cast_add_eq_ite

section CharDvd

/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/


variable {m : ℕ} [CharP R m]

@[simp]
theorem cast_one (h : m ∣ n) : (cast (1 : ZMod n) : R) = 1 := by
  cases' n with n
  · exact Int.cast_one
  show ((1 % (n + 1) : ℕ) : R) = 1
  cases n;
  · rw [Nat.dvd_one] at h
    subst m
    have : Subsingleton R := CharP.CharOne.subsingleton
    apply Subsingleton.elim
  rw [Nat.mod_eq_of_lt]
  · exact Nat.cast_one
  exact Nat.lt_of_sub_eq_succ rfl
#align zmod.cast_one ZMod.cast_one

theorem cast_add (h : m ∣ n) (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b := by
  cases n
  · apply Int.cast_add
  symm
  dsimp [ZMod, ZMod.cast]
  erw [← Nat.cast_add, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)
#align zmod.cast_add ZMod.cast_add

theorem cast_mul (h : m ∣ n) (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b := by
  cases n
  · apply Int.cast_mul
  symm
  dsimp [ZMod, ZMod.cast]
  erw [← Nat.cast_mul, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)
#align zmod.cast_mul ZMod.cast_mul

/-- The canonical ring homomorphism from `ZMod n` to a ring of characteristic dividing `n`.

See also `ZMod.lift` for a generalized version working in `AddGroup`s.
-/
def castHom (h : m ∣ n) (R : Type*) [Ring R] [CharP R m] : ZMod n →+* R where
  toFun := cast
  map_zero' := cast_zero
  map_one' := cast_one h
  map_add' := cast_add h
  map_mul' := cast_mul h
#align zmod.cast_hom ZMod.castHom

@[simp]
theorem castHom_apply {h : m ∣ n} (i : ZMod n) : castHom h R i = cast i :=
  rfl
#align zmod.cast_hom_apply ZMod.castHom_apply

@[simp]
theorem cast_sub (h : m ∣ n) (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b :=
  (castHom h R).map_sub a b
#align zmod.cast_sub ZMod.cast_sub

@[simp]
theorem cast_neg (h : m ∣ n) (a : ZMod n) : (cast (-a : ZMod n) : R) = -(cast a) :=
  (castHom h R).map_neg a
#align zmod.cast_neg ZMod.cast_neg

@[simp]
theorem cast_pow (h : m ∣ n) (a : ZMod n) (k : ℕ) : (cast (a ^ k : ZMod n) : R) = (cast a) ^ k :=
  (castHom h R).map_pow a k
#align zmod.cast_pow ZMod.cast_pow

@[simp, norm_cast]
theorem cast_natCast (h : m ∣ n) (k : ℕ) : (cast (k : ZMod n) : R) = k :=
  map_natCast (castHom h R) k
#align zmod.cast_nat_cast ZMod.cast_natCast

@[deprecated (since := "2024-04-17")]
alias cast_nat_cast := cast_natCast

@[simp, norm_cast]
theorem cast_intCast (h : m ∣ n) (k : ℤ) : (cast (k : ZMod n) : R) = k :=
  map_intCast (castHom h R) k
#align zmod.cast_int_cast ZMod.cast_intCast

@[deprecated (since := "2024-04-17")]
alias cast_int_cast := cast_intCast

end CharDvd

section CharEq

/-! Some specialised simp lemmas which apply when `R` has characteristic `n`. -/


variable [CharP R n]

@[simp]
theorem cast_one' : (cast (1 : ZMod n) : R) = 1 :=
  cast_one dvd_rfl
#align zmod.cast_one' ZMod.cast_one'

@[simp]
theorem cast_add' (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b :=
  cast_add dvd_rfl a b
#align zmod.cast_add' ZMod.cast_add'

@[simp]
theorem cast_mul' (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b :=
  cast_mul dvd_rfl a b
#align zmod.cast_mul' ZMod.cast_mul'

@[simp]
theorem cast_sub' (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b :=
  cast_sub dvd_rfl a b
#align zmod.cast_sub' ZMod.cast_sub'

@[simp]
theorem cast_pow' (a : ZMod n) (k : ℕ) : (cast (a ^ k : ZMod n) : R) = (cast a : R) ^ k :=
  cast_pow dvd_rfl a k
#align zmod.cast_pow' ZMod.cast_pow'

@[simp, norm_cast]
theorem cast_natCast' (k : ℕ) : (cast (k : ZMod n) : R) = k :=
  cast_natCast dvd_rfl k
#align zmod.cast_nat_cast' ZMod.cast_natCast'

@[deprecated (since := "2024-04-17")]
alias cast_nat_cast' := cast_natCast'

@[simp, norm_cast]
theorem cast_intCast' (k : ℤ) : (cast (k : ZMod n) : R) = k :=
  cast_intCast dvd_rfl k
#align zmod.cast_int_cast' ZMod.cast_intCast'

@[deprecated (since := "2024-04-17")]
alias cast_int_cast' := cast_intCast'

variable (R)

theorem castHom_injective : Function.Injective (ZMod.castHom (dvd_refl n) R) := by
  rw [injective_iff_map_eq_zero]
  intro x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, CharP.intCast_eq_zero_iff R n, CharP.intCast_eq_zero_iff (ZMod n) n]
  exact id
#align zmod.cast_hom_injective ZMod.castHom_injective

theorem castHom_bijective [Fintype R] (h : Fintype.card R = n) :
    Function.Bijective (ZMod.castHom (dvd_refl n) R) := by
  haveI : NeZero n :=
    ⟨by
      intro hn
      rw [hn] at h
      exact (Fintype.card_eq_zero_iff.mp h).elim' 0⟩
  rw [Fintype.bijective_iff_injective_and_card, ZMod.card, h, eq_self_iff_true, and_true_iff]
  apply ZMod.castHom_injective
#align zmod.cast_hom_bijective ZMod.castHom_bijective

/-- The unique ring isomorphism between `ZMod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
noncomputable def ringEquiv [Fintype R] (h : Fintype.card R = n) : ZMod n ≃+* R :=
  RingEquiv.ofBijective _ (ZMod.castHom_bijective R h)
#align zmod.ring_equiv ZMod.ringEquiv

/-- The identity between `ZMod m` and `ZMod n` when `m = n`, as a ring isomorphism. -/
def ringEquivCongr {m n : ℕ} (h : m = n) : ZMod m ≃+* ZMod n := by
  cases' m with m <;> cases' n with n
  · exact RingEquiv.refl _
  · exfalso
    exact n.succ_ne_zero h.symm
  · exfalso
    exact m.succ_ne_zero h
  · exact
      { finCongr h with
        map_mul' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.coe_cast, Fin.coe_mul, Fin.coe_mul, Fin.coe_cast, Fin.coe_cast, ← h]
        map_add' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.coe_cast, Fin.val_add, Fin.val_add, Fin.coe_cast, Fin.coe_cast, ← h] }
#align zmod.ring_equiv_congr ZMod.ringEquivCongr

@[simp] lemma ringEquivCongr_refl (a : ℕ) : ringEquivCongr (rfl : a = a) = .refl _ := by
  cases a <;> rfl

lemma ringEquivCongr_refl_apply {a : ℕ} (x : ZMod a) : ringEquivCongr rfl x = x := by
  rw [ringEquivCongr_refl]
  rfl

lemma ringEquivCongr_symm {a b : ℕ} (hab : a = b) :
    (ringEquivCongr hab).symm = ringEquivCongr hab.symm := by
  subst hab
  cases a <;> rfl

lemma ringEquivCongr_trans {a b c : ℕ} (hab : a = b) (hbc : b = c) :
    (ringEquivCongr hab).trans (ringEquivCongr hbc) = ringEquivCongr (hab.trans hbc) := by
  subst hab hbc
  cases a <;> rfl

lemma ringEquivCongr_ringEquivCongr_apply {a b c : ℕ} (hab : a = b) (hbc : b = c) (x : ZMod a) :
    ringEquivCongr hbc (ringEquivCongr hab x) = ringEquivCongr (hab.trans hbc) x := by
  rw [← ringEquivCongr_trans hab hbc]
  rfl

lemma ringEquivCongr_val {a b : ℕ} (h : a = b) (x : ZMod a) :
    ZMod.val ((ZMod.ringEquivCongr h) x) = ZMod.val x := by
  subst h
  cases a <;> rfl

lemma ringEquivCongr_intCast {a b : ℕ} (h : a = b) (z : ℤ) :
    ZMod.ringEquivCongr h z = z := by
  subst h
  cases a <;> rfl

@[deprecated (since := "2024-05-25")] alias int_coe_ringEquivCongr := ringEquivCongr_intCast

end CharEq

end UniversalProperty

theorem intCast_eq_intCast_iff (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c] :=
  CharP.intCast_eq_intCast (ZMod c) c
#align zmod.int_coe_eq_int_coe_iff ZMod.intCast_eq_intCast_iff

@[deprecated (since := "2024-04-17")]
alias int_cast_eq_int_cast_iff := intCast_eq_intCast_iff

theorem intCast_eq_intCast_iff' (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.intCast_eq_intCast_iff a b c
#align zmod.int_coe_eq_int_coe_iff' ZMod.intCast_eq_intCast_iff'

@[deprecated (since := "2024-04-17")]
alias int_cast_eq_int_cast_iff' := intCast_eq_intCast_iff'

theorem natCast_eq_natCast_iff (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c] := by
  simpa [Int.natCast_modEq_iff] using ZMod.intCast_eq_intCast_iff a b c
#align zmod.nat_coe_eq_nat_coe_iff ZMod.natCast_eq_natCast_iff

@[deprecated (since := "2024-04-17")]
alias nat_cast_eq_nat_cast_iff := natCast_eq_natCast_iff

theorem natCast_eq_natCast_iff' (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.natCast_eq_natCast_iff a b c
#align zmod.nat_coe_eq_nat_coe_iff' ZMod.natCast_eq_natCast_iff'

@[deprecated (since := "2024-04-17")]
alias nat_cast_eq_nat_cast_iff' := natCast_eq_natCast_iff'

theorem intCast_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : ZMod b) = 0 ↔ (b : ℤ) ∣ a := by
  rw [← Int.cast_zero, ZMod.intCast_eq_intCast_iff, Int.modEq_zero_iff_dvd]
#align zmod.int_coe_zmod_eq_zero_iff_dvd ZMod.intCast_zmod_eq_zero_iff_dvd

@[deprecated (since := "2024-04-17")]
alias int_cast_zmod_eq_zero_iff_dvd := intCast_zmod_eq_zero_iff_dvd

theorem intCast_eq_intCast_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : ZMod c) = ↑b ↔ ↑c ∣ b - a := by
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
#align zmod.int_coe_eq_int_coe_iff_dvd_sub ZMod.intCast_eq_intCast_iff_dvd_sub

@[deprecated (since := "2024-04-17")]
alias int_cast_eq_int_cast_iff_dvd_sub := intCast_eq_intCast_iff_dvd_sub

theorem natCast_zmod_eq_zero_iff_dvd (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a := by
  rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]
#align zmod.nat_coe_zmod_eq_zero_iff_dvd ZMod.natCast_zmod_eq_zero_iff_dvd

@[deprecated (since := "2024-04-17")]
alias nat_cast_zmod_eq_zero_iff_dvd := natCast_zmod_eq_zero_iff_dvd

theorem val_intCast {n : ℕ} (a : ℤ) [NeZero n] : ↑(a : ZMod n).val = a % n := by
  have hle : (0 : ℤ) ≤ ↑(a : ZMod n).val := Int.natCast_nonneg _
  have hlt : ↑(a : ZMod n).val < (n : ℤ) := Int.ofNat_lt.mpr (ZMod.val_lt a)
  refine (Int.emod_eq_of_lt hle hlt).symm.trans ?_
  rw [← ZMod.intCast_eq_intCast_iff', Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
#align zmod.val_int_cast ZMod.val_intCast

@[deprecated (since := "2024-04-17")]
alias val_int_cast := val_intCast

theorem coe_intCast {n : ℕ} (a : ℤ) : cast (a : ZMod n) = a % n := by
  cases n
  · rw [Int.ofNat_zero, Int.emod_zero, Int.cast_id]; rfl
  · rw [← val_intCast, val]; rfl
#align zmod.coe_int_cast ZMod.coe_intCast

@[deprecated (since := "2024-04-17")]
alias coe_int_cast := coe_intCast

@[simp]
theorem val_neg_one (n : ℕ) : (-1 : ZMod n.succ).val = n := by
  dsimp [val, Fin.coe_neg]
  cases n
  · simp [Nat.mod_one]
  · dsimp [ZMod, ZMod.cast]
    rw [Fin.coe_neg_one]
#align zmod.val_neg_one ZMod.val_neg_one

/-- `-1 : ZMod n` lifts to `n - 1 : R`. This avoids the characteristic assumption in `cast_neg`. -/
theorem cast_neg_one {R : Type*} [Ring R] (n : ℕ) : cast (-1 : ZMod n) = (n - 1 : R) := by
  cases' n with n
  · dsimp [ZMod, ZMod.cast]; simp
  · rw [← natCast_val, val_neg_one, Nat.cast_succ, add_sub_cancel_right]
#align zmod.cast_neg_one ZMod.cast_neg_one

theorem cast_sub_one {R : Type*} [Ring R] {n : ℕ} (k : ZMod n) :
    (cast (k - 1 : ZMod n) : R) = (if k = 0 then (n : R) else cast k) - 1 := by
  split_ifs with hk
  · rw [hk, zero_sub, ZMod.cast_neg_one]
  · cases n
    · dsimp [ZMod, ZMod.cast]
      rw [Int.cast_sub, Int.cast_one]
    · dsimp [ZMod, ZMod.cast, ZMod.val]
      rw [Fin.coe_sub_one, if_neg]
      · rw [Nat.cast_sub, Nat.cast_one]
        rwa [Fin.ext_iff, Fin.val_zero, ← Ne, ← Nat.one_le_iff_ne_zero] at hk
      · exact hk
#align zmod.cast_sub_one ZMod.cast_sub_one

theorem natCast_eq_iff (p : ℕ) (n : ℕ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_natCast, Nat.mod_add_div]
  · rintro ⟨k, rfl⟩
    rw [Nat.cast_add, natCast_zmod_val, Nat.cast_mul, natCast_self, zero_mul,
      add_zero]
#align zmod.nat_coe_zmod_eq_iff ZMod.natCast_eq_iff

theorem intCast_eq_iff (p : ℕ) (n : ℤ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_intCast, Int.emod_add_ediv]
  · rintro ⟨k, rfl⟩
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, natCast_val,
      ZMod.natCast_self, zero_mul, add_zero, cast_id]
#align zmod.int_coe_zmod_eq_iff ZMod.intCast_eq_iff

@[deprecated (since := "2024-05-25")] alias nat_coe_zmod_eq_iff := natCast_eq_iff
@[deprecated (since := "2024-05-25")] alias int_coe_zmod_eq_iff := intCast_eq_iff

@[push_cast, simp]
theorem intCast_mod (a : ℤ) (b : ℕ) : ((a % b : ℤ) : ZMod b) = (a : ZMod b) := by
  rw [ZMod.intCast_eq_intCast_iff]
  apply Int.mod_modEq
#align zmod.int_cast_mod ZMod.intCast_mod

@[deprecated (since := "2024-04-17")]
alias int_cast_mod := intCast_mod

theorem ker_intCastAddHom (n : ℕ) :
    (Int.castAddHom (ZMod n)).ker = AddSubgroup.zmultiples (n : ℤ) := by
  ext
  rw [Int.mem_zmultiples_iff, AddMonoidHom.mem_ker, Int.coe_castAddHom,
    intCast_zmod_eq_zero_iff_dvd]
#align zmod.ker_int_cast_add_hom ZMod.ker_intCastAddHom

@[deprecated (since := "2024-04-17")]
alias ker_int_castAddHom := ker_intCastAddHom

theorem cast_injective_of_le {m n : ℕ} [nzm : NeZero m] (h : m ≤ n) :
    Function.Injective (@cast (ZMod n) _ m) := by
  cases m with
  | zero => cases nzm; simp_all
  | succ m =>
    rintro ⟨x, hx⟩ ⟨y, hy⟩ f
    simp only [cast, val, natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (hx.trans_le h), Nat.mod_eq_of_lt (hy.trans_le h)] at f
    apply Fin.ext
    exact f

theorem cast_zmod_eq_zero_iff_of_le {m n : ℕ} [NeZero m] (h : m ≤ n) (a : ZMod m) :
    (cast a : ZMod n) = 0 ↔ a = 0 := by
  rw [← ZMod.cast_zero (n := m)]
  exact Injective.eq_iff' (cast_injective_of_le h) rfl

-- Porting note: commented
-- unseal Int.NonNeg

@[simp]
theorem natCast_toNat (p : ℕ) : ∀ {z : ℤ} (_h : 0 ≤ z), (z.toNat : ZMod p) = z
  | (n : ℕ), _h => by simp only [Int.cast_natCast, Int.toNat_natCast]
  | Int.negSucc n, h => by simp at h
#align zmod.nat_cast_to_nat ZMod.natCast_toNat

@[deprecated (since := "2024-04-17")]
alias nat_cast_toNat := natCast_toNat

theorem val_injective (n : ℕ) [NeZero n] : Function.Injective (val : ZMod n → ℕ) := by
  cases n
  · cases NeZero.ne 0 rfl
  intro a b h
  dsimp [ZMod]
  ext
  exact h
#align zmod.val_injective ZMod.val_injective

theorem val_one_eq_one_mod (n : ℕ) : (1 : ZMod n).val = 1 % n := by
  rw [← Nat.cast_one, val_natCast]
#align zmod.val_one_eq_one_mod ZMod.val_one_eq_one_mod

theorem val_one (n : ℕ) [Fact (1 < n)] : (1 : ZMod n).val = 1 := by
  rw [val_one_eq_one_mod]
  exact Nat.mod_eq_of_lt Fact.out
#align zmod.val_one ZMod.val_one

theorem val_add {n : ℕ} [NeZero n] (a b : ZMod n) : (a + b).val = (a.val + b.val) % n := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.val_add
#align zmod.val_add ZMod.val_add

theorem val_add_of_lt {n : ℕ} {a b : ZMod n} (h : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  have : NeZero n := by constructor; rintro rfl; simp at h
  rw [ZMod.val_add, Nat.mod_eq_of_lt h]

theorem val_add_val_of_le {n : ℕ} [NeZero n] {a b : ZMod n} (h : n ≤ a.val + b.val) :
    a.val + b.val = (a + b).val + n := by
  rw [val_add, Nat.add_mod_add_of_le_add_mod, Nat.mod_eq_of_lt (val_lt _),
    Nat.mod_eq_of_lt (val_lt _)]
  rwa [Nat.mod_eq_of_lt (val_lt _), Nat.mod_eq_of_lt (val_lt _)]

theorem val_add_of_le {n : ℕ} [NeZero n] {a b : ZMod n} (h : n ≤ a.val + b.val) :
    (a + b).val = a.val + b.val - n := by
  rw [val_add_val_of_le h]
  exact eq_tsub_of_add_eq rfl

theorem val_add_le {n : ℕ} (a b : ZMod n) : (a + b).val ≤ a.val + b.val := by
  cases n
  · simp [ZMod.val]; apply Int.natAbs_add_le
  · simp [ZMod.val_add]; apply Nat.mod_le

theorem val_mul {n : ℕ} (a b : ZMod n) : (a * b).val = a.val * b.val % n := by
  cases n
  · rw [Nat.mod_zero]
    apply Int.natAbs_mul
  · apply Fin.val_mul
#align zmod.val_mul ZMod.val_mul

theorem val_mul_le {n : ℕ} (a b : ZMod n) : (a * b).val ≤ a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_le

theorem val_mul_of_lt {n : ℕ} {a b : ZMod n} (h : a.val * b.val < n) :
    (a * b).val = a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_eq_of_lt h

instance nontrivial (n : ℕ) [Fact (1 < n)] : Nontrivial (ZMod n) :=
  ⟨⟨0, 1, fun h =>
      zero_ne_one <|
        calc
          0 = (0 : ZMod n).val := by rw [val_zero]
          _ = (1 : ZMod n).val := congr_arg ZMod.val h
          _ = 1 := val_one n
          ⟩⟩
#align zmod.nontrivial ZMod.nontrivial

instance nontrivial' : Nontrivial (ZMod 0) := by
  delta ZMod; infer_instance
#align zmod.nontrivial' ZMod.nontrivial'

/-- The inversion on `ZMod n`.
It is setup in such a way that `a * a⁻¹` is equal to `gcd a.val n`.
In particular, if `a` is coprime to `n`, and hence a unit, `a * a⁻¹ = 1`. -/
def inv : ∀ n : ℕ, ZMod n → ZMod n
  | 0, i => Int.sign i
  | n + 1, i => Nat.gcdA i.val (n + 1)
#align zmod.inv ZMod.inv

instance (n : ℕ) : Inv (ZMod n) :=
  ⟨inv n⟩

@[nolint unusedHavesSuffices]
theorem inv_zero : ∀ n : ℕ, (0 : ZMod n)⁻¹ = 0
  | 0 => Int.sign_zero
  | n + 1 =>
    show (Nat.gcdA _ (n + 1) : ZMod (n + 1)) = 0 by
      rw [val_zero]
      unfold Nat.gcdA Nat.xgcd Nat.xgcdAux
      rfl
#align zmod.inv_zero ZMod.inv_zero

theorem mul_inv_eq_gcd {n : ℕ} (a : ZMod n) : a * a⁻¹ = Nat.gcd a.val n := by
  cases' n with n
  · dsimp [ZMod] at a ⊢
    calc
      _ = a * Int.sign a := rfl
      _ = a.natAbs := by rw [Int.mul_sign]
      _ = a.natAbs.gcd 0 := by rw [Nat.gcd_zero_right]
  · calc
      a * a⁻¹ = a * a⁻¹ + n.succ * Nat.gcdB (val a) n.succ := by
        rw [natCast_self, zero_mul, add_zero]
      _ = ↑(↑a.val * Nat.gcdA (val a) n.succ + n.succ * Nat.gcdB (val a) n.succ) := by
        push_cast
        rw [natCast_zmod_val]
        rfl
      _ = Nat.gcd a.val n.succ := by rw [← Nat.gcd_eq_gcd_ab a.val n.succ]; rfl
#align zmod.mul_inv_eq_gcd ZMod.mul_inv_eq_gcd

@[simp]
theorem natCast_mod (a : ℕ) (n : ℕ) : ((a % n : ℕ) : ZMod n) = a := by
  conv =>
      rhs
      rw [← Nat.mod_add_div a n]
  simp
#align zmod.nat_cast_mod ZMod.natCast_mod

@[deprecated (since := "2024-04-17")]
alias nat_cast_mod := natCast_mod

theorem eq_iff_modEq_nat (n : ℕ) {a b : ℕ} : (a : ZMod n) = b ↔ a ≡ b [MOD n] := by
  cases n
  · simp [Nat.ModEq, Int.natCast_inj, Nat.mod_zero]
  · rw [Fin.ext_iff, Nat.ModEq, ← val_natCast, ← val_natCast]
    exact Iff.rfl
#align zmod.eq_iff_modeq_nat ZMod.eq_iff_modEq_nat

theorem coe_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) :
    ((x : ZMod n) * (x : ZMod n)⁻¹) = 1 := by
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec] at h
  rw [mul_inv_eq_gcd, val_natCast, h, Nat.cast_one]
#align zmod.coe_mul_inv_eq_one ZMod.coe_mul_inv_eq_one

/-- `unitOfCoprime` makes an element of `(ZMod n)ˣ` given
  a natural number `x` and a proof that `x` is coprime to `n`  -/
def unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (ZMod n)ˣ :=
  ⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩
#align zmod.unit_of_coprime ZMod.unitOfCoprime

@[simp]
theorem coe_unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) :
    (unitOfCoprime x h : ZMod n) = x :=
  rfl
#align zmod.coe_unit_of_coprime ZMod.coe_unitOfCoprime

theorem val_coe_unit_coprime {n : ℕ} (u : (ZMod n)ˣ) : Nat.Coprime (u : ZMod n).val n := by
  cases' n with n
  · rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp
  apply Nat.coprime_of_mul_modEq_one ((u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1)).val
  have := Units.ext_iff.1 (mul_right_inv u)
  rw [Units.val_one] at this
  rw [← eq_iff_modEq_nat, Nat.cast_one, ← this]; clear this
  rw [← natCast_zmod_val ((u * u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1))]
  rw [Units.val_mul, val_mul, natCast_mod]
#align zmod.val_coe_unit_coprime ZMod.val_coe_unit_coprime

lemma isUnit_iff_coprime (m n : ℕ) : IsUnit (m : ZMod n) ↔ m.Coprime n := by
  refine ⟨fun H ↦ ?_, fun H ↦ (unitOfCoprime m H).isUnit⟩
  have H' := val_coe_unit_coprime H.unit
  rw [IsUnit.unit_spec, val_natCast m, Nat.coprime_iff_gcd_eq_one] at H'
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, ← H']
  exact Nat.gcd_rec n m

lemma isUnit_prime_iff_not_dvd {n p : ℕ} (hp : p.Prime) : IsUnit (p : ZMod n) ↔ ¬p ∣ n := by
  rw [isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp]

lemma isUnit_prime_of_not_dvd {n p : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) : IsUnit (p : ZMod n) :=
  (isUnit_prime_iff_not_dvd hp).mpr h

@[simp]
theorem inv_coe_unit {n : ℕ} (u : (ZMod n)ˣ) : (u : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ) := by
  have := congr_arg ((↑) : ℕ → ZMod n) (val_coe_unit_coprime u)
  rw [← mul_inv_eq_gcd, Nat.cast_one] at this
  let u' : (ZMod n)ˣ := ⟨u, (u : ZMod n)⁻¹, this, by rwa [mul_comm]⟩
  have h : u = u' := by
    apply Units.ext
    rfl
  rw [h]
  rfl
#align zmod.inv_coe_unit ZMod.inv_coe_unit

theorem mul_inv_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a * a⁻¹ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit, u.mul_inv]
#align zmod.mul_inv_of_unit ZMod.mul_inv_of_unit

theorem inv_mul_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_of_unit a h]
#align zmod.inv_mul_of_unit ZMod.inv_mul_of_unit

-- TODO: If we changed `⁻¹` so that `ZMod n` is always a `DivisionMonoid`,
-- then we could use the general lemma `inv_eq_of_mul_eq_one`
protected theorem inv_eq_of_mul_eq_one (n : ℕ) (a b : ZMod n) (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_of_unit a ⟨⟨a, b, h, mul_comm a b ▸ h⟩, rfl⟩) h

-- TODO: this equivalence is true for `ZMod 0 = ℤ`, but needs to use different functions.
/-- Equivalence between the units of `ZMod n` and
the subtype of terms `x : ZMod n` for which `x.val` is coprime to `n` -/
def unitsEquivCoprime {n : ℕ} [NeZero n] : (ZMod n)ˣ ≃ { x : ZMod n // Nat.Coprime x.val n } where
  toFun x := ⟨x, val_coe_unit_coprime x⟩
  invFun x := unitOfCoprime x.1.val x.2
  left_inv := fun ⟨_, _, _, _⟩ => Units.ext (natCast_zmod_val _)
  right_inv := fun ⟨_, _⟩ => by simp
#align zmod.units_equiv_coprime ZMod.unitsEquivCoprime

/-- The **Chinese remainder theorem**. For a pair of coprime natural numbers, `m` and `n`,
  the rings `ZMod (m * n)` and `ZMod m × ZMod n` are isomorphic.

See `Ideal.quotientInfRingEquivPiQuotient` for the Chinese remainder theorem for ideals in any
ring.
-/
def chineseRemainder {m n : ℕ} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
  let to_fun : ZMod (m * n) → ZMod m × ZMod n :=
    ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)
  let inv_fun : ZMod m × ZMod n → ZMod (m * n) := fun x =>
    if m * n = 0 then
      if m = 1 then cast (RingHom.snd _ (ZMod n) x) else cast (RingHom.fst (ZMod m) _ x)
    else Nat.chineseRemainder h x.1.val x.2.val
  have inv : Function.LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun :=
    if hmn0 : m * n = 0 then by
      rcases h.eq_of_mul_eq_zero hmn0 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · intro x; rfl
        · rintro ⟨x, y⟩
          fin_cases y
          simp [to_fun, inv_fun, castHom, Prod.ext_iff, eq_iff_true_of_subsingleton]
      · constructor
        · intro x; rfl
        · rintro ⟨x, y⟩
          fin_cases x
          simp [to_fun, inv_fun, castHom, Prod.ext_iff, eq_iff_true_of_subsingleton]
    else by
      haveI : NeZero (m * n) := ⟨hmn0⟩
      haveI : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
      haveI : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
      have left_inv : Function.LeftInverse inv_fun to_fun := by
        intro x
        dsimp only [to_fun, inv_fun, ZMod.castHom_apply]
        conv_rhs => rw [← ZMod.natCast_zmod_val x]
        rw [if_neg hmn0, ZMod.eq_iff_modEq_nat, ← Nat.modEq_and_modEq_iff_modEq_mul h,
          Prod.fst_zmod_cast, Prod.snd_zmod_cast]
        refine
          ⟨(Nat.chineseRemainder h (cast x : ZMod m).val (cast x : ZMod n).val).2.left.trans ?_,
            (Nat.chineseRemainder h (cast x : ZMod m).val (cast x : ZMod n).val).2.right.trans ?_⟩
        · rw [← ZMod.eq_iff_modEq_nat, ZMod.natCast_zmod_val, ZMod.natCast_val]
        · rw [← ZMod.eq_iff_modEq_nat, ZMod.natCast_zmod_val, ZMod.natCast_val]
      exact ⟨left_inv, left_inv.rightInverse_of_card_le (by simp)⟩
  { toFun := to_fun,
    invFun := inv_fun,
    map_mul' := RingHom.map_mul _
    map_add' := RingHom.map_add _
    left_inv := inv.1
    right_inv := inv.2 }
#align zmod.chinese_remainder ZMod.chineseRemainder

lemma subsingleton_iff {n : ℕ} : Subsingleton (ZMod n) ↔ n = 1 := by
  constructor
  · obtain (_ | _ | n) := n
    · simpa [ZMod] using not_subsingleton _
    · simp [ZMod]
    · simpa [ZMod] using not_subsingleton _
  · rintro rfl
    infer_instance

lemma nontrivial_iff {n : ℕ} : Nontrivial (ZMod n) ↔ n ≠ 1 := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]

-- todo: this can be made a `Unique` instance.
instance subsingleton_units : Subsingleton (ZMod 2)ˣ :=
  ⟨by decide⟩
#align zmod.subsingleton_units ZMod.subsingleton_units

@[simp]
theorem add_self_eq_zero_iff_eq_zero {n : ℕ} (hn : Odd n) {a : ZMod n} :
    a + a = 0 ↔ a = 0 := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, ← Nat.prime_two.coprime_iff_not_dvd] at hn
  rw [← mul_two, ← @Nat.cast_two (ZMod n), ← ZMod.coe_unitOfCoprime 2 hn, Units.mul_left_eq_zero]

theorem ne_neg_self {n : ℕ} (hn : Odd n) {a : ZMod n} (ha : a ≠ 0) : a ≠ -a := by
  rwa [Ne, eq_neg_iff_add_eq_zero, add_self_eq_zero_iff_eq_zero hn]
#align zmod.ne_neg_self ZMod.ne_neg_self

theorem neg_one_ne_one {n : ℕ} [Fact (2 < n)] : (-1 : ZMod n) ≠ 1 :=
  CharP.neg_one_ne_one (ZMod n) n
#align zmod.neg_one_ne_one ZMod.neg_one_ne_one

theorem neg_eq_self_mod_two (a : ZMod 2) : -a = a := by
  fin_cases a <;> apply Fin.ext <;> simp [Fin.coe_neg, Int.natMod]; rfl
#align zmod.neg_eq_self_mod_two ZMod.neg_eq_self_mod_two

@[simp]
theorem natAbs_mod_two (a : ℤ) : (a.natAbs : ZMod 2) = a := by
  cases a
  · simp only [Int.natAbs_ofNat, Int.cast_natCast, Int.ofNat_eq_coe]
  · simp only [neg_eq_self_mod_two, Nat.cast_succ, Int.natAbs, Int.cast_negSucc]
#align zmod.nat_abs_mod_two ZMod.natAbs_mod_two

@[simp]
theorem val_eq_zero : ∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
  | 0, a => Int.natAbs_eq_zero
  | n + 1, a => by
    rw [Fin.ext_iff]
    exact Iff.rfl
#align zmod.val_eq_zero ZMod.val_eq_zero

theorem val_ne_zero {n : ℕ} (a : ZMod n) : a.val ≠ 0 ↔ a ≠ 0 :=
  (val_eq_zero a).not

theorem neg_eq_self_iff {n : ℕ} (a : ZMod n) : -a = a ↔ a = 0 ∨ 2 * a.val = n := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul]
  cases n
  · erw [@mul_eq_zero ℤ, @mul_eq_zero ℕ, val_eq_zero]
    exact
      ⟨fun h => h.elim (by simp) Or.inl, fun h =>
        Or.inr (h.elim id fun h => h.elim (by simp) id)⟩
  conv_lhs =>
    rw [← a.natCast_zmod_val, ← Nat.cast_two, ← Nat.cast_mul, natCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨m, he⟩
    cases' m with m
    · erw [mul_zero, mul_eq_zero] at he
      rcases he with (⟨⟨⟩⟩ | he)
      exact Or.inl (a.val_eq_zero.1 he)
    cases m
    · right
      rwa [show 0 + 1 = 1 from rfl, mul_one] at he
    refine (a.val_lt.not_le <| Nat.le_of_mul_le_mul_left ?_ zero_lt_two).elim
    rw [he, mul_comm]
    apply Nat.mul_le_mul_left
    erw [Nat.succ_le_succ_iff, Nat.succ_le_succ_iff]; simp
  · rintro (rfl | h)
    · rw [val_zero, mul_zero]
      apply dvd_zero
    · rw [h]
#align zmod.neg_eq_self_iff ZMod.neg_eq_self_iff

theorem val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rw [val_natCast, Nat.mod_eq_of_lt h]
#align zmod.val_cast_of_lt ZMod.val_cast_of_lt

theorem neg_val' {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = (n - a.val) % n :=
  calc
    (-a).val = val (-a) % n := by rw [Nat.mod_eq_of_lt (-a).val_lt]
    _ = (n - val a) % n :=
      Nat.ModEq.add_right_cancel' _
        (by
          rw [Nat.ModEq, ← val_add, add_left_neg, tsub_add_cancel_of_le a.val_le, Nat.mod_self,
            val_zero])
#align zmod.neg_val' ZMod.neg_val'

theorem neg_val {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = if a = 0 then 0 else n - a.val := by
  rw [neg_val']
  by_cases h : a = 0; · rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_self]
  rw [if_neg h]
  apply Nat.mod_eq_of_lt
  apply Nat.sub_lt (NeZero.pos n)
  contrapose! h
  rwa [Nat.le_zero, val_eq_zero] at h
#align zmod.neg_val ZMod.neg_val

theorem val_neg_of_ne_zero {n : ℕ} [nz : NeZero n] (a : ZMod n) [na : NeZero a] :
    (- a).val = n - a.val := by simp_all [neg_val a, na.out]

theorem val_sub {n : ℕ} [NeZero n] {a b : ZMod n} (h : b.val ≤ a.val) :
    (a - b).val = a.val - b.val := by
  by_cases hb : b = 0
  · cases hb; simp
  · have : NeZero b := ⟨hb⟩
    rw [sub_eq_add_neg, val_add, val_neg_of_ne_zero, ← Nat.add_sub_assoc (le_of_lt (val_lt _)),
      add_comm, Nat.add_sub_assoc h, Nat.add_mod_left]
    apply Nat.mod_eq_of_lt (tsub_lt_of_lt (val_lt _))

theorem val_cast_eq_val_of_lt {m n : ℕ} [nzm : NeZero m] {a : ZMod m}
    (h : a.val < n) : (a.cast : ZMod n).val = a.val := by
  have nzn : NeZero n := by constructor; rintro rfl; simp at h
  cases m with
  | zero => cases nzm; simp_all
  | succ m =>
    cases n with
    | zero => cases nzn; simp_all
    | succ n => exact Fin.val_cast_of_lt h

theorem cast_cast_zmod_of_le {m n : ℕ} [hm : NeZero m] (h : m ≤ n) (a : ZMod m) :
    (cast (cast a : ZMod n) : ZMod m) = a := by
  have : NeZero n := ⟨((Nat.zero_lt_of_ne_zero hm.out).trans_le h).ne'⟩
  rw [cast_eq_val, val_cast_eq_val_of_lt (a.val_lt.trans_le h), natCast_zmod_val]

/-- `valMinAbs x` returns the integer in the same equivalence class as `x` that is closest to `0`,
  The result will be in the interval `(-n/2, n/2]`. -/
def valMinAbs : ∀ {n : ℕ}, ZMod n → ℤ
  | 0, x => x
  | n@(_ + 1), x => if x.val ≤ n / 2 then x.val else (x.val : ℤ) - n
#align zmod.val_min_abs ZMod.valMinAbs

@[simp]
theorem valMinAbs_def_zero (x : ZMod 0) : valMinAbs x = x :=
  rfl
#align zmod.val_min_abs_def_zero ZMod.valMinAbs_def_zero

theorem valMinAbs_def_pos {n : ℕ} [NeZero n] (x : ZMod n) :
    valMinAbs x = if x.val ≤ n / 2 then (x.val : ℤ) else x.val - n := by
  cases n
  · cases NeZero.ne 0 rfl
  · rfl
#align zmod.val_min_abs_def_pos ZMod.valMinAbs_def_pos

@[simp, norm_cast]
theorem coe_valMinAbs : ∀ {n : ℕ} (x : ZMod n), (x.valMinAbs : ZMod n) = x
  | 0, x => Int.cast_id
  | k@(n + 1), x => by
    rw [valMinAbs_def_pos]
    split_ifs
    · rw [Int.cast_natCast, natCast_zmod_val]
    · rw [Int.cast_sub, Int.cast_natCast, natCast_zmod_val, Int.cast_natCast, natCast_self,
        sub_zero]
#align zmod.coe_val_min_abs ZMod.coe_valMinAbs

theorem injective_valMinAbs {n : ℕ} : (valMinAbs : ZMod n → ℤ).Injective :=
  Function.injective_iff_hasLeftInverse.2 ⟨_, coe_valMinAbs⟩
#align zmod.injective_val_min_abs ZMod.injective_valMinAbs

theorem _root_.Nat.le_div_two_iff_mul_two_le {n m : ℕ} : m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n := by
  rw [Nat.le_div_iff_mul_le zero_lt_two, ← Int.ofNat_le, Int.ofNat_mul, Nat.cast_two]
#align nat.le_div_two_iff_mul_two_le Nat.le_div_two_iff_mul_two_le

theorem valMinAbs_nonneg_iff {n : ℕ} [NeZero n] (x : ZMod n) : 0 ≤ x.valMinAbs ↔ x.val ≤ n / 2 := by
  rw [valMinAbs_def_pos]; split_ifs with h
  · exact iff_of_true (Nat.cast_nonneg _) h
  · exact iff_of_false (sub_lt_zero.2 <| Int.ofNat_lt.2 x.val_lt).not_le h
#align zmod.val_min_abs_nonneg_iff ZMod.valMinAbs_nonneg_iff

theorem valMinAbs_mul_two_eq_iff {n : ℕ} (a : ZMod n) : a.valMinAbs * 2 = n ↔ 2 * a.val = n := by
  cases' n with n
  · simp
  by_cases h : a.val ≤ n.succ / 2
  · dsimp [valMinAbs]
    rw [if_pos h, ← Int.natCast_inj, Nat.cast_mul, Nat.cast_two, mul_comm]
  apply iff_of_false _ (mt _ h)
  · intro he
    rw [← a.valMinAbs_nonneg_iff, ← mul_nonneg_iff_left_nonneg_of_pos, he] at h
    exacts [h (Nat.cast_nonneg _), zero_lt_two]
  · rw [mul_comm]
    exact fun h => (Nat.le_div_iff_mul_le zero_lt_two).2 h.le
#align zmod.val_min_abs_mul_two_eq_iff ZMod.valMinAbs_mul_two_eq_iff

theorem valMinAbs_mem_Ioc {n : ℕ} [NeZero n] (x : ZMod n) :
    x.valMinAbs * 2 ∈ Set.Ioc (-n : ℤ) n := by
  simp_rw [valMinAbs_def_pos, Nat.le_div_two_iff_mul_two_le]; split_ifs with h
  · refine ⟨(neg_lt_zero.2 <| mod_cast NeZero.pos n).trans_le (mul_nonneg ?_ ?_), h⟩
    exacts [Nat.cast_nonneg _, zero_le_two]
  · refine ⟨?_, le_trans (mul_nonpos_of_nonpos_of_nonneg ?_ zero_le_two) <| Nat.cast_nonneg _⟩
    · linarith only [h]
    · rw [sub_nonpos, Int.ofNat_le]
      exact x.val_lt.le
#align zmod.val_min_abs_mem_Ioc ZMod.valMinAbs_mem_Ioc

theorem valMinAbs_spec {n : ℕ} [NeZero n] (x : ZMod n) (y : ℤ) :
    x.valMinAbs = y ↔ x = y ∧ y * 2 ∈ Set.Ioc (-n : ℤ) n :=
  ⟨by
    rintro rfl
    exact ⟨x.coe_valMinAbs.symm, x.valMinAbs_mem_Ioc⟩, fun h =>
      by
        rw [← sub_eq_zero]
        apply @Int.eq_zero_of_abs_lt_dvd n
        · rw [← intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, coe_valMinAbs, h.1, sub_self]
        rw [← mul_lt_mul_right (@zero_lt_two ℤ _ _ _ _ _)]
        nth_rw 1 [← abs_eq_self.2 (@zero_le_two ℤ _ _ _ _)]
        rw [← abs_mul, sub_mul, abs_lt]
        constructor <;> linarith only [x.valMinAbs_mem_Ioc.1, x.valMinAbs_mem_Ioc.2, h.2.1, h.2.2]⟩
#align zmod.val_min_abs_spec ZMod.valMinAbs_spec

theorem natAbs_valMinAbs_le {n : ℕ} [NeZero n] (x : ZMod n) : x.valMinAbs.natAbs ≤ n / 2 := by
  rw [Nat.le_div_two_iff_mul_two_le]
  cases' x.valMinAbs.natAbs_eq with h h
  · rw [← h]
    exact x.valMinAbs_mem_Ioc.2
  · rw [← neg_le_neg_iff, ← neg_mul, ← h]
    exact x.valMinAbs_mem_Ioc.1.le
#align zmod.nat_abs_val_min_abs_le ZMod.natAbs_valMinAbs_le

@[simp]
theorem valMinAbs_zero : ∀ n, (0 : ZMod n).valMinAbs = 0
  | 0 => by simp only [valMinAbs_def_zero]
  | n + 1 => by simp only [valMinAbs_def_pos, if_true, Int.ofNat_zero, zero_le, val_zero]
#align zmod.val_min_abs_zero ZMod.valMinAbs_zero

@[simp]
theorem valMinAbs_eq_zero {n : ℕ} (x : ZMod n) : x.valMinAbs = 0 ↔ x = 0 := by
  cases' n with n
  · simp
  rw [← valMinAbs_zero n.succ]
  apply injective_valMinAbs.eq_iff
#align zmod.val_min_abs_eq_zero ZMod.valMinAbs_eq_zero

theorem natCast_natAbs_valMinAbs {n : ℕ} [NeZero n] (a : ZMod n) :
    (a.valMinAbs.natAbs : ZMod n) = if a.val ≤ (n : ℕ) / 2 then a else -a := by
  have : (a.val : ℤ) - n ≤ 0 := by
    erw [sub_nonpos, Int.ofNat_le]
    exact a.val_le
  rw [valMinAbs_def_pos]
  split_ifs
  · rw [Int.natAbs_ofNat, natCast_zmod_val]
  · rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos this, Int.cast_neg, Int.cast_sub,
      Int.cast_natCast, Int.cast_natCast, natCast_self, sub_zero, natCast_zmod_val]
#align zmod.nat_cast_nat_abs_val_min_abs ZMod.natCast_natAbs_valMinAbs

@[deprecated (since := "2024-04-17")]
alias nat_cast_natAbs_valMinAbs := natCast_natAbs_valMinAbs

theorem valMinAbs_neg_of_ne_half {n : ℕ} {a : ZMod n} (ha : 2 * a.val ≠ n) :
    (-a).valMinAbs = -a.valMinAbs := by
  cases' eq_zero_or_neZero n with h h
  · subst h
    rfl
  refine (valMinAbs_spec _ _).2 ⟨?_, ?_, ?_⟩
  · rw [Int.cast_neg, coe_valMinAbs]
  · rw [neg_mul, neg_lt_neg_iff]
    exact a.valMinAbs_mem_Ioc.2.lt_of_ne (mt a.valMinAbs_mul_two_eq_iff.1 ha)
  · linarith only [a.valMinAbs_mem_Ioc.1]
#align zmod.val_min_abs_neg_of_ne_half ZMod.valMinAbs_neg_of_ne_half

@[simp]
theorem natAbs_valMinAbs_neg {n : ℕ} (a : ZMod n) : (-a).valMinAbs.natAbs = a.valMinAbs.natAbs := by
  by_cases h2a : 2 * a.val = n
  · rw [a.neg_eq_self_iff.2 (Or.inr h2a)]
  · rw [valMinAbs_neg_of_ne_half h2a, Int.natAbs_neg]
#align zmod.nat_abs_val_min_abs_neg ZMod.natAbs_valMinAbs_neg

theorem val_eq_ite_valMinAbs {n : ℕ} [NeZero n] (a : ZMod n) :
    (a.val : ℤ) = a.valMinAbs + if a.val ≤ n / 2 then 0 else n := by
  rw [valMinAbs_def_pos]
  split_ifs <;> simp [add_zero, sub_add_cancel]
#align zmod.val_eq_ite_val_min_abs ZMod.val_eq_ite_valMinAbs

theorem prime_ne_zero (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rwa [← Nat.cast_zero, Ne, eq_iff_modEq_nat, Nat.modEq_zero_iff_dvd, ←
    hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]
#align zmod.prime_ne_zero ZMod.prime_ne_zero

variable {n a : ℕ}

theorem valMinAbs_natAbs_eq_min {n : ℕ} [hpos : NeZero n] (a : ZMod n) :
    a.valMinAbs.natAbs = min a.val (n - a.val) := by
  rw [valMinAbs_def_pos]
  split_ifs with h
  · rw [Int.natAbs_ofNat]
    symm
    apply
      min_eq_left (le_trans h (le_trans (Nat.half_le_of_sub_le_half _) (Nat.sub_le_sub_left h n)))
    rw [Nat.sub_sub_self (Nat.div_le_self _ _)]
  · rw [← Int.natAbs_neg, neg_sub, ← Nat.cast_sub a.val_le]
    symm
    apply
      min_eq_right
        (le_trans (le_trans (Nat.sub_le_sub_left (lt_of_not_ge h) n) (Nat.le_half_of_half_lt_sub _))
          (le_of_not_ge h))
    rw [Nat.sub_sub_self (Nat.div_lt_self (lt_of_le_of_ne' (Nat.zero_le _) hpos.1) one_lt_two)]
    apply Nat.lt_succ_self
#align zmod.val_min_abs_nat_abs_eq_min ZMod.valMinAbs_natAbs_eq_min

theorem valMinAbs_natCast_of_le_half (ha : a ≤ n / 2) : (a : ZMod n).valMinAbs = a := by
  cases n
  · simp
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt (ha.trans_lt <| Nat.div_lt_self' _ 0),
      ha]
#align zmod.val_min_abs_nat_cast_of_le_half ZMod.valMinAbs_natCast_of_le_half

theorem valMinAbs_natCast_of_half_lt (ha : n / 2 < a) (ha' : a < n) :
    (a : ZMod n).valMinAbs = a - n := by
  cases n
  · cases not_lt_bot ha'
  · simp [valMinAbs_def_pos, val_natCast, Nat.mod_eq_of_lt ha', ha.not_le]
#align zmod.val_min_abs_nat_cast_of_half_lt ZMod.valMinAbs_natCast_of_half_lt

-- Porting note: There was an extraneous `nat_` in the mathlib3 name
@[simp]
theorem valMinAbs_natCast_eq_self [NeZero n] : (a : ZMod n).valMinAbs = a ↔ a ≤ n / 2 := by
  refine ⟨fun ha => ?_, valMinAbs_natCast_of_le_half⟩
  rw [← Int.natAbs_ofNat a, ← ha]
  exact natAbs_valMinAbs_le a
#align zmod.val_min_nat_abs_nat_cast_eq_self ZMod.valMinAbs_natCast_eq_self

theorem natAbs_min_of_le_div_two (n : ℕ) (x y : ℤ) (he : (x : ZMod n) = y) (hl : x.natAbs ≤ n / 2) :
    x.natAbs ≤ y.natAbs := by
  rw [intCast_eq_intCast_iff_dvd_sub] at he
  obtain ⟨m, he⟩ := he
  rw [sub_eq_iff_eq_add] at he
  subst he
  obtain rfl | hm := eq_or_ne m 0
  · rw [mul_zero, zero_add]
  apply hl.trans
  rw [← add_le_add_iff_right x.natAbs]
  refine le_trans (le_trans ((add_le_add_iff_left _).2 hl) ?_) (Int.natAbs_sub_le _ _)
  rw [add_sub_cancel_right, Int.natAbs_mul, Int.natAbs_ofNat]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ <| Int.natAbs_pos.2 hm)
  rw [← mul_two]; apply Nat.div_mul_le_self
#align zmod.nat_abs_min_of_le_div_two ZMod.natAbs_min_of_le_div_two

theorem natAbs_valMinAbs_add_le {n : ℕ} (a b : ZMod n) :
    (a + b).valMinAbs.natAbs ≤ (a.valMinAbs + b.valMinAbs).natAbs := by
  cases' n with n
  · rfl
  apply natAbs_min_of_le_div_two n.succ
  · simp_rw [Int.cast_add, coe_valMinAbs]
  · apply natAbs_valMinAbs_le
#align zmod.nat_abs_val_min_abs_add_le ZMod.natAbs_valMinAbs_add_le

variable (p : ℕ) [Fact p.Prime]

private theorem mul_inv_cancel_aux (a : ZMod p) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  obtain ⟨k, rfl⟩ := natCast_zmod_surjective a
  apply coe_mul_inv_eq_one
  apply Nat.Coprime.symm
  rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]

/-- Field structure on `ZMod p` if `p` is prime. -/
instance instField : Field (ZMod p) where
  mul_inv_cancel := mul_inv_cancel_aux p
  inv_zero := inv_zero p
  nnqsmul := _
  qsmul := _

/-- `ZMod p` is an integral domain when `p` is prime. -/
instance (p : ℕ) [hp : Fact p.Prime] : IsDomain (ZMod p) := by
  -- We need `cases p` here in order to resolve which `CommRing` instance is being used.
  cases p
  · exact (Nat.not_prime_zero hp.out).elim
  exact @Field.isDomain (ZMod _) (inferInstanceAs (Field (ZMod _)))

end ZMod

theorem RingHom.ext_zmod {n : ℕ} {R : Type*} [Semiring R] (f g : ZMod n →+* R) : f = g := by
  ext a
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  let φ : ℤ →+* R := f.comp (Int.castRingHom (ZMod n))
  let ψ : ℤ →+* R := g.comp (Int.castRingHom (ZMod n))
  show φ k = ψ k
  rw [φ.ext_int ψ]
#align ring_hom.ext_zmod RingHom.ext_zmod

namespace ZMod

variable {n : ℕ} {R : Type*}

instance subsingleton_ringHom [Semiring R] : Subsingleton (ZMod n →+* R) :=
  ⟨RingHom.ext_zmod⟩
#align zmod.subsingleton_ring_hom ZMod.subsingleton_ringHom

instance subsingleton_ringEquiv [Semiring R] : Subsingleton (ZMod n ≃+* R) :=
  ⟨fun f g => by
    rw [RingEquiv.coe_ringHom_inj_iff]
    apply RingHom.ext_zmod _ _⟩
#align zmod.subsingleton_ring_equiv ZMod.subsingleton_ringEquiv

@[simp]
theorem ringHom_map_cast [Ring R] (f : R →+* ZMod n) (k : ZMod n) : f (cast k) = k := by
  cases n
  · dsimp [ZMod, ZMod.cast] at f k ⊢; simp
  · dsimp [ZMod, ZMod.cast] at f k ⊢
    erw [map_natCast, Fin.cast_val_eq_self]
#align zmod.ring_hom_map_cast ZMod.ringHom_map_cast

/-- Any ring homomorphism into `ZMod n` has a right inverse. -/
theorem ringHom_rightInverse [Ring R] (f : R →+* ZMod n) :
    Function.RightInverse (cast : ZMod n → R) f :=
  ringHom_map_cast f
#align zmod.ring_hom_right_inverse ZMod.ringHom_rightInverse

/-- Any ring homomorphism into `ZMod n` is surjective. -/
theorem ringHom_surjective [Ring R] (f : R →+* ZMod n) : Function.Surjective f :=
  (ringHom_rightInverse f).surjective
#align zmod.ring_hom_surjective ZMod.ringHom_surjective

@[simp]
lemma castHom_self : ZMod.castHom dvd_rfl (ZMod n) = RingHom.id (ZMod n) :=
  Subsingleton.elim _ _

@[simp]
lemma castHom_comp {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    (castHom hm (ZMod n)).comp (castHom hd (ZMod m)) = castHom (dvd_trans hm hd) (ZMod n) :=
  RingHom.ext_zmod _ _

section lift

variable (n) {A : Type*} [AddGroup A]

/-- The map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`. -/
--@[simps] -- Porting note: removed, simplified LHS of `lift_coe` to something worse.
def lift : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A) :=
  (Equiv.subtypeEquivRight <| by
        intro f
        rw [ker_intCastAddHom]
        constructor
        · rintro hf _ ⟨x, rfl⟩
          simp only [f.map_zsmul, zsmul_zero, f.mem_ker, hf]
        · intro h
          exact h (AddSubgroup.mem_zmultiples _)).trans <|
    (Int.castAddHom (ZMod n)).liftOfRightInverse cast intCast_zmod_cast
#align zmod.lift ZMod.lift

variable (f : { f : ℤ →+ A // f n = 0 })

@[simp]
theorem lift_coe (x : ℤ) : lift n f (x : ZMod n) = f.val x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _
#align zmod.lift_coe ZMod.lift_coe

theorem lift_castAddHom (x : ℤ) : lift n f (Int.castAddHom (ZMod n) x) = f.1 x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _
#align zmod.lift_cast_add_hom ZMod.lift_castAddHom

@[simp]
theorem lift_comp_coe : ZMod.lift n f ∘ ((↑) : ℤ → _) = f :=
  funext <| lift_coe _ _
#align zmod.lift_comp_coe ZMod.lift_comp_coe

@[simp]
theorem lift_comp_castAddHom : (ZMod.lift n f).comp (Int.castAddHom (ZMod n)) = f :=
  AddMonoidHom.ext <| lift_castAddHom _ _
#align zmod.lift_comp_cast_add_hom ZMod.lift_comp_castAddHom

end lift

end ZMod

/-- The range of `(m * · + k)` on natural numbers is the set of elements `≥ k` in the
residue class of `k` mod `m`. -/
lemma Nat.range_mul_add (m k : ℕ) :
    Set.range (fun n : ℕ ↦ m * n + k) = {n : ℕ | (n : ZMod m) = k ∧ k ≤ n} := by
  ext n
  simp only [Set.mem_range, Set.mem_setOf_eq]
  conv => enter [1, 1, y]; rw [add_comm, eq_comm]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨?_, le_iff_exists_add.mpr ⟨_, ha⟩⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  · simpa using congr_arg ((↑) : ℕ → ZMod m) ha
  · obtain ⟨a, ha⟩ := le_iff_exists_add.mp H₂
    simp only [ha, Nat.cast_add, add_right_eq_self, ZMod.natCast_zmod_eq_zero_iff_dvd] at H₁
    obtain ⟨b, rfl⟩ := H₁
    exact ⟨b, ha⟩
