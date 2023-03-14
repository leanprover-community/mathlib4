/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.zmod.basic
! leanprover-community/mathlib commit 297619ec79dedf23525458b6bf5bf35c736fd2b8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.Data.Nat.Parity
import Mathbin.Algebra.Group.ConjFinite
import Mathbin.Tactic.FinCases

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `zmod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : zmod 0` it is the absolute value of `a`
  - for `a : zmod n` with `0 < n` it is the least natural number in the equivalence class

* `val_min_abs` returns the integer closest to zero in the equivalence class.

* A coercion `cast` is defined from `zmod n` into any ring.
This is a ring hom if the ring has characteristic dividing `n`

-/


namespace ZMod

instance : CharZero (ZMod 0) :=
  (by infer_instance : CharZero ℤ)

/-- `val a` is a natural number defined as:
  - for `a : zmod 0` it is the absolute value of `a`
  - for `a : zmod n` with `0 < n` it is the least natural number in the equivalence class

See `zmod.val_min_abs` for a variant that takes values in the integers.
-/
def val : ∀ {n : ℕ}, ZMod n → ℕ
  | 0 => Int.natAbs
  | n + 1 => (coe : Fin (n + 1) → ℕ)
#align zmod.val ZMod.val

theorem val_lt {n : ℕ} [NeZero n] (a : ZMod n) : a.val < n :=
  by
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
  | n + 1 => rfl
#align zmod.val_zero ZMod.val_zero

@[simp]
theorem val_one' : (1 : ZMod 0).val = 1 :=
  rfl
#align zmod.val_one' ZMod.val_one'

@[simp]
theorem val_neg' {n : ZMod 0} : (-n).val = n.val := by simp [val]
#align zmod.val_neg' ZMod.val_neg'

@[simp]
theorem val_mul' {m n : ZMod 0} : (m * n).val = m.val * n.val := by simp [val, Int.natAbs_mul]
#align zmod.val_mul' ZMod.val_mul'

theorem val_nat_cast {n : ℕ} (a : ℕ) : (a : ZMod n).val = a % n :=
  by
  cases n
  · rw [Nat.mod_zero]
    exact Int.natAbs_ofNat a
  rw [← Fin.ofNat_eq_val]
  rfl
#align zmod.val_nat_cast ZMod.val_nat_cast

instance (n : ℕ) : CharP (ZMod n) n
    where cast_eq_zero_iff := by
    intro k
    cases n
    · simp only [zero_dvd_iff, Int.coe_nat_eq_zero]
    rw [Fin.eq_iff_veq]
    show (k : ZMod (n + 1)).val = (0 : ZMod (n + 1)).val ↔ _
    rw [val_nat_cast, val_zero, Nat.dvd_iff_mod_eq_zero]

@[simp]
theorem addOrderOf_one (n : ℕ) : addOrderOf (1 : ZMod n) = n :=
  CharP.eq _ (CharP.addOrderOf_one _) (ZMod.charP n)
#align zmod.add_order_of_one ZMod.addOrderOf_one

/-- This lemma works in the case in which `zmod n` is not infinite, i.e. `n ≠ 0`.  The version
where `a ≠ 0` is `add_order_of_coe'`. -/
@[simp]
theorem addOrderOf_coe (a : ℕ) {n : ℕ} (n0 : n ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a :=
  by
  cases a
  simp [Nat.pos_of_ne_zero n0]
  rw [← Nat.smul_one_eq_coe, addOrderOf_nsmul' _ a.succ_ne_zero, ZMod.addOrderOf_one]
#align zmod.add_order_of_coe ZMod.addOrderOf_coe

/-- This lemma works in the case in which `a ≠ 0`.  The version where
 `zmod n` is not infinite, i.e. `n ≠ 0`, is `add_order_of_coe`. -/
@[simp]
theorem addOrderOf_coe' {a : ℕ} (n : ℕ) (a0 : a ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rw [← Nat.smul_one_eq_coe, addOrderOf_nsmul' _ a0, ZMod.addOrderOf_one]
#align zmod.add_order_of_coe' ZMod.addOrderOf_coe'

/-- We have that `ring_char (zmod n) = n`. -/
theorem ringChar_zMod_n (n : ℕ) : ringChar (ZMod n) = n :=
  by
  rw [ringChar.eq_iff]
  exact ZMod.charP n
#align zmod.ring_char_zmod_n ZMod.ringChar_zMod_n

@[simp]
theorem nat_cast_self (n : ℕ) : (n : ZMod n) = 0 :=
  CharP.cast_eq_zero (ZMod n) n
#align zmod.nat_cast_self ZMod.nat_cast_self

@[simp]
theorem nat_cast_self' (n : ℕ) : (n + 1 : ZMod (n + 1)) = 0 := by
  rw [← Nat.cast_add_one, nat_cast_self (n + 1)]
#align zmod.nat_cast_self' ZMod.nat_cast_self'

section UniversalProperty

variable {n : ℕ} {R : Type _}

section

variable [AddGroupWithOne R]

/-- Cast an integer modulo `n` to another semiring.
This function is a morphism if the characteristic of `R` divides `n`.
See `zmod.cast_hom` for a bundled version. -/
def cast : ∀ {n : ℕ}, ZMod n → R
  | 0 => Int.cast
  | n + 1 => fun i => i.val
#align zmod.cast ZMod.cast

-- see Note [coercion into rings]
instance (priority := 900) (n : ℕ) : CoeTC (ZMod n) R :=
  ⟨cast⟩

@[simp]
theorem cast_zero : ((0 : ZMod n) : R) = 0 := by cases n <;> simp
#align zmod.cast_zero ZMod.cast_zero

theorem cast_eq_val [NeZero n] (a : ZMod n) : (a : R) = a.val :=
  by
  cases n
  · cases NeZero.ne 0 rfl
  rfl
#align zmod.cast_eq_val ZMod.cast_eq_val

variable {S : Type _} [AddGroupWithOne S]

@[simp]
theorem Prod.fst_zMod_cast (a : ZMod n) : (a : R × S).fst = a := by cases n <;> simp
#align prod.fst_zmod_cast Prod.fst_zMod_cast

@[simp]
theorem Prod.snd_zMod_cast (a : ZMod n) : (a : R × S).snd = a := by cases n <;> simp
#align prod.snd_zmod_cast Prod.snd_zMod_cast

end

/-- So-named because the coercion is `nat.cast` into `zmod`. For `nat.cast` into an arbitrary ring,
see `zmod.nat_cast_val`. -/
theorem nat_cast_zMod_val {n : ℕ} [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a :=
  by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.cast_val_eq_self
#align zmod.nat_cast_zmod_val ZMod.nat_cast_zMod_val

theorem nat_cast_rightInverse [NeZero n] : Function.RightInverse val (coe : ℕ → ZMod n) :=
  nat_cast_zMod_val
#align zmod.nat_cast_right_inverse ZMod.nat_cast_rightInverse

theorem nat_cast_zMod_surjective [NeZero n] : Function.Surjective (coe : ℕ → ZMod n) :=
  nat_cast_rightInverse.Surjective
#align zmod.nat_cast_zmod_surjective ZMod.nat_cast_zMod_surjective

/-- So-named because the outer coercion is `int.cast` into `zmod`. For `int.cast` into an arbitrary
ring, see `zmod.int_cast_cast`. -/
@[norm_cast]
theorem int_cast_zMod_cast (a : ZMod n) : ((a : ℤ) : ZMod n) = a :=
  by
  cases n
  · rw [Int.cast_id a, Int.cast_id a]
  · rw [coe_coe, Int.cast_ofNat, Fin.cast_val_eq_self]
#align zmod.int_cast_zmod_cast ZMod.int_cast_zMod_cast

theorem int_cast_rightInverse : Function.RightInverse (coe : ZMod n → ℤ) (coe : ℤ → ZMod n) :=
  int_cast_zMod_cast
#align zmod.int_cast_right_inverse ZMod.int_cast_rightInverse

theorem int_cast_surjective : Function.Surjective (coe : ℤ → ZMod n) :=
  int_cast_rightInverse.Surjective
#align zmod.int_cast_surjective ZMod.int_cast_surjective

@[norm_cast]
theorem cast_id : ∀ (n) (i : ZMod n), ↑i = i
  | 0, i => Int.cast_id i
  | n + 1, i => nat_cast_zMod_val i
#align zmod.cast_id ZMod.cast_id

@[simp]
theorem cast_id' : (coe : ZMod n → ZMod n) = id :=
  funext (cast_id n)
#align zmod.cast_id' ZMod.cast_id'

variable (R) [Ring R]

/-- The coercions are respectively `nat.cast` and `zmod.cast`. -/
@[simp]
theorem nat_cast_comp_val [NeZero n] : (coe : ℕ → R) ∘ (val : ZMod n → ℕ) = coe :=
  by
  cases n
  · cases NeZero.ne 0 rfl
  rfl
#align zmod.nat_cast_comp_val ZMod.nat_cast_comp_val

/-- The coercions are respectively `int.cast`, `zmod.cast`, and `zmod.cast`. -/
@[simp]
theorem int_cast_comp_cast : (coe : ℤ → R) ∘ (coe : ZMod n → ℤ) = coe :=
  by
  cases n
  · exact congr_arg ((· ∘ ·) Int.cast) ZMod.cast_id'
  · ext
    simp
#align zmod.int_cast_comp_cast ZMod.int_cast_comp_cast

variable {R}

@[simp]
theorem nat_cast_val [NeZero n] (i : ZMod n) : (i.val : R) = i :=
  congr_fun (nat_cast_comp_val R) i
#align zmod.nat_cast_val ZMod.nat_cast_val

@[simp]
theorem int_cast_cast (i : ZMod n) : ((i : ℤ) : R) = i :=
  congr_fun (int_cast_comp_cast R) i
#align zmod.int_cast_cast ZMod.int_cast_cast

theorem coe_add_eq_ite {n : ℕ} (a b : ZMod n) :
    (↑(a + b) : ℤ) = if (n : ℤ) ≤ a + b then a + b - n else a + b :=
  by
  cases n
  · simp
  simp only [coe_coe, Fin.val_add_eq_ite, ← Int.ofNat_add, ← Int.ofNat_succ, Int.ofNat_le]
  split_ifs with h
  · exact Int.ofNat_sub h
  · rfl
#align zmod.coe_add_eq_ite ZMod.coe_add_eq_ite

section CharDvd

/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/


variable {n} {m : ℕ} [CharP R m]

@[simp]
theorem cast_one (h : m ∣ n) : ((1 : ZMod n) : R) = 1 :=
  by
  cases n
  · exact Int.cast_one
  show ((1 % (n + 1) : ℕ) : R) = 1
  cases n;
  · rw [Nat.dvd_one] at h
    subst m
    apply Subsingleton.elim
  rw [Nat.mod_eq_of_lt]
  · exact Nat.cast_one
  exact Nat.lt_of_sub_eq_succ rfl
#align zmod.cast_one ZMod.cast_one

theorem cast_add (h : m ∣ n) (a b : ZMod n) : ((a + b : ZMod n) : R) = a + b :=
  by
  cases n
  · apply Int.cast_add
  simp only [coe_coe]
  symm
  erw [Fin.val_add, ← Nat.cast_add, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)
#align zmod.cast_add ZMod.cast_add

theorem cast_mul (h : m ∣ n) (a b : ZMod n) : ((a * b : ZMod n) : R) = a * b :=
  by
  cases n
  · apply Int.cast_mul
  simp only [coe_coe]
  symm
  erw [Fin.coe_mul, ← Nat.cast_mul, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)
#align zmod.cast_mul ZMod.cast_mul

/-- The canonical ring homomorphism from `zmod n` to a ring of characteristic `n`.

See also `zmod.lift` (in `data.zmod.quotient`) for a generalized version working in `add_group`s.
-/
def castHom (h : m ∣ n) (R : Type _) [Ring R] [CharP R m] : ZMod n →+* R
    where
  toFun := coe
  map_zero' := cast_zero
  map_one' := cast_one h
  map_add' := cast_add h
  map_mul' := cast_mul h
#align zmod.cast_hom ZMod.castHom

@[simp]
theorem castHom_apply {h : m ∣ n} (i : ZMod n) : castHom h R i = i :=
  rfl
#align zmod.cast_hom_apply ZMod.castHom_apply

@[simp, norm_cast]
theorem cast_sub (h : m ∣ n) (a b : ZMod n) : ((a - b : ZMod n) : R) = a - b :=
  (castHom h R).map_sub a b
#align zmod.cast_sub ZMod.cast_sub

@[simp, norm_cast]
theorem cast_neg (h : m ∣ n) (a : ZMod n) : ((-a : ZMod n) : R) = -a :=
  (castHom h R).map_neg a
#align zmod.cast_neg ZMod.cast_neg

@[simp, norm_cast]
theorem cast_pow (h : m ∣ n) (a : ZMod n) (k : ℕ) : ((a ^ k : ZMod n) : R) = a ^ k :=
  (castHom h R).map_pow a k
#align zmod.cast_pow ZMod.cast_pow

@[simp, norm_cast]
theorem cast_nat_cast (h : m ∣ n) (k : ℕ) : ((k : ZMod n) : R) = k :=
  map_natCast (castHom h R) k
#align zmod.cast_nat_cast ZMod.cast_nat_cast

@[simp, norm_cast]
theorem cast_int_cast (h : m ∣ n) (k : ℤ) : ((k : ZMod n) : R) = k :=
  map_intCast (castHom h R) k
#align zmod.cast_int_cast ZMod.cast_int_cast

end CharDvd

section CharEq

/-! Some specialised simp lemmas which apply when `R` has characteristic `n`. -/


variable [CharP R n]

@[simp]
theorem cast_one' : ((1 : ZMod n) : R) = 1 :=
  cast_one dvd_rfl
#align zmod.cast_one' ZMod.cast_one'

@[simp]
theorem cast_add' (a b : ZMod n) : ((a + b : ZMod n) : R) = a + b :=
  cast_add dvd_rfl a b
#align zmod.cast_add' ZMod.cast_add'

@[simp]
theorem cast_mul' (a b : ZMod n) : ((a * b : ZMod n) : R) = a * b :=
  cast_mul dvd_rfl a b
#align zmod.cast_mul' ZMod.cast_mul'

@[simp]
theorem cast_sub' (a b : ZMod n) : ((a - b : ZMod n) : R) = a - b :=
  cast_sub dvd_rfl a b
#align zmod.cast_sub' ZMod.cast_sub'

@[simp]
theorem cast_pow' (a : ZMod n) (k : ℕ) : ((a ^ k : ZMod n) : R) = a ^ k :=
  cast_pow dvd_rfl a k
#align zmod.cast_pow' ZMod.cast_pow'

@[simp, norm_cast]
theorem cast_nat_cast' (k : ℕ) : ((k : ZMod n) : R) = k :=
  cast_nat_cast dvd_rfl k
#align zmod.cast_nat_cast' ZMod.cast_nat_cast'

@[simp, norm_cast]
theorem cast_int_cast' (k : ℤ) : ((k : ZMod n) : R) = k :=
  cast_int_cast dvd_rfl k
#align zmod.cast_int_cast' ZMod.cast_int_cast'

variable (R)

theorem castHom_injective : Function.Injective (ZMod.castHom (dvd_refl n) R) :=
  by
  rw [injective_iff_map_eq_zero]
  intro x
  obtain ⟨k, rfl⟩ := ZMod.int_cast_surjective x
  rw [map_intCast, CharP.int_cast_eq_zero_iff R n, CharP.int_cast_eq_zero_iff (ZMod n) n]
  exact id
#align zmod.cast_hom_injective ZMod.castHom_injective

theorem castHom_bijective [Fintype R] (h : Fintype.card R = n) :
    Function.Bijective (ZMod.castHom (dvd_refl n) R) :=
  by
  haveI : NeZero n :=
    ⟨by
      intro hn
      rw [hn] at h
      exact (fintype.card_eq_zero_iff.mp h).elim' 0⟩
  rw [Fintype.bijective_iff_injective_and_card, ZMod.card, h, eq_self_iff_true, and_true_iff]
  apply ZMod.castHom_injective
#align zmod.cast_hom_bijective ZMod.castHom_bijective

/-- The unique ring isomorphism between `zmod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
noncomputable def ringEquiv [Fintype R] (h : Fintype.card R = n) : ZMod n ≃+* R :=
  RingEquiv.ofBijective _ (ZMod.castHom_bijective R h)
#align zmod.ring_equiv ZMod.ringEquiv

/-- The identity between `zmod m` and `zmod n` when `m = n`, as a ring isomorphism. -/
def ringEquivCongr {m n : ℕ} (h : m = n) : ZMod m ≃+* ZMod n :=
  by
  cases m <;> cases n
  · exact RingEquiv.refl _
  · exfalso
    exact n.succ_ne_zero h.symm
  · exfalso
    exact m.succ_ne_zero h
  ·
    exact
      {
        Fin.cast
          h with
        map_mul' := fun a b => by
          rw [OrderIso.toFun_eq_coe]; ext
          rw [Fin.coe_cast, Fin.coe_mul, Fin.coe_mul, Fin.coe_cast, Fin.coe_cast, ← h]
        map_add' := fun a b => by
          rw [OrderIso.toFun_eq_coe]; ext
          rw [Fin.coe_cast, Fin.val_add, Fin.val_add, Fin.coe_cast, Fin.coe_cast, ← h] }
#align zmod.ring_equiv_congr ZMod.ringEquivCongr

end CharEq

end UniversalProperty

theorem int_coe_eq_int_coe_iff (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c] :=
  CharP.int_coe_eq_int_coe_iff (ZMod c) c a b
#align zmod.int_coe_eq_int_coe_iff ZMod.int_coe_eq_int_coe_iff

theorem int_coe_eq_int_coe_iff' (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.int_coe_eq_int_coe_iff a b c
#align zmod.int_coe_eq_int_coe_iff' ZMod.int_coe_eq_int_coe_iff'

theorem nat_coe_eq_nat_coe_iff (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c] := by
  simpa [Int.coe_nat_modEq_iff] using ZMod.int_coe_eq_int_coe_iff a b c
#align zmod.nat_coe_eq_nat_coe_iff ZMod.nat_coe_eq_nat_coe_iff

theorem nat_coe_eq_nat_coe_iff' (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.nat_coe_eq_nat_coe_iff a b c
#align zmod.nat_coe_eq_nat_coe_iff' ZMod.nat_coe_eq_nat_coe_iff'

theorem int_coe_zMod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : ZMod b) = 0 ↔ (b : ℤ) ∣ a := by
  rw [← Int.cast_zero, ZMod.int_coe_eq_int_coe_iff, Int.modEq_zero_iff_dvd]
#align zmod.int_coe_zmod_eq_zero_iff_dvd ZMod.int_coe_zMod_eq_zero_iff_dvd

theorem int_coe_eq_int_coe_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : ZMod c) = ↑b ↔ ↑c ∣ b - a := by
  rw [ZMod.int_coe_eq_int_coe_iff, Int.modEq_iff_dvd]
#align zmod.int_coe_eq_int_coe_iff_dvd_sub ZMod.int_coe_eq_int_coe_iff_dvd_sub

theorem nat_coe_zMod_eq_zero_iff_dvd (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a := by
  rw [← Nat.cast_zero, ZMod.nat_coe_eq_nat_coe_iff, Nat.modEq_zero_iff_dvd]
#align zmod.nat_coe_zmod_eq_zero_iff_dvd ZMod.nat_coe_zMod_eq_zero_iff_dvd

theorem val_int_cast {n : ℕ} (a : ℤ) [NeZero n] : ↑(a : ZMod n).val = a % n :=
  by
  have hle : (0 : ℤ) ≤ ↑(a : ZMod n).val := Int.coe_nat_nonneg _
  have hlt : ↑(a : ZMod n).val < (n : ℤ) := int.coe_nat_lt.mpr (ZMod.val_lt a)
  refine' (Int.emod_eq_of_lt hle hlt).symm.trans _
  rw [← ZMod.int_coe_eq_int_coe_iff', Int.cast_ofNat, ZMod.nat_cast_val, ZMod.cast_id]
#align zmod.val_int_cast ZMod.val_int_cast

theorem coe_int_cast {n : ℕ} (a : ℤ) : ↑(a : ZMod n) = a % n :=
  by
  cases n
  · rw [Int.ofNat_zero, Int.mod_zero, Int.cast_id, Int.cast_id]
  · rw [← val_int_cast, val, coe_coe]
#align zmod.coe_int_cast ZMod.coe_int_cast

@[simp]
theorem val_neg_one (n : ℕ) : (-1 : ZMod n.succ).val = n :=
  by
  rw [val, Fin.coe_neg]
  cases n
  · rw [Nat.mod_one]
  · rw [Fin.val_one, Nat.succ_add_sub_one, Nat.mod_eq_of_lt (Nat.lt.base _)]
#align zmod.val_neg_one ZMod.val_neg_one

/-- `-1 : zmod n` lifts to `n - 1 : R`. This avoids the characteristic assumption in `cast_neg`. -/
theorem cast_neg_one {R : Type _} [Ring R] (n : ℕ) : ↑(-1 : ZMod n) = (n - 1 : R) :=
  by
  cases n
  · rw [Int.cast_neg, Int.cast_one, Nat.cast_zero, zero_sub]
  · rw [← nat_cast_val, val_neg_one, Nat.cast_succ, add_sub_cancel]
#align zmod.cast_neg_one ZMod.cast_neg_one

theorem cast_sub_one {R : Type _} [Ring R] {n : ℕ} (k : ZMod n) :
    ((k - 1 : ZMod n) : R) = (if k = 0 then n else k) - 1 :=
  by
  split_ifs with hk
  · rw [hk, zero_sub, ZMod.cast_neg_one]
  · cases n
    · rw [Int.cast_sub, Int.cast_one]
    · rw [← ZMod.nat_cast_val, ZMod.val, Fin.coe_sub_one, if_neg]
      · rw [Nat.cast_sub, Nat.cast_one, coe_coe]
        rwa [Fin.ext_iff, Fin.val_zero, ← Ne, ← Nat.one_le_iff_ne_zero] at hk
      · exact hk
#align zmod.cast_sub_one ZMod.cast_sub_one

theorem nat_coe_zMod_eq_iff (p : ℕ) (n : ℕ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine' ⟨n / p, _⟩
    rw [val_nat_cast, Nat.mod_add_div]
  · rintro ⟨k, rfl⟩
    rw [Nat.cast_add, nat_cast_zmod_val, Nat.cast_mul, nat_cast_self, MulZeroClass.zero_mul,
      add_zero]
#align zmod.nat_coe_zmod_eq_iff ZMod.nat_coe_zMod_eq_iff

theorem int_coe_zMod_eq_iff (p : ℕ) (n : ℤ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine' ⟨n / p, _⟩
    rw [val_int_cast, Int.emod_add_ediv]
  · rintro ⟨k, rfl⟩
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_ofNat, nat_cast_val,
      ZMod.nat_cast_self, MulZeroClass.zero_mul, add_zero, cast_id]
#align zmod.int_coe_zmod_eq_iff ZMod.int_coe_zMod_eq_iff

@[push_cast, simp]
theorem int_cast_mod (a : ℤ) (b : ℕ) : ((a % b : ℤ) : ZMod b) = (a : ZMod b) :=
  by
  rw [ZMod.int_coe_eq_int_coe_iff]
  apply Int.mod_modEq
#align zmod.int_cast_mod ZMod.int_cast_mod

theorem ker_int_castAddHom (n : ℕ) : (Int.castAddHom (ZMod n)).ker = AddSubgroup.zmultiples n :=
  by
  ext
  rw [Int.mem_zmultiples_iff, AddMonoidHom.mem_ker, Int.coe_castAddHom,
    int_coe_zmod_eq_zero_iff_dvd]
#align zmod.ker_int_cast_add_hom ZMod.ker_int_castAddHom

theorem ker_int_castRingHom (n : ℕ) : (Int.castRingHom (ZMod n)).ker = Ideal.span ({n} : Set ℤ) :=
  by
  ext
  rw [Ideal.mem_span_singleton, RingHom.mem_ker, Int.coe_castRingHom, int_coe_zmod_eq_zero_iff_dvd]
#align zmod.ker_int_cast_ring_hom ZMod.ker_int_castRingHom

attribute [local semireducible] Int.NonNeg

@[simp]
theorem nat_cast_toNat (p : ℕ) : ∀ {z : ℤ} (h : 0 ≤ z), (z.toNat : ZMod p) = z
  | (n : ℕ), h => by simp only [Int.cast_ofNat, Int.toNat_coe_nat]
  | -[n+1], h => False.elim h
#align zmod.nat_cast_to_nat ZMod.nat_cast_toNat

theorem val_injective (n : ℕ) [NeZero n] : Function.Injective (ZMod.val : ZMod n → ℕ) :=
  by
  cases n
  · cases NeZero.ne 0 rfl
  intro a b h
  ext
  exact h
#align zmod.val_injective ZMod.val_injective

theorem val_one_eq_one_mod (n : ℕ) : (1 : ZMod n).val = 1 % n := by
  rw [← Nat.cast_one, val_nat_cast]
#align zmod.val_one_eq_one_mod ZMod.val_one_eq_one_mod

theorem val_one (n : ℕ) [Fact (1 < n)] : (1 : ZMod n).val = 1 :=
  by
  rw [val_one_eq_one_mod]
  exact Nat.mod_eq_of_lt (Fact.out _)
#align zmod.val_one ZMod.val_one

theorem val_add {n : ℕ} [NeZero n] (a b : ZMod n) : (a + b).val = (a.val + b.val) % n :=
  by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.val_add
#align zmod.val_add ZMod.val_add

theorem val_mul {n : ℕ} (a b : ZMod n) : (a * b).val = a.val * b.val % n :=
  by
  cases n
  · rw [Nat.mod_zero]
    apply Int.natAbs_mul
  · apply Fin.val_mul
#align zmod.val_mul ZMod.val_mul

instance nontrivial (n : ℕ) [Fact (1 < n)] : Nontrivial (ZMod n) :=
  ⟨⟨0, 1, fun h =>
      zero_ne_one <|
        calc
          0 = (0 : ZMod n).val := by rw [val_zero]
          _ = (1 : ZMod n).val := (congr_arg ZMod.val h)
          _ = 1 := val_one n
          ⟩⟩
#align zmod.nontrivial ZMod.nontrivial

instance nontrivial' : Nontrivial (ZMod 0) :=
  Int.nontrivial
#align zmod.nontrivial' ZMod.nontrivial'

/-- The inversion on `zmod n`.
It is setup in such a way that `a * a⁻¹` is equal to `gcd a.val n`.
In particular, if `a` is coprime to `n`, and hence a unit, `a * a⁻¹ = 1`. -/
def inv : ∀ n : ℕ, ZMod n → ZMod n
  | 0, i => Int.sign i
  | n + 1, i => Nat.gcdA i.val (n + 1)
#align zmod.inv ZMod.inv

instance (n : ℕ) : Inv (ZMod n) :=
  ⟨inv n⟩

theorem inv_zero : ∀ n : ℕ, (0 : ZMod n)⁻¹ = 0
  | 0 => Int.sign_zero
  | n + 1 =>
    show (Nat.gcdA _ (n + 1) : ZMod (n + 1)) = 0
      by
      rw [val_zero]
      unfold Nat.gcdA Nat.xgcd Nat.xgcdAux
      rfl
#align zmod.inv_zero ZMod.inv_zero

theorem mul_inv_eq_gcd {n : ℕ} (a : ZMod n) : a * a⁻¹ = Nat.gcd a.val n :=
  by
  cases n
  ·
    calc
      a * a⁻¹ = a * Int.sign a := rfl
      _ = a.nat_abs := by rw [Int.mul_sign]
      _ = a.val.gcd 0 := by rw [Nat.gcd_zero_right] <;> rfl
      
  · set k := n.succ
    calc
      a * a⁻¹ = a * a⁻¹ + k * Nat.gcdB (val a) k := by
        rw [nat_cast_self, MulZeroClass.zero_mul, add_zero]
      _ = ↑(↑a.val * Nat.gcdA (val a) k + k * Nat.gcdB (val a) k) :=
        by
        push_cast
        rw [nat_cast_zmod_val]
        rfl
      _ = Nat.gcd a.val k := (congr_arg coe (Nat.gcd_eq_gcd_ab a.val k)).symm
      
#align zmod.mul_inv_eq_gcd ZMod.mul_inv_eq_gcd

@[simp]
theorem nat_cast_mod (a : ℕ) (n : ℕ) : ((a % n : ℕ) : ZMod n) = a := by
  conv =>
      rhs
      rw [← Nat.mod_add_div a n] <;>
    simp
#align zmod.nat_cast_mod ZMod.nat_cast_mod

theorem eq_iff_modEq_nat (n : ℕ) {a b : ℕ} : (a : ZMod n) = b ↔ a ≡ b [MOD n] :=
  by
  cases n
  · simp only [Nat.ModEq, Int.coe_nat_inj', Nat.mod_zero]
  · rw [Fin.ext_iff, Nat.ModEq, ← val_nat_cast, ← val_nat_cast]
    exact Iff.rfl
#align zmod.eq_iff_modeq_nat ZMod.eq_iff_modEq_nat

theorem coe_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : Nat.coprime x n) : (x * x⁻¹ : ZMod n) = 1 :=
  by
  rw [Nat.coprime, Nat.gcd_comm, Nat.gcd_rec] at h
  rw [mul_inv_eq_gcd, val_nat_cast, h, Nat.cast_one]
#align zmod.coe_mul_inv_eq_one ZMod.coe_mul_inv_eq_one

/-- `unit_of_coprime` makes an element of `(zmod n)ˣ` given
  a natural number `x` and a proof that `x` is coprime to `n`  -/
def unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.coprime x n) : (ZMod n)ˣ :=
  ⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩
#align zmod.unit_of_coprime ZMod.unitOfCoprime

@[simp]
theorem coe_unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.coprime x n) :
    (unitOfCoprime x h : ZMod n) = x :=
  rfl
#align zmod.coe_unit_of_coprime ZMod.coe_unitOfCoprime

theorem val_coe_unit_coprime {n : ℕ} (u : (ZMod n)ˣ) : Nat.coprime (u : ZMod n).val n :=
  by
  cases n
  · rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp
  apply Nat.coprime_of_mul_modEq_one ((u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1)).val
  have := Units.ext_iff.1 (mul_right_inv u)
  rw [Units.val_one] at this
  rw [← eq_iff_modeq_nat, Nat.cast_one, ← this]; clear this
  rw [← nat_cast_zmod_val ((u * u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1))]
  rw [Units.val_mul, val_mul, nat_cast_mod]
#align zmod.val_coe_unit_coprime ZMod.val_coe_unit_coprime

@[simp]
theorem inv_coe_unit {n : ℕ} (u : (ZMod n)ˣ) : (u : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ) :=
  by
  have := congr_arg (coe : ℕ → ZMod n) (val_coe_unit_coprime u)
  rw [← mul_inv_eq_gcd, Nat.cast_one] at this
  let u' : (ZMod n)ˣ := ⟨u, (u : ZMod n)⁻¹, this, by rwa [mul_comm]⟩
  have h : u = u' := by
    apply Units.ext
    rfl
  rw [h]
  rfl
#align zmod.inv_coe_unit ZMod.inv_coe_unit

theorem mul_inv_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a * a⁻¹ = 1 :=
  by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit, u.mul_inv]
#align zmod.mul_inv_of_unit ZMod.mul_inv_of_unit

theorem inv_mul_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_of_unit a h]
#align zmod.inv_mul_of_unit ZMod.inv_mul_of_unit

-- TODO: this equivalence is true for `zmod 0 = ℤ`, but needs to use different functions.
/-- Equivalence between the units of `zmod n` and
the subtype of terms `x : zmod n` for which `x.val` is comprime to `n` -/
def unitsEquivCoprime {n : ℕ} [NeZero n] : (ZMod n)ˣ ≃ { x : ZMod n // Nat.coprime x.val n }
    where
  toFun x := ⟨x, val_coe_unit_coprime x⟩
  invFun x := unitOfCoprime x.1.val x.2
  left_inv := fun ⟨_, _, _, _⟩ => Units.ext (nat_cast_zMod_val _)
  right_inv := fun ⟨_, _⟩ => by simp
#align zmod.units_equiv_coprime ZMod.unitsEquivCoprime

/-- The **Chinese remainder theorem**. For a pair of coprime natural numbers, `m` and `n`,
  the rings `zmod (m * n)` and `zmod m × zmod n` are isomorphic.

See `ideal.quotient_inf_ring_equiv_pi_quotient` for the Chinese remainder theorem for ideals in any
ring.
-/
def chineseRemainder {m n : ℕ} (h : m.coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
  let to_fun : ZMod (m * n) → ZMod m × ZMod n :=
    ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)
  let inv_fun : ZMod m × ZMod n → ZMod (m * n) := fun x =>
    if m * n = 0 then if m = 1 then RingHom.snd _ _ x else RingHom.fst _ _ x
    else Nat.chineseRemainder h x.1.val x.2.val
  have inv : Function.LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun :=
    if hmn0 : m * n = 0 then by
      rcases h.eq_of_mul_eq_zero hmn0 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
        simp [inv_fun, to_fun, Function.LeftInverse, Function.RightInverse, eq_intCast,
          Prod.ext_iff]
    else by
      haveI : NeZero (m * n) := ⟨hmn0⟩
      haveI : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
      haveI : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
      have left_inv : Function.LeftInverse inv_fun to_fun :=
        by
        intro x
        dsimp only [dvd_mul_left, dvd_mul_right, ZMod.castHom_apply, coe_coe, inv_fun, to_fun]
        conv_rhs => rw [← ZMod.nat_cast_zMod_val x]
        rw [if_neg hmn0, ZMod.eq_iff_modEq_nat, ← Nat.modEq_and_modEq_iff_modEq_mul h,
          Prod.fst_zMod_cast, Prod.snd_zMod_cast]
        refine'
          ⟨(Nat.chineseRemainder h (x : ZMod m).val (x : ZMod n).val).2.left.trans _,
            (Nat.chineseRemainder h (x : ZMod m).val (x : ZMod n).val).2.right.trans _⟩
        · rw [← ZMod.eq_iff_modEq_nat, ZMod.nat_cast_zMod_val, ZMod.nat_cast_val]
        · rw [← ZMod.eq_iff_modEq_nat, ZMod.nat_cast_zMod_val, ZMod.nat_cast_val]
      exact ⟨left_inv, left_inv.right_inverse_of_card_le (by simp)⟩
  { toFun
    invFun
    map_mul' := RingHom.map_mul _
    map_add' := RingHom.map_add _
    left_inv := inv.1
    right_inv := inv.2 }
#align zmod.chinese_remainder ZMod.chineseRemainder

-- todo: this can be made a `unique` instance.
instance subsingleton_units : Subsingleton (ZMod 2)ˣ :=
  ⟨by decide⟩
#align zmod.subsingleton_units ZMod.subsingleton_units

theorem le_div_two_iff_lt_neg (n : ℕ) [hn : Fact ((n : ℕ) % 2 = 1)] {x : ZMod n} (hx0 : x ≠ 0) :
    x.val ≤ (n / 2 : ℕ) ↔ (n / 2 : ℕ) < (-x).val :=
  by
  haveI npos : NeZero n :=
    ⟨by
      rintro rfl
      simpa [fact_iff] using hn⟩
  have hn2 : (n : ℕ) / 2 < n :=
    Nat.div_lt_of_lt_mul ((lt_mul_iff_one_lt_left <| NeZero.pos n).2 (by decide))
  have hn2' : (n : ℕ) - n / 2 = n / 2 + 1 :=
    by
    conv =>
      lhs
      congr
      rw [← Nat.succ_sub_one n, Nat.succ_sub <| NeZero.pos n]
    rw [← Nat.two_mul_odd_div_two hn.1, two_mul, ← Nat.succ_add, add_tsub_cancel_right]
  have hxn : (n : ℕ) - x.val < n :=
    by
    rw [tsub_lt_iff_tsub_lt x.val_le le_rfl, tsub_self]
    rw [← ZMod.nat_cast_zMod_val x] at hx0
    exact Nat.pos_of_ne_zero fun h => by simpa [h] using hx0
  ·
    conv =>
      rhs
      rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← hn2', ← zero_add (-x), ← ZMod.nat_cast_self, ←
        sub_eq_add_neg, ← ZMod.nat_cast_zMod_val x, ← Nat.cast_sub x.val_le, ZMod.val_nat_cast,
        Nat.mod_eq_of_lt hxn, tsub_le_tsub_iff_left x.val_le]
#align zmod.le_div_two_iff_lt_neg ZMod.le_div_two_iff_lt_neg

theorem ne_neg_self (n : ℕ) [hn : Fact ((n : ℕ) % 2 = 1)] {a : ZMod n} (ha : a ≠ 0) : a ≠ -a :=
  fun h => by
  have : a.val ≤ n / 2 ↔ (n : ℕ) / 2 < (-a).val := le_div_two_iff_lt_neg n ha
  rwa [← h, ← not_lt, not_iff_self] at this
#align zmod.ne_neg_self ZMod.ne_neg_self

theorem neg_one_ne_one {n : ℕ} [Fact (2 < n)] : (-1 : ZMod n) ≠ 1 :=
  CharP.neg_one_ne_one (ZMod n) n
#align zmod.neg_one_ne_one ZMod.neg_one_ne_one

theorem neg_eq_self_mod_two (a : ZMod 2) : -a = a := by
  fin_cases a <;> ext <;> simp [Fin.coe_neg, Int.natMod] <;> norm_num
#align zmod.neg_eq_self_mod_two ZMod.neg_eq_self_mod_two

@[simp]
theorem natAbs_mod_two (a : ℤ) : (a.natAbs : ZMod 2) = a :=
  by
  cases a
  · simp only [Int.natAbs_ofNat, Int.cast_ofNat, Int.ofNat_eq_coe]
  · simp only [neg_eq_self_mod_two, Nat.cast_succ, Int.natAbs, Int.cast_negSucc]
#align zmod.nat_abs_mod_two ZMod.natAbs_mod_two

@[simp]
theorem val_eq_zero : ∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
  | 0, a => Int.natAbs_eq_zero
  | n + 1, a => by
    rw [Fin.ext_iff]
    exact Iff.rfl
#align zmod.val_eq_zero ZMod.val_eq_zero

theorem neg_eq_self_iff {n : ℕ} (a : ZMod n) : -a = a ↔ a = 0 ∨ 2 * a.val = n :=
  by
  rw [neg_eq_iff_add_eq_zero, ← two_mul]
  cases n
  · rw [@mul_eq_zero ℤ, @mul_eq_zero ℕ, val_eq_zero]
    exact
      ⟨fun h => h.elim (by decide) Or.inl, fun h =>
        Or.inr (h.elim id fun h => h.elim (by decide) id)⟩
  conv_lhs =>
    rw [← a.nat_cast_zmod_val, ← Nat.cast_two, ← Nat.cast_mul, nat_coe_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨m, he⟩
    cases m
    · rw [MulZeroClass.mul_zero, mul_eq_zero] at he
      rcases he with (⟨⟨⟩⟩ | he)
      exact Or.inl (a.val_eq_zero.1 he)
    cases m
    · right
      rwa [mul_one] at he
    refine' (a.val_lt.not_le <| Nat.le_of_mul_le_mul_left _ zero_lt_two).elim
    rw [he, mul_comm]
    apply Nat.mul_le_mul_left
    decide
  · rintro (rfl | h)
    · rw [val_zero, MulZeroClass.mul_zero]
      apply dvd_zero
    · rw [h]
#align zmod.neg_eq_self_iff ZMod.neg_eq_self_iff

theorem val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rw [val_nat_cast, Nat.mod_eq_of_lt h]
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

theorem neg_val {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = if a = 0 then 0 else n - a.val :=
  by
  rw [neg_val']
  by_cases h : a = 0; · rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_self]
  rw [if_neg h]
  apply Nat.mod_eq_of_lt
  apply Nat.sub_lt (NeZero.pos n)
  contrapose! h
  rwa [le_zero_iff, val_eq_zero] at h
#align zmod.neg_val ZMod.neg_val

/-- `val_min_abs x` returns the integer in the same equivalence class as `x` that is closest to `0`,
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
    valMinAbs x = if x.val ≤ n / 2 then x.val else x.val - n :=
  by
  cases n
  · cases NeZero.ne 0 rfl
  · rfl
#align zmod.val_min_abs_def_pos ZMod.valMinAbs_def_pos

@[simp, norm_cast]
theorem coe_valMinAbs : ∀ {n : ℕ} (x : ZMod n), (x.valMinAbs : ZMod n) = x
  | 0, x => Int.cast_id x
  | k@(n + 1), x => by
    rw [val_min_abs_def_pos]
    split_ifs
    · rw [Int.cast_ofNat, nat_cast_zmod_val]
    · rw [Int.cast_sub, Int.cast_ofNat, nat_cast_zmod_val, Int.cast_ofNat, nat_cast_self, sub_zero]
#align zmod.coe_val_min_abs ZMod.coe_valMinAbs

theorem injective_valMinAbs {n : ℕ} : (valMinAbs : ZMod n → ℤ).Injective :=
  Function.injective_iff_hasLeftInverse.2 ⟨_, coe_valMinAbs⟩
#align zmod.injective_val_min_abs ZMod.injective_valMinAbs

theorem Nat.le_div_two_iff_mul_two_le {n m : ℕ} : m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n := by
  rw [Nat.le_div_iff_mul_le zero_lt_two, ← Int.ofNat_le, Int.ofNat_mul, Nat.cast_two]
#align nat.le_div_two_iff_mul_two_le Nat.le_div_two_iff_mul_two_le

theorem valMinAbs_nonneg_iff {n : ℕ} [NeZero n] (x : ZMod n) : 0 ≤ x.valMinAbs ↔ x.val ≤ n / 2 :=
  by
  rw [val_min_abs_def_pos]; split_ifs
  · exact iff_of_true (Nat.cast_nonneg _) h
  · exact iff_of_false (sub_lt_zero.2 <| Int.ofNat_lt.2 x.val_lt).not_le h
#align zmod.val_min_abs_nonneg_iff ZMod.valMinAbs_nonneg_iff

theorem valMinAbs_mul_two_eq_iff {n : ℕ} (a : ZMod n) : a.valMinAbs * 2 = n ↔ 2 * a.val = n :=
  by
  cases n; · simp
  by_cases a.val ≤ n.succ / 2
  · rw [val_min_abs, if_pos h, ← Int.coe_nat_inj', Nat.cast_mul, Nat.cast_two, mul_comm]
  apply iff_of_false (fun he => _) (mt _ h)
  · rw [← a.val_min_abs_nonneg_iff, ← mul_nonneg_iff_left_nonneg_of_pos, he] at h
    exacts[h (Nat.cast_nonneg _), zero_lt_two]
  · rw [mul_comm]
    exact fun h => (Nat.le_div_iff_mul_le zero_lt_two).2 h.le
#align zmod.val_min_abs_mul_two_eq_iff ZMod.valMinAbs_mul_two_eq_iff

theorem valMinAbs_mem_Ioc {n : ℕ} [NeZero n] (x : ZMod n) : x.valMinAbs * 2 ∈ Set.Ioc (-n : ℤ) n :=
  by
  simp_rw [val_min_abs_def_pos, Nat.le_div_two_iff_mul_two_le]; split_ifs
  · refine' ⟨(neg_lt_zero.2 <| by exact_mod_cast NeZero.pos n).trans_le (mul_nonneg _ _), h⟩
    exacts[Nat.cast_nonneg _, zero_le_two]
  · refine' ⟨_, trans (mul_nonpos_of_nonpos_of_nonneg _ zero_le_two) <| Nat.cast_nonneg _⟩
    · linarith only [h]
    · rw [sub_nonpos, Int.ofNat_le]
      exact x.val_lt.le
#align zmod.val_min_abs_mem_Ioc ZMod.valMinAbs_mem_Ioc

theorem valMinAbs_spec {n : ℕ} [NeZero n] (x : ZMod n) (y : ℤ) :
    x.valMinAbs = y ↔ x = y ∧ y * 2 ∈ Set.Ioc (-n : ℤ) n :=
  ⟨by
    rintro rfl
    exact ⟨x.coe_val_min_abs.symm, x.val_min_abs_mem_Ioc⟩, fun h =>
    by
    rw [← sub_eq_zero]
    apply @Int.eq_zero_of_abs_lt_dvd n
    · rw [← int_coe_zmod_eq_zero_iff_dvd, Int.cast_sub, coe_val_min_abs, h.1, sub_self]
    rw [← mul_lt_mul_right (@zero_lt_two ℤ _ _ _ _ _)]
    nth_rw 1 [← abs_eq_self.2 (@zero_le_two ℤ _ _ _ _)]
    rw [← abs_mul, sub_mul, abs_lt];
    constructor <;> linarith only [x.val_min_abs_mem_Ioc.1, x.val_min_abs_mem_Ioc.2, h.2.1, h.2.2]⟩
#align zmod.val_min_abs_spec ZMod.valMinAbs_spec

theorem natAbs_valMinAbs_le {n : ℕ} [NeZero n] (x : ZMod n) : x.valMinAbs.natAbs ≤ n / 2 :=
  by
  rw [Nat.le_div_two_iff_mul_two_le]
  cases x.val_min_abs.nat_abs_eq
  · rw [← h]
    exact x.val_min_abs_mem_Ioc.2
  · rw [← neg_le_neg_iff, ← neg_mul, ← h]
    exact x.val_min_abs_mem_Ioc.1.le
#align zmod.nat_abs_val_min_abs_le ZMod.natAbs_valMinAbs_le

@[simp]
theorem valMinAbs_zero : ∀ n, (0 : ZMod n).valMinAbs = 0
  | 0 => by simp only [val_min_abs_def_zero]
  | n + 1 => by simp only [val_min_abs_def_pos, if_true, Int.ofNat_zero, zero_le, val_zero]
#align zmod.val_min_abs_zero ZMod.valMinAbs_zero

@[simp]
theorem valMinAbs_eq_zero {n : ℕ} (x : ZMod n) : x.valMinAbs = 0 ↔ x = 0 :=
  by
  cases n; · simp
  rw [← val_min_abs_zero n.succ]
  apply injective_val_min_abs.eq_iff
#align zmod.val_min_abs_eq_zero ZMod.valMinAbs_eq_zero

theorem nat_cast_natAbs_valMinAbs {n : ℕ} [NeZero n] (a : ZMod n) :
    (a.valMinAbs.natAbs : ZMod n) = if a.val ≤ (n : ℕ) / 2 then a else -a :=
  by
  have : (a.val : ℤ) - n ≤ 0 := by
    erw [sub_nonpos, Int.ofNat_le]
    exact a.val_le
  rw [val_min_abs_def_pos]
  split_ifs
  · rw [Int.natAbs_ofNat, nat_cast_zmod_val]
  ·
    rw [← Int.cast_ofNat, Int.ofNat_natAbs_of_nonpos this, Int.cast_neg, Int.cast_sub,
      Int.cast_ofNat, Int.cast_ofNat, nat_cast_self, sub_zero, nat_cast_zmod_val]
#align zmod.nat_cast_nat_abs_val_min_abs ZMod.nat_cast_natAbs_valMinAbs

theorem valMinAbs_neg_of_ne_half {n : ℕ} {a : ZMod n} (ha : 2 * a.val ≠ n) :
    (-a).valMinAbs = -a.valMinAbs :=
  by
  cases eq_zero_or_neZero n;
  · subst h
    rfl
  refine' (val_min_abs_spec _ _).2 ⟨_, _, _⟩
  · rw [Int.cast_neg, coe_val_min_abs]
  · rw [neg_mul, neg_lt_neg_iff]
    exact a.val_min_abs_mem_Ioc.2.lt_of_ne (mt a.val_min_abs_mul_two_eq_iff.1 ha)
  · linarith only [a.val_min_abs_mem_Ioc.1]
#align zmod.val_min_abs_neg_of_ne_half ZMod.valMinAbs_neg_of_ne_half

@[simp]
theorem natAbs_valMinAbs_neg {n : ℕ} (a : ZMod n) : (-a).valMinAbs.natAbs = a.valMinAbs.natAbs :=
  by
  by_cases h2a : 2 * a.val = n
  · rw [a.neg_eq_self_iff.2 (Or.inr h2a)]
  · rw [val_min_abs_neg_of_ne_half h2a, Int.natAbs_neg]
#align zmod.nat_abs_val_min_abs_neg ZMod.natAbs_valMinAbs_neg

theorem val_eq_ite_valMinAbs {n : ℕ} [NeZero n] (a : ZMod n) :
    (a.val : ℤ) = a.valMinAbs + if a.val ≤ n / 2 then 0 else n :=
  by
  rw [val_min_abs_def_pos]
  split_ifs <;> simp only [add_zero, sub_add_cancel]
#align zmod.val_eq_ite_val_min_abs ZMod.val_eq_ite_valMinAbs

theorem prime_ne_zero (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rwa [← Nat.cast_zero, Ne.def, eq_iff_modeq_nat, Nat.modEq_zero_iff_dvd, ←
    hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]
#align zmod.prime_ne_zero ZMod.prime_ne_zero

theorem valMinAbs_natAbs_eq_min {n : ℕ} [hpos : NeZero n] (a : ZMod n) :
    a.valMinAbs.natAbs = min a.val (n - a.val) :=
  by
  rw [val_min_abs_def_pos]
  split_ifs with h h
  · rw [Int.natAbs_ofNat]
    symm
    apply
      min_eq_left (le_trans h (le_trans (Nat.half_le_of_sub_le_half _) (Nat.sub_le_sub_left n h)))
    rw [Nat.sub_sub_self (Nat.div_le_self _ _)]
  · rw [← Int.natAbs_neg, neg_sub, ← Nat.cast_sub a.val_le]
    symm
    apply
      min_eq_right
        (le_trans (le_trans (Nat.sub_le_sub_left n (lt_of_not_ge h)) (Nat.le_half_of_half_lt_sub _))
          (le_of_not_ge h))
    rw [Nat.sub_sub_self (Nat.div_lt_self (lt_of_le_of_ne' (Nat.zero_le _) hpos.1) one_lt_two)]
    apply Nat.lt_succ_self
#align zmod.val_min_abs_nat_abs_eq_min ZMod.valMinAbs_natAbs_eq_min

theorem natAbs_min_of_le_div_two (n : ℕ) (x y : ℤ) (he : (x : ZMod n) = y) (hl : x.natAbs ≤ n / 2) :
    x.natAbs ≤ y.natAbs := by
  rw [int_coe_eq_int_coe_iff_dvd_sub] at he
  obtain ⟨m, he⟩ := he
  rw [sub_eq_iff_eq_add] at he
  subst he
  obtain rfl | hm := eq_or_ne m 0
  · rw [MulZeroClass.mul_zero, zero_add]
  apply hl.trans
  rw [← add_le_add_iff_right x.nat_abs]
  refine' trans (trans ((add_le_add_iff_left _).2 hl) _) (Int.natAbs_sub_le _ _)
  rw [add_sub_cancel, Int.natAbs_mul, Int.natAbs_ofNat]
  refine' trans _ (Nat.le_mul_of_pos_right <| Int.natAbs_pos_of_ne_zero hm)
  rw [← mul_two]; apply Nat.div_mul_le_self
#align zmod.nat_abs_min_of_le_div_two ZMod.natAbs_min_of_le_div_two

theorem natAbs_valMinAbs_add_le {n : ℕ} (a b : ZMod n) :
    (a + b).valMinAbs.natAbs ≤ (a.valMinAbs + b.valMinAbs).natAbs :=
  by
  cases n; · rfl
  apply nat_abs_min_of_le_div_two n.succ
  · simp_rw [Int.cast_add, coe_val_min_abs]
  · apply nat_abs_val_min_abs_le
#align zmod.nat_abs_val_min_abs_add_le ZMod.natAbs_valMinAbs_add_le

variable (p : ℕ) [Fact p.Prime]

private theorem mul_inv_cancel_aux (a : ZMod p) (h : a ≠ 0) : a * a⁻¹ = 1 :=
  by
  obtain ⟨k, rfl⟩ := nat_cast_zmod_surjective a
  apply coe_mul_inv_eq_one
  apply Nat.coprime.symm
  rwa [Nat.Prime.coprime_iff_not_dvd (Fact.out p.prime), ← CharP.cast_eq_zero_iff (ZMod p)]
#align zmod.mul_inv_cancel_aux zmod.mul_inv_cancel_aux

/-- Field structure on `zmod p` if `p` is prime. -/
instance : Field (ZMod p) :=
  { ZMod.commRing p, ZMod.hasInv p,
    ZMod.nontrivial p with
    mul_inv_cancel := mul_inv_cancel_aux p
    inv_zero := inv_zero p }

/-- `zmod p` is an integral domain when `p` is prime. -/
instance (p : ℕ) [hp : Fact p.Prime] : IsDomain (ZMod p) :=
  by
  -- We need `cases p` here in order to resolve which `comm_ring` instance is being used.
  cases p
  · exact (Nat.not_prime_zero hp.out).elim
  exact @Field.isDomain (ZMod _) (ZMod.field _)

end ZMod

theorem RingHom.ext_zMod {n : ℕ} {R : Type _} [Semiring R] (f g : ZMod n →+* R) : f = g :=
  by
  ext a
  obtain ⟨k, rfl⟩ := ZMod.int_cast_surjective a
  let φ : ℤ →+* R := f.comp (Int.castRingHom (ZMod n))
  let ψ : ℤ →+* R := g.comp (Int.castRingHom (ZMod n))
  show φ k = ψ k
  rw [φ.ext_int ψ]
#align ring_hom.ext_zmod RingHom.ext_zMod

namespace ZMod

variable {n : ℕ} {R : Type _}

instance subsingleton_ringHom [Semiring R] : Subsingleton (ZMod n →+* R) :=
  ⟨RingHom.ext_zMod⟩
#align zmod.subsingleton_ring_hom ZMod.subsingleton_ringHom

instance subsingleton_ringEquiv [Semiring R] : Subsingleton (ZMod n ≃+* R) :=
  ⟨fun f g => by
    rw [RingEquiv.coe_ringHom_inj_iff]
    apply RingHom.ext_zMod _ _⟩
#align zmod.subsingleton_ring_equiv ZMod.subsingleton_ringEquiv

@[simp]
theorem ringHom_map_cast [Ring R] (f : R →+* ZMod n) (k : ZMod n) : f k = k := by cases n <;> simp
#align zmod.ring_hom_map_cast ZMod.ringHom_map_cast

theorem ringHom_rightInverse [Ring R] (f : R →+* ZMod n) :
    Function.RightInverse (coe : ZMod n → R) f :=
  ringHom_map_cast f
#align zmod.ring_hom_right_inverse ZMod.ringHom_rightInverse

theorem ringHom_surjective [Ring R] (f : R →+* ZMod n) : Function.Surjective f :=
  (ringHom_rightInverse f).Surjective
#align zmod.ring_hom_surjective ZMod.ringHom_surjective

theorem ringHom_eq_of_ker_eq [CommRing R] (f g : R →+* ZMod n) (h : f.ker = g.ker) : f = g :=
  by
  have := f.lift_of_right_inverse_comp _ (ZMod.ringHom_rightInverse f) ⟨g, le_of_eq h⟩
  rw [Subtype.coe_mk] at this
  rw [← this, RingHom.ext_zMod (f.lift_of_right_inverse _ _ ⟨g, _⟩) _, RingHom.id_comp]
#align zmod.ring_hom_eq_of_ker_eq ZMod.ringHom_eq_of_ker_eq

section lift

variable (n) {A : Type _} [AddGroup A]

/-- The map from `zmod n` induced by `f : ℤ →+ A` that maps `n` to `0`. -/
@[simps]
def lift : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A) :=
  (Equiv.subtypeEquivRight <| by
        intro f
        rw [ker_int_cast_add_hom]
        constructor
        · rintro hf _ ⟨x, rfl⟩
          simp only [f.map_zsmul, zsmul_zero, f.mem_ker, hf]
        · intro h
          refine' h (AddSubgroup.mem_zmultiples _)).trans <|
    (Int.castAddHom (ZMod n)).liftOfRightInverse coe int_cast_zMod_cast
#align zmod.lift ZMod.lift

variable (f : { f : ℤ →+ A // f n = 0 })

@[simp]
theorem lift_coe (x : ℤ) : lift n f (x : ZMod n) = f x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
#align zmod.lift_coe ZMod.lift_coe

theorem lift_castAddHom (x : ℤ) : lift n f (Int.castAddHom (ZMod n) x) = f x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
#align zmod.lift_cast_add_hom ZMod.lift_castAddHom

@[simp]
theorem lift_comp_coe : ZMod.lift n f ∘ coe = f :=
  funext <| lift_coe _ _
#align zmod.lift_comp_coe ZMod.lift_comp_coe

@[simp]
theorem lift_comp_castAddHom : (ZMod.lift n f).comp (Int.castAddHom (ZMod n)) = f :=
  AddMonoidHom.ext <| lift_castAddHom _ _
#align zmod.lift_comp_cast_add_hom ZMod.lift_comp_castAddHom

end lift

end ZMod

