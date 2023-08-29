/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Nat.Parity
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

open Function

namespace ZMod

instance charZero : CharZero (ZMod 0) :=
  (by infer_instance : CharZero ℤ)
      -- 🎉 no goals

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
  -- ⊢ val a < Nat.zero
  · cases NeZero.ne 0 rfl
    -- 🎉 no goals
  exact Fin.is_lt a
  -- 🎉 no goals
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

theorem val_nat_cast {n : ℕ} (a : ℕ) : (a : ZMod n).val = a % n := by
  cases n
  -- ⊢ val ↑a = a % Nat.zero
  · rw [Nat.mod_zero]
    -- ⊢ val ↑a = a
    exact Int.natAbs_ofNat a
    -- 🎉 no goals
  rw [← Fin.ofNat_eq_val]
  -- ⊢ val (Fin.ofNat'' a) = a % Nat.succ n✝
  rfl
  -- 🎉 no goals
#align zmod.val_nat_cast ZMod.val_nat_cast

instance charP (n : ℕ) : CharP (ZMod n) n where
    cast_eq_zero_iff' := by
      intro k
      -- ⊢ ↑k = 0 ↔ n ∣ k
      cases' n with n
      -- ⊢ ↑k = 0 ↔ Nat.zero ∣ k
      · simp [zero_dvd_iff, Int.coe_nat_eq_zero, Nat.zero_eq]
        -- 🎉 no goals
      rw [Fin.eq_iff_veq]
      -- ⊢ ↑↑k = ↑0 ↔ Nat.succ n ∣ k
      show (k : ZMod (n + 1)).val = (0 : ZMod (n + 1)).val ↔ _
      -- ⊢ val ↑k = val 0 ↔ Nat.succ n ∣ k
      rw [val_nat_cast, val_zero, Nat.dvd_iff_mod_eq_zero]
      -- 🎉 no goals

@[simp]
theorem addOrderOf_one (n : ℕ) : addOrderOf (1 : ZMod n) = n :=
  CharP.eq _ (CharP.addOrderOf_one _) (ZMod.charP n)
#align zmod.add_order_of_one ZMod.addOrderOf_one

/-- This lemma works in the case in which `ZMod n` is not infinite, i.e. `n ≠ 0`.  The version
where `a ≠ 0` is `addOrderOf_coe'`. -/
@[simp]
theorem addOrderOf_coe (a : ℕ) {n : ℕ} (n0 : n ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  cases' a with a
  -- ⊢ addOrderOf ↑Nat.zero = n / Nat.gcd n Nat.zero
  simp [Nat.pos_of_ne_zero n0]
  -- ⊢ addOrderOf ↑(Nat.succ a) = n / Nat.gcd n (Nat.succ a)
  rw [← Nat.smul_one_eq_coe, addOrderOf_nsmul' _ a.succ_ne_zero, ZMod.addOrderOf_one]
  -- 🎉 no goals
#align zmod.add_order_of_coe ZMod.addOrderOf_coe

/-- This lemma works in the case in which `a ≠ 0`.  The version where
 `ZMod n` is not infinite, i.e. `n ≠ 0`, is `addOrderOf_coe`. -/
@[simp]
theorem addOrderOf_coe' {a : ℕ} (n : ℕ) (a0 : a ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rw [← Nat.smul_one_eq_coe, addOrderOf_nsmul' _ a0, ZMod.addOrderOf_one]
  -- 🎉 no goals
#align zmod.add_order_of_coe' ZMod.addOrderOf_coe'

/-- We have that `ringChar (ZMod n) = n`. -/
theorem ringChar_zmod_n (n : ℕ) : ringChar (ZMod n) = n := by
  rw [ringChar.eq_iff]
  -- ⊢ CharP (ZMod n) n
  exact ZMod.charP n
  -- 🎉 no goals
#align zmod.ring_char_zmod_n ZMod.ringChar_zmod_n

-- @[simp] -- Porting note: simp can prove this
theorem nat_cast_self (n : ℕ) : (n : ZMod n) = 0 :=
  CharP.cast_eq_zero (ZMod n) n
#align zmod.nat_cast_self ZMod.nat_cast_self

@[simp]
theorem nat_cast_self' (n : ℕ) : (n + 1 : ZMod (n + 1)) = 0 := by
  rw [← Nat.cast_add_one, nat_cast_self (n + 1)]
  -- 🎉 no goals
#align zmod.nat_cast_self' ZMod.nat_cast_self'

section UniversalProperty

variable {n : ℕ} {R : Type*}

section

variable [AddGroupWithOne R]

/-- Cast an integer modulo `n` to another semiring.
This function is a morphism if the characteristic of `R` divides `n`.
See `ZMod.cast_hom` for a bundled version. -/
@[coe] def cast : ∀ {n : ℕ}, ZMod n → R
  | 0 => Int.cast
  | _ + 1 => fun i => i.val
#align zmod.cast ZMod.cast

-- see Note [coercion into rings]
instance (priority := 900) (n : ℕ) : CoeTC (ZMod n) R :=
  ⟨cast⟩

@[simp]
theorem cast_zero : ((0 : ZMod n) : R) = 0 := by
  delta ZMod.cast
  -- ⊢ (match (motive := (x : ℕ) → ZMod x → R) n with
  cases n
  · exact Int.cast_zero
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align zmod.cast_zero ZMod.cast_zero

theorem cast_eq_val [NeZero n] (a : ZMod n) : (a : R) = a.val := by
  cases n
  -- ⊢ ↑a = ↑(val a)
  · cases NeZero.ne 0 rfl
    -- 🎉 no goals
  rfl
  -- 🎉 no goals
#align zmod.cast_eq_val ZMod.cast_eq_val

variable {S : Type*} [AddGroupWithOne S]

@[simp]
theorem _root_.Prod.fst_zmod_cast (a : ZMod n) : (a : R × S).fst = a := by
  cases n
  -- ⊢ (↑a).fst = ↑a
  · rfl
    -- 🎉 no goals
  · simp [ZMod.cast]
    -- 🎉 no goals
#align prod.fst_zmod_cast Prod.fst_zmod_cast

@[simp]
theorem _root_.Prod.snd_zmod_cast (a : ZMod n) : (a : R × S).snd = a := by
  cases n
  -- ⊢ (↑a).snd = ↑a
  · rfl
    -- 🎉 no goals
  · simp [ZMod.cast]
    -- 🎉 no goals
#align prod.snd_zmod_cast Prod.snd_zmod_cast

end

/-- So-named because the coercion is `Nat.cast` into `ZMod`. For `Nat.cast` into an arbitrary ring,
see `ZMod.nat_cast_val`. -/
theorem nat_cast_zmod_val {n : ℕ} [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a := by
  cases n
  -- ⊢ ↑(val a) = a
  · cases NeZero.ne 0 rfl
    -- 🎉 no goals
  · apply Fin.cast_val_eq_self
    -- 🎉 no goals
#align zmod.nat_cast_zmod_val ZMod.nat_cast_zmod_val

theorem nat_cast_rightInverse [NeZero n] : Function.RightInverse val ((↑) : ℕ → ZMod n) :=
  nat_cast_zmod_val
#align zmod.nat_cast_right_inverse ZMod.nat_cast_rightInverse

theorem nat_cast_zmod_surjective [NeZero n] : Function.Surjective ((↑) : ℕ → ZMod n) :=
  nat_cast_rightInverse.surjective
#align zmod.nat_cast_zmod_surjective ZMod.nat_cast_zmod_surjective

/-- So-named because the outer coercion is `Int.cast` into `ZMod`. For `Int.cast` into an arbitrary
ring, see `ZMod.int_cast_cast`. -/
@[norm_cast]
theorem int_cast_zmod_cast (a : ZMod n) : ((a : ℤ) : ZMod n) = a := by
  cases n
  -- ⊢ ↑↑a = a
  · simp [ZMod.cast, ZMod]
    -- 🎉 no goals
  · dsimp [ZMod.cast, ZMod]
    -- ⊢ ↑↑(val a) = a
    erw [Int.cast_ofNat, Fin.cast_val_eq_self]
    -- 🎉 no goals
#align zmod.int_cast_zmod_cast ZMod.int_cast_zmod_cast

theorem int_cast_rightInverse : Function.RightInverse ((↑) : ZMod n → ℤ) ((↑) : ℤ → ZMod n) :=
  int_cast_zmod_cast
#align zmod.int_cast_right_inverse ZMod.int_cast_rightInverse

theorem int_cast_surjective : Function.Surjective ((↑) : ℤ → ZMod n) :=
  int_cast_rightInverse.surjective
#align zmod.int_cast_surjective ZMod.int_cast_surjective

@[norm_cast]
theorem cast_id : ∀ (n) (i : ZMod n), (ZMod.cast i : ZMod n) = i
  | 0, _ => Int.cast_id
  | _ + 1, i => nat_cast_zmod_val i
#align zmod.cast_id ZMod.cast_id

@[simp]
theorem cast_id' : (ZMod.cast : ZMod n → ZMod n) = id :=
  funext (cast_id n)
#align zmod.cast_id' ZMod.cast_id'

variable (R) [Ring R]

/-- The coercions are respectively `Nat.cast` and `ZMod.cast`. -/
@[simp]
theorem nat_cast_comp_val [NeZero n] : ((↑) : ℕ → R) ∘ (val : ZMod n → ℕ) = (↑) := by
  cases n
  -- ⊢ Nat.cast ∘ val = cast
  · cases NeZero.ne 0 rfl
    -- 🎉 no goals
  rfl
  -- 🎉 no goals
#align zmod.nat_cast_comp_val ZMod.nat_cast_comp_val

/-- The coercions are respectively `Int.cast`, `ZMod.cast`, and `ZMod.cast`. -/
@[simp]
theorem int_cast_comp_cast : ((↑) : ℤ → R) ∘ ((↑) : ZMod n → ℤ) = (↑) := by
  cases n
  -- ⊢ Int.cast ∘ cast = cast
  · exact congr_arg ((· ∘ ·) Int.cast) ZMod.cast_id'
    -- 🎉 no goals
  · ext
    -- ⊢ (Int.cast ∘ cast) x✝ = ↑x✝
    simp [ZMod, ZMod.cast]
    -- 🎉 no goals
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
    (↑(a + b) : ℤ) = if (n : ℤ) ≤ a + b then (a : ℤ) + b - n else a + b := by
  cases' n with n
  -- ⊢ ↑(a + b) = if ↑Nat.zero ≤ ↑a + ↑b then ↑a + ↑b - ↑Nat.zero else ↑a + ↑b
  · simp; rfl
    -- ⊢ ↑(a + b) = ↑a + ↑b
          -- 🎉 no goals
  change Fin (n + 1) at a b
  -- ⊢ ↑(a + b) = if ↑(Nat.succ n) ≤ ↑a + ↑b then ↑a + ↑b - ↑(Nat.succ n) else ↑a + …
  change ((((a + b) : Fin (n + 1)) : ℕ) : ℤ) = if ((n + 1 : ℕ) : ℤ) ≤ (a : ℕ) + b then _ else _
  -- ⊢ ↑↑(a + b) = if ↑(n + 1) ≤ ↑↑a + ↑↑b then ↑a + ↑b - ↑(Nat.succ n) else ↑a + ↑b
  simp only [Fin.val_add_eq_ite, Int.ofNat_succ, Int.ofNat_le]
  -- ⊢ ↑(if n + 1 ≤ ↑a + ↑b then ↑a + ↑b - (n + 1) else ↑a + ↑b) = if ↑n + 1 ≤ ↑↑a  …
  norm_cast
  -- ⊢ ↑(if n + 1 ≤ ↑a + ↑b then ↑a + ↑b - (n + 1) else ↑a + ↑b) = if n + 1 ≤ ↑a +  …
  split_ifs with h
  -- ⊢ ↑(↑a + ↑b - (n + 1)) = ↑a + ↑b - ↑(n + 1)
  · rw [Nat.cast_sub h]
    -- ⊢ ↑(↑a + ↑b) - ↑(n + 1) = ↑a + ↑b - ↑(n + 1)
    congr
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align zmod.coe_add_eq_ite ZMod.coe_add_eq_ite

section CharDvd

/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/


variable {m : ℕ} [CharP R m]

@[simp]
theorem cast_one (h : m ∣ n) : ((1 : ZMod n) : R) = 1 := by
  cases' n with n
  -- ⊢ ↑1 = 1
  · exact Int.cast_one
    -- 🎉 no goals
  show ((1 % (n + 1) : ℕ) : R) = 1
  -- ⊢ ↑(1 % (n + 1)) = 1
  cases n;
  -- ⊢ ↑(1 % (Nat.zero + 1)) = 1
  · rw [Nat.dvd_one] at h
    -- ⊢ ↑(1 % (Nat.zero + 1)) = 1
    subst m
    -- ⊢ ↑(1 % (Nat.zero + 1)) = 1
    apply Subsingleton.elim
    -- 🎉 no goals
  rw [Nat.mod_eq_of_lt]
  -- ⊢ ↑1 = 1
  · exact Nat.cast_one
    -- 🎉 no goals
  exact Nat.lt_of_sub_eq_succ rfl
  -- 🎉 no goals
#align zmod.cast_one ZMod.cast_one

theorem cast_add (h : m ∣ n) (a b : ZMod n) : ((a + b : ZMod n) : R) = a + b := by
  cases n
  -- ⊢ ↑(a + b) = ↑a + ↑b
  · apply Int.cast_add
    -- 🎉 no goals
  symm
  -- ⊢ ↑a + ↑b = ↑(a + b)
  dsimp [ZMod, ZMod.cast]
  -- ⊢ ↑(val a) + ↑(val b) = ↑(val (a + b))
  erw [← Nat.cast_add, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)
  -- 🎉 no goals
#align zmod.cast_add ZMod.cast_add

theorem cast_mul (h : m ∣ n) (a b : ZMod n) : ((a * b : ZMod n) : R) = a * b := by
  cases n
  -- ⊢ ↑(a * b) = ↑a * ↑b
  · apply Int.cast_mul
    -- 🎉 no goals
  symm
  -- ⊢ ↑a * ↑b = ↑(a * b)
  dsimp [ZMod, ZMod.cast]
  -- ⊢ ↑(val a) * ↑(val b) = ↑(val (a * b))
  erw [← Nat.cast_mul, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)
  -- 🎉 no goals
#align zmod.cast_mul ZMod.cast_mul

/-- The canonical ring homomorphism from `ZMod n` to a ring of characteristic `n`.

See also `ZMod.lift` (in `Data.ZMod.Quotient`) for a generalized version working in `AddGroup`s.
-/
def castHom (h : m ∣ n) (R : Type*) [Ring R] [CharP R m] : ZMod n →+* R where
  toFun := (↑)
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
theorem cast_sub (h : m ∣ n) (a b : ZMod n) : ((a - b : ZMod n) : R) = (a : R) - b :=
  (castHom h R).map_sub a b
#align zmod.cast_sub ZMod.cast_sub

@[simp, norm_cast]
theorem cast_neg (h : m ∣ n) (a : ZMod n) : ((-a : ZMod n) : R) = -(a : R) :=
  (castHom h R).map_neg a
#align zmod.cast_neg ZMod.cast_neg

@[simp, norm_cast]
theorem cast_pow (h : m ∣ n) (a : ZMod n) (k : ℕ) : ((a ^ k : ZMod n) : R) = (a : R) ^ k :=
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
theorem cast_pow' (a : ZMod n) (k : ℕ) : ((a ^ k : ZMod n) : R) = (a : R) ^ k :=
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

theorem castHom_injective : Function.Injective (ZMod.castHom (dvd_refl n) R) := by
  rw [injective_iff_map_eq_zero]
  -- ⊢ ∀ (a : ZMod n), ↑(castHom (_ : n ∣ n) R) a = 0 → a = 0
  intro x
  -- ⊢ ↑(castHom (_ : n ∣ n) R) x = 0 → x = 0
  obtain ⟨k, rfl⟩ := ZMod.int_cast_surjective x
  -- ⊢ ↑(castHom (_ : n ∣ n) R) ↑k = 0 → ↑k = 0
  rw [map_intCast, CharP.int_cast_eq_zero_iff R n, CharP.int_cast_eq_zero_iff (ZMod n) n]
  -- ⊢ ↑n ∣ k → ↑n ∣ k
  exact id
  -- 🎉 no goals
#align zmod.cast_hom_injective ZMod.castHom_injective

theorem castHom_bijective [Fintype R] (h : Fintype.card R = n) :
    Function.Bijective (ZMod.castHom (dvd_refl n) R) := by
  haveI : NeZero n :=
    ⟨by
      intro hn
      rw [hn] at h
      exact (Fintype.card_eq_zero_iff.mp h).elim' 0⟩
  rw [Fintype.bijective_iff_injective_and_card, ZMod.card, h, eq_self_iff_true, and_true_iff]
  -- ⊢ Injective ↑(castHom (_ : n ∣ n) R)
  apply ZMod.castHom_injective
  -- 🎉 no goals
#align zmod.cast_hom_bijective ZMod.castHom_bijective

/-- The unique ring isomorphism between `ZMod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
noncomputable def ringEquiv [Fintype R] (h : Fintype.card R = n) : ZMod n ≃+* R :=
  RingEquiv.ofBijective _ (ZMod.castHom_bijective R h)
#align zmod.ring_equiv ZMod.ringEquiv

/-- The identity between `ZMod m` and `ZMod n` when `m = n`, as a ring isomorphism. -/
def ringEquivCongr {m n : ℕ} (h : m = n) : ZMod m ≃+* ZMod n := by
  cases' m with m <;> cases' n with n
  -- ⊢ ZMod Nat.zero ≃+* ZMod n
                      -- ⊢ ZMod Nat.zero ≃+* ZMod Nat.zero
                      -- ⊢ ZMod (Nat.succ m) ≃+* ZMod Nat.zero
  · exact RingEquiv.refl _
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    exact n.succ_ne_zero h.symm
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    exact m.succ_ne_zero h
    -- 🎉 no goals
  · exact
      { Fin.castIso h with
        map_mul' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.coe_castIso, Fin.coe_mul, Fin.coe_mul, Fin.coe_castIso, Fin.coe_castIso, ← h]
        map_add' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.coe_castIso, Fin.val_add, Fin.val_add, Fin.coe_castIso, Fin.coe_castIso, ← h] }
#align zmod.ring_equiv_congr ZMod.ringEquivCongr

end CharEq

end UniversalProperty

theorem int_cast_eq_int_cast_iff (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c] :=
  CharP.intCast_eq_intCast (ZMod c) c
#align zmod.int_coe_eq_int_coe_iff ZMod.int_cast_eq_int_cast_iff

theorem int_cast_eq_int_cast_iff' (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.int_cast_eq_int_cast_iff a b c
#align zmod.int_coe_eq_int_coe_iff' ZMod.int_cast_eq_int_cast_iff'

theorem nat_cast_eq_nat_cast_iff (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c] := by
  simpa [Int.coe_nat_modEq_iff] using ZMod.int_cast_eq_int_cast_iff a b c
  -- 🎉 no goals
#align zmod.nat_coe_eq_nat_coe_iff ZMod.nat_cast_eq_nat_cast_iff

theorem nat_cast_eq_nat_cast_iff' (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.nat_cast_eq_nat_cast_iff a b c
#align zmod.nat_coe_eq_nat_coe_iff' ZMod.nat_cast_eq_nat_cast_iff'

theorem int_cast_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : ZMod b) = 0 ↔ (b : ℤ) ∣ a := by
  rw [← Int.cast_zero, ZMod.int_cast_eq_int_cast_iff, Int.modEq_zero_iff_dvd]
  -- 🎉 no goals
#align zmod.int_coe_zmod_eq_zero_iff_dvd ZMod.int_cast_zmod_eq_zero_iff_dvd

theorem int_cast_eq_int_cast_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : ZMod c) = ↑b ↔ ↑c ∣ b - a := by
  rw [ZMod.int_cast_eq_int_cast_iff, Int.modEq_iff_dvd]
  -- 🎉 no goals
#align zmod.int_coe_eq_int_coe_iff_dvd_sub ZMod.int_cast_eq_int_cast_iff_dvd_sub

theorem nat_cast_zmod_eq_zero_iff_dvd (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a := by
  rw [← Nat.cast_zero, ZMod.nat_cast_eq_nat_cast_iff, Nat.modEq_zero_iff_dvd]
  -- 🎉 no goals
#align zmod.nat_coe_zmod_eq_zero_iff_dvd ZMod.nat_cast_zmod_eq_zero_iff_dvd

theorem val_int_cast {n : ℕ} (a : ℤ) [NeZero n] : ↑(a : ZMod n).val = a % n := by
  have hle : (0 : ℤ) ≤ ↑(a : ZMod n).val := Int.coe_nat_nonneg _
  -- ⊢ ↑(val ↑a) = a % ↑n
  have hlt : ↑(a : ZMod n).val < (n : ℤ) := Int.ofNat_lt.mpr (ZMod.val_lt a)
  -- ⊢ ↑(val ↑a) = a % ↑n
  refine' (Int.emod_eq_of_lt hle hlt).symm.trans _
  -- ⊢ ↑(val ↑a) % ↑n = a % ↑n
  rw [← ZMod.int_cast_eq_int_cast_iff', Int.cast_ofNat, ZMod.nat_cast_val, ZMod.cast_id]
  -- 🎉 no goals
#align zmod.val_int_cast ZMod.val_int_cast

theorem coe_int_cast {n : ℕ} (a : ℤ) : ↑(a : ZMod n) = a % n := by
  cases n
  -- ⊢ ↑↑a = a % ↑Nat.zero
  · rw [Int.ofNat_zero, Int.emod_zero, Int.cast_id]; rfl
    -- ⊢ ↑a = a
                                                     -- 🎉 no goals
  · rw [← val_int_cast, val]; rfl
    -- ⊢ ↑↑a =
                              -- 🎉 no goals
#align zmod.coe_int_cast ZMod.coe_int_cast

@[simp]
theorem val_neg_one (n : ℕ) : (-1 : ZMod n.succ).val = n := by
  dsimp [val, Fin.coe_neg]
  -- ⊢ ↑(-1) = n
  cases n
  -- ⊢ ↑(-1) = Nat.zero
  · simp [Nat.mod_one]
    -- 🎉 no goals
  · dsimp [ZMod, ZMod.cast]
    -- ⊢ ↑(-1) = Nat.succ n✝
    rw [Fin.coe_neg_one]
    -- 🎉 no goals
#align zmod.val_neg_one ZMod.val_neg_one

/-- `-1 : ZMod n` lifts to `n - 1 : R`. This avoids the characteristic assumption in `cast_neg`. -/
theorem cast_neg_one {R : Type*} [Ring R] (n : ℕ) : ↑(-1 : ZMod n) = (n - 1 : R) := by
  cases' n with n
  -- ⊢ ↑(-1) = ↑Nat.zero - 1
  · dsimp [ZMod, ZMod.cast]; simp
    -- ⊢ ↑(-1) = ↑0 - 1
                             -- 🎉 no goals
  · rw [← nat_cast_val, val_neg_one, Nat.cast_succ, add_sub_cancel]
    -- 🎉 no goals
#align zmod.cast_neg_one ZMod.cast_neg_one

theorem cast_sub_one {R : Type*} [Ring R] {n : ℕ} (k : ZMod n) :
    ((k - 1 : ZMod n) : R) = (if k = 0 then (n : R) else k) - 1 := by
  split_ifs with hk
  -- ⊢ ↑(k - 1) = ↑n - 1
  · rw [hk, zero_sub, ZMod.cast_neg_one]
    -- 🎉 no goals
  · cases n
    -- ⊢ ↑(k - 1) = ↑k - 1
    · dsimp [ZMod, ZMod.cast]
      -- ⊢ ↑(k - 1) = ↑k - 1
      rw [Int.cast_sub, Int.cast_one]
      -- 🎉 no goals
    · dsimp [ZMod, ZMod.cast, ZMod.val]
      -- ⊢ ↑↑(k - 1) = ↑↑k - 1
      rw [Fin.coe_sub_one, if_neg]
      -- ⊢ ↑(↑k - 1) = ↑↑k - 1
      · rw [Nat.cast_sub, Nat.cast_one]
        -- ⊢ 1 ≤ ↑k
        rwa [Fin.ext_iff, Fin.val_zero, ← Ne, ← Nat.one_le_iff_ne_zero] at hk
        -- 🎉 no goals
      · exact hk
        -- 🎉 no goals
#align zmod.cast_sub_one ZMod.cast_sub_one

theorem nat_coe_zmod_eq_iff (p : ℕ) (n : ℕ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  -- ⊢ ↑n = z → ∃ k, n = val z + p * k
  · rintro rfl
    -- ⊢ ∃ k, n = val ↑n + p * k
    refine' ⟨n / p, _⟩
    -- ⊢ n = val ↑n + p * (n / p)
    rw [val_nat_cast, Nat.mod_add_div]
    -- 🎉 no goals
  · rintro ⟨k, rfl⟩
    -- ⊢ ↑(val z + p * k) = z
    rw [Nat.cast_add, nat_cast_zmod_val, Nat.cast_mul, nat_cast_self, zero_mul,
      add_zero]
#align zmod.nat_coe_zmod_eq_iff ZMod.nat_coe_zmod_eq_iff

theorem int_coe_zmod_eq_iff (p : ℕ) (n : ℤ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  -- ⊢ ↑n = z → ∃ k, n = ↑(val z) + ↑p * k
  · rintro rfl
    -- ⊢ ∃ k, n = ↑(val ↑n) + ↑p * k
    refine' ⟨n / p, _⟩
    -- ⊢ n = ↑(val ↑n) + ↑p * (n / ↑p)
    rw [val_int_cast, Int.emod_add_ediv]
    -- 🎉 no goals
  · rintro ⟨k, rfl⟩
    -- ⊢ ↑(↑(val z) + ↑p * k) = z
    rw [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_ofNat, nat_cast_val,
      ZMod.nat_cast_self, zero_mul, add_zero, cast_id]
#align zmod.int_coe_zmod_eq_iff ZMod.int_coe_zmod_eq_iff

@[push_cast, simp]
theorem int_cast_mod (a : ℤ) (b : ℕ) : ((a % b : ℤ) : ZMod b) = (a : ZMod b) := by
  rw [ZMod.int_cast_eq_int_cast_iff]
  -- ⊢ a % ↑b ≡ a [ZMOD ↑b]
  apply Int.mod_modEq
  -- 🎉 no goals
#align zmod.int_cast_mod ZMod.int_cast_mod

theorem ker_int_castAddHom (n : ℕ) :
    (Int.castAddHom (ZMod n)).ker = AddSubgroup.zmultiples (n : ℤ) := by
  ext
  -- ⊢ x✝ ∈ AddMonoidHom.ker (Int.castAddHom (ZMod n)) ↔ x✝ ∈ AddSubgroup.zmultiple …
  rw [Int.mem_zmultiples_iff, AddMonoidHom.mem_ker, Int.coe_castAddHom,
    int_cast_zmod_eq_zero_iff_dvd]
#align zmod.ker_int_cast_add_hom ZMod.ker_int_castAddHom

theorem ker_int_castRingHom (n : ℕ) :
    RingHom.ker (Int.castRingHom (ZMod n)) = Ideal.span ({(n : ℤ)} : Set ℤ) := by
  ext
  -- ⊢ x✝ ∈ RingHom.ker (Int.castRingHom (ZMod n)) ↔ x✝ ∈ Ideal.span {↑n}
  rw [Ideal.mem_span_singleton, RingHom.mem_ker, Int.coe_castRingHom, int_cast_zmod_eq_zero_iff_dvd]
  -- 🎉 no goals
#align zmod.ker_int_cast_ring_hom ZMod.ker_int_castRingHom

--Porting note: commented
-- attribute [local semireducible] Int.NonNeg

@[simp]
theorem nat_cast_toNat (p : ℕ) : ∀ {z : ℤ} (_h : 0 ≤ z), (z.toNat : ZMod p) = z
  | (n : ℕ), _h => by simp only [Int.cast_ofNat, Int.toNat_coe_nat]
                      -- 🎉 no goals
  | Int.negSucc n, h => by simp at h
                           -- 🎉 no goals
#align zmod.nat_cast_to_nat ZMod.nat_cast_toNat

theorem val_injective (n : ℕ) [NeZero n] : Function.Injective (ZMod.val : ZMod n → ℕ) := by
  cases n
  -- ⊢ Injective val
  · cases NeZero.ne 0 rfl
    -- 🎉 no goals
  intro a b h
  -- ⊢ a = b
  dsimp [ZMod]
  -- ⊢ a = b
  ext
  -- ⊢ ↑a = ↑b
  exact h
  -- 🎉 no goals
#align zmod.val_injective ZMod.val_injective

theorem val_one_eq_one_mod (n : ℕ) : (1 : ZMod n).val = 1 % n := by
  rw [← Nat.cast_one, val_nat_cast]
  -- 🎉 no goals
#align zmod.val_one_eq_one_mod ZMod.val_one_eq_one_mod

theorem val_one (n : ℕ) [Fact (1 < n)] : (1 : ZMod n).val = 1 := by
  rw [val_one_eq_one_mod]
  -- ⊢ 1 % n = 1
  exact Nat.mod_eq_of_lt Fact.out
  -- 🎉 no goals
#align zmod.val_one ZMod.val_one

theorem val_add {n : ℕ} [NeZero n] (a b : ZMod n) : (a + b).val = (a.val + b.val) % n := by
  cases n
  -- ⊢ val (a + b) = (val a + val b) % Nat.zero
  · cases NeZero.ne 0 rfl
    -- 🎉 no goals
  · apply Fin.val_add
    -- 🎉 no goals
#align zmod.val_add ZMod.val_add

theorem val_mul {n : ℕ} (a b : ZMod n) : (a * b).val = a.val * b.val % n := by
  cases n
  -- ⊢ val (a * b) = val a * val b % Nat.zero
  · rw [Nat.mod_zero]
    -- ⊢ val (a * b) = val a * val b
    apply Int.natAbs_mul
    -- 🎉 no goals
  · apply Fin.val_mul
    -- 🎉 no goals
#align zmod.val_mul ZMod.val_mul

instance nontrivial (n : ℕ) [Fact (1 < n)] : Nontrivial (ZMod n) :=
  ⟨⟨0, 1, fun h =>
      zero_ne_one <|
        calc
          0 = (0 : ZMod n).val := by rw [val_zero]
                                     -- 🎉 no goals
          _ = (1 : ZMod n).val := (congr_arg ZMod.val h)
          _ = 1 := val_one n
          ⟩⟩
#align zmod.nontrivial ZMod.nontrivial

instance nontrivial' : Nontrivial (ZMod 0) :=
  by delta ZMod; infer_instance
     -- ⊢ Nontrivial
                 -- 🎉 no goals
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
      -- ⊢ ↑(Nat.gcdA 0 (n + 1)) = 0
      unfold Nat.gcdA Nat.xgcd Nat.xgcdAux
      -- ⊢ ↑(n + 1, 0, 1).snd.fst = 0
      rfl
      -- 🎉 no goals
#align zmod.inv_zero ZMod.inv_zero

theorem mul_inv_eq_gcd {n : ℕ} (a : ZMod n) : a * a⁻¹ = Nat.gcd a.val n := by
  cases' n with n
  -- ⊢ a * a⁻¹ = ↑(Nat.gcd (val a) Nat.zero)
  · dsimp [ZMod] at a ⊢
    -- ⊢ a * a⁻¹ = ↑(Nat.gcd (val a) 0)
    calc
      _ = a * Int.sign a := rfl
      _ = a.natAbs := by rw [Int.mul_sign]
      _ = a.natAbs.gcd 0 := by rw [Nat.gcd_zero_right]
  · calc
      a * a⁻¹ = a * a⁻¹ + n.succ * Nat.gcdB (val a) n.succ := by
        rw [nat_cast_self, zero_mul, add_zero]
      _ = ↑(↑a.val * Nat.gcdA (val a) n.succ + n.succ * Nat.gcdB (val a) n.succ) := by
        push_cast
        rw [nat_cast_zmod_val]
        rfl
      _ = Nat.gcd a.val n.succ := by rw [← Nat.gcd_eq_gcd_ab a.val n.succ]; rfl
#align zmod.mul_inv_eq_gcd ZMod.mul_inv_eq_gcd

@[simp]
theorem nat_cast_mod (a : ℕ) (n : ℕ) : ((a % n : ℕ) : ZMod n) = a := by
  conv =>
      rhs
      rw [← Nat.mod_add_div a n]
  simp
  -- 🎉 no goals
#align zmod.nat_cast_mod ZMod.nat_cast_mod

theorem eq_iff_modEq_nat (n : ℕ) {a b : ℕ} : (a : ZMod n) = b ↔ a ≡ b [MOD n] := by
  cases n
  -- ⊢ ↑a = ↑b ↔ a ≡ b [MOD Nat.zero]
  · simp [Nat.ModEq, Int.coe_nat_inj', Nat.mod_zero]
    -- 🎉 no goals
  · rw [Fin.ext_iff, Nat.ModEq, ← val_nat_cast, ← val_nat_cast]
    -- ⊢ ↑↑a = ↑↑b ↔ val ↑a = val ↑b
    exact Iff.rfl
    -- 🎉 no goals
#align zmod.eq_iff_modeq_nat ZMod.eq_iff_modEq_nat

theorem coe_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : Nat.coprime x n) :
    ((x : ZMod n) * (x : ZMod n)⁻¹) = 1 := by
  rw [Nat.coprime, Nat.gcd_comm, Nat.gcd_rec] at h
  -- ⊢ ↑x * (↑x)⁻¹ = 1
  rw [mul_inv_eq_gcd, val_nat_cast, h, Nat.cast_one]
  -- 🎉 no goals
#align zmod.coe_mul_inv_eq_one ZMod.coe_mul_inv_eq_one

/-- `unitOfCoprime` makes an element of `(ZMod n)ˣ` given
  a natural number `x` and a proof that `x` is coprime to `n`  -/
def unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.coprime x n) : (ZMod n)ˣ :=
  ⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩
                                      -- 🎉 no goals
#align zmod.unit_of_coprime ZMod.unitOfCoprime

@[simp]
theorem coe_unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.coprime x n) :
    (unitOfCoprime x h : ZMod n) = x :=
  rfl
#align zmod.coe_unit_of_coprime ZMod.coe_unitOfCoprime

theorem val_coe_unit_coprime {n : ℕ} (u : (ZMod n)ˣ) : Nat.coprime (u : ZMod n).val n := by
  cases' n with n
  -- ⊢ Nat.coprime (val ↑u) Nat.zero
  · rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp
    -- ⊢ Nat.coprime (val ↑1) Nat.zero
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
  apply Nat.coprime_of_mul_modEq_one ((u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1)).val
  -- ⊢ val ↑u * val ↑u⁻¹ ≡ 1 [MOD Nat.succ n]
  have := Units.ext_iff.1 (mul_right_inv u)
  -- ⊢ val ↑u * val ↑u⁻¹ ≡ 1 [MOD Nat.succ n]
  rw [Units.val_one] at this
  -- ⊢ val ↑u * val ↑u⁻¹ ≡ 1 [MOD Nat.succ n]
  rw [← eq_iff_modEq_nat, Nat.cast_one, ← this]; clear this
  -- ⊢ ↑(val ↑u * val ↑u⁻¹) = ↑(u * u⁻¹)
                                                 -- ⊢ ↑(val ↑u * val ↑u⁻¹) = ↑(u * u⁻¹)
  rw [← nat_cast_zmod_val ((u * u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1))]
  -- ⊢ ↑(val ↑u * val ↑u⁻¹) = ↑(val ↑(u * u⁻¹))
  rw [Units.val_mul, val_mul, nat_cast_mod]
  -- 🎉 no goals
#align zmod.val_coe_unit_coprime ZMod.val_coe_unit_coprime

@[simp]
theorem inv_coe_unit {n : ℕ} (u : (ZMod n)ˣ) : (u : ZMod n)⁻¹ = (u⁻¹ : (ZMod n)ˣ) := by
  have := congr_arg ((↑) : ℕ → ZMod n) (val_coe_unit_coprime u)
  -- ⊢ (↑u)⁻¹ = ↑u⁻¹
  rw [← mul_inv_eq_gcd, Nat.cast_one] at this
  -- ⊢ (↑u)⁻¹ = ↑u⁻¹
  let u' : (ZMod n)ˣ := ⟨u, (u : ZMod n)⁻¹, this, by rwa [mul_comm]⟩
  -- ⊢ (↑u)⁻¹ = ↑u⁻¹
  have h : u = u' := by
    apply Units.ext
    rfl
  rw [h]
  -- ⊢ (↑u')⁻¹ = ↑u'⁻¹
  rfl
  -- 🎉 no goals
#align zmod.inv_coe_unit ZMod.inv_coe_unit

theorem mul_inv_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a * a⁻¹ = 1 := by
  rcases h with ⟨u, rfl⟩
  -- ⊢ ↑u * (↑u)⁻¹ = 1
  rw [inv_coe_unit, u.mul_inv]
  -- 🎉 no goals
#align zmod.mul_inv_of_unit ZMod.mul_inv_of_unit

theorem inv_mul_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_of_unit a h]
  -- 🎉 no goals
#align zmod.inv_mul_of_unit ZMod.inv_mul_of_unit

-- TODO: this equivalence is true for `ZMod 0 = ℤ`, but needs to use different functions.
/-- Equivalence between the units of `ZMod n` and
the subtype of terms `x : ZMod n` for which `x.val` is coprime to `n` -/
def unitsEquivCoprime {n : ℕ} [NeZero n] : (ZMod n)ˣ ≃ { x : ZMod n // Nat.coprime x.val n }
    where
  toFun x := ⟨x, val_coe_unit_coprime x⟩
  invFun x := unitOfCoprime x.1.val x.2
  left_inv := fun ⟨_, _, _, _⟩ => Units.ext (nat_cast_zmod_val _)
  right_inv := fun ⟨_, _⟩ => by simp
                                -- 🎉 no goals
#align zmod.units_equiv_coprime ZMod.unitsEquivCoprime

/-- The **Chinese remainder theorem**. For a pair of coprime natural numbers, `m` and `n`,
  the rings `ZMod (m * n)` and `ZMod m × ZMod n` are isomorphic.

See `Ideal.quotientInfRingEquivPiQuotient` for the Chinese remainder theorem for ideals in any
ring.
-/
def chineseRemainder {m n : ℕ} (h : m.coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n :=
  let to_fun : ZMod (m * n) → ZMod m × ZMod n :=
    ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n)
                                          -- 🎉 no goals
  let inv_fun : ZMod m × ZMod n → ZMod (m * n) := fun x =>
    if m * n = 0 then if m = 1 then RingHom.snd _ _ x else RingHom.fst _ _ x
    else Nat.chineseRemainder h x.1.val x.2.val
  have inv : Function.LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun :=
    if hmn0 : m * n = 0 then by
      rcases h.eq_of_mul_eq_zero hmn0 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      -- ⊢ LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun
      · constructor
        -- ⊢ LeftInverse inv_fun to_fun
        · intro x; rfl
          -- ⊢ inv_fun (to_fun x) = x
                   -- 🎉 no goals
        · rintro ⟨x, y⟩
          -- ⊢ to_fun (inv_fun (x, y)) = (x, y)
          fin_cases y
          -- ⊢ to_fun (inv_fun (x, { val := 0, isLt := (_ : 0 < 0 + 1) })) = (x, { val := 0 …
          simp [castHom, Prod.ext_iff]
          -- 🎉 no goals
      · constructor
        -- ⊢ LeftInverse inv_fun to_fun
        · intro x; rfl
          -- ⊢ inv_fun (to_fun x) = x
                   -- 🎉 no goals
        · rintro ⟨x, y⟩
          -- ⊢ to_fun (inv_fun (x, y)) = (x, y)
          fin_cases x
          -- ⊢ to_fun (inv_fun ({ val := 0, isLt := (_ : 0 < 0 + 1) }, y)) = ({ val := 0, i …
          simp [castHom, Prod.ext_iff]
          -- 🎉 no goals
    else by
      haveI : NeZero (m * n) := ⟨hmn0⟩
      -- ⊢ LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun
      haveI : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
      -- ⊢ LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun
      haveI : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
      -- ⊢ LeftInverse inv_fun to_fun ∧ Function.RightInverse inv_fun to_fun
      have left_inv : Function.LeftInverse inv_fun to_fun := by
        intro x
        dsimp only [dvd_mul_left, dvd_mul_right, ZMod.castHom_apply]
        conv_rhs => rw [← ZMod.nat_cast_zmod_val x]
        rw [if_neg hmn0, ZMod.eq_iff_modEq_nat, ← Nat.modEq_and_modEq_iff_modEq_mul h,
          Prod.fst_zmod_cast, Prod.snd_zmod_cast]
        refine'
          ⟨(Nat.chineseRemainder h (x : ZMod m).val (x : ZMod n).val).2.left.trans _,
            (Nat.chineseRemainder h (x : ZMod m).val (x : ZMod n).val).2.right.trans _⟩
        · rw [← ZMod.eq_iff_modEq_nat, ZMod.nat_cast_zmod_val, ZMod.nat_cast_val]
        · rw [← ZMod.eq_iff_modEq_nat, ZMod.nat_cast_zmod_val, ZMod.nat_cast_val]
      exact ⟨left_inv, left_inv.rightInverse_of_card_le (by simp)⟩
      -- 🎉 no goals
  { toFun := to_fun,
    invFun := inv_fun,
    map_mul' := RingHom.map_mul _
    map_add' := RingHom.map_add _
    left_inv := inv.1
    right_inv := inv.2 }
#align zmod.chinese_remainder ZMod.chineseRemainder

-- todo: this can be made a `Unique` instance.
instance subsingleton_units : Subsingleton (ZMod 2)ˣ :=
  ⟨by decide⟩
      -- 🎉 no goals
#align zmod.subsingleton_units ZMod.subsingleton_units

@[simp]
theorem add_self_eq_zero_iff_eq_zero {n : ℕ} (hn : Odd n) {a : ZMod n} :
    a + a = 0 ↔ a = 0 := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, ← Nat.prime_two.coprime_iff_not_dvd] at hn
  -- ⊢ a + a = 0 ↔ a = 0
  rw [←mul_two, ←@Nat.cast_two (ZMod n), ←ZMod.coe_unitOfCoprime 2 hn, Units.mul_left_eq_zero]
  -- 🎉 no goals

theorem ne_neg_self {n : ℕ} (hn : Odd n) {a : ZMod n} (ha : a ≠ 0) : a ≠ -a := by
  rwa [Ne, eq_neg_iff_add_eq_zero, add_self_eq_zero_iff_eq_zero hn]
  -- 🎉 no goals
#align zmod.ne_neg_self ZMod.ne_neg_self

theorem neg_one_ne_one {n : ℕ} [Fact (2 < n)] : (-1 : ZMod n) ≠ 1 :=
  CharP.neg_one_ne_one (ZMod n) n
#align zmod.neg_one_ne_one ZMod.neg_one_ne_one

theorem neg_eq_self_mod_two (a : ZMod 2) : -a = a := by
  fin_cases a <;> apply Fin.ext <;> simp [Fin.coe_neg, Int.natMod]
  -- ⊢ -{ val := 0, isLt := (_ : 0 < 1 + 1) } = { val := 0, isLt := (_ : 0 < 1 + 1) }
                  -- ⊢ ↑(-{ val := 0, isLt := (_ : 0 < 1 + 1) }) = ↑{ val := 0, isLt := (_ : 0 < 1  …
                  -- ⊢ ↑(-{ val := 1, isLt := (_ : (fun a => a < 1 + 1) 1) }) = ↑{ val := 1, isLt : …
                                    -- 🎉 no goals
                                    -- 🎉 no goals
#align zmod.neg_eq_self_mod_two ZMod.neg_eq_self_mod_two

@[simp]
theorem natAbs_mod_two (a : ℤ) : (a.natAbs : ZMod 2) = a := by
  cases a
  -- ⊢ ↑(Int.natAbs (Int.ofNat a✝)) = ↑(Int.ofNat a✝)
  · simp only [Int.natAbs_ofNat, Int.cast_ofNat, Int.ofNat_eq_coe]
    -- 🎉 no goals
  · simp only [neg_eq_self_mod_two, Nat.cast_succ, Int.natAbs, Int.cast_negSucc]
    -- 🎉 no goals
#align zmod.nat_abs_mod_two ZMod.natAbs_mod_two

@[simp]
theorem val_eq_zero : ∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
  | 0, a => Int.natAbs_eq_zero
  | n + 1, a => by
    rw [Fin.ext_iff]
    -- ⊢ val a = 0 ↔ ↑a = ↑0
    exact Iff.rfl
    -- 🎉 no goals
#align zmod.val_eq_zero ZMod.val_eq_zero

theorem neg_eq_self_iff {n : ℕ} (a : ZMod n) : -a = a ↔ a = 0 ∨ 2 * a.val = n := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul]
  -- ⊢ 2 * a = 0 ↔ a = 0 ∨ 2 * val a = n
  cases n
  -- ⊢ 2 * a = 0 ↔ a = 0 ∨ 2 * val a = Nat.zero
  · erw [@mul_eq_zero ℤ, @mul_eq_zero ℕ, val_eq_zero]
    -- ⊢ 2 = 0 ∨ a = 0 ↔ a = 0 ∨ 2 = 0 ∨ a = 0
    exact
      ⟨fun h => h.elim (by simp) Or.inl, fun h =>
        Or.inr (h.elim id fun h => h.elim (by simp) id)⟩
  conv_lhs =>
    rw [← a.nat_cast_zmod_val, ← Nat.cast_two, ← Nat.cast_mul, nat_cast_zmod_eq_zero_iff_dvd]
  constructor
  -- ⊢ Nat.succ n✝ ∣ 2 * val a → a = 0 ∨ 2 * val a = Nat.succ n✝
  · rintro ⟨m, he⟩
    -- ⊢ a = 0 ∨ 2 * val a = Nat.succ n✝
    cases' m with m
    -- ⊢ a = 0 ∨ 2 * val a = Nat.succ n✝
    · erw [mul_zero, mul_eq_zero] at he
      -- ⊢ a = 0 ∨ 2 * val a = Nat.succ n✝
      rcases he with (⟨⟨⟩⟩ | he)
      -- ⊢ a = 0 ∨ 2 * val a = Nat.succ n✝
      exact Or.inl (a.val_eq_zero.1 he)
      -- 🎉 no goals
    cases m
    -- ⊢ a = 0 ∨ 2 * val a = Nat.succ n✝
    · right
      -- ⊢ 2 * val a = Nat.succ n✝
      rwa [show Nat.succ Nat.zero = 1 from rfl, mul_one] at he
      -- 🎉 no goals
    refine' (a.val_lt.not_le <| Nat.le_of_mul_le_mul_left _ zero_lt_two).elim
    -- ⊢ 2 * Nat.succ n✝¹ ≤ 2 * val a
    rw [he, mul_comm]
    -- ⊢ Nat.succ n✝¹ * 2 ≤ Nat.succ n✝¹ * Nat.succ (Nat.succ n✝)
    apply Nat.mul_le_mul_left
    -- ⊢ 2 ≤ Nat.succ (Nat.succ n✝)
    erw [Nat.succ_le_succ_iff, Nat.succ_le_succ_iff]; simp
    -- ⊢ 0 ≤ n✝
                                                      -- 🎉 no goals
  · rintro (rfl | h)
    -- ⊢ Nat.succ n✝ ∣ 2 * val 0
    · rw [val_zero, mul_zero]
      -- ⊢ Nat.succ n✝ ∣ 0
      apply dvd_zero
      -- 🎉 no goals
    · rw [h]
      -- 🎉 no goals
#align zmod.neg_eq_self_iff ZMod.neg_eq_self_iff

theorem val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rw [val_nat_cast, Nat.mod_eq_of_lt h]
  -- 🎉 no goals
#align zmod.val_cast_of_lt ZMod.val_cast_of_lt

theorem neg_val' {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = (n - a.val) % n :=
  calc
    (-a).val = val (-a) % n := by rw [Nat.mod_eq_of_lt (-a).val_lt]
                                  -- 🎉 no goals
    _ = (n - val a) % n :=
      Nat.ModEq.add_right_cancel' _
        (by
          rw [Nat.ModEq, ← val_add, add_left_neg, tsub_add_cancel_of_le a.val_le, Nat.mod_self,
            val_zero])
#align zmod.neg_val' ZMod.neg_val'

theorem neg_val {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = if a = 0 then 0 else n - a.val := by
  rw [neg_val']
  -- ⊢ (n - val a) % n = if a = 0 then 0 else n - val a
  by_cases h : a = 0; · rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_self]
  -- ⊢ (n - val a) % n = if a = 0 then 0 else n - val a
                        -- 🎉 no goals
  rw [if_neg h]
  -- ⊢ (n - val a) % n = n - val a
  apply Nat.mod_eq_of_lt
  -- ⊢ n - val a < n
  apply Nat.sub_lt (NeZero.pos n)
  -- ⊢ 0 < val a
  contrapose! h
  -- ⊢ a = 0
  rwa [le_zero_iff, val_eq_zero] at h
  -- 🎉 no goals
#align zmod.neg_val ZMod.neg_val

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
  -- ⊢ valMinAbs x = if val x ≤ Nat.zero / 2 then ↑(val x) else ↑(val x) - ↑Nat.zero
  · cases NeZero.ne 0 rfl
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align zmod.val_min_abs_def_pos ZMod.valMinAbs_def_pos

@[simp, norm_cast]
theorem coe_valMinAbs : ∀ {n : ℕ} (x : ZMod n), (x.valMinAbs : ZMod n) = x
  | 0, x => Int.cast_id
  | k@(n + 1), x => by
    rw [valMinAbs_def_pos]
    -- ⊢ ↑(if val x ≤ namedPattern k (n + 1) h✝ / 2 then ↑(val x) else ↑(val x) - ↑(n …
    split_ifs
    -- ⊢ ↑↑(val x) = x
    · rw [Int.cast_ofNat, nat_cast_zmod_val]
      -- 🎉 no goals
    · rw [Int.cast_sub, Int.cast_ofNat, nat_cast_zmod_val, Int.cast_ofNat, nat_cast_self, sub_zero]
      -- 🎉 no goals
#align zmod.coe_val_min_abs ZMod.coe_valMinAbs

theorem injective_valMinAbs {n : ℕ} : (valMinAbs : ZMod n → ℤ).Injective :=
  Function.injective_iff_hasLeftInverse.2 ⟨_, coe_valMinAbs⟩
#align zmod.injective_val_min_abs ZMod.injective_valMinAbs

theorem _root_.Nat.le_div_two_iff_mul_two_le {n m : ℕ} : m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n := by
  rw [Nat.le_div_iff_mul_le zero_lt_two, ← Int.ofNat_le, Int.ofNat_mul, Nat.cast_two]
  -- 🎉 no goals
#align nat.le_div_two_iff_mul_two_le Nat.le_div_two_iff_mul_two_le

theorem valMinAbs_nonneg_iff {n : ℕ} [NeZero n] (x : ZMod n) : 0 ≤ x.valMinAbs ↔ x.val ≤ n / 2 := by
  rw [valMinAbs_def_pos]; split_ifs with h
  -- ⊢ (0 ≤ if val x ≤ n / 2 then ↑(val x) else ↑(val x) - ↑n) ↔ val x ≤ n / 2
                          -- ⊢ 0 ≤ ↑(val x) ↔ val x ≤ n / 2
  · exact iff_of_true (Nat.cast_nonneg _) h
    -- 🎉 no goals
  · exact iff_of_false (sub_lt_zero.2 <| Int.ofNat_lt.2 x.val_lt).not_le h
    -- 🎉 no goals
#align zmod.val_min_abs_nonneg_iff ZMod.valMinAbs_nonneg_iff

theorem valMinAbs_mul_two_eq_iff {n : ℕ} (a : ZMod n) : a.valMinAbs * 2 = n ↔ 2 * a.val = n := by
  cases' n with n
  -- ⊢ valMinAbs a * 2 = ↑Nat.zero ↔ 2 * val a = Nat.zero
  · simp
    -- 🎉 no goals
  by_cases h : a.val ≤ n.succ / 2
  -- ⊢ valMinAbs a * 2 = ↑(Nat.succ n) ↔ 2 * val a = Nat.succ n
  · dsimp [valMinAbs]
    -- ⊢ (if val a ≤ Nat.succ n / 2 then ↑(val a) else ↑(val a) - ↑(Nat.succ n)) * 2  …
    rw [if_pos h, ← Int.coe_nat_inj', Nat.cast_mul, Nat.cast_two, mul_comm]
    -- 🎉 no goals
  apply iff_of_false _ (mt _ h)
  -- ⊢ ¬valMinAbs a * 2 = ↑(Nat.succ n)
  · intro he
    -- ⊢ False
    rw [← a.valMinAbs_nonneg_iff, ← mul_nonneg_iff_left_nonneg_of_pos, he] at h
    -- ⊢ False
    exacts [h (Nat.cast_nonneg _), zero_lt_two]
    -- 🎉 no goals
  · rw [mul_comm]
    -- ⊢ val a * 2 = Nat.succ n → val a ≤ Nat.succ n / 2
    exact fun h => (Nat.le_div_iff_mul_le zero_lt_two).2 h.le
    -- 🎉 no goals
#align zmod.val_min_abs_mul_two_eq_iff ZMod.valMinAbs_mul_two_eq_iff

theorem valMinAbs_mem_Ioc {n : ℕ} [NeZero n] (x : ZMod n) :
    x.valMinAbs * 2 ∈ Set.Ioc (-n : ℤ) n := by
  simp_rw [valMinAbs_def_pos, Nat.le_div_two_iff_mul_two_le]; split_ifs with h
  -- ⊢ (if ↑(val x) * 2 ≤ ↑n then ↑(val x) else ↑(val x) - ↑n) * 2 ∈ Set.Ioc (-↑n) ↑n
                                                              -- ⊢ ↑(val x) * 2 ∈ Set.Ioc (-↑n) ↑n
  · refine' ⟨(neg_lt_zero.2 <| by exact_mod_cast NeZero.pos n).trans_le (mul_nonneg _ _), h⟩
    -- ⊢ 0 ≤ ↑(val x)
    exacts [Nat.cast_nonneg _, zero_le_two]
    -- 🎉 no goals
  · refine' ⟨_, le_trans (mul_nonpos_of_nonpos_of_nonneg _ zero_le_two) <| Nat.cast_nonneg _⟩
    -- ⊢ -↑n < (↑(val x) - ↑n) * 2
    · linarith only [h]
      -- 🎉 no goals
    · rw [sub_nonpos, Int.ofNat_le]
      -- ⊢ val x ≤ n
      exact x.val_lt.le
      -- 🎉 no goals
#align zmod.val_min_abs_mem_Ioc ZMod.valMinAbs_mem_Ioc

theorem valMinAbs_spec {n : ℕ} [NeZero n] (x : ZMod n) (y : ℤ) :
    x.valMinAbs = y ↔ x = y ∧ y * 2 ∈ Set.Ioc (-n : ℤ) n :=
  ⟨by
    rintro rfl
    -- ⊢ x = ↑(valMinAbs x) ∧ valMinAbs x * 2 ∈ Set.Ioc (-↑n) ↑n
    exact ⟨x.coe_valMinAbs.symm, x.valMinAbs_mem_Ioc⟩, fun h =>
    -- 🎉 no goals
      by
        rw [← sub_eq_zero]
        -- ⊢ valMinAbs x - y = 0
        apply @Int.eq_zero_of_abs_lt_dvd n
        -- ⊢ ↑n ∣ valMinAbs x - y
        · rw [← int_cast_zmod_eq_zero_iff_dvd, Int.cast_sub, coe_valMinAbs, h.1, sub_self]
          -- 🎉 no goals
        rw [← mul_lt_mul_right (@zero_lt_two ℤ _ _ _ _ _)]
        -- ⊢ |valMinAbs x - y| * 2 < ↑n * 2
        nth_rw 1 [← abs_eq_self.2 (@zero_le_two ℤ _ _ _ _)]
        -- ⊢ |valMinAbs x - y| * |2| < ↑n * 2
        rw [← abs_mul, sub_mul, abs_lt]
        -- ⊢ -(↑n * 2) < valMinAbs x * 2 - y * 2 ∧ valMinAbs x * 2 - y * 2 < ↑n * 2
        constructor <;> linarith only [x.valMinAbs_mem_Ioc.1, x.valMinAbs_mem_Ioc.2, h.2.1, h.2.2]⟩
        -- ⊢ -(↑n * 2) < valMinAbs x * 2 - y * 2
                        -- 🎉 no goals
                        -- 🎉 no goals
#align zmod.val_min_abs_spec ZMod.valMinAbs_spec

theorem natAbs_valMinAbs_le {n : ℕ} [NeZero n] (x : ZMod n) : x.valMinAbs.natAbs ≤ n / 2 := by
  rw [Nat.le_div_two_iff_mul_two_le]
  -- ⊢ ↑(Int.natAbs (valMinAbs x)) * 2 ≤ ↑n
  cases' x.valMinAbs.natAbs_eq with h h
  -- ⊢ ↑(Int.natAbs (valMinAbs x)) * 2 ≤ ↑n
  · rw [← h]
    -- ⊢ valMinAbs x * 2 ≤ ↑n
    exact x.valMinAbs_mem_Ioc.2
    -- 🎉 no goals
  · rw [← neg_le_neg_iff, ← neg_mul, ← h]
    -- ⊢ -↑n ≤ valMinAbs x * 2
    exact x.valMinAbs_mem_Ioc.1.le
    -- 🎉 no goals
#align zmod.nat_abs_val_min_abs_le ZMod.natAbs_valMinAbs_le

@[simp]
theorem valMinAbs_zero : ∀ n, (0 : ZMod n).valMinAbs = 0
  | 0 => by simp only [valMinAbs_def_zero]
            -- 🎉 no goals
  | n + 1 => by simp only [valMinAbs_def_pos, if_true, Int.ofNat_zero, zero_le, val_zero]
                -- 🎉 no goals
#align zmod.val_min_abs_zero ZMod.valMinAbs_zero

@[simp]
theorem valMinAbs_eq_zero {n : ℕ} (x : ZMod n) : x.valMinAbs = 0 ↔ x = 0 := by
  cases' n with n
  -- ⊢ valMinAbs x = 0 ↔ x = 0
  · simp
    -- 🎉 no goals
  rw [← valMinAbs_zero n.succ]
  -- ⊢ valMinAbs x = valMinAbs 0 ↔ x = 0
  apply injective_valMinAbs.eq_iff
  -- 🎉 no goals
#align zmod.val_min_abs_eq_zero ZMod.valMinAbs_eq_zero

theorem nat_cast_natAbs_valMinAbs {n : ℕ} [NeZero n] (a : ZMod n) :
    (a.valMinAbs.natAbs : ZMod n) = if a.val ≤ (n : ℕ) / 2 then a else -a := by
  have : (a.val : ℤ) - n ≤ 0 := by
    erw [sub_nonpos, Int.ofNat_le]
    exact a.val_le
  rw [valMinAbs_def_pos]
  -- ⊢ ↑(Int.natAbs (if val a ≤ n / 2 then ↑(val a) else ↑(val a) - ↑n)) = if val a …
  split_ifs
  -- ⊢ ↑(Int.natAbs ↑(val a)) = a
  · rw [Int.natAbs_ofNat, nat_cast_zmod_val]
    -- 🎉 no goals
  · rw [← Int.cast_ofNat, Int.ofNat_natAbs_of_nonpos this, Int.cast_neg, Int.cast_sub,
      Int.cast_ofNat, Int.cast_ofNat, nat_cast_self, sub_zero, nat_cast_zmod_val]
#align zmod.nat_cast_nat_abs_val_min_abs ZMod.nat_cast_natAbs_valMinAbs

theorem valMinAbs_neg_of_ne_half {n : ℕ} {a : ZMod n} (ha : 2 * a.val ≠ n) :
    (-a).valMinAbs = -a.valMinAbs := by
  cases' eq_zero_or_neZero n with h h
  -- ⊢ valMinAbs (-a) = -valMinAbs a
  · subst h
    -- ⊢ valMinAbs (-a) = -valMinAbs a
    rfl
    -- 🎉 no goals
  refine' (valMinAbs_spec _ _).2 ⟨_, _, _⟩
  · rw [Int.cast_neg, coe_valMinAbs]
    -- 🎉 no goals
  · rw [neg_mul, neg_lt_neg_iff]
    -- ⊢ valMinAbs a * 2 < ↑n
    exact a.valMinAbs_mem_Ioc.2.lt_of_ne (mt a.valMinAbs_mul_two_eq_iff.1 ha)
    -- 🎉 no goals
  · linarith only [a.valMinAbs_mem_Ioc.1]
    -- 🎉 no goals
#align zmod.val_min_abs_neg_of_ne_half ZMod.valMinAbs_neg_of_ne_half

@[simp]
theorem natAbs_valMinAbs_neg {n : ℕ} (a : ZMod n) : (-a).valMinAbs.natAbs = a.valMinAbs.natAbs := by
  by_cases h2a : 2 * a.val = n
  -- ⊢ Int.natAbs (valMinAbs (-a)) = Int.natAbs (valMinAbs a)
  · rw [a.neg_eq_self_iff.2 (Or.inr h2a)]
    -- 🎉 no goals
  · rw [valMinAbs_neg_of_ne_half h2a, Int.natAbs_neg]
    -- 🎉 no goals
#align zmod.nat_abs_val_min_abs_neg ZMod.natAbs_valMinAbs_neg

theorem val_eq_ite_valMinAbs {n : ℕ} [NeZero n] (a : ZMod n) :
    (a.val : ℤ) = a.valMinAbs + if a.val ≤ n / 2 then 0 else n := by
  rw [valMinAbs_def_pos]
  -- ⊢ ↑(val a) = (if val a ≤ n / 2 then ↑(val a) else ↑(val a) - ↑n) + ↑(if val a  …
  split_ifs <;> simp [add_zero, sub_add_cancel]
  -- ⊢ ↑(val a) = ↑(val a) + ↑0
                -- 🎉 no goals
                -- 🎉 no goals
#align zmod.val_eq_ite_val_min_abs ZMod.val_eq_ite_valMinAbs

theorem prime_ne_zero (p q : ℕ) [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rwa [← Nat.cast_zero, Ne.def, eq_iff_modEq_nat, Nat.modEq_zero_iff_dvd, ←
    hp.1.coprime_iff_not_dvd, Nat.coprime_primes hp.1 hq.1]
#align zmod.prime_ne_zero ZMod.prime_ne_zero

variable {n a : ℕ}

theorem valMinAbs_natAbs_eq_min {n : ℕ} [hpos : NeZero n] (a : ZMod n) :
    a.valMinAbs.natAbs = min a.val (n - a.val) := by
  rw [valMinAbs_def_pos]
  -- ⊢ Int.natAbs (if val a ≤ n / 2 then ↑(val a) else ↑(val a) - ↑n) = min (val a) …
  split_ifs with h
  -- ⊢ Int.natAbs ↑(val a) = min (val a) (n - val a)
  · rw [Int.natAbs_ofNat]
    -- ⊢ val a = min (val a) (n - val a)
    symm
    -- ⊢ min (val a) (n - val a) = val a
    apply
      min_eq_left (le_trans h (le_trans (Nat.half_le_of_sub_le_half _) (Nat.sub_le_sub_left n h)))
    rw [Nat.sub_sub_self (Nat.div_le_self _ _)]
    -- 🎉 no goals
  · rw [← Int.natAbs_neg, neg_sub, ← Nat.cast_sub a.val_le]
    -- ⊢ Int.natAbs ↑(n - val a) = min (val a) (n - val a)
    symm
    -- ⊢ min (val a) (n - val a) = Int.natAbs ↑(n - val a)
    apply
      min_eq_right
        (le_trans (le_trans (Nat.sub_le_sub_left n (lt_of_not_ge h)) (Nat.le_half_of_half_lt_sub _))
          (le_of_not_ge h))
    rw [Nat.sub_sub_self (Nat.div_lt_self (lt_of_le_of_ne' (Nat.zero_le _) hpos.1) one_lt_two)]
    -- ⊢ n / 2 < Nat.succ (n / 2)
    apply Nat.lt_succ_self
    -- 🎉 no goals
#align zmod.val_min_abs_nat_abs_eq_min ZMod.valMinAbs_natAbs_eq_min

theorem valMinAbs_natCast_of_le_half (ha : a ≤ n / 2) : (a : ZMod n).valMinAbs = a := by
  cases n
  -- ⊢ valMinAbs ↑a = ↑a
  · simp
    -- 🎉 no goals
  · simp [valMinAbs_def_pos, val_nat_cast, Nat.mod_eq_of_lt (ha.trans_lt <| Nat.div_lt_self' _ 0),
      ha]
#align zmod.val_min_abs_nat_cast_of_le_half ZMod.valMinAbs_natCast_of_le_half

theorem valMinAbs_natCast_of_half_lt (ha : n / 2 < a) (ha' : a < n) :
    (a : ZMod n).valMinAbs = a - n := by
  cases n
  -- ⊢ valMinAbs ↑a = ↑a - ↑Nat.zero
  · cases not_lt_bot ha'
    -- 🎉 no goals
  · simp [valMinAbs_def_pos, val_nat_cast, Nat.mod_eq_of_lt ha', ha.not_le]
    -- 🎉 no goals
#align zmod.val_min_abs_nat_cast_of_half_lt ZMod.valMinAbs_natCast_of_half_lt

-- porting note: There was an extraneous `nat_` in the mathlib3 name
@[simp]
theorem valMinAbs_natCast_eq_self [NeZero n] : (a : ZMod n).valMinAbs = a ↔ a ≤ n / 2 := by
  refine' ⟨fun ha => _, valMinAbs_natCast_of_le_half⟩
  -- ⊢ a ≤ n / 2
  rw [← Int.natAbs_ofNat a, ← ha]
  -- ⊢ Int.natAbs (valMinAbs ↑a) ≤ n / 2
  exact natAbs_valMinAbs_le a
  -- 🎉 no goals
#align zmod.val_min_nat_abs_nat_cast_eq_self ZMod.valMinAbs_natCast_eq_self

theorem natAbs_min_of_le_div_two (n : ℕ) (x y : ℤ) (he : (x : ZMod n) = y) (hl : x.natAbs ≤ n / 2) :
    x.natAbs ≤ y.natAbs := by
  rw [int_cast_eq_int_cast_iff_dvd_sub] at he
  -- ⊢ Int.natAbs x ≤ Int.natAbs y
  obtain ⟨m, he⟩ := he
  -- ⊢ Int.natAbs x ≤ Int.natAbs y
  rw [sub_eq_iff_eq_add] at he
  -- ⊢ Int.natAbs x ≤ Int.natAbs y
  subst he
  -- ⊢ Int.natAbs x ≤ Int.natAbs (↑n * m + x)
  obtain rfl | hm := eq_or_ne m 0
  -- ⊢ Int.natAbs x ≤ Int.natAbs (↑n * 0 + x)
  · rw [mul_zero, zero_add]
    -- 🎉 no goals
  apply hl.trans
  -- ⊢ n / 2 ≤ Int.natAbs (↑n * m + x)
  rw [← add_le_add_iff_right x.natAbs]
  -- ⊢ n / 2 + Int.natAbs x ≤ Int.natAbs (↑n * m + x) + Int.natAbs x
  refine' le_trans (le_trans ((add_le_add_iff_left _).2 hl) _) (Int.natAbs_sub_le _ _)
  -- ⊢ n / 2 + n / 2 ≤ Int.natAbs (↑n * m + x - x)
  rw [add_sub_cancel, Int.natAbs_mul, Int.natAbs_ofNat]
  -- ⊢ n / 2 + n / 2 ≤ n * Int.natAbs m
  refine' le_trans _ (Nat.le_mul_of_pos_right <| Int.natAbs_pos.2 hm)
  -- ⊢ n / 2 + n / 2 ≤ n
  rw [← mul_two]; apply Nat.div_mul_le_self
  -- ⊢ n / 2 * 2 ≤ n
                  -- 🎉 no goals
#align zmod.nat_abs_min_of_le_div_two ZMod.natAbs_min_of_le_div_two

theorem natAbs_valMinAbs_add_le {n : ℕ} (a b : ZMod n) :
    (a + b).valMinAbs.natAbs ≤ (a.valMinAbs + b.valMinAbs).natAbs := by
  cases' n with n
  -- ⊢ Int.natAbs (valMinAbs (a + b)) ≤ Int.natAbs (valMinAbs a + valMinAbs b)
  · rfl
    -- 🎉 no goals
  apply natAbs_min_of_le_div_two n.succ
  -- ⊢ ↑(valMinAbs (a + b)) = ↑(valMinAbs a + valMinAbs b)
  · simp_rw [Int.cast_add, coe_valMinAbs]
    -- 🎉 no goals
  · apply natAbs_valMinAbs_le
    -- 🎉 no goals
#align zmod.nat_abs_val_min_abs_add_le ZMod.natAbs_valMinAbs_add_le

variable (p : ℕ) [Fact p.Prime]

private theorem mul_inv_cancel_aux (a : ZMod p) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  obtain ⟨k, rfl⟩ := nat_cast_zmod_surjective a
  -- ⊢ ↑k * (↑k)⁻¹ = 1
  apply coe_mul_inv_eq_one
  -- ⊢ Nat.coprime k p
  apply Nat.coprime.symm
  -- ⊢ Nat.coprime p k
  rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]
  -- 🎉 no goals

/-- Field structure on `ZMod p` if `p` is prime. -/
instance : Field (ZMod p) :=
  { inferInstanceAs (CommRing (ZMod p)), inferInstanceAs (Inv (ZMod p)),
    ZMod.nontrivial p with
    mul_inv_cancel := mul_inv_cancel_aux p
    inv_zero := inv_zero p }

/-- `ZMod p` is an integral domain when `p` is prime. -/
instance (p : ℕ) [hp : Fact p.Prime] : IsDomain (ZMod p) := by
  -- We need `cases p` here in order to resolve which `CommRing` instance is being used.
  cases p
  -- ⊢ IsDomain (ZMod Nat.zero)
  · exact (Nat.not_prime_zero hp.out).elim
    -- 🎉 no goals
  exact @Field.isDomain (ZMod _) (inferInstanceAs (Field (ZMod _)))
  -- 🎉 no goals

end ZMod

theorem RingHom.ext_zmod {n : ℕ} {R : Type*} [Semiring R] (f g : ZMod n →+* R) : f = g := by
  ext a
  -- ⊢ ↑f a = ↑g a
  obtain ⟨k, rfl⟩ := ZMod.int_cast_surjective a
  -- ⊢ ↑f ↑k = ↑g ↑k
  let φ : ℤ →+* R := f.comp (Int.castRingHom (ZMod n))
  -- ⊢ ↑f ↑k = ↑g ↑k
  let ψ : ℤ →+* R := g.comp (Int.castRingHom (ZMod n))
  -- ⊢ ↑f ↑k = ↑g ↑k
  show φ k = ψ k
  -- ⊢ ↑φ k = ↑ψ k
  rw [φ.ext_int ψ]
  -- 🎉 no goals
#align ring_hom.ext_zmod RingHom.ext_zmod

namespace ZMod

variable {n : ℕ} {R : Type*}

instance subsingleton_ringHom [Semiring R] : Subsingleton (ZMod n →+* R) :=
  ⟨RingHom.ext_zmod⟩
#align zmod.subsingleton_ring_hom ZMod.subsingleton_ringHom

instance subsingleton_ringEquiv [Semiring R] : Subsingleton (ZMod n ≃+* R) :=
  ⟨fun f g => by
    rw [RingEquiv.coe_ringHom_inj_iff]
    -- ⊢ ↑f = ↑g
    apply RingHom.ext_zmod _ _⟩
    -- 🎉 no goals
#align zmod.subsingleton_ring_equiv ZMod.subsingleton_ringEquiv

@[simp]
theorem ringHom_map_cast [Ring R] (f : R →+* ZMod n) (k : ZMod n) : f k = k := by
  cases n
  -- ⊢ ↑f ↑k = k
  · dsimp [ZMod, ZMod.cast] at f k ⊢; simp
    -- ⊢ ↑f ↑k = k
                                      -- 🎉 no goals
  · dsimp [ZMod, ZMod.cast] at f k ⊢
    -- ⊢ ↑f ↑(val k) = k
    erw [map_natCast, Fin.cast_val_eq_self]
    -- 🎉 no goals
#align zmod.ring_hom_map_cast ZMod.ringHom_map_cast

theorem ringHom_rightInverse [Ring R] (f : R →+* ZMod n) :
    Function.RightInverse ((↑) : ZMod n → R) f :=
  ringHom_map_cast f
#align zmod.ring_hom_right_inverse ZMod.ringHom_rightInverse

theorem ringHom_surjective [Ring R] (f : R →+* ZMod n) : Function.Surjective f :=
  (ringHom_rightInverse f).surjective
#align zmod.ring_hom_surjective ZMod.ringHom_surjective

theorem ringHom_eq_of_ker_eq [CommRing R] (f g : R →+* ZMod n)
    (h : RingHom.ker f = RingHom.ker g) : f = g := by
  have := f.liftOfRightInverse_comp _ (ZMod.ringHom_rightInverse f) ⟨g, le_of_eq h⟩
  -- ⊢ f = g
  rw [Subtype.coe_mk] at this
  -- ⊢ f = g
  rw [← this, RingHom.ext_zmod (f.liftOfRightInverse _ _ ⟨g, _⟩) _, RingHom.id_comp]
  -- 🎉 no goals
#align zmod.ring_hom_eq_of_ker_eq ZMod.ringHom_eq_of_ker_eq

section lift

variable (n) {A : Type*} [AddGroup A]

/-- The map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`. -/
--@[simps] --Porting note: removed, simplified LHS of `lift_coe` to something worse.
def lift : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A) :=
  (Equiv.subtypeEquivRight <| by
        intro f
        -- ⊢ ↑f ↑n = 0 ↔ AddMonoidHom.ker (Int.castAddHom (ZMod n)) ≤ AddMonoidHom.ker f
        rw [ker_int_castAddHom]
        -- ⊢ ↑f ↑n = 0 ↔ AddSubgroup.zmultiples ↑n ≤ AddMonoidHom.ker f
        constructor
        -- ⊢ ↑f ↑n = 0 → AddSubgroup.zmultiples ↑n ≤ AddMonoidHom.ker f
        · rintro hf _ ⟨x, rfl⟩
          -- ⊢ (fun x => x • ↑n) x ∈ AddMonoidHom.ker f
          simp only [f.map_zsmul, zsmul_zero, f.mem_ker, hf]
          -- 🎉 no goals
        · intro h
          -- ⊢ ↑f ↑n = 0
          refine' h (AddSubgroup.mem_zmultiples _)).trans <|
          -- 🎉 no goals
    (Int.castAddHom (ZMod n)).liftOfRightInverse (↑) int_cast_zmod_cast
#align zmod.lift ZMod.lift

variable (f : { f : ℤ →+ A // f n = 0 })

@[simp]
theorem lift_coe (x : ℤ) : lift n f (x : ZMod n) = f.val x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => int_cast_zmod_cast _) _ _
#align zmod.lift_coe ZMod.lift_coe

theorem lift_castAddHom (x : ℤ) : lift n f (Int.castAddHom (ZMod n) x) = f.1 x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => int_cast_zmod_cast _) _ _
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
