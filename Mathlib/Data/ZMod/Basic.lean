/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Fintype.Units
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `ZMod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivalence class

* A coercion `cast` is defined from `ZMod n` into any ring.
  This is a ring hom if the ring has characteristic dividing `n`

-/

assert_not_exists Field Submodule TwoSidedIdeal

open Function ZMod

namespace ZMod

instance : IsDomain (ZMod 0) := inferInstanceAs (IsDomain ℤ)

/-- For non-zero `n : ℕ`, the ring `Fin n` is equivalent to `ZMod n`. -/
def finEquiv : ∀ (n : ℕ) [NeZero n], Fin n ≃+* ZMod n
  | 0, h => (h.ne _ rfl).elim
  | _ + 1, _ => .refl _

instance charZero : CharZero (ZMod 0) := inferInstanceAs (CharZero ℤ)

/-- `val a` is a natural number defined as:
  - for `a : ZMod 0` it is the absolute value of `a`
  - for `a : ZMod n` with `0 < n` it is the least natural number in the equivalence class

See `ZMod.valMinAbs` for a variant that takes values in the integers.
-/
def val : ∀ {n : ℕ}, ZMod n → ℕ
  | 0 => Int.natAbs
  | n + 1 => ((↑) : Fin (n + 1) → ℕ)

theorem val_lt {n : ℕ} [NeZero n] (a : ZMod n) : a.val < n := by
  cases n
  · cases NeZero.ne 0 rfl
  exact Fin.is_lt a

theorem val_le {n : ℕ} [NeZero n] (a : ZMod n) : a.val ≤ n :=
  a.val_lt.le

@[simp]
theorem val_zero : ∀ {n}, (0 : ZMod n).val = 0
  | 0 => rfl
  | _ + 1 => rfl

@[simp]
theorem val_one' : (1 : ZMod 0).val = 1 :=
  rfl

@[simp]
theorem val_neg' {n : ZMod 0} : (-n).val = n.val :=
  Int.natAbs_neg n

@[simp]
theorem val_mul' {m n : ZMod 0} : (m * n).val = m.val * n.val :=
  Int.natAbs_mul m n

@[simp]
theorem val_natCast (n a : ℕ) : (a : ZMod n).val = a % n := by
  cases n
  · rw [Nat.mod_zero]
    exact Int.natAbs_natCast a
  · apply Fin.val_natCast

lemma val_natCast_of_lt {n a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rwa [val_natCast, Nat.mod_eq_of_lt]

lemma val_ofNat (n a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ZMod n).val = ofNat(a) % n := val_natCast ..

lemma val_ofNat_of_lt {n a : ℕ} [a.AtLeastTwo] (han : a < n) : (ofNat(a) : ZMod n).val = ofNat(a) :=
  val_natCast_of_lt han

theorem val_unit' {n : ZMod 0} : IsUnit n ↔ n.val = 1 := by
  simp only [val]
  rw [Int.isUnit_iff, Int.natAbs_eq_iff, Nat.cast_one]

lemma eq_one_of_isUnit_natCast {n : ℕ} (h : IsUnit (n : ZMod 0)) : n = 1 := by
  rw [← Nat.mod_zero n, ← val_natCast, val_unit'.mp h]

instance charP (n : ℕ) : CharP (ZMod n) n where
  cast_eq_zero_iff := by
    intro k
    rcases n with - | n
    · simp [zero_dvd_iff]
    · exact Fin.natCast_eq_zero

-- Verify that `grind` can see that `ZMod n` has characteristic `n`.
example (n : ℕ) : Lean.Grind.IsCharP (ZMod n) n := inferInstance

@[simp]
theorem addOrderOf_one (n : ℕ) : addOrderOf (1 : ZMod n) = n :=
  CharP.eq _ (CharP.addOrderOf_one _) (ZMod.charP n)

/-- This lemma works in the case in which `ZMod n` is not infinite, i.e. `n ≠ 0`.  The version
where `a ≠ 0` is `addOrderOf_coe'`. -/
@[simp]
theorem addOrderOf_coe (a : ℕ) {n : ℕ} (n0 : n ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rcases a with - | a
  · simp only [Nat.cast_zero, addOrderOf_zero, Nat.gcd_zero_right,
      Nat.pos_of_ne_zero n0, Nat.div_self]
  rw [← Nat.smul_one_eq_cast, addOrderOf_nsmul' _ a.succ_ne_zero, ZMod.addOrderOf_one]

/-- This lemma works in the case in which `a ≠ 0`.  The version where
`ZMod n` is not infinite, i.e. `n ≠ 0`, is `addOrderOf_coe`. -/
@[simp]
theorem addOrderOf_coe' {a : ℕ} (n : ℕ) (a0 : a ≠ 0) : addOrderOf (a : ZMod n) = n / n.gcd a := by
  rw [← Nat.smul_one_eq_cast, addOrderOf_nsmul' _ a0, ZMod.addOrderOf_one]

/-- We have that `ringChar (ZMod n) = n`. -/
theorem ringChar_zmod_n (n : ℕ) : ringChar (ZMod n) = n := by
  rw [ringChar.eq_iff]
  exact ZMod.charP n

theorem natCast_self (n : ℕ) : (n : ZMod n) = 0 :=
  CharP.cast_eq_zero (ZMod n) n

@[simp]
theorem natCast_self' (n : ℕ) : (n + 1 : ZMod (n + 1)) = 0 := by
  rw [← Nat.cast_add_one, natCast_self (n + 1)]

lemma natCast_pow_eq_zero_of_le (p : ℕ) {m n : ℕ} (h : n ≤ m) :
    (p ^ m : ZMod (p ^ n)) = 0 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, ← Nat.cast_pow]
  simp

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


@[simp]
theorem cast_zero : (cast (0 : ZMod n) : R) = 0 := by
  delta ZMod.cast
  cases n
  · exact Int.cast_zero
  · simp

theorem cast_eq_val [NeZero n] (a : ZMod n) : (cast a : R) = a.val := by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

variable {S : Type*} [AddGroupWithOne S]

@[simp]
theorem _root_.Prod.fst_zmod_cast (a : ZMod n) : (cast a : R × S).fst = cast a := by
  cases n
  · rfl
  · simp [ZMod.cast]

@[simp]
theorem _root_.Prod.snd_zmod_cast (a : ZMod n) : (cast a : R × S).snd = cast a := by
  cases n
  · rfl
  · simp [ZMod.cast]

end

/-- So-named because the coercion is `Nat.cast` into `ZMod`. For `Nat.cast` into an arbitrary ring,
see `ZMod.natCast_val`. -/
theorem natCast_zmod_val {n : ℕ} [NeZero n] (a : ZMod n) : (a.val : ZMod n) = a := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.cast_val_eq_self

theorem natCast_rightInverse [NeZero n] : Function.RightInverse val ((↑) : ℕ → ZMod n) :=
  natCast_zmod_val

theorem natCast_zmod_surjective [NeZero n] : Function.Surjective ((↑) : ℕ → ZMod n) :=
  natCast_rightInverse.surjective

/-- So-named because the outer coercion is `Int.cast` into `ZMod`. For `Int.cast` into an arbitrary
ring, see `ZMod.intCast_cast`. -/
@[norm_cast]
theorem intCast_zmod_cast (a : ZMod n) : ((cast a : ℤ) : ZMod n) = a := by
  cases n
  · simp [ZMod.cast, ZMod]
  · dsimp [ZMod.cast]
    rw [Int.cast_natCast, natCast_zmod_val]

theorem intCast_rightInverse : Function.RightInverse (cast : ZMod n → ℤ) ((↑) : ℤ → ZMod n) :=
  intCast_zmod_cast

theorem intCast_surjective : Function.Surjective ((↑) : ℤ → ZMod n) :=
  intCast_rightInverse.surjective

lemma «forall» {P : ZMod n → Prop} : (∀ x, P x) ↔ ∀ x : ℤ, P x := intCast_surjective.forall
lemma «exists» {P : ZMod n → Prop} : (∃ x, P x) ↔ ∃ x : ℤ, P x := intCast_surjective.exists

theorem cast_id : ∀ (n) (i : ZMod n), (ZMod.cast i : ZMod n) = i
  | 0, _ => Int.cast_id
  | _ + 1, i => natCast_zmod_val i

@[simp]
theorem cast_id' : (ZMod.cast : ZMod n → ZMod n) = id :=
  funext (cast_id n)

variable (R) [Ring R]

/-- The coercions are respectively `Nat.cast` and `ZMod.cast`. -/
@[simp]
theorem natCast_comp_val [NeZero n] : ((↑) : ℕ → R) ∘ (val : ZMod n → ℕ) = cast := by
  cases n
  · cases NeZero.ne 0 rfl
  rfl

/-- The coercions are respectively `Int.cast`, `ZMod.cast`, and `ZMod.cast`. -/
@[simp]
theorem intCast_comp_cast : ((↑) : ℤ → R) ∘ (cast : ZMod n → ℤ) = cast := by
  cases n
  · exact congr_arg (Int.cast ∘ ·) ZMod.cast_id'
  · ext
    simp [ZMod, ZMod.cast]

variable {R}

@[simp]
theorem natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = cast i :=
  congr_fun (natCast_comp_val R) i

@[simp]
theorem intCast_cast (i : ZMod n) : ((cast i : ℤ) : R) = cast i :=
  congr_fun (intCast_comp_cast R) i

theorem cast_add_eq_ite {n : ℕ} (a b : ZMod n) :
    (cast (a + b) : ℤ) =
      if (n : ℤ) ≤ cast a + cast b then (cast a + cast b - n : ℤ) else cast a + cast b := by
  rcases n with - | n
  · simp; rfl
  change Fin (n + 1) at a b
  change ((((a + b) : Fin (n + 1)) : ℕ) : ℤ) = if ((n + 1 : ℕ) : ℤ) ≤ (a : ℕ) + b then _ else _
  simp only [Fin.val_add_eq_ite, Int.natCast_succ]
  norm_cast
  split_ifs with h
  · rw [Nat.cast_sub h]
    congr
  · rfl

section CharDvd

/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/


variable {m : ℕ} [CharP R m]

@[simp]
theorem cast_one (h : m ∣ n) : (cast (1 : ZMod n) : R) = 1 := by
  rcases n with - | n
  · exact Int.cast_one
  change ((1 % (n + 1) : ℕ) : R) = 1
  cases n
  · rw [Nat.dvd_one] at h
    subst m
    subsingleton [CharP.CharOne.subsingleton]
  rw [Nat.mod_eq_of_lt]
  · exact Nat.cast_one
  exact Nat.lt_of_sub_eq_succ rfl

@[simp]
theorem cast_add (h : m ∣ n) (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b := by
  cases n
  · apply Int.cast_add
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_add, Fin.val_add, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

@[simp]
theorem cast_mul (h : m ∣ n) (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b := by
  cases n
  · apply Int.cast_mul
  symm
  dsimp [ZMod, ZMod.cast, ZMod.val]
  rw [← Nat.cast_mul, Fin.val_mul, ← sub_eq_zero, ← Nat.cast_sub (Nat.mod_le _ _),
    @CharP.cast_eq_zero_iff R _ m]
  exact h.trans (Nat.dvd_sub_mod _)

/-- The canonical ring homomorphism from `ZMod n` to a ring of characteristic dividing `n`.

See also `ZMod.lift` for a generalized version working in `AddGroup`s.
-/
def castHom (h : m ∣ n) (R : Type*) [Ring R] [CharP R m] : ZMod n →+* R where
  toFun := cast
  map_zero' := cast_zero
  map_one' := cast_one h
  map_add' := cast_add h
  map_mul' := cast_mul h

@[simp]
theorem castHom_apply {h : m ∣ n} (i : ZMod n) : castHom h R i = cast i :=
  rfl

@[simp]
theorem cast_sub (h : m ∣ n) (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b :=
  (castHom h R).map_sub a b

@[simp]
theorem cast_neg (h : m ∣ n) (a : ZMod n) : (cast (-a : ZMod n) : R) = -(cast a) :=
  (castHom h R).map_neg a

@[simp]
theorem cast_pow (h : m ∣ n) (a : ZMod n) (k : ℕ) : (cast (a ^ k : ZMod n) : R) = (cast a) ^ k :=
  (castHom h R).map_pow a k

@[simp, norm_cast]
theorem cast_natCast (h : m ∣ n) (k : ℕ) : (cast (k : ZMod n) : R) = k :=
  map_natCast (castHom h R) k

@[simp, norm_cast]
theorem cast_intCast (h : m ∣ n) (k : ℤ) : (cast (k : ZMod n) : R) = k :=
  map_intCast (castHom h R) k

theorem castHom_surjective (h : m ∣ n) : Function.Surjective (castHom h (ZMod m)) :=
  fun a ↦ by obtain ⟨a, rfl⟩ := intCast_surjective a; exact ⟨a, map_intCast ..⟩

end CharDvd

section CharEq

/-! Some specialised simp lemmas which apply when `R` has characteristic `n`. -/


variable [CharP R n]

theorem cast_one' : (cast (1 : ZMod n) : R) = 1 := by simp

theorem cast_add' (a b : ZMod n) : (cast (a + b : ZMod n) : R) = cast a + cast b := by simp

theorem cast_mul' (a b : ZMod n) : (cast (a * b : ZMod n) : R) = cast a * cast b := by simp

theorem cast_sub' (a b : ZMod n) : (cast (a - b : ZMod n) : R) = cast a - cast b := by simp

theorem cast_pow' (a : ZMod n) (k : ℕ) : (cast (a ^ k : ZMod n) : R) = (cast a : R) ^ k := by simp

@[norm_cast]
theorem cast_natCast' (k : ℕ) : (cast (k : ZMod n) : R) = k := by simp

@[norm_cast]
theorem cast_intCast' (k : ℤ) : (cast (k : ZMod n) : R) = k := by simp

variable (R)

theorem castHom_injective : Function.Injective (ZMod.castHom (dvd_refl n) R) := by
  rw [injective_iff_map_eq_zero]
  intro x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, CharP.intCast_eq_zero_iff R n, CharP.intCast_eq_zero_iff (ZMod n) n]
  exact id

theorem castHom_bijective [Fintype R] (h : Fintype.card R = n) :
    Function.Bijective (ZMod.castHom (dvd_refl n) R) := by
  haveI : NeZero n :=
    ⟨by
      intro hn
      rw [hn] at h
      exact (Fintype.card_eq_zero_iff.mp h).elim' 0⟩
  rw [Fintype.bijective_iff_injective_and_card, ZMod.card, h, eq_self_iff_true, and_true]
  apply ZMod.castHom_injective

/-- The unique ring isomorphism between `ZMod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
noncomputable def ringEquiv [Fintype R] (h : Fintype.card R = n) : ZMod n ≃+* R :=
  RingEquiv.ofBijective _ (ZMod.castHom_bijective R h)

/-- The unique ring isomorphism between `ZMod p` and a ring `R` of cardinality a prime `p`.

If you need any property of this isomorphism, first of all use `ringEquivOfPrime_eq_ringEquiv`
below (after `have : CharP R p := ...`) and deduce it by the results about `ZMod.ringEquiv`. -/
noncomputable def ringEquivOfPrime [Fintype R] {p : ℕ} (hp : p.Prime) (hR : Fintype.card R = p) :
    ZMod p ≃+* R :=
  have : Nontrivial R := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.one_lt)
  -- The following line exists as `charP_of_card_eq_prime` in
  -- `Mathlib/Algebra/CharP/CharAndCard.lean`.
  have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 (hR ▸ Nat.cast_card_eq_zero R)
  ZMod.ringEquiv R hR

@[simp]
lemma ringEquivOfPrime_eq_ringEquiv [Fintype R] {p : ℕ} [CharP R p] (hp : p.Prime)
    (hR : Fintype.card R = p) : ringEquivOfPrime R hp hR = ringEquiv R hR := rfl

/-- The identity between `ZMod m` and `ZMod n` when `m = n`, as a ring isomorphism. -/
def ringEquivCongr {m n : ℕ} (h : m = n) : ZMod m ≃+* ZMod n := by
  rcases m with - | m <;> rcases n with - | n
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
          rw [Fin.coe_cast, Fin.val_mul, Fin.val_mul, Fin.coe_cast, Fin.coe_cast, ← h]
        map_add' := fun a b => by
          dsimp [ZMod]
          ext
          rw [Fin.coe_cast, Fin.val_add, Fin.val_add, Fin.coe_cast, Fin.coe_cast, ← h] }

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
    ZMod.ringEquivCongr h z = z := map_intCast (ringEquivCongr h) z

end CharEq

end UniversalProperty

variable {m n : ℕ}

@[simp]
theorem val_eq_zero : ∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
  | 0, _ => Int.natAbs_eq_zero
  | n + 1, a => by
    rw [Fin.ext_iff]
    exact Iff.rfl

theorem intCast_eq_intCast_iff (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c] :=
  CharP.intCast_eq_intCast (ZMod c) c

theorem intCast_eq_intCast_iff' (a b : ℤ) (c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.intCast_eq_intCast_iff a b c

theorem val_intCast {n : ℕ} (a : ℤ) [NeZero n] : ↑(a : ZMod n).val = a % n := by
  have hle : (0 : ℤ) ≤ ↑(a : ZMod n).val := Int.natCast_nonneg _
  have hlt : ↑(a : ZMod n).val < (n : ℤ) := Int.ofNat_lt.mpr (ZMod.val_lt a)
  refine (Int.emod_eq_of_lt hle hlt).symm.trans ?_
  rw [← ZMod.intCast_eq_intCast_iff', Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]

theorem natCast_eq_natCast_iff (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c] := by
  simpa [Int.natCast_modEq_iff] using ZMod.intCast_eq_intCast_iff a b c

theorem natCast_eq_natCast_iff' (a b c : ℕ) : (a : ZMod c) = (b : ZMod c) ↔ a % c = b % c :=
  ZMod.natCast_eq_natCast_iff a b c

theorem intCast_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : ZMod b) = 0 ↔ (b : ℤ) ∣ a := by
  rw [← Int.cast_zero, ZMod.intCast_eq_intCast_iff, Int.modEq_zero_iff_dvd]

theorem intCast_eq_intCast_iff_dvd_sub (a b : ℤ) (c : ℕ) : (a : ZMod c) = ↑b ↔ ↑c ∣ b - a := by
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]

theorem natCast_eq_zero_iff (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a := by
  rw [← Nat.cast_zero, ZMod.natCast_eq_natCast_iff, Nat.modEq_zero_iff_dvd]

@[deprecated (since := "2025-06-30")] alias natCast_zmod_eq_zero_iff_dvd := natCast_eq_zero_iff

theorem coe_intCast (a : ℤ) : cast (a : ZMod n) = a % n := by
  cases n
  · rw [Int.ofNat_zero, Int.emod_zero, Int.cast_id]; rfl
  · rw [← val_intCast, val]; rfl

lemma intCast_cast_add (x y : ZMod n) : (cast (x + y) : ℤ) = (cast x + cast y) % n := by
  rw [← ZMod.coe_intCast, Int.cast_add, ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast]

lemma intCast_cast_mul (x y : ZMod n) : (cast (x * y) : ℤ) = cast x * cast y % n := by
  rw [← ZMod.coe_intCast, Int.cast_mul, ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast]

lemma intCast_cast_sub (x y : ZMod n) : (cast (x - y) : ℤ) = (cast x - cast y) % n := by
  rw [← ZMod.coe_intCast, Int.cast_sub, ZMod.intCast_zmod_cast, ZMod.intCast_zmod_cast]

lemma intCast_cast_neg (x : ZMod n) : (cast (-x) : ℤ) = -cast x % n := by
  rw [← ZMod.coe_intCast, Int.cast_neg, ZMod.intCast_zmod_cast]

@[simp]
theorem val_neg_one (n : ℕ) : (-1 : ZMod n.succ).val = n := by
  dsimp [val, Fin.coe_neg]
  cases n
  · simp
  · dsimp [ZMod, ZMod.cast]
    rw [Fin.coe_neg_one]

/-- `-1 : ZMod n` lifts to `n - 1 : R`. This avoids the characteristic assumption in `cast_neg`. -/
theorem cast_neg_one {R : Type*} [Ring R] (n : ℕ) : cast (-1 : ZMod n) = (n - 1 : R) := by
  rcases n with - | n
  · dsimp [ZMod, ZMod.cast]; simp
  · rw [← natCast_val, val_neg_one, Nat.cast_succ, add_sub_cancel_right]

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

theorem natCast_eq_iff (p : ℕ) (n : ℕ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_natCast, Nat.mod_add_div]
  · rintro ⟨k, rfl⟩
    rw [Nat.cast_add, natCast_zmod_val, Nat.cast_mul, natCast_self, zero_mul,
      add_zero]

theorem intCast_eq_iff (p : ℕ) (n : ℤ) (z : ZMod p) [NeZero p] :
    ↑n = z ↔ ∃ k, n = z.val + p * k := by
  constructor
  · rintro rfl
    refine ⟨n / p, ?_⟩
    rw [val_intCast, Int.emod_add_mul_ediv]
  · rintro ⟨k, rfl⟩
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, natCast_val,
      ZMod.natCast_self, zero_mul, add_zero, cast_id]

@[push_cast, simp]
theorem intCast_mod (a : ℤ) (b : ℕ) : ((a % b : ℤ) : ZMod b) = (a : ZMod b) := by
  rw [ZMod.intCast_eq_intCast_iff]
  apply Int.mod_modEq

theorem ker_intCastAddHom (n : ℕ) :
    (Int.castAddHom (ZMod n)).ker = AddSubgroup.zmultiples (n : ℤ) := by
  ext
  rw [Int.mem_zmultiples_iff, AddMonoidHom.mem_ker, Int.coe_castAddHom,
    intCast_zmod_eq_zero_iff_dvd]

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

@[simp]
theorem natCast_toNat (p : ℕ) : ∀ {z : ℤ} (_h : 0 ≤ z), (z.toNat : ZMod p) = z
  | (n : ℕ), _h => by simp only [Int.cast_natCast, Int.toNat_natCast]
  | Int.negSucc n, h => by simp at h

theorem val_injective (n : ℕ) [NeZero n] : Function.Injective (val : ZMod n → ℕ) := by
  cases n
  · cases NeZero.ne 0 rfl
  intro a b h
  dsimp [ZMod]
  ext
  exact h

theorem val_one_eq_one_mod (n : ℕ) : (1 : ZMod n).val = 1 % n := by
  rw [← Nat.cast_one, val_natCast]

theorem val_two_eq_two_mod (n : ℕ) : (2 : ZMod n).val = 2 % n := by
  rw [← Nat.cast_two, val_natCast]

theorem val_one (n : ℕ) [Fact (1 < n)] : (1 : ZMod n).val = 1 := by
  rw [val_one_eq_one_mod]
  exact Nat.mod_eq_of_lt Fact.out

lemma val_one'' : ∀ {n}, n ≠ 1 → (1 : ZMod n).val = 1
  | 0, _ => rfl
  | 1, hn => by cases hn rfl
  | n + 2, _ =>
    haveI : Fact (1 < n + 2) := ⟨by simp⟩
    ZMod.val_one _

theorem val_add {n : ℕ} [NeZero n] (a b : ZMod n) : (a + b).val = (a.val + b.val) % n := by
  cases n
  · cases NeZero.ne 0 rfl
  · apply Fin.val_add

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
  · simpa [ZMod.val] using Int.natAbs_add_le _ _
  · simpa [ZMod.val_add] using Nat.mod_le _ _

theorem val_mul {n : ℕ} (a b : ZMod n) : (a * b).val = a.val * b.val % n := by
  cases n
  · rw [Nat.mod_zero]
    apply Int.natAbs_mul
  · apply Fin.val_mul

theorem val_mul_le {n : ℕ} (a b : ZMod n) : (a * b).val ≤ a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_le

theorem val_mul_of_lt {n : ℕ} {a b : ZMod n} (h : a.val * b.val < n) :
    (a * b).val = a.val * b.val := by
  rw [val_mul]
  apply Nat.mod_eq_of_lt h

theorem val_mul_iff_lt {n : ℕ} [NeZero n] (a b : ZMod n) :
    (a * b).val = a.val * b.val ↔ a.val * b.val < n := by
  constructor <;> intro h
  · rw [← h]; apply ZMod.val_lt
  · apply ZMod.val_mul_of_lt h

instance nontrivial (n : ℕ) [Fact (1 < n)] : Nontrivial (ZMod n) :=
  ⟨⟨0, 1, fun h =>
      zero_ne_one <|
        calc
          0 = (0 : ZMod n).val := by rw [val_zero]
          _ = (1 : ZMod n).val := congr_arg ZMod.val h
          _ = 1 := val_one n
          ⟩⟩

instance nontrivial' : Nontrivial (ZMod 0) := by
  delta ZMod; infer_instance

lemma one_eq_zero_iff {n : ℕ} : (1 : ZMod n) = 0 ↔ n = 1 := by
  rw [← Nat.cast_one, natCast_eq_zero_iff, Nat.dvd_one]

/-- The inversion on `ZMod n`.
It is setup in such a way that `a * a⁻¹` is equal to `gcd a.val n`.
In particular, if `a` is coprime to `n`, and hence a unit, `a * a⁻¹ = 1`. -/
def inv : ∀ n : ℕ, ZMod n → ZMod n
  | 0, i => Int.sign i
  | n + 1, i => Nat.gcdA i.val (n + 1)

instance (n : ℕ) : Inv (ZMod n) :=
  ⟨inv n⟩

theorem inv_zero : ∀ n : ℕ, (0 : ZMod n)⁻¹ = 0
  | 0 => Int.sign_zero
  | n + 1 =>
    show (Nat.gcdA _ (n + 1) : ZMod (n + 1)) = 0 by
      rw [val_zero]
      unfold Nat.gcdA Nat.xgcd Nat.xgcdAux
      rfl

theorem mul_inv_eq_gcd {n : ℕ} (a : ZMod n) : a * a⁻¹ = Nat.gcd a.val n := by
  rcases n with - | n
  · dsimp [ZMod] at a ⊢
    calc
      _ = a * Int.sign a := rfl
      _ = a.natAbs := by rw [Int.mul_sign_self]
      _ = a.natAbs.gcd 0 := by rw [Nat.gcd_zero_right]
  · calc
      a * a⁻¹ = a * a⁻¹ + n.succ * Nat.gcdB (val a) n.succ := by
        rw [natCast_self, zero_mul, add_zero]
      _ = ↑(↑a.val * Nat.gcdA (val a) n.succ + n.succ * Nat.gcdB (val a) n.succ) := by
        push_cast
        rw [natCast_zmod_val]
        rfl
      _ = Nat.gcd a.val n.succ := by rw [← Nat.gcd_eq_gcd_ab a.val n.succ]; rfl

@[simp] protected lemma inv_one (n : ℕ) : (1⁻¹ : ZMod n) = 1 := by
  obtain rfl | hn := eq_or_ne n 1
  · exact Subsingleton.elim _ _
  · simpa [ZMod.val_one'' hn] using mul_inv_eq_gcd (1 : ZMod n)

@[simp]
theorem natCast_mod (a : ℕ) (n : ℕ) : ((a % n : ℕ) : ZMod n) = a :=
  (CharP.cast_eq_mod (ZMod n) n a).symm

@[deprecated natCast_eq_natCast_iff (since := "2025-08-12")]
theorem eq_iff_modEq_nat (n : ℕ) {a b : ℕ} : (a : ZMod n) = b ↔ a ≡ b [MOD n] :=
  natCast_eq_natCast_iff a b n

theorem intCast_eq_zero_iff_even {n : ℤ} : (n : ZMod 2) = 0 ↔ Even n :=
  (CharP.intCast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm

alias ⟨_, _root_.Even.intCast_zmod_two⟩ := intCast_eq_zero_iff_even

theorem natCast_eq_zero_iff_even {n : ℕ} : (n : ZMod 2) = 0 ↔ Even n :=
  mod_cast intCast_eq_zero_iff_even (n := n)

@[deprecated (since := "2025-08-25")]
alias eq_zero_iff_even := natCast_eq_zero_iff_even

alias ⟨_, _root_.Even.natCast_zmod_two⟩ := natCast_eq_zero_iff_even

theorem intCast_eq_one_iff_odd {n : ℤ} : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff, Int.odd_iff, Int.ModEq]
  simp

alias ⟨_, _root_.Odd.intCast_zmod_two⟩ := intCast_eq_one_iff_odd

theorem natCast_eq_one_iff_odd {n : ℕ} : (n : ZMod 2) = 1 ↔ Odd n :=
  mod_cast intCast_eq_one_iff_odd (n := n)

@[deprecated (since := "2025-08-25")]
alias eq_one_iff_odd := natCast_eq_one_iff_odd

alias ⟨_, _root_.Odd.natCast_zmod_two⟩ := natCast_eq_one_iff_odd

theorem natCast_ne_zero_iff_odd {n : ℕ} : (n : ZMod 2) ≠ 0 ↔ Odd n := by
  simp [natCast_eq_zero_iff_even]

@[deprecated (since := "2025-08-25")]
alias ne_zero_iff_odd := natCast_ne_zero_iff_odd

theorem coe_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) :
    ((x : ZMod n) * (x : ZMod n)⁻¹) = 1 := by
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec] at h
  rw [mul_inv_eq_gcd, val_natCast, h, Nat.cast_one]

lemma mul_val_inv (hmn : m.Coprime n) : (m * (m⁻¹ : ZMod n).val : ZMod n) = 1 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [m.coprime_zero_right.1 hmn]
  haveI : NeZero n := ⟨hn⟩
  rw [ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one _ hmn]

lemma val_inv_mul (hmn : m.Coprime n) : ((m⁻¹ : ZMod n).val * m : ZMod n) = 1 := by
  rw [mul_comm, mul_val_inv hmn]

/-- `unitOfCoprime` makes an element of `(ZMod n)ˣ` given
a natural number `x` and a proof that `x` is coprime to `n` -/
def unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) : (ZMod n)ˣ :=
  ⟨x, x⁻¹, coe_mul_inv_eq_one x h, by rw [mul_comm, coe_mul_inv_eq_one x h]⟩

@[simp]
theorem coe_unitOfCoprime {n : ℕ} (x : ℕ) (h : Nat.Coprime x n) :
    (unitOfCoprime x h : ZMod n) = x :=
  rfl

theorem val_coe_unit_coprime {n : ℕ} (u : (ZMod n)ˣ) : Nat.Coprime (u : ZMod n).val n := by
  rcases n with - | n
  · rcases Int.units_eq_one_or u with (rfl | rfl) <;> simp
  apply Nat.coprime_of_mul_modEq_one ((u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1)).val
  have := Units.ext_iff.1 (mul_inv_cancel u)
  rw [Units.val_one] at this
  rw [← natCast_eq_natCast_iff, Nat.cast_one, ← this]; clear this
  rw [← natCast_zmod_val ((u * u⁻¹ : Units (ZMod (n + 1))) : ZMod (n + 1))]
  rw [Units.val_mul, val_mul, natCast_mod]

lemma isUnit_iff_coprime (m n : ℕ) : IsUnit (m : ZMod n) ↔ m.Coprime n := by
  refine ⟨fun H ↦ ?_, fun H ↦ (unitOfCoprime m H).isUnit⟩
  have H' := val_coe_unit_coprime H.unit
  rw [IsUnit.unit_spec, val_natCast, Nat.coprime_iff_gcd_eq_one] at H'
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

theorem mul_inv_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a * a⁻¹ = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inv_coe_unit, u.mul_inv]

theorem inv_mul_of_unit {n : ℕ} (a : ZMod n) (h : IsUnit a) : a⁻¹ * a = 1 := by
  rw [mul_comm, mul_inv_of_unit a h]

-- TODO: If we changed `⁻¹` so that `ZMod n` is always a `DivisionMonoid`,
-- then we could use the general lemma `inv_eq_of_mul_eq_one`
protected theorem inv_eq_of_mul_eq_one (n : ℕ) (a b : ZMod n) (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_of_unit a ⟨⟨a, b, h, mul_comm a b ▸ h⟩, rfl⟩) h

@[simp]
theorem inv_neg_one (n : ℕ) : (-1 : ZMod n)⁻¹ = -1 :=
  ZMod.inv_eq_of_mul_eq_one n (-1) (-1) (by simp)

lemma inv_mul_eq_one_of_isUnit {n : ℕ} {a : ZMod n} (ha : IsUnit a) (b : ZMod n) :
    a⁻¹ * b = 1 ↔ a = b := by
  -- ideally, this would be `ha.inv_mul_eq_one`, but `ZMod n` is not a `DivisionMonoid`...
  -- (see the "TODO" above)
  refine ⟨fun H ↦ ?_, fun H ↦ H ▸ a.inv_mul_of_unit ha⟩
  apply_fun (a * ·) at H
  rwa [← mul_assoc, a.mul_inv_of_unit ha, one_mul, mul_one, eq_comm] at H

-- TODO: this equivalence is true for `ZMod 0 = ℤ`, but needs to use different functions.
/-- Equivalence between the units of `ZMod n` and
the subtype of terms `x : ZMod n` for which `x.val` is coprime to `n` -/
def unitsEquivCoprime {n : ℕ} [NeZero n] : (ZMod n)ˣ ≃ { x : ZMod n // Nat.Coprime x.val n } where
  toFun x := ⟨x, val_coe_unit_coprime x⟩
  invFun x := unitOfCoprime x.1.val x.2
  left_inv := fun ⟨_, _, _, _⟩ => Units.ext (natCast_zmod_val _)
  right_inv := fun ⟨_, _⟩ => by simp

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
        rw [if_neg hmn0, ZMod.natCast_eq_natCast_iff, ← Nat.modEq_and_modEq_iff_modEq_mul h,
          Prod.fst_zmod_cast, Prod.snd_zmod_cast]
        refine
          ⟨(Nat.chineseRemainder h (cast x : ZMod m).val (cast x : ZMod n).val).2.left.trans ?_,
            (Nat.chineseRemainder h (cast x : ZMod m).val (cast x : ZMod n).val).2.right.trans ?_⟩
        · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val]
        · rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val]
      exact ⟨left_inv, left_inv.rightInverse_of_card_le (by simp)⟩
  { toFun := to_fun,
    invFun := inv_fun,
    map_mul' := RingHom.map_mul _
    map_add' := RingHom.map_add _
    left_inv := inv.1
    right_inv := inv.2 }

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

@[simp]
theorem add_self_eq_zero_iff_eq_zero {n : ℕ} (hn : Odd n) {a : ZMod n} :
    a + a = 0 ↔ a = 0 := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, ← Nat.prime_two.coprime_iff_not_dvd] at hn
  rw [← mul_two, ← @Nat.cast_two (ZMod n), ← ZMod.coe_unitOfCoprime 2 hn, Units.mul_left_eq_zero]

theorem ne_neg_self {n : ℕ} (hn : Odd n) {a : ZMod n} (ha : a ≠ 0) : a ≠ -a := by
  rwa [Ne, eq_neg_iff_add_eq_zero, add_self_eq_zero_iff_eq_zero hn]

theorem neg_one_ne_one {n : ℕ} [Fact (2 < n)] : (-1 : ZMod n) ≠ 1 :=
  CharP.neg_one_ne_one (ZMod n) n

@[simp]
theorem neg_eq_self_mod_two (a : ZMod 2) : -a = a := by
  fin_cases a <;> apply Fin.ext <;> simp; rfl

@[simp]
theorem intCast_abs_mod_two (a : ℤ) : (↑|a| : ZMod 2) = a := by
  cases le_total a 0 <;> simp [abs_of_nonneg, abs_of_nonpos, *]

theorem natAbs_mod_two (a : ℤ) : (a.natAbs : ZMod 2) = a := by
  simp

theorem val_ne_zero {n : ℕ} (a : ZMod n) : a.val ≠ 0 ↔ a ≠ 0 :=
  (val_eq_zero a).not

@[simp]
theorem val_pos {n : ℕ} {a : ZMod n} : 0 < a.val ↔ a ≠ 0 := by
  simp [pos_iff_ne_zero]

theorem val_eq_one : ∀ {n : ℕ} (_ : 1 < n) (a : ZMod n), a.val = 1 ↔ a = 1
  | 0, hn, _
  | 1, hn, _ => by simp at hn
  | n + 2, _, _ => by simp only [val, ZMod, Fin.ext_iff, Fin.val_one]

theorem neg_eq_self_iff {n : ℕ} (a : ZMod n) : -a = a ↔ a = 0 ∨ 2 * a.val = n := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul]
  cases n
  · rw [@mul_eq_zero ℤ, @mul_eq_zero ℕ, val_eq_zero]
    exact
      ⟨fun h => h.elim (by simp) Or.inl, fun h =>
        Or.inr (h.elim id fun h => h.elim (by simp) id)⟩
  conv_lhs =>
    rw [← a.natCast_zmod_val, ← Nat.cast_two, ← Nat.cast_mul, natCast_eq_zero_iff]
  constructor
  · rintro ⟨m, he⟩
    rcases m with - | m
    · rw [mul_zero, mul_eq_zero] at he
      rcases he with (⟨⟨⟩⟩ | he)
      exact Or.inl (a.val_eq_zero.1 he)
    cases m
    · right
      rwa [show 0 + 1 = 1 from rfl, mul_one] at he
    refine (a.val_lt.not_ge <| Nat.le_of_mul_le_mul_left ?_ zero_lt_two).elim
    rw [he, mul_comm]
    apply Nat.mul_le_mul_left
    simp
  · rintro (rfl | h)
    · rw [val_zero, mul_zero]
      apply dvd_zero
    · rw [h]

theorem val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n) : (a : ZMod n).val = a := by
  rw [val_natCast, Nat.mod_eq_of_lt h]

theorem val_cast_zmod_lt {m : ℕ} [NeZero m] (n : ℕ) [NeZero n] (a : ZMod m) :
    (a.cast : ZMod n).val < m := by
  rcases m with (⟨⟩|⟨m⟩); · cases NeZero.ne 0 rfl
  by_cases h : m < n
  · rcases n with (⟨⟩|⟨n⟩); · simp at h
    rw [← natCast_val, val_cast_of_lt]
    · apply a.val_lt
    apply lt_of_le_of_lt (Nat.le_of_lt_succ (ZMod.val_lt a)) h
  · rw [not_lt] at h
    apply lt_of_lt_of_le (ZMod.val_lt _) (le_trans h (Nat.le_succ m))

theorem neg_val' {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = (n - a.val) % n :=
  calc
    (-a).val = val (-a) % n := by rw [Nat.mod_eq_of_lt (-a).val_lt]
    _ = (n - val a) % n :=
      Nat.ModEq.add_right_cancel' (val a)
        (by
          rw [Nat.ModEq, ← val_add, neg_add_cancel, tsub_add_cancel_of_le a.val_le, Nat.mod_self,
            val_zero])

theorem neg_val {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = if a = 0 then 0 else n - a.val := by
  rw [neg_val']
  by_cases h : a = 0; · rw [if_pos h, h, val_zero, tsub_zero, Nat.mod_self]
  rw [if_neg h]
  apply Nat.mod_eq_of_lt
  apply Nat.sub_lt (NeZero.pos n)
  contrapose! h
  rwa [Nat.le_zero, val_eq_zero] at h

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

theorem val_pow {m n : ℕ} {a : ZMod n} [ilt : Fact (1 < n)] (h : a.val ^ m < n) :
    (a ^ m).val = a.val ^ m := by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    have : a.val ^ m < n := by
      obtain rfl | ha := eq_or_ne a 0
      · by_cases hm : m = 0
        · cases hm; simp [ilt.out]
        · simp only [val_zero, ne_eq, hm, not_false_eq_true, zero_pow, Nat.zero_lt_of_lt h]
      · exact lt_of_le_of_lt
         (Nat.pow_le_pow_right (by rwa [gt_iff_lt, ZMod.val_pos]) (Nat.le_succ m)) h
    rw [pow_succ, ZMod.val_mul, ih this, ← pow_succ, Nat.mod_eq_of_lt h]

theorem val_pow_le {m n : ℕ} [Fact (1 < n)] {a : ZMod n} : (a ^ m).val ≤ a.val ^ m := by
  induction m with
  | zero => simp [ZMod.val_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    apply le_trans (ZMod.val_mul_le _ _)
    apply Nat.mul_le_mul_right _ ih

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
  rw [add_sub_cancel_right, Int.natAbs_mul, Int.natAbs_natCast]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ <| Int.natAbs_pos.2 hm)
  rw [← mul_two]; apply Nat.div_mul_le_self

end ZMod

theorem RingHom.ext_zmod {n : ℕ} {R : Type*} [NonAssocSemiring R] (f g : ZMod n →+* R) : f = g := by
  ext a
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
  let φ : ℤ →+* R := f.comp (Int.castRingHom (ZMod n))
  let ψ : ℤ →+* R := g.comp (Int.castRingHom (ZMod n))
  change φ k = ψ k
  rw [φ.ext_int ψ]

namespace ZMod

variable {n : ℕ} {R : Type*}

instance subsingleton_ringHom [Semiring R] : Subsingleton (ZMod n →+* R) :=
  ⟨RingHom.ext_zmod⟩

instance subsingleton_ringEquiv [Semiring R] : Subsingleton (ZMod n ≃+* R) :=
  ⟨fun f g => by
    rw [RingEquiv.coe_ringHom_inj_iff]
    apply RingHom.ext_zmod _ _⟩

@[simp]
theorem ringHom_map_cast [NonAssocRing R] (f : R →+* ZMod n) (k : ZMod n) : f (cast k) = k := by
  cases n
  · dsimp [ZMod, ZMod.cast] at f k ⊢; simp
  · dsimp [ZMod.cast]
    rw [map_natCast, natCast_zmod_val]

/-- Any ring homomorphism into `ZMod n` has a right inverse. -/
theorem ringHom_rightInverse [NonAssocRing R] (f : R →+* ZMod n) :
    Function.RightInverse (cast : ZMod n → R) f :=
  ringHom_map_cast f

/-- Any ring homomorphism into `ZMod n` is surjective. -/
theorem ringHom_surjective [NonAssocRing R] (f : R →+* ZMod n) : Function.Surjective f :=
  (ringHom_rightInverse f).surjective

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

variable (f : { f : ℤ →+ A // f n = 0 })

@[simp]
theorem lift_coe (x : ℤ) : lift n f (x : ZMod n) = f.val x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

theorem lift_castAddHom (x : ℤ) : lift n f (Int.castAddHom (ZMod n) x) = f.1 x :=
  AddMonoidHom.liftOfRightInverse_comp_apply _ _ (fun _ => intCast_zmod_cast _) _ _

@[simp]
theorem lift_comp_coe : ZMod.lift n f ∘ ((↑) : ℤ → _) = f :=
  funext <| lift_coe _ _

@[simp]
theorem lift_comp_castAddHom : (ZMod.lift n f).comp (Int.castAddHom (ZMod n)) = f :=
  AddMonoidHom.ext <| lift_castAddHom _ _

lemma lift_injective {f : {f : ℤ →+ A // f n = 0}} :
    Injective (lift n f) ↔ ∀ m, f.1 m = 0 → (m : ZMod n) = 0 := by
  simp only [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff, SetLike.le_def,
    ZMod.intCast_surjective.forall, ZMod.lift_coe, AddMonoidHom.mem_ker, AddSubgroup.mem_bot]

end lift

end ZMod

/-!
### Groups of bounded torsion

For `G` a group and `n` a natural number, `G` having torsion dividing `n`
(`∀ x : G, n • x = 0`) can be derived from `Module R G` where `R` has characteristic dividing `n`.

It is however painful to have the API for such groups `G` stated in this generality, as `R` does not
appear anywhere in the lemmas' return type. Instead of writing the API in terms of a general `R`, we
therefore specialise to the canonical ring of order `n`, namely `ZMod n`.

This spelling `Module (ZMod n) G` has the extra advantage of providing the canonical action by
`ZMod n`. It is however Type-valued, so we might want to acquire a Prop-valued version in the
future.
-/

section Module
variable {n : ℕ} {S G : Type*} [AddCommGroup G] [SetLike S G] [AddSubgroupClass S G] {K : S} {x : G}

section general
variable [Module (ZMod n) G] {x : G}

lemma zmod_smul_mem (hx : x ∈ K) : ∀ a : ZMod n, a • x ∈ K := by
  simpa [ZMod.forall, Int.cast_smul_eq_zsmul] using zsmul_mem hx

/-- This cannot be made an instance because of the `[Module (ZMod n) G]` argument and the fact that
`n` only appears in the second argument of `SMulMemClass`, which is an `OutParam`. -/
lemma smulMemClass : SMulMemClass S (ZMod n) G where smul_mem _ _ {_x} hx := zmod_smul_mem hx _

namespace AddSubgroupClass

instance instZModSMul : SMul (ZMod n) K where smul a x := ⟨a • x, zmod_smul_mem x.2 _⟩

@[simp, norm_cast] lemma coe_zmod_smul (a : ZMod n) (x : K) : ↑(a • x) = (a • x : G) := rfl

instance instZModModule : Module (ZMod n) K := fast_instance%
  Subtype.coe_injective.module _ (AddSubmonoidClass.subtype K) coe_zmod_smul

end AddSubgroupClass

variable (n)

lemma ZModModule.char_nsmul_eq_zero (x : G) : n • x = 0 := by
  simp [← Nat.cast_smul_eq_nsmul (ZMod n)]

variable (G) in
lemma ZModModule.char_ne_one [Nontrivial G] : n ≠ 1 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
  exact hx <| by simpa using char_nsmul_eq_zero 1 x

variable (G) in
lemma ZModModule.two_le_char [NeZero n] [Nontrivial G] : 2 ≤ n := by
  have := NeZero.ne n
  have := char_ne_one n G
  cutsat

lemma ZModModule.periodicPts_add_left [NeZero n] (x : G) : periodicPts (x + ·) = .univ :=
  Set.eq_univ_of_forall fun y ↦ ⟨n, NeZero.pos n, by
    simpa [char_nsmul_eq_zero, IsPeriodicPt] using isFixedPt_id _⟩

end general

section two
variable [Module (ZMod 2) G]

lemma ZModModule.add_self (x : G) : x + x = 0 := by
  simpa [two_nsmul] using char_nsmul_eq_zero 2 x

lemma ZModModule.neg_eq_self (x : G) : -x = x := by simp [add_self, eq_comm, ← sub_eq_zero]

lemma ZModModule.sub_eq_add (x y : G) : x - y = x + y := by simp [neg_eq_self, sub_eq_add_neg]

lemma ZModModule.add_add_add_cancel (x y z : G) : (x + y) + (y + z) = x + z := by
  simpa [sub_eq_add] using sub_add_sub_cancel x y z

end two
end Module

section Group
variable {α : Type*} [Group α] {n : ℕ}

@[to_additive (attr := simp) nsmul_zmod_val_inv_nsmul]
lemma pow_zmod_val_inv_pow (hn : (Nat.card α).gcd n = 1) (a : α) :
    (a ^ (n⁻¹ : ZMod (Nat.card α)).val) ^ n = a := by
  replace hn : (Nat.card α).Coprime n := hn
  rw [← pow_mul', ← pow_mod_natCard, ← ZMod.val_natCast, Nat.cast_mul, ZMod.mul_val_inv hn.symm,
    ZMod.val_one_eq_one_mod, pow_mod_natCard, pow_one]

@[to_additive (attr := simp) zmod_val_inv_nsmul_nsmul]
lemma pow_pow_zmod_val_inv (hn : (Nat.card α).gcd n = 1) (a : α) :
    (a ^ n) ^ (n⁻¹ : ZMod (Nat.card α)).val = a := by rw [pow_right_comm, pow_zmod_val_inv_pow hn]

end Group

open ZMod

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
    simp only [ha, Nat.cast_add, add_eq_left, ZMod.natCast_eq_zero_iff] at H₁
    obtain ⟨b, rfl⟩ := H₁
    exact ⟨b, ha⟩

/-- Equivalence between `ℕ` and `ZMod N × ℕ`, sending `n` to `(n mod N, n / N)`. -/
def Nat.residueClassesEquiv (N : ℕ) [NeZero N] : ℕ ≃ ZMod N × ℕ where
  toFun n := (↑n, n / N)
  invFun p := p.1.val + N * p.2
  left_inv n := by simpa only [val_natCast] using mod_add_div n N
  right_inv p := by
    ext1
    · simp only [add_comm p.1.val, cast_add, cast_mul, natCast_self, zero_mul, natCast_val,
        cast_id', id_eq, zero_add]
    · simp only [add_comm p.1.val, mul_add_div (NeZero.pos _),
        (Nat.div_eq_zero_iff).2 <| .inr p.1.val_lt, add_zero]
