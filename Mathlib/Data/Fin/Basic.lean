/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Data.Int.DivMod
import Mathlib.Order.Lattice
import Mathlib.Tactic.Common
import Batteries.Data.Fin.Basic

/-!
# The finite type with `n` elements

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

* `finZeroElim` : Elimination principle for the empty set `Fin 0`, generalizes `Fin.elim0`.
Further definitions and eliminators can be found in `Init.Data.Fin.Lemmas`
* `Fin.equivSubtype` : Equivalence between `Fin n` and `{ i // i < n }`.

-/


assert_not_exists Monoid Finset

open Fin Nat Function

attribute [simp] Fin.succ_ne_zero Fin.castSucc_lt_last

/-- Elimination principle for the empty set `Fin 0`, dependent version. -/
def finZeroElim {α : Fin 0 → Sort*} (x : Fin 0) : α x :=
  x.elim0

namespace Fin

@[simp] theorem mk_eq_one {n a : Nat} {ha : a < n + 2} :
    (⟨a, ha⟩ : Fin (n + 2)) = 1 ↔ a = 1 :=
  mk.inj_iff

@[simp] theorem one_eq_mk {n a : Nat} {ha : a < n + 2} :
    1 = (⟨a, ha⟩ : Fin (n + 2)) ↔ a = 1 := by
  simp [eq_comm]

instance {n : ℕ} : CanLift ℕ (Fin n) Fin.val (· < n) where
  prf k hk := ⟨⟨k, hk⟩, rfl⟩

/-- A dependent variant of `Fin.elim0`. -/
def rec0 {α : Fin 0 → Sort*} (i : Fin 0) : α i := absurd i.2 (Nat.not_lt_zero _)

variable {n m : ℕ}

theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_val_eq n

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
lemma size_positive : Fin n → 0 < n := Fin.pos

lemma size_positive' [Nonempty (Fin n)] : 0 < n :=
  ‹Nonempty (Fin n)›.elim Fin.pos

protected theorem prop (a : Fin n) : a.val < n :=
  a.2

lemma lt_last_iff_ne_last {a : Fin (n + 1)} : a < last n ↔ a ≠ last n := by
  simp [Fin.lt_iff_le_and_ne, le_last]

lemma ne_zero_of_lt {a b : Fin (n + 1)} (hab : a < b) : b ≠ 0 :=
  Fin.ne_of_gt <| Fin.lt_of_le_of_lt a.zero_le hab

lemma ne_last_of_lt {a b : Fin (n + 1)} (hab : a < b) : a ≠ last n :=
  Fin.ne_of_lt <| Fin.lt_of_lt_of_le hab b.le_last

/-- Equivalence between `Fin n` and `{ i // i < n }`. -/
@[simps apply symm_apply]
def equivSubtype : Fin n ≃ { i // i < n } where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩

section coe

/-!
### coercions and constructions
-/

theorem val_eq_val (a b : Fin n) : (a : ℕ) = b ↔ a = b :=
  Fin.ext_iff.symm

theorem ne_iff_vne (a b : Fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
  Fin.ext_iff.not

theorem mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a' :=
  Fin.ext_iff

/-- Assume `k = l`. If two functions defined on `Fin k` and `Fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected theorem heq_fun_iff {α : Sort*} {k l : ℕ} (h : k = l) {f : Fin k → α} {g : Fin l → α} :
    f ≍ g ↔ ∀ i : Fin k, f i = g ⟨(i : ℕ), h ▸ i.2⟩ := by
  subst h
  simp [funext_iff]

/-- Assume `k = l` and `k' = l'`.
If two functions `Fin k → Fin k' → α` and `Fin l → Fin l' → α` are equal on each pair,
then they coincide (in the heq sense). -/
protected theorem heq_fun₂_iff {α : Sort*} {k l k' l' : ℕ} (h : k = l) (h' : k' = l')
    {f : Fin k → Fin k' → α} {g : Fin l → Fin l' → α} :
    f ≍ g ↔ ∀ (i : Fin k) (j : Fin k'), f i j = g ⟨(i : ℕ), h ▸ i.2⟩ ⟨(j : ℕ), h' ▸ j.2⟩ := by
  subst h
  subst h'
  simp [funext_iff]

/-- Two elements of `Fin k` and `Fin l` are heq iff their values in `ℕ` coincide. This requires
`k = l`. For the left implication without this assumption, see `val_eq_val_of_heq`. -/
protected theorem heq_ext_iff {k l : ℕ} (h : k = l) {i : Fin k} {j : Fin l} :
    i ≍ j ↔ (i : ℕ) = (j : ℕ) := by
  subst h
  simp [val_eq_val]

end coe


section Order

/-!
### order
-/

/-- `Fin.lt_or_ge` is an alias of `Fin.lt_or_le`.
It is preferred since it follows the mathlib naming convention. -/
protected alias lt_or_ge := Fin.lt_or_le
/-- `Fin.le_or_gt` is an alias of `Fin.le_or_lt`.
It is preferred since it follows the mathlib naming convention. -/
protected alias le_or_gt := Fin.le_or_lt

theorem le_iff_val_le_val {a b : Fin n} : a ≤ b ↔ (a : ℕ) ≤ b :=
  Iff.rfl

/-- `a < b` as natural numbers if and only if `a < b` in `Fin n`. -/
@[norm_cast, simp]
theorem val_fin_lt {n : ℕ} {a b : Fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
  Iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `Fin n`. -/
@[norm_cast, simp]
theorem val_fin_le {n : ℕ} {a b : Fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
  Iff.rfl

theorem min_val {a : Fin n} : min (a : ℕ) n = a := by simp

theorem max_val {a : Fin n} : max (a : ℕ) n = n := by simp

/-- Use the ordering on `Fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker,
unless we declare the `WellFoundedRelation` instance:
```lean
def factorial {n : ℕ} : Fin n → ℕ
  | ⟨0, _⟩ := 1
  | ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : ℕ} : WellFoundedRelation (Fin n) :=
  measure (val : Fin n → ℕ)

/-- `Fin.mk_zero` in `Lean` only applies in `Fin (n + 1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem mk_zero' (n : ℕ) [NeZero n] : (⟨0, pos_of_neZero n⟩ : Fin n) = 0 := rfl

@[deprecated Fin.zero_le (since := "2025-05-13")]
protected theorem zero_le' [NeZero n] (a : Fin n) : 0 ≤ a :=
  Nat.zero_le a.val

@[simp, norm_cast]
theorem val_pos_iff [NeZero n] {a : Fin n} : 0 < a.val ↔ 0 < a := by
  rw [← val_fin_lt, val_zero]

/--
The `Fin.pos_iff_ne_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem pos_iff_ne_zero' [NeZero n] (a : Fin n) : 0 < a ↔ a ≠ 0 := by
  rw [← val_pos_iff, Nat.pos_iff_ne_zero, val_ne_zero_iff]

@[simp] lemma cast_eq_self (a : Fin n) : a.cast rfl = a := rfl

@[simp] theorem cast_eq_zero {k l : ℕ} [NeZero k] [NeZero l]
    (h : k = l) (x : Fin k) : Fin.cast h x = 0 ↔ x = 0 := by
  simp [← val_eq_zero_iff]

lemma cast_injective {k l : ℕ} (h : k = l) : Injective (Fin.cast h) :=
  fun a b hab ↦ by simpa [← val_eq_val] using hab

theorem last_pos' [NeZero n] : 0 < last n := n.pos_of_neZero

theorem one_lt_last [NeZero n] : 1 < last (n + 1) := by
  rw [lt_iff_val_lt_val, val_one, val_last, Nat.lt_add_left_iff_pos, Nat.pos_iff_ne_zero]
  exact NeZero.ne n

end Order

/-! ### Coercions to `ℤ` and the `fin_omega` tactic. -/

open Int

theorem coe_int_sub_eq_ite {n : Nat} (u v : Fin n) :
    ((u - v : Fin n) : Int) = if v ≤ u then (u - v : Int) else (u - v : Int) + n := by
  rw [Fin.sub_def]
  split
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> omega
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> omega

theorem coe_int_sub_eq_mod {n : Nat} (u v : Fin n) :
    ((u - v : Fin n) : Int) = ((u : Int) - (v : Int)) % n := by
  rw [coe_int_sub_eq_ite]
  split
  · rw [Int.emod_eq_of_lt] <;> omega
  · rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt] <;> omega

theorem coe_int_add_eq_ite {n : Nat} (u v : Fin n) :
    ((u + v : Fin n) : Int) = if (u + v : ℕ) < n then (u + v : Int) else (u + v : Int) - n := by
  rw [Fin.add_def]
  split
  · rw [natCast_emod, Int.emod_eq_of_lt] <;> omega
  · rw [natCast_emod, Int.emod_eq_sub_self_emod, Int.emod_eq_of_lt] <;> omega

theorem coe_int_add_eq_mod {n : Nat} (u v : Fin n) :
    ((u + v : Fin n) : Int) = ((u : Int) + (v : Int)) % n := by
  omega

-- Write `a + b` as `if (a + b : ℕ) < n then (a + b : ℤ) else (a + b : ℤ) - n` and
-- similarly `a - b` as `if (b : ℕ) ≤ a then (a - b : ℤ) else (a - b : ℤ) + n`.
attribute [fin_omega] coe_int_sub_eq_ite coe_int_add_eq_ite

-- Rewrite inequalities in `Fin` to inequalities in `ℕ`
attribute [fin_omega] Fin.lt_iff_val_lt_val Fin.le_iff_val_le_val

-- Rewrite `1 : Fin (n + 2)` to `1 : ℤ`
attribute [fin_omega] val_one

/--
Preprocessor for `omega` to handle inequalities in `Fin`.
Note that this involves a lot of case splitting, so may be slow.
-/
-- Further adjustment to the simp set can probably make this more powerful.
-- Please experiment and PR updates!
macro "fin_omega" : tactic => `(tactic|
  { try simp only [fin_omega, ← Int.ofNat_lt, ← Int.ofNat_le] at *
    omega })

section Add

/-!
### addition, numerals, and coercion from Nat
-/

theorem val_one' (n : ℕ) [NeZero n] : ((1 : Fin n) : ℕ) = 1 % n :=
  rfl

@[deprecated val_one' (since := "2025-03-10")]
theorem val_one'' {n : ℕ} : ((1 : Fin (n + 1)) : ℕ) = 1 % (n + 1) :=
  rfl

theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  simp [← not_subsingleton_iff_nontrivial, subsingleton_iff_le_one]; cutsat

instance instNontrivial [n.AtLeastTwo] : Nontrivial (Fin n) :=
  nontrivial_iff_two_le.2 Nat.AtLeastTwo.one_lt

/-- If working with more than two elements, we can always pick a third distinct from two existing
elements. -/
theorem exists_ne_and_ne_of_two_lt (i j : Fin n) (h : 2 < n) : ∃ k, k ≠ i ∧ k ≠ j := by
  have : NeZero n := ⟨by cutsat⟩
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp_rw [← Fin.val_ne_iff]
  by_cases h0 : 0 ≠ i ∧ 0 ≠ j
  · exact ⟨0, h0⟩
  · by_cases h1 : 1 ≠ i ∧ 1 ≠ j
    · exact ⟨⟨1, by cutsat⟩, h1⟩
    · refine ⟨⟨2, by cutsat⟩, ?_⟩
      dsimp only
      cutsat

section Monoid

instance inhabitedFinOneAdd (n : ℕ) : Inhabited (Fin (1 + n)) :=
  haveI : NeZero (1 + n) := by rw [Nat.add_comm]; infer_instance
  inferInstance

@[simp]
theorem default_eq_zero (n : ℕ) [NeZero n] : (default : Fin n) = 0 :=
  rfl

end Monoid

theorem val_add_eq_ite {n : ℕ} (a b : Fin n) :
    (↑(a + b) : ℕ) = if n ≤ a + b then a + b - n else a + b := by
  rw [Fin.val_add, Nat.add_mod_eq_ite, Nat.mod_eq_of_lt (show ↑a < n from a.2),
    Nat.mod_eq_of_lt (show ↑b < n from b.2)]

theorem val_add_eq_of_add_lt {n : ℕ} {a b : Fin n} (huv : a.val + b.val < n) :
    (a + b).val = a.val + b.val := by
  rw [val_add]
  simp [Nat.mod_eq_of_lt huv]

lemma intCast_val_sub_eq_sub_add_ite {n : ℕ} (a b : Fin n) :
    ((a - b).val : ℤ) = a.val - b.val + if b ≤ a then 0 else n := by
  split <;> fin_omega

lemma sub_val_lt_sub {n : ℕ} {i j : Fin n} (hij : i ≤ j) : (j - i).val < n - i.val := by
  simp [sub_val_of_le hij, Nat.sub_lt_sub_right hij j.isLt]

lemma castLT_sub_nezero {n : ℕ} {i j : Fin n} (hij : i < j) :
    letI : NeZero (n - i.1) := neZero_iff.mpr (by cutsat)
    (j - i).castLT (sub_val_lt_sub (Fin.le_of_lt hij)) ≠ 0 := by
  refine Ne.symm (ne_of_val_ne ?_)
  simpa [coe_sub_iff_le.mpr (Fin.le_of_lt hij)] using by cutsat

lemma one_le_of_ne_zero {n : ℕ} [NeZero n] {k : Fin n} (hk : k ≠ 0) : 1 ≤ k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  cases n with
  | zero => simp only [Fin.isValue, Fin.zero_le]
  | succ n => rwa [Fin.le_iff_val_le_val, Fin.val_one, Nat.one_le_iff_ne_zero, val_ne_zero_iff]

lemma val_sub_one_of_ne_zero [NeZero n] {i : Fin n} (hi : i ≠ 0) : (i - 1).val = i - 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [Fin.sub_val_of_le (one_le_of_ne_zero hi), Fin.val_one', Nat.mod_eq_of_lt
    (Nat.succ_le_iff.mpr (nontrivial_iff_two_le.mp <| nontrivial_of_ne i 0 hi))]

section OfNatCoe

-- We allow the coercion from `Nat` to `Fin` in this section.
open Fin.NatCast

@[simp]
theorem ofNat_eq_cast (n : ℕ) [NeZero n] (a : ℕ) : Fin.ofNat n a = (a : Fin n) :=
  rfl

@[deprecated ofNat_eq_cast (since := "2025-05-30")]
alias ofNat'_eq_cast := ofNat_eq_cast

@[simp] lemma val_natCast (a n : ℕ) [NeZero n] : (a : Fin n).val = a % n := rfl

/-- Converting an in-range number to `Fin (n + 1)` produces a result
whose value is the original number. -/
theorem val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) : (a : Fin n).val = a :=
  Nat.mod_eq_of_lt h

/-- If `n` is non-zero, converting the value of a `Fin n` to `Fin n` results
in the same value. -/
@[simp, norm_cast] theorem cast_val_eq_self {n : ℕ} [NeZero n] (a : Fin n) : (a.val : Fin n) = a :=
  Fin.ext <| val_cast_of_lt a.isLt

-- This is a special case of `CharP.cast_eq_zero` that doesn't require typeclass search
@[simp high] lemma natCast_self (n : ℕ) [NeZero n] : (n : Fin n) = 0 := by ext; simp

@[simp] lemma natCast_eq_zero {a n : ℕ} [NeZero n] : (a : Fin n) = 0 ↔ n ∣ a := by
  simp [Fin.ext_iff, Nat.dvd_iff_mod_eq_zero]

@[simp]
theorem natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by ext; simp

theorem natCast_eq_mk {m n : ℕ} (h : m < n) : have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
    (m : Fin n) = Fin.mk m h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

theorem one_eq_mk_of_lt {n : ℕ} (h : 1 < n) : have : NeZero n := ⟨Nat.ne_zero_of_lt h⟩
    1 = Fin.mk 1 h :=
  Fin.val_inj.mp (Nat.mod_eq_of_lt h)

theorem le_val_last (i : Fin (n + 1)) : i ≤ n := by
  rw [Fin.natCast_eq_last]
  exact Fin.le_last i

variable {a b : ℕ}

lemma natCast_le_natCast (han : a ≤ n) (hbn : b ≤ n) : (a : Fin (n + 1)) ≤ b ↔ a ≤ b := by
  rw [← Nat.lt_succ_iff] at han hbn
  simp [le_iff_val_le_val, -val_fin_le, Nat.mod_eq_of_lt, han, hbn]

lemma natCast_lt_natCast (han : a ≤ n) (hbn : b ≤ n) : (a : Fin (n + 1)) < b ↔ a < b := by
  rw [← Nat.lt_succ_iff] at han hbn; simp [lt_iff_val_lt_val, Nat.mod_eq_of_lt, han, hbn]

lemma natCast_mono (hbn : b ≤ n) (hab : a ≤ b) : (a : Fin (n + 1)) ≤ b :=
  (natCast_le_natCast (hab.trans hbn) hbn).2 hab

lemma natCast_strictMono (hbn : b ≤ n) (hab : a < b) : (a : Fin (n + 1)) < b :=
  (natCast_lt_natCast (hab.le.trans hbn) hbn).2 hab

@[simp]
lemma castLE_natCast {m n : ℕ} [NeZero m] (h : m ≤ n) (a : ℕ) :
    letI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le m.pos_of_neZero h)⟩
    Fin.castLE h (a.cast : Fin m) = (a % m : ℕ) := by
  ext
  simp only [coe_castLE, val_natCast]
  rw [Nat.mod_eq_of_lt (a := a % m) (lt_of_lt_of_le (Nat.mod_lt _ m.pos_of_neZero) h)]

end OfNatCoe

end Add

section DivMod

theorem modNat_rev (i : Fin (m * n)) : i.rev.modNat = i.modNat.rev := by
  ext
  have H₁ : i % n + 1 ≤ n := i.modNat.is_lt
  have H₂ : i / n < m := i.divNat.is_lt
  simp only [val_rev]
  calc
    (m * n - (i + 1)) % n = (m * n - ((i / n) * n + i % n + 1)) % n := by rw [Nat.div_add_mod']
    _ = ((m - i / n - 1) * n + (n - (i % n + 1))) % n := by
      rw [Nat.mul_sub_right_distrib, Nat.one_mul, Nat.sub_add_sub_cancel _ H₁,
        Nat.mul_sub_right_distrib, Nat.sub_sub, Nat.add_assoc]
      exact Nat.le_mul_of_pos_left _ <| Nat.le_sub_of_add_le' H₂
    _ = n - (i % n + 1) := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt]; exact i.modNat.rev.is_lt

end DivMod

section Rec

/-!
### recursion and induction principles
-/

end Rec

open scoped Relator in
theorem liftFun_iff_succ {α : Type*} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} :
    ((· < ·) ⇒ r) f f ↔ ∀ i : Fin n, r (f (castSucc i)) (f i.succ) := by
  constructor
  · intro H i
    exact H i.castSucc_lt_succ
  · refine fun H i => Fin.induction (fun h ↦ ?_) ?_
    · simp at h
    · intro j ihj hij
      rw [← le_castSucc_iff] at hij
      obtain hij | hij := (le_def.1 hij).eq_or_lt
      · obtain rfl := Fin.ext hij
        exact H _
      · exact _root_.trans (ihj hij) (H j)

section AddGroup

theorem eq_zero (n : Fin 1) : n = 0 := Subsingleton.elim _ _

lemma eq_one_of_ne_zero (i : Fin 2) (hi : i ≠ 0) : i = 1 := by fin_omega

@[deprecated (since := "2025-04-27")]
alias eq_one_of_neq_zero := eq_one_of_ne_zero

@[simp]
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  · simp
  rw [Fin.coe_neg, Fin.val_one, Nat.add_one_sub_one, Nat.mod_eq_of_lt]
  constructor

theorem last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i :=
  Fin.ext <| by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]

theorem add_one_le_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) : a + 1 ≤ b := by
  cases n <;> fin_omega

theorem exists_eq_add_of_le {n : ℕ} {a b : Fin n} (h : a ≤ b) : ∃ k ≤ b, b = a + k := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k := Nat.exists_eq_add_of_le h
  have hkb : k ≤ b := by omega
  refine ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

theorem exists_eq_add_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) :
    ∃ k < b, k + 1 ≤ b ∧ b = a + k + 1 := by
  cases n
  · cutsat
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by omega
  refine ⟨⟨k, hkb.trans b.is_lt⟩, hkb, by fin_omega, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

lemma pos_of_ne_zero {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) : 0 < a :=
  Nat.pos_of_ne_zero (val_ne_of_ne h)

lemma sub_succ_le_sub_of_le {n : ℕ} {u v : Fin (n + 2)} (h : u < v) : v - (u + 1) < v - u := by
  fin_omega

end AddGroup

open Fin.NatCast in
@[simp]
theorem coe_natCast_eq_mod (m n : ℕ) [NeZero m] :
    ((n : Fin m) : ℕ) = n % m :=
  rfl

@[simp]
theorem coe_ofNat_eq_mod (m n : ℕ) [NeZero m] :
    ((ofNat(n) : Fin m) : ℕ) = ofNat(n) % m :=
  rfl

theorem val_add_one_of_lt' {n : ℕ} [NeZero n] {i : Fin n} (h : i + 1 < n) :
    (i + 1).val = i.val + 1 := by
  simpa [add_def] using Nat.mod_eq_of_lt (by cutsat)

instance [NeZero n] [NeZero ofNat(m)] : NeZero (ofNat(m) : Fin (n + ofNat(m))) := by
  suffices m % (n + m) = m by simpa [neZero_iff, Fin.ext_iff, OfNat.ofNat, this] using NeZero.ne m
  apply Nat.mod_eq_of_lt
  simpa using zero_lt_of_ne_zero (NeZero.ne n)

section Mul

/-!
### mul
-/

protected theorem mul_one' [NeZero n] (k : Fin n) : k * 1 = k := by
  rcases n with - | n
  · simp [eq_iff_true_of_subsingleton]
  cases n
  · simp [fin_one_eq_zero]
  simp [mul_def, mod_eq_of_lt (is_lt k)]

protected theorem one_mul' [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by
  rw [Fin.mul_comm, Fin.mul_one']

protected theorem mul_zero' [NeZero n] (k : Fin n) : k * 0 = 0 := by simp [mul_def]

protected theorem zero_mul' [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by
  simp [mul_def]

end Mul

end Fin
