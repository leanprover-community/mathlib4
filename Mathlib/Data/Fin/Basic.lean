/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Data.Int.DivMod
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.Common

/-!
# The finite type with `n` elements

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

### Induction principles

* `finZeroElim` : Elimination principle for the empty set `Fin 0`, generalizes `Fin.elim0`.
Further definitions and eliminators can be found in `Init.Data.Fin.Lemmas`

### Embeddings and isomorphisms

* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.succEmb` : `Fin.succ` as an `Embedding`;
* `Fin.castLEEmb h` : `Fin.castLE` as an `Embedding`, embed `Fin n` into `Fin m`, `h : n ≤ m`;
* `finCongr` : `Fin.cast` as an `Equiv`, equivalence between `Fin n` and `Fin m` when `n = m`;
* `Fin.castAddEmb m` : `Fin.castAdd` as an `Embedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccEmb` : `Fin.castSucc` as an `Embedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.addNatEmb m i` : `Fin.addNat` as an `Embedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddEmb n i` : `Fin.natAdd` as an `Embedding`, adds `n` on `i` on the left;

### Other casts

* `Fin.divNat i` : divides `i : Fin (m * n)` by `n`;
* `Fin.modNat i` : takes the mod of `i : Fin (m * n)` by `n`;

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

@[deprecated (since := "2025-02-24")]
alias val_zero' := val_zero

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

instance nontrivial {n : ℕ} [NeZero n] : Nontrivial (Fin (n + 1)) where
  exists_pair_ne := ⟨0, 1, (ne_iff_vne 0 1).mpr (by simp [val_one', val_zero, NeZero.ne])⟩

theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  rcases n with (_ | _ | n) <;>
  simp [Fin.nontrivial, not_nontrivial, Nat.succ_le_iff]

/-- If working with more than two elements, we can always pick a third distinct from two existing
elements. -/
theorem exists_ne_and_ne_of_two_lt (i j : Fin n) (h : 2 < n) : ∃ k, k ≠ i ∧ k ≠ j := by
  have : NeZero n := ⟨by omega⟩
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  simp_rw [← Fin.val_ne_iff]
  by_cases h0 : 0 ≠ i ∧ 0 ≠ j
  · exact ⟨0, h0⟩
  · by_cases h1 : 1 ≠ i ∧ 1 ≠ j
    · exact ⟨⟨1, by omega⟩, h1⟩
    · refine ⟨⟨2, by omega⟩, ?_⟩
      dsimp only
      omega

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

section Succ

/-!
### succ and casts into larger Fin types
-/

lemma succ_injective (n : ℕ) : Injective (@Fin.succ n) := fun a b ↦ by simp [Fin.ext_iff]

@[simp]
theorem exists_succ_eq {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 :=
  ⟨fun ⟨_, hy⟩ => hy ▸ succ_ne_zero _, x.cases (fun h => h.irrefl.elim) (fun _ _ => ⟨_, rfl⟩)⟩

theorem exists_succ_eq_of_ne_zero {x : Fin (n + 1)} (h : x ≠ 0) :
    ∃ y, Fin.succ y = x := exists_succ_eq.mpr h

@[simp]
theorem succ_zero_eq_one' [NeZero n] : Fin.succ (0 : Fin n) = 1 := by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

theorem one_pos' [NeZero n] : (0 : Fin (n + 1)) < 1 := succ_zero_eq_one' (n := n) ▸ succ_pos _
theorem zero_ne_one' [NeZero n] : (0 : Fin (n + 1)) ≠ 1 := Fin.ne_of_lt one_pos'

/--
The `Fin.succ_one_eq_two` in `Lean` only applies in `Fin (n+2)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem succ_one_eq_two' [NeZero n] : Fin.succ (1 : Fin (n + 1)) = 2 := by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl

-- Version of `succ_one_eq_two` to be used by `dsimp`.
-- Note the `'` swapped around due to a move to std4.

/--
The `Fin.le_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem le_zero_iff' {n : ℕ} [NeZero n] {k : Fin n} : k ≤ 0 ↔ k = 0 :=
  ⟨fun h => Fin.ext <| by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact Nat.le_refl _⟩

-- TODO: Move to Batteries
@[simp] lemma castLE_inj {hmn : m ≤ n} {a b : Fin m} : castLE hmn a = castLE hmn b ↔ a = b := by
  simp [Fin.ext_iff]

@[simp] lemma castAdd_inj {a b : Fin m} : castAdd n a = castAdd n b ↔ a = b := by simp [Fin.ext_iff]

attribute [simp] castSucc_inj

lemma castLE_injective (hmn : m ≤ n) : Injective (castLE hmn) :=
  fun _ _ hab ↦ Fin.ext (congr_arg val hab :)

lemma castAdd_injective (m n : ℕ) : Injective (@Fin.castAdd m n) := castLE_injective _

lemma castSucc_injective (n : ℕ) : Injective (@Fin.castSucc n) := castAdd_injective _ _

@[simp] lemma castLE_castSucc {n m} (i : Fin n) (h : n + 1 ≤ m) :
    i.castSucc.castLE h = i.castLE (Nat.le_of_succ_le h) :=
  rfl

@[simp] lemma castLE_comp_castSucc {n m} (h : n + 1 ≤ m) :
    Fin.castLE h ∘ Fin.castSucc = Fin.castLE (Nat.le_of_succ_le h) :=
  rfl

@[simp] lemma castLE_rfl (n : ℕ) : Fin.castLE (le_refl n) = id :=
  rfl

@[simp]
theorem range_castLE {n k : ℕ} (h : n ≤ k) : Set.range (castLE h) = { i : Fin k | (i : ℕ) < n } :=
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

@[simp]
theorem coe_of_injective_castLE_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLE_injective h)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_castLE h]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)

theorem leftInverse_cast (eq : n = m) : LeftInverse (Fin.cast eq.symm) (Fin.cast eq) :=
  fun _ => rfl

theorem rightInverse_cast (eq : n = m) : RightInverse (Fin.cast eq.symm) (Fin.cast eq) :=
  fun _ => rfl

@[simp]
theorem cast_inj (eq : n = m) {a b : Fin n} : a.cast eq = b.cast eq ↔ a = b := by
  simp [← val_inj]

@[simp]
theorem cast_lt_cast (eq : n = m) {a b : Fin n} : a.cast eq < b.cast eq ↔ a < b :=
  Iff.rfl

@[simp]
theorem cast_le_cast (eq : n = m) {a b : Fin n} : a.cast eq ≤ b.cast eq ↔ a ≤ b :=
  Iff.rfl

/-- The 'identity' equivalence between `Fin m` and `Fin n` when `m = n`. -/
@[simps]
def _root_.finCongr (eq : n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast eq
  invFun := Fin.cast eq.symm
  left_inv := leftInverse_cast eq
  right_inv := rightInverse_cast eq

@[simp] lemma _root_.finCongr_apply_mk (h : m = n) (k : ℕ) (hk : k < m) :
    finCongr h ⟨k, hk⟩ = ⟨k, h ▸ hk⟩ := rfl

@[simp]
lemma _root_.finCongr_refl (h : n = n := rfl) : finCongr h = Equiv.refl (Fin n) := by ext; simp

@[simp] lemma _root_.finCongr_symm (h : m = n) : (finCongr h).symm = finCongr h.symm := rfl

@[simp] lemma _root_.finCongr_apply_coe (h : m = n) (k : Fin m) : (finCongr h k : ℕ) = k := rfl

lemma _root_.finCongr_symm_apply_coe (h : m = n) (k : Fin n) : ((finCongr h).symm k : ℕ) = k := rfl

/-- While in many cases `finCongr` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
lemma _root_.finCongr_eq_equivCast (h : n = m) : finCongr h = .cast (h ▸ rfl) := by subst h; simp

/-- While in many cases `Fin.cast` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_eq_cast (h : n = m) : (Fin.cast h : Fin n → Fin m) = _root_.cast (h ▸ rfl) := by
  subst h
  ext
  rfl

theorem castSucc_le_succ {n} (i : Fin n) : i.castSucc ≤ i.succ := Nat.le_succ i

@[simp] theorem castSucc_le_castSucc_iff {a b : Fin n} : castSucc a ≤ castSucc b ↔ a ≤ b := .rfl

@[simp] theorem succ_le_castSucc_iff {a b : Fin n} : succ a ≤ castSucc b ↔ a < b := by
  rw [le_castSucc_iff, succ_lt_succ_iff]

@[simp] theorem castSucc_lt_succ_iff {a b : Fin n} : castSucc a < succ b ↔ a ≤ b := by
  rw [castSucc_lt_iff_succ_le, succ_le_succ_iff]

theorem le_of_castSucc_lt_of_succ_lt {a b : Fin (n + 1)} {i : Fin n}
    (hl : castSucc i < a) (hu : b < succ i) : b < a := by
  simp [Fin.lt_def, -val_fin_lt] at *; omega

theorem castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p < i.succ := by
  simp [Fin.lt_def, -val_fin_lt]; omega

theorem succ_le_or_le_castSucc (p : Fin (n + 1)) (i : Fin n) : succ i ≤ p ∨ p ≤ i.castSucc := by
  rw [le_castSucc_iff, ← castSucc_lt_iff_succ_le]
  exact p.castSucc_lt_or_lt_succ i

theorem eq_castSucc_of_ne_last {x : Fin (n + 1)} (h : x ≠ (last _)) :
    ∃ y, Fin.castSucc y = x := exists_castSucc_eq.mpr h

@[deprecated (since := "2025-02-06")]
alias exists_castSucc_eq_of_ne_last := eq_castSucc_of_ne_last

theorem forall_fin_succ' {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ (∀ i : Fin n, P i.castSucc) ∧ P (.last _) :=
  ⟨fun H => ⟨fun _ => H _, H _⟩, fun ⟨H0, H1⟩ i => Fin.lastCases H1 H0 i⟩

-- to match `Fin.eq_zero_or_eq_succ`
theorem eq_castSucc_or_eq_last {n : Nat} (i : Fin (n + 1)) :
    (∃ j : Fin n, i = j.castSucc) ∨ i = last n := i.lastCases (Or.inr rfl) (Or.inl ⟨·, rfl⟩)

@[simp]
theorem castSucc_ne_last {n : ℕ} (i : Fin n) : i.castSucc ≠ .last n :=
  Fin.ne_of_lt i.castSucc_lt_last

theorem exists_fin_succ' {P : Fin (n + 1) → Prop} :
    (∃ i, P i) ↔ (∃ i : Fin n, P i.castSucc) ∨ P (.last _) :=
  ⟨fun ⟨i, h⟩ => Fin.lastCases Or.inr (fun i hi => Or.inl ⟨i, hi⟩) i h,
   fun h => h.elim (fun ⟨i, hi⟩ => ⟨i.castSucc, hi⟩) (fun h => ⟨.last _, h⟩)⟩

/--
The `Fin.castSucc_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem castSucc_zero' [NeZero n] : castSucc (0 : Fin n) = 0 := rfl

@[simp]
theorem castSucc_pos_iff [NeZero n] {i : Fin n} : 0 < castSucc i ↔ 0 < i := by simp [← val_pos_iff]

/-- `castSucc i` is positive when `i` is positive.

The `Fin.castSucc_pos` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis. -/
alias ⟨_, castSucc_pos'⟩ := castSucc_pos_iff

@[deprecated Fin.castSucc_eq_zero_iff (since := "2025-05-13")]
theorem castSucc_eq_zero_iff' [NeZero n] (a : Fin n) : castSucc a = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| by simp).symm

@[deprecated Fin.castSucc_ne_zero_iff (since := "2025-05-13")]
theorem castSucc_ne_zero_iff' [NeZero n] (a : Fin n) : castSucc a ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| castSucc_eq_zero_iff

theorem castSucc_ne_zero_of_lt {p i : Fin n} (h : p < i) : castSucc i ≠ 0 := by
  cases n
  · exact i.elim0
  · rw [castSucc_ne_zero_iff, Ne, Fin.ext_iff]
    exact ((zero_le _).trans_lt h).ne'

theorem succ_ne_last_iff (a : Fin (n + 1)) : succ a ≠ last (n + 1) ↔ a ≠ last n :=
  not_iff_not.mpr <| succ_eq_last_succ

theorem succ_ne_last_of_lt {p i : Fin n} (h : i < p) : succ i ≠ last n := by
  cases n
  · exact i.elim0
  · rw [succ_ne_last_iff, Ne, Fin.ext_iff]
    exact ((le_last _).trans_lt' h).ne

open Fin.NatCast in
@[norm_cast, simp]
theorem coe_eq_castSucc {a : Fin n} : ((a : Nat) : Fin (n + 1)) = castSucc a := by
  ext
  exact val_cast_of_lt (Nat.lt.step a.is_lt)

open Fin.NatCast in
theorem coe_succ_lt_iff_lt {n : ℕ} {j k : Fin n} : (j : Fin (n + 1)) < k ↔ j < k := by
  simp only [coe_eq_castSucc, castSucc_lt_castSucc_iff]

@[simp]
theorem range_castSucc {n : ℕ} : Set.range (castSucc : Fin n → Fin n.succ) =
    ({ i | (i : ℕ) < n } : Set (Fin n.succ)) := range_castLE (by omega)

@[simp]
theorem coe_of_injective_castSucc_symm {n : ℕ} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)

theorem castSucc_castAdd (i : Fin n) : castSucc (castAdd m i) = castAdd (m + 1) i := rfl

theorem succ_castAdd (i : Fin n) : succ (castAdd m i) =
    if h : i.succ = last _ then natAdd n (0 : Fin (m + 1))
      else castAdd (m + 1) ⟨i.1 + 1, lt_of_le_of_ne i.2 (Fin.val_ne_iff.mpr h)⟩ := by
  split_ifs with h
  exacts [Fin.ext (congr_arg Fin.val h :), rfl]

theorem succ_natAdd (i : Fin m) : succ (natAdd n i) = natAdd n (succ i) := rfl

end Succ

section Pred

/-!
### pred
-/

theorem pred_one' [NeZero n] (h := (zero_ne_one' (n := n)).symm) :
    Fin.pred (1 : Fin (n + 1)) h = 0 := by
  simp_rw [Fin.ext_iff, coe_pred, val_one', val_zero, Nat.sub_eq_zero_iff_le, Nat.mod_le]

theorem pred_last (h := Fin.ext_iff.not.2 last_pos'.ne') :
    pred (last (n + 1)) h = last n := by simp_rw [← succ_last, pred_succ]

theorem pred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ 0) : pred i hi < j ↔ i < succ j := by
  rw [← succ_lt_succ_iff, succ_pred]
theorem lt_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ 0) : j < pred i hi ↔ succ j < i := by
  rw [← succ_lt_succ_iff, succ_pred]
theorem pred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ 0) : pred i hi ≤ j ↔ i ≤ succ j := by
  rw [← succ_le_succ_iff, succ_pred]
theorem le_pred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ 0) : j ≤ pred i hi ↔ succ j ≤ i := by
  rw [← succ_le_succ_iff, succ_pred]

theorem castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a ≠ 0) :
    (a.pred ha).castSucc = (castSucc a).pred (castSucc_ne_zero_iff.mpr ha) := rfl

theorem castSucc_pred_add_one_eq {a : Fin (n + 1)} (ha : a ≠ 0) :
    (a.pred ha).castSucc + 1 = a := by
  simp

theorem le_pred_castSucc_iff {a b : Fin (n + 1)} (ha : castSucc a ≠ 0) :
    b ≤ (castSucc a).pred ha ↔ b < a := by
  rw [le_pred_iff, succ_le_castSucc_iff]

theorem pred_castSucc_lt_iff {a b : Fin (n + 1)} (ha : castSucc a ≠ 0) :
    (castSucc a).pred ha < b ↔ a ≤ b := by
  rw [pred_lt_iff, castSucc_lt_succ_iff]

theorem pred_castSucc_lt {a : Fin (n + 1)} (ha : castSucc a ≠ 0) :
    (castSucc a).pred ha < a := by rw [pred_castSucc_lt_iff, le_def]

theorem le_castSucc_pred_iff {a b : Fin (n + 1)} (ha : a ≠ 0) :
    b ≤ castSucc (a.pred ha) ↔ b < a := by
  rw [castSucc_pred_eq_pred_castSucc, le_pred_castSucc_iff]

theorem castSucc_pred_lt_iff {a b : Fin (n + 1)} (ha : a ≠ 0) :
    castSucc (a.pred ha) < b ↔ a ≤ b := by
  rw [castSucc_pred_eq_pred_castSucc, pred_castSucc_lt_iff]

theorem castSucc_pred_lt {a : Fin (n + 1)} (ha : a ≠ 0) :
    castSucc (a.pred ha) < a := by rw [castSucc_pred_lt_iff, le_def]

end Pred

section CastPred

/-- `castPred i` sends `i : Fin (n + 1)` to `Fin n` as long as i ≠ last n. -/
@[inline] def castPred (i : Fin (n + 1)) (h : i ≠ last n) : Fin n := castLT i (val_lt_last h)

@[simp]
lemma castLT_eq_castPred (i : Fin (n + 1)) (h : i < last _) (h' := Fin.ext_iff.not.2 h.ne) :
    castLT i h = castPred i h' := rfl

@[simp]
lemma coe_castPred (i : Fin (n + 1)) (h : i ≠ last _) : (castPred i h : ℕ) = i := rfl

@[simp]
theorem castPred_castSucc {i : Fin n} (h' := Fin.ext_iff.not.2 (castSucc_lt_last i).ne) :
    castPred (castSucc i) h' = i := rfl

@[simp]
theorem castSucc_castPred (i : Fin (n + 1)) (h : i ≠ last n) :
    castSucc (i.castPred h) = i := by
  rcases exists_castSucc_eq.mpr h with ⟨y, rfl⟩
  rw [castPred_castSucc]

theorem castPred_eq_iff_eq_castSucc (i : Fin (n + 1)) (hi : i ≠ last _) (j : Fin n) :
    castPred i hi = j ↔ i = castSucc j :=
  ⟨fun h => by rw [← h, castSucc_castPred], fun h => by simp_rw [h, castPred_castSucc]⟩

@[simp]
theorem castPred_mk (i : ℕ) (h₁ : i < n) (h₂ := h₁.trans (Nat.lt_succ_self _))
    (h₃ : ⟨i, h₂⟩ ≠ last _ := (ne_iff_vne _ _).mpr (val_last _ ▸ h₁.ne)) :
    castPred ⟨i, h₂⟩ h₃ = ⟨i, h₁⟩ := rfl

@[simp]
theorem castPred_le_castPred_iff {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi ≤ castPred j hj ↔ i ≤ j := Iff.rfl

/-- A version of the right-to-left implication of `castPred_le_castPred_iff`
that deduces `i ≠ last n` from `i ≤ j` and `j ≠ last n`. -/
@[gcongr]
theorem castPred_le_castPred {i j : Fin (n + 1)} (h : i ≤ j) (hj : j ≠ last n) :
    castPred i (by rw [← lt_last_iff_ne_last] at hj ⊢; exact Fin.lt_of_le_of_lt h hj) ≤
      castPred j hj :=
  h

@[simp]
theorem castPred_lt_castPred_iff {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi < castPred j hj ↔ i < j := Iff.rfl

/-- A version of the right-to-left implication of `castPred_lt_castPred_iff`
that deduces `i ≠ last n` from `i < j`. -/
@[gcongr]
theorem castPred_lt_castPred {i j : Fin (n + 1)} (h : i < j) (hj : j ≠ last n) :
    castPred i (ne_last_of_lt h) < castPred j hj := h

theorem castPred_lt_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ last n) :
    castPred i hi < j ↔ i < castSucc j := by
  rw [← castSucc_lt_castSucc_iff, castSucc_castPred]

theorem lt_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ last n) :
    j < castPred i hi ↔ castSucc j < i := by
  rw [← castSucc_lt_castSucc_iff, castSucc_castPred]

theorem castPred_le_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ last n) :
    castPred i hi ≤ j ↔ i ≤ castSucc j := by
  rw [← castSucc_le_castSucc_iff, castSucc_castPred]

theorem le_castPred_iff {j : Fin n} {i : Fin (n + 1)} (hi : i ≠ last n) :
    j ≤ castPred i hi ↔ castSucc j ≤ i := by
  rw [← castSucc_le_castSucc_iff, castSucc_castPred]

@[simp]
theorem castPred_inj {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi = castPred j hj ↔ i = j := by
  simp_rw [Fin.ext_iff, le_antisymm_iff, ← le_def, castPred_le_castPred_iff]

@[simp]
theorem castPred_zero [NeZero n] :
    castPred (0 : Fin (n + 1)) (Fin.ext_iff.not.2 last_pos'.ne) = 0 := rfl

@[deprecated (since := "2025-05-11")]
alias castPred_zero' := castPred_zero

@[simp]
theorem castPred_eq_zero [NeZero n] {i : Fin (n + 1)} (h : i ≠ last n) :
    Fin.castPred i h = 0 ↔ i = 0 := by
  rw [← castPred_zero, castPred_inj]

theorem castPred_ne_zero [NeZero n] {i : Fin (n + 1)} (h₁ : i ≠ last n) (h₂ : i ≠ 0) :
    castPred i h₁ ≠ 0 :=
  (castPred_eq_zero h₁).not.mpr h₂

@[simp]
theorem castPred_one [NeZero n] :
    castPred (1 : Fin (n + 2)) (Fin.ext_iff.not.2 one_lt_last.ne) = 1 := by
  cases n
  · exact subsingleton_one.elim _ 1
  · rfl

theorem succ_castPred_eq_castPred_succ {a : Fin (n + 1)} (ha : a ≠ last n)
    (ha' := a.succ_ne_last_iff.mpr ha) :
    (a.castPred ha).succ = (succ a).castPred ha' := rfl

theorem succ_castPred_eq_add_one {a : Fin (n + 1)} (ha : a ≠ last n) :
    (a.castPred ha).succ = a + 1 := by
  cases a using lastCases
  · exact (ha rfl).elim
  · rw [castPred_castSucc, coeSucc_eq_succ]

theorem castpred_succ_le_iff {a b : Fin (n + 1)} (ha : succ a ≠ last (n + 1)) :
    (succ a).castPred ha ≤ b ↔ a < b := by
  rw [castPred_le_iff, succ_le_castSucc_iff]

theorem lt_castPred_succ_iff {a b : Fin (n + 1)} (ha : succ a ≠ last (n + 1)) :
    b < (succ a).castPred ha ↔ b ≤ a := by
  rw [lt_castPred_iff, castSucc_lt_succ_iff]

theorem lt_castPred_succ {a : Fin (n + 1)} (ha : succ a ≠ last (n + 1)) :
    a < (succ a).castPred ha := by rw [lt_castPred_succ_iff, le_def]

theorem succ_castPred_le_iff {a b : Fin (n + 1)} (ha : a ≠ last n) :
    succ (a.castPred ha) ≤ b ↔ a < b := by
  rw [succ_castPred_eq_castPred_succ ha, castpred_succ_le_iff]

theorem lt_succ_castPred_iff {a b : Fin (n + 1)} (ha : a ≠ last n) :
    b < succ (a.castPred ha) ↔ b ≤ a := by
  rw [succ_castPred_eq_castPred_succ ha, lt_castPred_succ_iff]

theorem lt_succ_castPred {a : Fin (n + 1)} (ha : a ≠ last n) :
    a < succ (a.castPred ha) := by rw [lt_succ_castPred_iff, le_def]

theorem castPred_le_pred_iff {a b : Fin (n + 1)} (ha : a ≠ last n) (hb : b ≠ 0) :
    castPred a ha ≤ pred b hb ↔ a < b := by
  rw [le_pred_iff, succ_castPred_le_iff]

theorem pred_lt_castPred_iff {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ last n) :
    pred a ha < castPred b hb ↔ a ≤ b := by
  rw [lt_castPred_iff, castSucc_pred_lt_iff ha]

theorem pred_lt_castPred {a : Fin (n + 1)} (h₁ : a ≠ 0) (h₂ : a ≠ last n) :
    pred a h₁ < castPred a h₂ := by
  rw [pred_lt_castPred_iff, le_def]

end CastPred

section SuccAbove
variable {p : Fin (n + 1)} {i j : Fin n}

/-- `succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`. -/
def succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if castSucc i < p then i.castSucc else i.succ

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `castSucc` when the resulting `i.castSucc < p`. -/
lemma succAbove_of_castSucc_lt (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p) :
    p.succAbove i = castSucc i := if_pos h

lemma succAbove_of_succ_le (p : Fin (n + 1)) (i : Fin n) (h : succ i ≤ p) :
    p.succAbove i = castSucc i :=
  succAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
lemma succAbove_of_le_castSucc (p : Fin (n + 1)) (i : Fin n) (h : p ≤ castSucc i) :
    p.succAbove i = i.succ := if_neg (Fin.not_lt.2 h)

lemma succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fin n) (h : p < succ i) :
    p.succAbove i = succ i := succAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

lemma succAbove_succ_of_lt (p i : Fin n) (h : p < i) : succAbove p.succ i = i.succ :=
  succAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)

lemma succAbove_succ_of_le (p i : Fin n) (h : i ≤ p) : succAbove p.succ i = i.castSucc :=
  succAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)

@[simp] lemma succAbove_succ_self (j : Fin n) : j.succ.succAbove j = j.castSucc :=
  succAbove_succ_of_le _ _ Fin.le_rfl

lemma succAbove_castSucc_of_lt (p i : Fin n) (h : i < p) : succAbove p.castSucc i = i.castSucc :=
  succAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)

lemma succAbove_castSucc_of_le (p i : Fin n) (h : p ≤ i) : succAbove p.castSucc i = i.succ :=
  succAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.2 h)

@[simp] lemma succAbove_castSucc_self (j : Fin n) : succAbove j.castSucc j = j.succ :=
  succAbove_castSucc_of_le _ _ Fin.le_rfl

lemma succAbove_pred_of_lt (p i : Fin (n + 1)) (h : p < i) :
    succAbove p (i.pred (Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h)) = i := by
  rw [succAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h), succ_pred]

lemma succAbove_pred_of_le (p i : Fin (n + 1)) (h : i ≤ p) (hi : i ≠ 0) :
    succAbove p (i.pred hi) = (i.pred hi).castSucc := succAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)

@[simp] lemma succAbove_pred_self (p : Fin (n + 1)) (h : p ≠ 0) :
    succAbove p (p.pred h) = (p.pred h).castSucc := succAbove_pred_of_le _ _ Fin.le_rfl h

lemma succAbove_castPred_of_lt (p i : Fin (n + 1)) (h : i < p) :
    succAbove p (i.castPred (Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p.le_last)) = i := by
  rw [succAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h), castSucc_castPred]

lemma succAbove_castPred_of_le (p i : Fin (n + 1)) (h : p ≤ i) (hi : i ≠ last n) :
    succAbove p (i.castPred hi) = (i.castPred hi).succ :=
  succAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)

lemma succAbove_castPred_self (p : Fin (n + 1)) (h : p ≠ last n) :
    succAbove p (p.castPred h) = (p.castPred h).succ := succAbove_castPred_of_le _ _ Fin.le_rfl h

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself -/
@[simp]
lemma succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  rcases p.castSucc_lt_or_lt_succ i with (h | h)
  · rw [succAbove_of_castSucc_lt _ _ h]
    exact Fin.ne_of_lt h
  · rw [succAbove_of_lt_succ _ _ h]
    exact Fin.ne_of_gt h

@[simp]
lemma ne_succAbove (p : Fin (n + 1)) (i : Fin n) : p ≠ p.succAbove i := (succAbove_ne _ _).symm

/-- Given a fixed pivot `p : Fin (n + 1)`, `p.succAbove` is injective. -/
lemma succAbove_right_injective : Injective p.succAbove := by
  rintro i j hij
  unfold succAbove at hij
  split_ifs at hij with hi hj hj
  · exact castSucc_injective _ hij
  · rw [hij] at hi
    cases hj <| Nat.lt_trans j.castSucc_lt_succ hi
  · rw [← hij] at hj
    cases hi <| Nat.lt_trans i.castSucc_lt_succ hj
  · exact succ_injective _ hij

/-- Given a fixed pivot `p : Fin (n + 1)`, `p.succAbove` is injective. -/
lemma succAbove_right_inj : p.succAbove i = p.succAbove j ↔ i = j :=
  succAbove_right_injective.eq_iff

@[simp]
lemma succAbove_ne_zero_zero [NeZero n] {a : Fin (n + 1)} (ha : a ≠ 0) : a.succAbove 0 = 0 := by
  rw [Fin.succAbove_of_castSucc_lt]
  · exact castSucc_zero'
  · exact Fin.pos_iff_ne_zero.2 ha

lemma succAbove_eq_zero_iff [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) :
    a.succAbove b = 0 ↔ b = 0 := by
  rw [← succAbove_ne_zero_zero ha, succAbove_right_inj]

lemma succAbove_ne_zero [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.succAbove b ≠ 0 := mt (succAbove_eq_zero_iff ha).mp hb

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp] lemma succAbove_zero : succAbove (0 : Fin (n + 1)) = Fin.succ := rfl

lemma succAbove_zero_apply (i : Fin n) : succAbove 0 i = succ i := by rw [succAbove_zero]

@[simp] lemma succAbove_ne_last_last {a : Fin (n + 2)} (h : a ≠ last (n + 1)) :
    a.succAbove (last n) = last (n + 1) := by
  rw [succAbove_of_lt_succ _ _ (succ_last _ ▸ lt_last_iff_ne_last.2 h), succ_last]

lemma succAbove_eq_last_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last _) :
    a.succAbove b = last _ ↔ b = last _ := by
  rw [← succAbove_ne_last_last ha, succAbove_right_inj]

lemma succAbove_ne_last {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last _) (hb : b ≠ last _) :
    a.succAbove b ≠ last _ := mt (succAbove_eq_last_iff ha).mp hb

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around `last n` embeds by `castSucc`. -/
@[simp] lemma succAbove_last : succAbove (last n) = castSucc := by
  ext; simp only [succAbove_of_castSucc_lt, castSucc_lt_last]

lemma succAbove_last_apply (i : Fin n) : succAbove (last n) i = castSucc i := by rw [succAbove_last]

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
lemma succAbove_lt_iff_castSucc_lt (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ castSucc i < p := by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rwa [iff_true_right H, succAbove_of_castSucc_lt _ _ H]
  · rw [castSucc_lt_iff_succ_le, iff_false_right (Fin.not_le.2 H), succAbove_of_lt_succ _ _ H]
    exact Fin.not_lt.2 <| Fin.le_of_lt H

lemma succAbove_lt_iff_succ_le (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ succ i ≤ p := by
  rw [succAbove_lt_iff_castSucc_lt, castSucc_lt_iff_succ_le]

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
lemma lt_succAbove_iff_le_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p ≤ castSucc i := by
  rcases castSucc_lt_or_lt_succ p i with H | H
  · rw [iff_false_right (Fin.not_le.2 H), succAbove_of_castSucc_lt _ _ H]
    exact Fin.not_lt.2 <| Fin.le_of_lt H
  · rwa [succAbove_of_lt_succ _ _ H, iff_true_left H, le_castSucc_iff]

lemma lt_succAbove_iff_lt_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p < succ i := by rw [lt_succAbove_iff_le_castSucc, le_castSucc_iff]

/-- Embedding a positive `Fin n` results in a positive `Fin (n + 1)` -/
lemma succAbove_pos [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i) : 0 < p.succAbove i := by
  by_cases H : castSucc i < p
  · simpa [succAbove_of_castSucc_lt _ _ H] using castSucc_pos' h
  · simp [succAbove_of_le_castSucc _ _ (Fin.not_lt.1 H)]

lemma castPred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : castSucc x < y)
    (h' := Fin.ne_last_of_lt <| (succAbove_lt_iff_castSucc_lt ..).2 h) :
    (y.succAbove x).castPred h' = x := by
  rw [castPred_eq_iff_eq_castSucc, succAbove_of_castSucc_lt _ _ h]

lemma pred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : y ≤ castSucc x)
    (h' := Fin.ne_zero_of_lt <| (lt_succAbove_iff_le_castSucc ..).2 h) :
    (y.succAbove x).pred h' = x := by simp only [succAbove_of_le_castSucc _ _ h, pred_succ]

lemma exists_succAbove_eq {x y : Fin (n + 1)} (h : x ≠ y) : ∃ z, y.succAbove z = x := by
  obtain hxy | hyx := Fin.lt_or_lt_of_ne h
  exacts [⟨_, succAbove_castPred_of_lt _ _ hxy⟩, ⟨_, succAbove_pred_of_lt _ _ hyx⟩]

@[simp] lemma exists_succAbove_eq_iff {x y : Fin (n + 1)} : (∃ z, x.succAbove z = y) ↔ y ≠ x :=
  ⟨by rintro ⟨y, rfl⟩; exact succAbove_ne _ _, exists_succAbove_eq⟩

/-- The range of `p.succAbove` is everything except `p`. -/
@[simp] lemma range_succAbove (p : Fin (n + 1)) : Set.range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff

@[simp] lemma range_succ (n : ℕ) : Set.range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ := by
  rw [← succAbove_zero]; exact range_succAbove (0 : Fin (n + 1))

/-- `succAbove` is injective at the pivot -/
lemma succAbove_left_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n → Fin (n + 1) => (Set.range f)ᶜ) h

/-- `succAbove` is injective at the pivot -/
@[simp] lemma succAbove_left_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succAbove_left_injective.eq_iff

@[simp] lemma zero_succAbove {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)).succAbove i = i.succ := rfl

lemma succ_succAbove_zero {n : ℕ} [NeZero n] (i : Fin n) : succAbove i.succ 0 = 0 := by simp

/-- `succ` commutes with `succAbove`. -/
@[simp] lemma succ_succAbove_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.succ.succAbove j.succ = (i.succAbove j).succ := by
  obtain h | h := i.lt_or_ge (succ j)
  · rw [succAbove_of_lt_succ _ _ h, succAbove_succ_of_lt _ _ h]
  · rwa [succAbove_of_castSucc_lt _ _ h, succAbove_succ_of_le, succ_castSucc]

/-- `castSucc` commutes with `succAbove`. -/
@[simp]
lemma castSucc_succAbove_castSucc {n : ℕ} {i : Fin (n + 1)} {j : Fin n} :
    i.castSucc.succAbove j.castSucc = (i.succAbove j).castSucc := by
  rcases i.le_or_gt (castSucc j) with (h | h)
  · rw [succAbove_of_le_castSucc _ _ h, succAbove_castSucc_of_le _ _ h, succ_castSucc]
  · rw [succAbove_of_castSucc_lt _ _ h, succAbove_castSucc_of_lt _ _ h]

/-- `pred` commutes with `succAbove`. -/
lemma pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succAbove_ne_zero ha hb) :
    (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  simp_rw [← succ_inj (b := pred (succAbove a b) hk), ← succ_succAbove_succ, succ_pred]

/-- `castPred` commutes with `succAbove`. -/
lemma castPred_succAbove_castPred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last (n + 1))
    (hb : b ≠ last n) (hk := succAbove_ne_last ha hb) :
    (a.castPred ha).succAbove (b.castPred hb) = (a.succAbove b).castPred hk := by
  simp_rw [← castSucc_inj (b := (a.succAbove b).castPred hk), ← castSucc_succAbove_castSucc,
    castSucc_castPred]

lemma one_succAbove_zero {n : ℕ} : (1 : Fin (n + 2)).succAbove 0 = 0 := by
  rfl

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succAbove_zero` or `succ_succAbove_zero`. -/
@[simp] lemma succ_succAbove_one {n : ℕ} [NeZero n] (i : Fin (n + 1)) :
    i.succ.succAbove 1 = (i.succAbove 0).succ := by
  rw [← succ_zero_eq_one']; convert succ_succAbove_succ i 0

@[simp] lemma one_succAbove_succ {n : ℕ} (j : Fin n) :
    (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ := by
  have := succ_succAbove_succ 0 j; rwa [succ_zero_eq_one, zero_succAbove] at this

@[simp] lemma one_succAbove_one {n : ℕ} : (1 : Fin (n + 3)).succAbove 1 = 2 := by
  simpa only [succ_zero_eq_one, val_zero, zero_succAbove, succ_one_eq_two]
    using succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 1))

end SuccAbove

section PredAbove

/-- `predAbove p i` surjects `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i
  then pred i (Fin.ne_zero_of_lt h)
  else castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt (Fin.not_lt.1 h) (castSucc_lt_last _))

lemma predAbove_of_le_castSucc (p : Fin n) (i : Fin (n + 1)) (h : i ≤ castSucc p) :
    p.predAbove i = i.castPred (Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| castSucc_lt_last _) :=
  dif_neg <| Fin.not_lt.2 h

lemma predAbove_of_lt_succ (p : Fin n) (i : Fin (n + 1)) (h : i < succ p) :
    p.predAbove i = i.castPred (Fin.ne_last_of_lt h) :=
  predAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

lemma predAbove_of_castSucc_lt (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i) :
    p.predAbove i = i.pred (Fin.ne_zero_of_lt h) := dif_pos h

lemma predAbove_of_succ_le (p : Fin n) (i : Fin (n + 1)) (h : succ p ≤ i) :
    p.predAbove i = i.pred (Fin.ne_of_gt <| Fin.lt_of_lt_of_le (succ_pos _) h) :=
  predAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

lemma predAbove_succ_of_lt (p i : Fin n) (h : i < p) :
    p.predAbove (succ i) = (i.succ).castPred (succ_ne_last_of_lt h) := by
  rw [predAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)]

lemma predAbove_succ_of_le (p i : Fin n) (h : p ≤ i) : p.predAbove (succ i) = i := by
  rw [predAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h), pred_succ]

@[simp] lemma predAbove_succ_self (p : Fin n) : p.predAbove (succ p) = p :=
  predAbove_succ_of_le _ _ Fin.le_rfl

lemma predAbove_castSucc_of_lt (p i : Fin n) (h : p < i) :
    p.predAbove (castSucc i) = i.castSucc.pred (castSucc_ne_zero_of_lt h) := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)]

lemma predAbove_castSucc_of_le (p i : Fin n) (h : i ≤ p) : p.predAbove (castSucc i) = i := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr h), castPred_castSucc]

@[simp] lemma predAbove_castSucc_self (p : Fin n) : p.predAbove (castSucc p) = p :=
  predAbove_castSucc_of_le _ _ Fin.le_rfl

lemma predAbove_pred_of_lt (p i : Fin (n + 1)) (h : i < p) :
    (pred p (Fin.ne_zero_of_lt h)).predAbove i = castPred i (Fin.ne_last_of_lt h) := by
  rw [predAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]

lemma predAbove_pred_of_le (p i : Fin (n + 1)) (h : p ≤ i) (hp : p ≠ 0) :
    (pred p hp).predAbove i =
      pred i (Fin.ne_of_gt <| Fin.lt_of_lt_of_le (Fin.pos_iff_ne_zero.2 hp) h) := by
  rw [predAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)]

lemma predAbove_pred_self (p : Fin (n + 1)) (hp : p ≠ 0) : (pred p hp).predAbove p = pred p hp :=
  predAbove_pred_of_le _ _ Fin.le_rfl hp

lemma predAbove_castPred_of_lt (p i : Fin (n + 1)) (h : p < i) :
    (castPred p (Fin.ne_last_of_lt h)).predAbove i = pred i (Fin.ne_zero_of_lt h) := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]

lemma predAbove_castPred_of_le (p i : Fin (n + 1)) (h : i ≤ p) (hp : p ≠ last n) :
    (castPred p hp).predAbove i =
      castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| Fin.lt_last_iff_ne_last.2 hp) := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)]

lemma predAbove_castPred_self (p : Fin (n + 1)) (hp : p ≠ last n) :
    (castPred p hp).predAbove p = castPred p hp := predAbove_castPred_of_le _ _ Fin.le_rfl hp

@[simp] lemma predAbove_right_zero [NeZero n] {i : Fin n} : predAbove (i : Fin n) 0 = 0 := by
  cases n
  · exact i.elim0
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero]

lemma predAbove_zero_succ [NeZero n] {i : Fin n} : predAbove 0 i.succ = i := by
  rw [predAbove_succ_of_le _ _ (Fin.zero_le _)]

@[simp] lemma predAbove_zero_of_ne_zero [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    predAbove 0 i = i.pred hi := by
  obtain ⟨y, rfl⟩ := exists_succ_eq.2 hi; exact predAbove_zero_succ

lemma succ_predAbove_zero [NeZero n] {j : Fin (n + 1)} (h : j ≠ 0) : succ (predAbove 0 j) = j := by
  simp [*]

lemma predAbove_zero [NeZero n] {i : Fin (n + 1)} :
    predAbove (0 : Fin n) i = if hi : i = 0 then 0 else i.pred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_zero]
  · rw [predAbove_zero_of_ne_zero hi]

@[simp] lemma predAbove_right_last {i : Fin (n + 1)} : predAbove i (last (n + 1)) = last n := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_last _), pred_last]

lemma predAbove_last_castSucc {i : Fin (n + 1)} : predAbove (last n) (i.castSucc) = i := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr (le_last _)), castPred_castSucc]

@[simp] lemma predAbove_last_of_ne_last {i : Fin (n + 2)} (hi : i ≠ last (n + 1)) :
    predAbove (last n) i = castPred i hi := by
  rw [← exists_castSucc_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_last_castSucc

lemma predAbove_last_apply {i : Fin (n + 2)} :
    predAbove (last n) i = if hi : i = last _ then last _ else i.castPred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_last]
  · rw [predAbove_last_of_ne_last hi]

lemma predAbove_surjective {n : ℕ} (p : Fin n) :
    Function.Surjective p.predAbove := by
  intro i
  by_cases hi : i ≤ p
  · exact ⟨i.castSucc, predAbove_castSucc_of_le p i hi⟩
  · rw [Fin.not_le] at hi
    exact ⟨i.succ, predAbove_succ_of_le p i (Fin.le_of_lt hi)⟩

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
lemma succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (Fin.le_of_lt h), succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ h, succAbove_pred_of_lt _ _ h]

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p.succ` is the identity away from `p.succ`. -/
@[simp]
lemma succ_succAbove_predAbove {n : ℕ} {p : Fin n} {i : Fin (n + 1)} (h : i ≠ p.succ) :
    p.succ.succAbove (p.predAbove i) = i := by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (le_castSucc_iff.2 h),
      succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ (Fin.lt_of_le_of_lt (p.castSucc_le_succ) h),
      succAbove_pred_of_lt _ _ h]

/-- Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
lemma predAbove_succAbove (p : Fin n) (i : Fin n) : p.predAbove ((castSucc p).succAbove i) = i := by
  obtain h | h := p.le_or_gt i
  · rw [succAbove_castSucc_of_le _ _ h, predAbove_succ_of_le _ _ h]
  · rw [succAbove_castSucc_of_lt _ _ h, predAbove_castSucc_of_le _ _ <| Fin.le_of_lt h]

/-- `succ` commutes with `predAbove`. -/
@[simp] lemma succ_predAbove_succ (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h | h := Fin.le_or_gt (succ a) b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_succ_of_le _ _ h, succ_pred]
  · rw [predAbove_of_lt_succ _ _ h, predAbove_succ_of_lt _ _ h, succ_castPred_eq_castPred_succ]

/-- `castSucc` commutes with `predAbove`. -/
@[simp] lemma castSucc_predAbove_castSucc {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    a.castSucc.predAbove b.castSucc = (a.predAbove b).castSucc := by
  obtain h | h := a.castSucc.lt_or_ge b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_castSucc_of_lt _ _ h,
      castSucc_pred_eq_pred_castSucc]
  · rw [predAbove_of_le_castSucc _ _ h, predAbove_castSucc_of_le _ _ h, castSucc_castPred]

theorem predAbove_predAbove_succAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (j.predAbove i).predAbove (i.succAbove j) = j := by
  cases j.castSucc.lt_or_le i with
  | inl h =>
    rw [predAbove_of_castSucc_lt _ _ h, succAbove_of_castSucc_lt _ _ h, predAbove_of_le_castSucc,
      castPred_castSucc]
    rwa [le_castSucc_iff, succ_pred]
  | inr h =>
    rw [predAbove_of_le_castSucc _ _ h, succAbove_of_le_castSucc _ _ h, predAbove_of_castSucc_lt,
      pred_succ]
    rwa [castSucc_castPred, ← le_castSucc_iff]

theorem succAbove_succAbove_predAbove {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (i.succAbove j).succAbove (j.predAbove i) = i := by
  cases Fin.lt_or_le j.castSucc i with
  | inl h => rw [succAbove_of_castSucc_lt _ _ h, succAbove_predAbove (Fin.ne_of_gt h)]
  | inr h =>
    rw [succAbove_of_le_castSucc _ _ h,
      succ_succAbove_predAbove (Fin.ne_of_lt <| le_castSucc_iff.mp h)]

/-- Given `i : Fin (n + 2)` and `j : Fin (n + 1)`,
there are two ways to represent the order embedding `Fin n → Fin (n + 2)`
leaving holes at `i` and `i.succAbove j`.

One is `i.succAbove ∘ j.succAbove`.
It corresponds to embedding `Fin n` to `Fin (n + 1)` leaving a hole at `j`,
then embedding the result to `Fin (n + 2)` leaving a hole at `i`.
The other one is `(i.succAbove j).succAbove ∘ (j.predAbove i).succAbove`.
It corresponds to swapping the roles of `i` and `j`.

This lemma says that these two ways are equal.
It is used in `Fin.removeNth_removeNth_eq_swap`
to show that two ways of removing 2 elements from a sequence give the same answer.
-/
theorem succAbove_succAbove_succAbove_predAbove {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (k : Fin n) :
    (i.succAbove j).succAbove ((j.predAbove i).succAbove k) = i.succAbove (j.succAbove k) := by
  /- While it is possible to give a "morally correct" proof
  by saying that both functions are strictly monotone and have the same range `{i, i.succAbove j}ᶜ`,
  we give a direct proof by case analysis to avoid extra dependencies. -/
  ext
  simp? [succAbove, predAbove, lt_def, apply_dite Fin.val, apply_ite Fin.val] says
    simp only [succAbove, predAbove, lt_def, coe_castSucc, apply_dite Fin.val, coe_pred,
      coe_castPred, dite_eq_ite, apply_ite Fin.val, val_succ]
  split_ifs <;> omega

end PredAbove

section DivMod

/-- Compute `i / n`, where `n` is a `Nat` and inferred the type of `i`. -/
def divNat (i : Fin (m * n)) : Fin m :=
  ⟨i / n, Nat.div_lt_of_lt_mul <| Nat.mul_comm m n ▸ i.prop⟩

@[simp]
theorem coe_divNat (i : Fin (m * n)) : (i.divNat : ℕ) = i / n :=
  rfl

/-- Compute `i % n`, where `n` is a `Nat` and inferred the type of `i`. -/
def modNat (i : Fin (m * n)) : Fin n := ⟨i % n, Nat.mod_lt _ <| Nat.pos_of_mul_pos_left i.pos⟩

@[simp]
theorem coe_modNat (i : Fin (m * n)) : (i.modNat : ℕ) = i % n :=
  rfl

theorem modNat_rev (i : Fin (m * n)) : i.rev.modNat = i.modNat.rev := by
  ext
  have H₁ : i % n + 1 ≤ n := i.modNat.is_lt
  have H₂ : i / n < m := i.divNat.is_lt
  simp only [coe_modNat, val_rev]
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
  · omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by omega
  refine ⟨⟨k, hkb.trans b.is_lt⟩, hkb, by fin_omega, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

lemma pos_of_ne_zero {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) :
    0 < a :=
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
