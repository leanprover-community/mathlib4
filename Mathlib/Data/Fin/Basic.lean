/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Algebra.NeZero
import Mathlib.Data.Nat.Defs
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.Common

/-!
# The finite type with `n` elements

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

### Induction principles

* `finZeroElim` : Elimination principle for the empty set `Fin 0`, generalizes `Fin.elim0`.
* `Fin.succRec` : Define `C n i` by induction on `i : Fin n` interpreted
  as `(0 : Fin (n - i)).succ.succ…`. This function has two arguments: `H0 n` defines
  `0`-th element `C (n+1) 0` of an `(n+1)`-tuple, and `Hs n i` defines `(i+1)`-st element
  of `(n+1)`-tuple based on `n`, `i`, and `i`-th element of `n`-tuple.
* `Fin.succRecOn` : same as `Fin.succRec` but `i : Fin n` is the first argument;
* `Fin.induction` : Define `C i` by induction on `i : Fin (n + 1)`, separating into the
  `Nat`-like base cases of `C 0` and `C (i.succ)`.
* `Fin.inductionOn` : same as `Fin.induction` but with `i : Fin (n + 1)` as the first argument.
* `Fin.cases` : define `f : Π i : Fin n.succ, C i` by separately handling the cases `i = 0` and
  `i = Fin.succ j`, `j : Fin n`, defined using `Fin.induction`.
* `Fin.reverseInduction`: reverse induction on `i : Fin (n + 1)`; given `C (Fin.last n)` and
  `∀ i : Fin n, C (Fin.succ i) → C (Fin.castSucc i)`, constructs all values `C i` by going down;
* `Fin.lastCases`: define `f : Π i, Fin (n + 1), C i` by separately handling the cases
  `i = Fin.last n` and `i = Fin.castSucc j`, a special case of `Fin.reverseInduction`;
* `Fin.addCases`: define a function on `Fin (m + n)` by separately handling the cases
  `Fin.castAdd n i` and `Fin.natAdd m i`;
* `Fin.succAboveCases`: given `i : Fin (n + 1)`, define a function on `Fin (n + 1)` by separately
  handling the cases `j = i` and `j = Fin.succAbove i k`, same as `Fin.insertNth` but marked
  as eliminator and works for `Sort*`. -- Porting note: this is in another file

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

* `Fin.ofNat'`: given a positive number `n` (deduced from `[NeZero n]`), `Fin.ofNat' i` is
  `i % n` interpreted as an element of `Fin n`;
* `Fin.divNat i` : divides `i : Fin (m * n)` by `n`;
* `Fin.modNat i` : takes the mod of `i : Fin (m * n)` by `n`;

### Misc definitions

* `Fin.revPerm : Equiv.Perm (Fin n)` : `Fin.rev` as an `Equiv.Perm`, the antitone involution given
  by `i ↦ n-(i+1)`
-/

assert_not_exists Monoid
assert_not_exists Fintype
universe u v

open Fin Nat Function

/-- Elimination principle for the empty set `Fin 0`, dependent version. -/
def finZeroElim {α : Fin 0 → Sort*} (x : Fin 0) : α x :=
  x.elim0

namespace Fin

@[deprecated (since := "2024-02-15")] alias eq_of_veq := eq_of_val_eq
@[deprecated (since := "2024-02-15")] alias veq_of_eq := val_eq_of_eq
@[deprecated (since := "2024-08-13")] alias ne_of_vne := ne_of_val_ne
@[deprecated (since := "2024-08-13")] alias vne_of_ne := val_ne_of_ne

instance {n : ℕ} : CanLift ℕ (Fin n) Fin.val (· < n) where
  prf k hk := ⟨⟨k, hk⟩, rfl⟩

/-- A dependent variant of `Fin.elim0`. -/
def rec0 {α : Fin 0 → Sort*} (i : Fin 0) : α i := absurd i.2 (Nat.not_lt_zero _)

variable {n m : ℕ}
--variable {a b : Fin n} -- this *really* breaks stuff

theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_val_eq n

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
lemma size_positive : Fin n → 0 < n := Fin.pos

lemma size_positive' [Nonempty (Fin n)] : 0 < n :=
  ‹Nonempty (Fin n)›.elim Fin.pos

protected theorem prop (a : Fin n) : a.val < n :=
  a.2

section Order
variable {a b c : Fin n}

protected lemma lt_of_le_of_lt : a ≤ b → b < c → a < c := Nat.lt_of_le_of_lt
protected lemma lt_of_lt_of_le : a < b → b ≤ c → a < c := Nat.lt_of_lt_of_le
protected lemma le_rfl : a ≤ a := Nat.le_refl _
protected lemma lt_iff_le_and_ne : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [← val_ne_iff]; exact Nat.lt_iff_le_and_ne
protected lemma lt_or_lt_of_ne (h : a ≠ b) : a < b ∨ b < a := Nat.lt_or_lt_of_ne <| val_ne_iff.2 h
protected lemma lt_or_le (a b : Fin n) : a < b ∨ b ≤ a := Nat.lt_or_ge _ _
protected lemma le_or_lt (a b : Fin n) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected lemma le_of_eq (hab : a = b) : a ≤ b := Nat.le_of_eq <| congr_arg val hab
protected lemma ge_of_eq (hab : a = b) : b ≤ a := Fin.le_of_eq hab.symm
protected lemma eq_or_lt_of_le : a ≤ b → a = b ∨ a < b := by
  rw [Fin.ext_iff]; exact Nat.eq_or_lt_of_le
protected lemma lt_or_eq_of_le : a ≤ b → a < b ∨ a = b := by
  rw [Fin.ext_iff]; exact Nat.lt_or_eq_of_le

end Order

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
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

section coe

/-!
### coercions and constructions
-/

theorem val_eq_val (a b : Fin n) : (a : ℕ) = b ↔ a = b :=
  Fin.ext_iff.symm

@[deprecated Fin.ext_iff (since := "2024-02-20")]
theorem eq_iff_veq (a b : Fin n) : a = b ↔ a.1 = b.1 :=
  Fin.ext_iff

theorem ne_iff_vne (a b : Fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
  Fin.ext_iff.not

-- Porting note: I'm not sure if this comment still applies.
-- built-in reduction doesn't always work
@[simp, nolint simpNF]
theorem mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a' :=
  Fin.ext_iff

-- syntactic tautologies now

/-- Assume `k = l`. If two functions defined on `Fin k` and `Fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected theorem heq_fun_iff {α : Sort*} {k l : ℕ} (h : k = l) {f : Fin k → α} {g : Fin l → α} :
    HEq f g ↔ ∀ i : Fin k, f i = g ⟨(i : ℕ), h ▸ i.2⟩ := by
  subst h
  simp [Function.funext_iff]

/-- Assume `k = l` and `k' = l'`.
If two functions `Fin k → Fin k' → α` and `Fin l → Fin l' → α` are equal on each pair,
then they coincide (in the heq sense). -/
protected theorem heq_fun₂_iff {α : Sort*} {k l k' l' : ℕ} (h : k = l) (h' : k' = l')
    {f : Fin k → Fin k' → α} {g : Fin l → Fin l' → α} :
    HEq f g ↔ ∀ (i : Fin k) (j : Fin k'), f i j = g ⟨(i : ℕ), h ▸ i.2⟩ ⟨(j : ℕ), h' ▸ j.2⟩ := by
  subst h
  subst h'
  simp [Function.funext_iff]

protected theorem heq_ext_iff {k l : ℕ} (h : k = l) {i : Fin k} {j : Fin l} :
    HEq i j ↔ (i : ℕ) = (j : ℕ) := by
  subst h
  simp [val_eq_val]

end coe

section Order

/-!
### order
-/

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

-- @[simp] -- Porting note (#10618): simp can prove this
theorem min_val {a : Fin n} : min (a : ℕ) n = a := by simp

-- @[simp] -- Porting note (#10618): simp can prove this
theorem max_val {a : Fin n} : max (a : ℕ) n = n := by simp

/-- The inclusion map `Fin n → ℕ` is an embedding. -/
@[simps apply]
def valEmbedding : Fin n ↪ ℕ :=
  ⟨val, val_injective⟩

@[simp]
theorem equivSubtype_symm_trans_valEmbedding :
    equivSubtype.symm.toEmbedding.trans valEmbedding = Embedding.subtype (· < n) :=
  rfl

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

/-- Given a positive `n`, `Fin.ofNat' i` is `i % n` as an element of `Fin n`. -/
def ofNat'' [NeZero n] (i : ℕ) : Fin n :=
  ⟨i % n, mod_lt _ n.pos_of_neZero⟩
-- Porting note: `Fin.ofNat'` conflicts with something in core (there the hypothesis is `n > 0`),
-- so for now we make this double-prime `''`. This is also the reason for the dubious translation.

instance {n : ℕ} [NeZero n] : Zero (Fin n) := ⟨ofNat'' 0⟩
instance {n : ℕ} [NeZero n] : One (Fin n) := ⟨ofNat'' 1⟩

/--
The `Fin.val_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem val_zero' (n : ℕ) [NeZero n] : ((0 : Fin n) : ℕ) = 0 :=
  rfl

/--
The `Fin.zero_le` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
protected theorem zero_le' [NeZero n] (a : Fin n) : 0 ≤ a :=
  Nat.zero_le a.val

/--
The `Fin.pos_iff_ne_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem pos_iff_ne_zero' [NeZero n] (a : Fin n) : 0 < a ↔ a ≠ 0 := by
  rw [← val_fin_lt, val_zero', Nat.pos_iff_ne_zero, Ne, Ne, Fin.ext_iff, val_zero']

@[simp] lemma cast_eq_self (a : Fin n) : cast rfl a = a := rfl

theorem rev_involutive : Involutive (rev : Fin n → Fin n) := rev_rev

/-- `Fin.rev` as an `Equiv.Perm`, the antitone involution `Fin n → Fin n` given by
`i ↦ n-(i+1)`. -/
@[simps! apply symm_apply]
def revPerm : Equiv.Perm (Fin n) :=
  Involutive.toPerm rev rev_involutive

theorem rev_injective : Injective (@rev n) :=
  rev_involutive.injective

theorem rev_surjective : Surjective (@rev n) :=
  rev_involutive.surjective

theorem rev_bijective : Bijective (@rev n) :=
  rev_involutive.bijective

@[simp]
theorem revPerm_symm : (@revPerm n).symm = revPerm :=
  rfl

theorem cast_rev (i : Fin n) (h : n = m) :
    cast h i.rev = (i.cast h).rev := by
  subst h; simp

theorem rev_eq_iff {i j : Fin n} : rev i = j ↔ i = rev j := by
  rw [← rev_inj, rev_rev]

theorem rev_ne_iff {i j : Fin n} : rev i ≠ j ↔ i ≠ rev j := rev_eq_iff.not

theorem rev_lt_iff {i j : Fin n} : rev i < j ↔ rev j < i := by
  rw [← rev_lt_rev, rev_rev]

theorem rev_le_iff {i j : Fin n} : rev i ≤ j ↔ rev j ≤ i := by
  rw [← rev_le_rev, rev_rev]

theorem lt_rev_iff {i j : Fin n} : i < rev j ↔ j < rev i := by
  rw [← rev_lt_rev, rev_rev]

theorem le_rev_iff {i j : Fin n} : i ≤ rev j ↔ j ≤ rev i := by
  rw [← rev_le_rev, rev_rev]

-- Porting note: this is now syntactically equal to `val_last`

@[simp] theorem val_rev_zero [NeZero n] : ((rev 0 : Fin n) : ℕ) = n.pred := rfl

theorem last_pos' [NeZero n] : 0 < last n := n.pos_of_neZero

theorem one_lt_last [NeZero n] : 1 < last (n + 1) := by
  rw [lt_iff_val_lt_val, val_one, val_last, Nat.lt_add_left_iff_pos, Nat.pos_iff_ne_zero]
  exact NeZero.ne n

end Order

section Add

/-!
### addition, numerals, and coercion from Nat
-/

@[simp]
theorem val_one' (n : ℕ) [NeZero n] : ((1 : Fin n) : ℕ) = 1 % n :=
  rfl

-- Porting note: Delete this lemma after porting
theorem val_one'' {n : ℕ} : ((1 : Fin (n + 1)) : ℕ) = 1 % (n + 1) :=
  rfl

instance nontrivial {n : ℕ} : Nontrivial (Fin (n + 2)) where
  exists_pair_ne := ⟨0, 1, (ne_iff_vne 0 1).mpr (by simp [val_one, val_zero])⟩

theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  rcases n with (_ | _ | n) <;>
  simp [Fin.nontrivial, not_nontrivial, Nat.succ_le_iff]

section Monoid

-- Porting note (#10618): removing `simp`, `simp` can prove it with AddCommMonoid instance
protected theorem add_zero [NeZero n] (k : Fin n) : k + 0 = k := by
  simp only [add_def, val_zero', Nat.add_zero, mod_eq_of_lt (is_lt k)]

-- Porting note (#10618): removing `simp`, `simp` can prove it with AddCommMonoid instance
protected theorem zero_add [NeZero n] (k : Fin n) : 0 + k = k := by
  simp [Fin.ext_iff, add_def, mod_eq_of_lt (is_lt k)]

instance {a : ℕ} [NeZero n] : OfNat (Fin n) a where
  ofNat := Fin.ofNat' a n.pos_of_neZero

instance inhabited (n : ℕ) [NeZero n] : Inhabited (Fin n) :=
  ⟨0⟩

instance inhabitedFinOneAdd (n : ℕ) : Inhabited (Fin (1 + n)) :=
  haveI : NeZero (1 + n) := by rw [Nat.add_comm]; infer_instance
  inferInstance

@[simp]
theorem default_eq_zero (n : ℕ) [NeZero n] : (default : Fin n) = 0 :=
  rfl

section from_ad_hoc

@[simp] lemma ofNat'_zero {h : 0 < n} [NeZero n] : (Fin.ofNat' 0 h : Fin n) = 0 := rfl
@[simp] lemma ofNat'_one {h : 0 < n} [NeZero n] : (Fin.ofNat' 1 h : Fin n) = 1 := rfl

end from_ad_hoc

instance instNatCast [NeZero n] : NatCast (Fin n) where
  natCast n := Fin.ofNat'' n

lemma natCast_def [NeZero n] (a : ℕ) : (a : Fin n) = ⟨a % n, mod_lt _ n.pos_of_neZero⟩ := rfl

end Monoid

theorem val_add_eq_ite {n : ℕ} (a b : Fin n) :
    (↑(a + b) : ℕ) = if n ≤ a + b then a + b - n else a + b := by
  rw [Fin.val_add, Nat.add_mod_eq_ite, Nat.mod_eq_of_lt (show ↑a < n from a.2),
    Nat.mod_eq_of_lt (show ↑b < n from b.2)]
--- Porting note: syntactically the same as the above

section OfNatCoe

@[simp]
theorem ofNat''_eq_cast (n : ℕ) [NeZero n] (a : ℕ) : (Fin.ofNat'' a : Fin n) = a :=
  rfl

@[simp] lemma val_natCast (a n : ℕ) [NeZero n] : (a : Fin n).val = a % n := rfl

@[deprecated (since := "2024-04-17")]
alias val_nat_cast := val_natCast

-- Porting note: is this the right name for things involving `Nat.cast`?
/-- Converting an in-range number to `Fin (n + 1)` produces a result
whose value is the original number. -/
theorem val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) : (a : Fin n).val = a :=
  Nat.mod_eq_of_lt h

/-- If `n` is non-zero, converting the value of a `Fin n` to `Fin n` results
in the same value. -/
@[simp] theorem cast_val_eq_self {n : ℕ} [NeZero n] (a : Fin n) : (a.val : Fin n) = a :=
  Fin.ext <| val_cast_of_lt a.isLt

-- Porting note: this is syntactically the same as `val_cast_of_lt`

-- Porting note: this is syntactically the same as `cast_val_of_lt`

@[simp] lemma natCast_self (n : ℕ) [NeZero n] : (n : Fin n) = 0 := by ext; simp

@[deprecated (since := "2024-04-17")]
alias nat_cast_self := natCast_self

@[simp] lemma natCast_eq_zero {a n : ℕ} [NeZero n] : (a : Fin n) = 0 ↔ n ∣ a := by
  simp [Fin.ext_iff, Nat.dvd_iff_mod_eq_zero]

@[deprecated (since := "2024-04-17")]
alias nat_cast_eq_zero := natCast_eq_zero

@[simp]
theorem natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by ext; simp

@[deprecated (since := "2024-05-04")] alias cast_nat_eq_last := natCast_eq_last

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

end OfNatCoe

@[simp]
theorem one_eq_zero_iff [NeZero n] : (1 : Fin n) = 0 ↔ n = 1 := by
  obtain _ | _ | n := n <;> simp [Fin.ext_iff]

@[simp]
theorem zero_eq_one_iff [NeZero n] : (0 : Fin n) = 1 ↔ n = 1 := by rw [eq_comm, one_eq_zero_iff]

end Add

section Succ

/-!
### succ and casts into larger Fin types
-/

lemma succ_injective (n : ℕ) : Injective (@Fin.succ n) := fun a b ↦ by simp [Fin.ext_iff]

/-- `Fin.succ` as an `Embedding` -/
def succEmb (n : ℕ) : Fin n ↪ Fin (n + 1) where
  toFun := succ
  inj' := succ_injective _

@[simp]
theorem val_succEmb : ⇑(succEmb n) = Fin.succ := rfl

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

-- Move to Batteries?
@[simp] theorem cast_refl {n : Nat} (h : n = n) :
    Fin.cast h = id := rfl

-- TODO: Move to Batteries
@[simp] lemma castLE_inj {hmn : m ≤ n} {a b : Fin m} : castLE hmn a = castLE hmn b ↔ a = b := by
  simp [Fin.ext_iff]

@[simp] lemma castAdd_inj {a b : Fin m} : castAdd n a = castAdd n b ↔ a = b := by simp [Fin.ext_iff]

attribute [simp] castSucc_inj

lemma castLE_injective (hmn : m ≤ n) : Injective (castLE hmn) :=
  fun _ _ hab ↦ Fin.ext (congr_arg val hab :)

lemma castAdd_injective (m n : ℕ) : Injective (@Fin.castAdd m n) := castLE_injective _

lemma castSucc_injective (n : ℕ) : Injective (@Fin.castSucc n) := castAdd_injective _ _

/-- `Fin.castLE` as an `Embedding`, `castLEEmb h i` embeds `i` into a larger `Fin` type. -/
@[simps! apply]
def castLEEmb (h : n ≤ m) : Fin n ↪ Fin m where
  toFun := castLE h
  inj' := castLE_injective _

@[simp, norm_cast] lemma coe_castLEEmb {m n} (hmn : m ≤ n) : castLEEmb hmn = castLE hmn := rfl

/- The next proof can be golfed a lot using `Fintype.card`.
It is written this way to define `ENat.card` and `Nat.card` without a `Fintype` dependency
(not done yet). -/
lemma nonempty_embedding_iff : Nonempty (Fin n ↪ Fin m) ↔ n ≤ m := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨castLEEmb h⟩⟩
  induction n generalizing m with
  | zero => exact m.zero_le
  | succ n ihn =>
    cases' h with e
    rcases exists_eq_succ_of_ne_zero (pos_iff_nonempty.2 (Nonempty.map e inferInstance)).ne'
      with ⟨m, rfl⟩
    refine Nat.succ_le_succ <| ihn ⟨?_⟩
    refine ⟨fun i ↦ (e.setValue 0 0 i.succ).pred (mt e.setValue_eq_iff.1 i.succ_ne_zero),
      fun i j h ↦ ?_⟩
    simpa only [pred_inj, EmbeddingLike.apply_eq_iff_eq, succ_inj] using h

lemma equiv_iff_eq : Nonempty (Fin m ≃ Fin n) ↔ m = n :=
  ⟨fun ⟨e⟩ ↦ le_antisymm (nonempty_embedding_iff.1 ⟨e⟩) (nonempty_embedding_iff.1 ⟨e.symm⟩),
    fun h ↦ h ▸ ⟨.refl _⟩⟩

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

theorem leftInverse_cast (eq : n = m) : LeftInverse (cast eq.symm) (cast eq) :=
  fun _ => rfl

theorem rightInverse_cast (eq : n = m) : RightInverse (cast eq.symm) (cast eq) :=
  fun _ => rfl

theorem cast_le_cast (eq : n = m) {a b : Fin n} : cast eq a ≤ cast eq b ↔ a ≤ b :=
  Iff.rfl

/-- The 'identity' equivalence between `Fin m` and `Fin n` when `m = n`. -/
@[simps]
def _root_.finCongr (eq : n = m) : Fin n ≃ Fin m where
  toFun := cast eq
  invFun := cast eq.symm
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

@[simp]
theorem cast_zero {n' : ℕ} [NeZero n] {h : n = n'} : cast h (0 : Fin n) =
    by { haveI : NeZero n' := by {rw [← h]; infer_instance}; exact 0} := rfl

/-- While in many cases `Fin.cast` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_eq_cast (h : n = m) : (cast h : Fin n → Fin m) = _root_.cast (h ▸ rfl) := by
  subst h
  ext
  rfl

/-- `Fin.castAdd` as an `Embedding`, `castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`.
See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
@[simps! apply]
def castAddEmb (m) : Fin n ↪ Fin (n + m) := castLEEmb (le_add_right n m)

/-- `Fin.castSucc` as an `Embedding`, `castSuccEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[simps! apply]
def castSuccEmb : Fin n ↪ Fin (n + 1) := castAddEmb _

@[simp, norm_cast] lemma coe_castSuccEmb : (castSuccEmb : Fin n → Fin (n + 1)) = Fin.castSucc := rfl

@[simp]
theorem castSucc_le_castSucc_iff {a b : Fin n} : castSucc a ≤ castSucc b ↔ a ≤ b := Iff.rfl
@[simp]
theorem succ_le_castSucc_iff {a b : Fin n} : succ a ≤ castSucc b ↔ a < b := by
  rw [le_castSucc_iff, succ_lt_succ_iff]
@[simp]
theorem castSucc_lt_succ_iff {a b : Fin n} : castSucc a < succ b ↔ a ≤ b := by
  rw [castSucc_lt_iff_succ_le, succ_le_succ_iff]

theorem le_of_castSucc_lt_of_succ_lt {a b : Fin (n + 1)} {i : Fin n}
    (hl : castSucc i < a) (hu : b < succ i) : b < a := by
  simp [Fin.lt_def, -val_fin_lt] at *; omega

theorem castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p < i.succ := by
  simp [Fin.lt_def, -val_fin_lt]; omega

@[deprecated (since := "2024-05-30")] alias succAbove_lt_gt := castSucc_lt_or_lt_succ

theorem succ_le_or_le_castSucc (p : Fin (n + 1)) (i : Fin n) : succ i ≤ p ∨ p ≤ i.castSucc := by
  rw [le_castSucc_iff, ← castSucc_lt_iff_succ_le]
  exact p.castSucc_lt_or_lt_succ i

theorem exists_castSucc_eq_of_ne_last {x : Fin (n + 1)} (h : x ≠ (last _)) :
    ∃ y, Fin.castSucc y = x := exists_castSucc_eq.mpr h

theorem forall_fin_succ' {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ (∀ i : Fin n, P i.castSucc) ∧ P (.last _) :=
  ⟨fun H => ⟨fun _ => H _, H _⟩, fun ⟨H0, H1⟩ i => Fin.lastCases H1 H0 i⟩

-- to match `Fin.eq_zero_or_eq_succ`
theorem eq_castSucc_or_eq_last {n : Nat} (i : Fin (n + 1)) :
    (∃ j : Fin n, i = j.castSucc) ∨ i = last n := i.lastCases (Or.inr rfl) (Or.inl ⟨·, rfl⟩)

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

/-- `castSucc i` is positive when `i` is positive.

The `Fin.castSucc_pos` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis. -/
theorem castSucc_pos' [NeZero n] {i : Fin n} (h : 0 < i) : 0 < castSucc i := by
  simpa [lt_iff_val_lt_val] using h

/--
The `Fin.castSucc_eq_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem castSucc_eq_zero_iff' [NeZero n] (a : Fin n) : castSucc a = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| by simp).symm

/--
The `Fin.castSucc_ne_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem castSucc_ne_zero_iff' [NeZero n] (a : Fin n) : castSucc a ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| castSucc_eq_zero_iff' a

theorem castSucc_ne_zero_of_lt {p i : Fin n} (h : p < i) : castSucc i ≠ 0 := by
  cases n
  · exact i.elim0
  · rw [castSucc_ne_zero_iff', Ne, Fin.ext_iff]
    exact ((zero_le _).trans_lt h).ne'

theorem succ_ne_last_iff (a : Fin (n + 1)) : succ a ≠ last (n + 1) ↔ a ≠ last n :=
  not_iff_not.mpr <| succ_eq_last_succ a

theorem succ_ne_last_of_lt {p i : Fin n} (h : i < p) : succ i ≠ last n := by
  cases n
  · exact i.elim0
  · rw [succ_ne_last_iff, Ne, Fin.ext_iff]
    exact ((le_last _).trans_lt' h).ne

@[norm_cast, simp]
theorem coe_eq_castSucc {a : Fin n} : (a : Fin (n + 1)) = castSucc a := by
  ext
  exact val_cast_of_lt (Nat.lt.step a.is_lt)

theorem coe_succ_lt_iff_lt {n : ℕ} {j k : Fin n} : (j : Fin <| n + 1) < k ↔ j < k := by
  simp only [coe_eq_castSucc, castSucc_lt_castSucc_iff]

@[simp]
theorem range_castSucc {n : ℕ} : Set.range (castSucc : Fin n → Fin n.succ) =
    ({ i | (i : ℕ) < n } : Set (Fin n.succ)) := range_castLE (by omega)

@[simp]
theorem coe_of_injective_castSucc_symm {n : ℕ} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)

/-- `Fin.addNat` as an `Embedding`, `addNatEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply]
def addNatEmb (m) : Fin n ↪ Fin (n + m) where
  toFun := (addNat · m)
  inj' a b := by simp [Fin.ext_iff]

/-- `Fin.natAdd` as an `Embedding`, `natAddEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply]
def natAddEmb (n) {m} : Fin m ↪ Fin (n + m) where
  toFun := natAdd n
  inj' a b := by simp [Fin.ext_iff]

end Succ

section Pred

/-!
### pred
-/

theorem pred_one' [NeZero n] (h := (zero_ne_one' (n := n)).symm) :
    Fin.pred (1 : Fin (n + 1)) h = 0 := by
  simp_rw [Fin.ext_iff, coe_pred, val_one', val_zero', Nat.sub_eq_zero_iff_le, Nat.mod_le]

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

theorem castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a ≠ 0)
    (ha' := a.castSucc_ne_zero_iff.mpr ha) :
    (a.pred ha).castSucc = (castSucc a).pred ha' := rfl

theorem castSucc_pred_add_one_eq {a : Fin (n + 1)} (ha : a ≠ 0) :
    (a.pred ha).castSucc + 1 = a := by
  cases' a using cases with a
  · exact (ha rfl).elim
  · rw [pred_succ, coeSucc_eq_succ]

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

theorem castPred_le_castPred_iff {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi ≤ castPred j hj ↔ i ≤ j := Iff.rfl

theorem castPred_lt_castPred_iff {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi < castPred j hj ↔ i < j := Iff.rfl

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

theorem castPred_inj {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi = castPred j hj ↔ i = j := by
  simp_rw [Fin.ext_iff, le_antisymm_iff, ← le_def, castPred_le_castPred_iff]

theorem castPred_zero' [NeZero n] (h := Fin.ext_iff.not.2 last_pos'.ne) :
    castPred (0 : Fin (n + 1)) h = 0 := rfl

theorem castPred_zero (h := Fin.ext_iff.not.2 last_pos.ne)  :
    castPred (0 : Fin (n + 2)) h = 0 := rfl

@[simp]
theorem castPred_one [NeZero n] (h := Fin.ext_iff.not.2 one_lt_last.ne) :
    castPred (1 : Fin (n + 2)) h = 1 := by
  cases n
  · exact subsingleton_one.elim _ 1
  · rfl

theorem rev_pred {i : Fin (n + 1)} (h : i ≠ 0) (h' := rev_ne_iff.mpr ((rev_last _).symm ▸ h)) :
    rev (pred i h) = castPred (rev i) h' := by
  rw [← castSucc_inj, castSucc_castPred, ← rev_succ, succ_pred]

theorem rev_castPred {i : Fin (n + 1)}
    (h : i ≠ last n) (h' := rev_ne_iff.mpr ((rev_zero _).symm ▸ h)) :
    rev (castPred i h) = pred (rev i) h' := by
  rw [← succ_inj, succ_pred, ← rev_castSucc, castSucc_castPred]

theorem succ_castPred_eq_castPred_succ {a : Fin (n + 1)} (ha : a ≠ last n)
    (ha' := a.succ_ne_last_iff.mpr ha) :
    (a.castPred ha).succ = (succ a).castPred ha' := rfl

theorem succ_castPred_eq_add_one {a : Fin (n + 1)} (ha : a ≠ last n) :
    (a.castPred ha).succ = a + 1 := by
  cases' a using lastCases with a
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

lemma succAbove_pred_of_lt (p i : Fin (n + 1)) (h : p < i)
    (hi := Fin.ne_of_gt <| Fin.lt_of_le_of_lt p.zero_le h) : succAbove p (i.pred hi) = i := by
  rw [succAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h), succ_pred]

lemma succAbove_pred_of_le (p i : Fin (n + 1)) (h : i ≤ p) (hi : i ≠ 0) :
    succAbove p (i.pred hi) = (i.pred hi).castSucc := succAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)

@[simp] lemma succAbove_pred_self (p : Fin (n + 1)) (h : p ≠ 0) :
    succAbove p (p.pred h) = (p.pred h).castSucc := succAbove_pred_of_le _ _ Fin.le_rfl h

lemma succAbove_castPred_of_lt (p i : Fin (n + 1)) (h : i < p)
    (hi := Fin.ne_of_lt <| Nat.lt_of_lt_of_le h p.le_last) : succAbove p (i.castPred hi) = i := by
  rw [succAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h), castSucc_castPred]

lemma succAbove_castPred_of_le (p i : Fin (n + 1)) (h : p ≤ i) (hi : i ≠ last n) :
    succAbove p (i.castPred hi) = (i.castPred hi).succ :=
  succAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)

lemma succAbove_castPred_self (p : Fin (n + 1)) (h : p ≠ last n) :
    succAbove p (p.castPred h) = (p.castPred h).succ := succAbove_castPred_of_le _ _ Fin.le_rfl h

lemma succAbove_rev_left (p : Fin (n + 1)) (i : Fin n) :
    p.rev.succAbove i = (p.succAbove i.rev).rev := by
  obtain h | h := (rev p).succ_le_or_le_castSucc i
  · rw [succAbove_of_succ_le _ _ h,
      succAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), rev_succ, rev_rev]
  · rw [succAbove_of_le_castSucc _ _ h,
      succAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), rev_castSucc, rev_rev]

lemma succAbove_rev_right (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i.rev = (p.rev.succAbove i).rev := by rw [succAbove_rev_left, rev_rev]

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself -/
lemma succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  rcases p.castSucc_lt_or_lt_succ i with (h | h)
  · rw [succAbove_of_castSucc_lt _ _ h]
    exact Fin.ne_of_lt h
  · rw [succAbove_of_lt_succ _ _ h]
    exact Fin.ne_of_gt h

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

/--  `Fin.succAbove p` as an `Embedding`. -/
@[simps!]
def succAboveEmb (p : Fin (n + 1)) : Fin n ↪ Fin (n + 1) := ⟨p.succAbove, succAbove_right_injective⟩

@[simp, norm_cast] lemma coe_succAboveEmb (p : Fin (n + 1)) : p.succAboveEmb = p.succAbove := rfl

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
  simp [← succAbove_ne_last_last ha, succAbove_right_inj]

lemma succAbove_ne_last {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last _) (hb : b ≠ last _) :
    a.succAbove b ≠ last _ := mt (succAbove_eq_last_iff ha).mp hb

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around `last n` embeds by `castSucc`. -/
@[simp] lemma succAbove_last : succAbove (last n) = castSucc := by
  ext; simp only [succAbove_of_castSucc_lt, castSucc_lt_last]

lemma succAbove_last_apply (i : Fin n) : succAbove (last n) i = castSucc i := by rw [succAbove_last]

@[deprecated (since := "2024-05-30")]
lemma succAbove_lt_ge (p : Fin (n + 1)) (i : Fin n) :
    castSucc i < p ∨ p ≤ castSucc i := Nat.lt_or_ge (castSucc i) p

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
lemma succAbove_lt_iff_castSucc_lt (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ castSucc i < p := by
  cases' castSucc_lt_or_lt_succ p i with H H
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
  cases' castSucc_lt_or_lt_succ p i with H H
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

@[simp] lemma succ_succAbove_zero {n : ℕ} [NeZero n] (i : Fin n) : succAbove i.succ 0 = 0 :=
  succAbove_of_castSucc_lt i.succ 0 (by simp only [castSucc_zero', succ_pos])

/-- `succ` commutes with `succAbove`. -/
@[simp] lemma succ_succAbove_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.succ.succAbove j.succ = (i.succAbove j).succ := by
  obtain h | h := i.lt_or_le (succ j)
  · rw [succAbove_of_lt_succ _ _ h, succAbove_succ_of_lt _ _ h]
  · rwa [succAbove_of_castSucc_lt _ _ h, succAbove_succ_of_le, succ_castSucc]

/-- `castSucc` commutes with `succAbove`. -/
@[simp]
lemma castSucc_succAbove_castSucc {n : ℕ} {i : Fin (n + 1)} {j : Fin n} :
    i.castSucc.succAbove j.castSucc = (i.succAbove j).castSucc := by
  rcases i.le_or_lt (castSucc j) with (h | h)
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

/-- `rev` commutes with `succAbove`. -/
lemma rev_succAbove (p : Fin (n + 1)) (i : Fin n) :
    rev (succAbove p i) = succAbove (rev p) (rev i) := by
  rw [succAbove_rev_left, rev_rev]

--@[simp] -- Porting note: can be proved by `simp`
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
    using succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 2))

end SuccAbove

section PredAbove

/-- `predAbove p i` surjects `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i
  then pred i (Fin.ne_zero_of_lt h)
  else castPred i (Fin.ne_of_lt <| Fin.lt_of_le_of_lt (Fin.not_lt.1 h) (castSucc_lt_last _))

lemma predAbove_of_le_castSucc (p : Fin n) (i : Fin (n + 1)) (h : i ≤ castSucc p)
    (hi := Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| castSucc_lt_last _) :
    p.predAbove i = i.castPred hi := dif_neg <| Fin.not_lt.2 h

lemma predAbove_of_lt_succ (p : Fin n) (i : Fin (n + 1)) (h : i < succ p)
    (hi := Fin.ne_last_of_lt h) : p.predAbove i = i.castPred hi :=
  predAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

lemma predAbove_of_castSucc_lt (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i)
    (hi := Fin.ne_zero_of_lt h) : p.predAbove i = i.pred hi := dif_pos h

lemma predAbove_of_succ_le (p : Fin n) (i : Fin (n + 1)) (h : succ p ≤ i)
    (hi := Fin.ne_of_gt <| Fin.lt_of_lt_of_le (succ_pos _) h) :
    p.predAbove i = i.pred hi := predAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

lemma predAbove_succ_of_lt (p i : Fin n) (h : i < p) (hi := succ_ne_last_of_lt h) :
    p.predAbove (succ i) = (i.succ).castPred hi := by
  rw [predAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)]

lemma predAbove_succ_of_le (p i : Fin n) (h : p ≤ i) : p.predAbove (succ i) = i := by
  rw [predAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h), pred_succ]

@[simp] lemma predAbove_succ_self (p : Fin n) : p.predAbove (succ p) = p :=
  predAbove_succ_of_le _ _ Fin.le_rfl

lemma predAbove_castSucc_of_lt (p i : Fin n) (h : p < i) (hi := castSucc_ne_zero_of_lt h) :
    p.predAbove (castSucc i) = i.castSucc.pred hi := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.2 h)]

lemma predAbove_castSucc_of_le (p i : Fin n) (h : i ≤ p) : p.predAbove (castSucc i) = i := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr h), castPred_castSucc]

@[simp] lemma predAbove_castSucc_self (p : Fin n) : p.predAbove (castSucc p) = p :=
  predAbove_castSucc_of_le _ _ Fin.le_rfl

lemma predAbove_pred_of_lt (p i : Fin (n + 1)) (h : i < p) (hp := Fin.ne_zero_of_lt h)
    (hi := Fin.ne_last_of_lt h) : (pred p hp).predAbove i = castPred i hi := by
  rw [predAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]

lemma predAbove_pred_of_le (p i : Fin (n + 1)) (h : p ≤ i) (hp : p ≠ 0)
    (hi := Fin.ne_of_gt <| Fin.lt_of_lt_of_le (Fin.pos_iff_ne_zero.2 hp) h) :
  (pred p hp).predAbove i = pred i hi := by rw [predAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)]

lemma predAbove_pred_self (p : Fin (n + 1)) (hp : p ≠ 0) : (pred p hp).predAbove p = pred p hp :=
  predAbove_pred_of_le _ _ Fin.le_rfl hp

lemma predAbove_castPred_of_lt (p i : Fin (n + 1)) (h : p < i) (hp := Fin.ne_last_of_lt h)
  (hi := Fin.ne_zero_of_lt h) : (castPred p hp).predAbove i = pred i hi := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]

lemma predAbove_castPred_of_le (p i : Fin (n + 1)) (h : i ≤ p) (hp : p ≠ last n)
    (hi := Fin.ne_of_lt <| Fin.lt_of_le_of_lt h <| Fin.lt_last_iff_ne_last.2 hp) :
    (castPred p hp).predAbove i = castPred i hi := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)]

lemma predAbove_castPred_self (p : Fin (n + 1)) (hp : p ≠ last n) :
    (castPred p hp).predAbove p = castPred p hp := predAbove_castPred_of_le _ _ Fin.le_rfl hp

lemma predAbove_rev_left (p : Fin n) (i : Fin (n + 1)) :
    p.rev.predAbove i = (p.predAbove i.rev).rev := by
  obtain h | h := (rev i).succ_le_or_le_castSucc p
  · rw [predAbove_of_succ_le _ _ h, rev_pred,
      predAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), castPred_inj, rev_rev]
  · rw [predAbove_of_le_castSucc _ _ h, rev_castPred,
      predAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), pred_inj, rev_rev]

lemma predAbove_rev_right (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i.rev = (p.rev.predAbove i).rev := by rw [predAbove_rev_left, rev_rev]

@[simp] lemma predAbove_right_zero [NeZero n] {i : Fin n} : predAbove (i : Fin n) 0 = 0 := by
  cases n
  · exact i.elim0
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero]

@[simp] lemma predAbove_zero_succ [NeZero n] {i : Fin n} : predAbove 0 i.succ = i := by
  rw [predAbove_succ_of_le _ _ (Fin.zero_le' _)]

@[simp]
lemma succ_predAbove_zero [NeZero n] {j : Fin (n + 1)} (h : j ≠ 0) : succ (predAbove 0 j) = j := by
  rcases exists_succ_eq_of_ne_zero h with ⟨k, rfl⟩
  rw [predAbove_zero_succ]

@[simp] lemma predAbove_zero_of_ne_zero [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    predAbove 0 i = i.pred hi := by
  obtain ⟨y, rfl⟩ := exists_succ_eq.2 hi; exact predAbove_zero_succ

lemma predAbove_zero [NeZero n] {i : Fin (n + 1)} :
    predAbove (0 : Fin n) i = if hi : i = 0 then 0 else i.pred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_zero]
  · rw [predAbove_zero_of_ne_zero hi]

@[simp] lemma predAbove_right_last {i : Fin (n + 1)} : predAbove i (last (n + 1)) = last n := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_last _), pred_last]

@[simp] lemma predAbove_last_castSucc {i : Fin (n + 1)} : predAbove (last n) (i.castSucc) = i := by
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

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
lemma succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  obtain h | h := Fin.lt_or_lt_of_ne h
  · rw [predAbove_of_le_castSucc _ _ (Fin.le_of_lt h), succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ h, succAbove_pred_of_lt _ _ h]

/-- Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
lemma predAbove_succAbove (p : Fin n) (i : Fin n) : p.predAbove ((castSucc p).succAbove i) = i := by
  obtain h | h := p.le_or_lt i
  · rw [succAbove_castSucc_of_le _ _ h, predAbove_succ_of_le _ _ h]
  · rw [succAbove_castSucc_of_lt _ _ h, predAbove_castSucc_of_le _ _ <| Fin.le_of_lt h]

/-- `succ` commutes with `predAbove`. -/
@[simp] lemma succ_predAbove_succ (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h | h := Fin.le_or_lt (succ a) b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_succ_of_le _ _ h, succ_pred]
  · rw [predAbove_of_lt_succ _ _ h, predAbove_succ_of_lt _ _ h, succ_castPred_eq_castPred_succ]

/-- `castSucc` commutes with `predAbove`. -/
@[simp] lemma castSucc_predAbove_castSucc {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    a.castSucc.predAbove b.castSucc = (a.predAbove b).castSucc := by
  obtain h | h := a.castSucc.lt_or_le b
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_castSucc_of_lt _ _ h,
      castSucc_pred_eq_pred_castSucc]
  · rw [predAbove_of_le_castSucc _ _ h, predAbove_castSucc_of_le _ _ h, castSucc_castPred]

/-- `rev` commutes with `predAbove`. -/
lemma rev_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (predAbove p i).rev = predAbove p.rev i.rev := by rw [predAbove_rev_left, rev_rev]

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

theorem liftFun_iff_succ {α : Type*} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} :
    ((· < ·) ⇒ r) f f ↔ ∀ i : Fin n, r (f (castSucc i)) (f i.succ) := by
  constructor
  · intro H i
    exact H i.castSucc_lt_succ
  · refine fun H i => Fin.induction (fun h ↦ ?_) ?_
    · simp [le_def] at h
    · intro j ihj hij
      rw [← le_castSucc_iff] at hij
      obtain hij | hij := (le_def.1 hij).eq_or_lt
      · obtain rfl := Fin.ext hij
        exact H _
      · exact _root_.trans (ihj hij) (H j)

section AddGroup

open Nat Int

/-- Negation on `Fin n` -/
instance neg (n : ℕ) : Neg (Fin n) :=
  ⟨fun a => ⟨(n - a) % n, Nat.mod_lt _ a.pos⟩⟩

theorem neg_def (a : Fin n) : -a = ⟨(n - a) % n, Nat.mod_lt _ a.pos⟩ := rfl

protected theorem coe_neg (a : Fin n) : ((-a : Fin n) : ℕ) = (n - a) % n :=
  rfl

theorem eq_zero (n : Fin 1) : n = 0 := Subsingleton.elim _ _

instance uniqueFinOne : Unique (Fin 1) where
  uniq _ := Subsingleton.elim _ _

@[simp]
theorem coe_fin_one (a : Fin 1) : (a : ℕ) = 0 := by simp [Subsingleton.elim a 0]

lemma eq_one_of_neq_zero (i : Fin 2) (hi : i ≠ 0) : i = 1 :=
  fin_two_eq_of_eq_zero_iff (by simpa only [one_eq_zero_iff, succ.injEq, iff_false] using hi)

@[simp]
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  · simp
  rw [Fin.coe_neg, Fin.val_one, Nat.add_one_sub_one, Nat.mod_eq_of_lt]
  constructor

theorem last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i :=
  Fin.ext <| by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]

theorem add_one_le_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) : a + 1 ≤ b := by
  cases' a with a ha
  cases' b with b hb
  cases n
  · simp only [Nat.zero_add, Nat.lt_one_iff] at ha hb
    simp [ha, hb]
  simp only [le_iff_val_le_val, val_add, lt_iff_val_lt_val, val_mk, val_one] at h ⊢
  rwa [Nat.mod_eq_of_lt, Nat.succ_le_iff]
  rw [Nat.succ_lt_succ_iff]
  exact h.trans_le (Nat.le_of_lt_succ hb)

theorem exists_eq_add_of_le {n : ℕ} {a b : Fin n} (h : a ≤ b) : ∃ k ≤ b, b = a + k := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k := Nat.exists_eq_add_of_le h
  have hkb : k ≤ b := by omega
  refine ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, ?_⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

theorem exists_eq_add_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) :
    ∃ k < b, k + 1 ≤ b ∧ b = a + k + 1 := by
  cases n
  · cases' a with a ha
    cases' b with b hb
    simp only [Nat.zero_add, Nat.lt_one_iff] at ha hb
    simp [ha, hb] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by omega
  refine ⟨⟨k, hkb.trans b.is_lt⟩, hkb, ?_, ?_⟩
  · rw [Fin.le_iff_val_le_val, Fin.val_add_one]
    split_ifs <;> simp [Nat.succ_le_iff, hkb]
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

lemma pos_of_ne_zero {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) :
    0 < a :=
  Nat.pos_of_ne_zero (val_ne_of_ne h)

end AddGroup

@[simp]
theorem coe_ofNat_eq_mod (m n : ℕ) [NeZero m] :
    ((n : Fin m) : ℕ) = n % m :=
  rfl

section Mul

/-!
### mul
-/

protected theorem mul_one' [NeZero n] (k : Fin n) : k * 1 = k := by
  cases' n with n
  · simp [eq_iff_true_of_subsingleton]
  cases n
  · simp [fin_one_eq_zero]
  simp [Fin.ext_iff, mul_def, mod_eq_of_lt (is_lt k)]

protected theorem one_mul' [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by
  rw [Fin.mul_comm, Fin.mul_one']

protected theorem mul_zero' [NeZero n] (k : Fin n) : k * 0 = 0 := by simp [Fin.ext_iff, mul_def]

protected theorem zero_mul' [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by
  simp [Fin.ext_iff, mul_def]

end Mul

open Qq in
instance toExpr (n : ℕ) : Lean.ToExpr (Fin n) where
  toTypeExpr := q(Fin $n)
  toExpr := match n with
    | 0 => finZeroElim
    | k + 1 => fun i => show Q(Fin $n) from
      have i : Q(Nat) := Lean.mkRawNatLit i -- raw literal to avoid ofNat-double-wrapping
      have : Q(NeZero $n) := haveI : $n =Q $k + 1 := ⟨⟩; by exact q(NeZero.succ)
      q(OfNat.ofNat $i)

end Fin

set_option linter.style.longFile 1700
