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

#align_import data.fin.basic from "leanprover-community/mathlib"@"3a2b5524a138b5d0b818b858b516d4ac8a484b03"

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

universe u v

open Fin Nat Function

/-- Elimination principle for the empty set `Fin 0`, dependent version. -/
def finZeroElim {α : Fin 0 → Sort*} (x : Fin 0) : α x :=
  x.elim0
#align fin_zero_elim finZeroElim

namespace Fin

instance {n : ℕ} : CanLift ℕ (Fin n) Fin.val (· < n) where
  prf k hk := ⟨⟨k, hk⟩, rfl⟩

/-- A dependent variant of `Fin.elim0`. -/
def rec0 {α : Fin 0 → Sort*} (i : Fin 0) : α i := absurd i.2 (Nat.not_lt_zero _)

#align fin.elim0' Fin.elim0

variable {n m : ℕ}
--variable {a b : Fin n} -- this *really* breaks stuff

#align fin.fin_to_nat Fin.coeToNat

theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_val_eq n
#align fin.val_injective Fin.val_injective

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
lemma size_positive : Fin n → 0 < n := Fin.pos

lemma size_positive' [Nonempty (Fin n)] : 0 < n :=
  ‹Nonempty (Fin n)›.elim Fin.pos

protected theorem prop (a : Fin n) : a.val < n :=
  a.2
#align fin.prop Fin.prop

#align fin.is_lt Fin.is_lt
#align fin.pos Fin.pos
#align fin.pos_iff_nonempty Fin.pos_iff_nonempty

/-- Equivalence between `Fin n` and `{ i // i < n }`. -/
@[simps apply symm_apply]
def equivSubtype : Fin n ≃ { i // i < n } where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
#align fin.equiv_subtype Fin.equivSubtype
#align fin.equiv_subtype_symm_apply Fin.equivSubtype_symm_apply
#align fin.equiv_subtype_apply Fin.equivSubtype_apply

section coe

/-!
### coercions and constructions
-/

#align fin.eta Fin.eta
#align fin.ext Fin.ext
#align fin.ext_iff Fin.ext_iff
#align fin.coe_injective Fin.val_injective

theorem val_eq_val (a b : Fin n) : (a : ℕ) = b ↔ a = b :=
  ext_iff.symm
#align fin.coe_eq_coe Fin.val_eq_val

@[deprecated ext_iff] -- 2024-02-20
theorem eq_iff_veq (a b : Fin n) : a = b ↔ a.1 = b.1 :=
  ext_iff
#align fin.eq_iff_veq Fin.eq_iff_veq

theorem ne_iff_vne (a b : Fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
  ext_iff.not
#align fin.ne_iff_vne Fin.ne_iff_vne

-- Porting note: I'm not sure if this comment still applies.
-- built-in reduction doesn't always work
@[simp, nolint simpNF]
theorem mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a' :=
  ext_iff
#align fin.mk_eq_mk Fin.mk_eq_mk

#align fin.mk.inj_iff Fin.mk.inj_iff
#align fin.mk_val Fin.val_mk
#align fin.eq_mk_iff_coe_eq Fin.eq_mk_iff_val_eq
#align fin.coe_mk Fin.val_mk
#align fin.mk_coe Fin.mk_val

-- syntactic tautologies now
#noalign fin.coe_eq_val
#noalign fin.val_eq_coe

/-- Assume `k = l`. If two functions defined on `Fin k` and `Fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected theorem heq_fun_iff {α : Sort*} {k l : ℕ} (h : k = l) {f : Fin k → α} {g : Fin l → α} :
    HEq f g ↔ ∀ i : Fin k, f i = g ⟨(i : ℕ), h ▸ i.2⟩ := by
  subst h
  simp [Function.funext_iff]
#align fin.heq_fun_iff Fin.heq_fun_iff

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
#align fin.heq_ext_iff Fin.heq_ext_iff

#align fin.exists_iff Fin.exists_iff
#align fin.forall_iff Fin.forall_iff

end coe

section Order

/-!
### order
-/


#align fin.is_le Fin.is_le
#align fin.is_le' Fin.is_le'

#align fin.lt_iff_coe_lt_coe Fin.lt_iff_val_lt_val

theorem le_iff_val_le_val {a b : Fin n} : a ≤ b ↔ (a : ℕ) ≤ b :=
  Iff.rfl
#align fin.le_iff_coe_le_coe Fin.le_iff_val_le_val

#align fin.mk_lt_of_lt_coe Fin.mk_lt_of_lt_val
#align fin.mk_le_of_le_coe Fin.mk_le_of_le_val

/-- `a < b` as natural numbers if and only if `a < b` in `Fin n`. -/
@[norm_cast, simp]
theorem val_fin_lt {n : ℕ} {a b : Fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
  Iff.rfl
#align fin.coe_fin_lt Fin.val_fin_lt

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `Fin n`. -/
@[norm_cast, simp]
theorem val_fin_le {n : ℕ} {a b : Fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
  Iff.rfl
#align fin.coe_fin_le Fin.val_fin_le

#align fin.mk_le_mk Fin.mk_le_mk
#align fin.mk_lt_mk Fin.mk_lt_mk

-- @[simp] -- Porting note (#10618): simp can prove this
theorem min_val {a : Fin n} : min (a : ℕ) n = a := by simp
#align fin.min_coe Fin.min_val

-- @[simp] -- Porting note (#10618): simp can prove this
theorem max_val {a : Fin n} : max (a : ℕ) n = n := by simp
#align fin.max_coe Fin.max_val

/-- The inclusion map `Fin n → ℕ` is an embedding. -/
@[simps apply]
def valEmbedding : Fin n ↪ ℕ :=
  ⟨val, val_injective⟩
#align fin.coe_embedding Fin.valEmbedding

@[simp]
theorem equivSubtype_symm_trans_valEmbedding :
    equivSubtype.symm.toEmbedding.trans valEmbedding = Embedding.subtype (· < n) :=
  rfl
#align fin.equiv_subtype_symm_trans_val_embedding Fin.equivSubtype_symm_trans_valEmbedding

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
#align fin.of_nat' Fin.ofNat''ₓ
-- Porting note: `Fin.ofNat'` conflicts with something in core (there the hypothesis is `n > 0`),
-- so for now we make this double-prime `''`. This is also the reason for the dubious translation.

instance {n : ℕ} [NeZero n] : Zero (Fin n) := ⟨ofNat'' 0⟩
instance {n : ℕ} [NeZero n] : One (Fin n) := ⟨ofNat'' 1⟩

#align fin.coe_zero Fin.val_zero

/--
The `Fin.val_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem val_zero' (n : ℕ) [NeZero n] : ((0 : Fin n) : ℕ) = 0 :=
  rfl
#align fin.val_zero' Fin.val_zero'

#align fin.mk_zero Fin.mk_zero

/--
The `Fin.zero_le` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
protected theorem zero_le' [NeZero n] (a : Fin n) : 0 ≤ a :=
  Nat.zero_le a.val
#align fin.zero_le Fin.zero_le'

#align fin.zero_lt_one Fin.zero_lt_one
#align fin.not_lt_zero Fin.not_lt_zero

/--
The `Fin.pos_iff_ne_zero` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem pos_iff_ne_zero' [NeZero n] (a : Fin n) : 0 < a ↔ a ≠ 0 := by
  rw [← val_fin_lt, val_zero', Nat.pos_iff_ne_zero, Ne, Ne, ext_iff, val_zero']
#align fin.pos_iff_ne_zero Fin.pos_iff_ne_zero'

#align fin.eq_zero_or_eq_succ Fin.eq_zero_or_eq_succ
#align fin.eq_succ_of_ne_zero Fin.eq_succ_of_ne_zero

@[simp] lemma cast_eq_self (a : Fin n) : cast rfl a = a := rfl

theorem rev_involutive : Involutive (rev : Fin n → Fin n) := fun i =>
  ext <| by
    dsimp only [rev]
    rw [← Nat.sub_sub, Nat.sub_sub_self (Nat.add_one_le_iff.2 i.is_lt), Nat.add_sub_cancel_right]
#align fin.rev_involutive Fin.rev_involutive

/-- `Fin.rev` as an `Equiv.Perm`, the antitone involution `Fin n → Fin n` given by
`i ↦ n-(i+1)`. -/
@[simps! apply symm_apply]
def revPerm : Equiv.Perm (Fin n) :=
  Involutive.toPerm rev rev_involutive
#align fin.rev Fin.revPerm

#align fin.coe_rev Fin.val_revₓ

theorem rev_injective : Injective (@rev n) :=
  rev_involutive.injective
#align fin.rev_injective Fin.rev_injective

theorem rev_surjective : Surjective (@rev n) :=
  rev_involutive.surjective
#align fin.rev_surjective Fin.rev_surjective

theorem rev_bijective : Bijective (@rev n) :=
  rev_involutive.bijective
#align fin.rev_bijective Fin.rev_bijective

#align fin.rev_inj Fin.rev_injₓ

#align fin.rev_rev Fin.rev_revₓ

@[simp]
theorem revPerm_symm : (@revPerm n).symm = revPerm :=
  rfl
#align fin.rev_symm Fin.revPerm_symm

#align fin.rev_eq Fin.rev_eqₓ

#align fin.rev_le_rev Fin.rev_le_revₓ

#align fin.rev_lt_rev Fin.rev_lt_revₓ

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

#align fin.last Fin.last
#align fin.coe_last Fin.val_last

-- Porting note: this is now syntactically equal to `val_last`
#align fin.last_val Fin.val_last
#align fin.le_last Fin.le_last

#align fin.last_pos Fin.last_pos
#align fin.eq_last_of_not_lt Fin.eq_last_of_not_lt

theorem last_pos' [NeZero n] : 0 < last n := n.pos_of_neZero

theorem one_lt_last [NeZero n] : 1 < last (n + 1) := Nat.lt_add_left_iff_pos.2 n.pos_of_neZero

end Order

section Add

/-!
### addition, numerals, and coercion from Nat
-/

#align fin.val_one Fin.val_one
#align fin.coe_one Fin.val_one

@[simp]
theorem val_one' (n : ℕ) [NeZero n] : ((1 : Fin n) : ℕ) = 1 % n :=
  rfl
#align fin.coe_one' Fin.val_one'

-- Porting note: Delete this lemma after porting
theorem val_one'' {n : ℕ} : ((1 : Fin (n + 1)) : ℕ) = 1 % (n + 1) :=
  rfl
#align fin.one_val Fin.val_one''

#align fin.mk_one Fin.mk_one

instance nontrivial {n : ℕ} : Nontrivial (Fin (n + 2)) where
  exists_pair_ne := ⟨0, 1, (ne_iff_vne 0 1).mpr (by simp [val_one, val_zero])⟩

theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  rcases n with (_ | _ | n) <;>
  simp [← Nat.one_eq_succ_zero, Fin.nontrivial, not_nontrivial, Nat.succ_le_iff]
-- Porting note: here and in the next lemma, had to use `← Nat.one_eq_succ_zero`.
#align fin.nontrivial_iff_two_le Fin.nontrivial_iff_two_le

#align fin.subsingleton_iff_le_one Fin.subsingleton_iff_le_one

section Monoid

-- Porting note (#10618): removing `simp`, `simp` can prove it with AddCommMonoid instance
protected theorem add_zero [NeZero n] (k : Fin n) : k + 0 = k := by
  simp only [add_def, val_zero', Nat.add_zero, mod_eq_of_lt (is_lt k)]
#align fin.add_zero Fin.add_zero

-- Porting note (#10618): removing `simp`, `simp` can prove it with AddCommMonoid instance
protected theorem zero_add [NeZero n] (k : Fin n) : 0 + k = k := by
  simp [ext_iff, add_def, mod_eq_of_lt (is_lt k)]
#align fin.zero_add Fin.zero_add

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
#align fin.default_eq_zero Fin.default_eq_zero

section from_ad_hoc

@[simp] lemma ofNat'_zero {h : 0 < n} [NeZero n] : (Fin.ofNat' 0 h : Fin n) = 0 := rfl
@[simp] lemma ofNat'_one {h : 0 < n} [NeZero n] : (Fin.ofNat' 1 h : Fin n) = 1 := rfl

end from_ad_hoc

instance instNatCast [NeZero n] : NatCast (Fin n) where
  natCast n := Fin.ofNat'' n

lemma natCast_def [NeZero n] (a : ℕ) : (a : Fin n) = ⟨a % n, mod_lt _ n.pos_of_neZero⟩ := rfl

end Monoid

#align fin.val_add Fin.val_add
#align fin.coe_add Fin.val_add

theorem val_add_eq_ite {n : ℕ} (a b : Fin n) :
    (↑(a + b) : ℕ) = if n ≤ a + b then a + b - n else a + b := by
  rw [Fin.val_add, Nat.add_mod_eq_ite, Nat.mod_eq_of_lt (show ↑a < n from a.2),
    Nat.mod_eq_of_lt (show ↑b < n from b.2)]
#align fin.coe_add_eq_ite Fin.val_add_eq_ite

section deprecated
set_option linter.deprecated false

@[deprecated]
theorem val_bit0 {n : ℕ} (k : Fin n) : ((bit0 k : Fin n) : ℕ) = bit0 (k : ℕ) % n := by
  cases k
  rfl
#align fin.coe_bit0 Fin.val_bit0

@[deprecated]
theorem val_bit1 {n : ℕ} [NeZero n] (k : Fin n) :
    ((bit1 k : Fin n) : ℕ) = bit1 (k : ℕ) % n := by
  cases n;
  · cases' k with k h
    cases k
    · show _ % _ = _
      simp at h
    cases' h with _ h
  simp [bit1, Fin.val_bit0, Fin.val_add, Fin.val_one]
#align fin.coe_bit1 Fin.val_bit1

end deprecated

#align fin.coe_add_one_of_lt Fin.val_add_one_of_lt
#align fin.last_add_one Fin.last_add_one
#align fin.coe_add_one Fin.val_add_one

section Bit
set_option linter.deprecated false

@[simp, deprecated]
theorem mk_bit0 {m n : ℕ} (h : bit0 m < n) :
    (⟨bit0 m, h⟩ : Fin n) = (bit0 ⟨m, (Nat.le_add_right m m).trans_lt h⟩ : Fin _) :=
  eq_of_val_eq (Nat.mod_eq_of_lt h).symm
#align fin.mk_bit0 Fin.mk_bit0

@[simp, deprecated]
theorem mk_bit1 {m n : ℕ} [NeZero n] (h : bit1 m < n) :
    (⟨bit1 m, h⟩ : Fin n) =
      (bit1 ⟨m, (Nat.le_add_right m m).trans_lt ((m + m).lt_succ_self.trans h)⟩ : Fin _) := by
  ext
  simp only [bit1, bit0] at h
  simp only [bit1, bit0, val_add, val_one', ← Nat.add_mod, Nat.mod_eq_of_lt h]
#align fin.mk_bit1 Fin.mk_bit1

end Bit

#align fin.val_two Fin.val_two

--- Porting note: syntactically the same as the above
#align fin.coe_two Fin.val_two

section OfNatCoe

@[simp]
theorem ofNat''_eq_cast (n : ℕ) [NeZero n] (a : ℕ) : (Fin.ofNat'' a : Fin n) = a :=
  rfl
#align fin.of_nat_eq_coe Fin.ofNat''_eq_cast

@[simp] lemma val_natCast (a n : ℕ) [NeZero n] : (a : Fin n).val = a % n := rfl

-- Porting note: is this the right name for things involving `Nat.cast`?
/-- Converting an in-range number to `Fin (n + 1)` produces a result
whose value is the original number.  -/
theorem val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) : (a : Fin n).val = a :=
  Nat.mod_eq_of_lt h
#align fin.coe_val_of_lt Fin.val_cast_of_lt

/-- If `n` is non-zero, converting the value of a `Fin n` to `Fin n` results
in the same value.  -/
@[simp] theorem cast_val_eq_self {n : ℕ} [NeZero n] (a : Fin n) : (a.val : Fin n) = a :=
  ext <| val_cast_of_lt a.isLt
#align fin.coe_val_eq_self Fin.cast_val_eq_self

-- Porting note: this is syntactically the same as `val_cast_of_lt`
#align fin.coe_coe_of_lt Fin.val_cast_of_lt

-- Porting note: this is syntactically the same as `cast_val_of_lt`
#align fin.coe_coe_eq_self Fin.cast_val_eq_self

@[simp] lemma natCast_self (n : ℕ) [NeZero n] : (n : Fin n) = 0 := by ext; simp

@[simp] lemma natCast_eq_zero {a n : ℕ} [NeZero n] : (a : Fin n) = 0 ↔ n ∣ a := by
  simp [ext_iff, Nat.dvd_iff_mod_eq_zero]

@[simp]
theorem natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by ext; simp
#align fin.coe_nat_eq_last Fin.natCast_eq_last

@[deprecated (since := "2024-05-04")] alias cast_nat_eq_last := natCast_eq_last

theorem le_val_last (i : Fin (n + 1)) : i ≤ n := by
  rw [Fin.natCast_eq_last]
  exact Fin.le_last i
#align fin.le_coe_last Fin.le_val_last

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

#align fin.add_one_pos Fin.add_one_pos
#align fin.one_pos Fin.one_pos
#align fin.zero_ne_one Fin.zero_ne_one

@[simp]
theorem one_eq_zero_iff [NeZero n] : (1 : Fin n) = 0 ↔ n = 1 := by
  obtain _ | _ | n := n <;> simp [Fin.ext_iff]
#align fin.one_eq_zero_iff Fin.one_eq_zero_iff

@[simp]
theorem zero_eq_one_iff [NeZero n] : (0 : Fin n) = 1 ↔ n = 1 := by rw [eq_comm, one_eq_zero_iff]
#align fin.zero_eq_one_iff Fin.zero_eq_one_iff

end Add

section Succ

/-!
### succ and casts into larger Fin types
-/

#align fin.coe_succ Fin.val_succ
#align fin.succ_pos Fin.succ_pos

lemma succ_injective (n : ℕ) : Injective (@Fin.succ n) := fun a b ↦ by simp [ext_iff]
#align fin.succ_injective Fin.succ_injective

/-- `Fin.succ` as an `Embedding` -/
def succEmb (n : ℕ) : Fin n ↪ Fin (n + 1) where
  toFun := succ
  inj' := succ_injective _

@[simp]
theorem val_succEmb : ⇑(succEmb n) = Fin.succ := rfl

#align fin.succ_le_succ_iff Fin.succ_le_succ_iff
#align fin.succ_lt_succ_iff Fin.succ_lt_succ_iff

@[simp]
theorem exists_succ_eq {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 :=
  ⟨fun ⟨_, hy⟩ => hy ▸ succ_ne_zero _, x.cases (fun h => h.irrefl.elim) (fun _ _ => ⟨_, rfl⟩)⟩
#align fin.exists_succ_eq_iff Fin.exists_succ_eq

theorem exists_succ_eq_of_ne_zero {x : Fin (n + 1)} (h : x ≠ 0) :
    ∃ y, Fin.succ y = x := exists_succ_eq.mpr h

#align fin.succ_inj Fin.succ_inj
#align fin.succ_ne_zero Fin.succ_ne_zero

@[simp]
theorem succ_zero_eq_one' [NeZero n] : Fin.succ (0 : Fin n) = 1 := by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl
#align fin.succ_zero_eq_one Fin.succ_zero_eq_one'

theorem one_pos' [NeZero n] : (0 : Fin (n + 1)) < 1 := succ_zero_eq_one' (n := n) ▸ succ_pos _
theorem zero_ne_one' [NeZero n] : (0 : Fin (n + 1)) ≠ 1 := Fin.ne_of_lt one_pos'

#align fin.succ_zero_eq_one' Fin.succ_zero_eq_one

/--
The `Fin.succ_one_eq_two` in `Lean` only applies in `Fin (n+2)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem succ_one_eq_two' [NeZero n] : Fin.succ (1 : Fin (n + 1)) = 2 := by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl
#align fin.succ_one_eq_two Fin.succ_one_eq_two'

-- Version of `succ_one_eq_two` to be used by `dsimp`.
-- Note the `'` swapped around due to a move to std4.
#align fin.succ_one_eq_two' Fin.succ_one_eq_two

#align fin.succ_mk Fin.succ_mk
#align fin.mk_succ_pos Fin.mk_succ_pos
#align fin.one_lt_succ_succ Fin.one_lt_succ_succ
#align fin.add_one_lt_iff Fin.add_one_lt_iff
#align fin.add_one_le_iff Fin.add_one_le_iff
#align fin.last_le_iff Fin.last_le_iff
#align fin.lt_add_one_iff Fin.lt_add_one_iff

/--
The `Fin.le_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem le_zero_iff' {n : ℕ} [NeZero n] {k : Fin n} : k ≤ 0 ↔ k = 0 :=
  ⟨fun h => Fin.ext <| by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact Nat.le_refl _⟩
#align fin.le_zero_iff Fin.le_zero_iff'

#align fin.succ_succ_ne_one Fin.succ_succ_ne_one
#align fin.cast_lt Fin.castLT
#align fin.coe_cast_lt Fin.coe_castLT
#align fin.cast_lt_mk Fin.castLT_mk

-- Move to Batteries?
@[simp] theorem cast_refl {n : Nat} (h : n = n) :
    Fin.cast h = id := rfl

-- TODO: Move to Batteries
@[simp] lemma castLE_inj {hmn : m ≤ n} {a b : Fin m} : castLE hmn a = castLE hmn b ↔ a = b := by
  simp [ext_iff]

@[simp] lemma castAdd_inj {a b : Fin m} : castAdd n a = castAdd n b ↔ a = b := by simp [ext_iff]

attribute [simp] castSucc_inj

lemma castLE_injective (hmn : m ≤ n) : Injective (castLE hmn) :=
  fun a b hab ↦ ext (by have := congr_arg val hab; exact this)

lemma castAdd_injective (m n : ℕ) : Injective (@Fin.castAdd m n) := castLE_injective _

lemma castSucc_injective (n : ℕ) : Injective (@Fin.castSucc n) := castAdd_injective _ _
#align fin.cast_succ_injective Fin.castSucc_injective

/-- `Fin.castLE` as an `Embedding`, `castLEEmb h i` embeds `i` into a larger `Fin` type.  -/
@[simps! apply]
def castLEEmb (h : n ≤ m) : Fin n ↪ Fin m where
  toFun := castLE h
  inj' := castLE_injective _

@[simp, norm_cast] lemma coe_castLEEmb {m n} (hmn : m ≤ n) : castLEEmb hmn = castLE hmn := rfl

#align fin.coe_cast_le Fin.coe_castLE
#align fin.cast_le_mk Fin.castLE_mk
#align fin.cast_le_zero Fin.castLE_zero

/- The next proof can be golfed a lot using `Fintype.card`.
It is written this way to define `ENat.card` and `Nat.card` without a `Fintype` dependency
(not done yet). -/
assert_not_exists Fintype

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
#align fin.equiv_iff_eq Fin.equiv_iff_eq

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
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, Fin.ext rfl⟩⟩
#align fin.range_cast_le Fin.range_castLE

@[simp]
theorem coe_of_injective_castLE_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLE_injective h)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_castLE h]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)
#align fin.coe_of_injective_cast_le_symm Fin.coe_of_injective_castLE_symm

#align fin.cast_le_succ Fin.castLE_succ
#align fin.cast_le_cast_le Fin.castLE_castLE
#align fin.cast_le_comp_cast_le Fin.castLE_comp_castLE

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
#align fin_congr finCongr

@[simp] lemma _root_.finCongr_apply_mk (h : m = n) (k : ℕ) (hk : k < m) :
    finCongr h ⟨k, hk⟩ = ⟨k, h ▸ hk⟩ := rfl
#align fin_congr_apply_mk finCongr_apply_mk

@[simp]
lemma _root_.finCongr_refl (h : n = n := rfl) : finCongr h = Equiv.refl (Fin n) := by ext; simp

@[simp] lemma _root_.finCongr_symm (h : m = n) : (finCongr h).symm = finCongr h.symm := rfl
#align fin_congr_symm finCongr_symm

@[simp] lemma _root_.finCongr_apply_coe (h : m = n) (k : Fin m) : (finCongr h k : ℕ) = k := rfl
#align fin_congr_apply_coe finCongr_apply_coe

lemma _root_.finCongr_symm_apply_coe (h : m = n) (k : Fin n) : ((finCongr h).symm k : ℕ) = k := rfl
#align fin_congr_symm_apply_coe finCongr_symm_apply_coe

/-- While in many cases `finCongr` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
lemma _root_.finCongr_eq_equivCast (h : n = m) : finCongr h = .cast (h ▸ rfl) := by subst h; simp

#align fin.coe_cast Fin.coe_castₓ

@[simp]
theorem cast_zero {n' : ℕ} [NeZero n] {h : n = n'} : cast h (0 : Fin n) =
    by { haveI : NeZero n' := by {rw [← h]; infer_instance}; exact 0} :=
  ext rfl
#align fin.cast_zero Fin.cast_zero

#align fin.cast_last Fin.cast_lastₓ

#align fin.cast_mk Fin.cast_mkₓ

#align fin.cast_trans Fin.cast_transₓ

#align fin.cast_le_of_eq Fin.castLE_of_eq

/-- While in many cases `Fin.cast` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_eq_cast (h : n = m) : (cast h : Fin n → Fin m) = _root_.cast (h ▸ rfl) := by
  subst h
  ext
  rfl
#align fin.cast_eq_cast Fin.cast_eq_cast

/-- `Fin.castAdd` as an `Embedding`, `castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`.
See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
@[simps! apply]
def castAddEmb (m) : Fin n ↪ Fin (n + m) := castLEEmb (le_add_right n m)

#align fin.coe_cast_add Fin.coe_castAdd

#align fin.cast_add_zero Fin.castAdd_zeroₓ

#align fin.cast_add_lt Fin.castAdd_lt
#align fin.cast_add_mk Fin.castAdd_mk
#align fin.cast_add_cast_lt Fin.castAdd_castLT
#align fin.cast_lt_cast_add Fin.castLT_castAdd

#align fin.cast_add_cast Fin.castAdd_castₓ

#align fin.cast_cast_add_left Fin.cast_castAdd_leftₓ

#align fin.cast_cast_add_right Fin.cast_castAdd_rightₓ

#align fin.cast_add_cast_add Fin.castAdd_castAdd

#align fin.cast_succ_eq Fin.cast_succ_eqₓ

#align fin.succ_cast_eq Fin.succ_cast_eqₓ

/-- `Fin.castSucc` as an `Embedding`, `castSuccEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[simps! apply]
def castSuccEmb : Fin n ↪ Fin (n + 1) := castAddEmb _

@[simp, norm_cast] lemma coe_castSuccEmb : (castSuccEmb : Fin n → Fin (n + 1)) = Fin.castSucc := rfl

#align fin.coe_cast_succ Fin.coe_castSucc
#align fin.cast_succ_mk Fin.castSucc_mk

#align fin.cast_cast_succ Fin.cast_castSuccₓ

#align fin.cast_succ_lt_succ Fin.castSucc_lt_succ
#align fin.le_cast_succ_iff Fin.le_castSucc_iff
#align fin.cast_succ_lt_iff_succ_le Fin.castSucc_lt_iff_succ_le
#align fin.succ_last Fin.succ_last
#align fin.succ_eq_last_succ Fin.succ_eq_last_succ
#align fin.cast_succ_cast_lt Fin.castSucc_castLT
#align fin.cast_lt_cast_succ Fin.castLT_castSucc
#align fin.cast_succ_lt_cast_succ_iff Fin.castSucc_lt_castSucc_iff

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
#align fin.succ_above_lt_gt Fin.castSucc_lt_or_lt_succ

theorem succ_le_or_le_castSucc (p : Fin (n + 1)) (i : Fin n) : succ i ≤ p ∨ p ≤ i.castSucc := by
  rw [le_castSucc_iff, ← castSucc_lt_iff_succ_le]
  exact p.castSucc_lt_or_lt_succ i

theorem exists_castSucc_eq_of_ne_last {x : Fin (n + 1)} (h : x ≠ (last _)) :
    ∃ y, Fin.castSucc y = x := exists_castSucc_eq.mpr h

#align fin.cast_succ_inj Fin.castSucc_inj
#align fin.cast_succ_lt_last Fin.castSucc_lt_last

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
theorem castSucc_zero' [NeZero n] : castSucc (0 : Fin n) = 0 :=
  ext rfl
#align fin.cast_succ_zero Fin.castSucc_zero'
#align fin.cast_succ_one Fin.castSucc_one

/-- `castSucc i` is positive when `i` is positive.

The `Fin.castSucc_pos` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis. -/
theorem castSucc_pos' [NeZero n] {i : Fin n} (h : 0 < i) : 0 < castSucc i := by
  simpa [lt_iff_val_lt_val] using h
#align fin.cast_succ_pos Fin.castSucc_pos'

/--
The `Fin.castSucc_eq_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem castSucc_eq_zero_iff' [NeZero n] (a : Fin n) : castSucc a = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| by simp).symm
#align fin.cast_succ_eq_zero_iff Fin.castSucc_eq_zero_iff'

/--
The `Fin.castSucc_ne_zero_iff` in `Lean` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem castSucc_ne_zero_iff' [NeZero n] (a : Fin n) : castSucc a ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| castSucc_eq_zero_iff' a
#align fin.cast_succ_ne_zero_iff Fin.castSucc_ne_zero_iff

theorem castSucc_ne_zero_of_lt {p i : Fin n} (h : p < i) : castSucc i ≠ 0 := by
  cases n
  · exact i.elim0
  · rw [castSucc_ne_zero_iff', Ne, ext_iff]
    exact ((zero_le _).trans_lt h).ne'

theorem succ_ne_last_iff (a : Fin (n + 1)) : succ a ≠ last (n + 1) ↔ a ≠ last n :=
  not_iff_not.mpr <| succ_eq_last_succ a

theorem succ_ne_last_of_lt {p i : Fin n} (h : i < p) : succ i ≠ last n := by
  cases n
  · exact i.elim0
  · rw [succ_ne_last_iff, Ne, ext_iff]
    exact ((le_last _).trans_lt' h).ne

#align fin.cast_succ_fin_succ Fin.castSucc_fin_succ

@[norm_cast, simp]
theorem coe_eq_castSucc {a : Fin n} : (a : Fin (n + 1)) = castSucc a := by
  ext
  exact val_cast_of_lt (Nat.lt.step a.is_lt)
#align fin.coe_eq_cast_succ Fin.coe_eq_castSucc

theorem coe_succ_lt_iff_lt {n : ℕ} {j k : Fin n} : (j : Fin <| n + 1) < k ↔ j < k := by
  simp only [coe_eq_castSucc, castSucc_lt_castSucc_iff]

#align fin.coe_succ_eq_succ Fin.coeSucc_eq_succ

#align fin.lt_succ Fin.lt_succ

@[simp]
theorem range_castSucc {n : ℕ} : Set.range (castSucc : Fin n → Fin n.succ) =
    ({ i | (i : ℕ) < n } : Set (Fin n.succ)) := range_castLE (by omega)
#align fin.range_cast_succ Fin.range_castSucc

@[simp]
theorem coe_of_injective_castSucc_symm {n : ℕ} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)
#align fin.coe_of_injective_cast_succ_symm Fin.coe_of_injective_castSucc_symm

#align fin.succ_cast_succ Fin.succ_castSucc

/-- `Fin.addNat` as an `Embedding`, `addNatEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply]
def addNatEmb (m) : Fin n ↪ Fin (n + m) where
  toFun := (addNat · m)
  inj' a b := by simp [ext_iff]

#align fin.coe_add_nat Fin.coe_addNat
#align fin.add_nat_one Fin.addNat_one
#align fin.le_coe_add_nat Fin.le_coe_addNat
#align fin.add_nat_mk Fin.addNat_mk

#align fin.cast_add_nat_zero Fin.cast_addNat_zeroₓ

#align fin.add_nat_cast Fin.addNat_castₓ

#align fin.cast_add_nat_left Fin.cast_addNat_leftₓ

#align fin.cast_add_nat_right Fin.cast_addNat_rightₓ

/-- `Fin.natAdd` as an `Embedding`, `natAddEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply]
def natAddEmb (n) {m} : Fin m ↪ Fin (n + m) where
  toFun := natAdd n
  inj' a b := by simp [ext_iff]

#align fin.coe_nat_add Fin.coe_natAdd
#align fin.nat_add_mk Fin.natAdd_mk
#align fin.le_coe_nat_add Fin.le_coe_natAdd

#align fin.nat_add_zero Fin.natAdd_zeroₓ

#align fin.nat_add_cast Fin.natAdd_castₓ

#align fin.cast_nat_add_right Fin.cast_natAdd_rightₓ

#align fin.cast_nat_add_left Fin.cast_natAdd_leftₓ

#align fin.cast_add_nat_add Fin.castAdd_natAddₓ
#align fin.nat_add_cast_add Fin.natAdd_castAddₓ
#align fin.nat_add_nat_add Fin.natAdd_natAddₓ

#align fin.cast_nat_add_zero Fin.cast_natAdd_zeroₓ

#align fin.cast_nat_add Fin.cast_natAddₓ

#align fin.cast_add_nat Fin.cast_addNatₓ

#align fin.nat_add_last Fin.natAdd_last
#align fin.nat_add_cast_succ Fin.natAdd_castSucc

end Succ

section Pred

/-!
### pred
-/


#align fin.pred Fin.pred
#align fin.coe_pred Fin.coe_pred
#align fin.succ_pred Fin.succ_pred
#align fin.pred_succ Fin.pred_succ
#align fin.pred_eq_iff_eq_succ Fin.pred_eq_iff_eq_succ
#align fin.pred_mk_succ Fin.pred_mk_succ
#align fin.pred_mk Fin.pred_mk
#align fin.pred_le_pred_iff Fin.pred_le_pred_iff
#align fin.pred_lt_pred_iff Fin.pred_lt_pred_iff
#align fin.pred_inj Fin.pred_inj
#align fin.pred_one Fin.pred_one
#align fin.pred_add_one Fin.pred_add_one
#align fin.sub_nat Fin.subNat
#align fin.coe_sub_nat Fin.coe_subNat
#align fin.sub_nat_mk Fin.subNat_mk
#align fin.pred_cast_succ_succ Fin.pred_castSucc_succ
#align fin.add_nat_sub_nat Fin.addNat_subNat
#align fin.sub_nat_add_nat Fin.subNat_addNat

#align fin.nat_add_sub_nat_cast Fin.natAdd_subNat_castₓ

theorem pred_one' [NeZero n] (h := (zero_ne_one' (n := n)).symm) :
    Fin.pred (1 : Fin (n + 1)) h = 0 := by
  simp_rw [Fin.ext_iff, coe_pred, val_one', val_zero', Nat.sub_eq_zero_iff_le, Nat.mod_le]

theorem pred_last (h := ext_iff.not.2 last_pos'.ne') :
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
#align fin.cast_succ_pred_eq_pred_cast_succ Fin.castSucc_pred_eq_pred_castSucc

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
#align fin.cast_pred Fin.castPred

@[simp]
lemma castLT_eq_castPred (i : Fin (n + 1)) (h : i < last _) (h' := ext_iff.not.2 h.ne) :
    castLT i h = castPred i h' := rfl

@[simp]
lemma coe_castPred (i : Fin (n + 1)) (h : i ≠ last _) : (castPred i h : ℕ) = i := rfl
#align fin.coe_cast_pred Fin.coe_castPred

@[simp]
theorem castPred_castSucc {i : Fin n} (h' := ext_iff.not.2 (castSucc_lt_last i).ne) :
    castPred (castSucc i) h' = i := rfl
#align fin.cast_pred_cast_succ Fin.castPred_castSucc

@[simp]
theorem castSucc_castPred (i : Fin (n + 1)) (h : i ≠ last n) :
    castSucc (i.castPred h) = i := by
  rcases exists_castSucc_eq.mpr h with ⟨y, rfl⟩
  rw [castPred_castSucc]
#align fin.cast_succ_cast_pred Fin.castSucc_castPred

theorem castPred_eq_iff_eq_castSucc (i : Fin (n + 1)) (hi : i ≠ last _) (j : Fin n) :
    castPred i hi = j ↔ i = castSucc j :=
  ⟨fun h => by rw [← h, castSucc_castPred], fun h => by simp_rw [h, castPred_castSucc]⟩

@[simp]
theorem castPred_mk (i : ℕ) (h₁ : i < n) (h₂ := h₁.trans (Nat.lt_succ_self _))
    (h₃ : ⟨i, h₂⟩ ≠ last _ := (ne_iff_vne _ _).mpr (val_last _ ▸ h₁.ne)) :
  castPred ⟨i, h₂⟩ h₃ = ⟨i, h₁⟩ := rfl
#align fin.cast_pred_mk Fin.castPred_mk

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
  simp_rw [ext_iff, le_antisymm_iff, ← le_def, castPred_le_castPred_iff]

theorem castPred_zero' [NeZero n] (h := ext_iff.not.2 last_pos'.ne) :
    castPred (0 : Fin (n + 1)) h = 0 := rfl

theorem castPred_zero (h := ext_iff.not.2 last_pos.ne)  :
    castPred (0 : Fin (n + 2)) h = 0 := rfl
#align fin.cast_pred_zero Fin.castPred_zero

@[simp]
theorem castPred_one [NeZero n] (h := ext_iff.not.2 one_lt_last.ne) :
    castPred (1 : Fin (n + 2)) h = 1 := by
  cases n
  · exact subsingleton_one.elim _ 1
  · rfl
#align fin.cast_pred_one Fin.castPred_one

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

section DivMod

/-- Compute `i / n`, where `n` is a `Nat` and inferred the type of `i`. -/
def divNat (i : Fin (m * n)) : Fin m :=
  ⟨i / n, Nat.div_lt_of_lt_mul <| Nat.mul_comm m n ▸ i.prop⟩
#align fin.div_nat Fin.divNat

@[simp]
theorem coe_divNat (i : Fin (m * n)) : (i.divNat : ℕ) = i / n :=
  rfl
#align fin.coe_div_nat Fin.coe_divNat

/-- Compute `i % n`, where `n` is a `Nat` and inferred the type of `i`. -/
def modNat (i : Fin (m * n)) : Fin n := ⟨i % n, Nat.mod_lt _ <| Nat.pos_of_mul_pos_left i.pos⟩
#align fin.mod_nat Fin.modNat

@[simp]
theorem coe_modNat (i : Fin (m * n)) : (i.modNat : ℕ) = i % n :=
  rfl
#align fin.coe_mod_nat Fin.coe_modNat

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

#align fin.succ_rec Fin.succRec
#align fin.succ_rec_on Fin.succRecOn
#align fin.succ_rec_on_zero Fin.succRecOn_zero
#align fin.succ_rec_on_succ Fin.succRecOn_succ
#align fin.induction Fin.induction
#align fin.induction_zero Fin.induction_zero
#align fin.induction_succ Fin.induction_succ
#align fin.induction_on Fin.inductionOn
#align fin.cases Fin.cases
#align fin.cases_zero Fin.cases_zero
#align fin.cases_succ Fin.cases_succ
#align fin.cases_succ' Fin.cases_succ'
#align fin.forall_fin_succ Fin.forall_fin_succ
#align fin.exists_fin_succ Fin.exists_fin_succ
#align fin.forall_fin_one Fin.forall_fin_one
#align fin.exists_fin_one Fin.exists_fin_one
#align fin.forall_fin_two Fin.forall_fin_two
#align fin.exists_fin_two Fin.exists_fin_two
#align fin.fin_two_eq_of_eq_zero_iff Fin.fin_two_eq_of_eq_zero_iff
#align fin.reverse_induction Fin.reverseInduction
#align fin.reverse_induction_last Fin.reverseInduction_last
#align fin.reverse_induction_cast_succ Fin.reverseInduction_castSucc

#align fin.last_cases Fin.lastCases
#align fin.last_cases_last Fin.lastCases_last
#align fin.last_cases_cast_succ Fin.lastCases_castSucc

#align fin.add_cases Fin.addCases
#align fin.add_cases_left Fin.addCases_left
#align fin.add_cases_right Fin.addCases_right

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
      · obtain rfl := ext hij
        exact H _
      · exact _root_.trans (ihj hij) (H j)
#align fin.lift_fun_iff_succ Fin.liftFun_iff_succ

section AddGroup

open Nat Int

/-- Negation on `Fin n` -/
instance neg (n : ℕ) : Neg (Fin n) :=
  ⟨fun a => ⟨(n - a) % n, Nat.mod_lt _ a.pos⟩⟩

protected theorem coe_neg (a : Fin n) : ((-a : Fin n) : ℕ) = (n - a) % n :=
  rfl
#align fin.coe_neg Fin.coe_neg

#align fin.coe_sub Fin.coe_sub

theorem eq_zero (n : Fin 1) : n = 0 := Subsingleton.elim _ _
#align fin.eq_zero Fin.eq_zero

instance uniqueFinOne : Unique (Fin 1) where
  uniq _ := Subsingleton.elim _ _

@[simp]
theorem coe_fin_one (a : Fin 1) : (a : ℕ) = 0 := by simp [Subsingleton.elim a 0]
#align fin.coe_fin_one Fin.coe_fin_one

lemma eq_one_of_neq_zero (i : Fin 2) (hi : i ≠ 0) : i = 1 :=
  fin_two_eq_of_eq_zero_iff (by simpa only [one_eq_zero_iff, succ.injEq, iff_false] using hi)

@[simp]
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  · simp
  rw [Fin.coe_neg, Fin.val_one, Nat.add_one_sub_one, Nat.mod_eq_of_lt]
  constructor
#align fin.coe_neg_one Fin.coe_neg_one

theorem last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i :=
  ext <| by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]
#align fin.last_sub Fin.last_sub

theorem add_one_le_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) : a + 1 ≤ b := by
  cases' a with a ha
  cases' b with b hb
  cases n
  · simp only [Nat.zero_eq, Nat.zero_add, Nat.lt_one_iff] at ha hb
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
    simp only [Nat.zero_eq, Nat.zero_add, Nat.lt_one_iff] at ha hb
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

#align fin.coe_clamp Fin.coe_clamp

@[simp]
theorem coe_ofNat_eq_mod (m n : ℕ) [NeZero m] :
    ((n : Fin m) : ℕ) = n % m :=
  rfl
#align fin.coe_of_nat_eq_mod Fin.coe_ofNat_eq_mod

section Mul

/-!
### mul
-/

#align fin.val_mul Fin.val_mul
#align fin.coe_mul Fin.coe_mul

protected theorem mul_one' [NeZero n] (k : Fin n) : k * 1 = k := by
  cases' n with n
  · simp [eq_iff_true_of_subsingleton]
  cases n
  · simp [fin_one_eq_zero]
  simp [ext_iff, mul_def, mod_eq_of_lt (is_lt k)]
#align fin.mul_one Fin.mul_one'

#align fin.mul_comm Fin.mul_comm

protected theorem one_mul' [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by
  rw [Fin.mul_comm, Fin.mul_one']
#align fin.one_mul Fin.one_mul'

protected theorem mul_zero' [NeZero n] (k : Fin n) : k * 0 = 0 := by simp [ext_iff, mul_def]
#align fin.mul_zero Fin.mul_zero'

protected theorem zero_mul' [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by
  simp [ext_iff, mul_def]
#align fin.zero_mul Fin.zero_mul'

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
#align fin.reflect Fin.toExprₓ

end Fin
