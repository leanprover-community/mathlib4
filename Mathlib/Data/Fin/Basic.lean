/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek

! This file was ported from Lean 3 source module data.fin.basic
! leanprover-community/mathlib commit a59dad53320b73ef180174aae867addd707ef00e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.WithZero
import Mathlib.Order.RelIso.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Order.Hom.Set

/-!
# The finite type with `n` elements

`fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

### Induction principles

* `fin_zero_elim` : Elimination principle for the empty set `fin 0`, generalizes `fin.elim0`.
* `fin.succ_rec` : Define `C n i` by induction on  `i : fin n` interpreted
  as `(0 : fin (n - i)).succ.succ…`. This function has two arguments: `H0 n` defines
  `0`-th element `C (n+1) 0` of an `(n+1)`-tuple, and `Hs n i` defines `(i+1)`-st element
  of `(n+1)`-tuple based on `n`, `i`, and `i`-th element of `n`-tuple.
* `fin.succ_rec_on` : same as `fin.succ_rec` but `i : fin n` is the first argument;
* `fin.induction` : Define `C i` by induction on `i : fin (n + 1)`, separating into the
  `nat`-like base cases of `C 0` and `C (i.succ)`.
* `fin.induction_on` : same as `fin.induction` but with `i : fin (n + 1)` as the first argument.
* `fin.cases` : define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
  `i = fin.succ j`, `j : fin n`, defined using `fin.induction`.
* `fin.reverse_induction`: reverse induction on `i : fin (n + 1)`; given `C (fin.last n)` and
  `∀ i : fin n, C (fin.succ i) → C (fin.cast_succ i)`, constructs all values `C i` by going down;
* `fin.last_cases`: define `f : Π i, fin (n + 1), C i` by separately handling the cases
  `i = fin.last n` and `i = fin.cast_succ j`, a special case of `fin.reverse_induction`;
* `fin.add_cases`: define a function on `fin (m + n)` by separately handling the cases
  `fin.cast_add n i` and `fin.nat_add m i`;
* `fin.succAbove_cases`: given `i : fin (n + 1)`, define a function on `fin (n + 1)` by separately
  handling the cases `j = i` and `j = fin.succAbove i k`, same as `fin.insert_nth` but marked
  as eliminator and works for `Sort*`.

### Order embeddings and an order isomorphism

* `fin.order_iso_subtype` : coercion to `{ i // i < n }` as an `order_iso`;
* `fin.coe_embedding` : coercion to natural numbers as an `embedding`;
* `fin.coe_order_embedding` : coercion to natural numbers as an `order_embedding`;
* `fin.succ_embedding` : `fin.succ` as an `order_embedding`;
* `fin.cast_le h` : embed `fin n` into `fin m`, `h : n ≤ m`;
* `fin.cast eq` : order isomorphism between `fin n` and fin m` provided that `n = m`,
  see also `equiv.fin_congr`;
* `fin.cast_add m` : embed `fin n` into `fin (n+m)`;
* `fin.cast_succ` : embed `fin n` into `fin (n+1)`;
* `fin.succAbove p` : embed `fin n` into `fin (n + 1)` with a hole around `p`;
* `fin.add_nat m i` : add `m` on `i` on the right, generalizes `fin.succ`;
* `fin.nat_add n i` adds `n` on `i` on the left;

### Other casts

* `fin.of_nat'`: given a positive number `n` (deduced from `[ne_zero n]`), `fin.of_nat' i` is
  `i % n` interpreted as an element of `fin n`;
* `fin.cast_lt i h` : embed `i` into a `fin` where `h` proves it belongs into;
* `fin.pred_above (p : fin n) i` : embed `i : fin (n+1)` into `fin n` by subtracting one if `p < i`;
* `fin.cast_pred` : embed `fin (n + 2)` into `fin (n + 1)` by mapping `fin.last (n + 1)` to
  `fin.last n`;
* `fin.sub_nat i h` : subtract `m` from `i ≥ m`, generalizes `fin.pred`;
* `fin.clamp n m` : `min n m` as an element of `fin (m + 1)`;
* `fin.div_nat i` : divides `i : fin (m * n)` by `n`;
* `fin.mod_nat i` : takes the mod of `i : fin (m * n)` by `n`;

### Misc definitions

* `fin.last n` : The greatest value of `fin (n+1)`.
* `fin.rev : fin n → fin n` : the antitone involution given by `i ↦ n-(i+1)`

-/

-- set_option autoImplicit false

universe u v

open Fin Nat Function

/-- Elimination principle for the empty set `fin 0`, dependent version. -/
def finZeroElim {α : Fin 0 → Sort _} (x : Fin 0) : α x :=
  x.elim0
#align fin_zero_elim finZeroElim

namespace Fin

/-- A non-dependent variant of `elim0`. -/
def elim0' {α : Sort _} (x : Fin 0) : α :=
  x.elim0
#align fin.elim0' Fin.elim0'

variable {n m : ℕ}
--variable {a b : Fin n} -- this *really* breaks stuff

#align fin.fin_to_nat Fin.coeToNat

theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_veq n
#align fin.val_injective Fin.val_injective

section from_ad_hoc
-- porting note: the next seven lemmas aren't from mathlib3, but the `*_def` ones were in lean3 core
-- and they were in the ad hoc port of this file

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
lemma size_positive : Fin n → 0 < n
| ⟨x, h⟩ =>
  match Nat.eq_or_lt_of_le (Nat.zero_le x) with
  | Or.inl h_eq => h_eq ▸ h
  | Or.inr h_lt => Nat.lt_trans h_lt h

lemma mod_def : ∀ (a m : Fin n),
  a % m = Fin.mk ((a.val % m.val) % n) (Nat.mod_lt (a.val % m.val) (a.size_positive))
| ⟨_, _⟩, ⟨_, _⟩ => rfl

lemma add_def : ∀ (a b : Fin n),
  a + b = (Fin.mk ((a.val + b.val) % n) (Nat.mod_lt _ (a.size_positive)))
| ⟨_, _⟩, ⟨_, _⟩ => rfl

lemma mul_def : ∀ (a b : Fin n),
  a * b = (Fin.mk ((a.val * b.val) % n) (Nat.mod_lt _ (a.size_positive)))
| ⟨_, _⟩, ⟨_, _⟩ => rfl

lemma sub_def : ∀ (a b : Fin n),
  a - b = (Fin.mk ((a + (n - b)) % n) (Nat.mod_lt _ (a.size_positive)))
| ⟨_, _⟩, ⟨_, _⟩ => rfl

lemma size_positive' [Nonempty (Fin n)] : 0 < n :=
  ‹Nonempty (Fin n)›.elim fun i ↦ Fin.size_positive i

@[simp] lemma one_val : (1 : Fin (n + 2)).val = 1 := by
  simp only [OfNat.ofNat, Fin.ofNat]
  rw [Nat.mod_eq_of_lt]
  exact Nat.succ_lt_succ (Nat.zero_lt_succ _)

end from_ad_hoc

protected theorem prop (a : Fin n) : a.val < n :=
  a.2
#align fin.prop Fin.prop

@[simp]
theorem is_lt (a : Fin n) : (a : ℕ) < n :=
  a.2
#align fin.is_lt Fin.is_lt

protected theorem pos (i : Fin n) : 0 < n :=
  lt_of_le_of_lt (Nat.zero_le _) i.is_lt
#align fin.pos Fin.pos

theorem pos_iff_nonempty {n : ℕ} : 0 < n ↔ Nonempty (Fin n) :=
  ⟨fun h => ⟨⟨0, h⟩⟩, fun ⟨i⟩ => i.pos⟩
#align fin.pos_iff_nonempty Fin.pos_iff_nonempty

/-- Equivalence between `fin n` and `{ i // i < n }`. -/
@[simps apply symm_apply]
def equivSubtype : Fin n ≃ { i //
        i < n } where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
#align fin.equiv_subtype Fin.equivSubtype

section coe

/-!
### coercions and constructions
-/

--#print Fin.eta /-
@[simp]
protected theorem eta (a : Fin n) (h : (a : ℕ) < n) : (⟨(a : ℕ), h⟩ : Fin n) = a := by
  cases a; rfl
#align fin.eta Fin.eta

--#print Fin.ext /-
@[ext]
theorem ext {a b : Fin n} (h : (a : ℕ) = b) : a = b :=
  eq_of_veq h
#align fin.ext Fin.ext

--#print Fin.ext_iff /-
theorem ext_iff {a b : Fin n} : a = b ↔ (a : ℕ) = b :=
  Iff.intro (congr_arg _) Fin.eq_of_veq
#align fin.ext_iff Fin.ext_iff

section from_ad_hoc
-- porting note: this comes from the ad hoc port of this file
variable [Nonempty (Fin n)]

@[to_additive_fixed_numeral]
instance : OfNat (Fin n) x where
  ofNat := Fin.ofNat' x Fin.size_positive'

@[simp] lemma Fin.ofNat'_zero : (Fin.ofNat' 0 h : Fin n) = 0 := rfl
@[simp] lemma Fin.ofNat'_one : (Fin.ofNat' 1 h : Fin n) = 1 := rfl

lemma Fin.ofNat'_succ : {n : Nat} → [Nonempty (Fin n)] →
    (Fin.ofNat' i.succ Fin.size_positive' : Fin n) = (Fin.ofNat' i Fin.size_positive' : Fin n) + 1
  | n + 2, h => ext (by simp [Fin.ofNat', Fin.add_def])
  | 1, h => Subsingleton.allEq _ _
  | 0, h => Subsingleton.allEq _ _

end from_ad_hoc


-- this is syntactically the same as `Fin.val_injective` now.
#noalign fin.coe_injective

theorem val_eq_val (a b : Fin n) : (a : ℕ) = b ↔ a = b :=
  ext_iff.symm
#align fin.coe_eq_coe Fin.val_eq_val

theorem eq_iff_veq (a b : Fin n) : a = b ↔ a.1 = b.1 :=
  ⟨veq_of_eq, eq_of_veq⟩
#align fin.eq_iff_veq Fin.eq_iff_veq

theorem ne_iff_vne (a b : Fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
  ⟨vne_of_ne, ne_of_vne⟩
#align fin.ne_iff_vne Fin.ne_iff_vne

-- porting note: I'm not sure if this comment still applies.
-- built-in reduction doesn't always work
@[simp, nolint simpNF]
theorem mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a' :=
  ext_iff
#align fin.mk_eq_mk Fin.mk_eq_mk

protected theorem mk.inj_iff {n a b : ℕ} {ha : a < n} {hb : b < n} :
    (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ ↔ a = b :=
  eq_iff_veq _ _
#align fin.mk.inj_iff Fin.mk.inj_iff

theorem mk_val {m n : ℕ} (h : m < n) : (⟨m, h⟩ : Fin n).val = m :=
  rfl
#align fin.mk_val Fin.mk_val

theorem eq_mk_iff_val_eq {a : Fin n} {k : ℕ} {hk : k < n} : a = ⟨k, hk⟩ ↔ (a : ℕ) = k :=
  Fin.eq_iff_veq a ⟨k, hk⟩
#align fin.eq_mk_iff_coe_eq Fin.eq_mk_iff_val_eq

-- porting note: not necesary anymore because of the way coercions work
#noalign fin.coe_mk

theorem mk_val' (i : Fin n) : (⟨i, i.isLt⟩ : Fin n) = i :=
  Fin.eta _ _
#align fin.mk_coe Fin.mk_val'
-- porting note: `Fin.mk_val` already exists above and has a different type signature

-- syntactic tautologies now
#noalign fin.coe_eq_val
#noalign fin.val_eq_coe

/-- Assume `k = l`. If two functions defined on `fin k` and `fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected theorem heq_fun_iff {α : Sort _} {k l : ℕ} (h : k = l) {f : Fin k → α} {g : Fin l → α} :
    HEq f g ↔ ∀ i : Fin k, f i = g ⟨(i : ℕ), h ▸ i.2⟩ := by
  subst h
  simp [Function.funext_iff]
#align fin.heq_fun_iff Fin.heq_fun_iff

protected theorem heq_ext_iff {k l : ℕ} (h : k = l) {i : Fin k} {j : Fin l} :
    HEq i j ↔ (i : ℕ) = (j : ℕ) := by
  subst h
  simp [val_eq_val]
#align fin.heq_ext_iff Fin.heq_ext_iff

theorem exists_iff {p : Fin n → Prop} : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
  ⟨fun h => Exists.elim h fun ⟨i, hi⟩ hpi => ⟨i, hi, hpi⟩, fun h =>
    Exists.elim h fun i hi => ⟨⟨i, hi.fst⟩, hi.snd⟩⟩
#align fin.exists_iff Fin.exists_iff

theorem forall_iff {p : Fin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
  ⟨fun h i hi => h ⟨i, hi⟩, fun h ⟨i, hi⟩ => h i hi⟩
#align fin.forall_iff Fin.forall_iff

end coe

section Order

/-!
### order
-/


theorem is_le (i : Fin (n + 1)) : (i : ℕ) ≤ n :=
  le_of_lt_succ i.is_lt
#align fin.is_le Fin.is_le

@[simp]
theorem is_le' {a : Fin n} : (a : ℕ) ≤ n :=
  le_of_lt a.is_lt
#align fin.is_le' Fin.is_le'

theorem lt_iff_val_lt_val {a b : Fin n} : a < b ↔ (a : ℕ) < b :=
  Iff.rfl
#align fin.lt_iff_coe_lt_coe Fin.lt_iff_val_lt_val

theorem le_iff_val_le_val {a b : Fin n} : a ≤ b ↔ (a : ℕ) ≤ b :=
  Iff.rfl
#align fin.le_iff_coe_le_coe Fin.le_iff_val_le_val

theorem mk_lt_of_lt_val {b : Fin n} {a : ℕ} (h : a < b) : (⟨a, h.trans b.is_lt⟩ : Fin n) < b :=
  h
#align fin.mk_lt_of_lt_coe Fin.mk_lt_of_lt_val

theorem mk_le_of_le_val {b : Fin n} {a : ℕ} (h : a ≤ b) : (⟨a, h.trans_lt b.is_lt⟩ : Fin n) ≤ b :=
  h
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

instance {n : ℕ} : LinearOrder (Fin n) :=
  @LinearOrder.lift (Fin n) _ _ ⟨fun x y => ⟨max x y, max_rec' (· < n) x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' (· < n) x.2 y.2⟩⟩ Fin.val Fin.val_injective (fun _ _ => rfl)
    fun _ _ => rfl

@[simp]
theorem mk_le_mk {x y : Nat} {hx} {hy} : (⟨x, hx⟩ : Fin n) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl
#align fin.mk_le_mk Fin.mk_le_mk

@[simp]
theorem mk_lt_mk {x y : Nat} {hx} {hy} : (⟨x, hx⟩ : Fin n) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl
#align fin.mk_lt_mk Fin.mk_lt_mk

@[simp]
theorem min_val {a : Fin n} : min (a : ℕ) n = a := by simp
#align fin.min_coe Fin.min_val

@[simp]
theorem max_val {a : Fin n} : max (a : ℕ) n = n := by simp
#align fin.max_coe Fin.max_val

instance {n : ℕ} : PartialOrder (Fin n) := by infer_instance

theorem val_strictMono : StrictMono (val : Fin n → ℕ) := fun _ _ => id
#align fin.coe_strict_mono Fin.val_strictMono

/-- The equivalence `fin n ≃ { i // i < n }` is an order isomorphism. -/
@[simps apply symmApply]
def orderIsoSubtype : Fin n ≃o { i // i < n } :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])
#align fin.order_iso_subtype Fin.orderIsoSubtype

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

/-- The inclusion map `Fin n → ℕ` is an order embedding. -/
@[simps apply]
def valOrderEmbedding (n) : Fin n ↪o ℕ :=
  ⟨valEmbedding, Iff.rfl⟩
#align fin.coe_order_embedding Fin.valOrderEmbedding

/-- The ordering on `Fin n` is a well order. -/
instance Lt.isWellOrder (n) : IsWellOrder (Fin n) (· < ·) :=
  (valOrderEmbedding n).isWellOrder
#align fin.fin.lt.is_well_order Fin.Lt.isWellOrder

/-- Use the ordering on `Fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker,
unless we declare the `WellFoundedRelation` instance:
```lean
def factorial {n : ℕ} : fin n → ℕ
| ⟨0, _⟩ := 1
| ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : ℕ} : WellFoundedRelation (Fin n) :=
  measure (val : Fin n → ℕ)

-- porting note: hmm, this is broken, how to fix? Should we prove `Fin.val = Nat.cast`?
@[simp]
theorem val_zero {n : ℕ} : ((0 : Fin (n + 1)) : ℕ) = 0 := Fin.ofNat'_zero_val
#align fin.coe_zero Fin.val_zero

-- porting note: this is tagged above: `attribute [simp] val_zero`

@[simp]
theorem val_zero' (n) : (0 : Fin (n + 1)).val = 0 :=
  val_zero -- was `rfl`
#align fin.val_zero' Fin.val_zero'

@[simp]
theorem mk_zero : (⟨0, Nat.succ_pos'⟩ : Fin (n + 1)) = (0 : Fin _) := by
  ext
  simp only [val_zero] -- was `rfl`
#align fin.mk_zero Fin.mk_zero

@[simp]
theorem zero_le (a : Fin (n + 1)) : 0 ≤ a := by
  simp only [le_iff_val_le_val, val_zero, _root_.zero_le] -- was `zero_le a.val`
#align fin.zero_le Fin.zero_le

theorem zero_lt_one : (0 : Fin (n + 2)) < 1 :=
  Nat.zero_lt_one
#align fin.zero_lt_one Fin.zero_lt_one

@[simp]
theorem not_lt_zero (a : Fin n.succ) : ¬a < 0 := by
  simp only [lt_iff_val_lt_val, val_zero, not_lt_zero', not_false_iff] -- was `fun.`
#align fin.not_lt_zero Fin.not_lt_zero

theorem pos_iff_ne_zero (a : Fin (n + 1)) : 0 < a ↔ a ≠ 0 := by
  rw [← val_fin_lt, val_zero, _root_.pos_iff_ne_zero, Ne.def, Ne.def, ext_iff, val_zero]
#align fin.pos_iff_ne_zero Fin.pos_iff_ne_zero

theorem eq_zero_or_eq_succ {n : ℕ} (i : Fin (n + 1)) : i = 0 ∨ ∃ j : Fin n, i = j.succ := by
  rcases i with ⟨_ | j, h⟩
  · left
    simp only [zero_eq, mk_zero] -- was `rfl`
  · right
    exact ⟨⟨j, Nat.lt_of_succ_lt_succ h⟩, rfl⟩
#align fin.eq_zero_or_eq_succ Fin.eq_zero_or_eq_succ

theorem eq_succ_of_ne_zero {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ 0) : ∃ j : Fin n, i = j.succ :=
  (eq_zero_or_eq_succ i).resolve_left hi
#align fin.eq_succ_of_ne_zero Fin.eq_succ_of_ne_zero

/-- The antitone involution `fin n → fin n` given by `i ↦ n-(i+1)`. -/
def rev : Equiv.Perm (Fin n) :=
  (Involutive.toPerm fun i => ⟨n - (i + 1), tsub_lt_self i.pos (Nat.succ_pos _)⟩) fun i =>
    ext <| by
      dsimp only
      rw [← tsub_tsub, tsub_tsub_cancel_of_le (Nat.add_one_le_iff.2 i.is_lt),
        add_tsub_cancel_right]
#align fin.rev Fin.rev

-- porting note: dot notation of the form `i.rev` is broken here and throughout
@[simp]
theorem val_rev (i : Fin n) : (rev i : ℕ) = n - (i + 1) :=
  rfl
#align fin.coe_rev Fin.val_rev

theorem rev_involutive : Involutive (@rev n) :=
  Involutive.toPerm_involutive _
#align fin.rev_involutive Fin.rev_involutive

theorem rev_injective : Injective (@rev n) :=
  rev_involutive.injective
#align fin.rev_injective Fin.rev_injective

theorem rev_surjective : Surjective (@rev n) :=
  rev_involutive.surjective
#align fin.rev_surjective Fin.rev_surjective

theorem rev_bijective : Bijective (@rev n) :=
  rev_involutive.bijective
#align fin.rev_bijective Fin.rev_bijective

@[simp]
theorem rev_inj {i j : Fin n} : rev i = rev j ↔ i = j :=
  rev_injective.eq_iff
#align fin.rev_inj Fin.rev_inj

@[simp]
theorem rev_rev (i : Fin n) : rev (rev i) = i :=
  rev_involutive _
#align fin.rev_rev Fin.rev_rev

@[simp]
theorem rev_symm : (@rev n).symm = rev :=
  rfl
#align fin.rev_symm Fin.rev_symm

theorem rev_eq {n a : ℕ} (i : Fin (n + 1)) (h : n = a + i) :
    rev i = ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro h.symm)⟩ := by
  ext
  dsimp
  conv_lhs =>
    congr
    rw [h]
  rw [add_assoc, add_tsub_cancel_right]
#align fin.rev_eq Fin.rev_eq

@[simp]
theorem rev_le_rev {i j : Fin n} : rev i ≤ rev j ↔ j ≤ i := by
  simp only [le_iff_val_le_val, val_rev, tsub_le_tsub_iff_left (Nat.add_one_le_iff.2 j.is_lt),
    add_le_add_iff_right, iff_self]
#align fin.rev_le_rev Fin.rev_le_rev

@[simp]
theorem rev_lt_rev {i j : Fin n} : rev i < rev j ↔ j < i :=
  lt_iff_lt_of_le_iff_le rev_le_rev
#align fin.rev_lt_rev Fin.rev_lt_rev

/-- `fin.rev n` as an order-reversing isomorphism. -/
@[simps apply toEquiv]
def revOrderIso {n} : (Fin n)ᵒᵈ ≃o Fin n :=
  ⟨OrderDual.ofDual.trans rev, rev_le_rev⟩
#align fin.rev_order_iso Fin.revOrderIso

@[simp]
theorem revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual (rev i) :=
  rfl
#align fin.rev_order_iso_symm_apply Fin.revOrderIso_symm_apply

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : Fin (n + 1) :=
  ⟨_, n.lt_succ_self⟩
#align fin.last Fin.last

@[simp, norm_cast]
theorem val_last (n : ℕ) : (last n : ℕ) = n :=
  rfl
#align fin.coe_last Fin.val_last

-- porting note: this is now syntactically equal to `val_last`
theorem last_val (n : ℕ) : (last n).val = n :=
  rfl
#align fin.last_val Fin.last_val

theorem le_last (i : Fin (n + 1)) : i ≤ last n :=
  le_of_lt_succ i.is_lt
#align fin.le_last Fin.le_last

instance : BoundedOrder (Fin (n + 1)) where
  top := last n
  le_top := le_last
  bot := 0
  bot_le := zero_le

instance : Lattice (Fin (n + 1)) :=
  LinearOrder.toLattice

theorem last_pos : (0 : Fin (n + 2)) < last (n + 1) := by simp [lt_iff_val_lt_val]
#align fin.last_pos Fin.last_pos

theorem eq_last_of_not_lt {i : Fin (n + 1)} (h : ¬(i : ℕ) < n) : i = last n :=
  le_antisymm (le_last i) (not_lt.1 h)
#align fin.eq_last_of_not_lt Fin.eq_last_of_not_lt

theorem top_eq_last (n : ℕ) : ⊤ = Fin.last n :=
  rfl
#align fin.top_eq_last Fin.top_eq_last

theorem bot_eq_zero (n : ℕ) : ⊥ = (0 : Fin (n + 1)) :=
  rfl
#align fin.bot_eq_zero Fin.bot_eq_zero

section

variable {α : Type _} [Preorder α]

open Set

/-- If `e` is an `orderIso` between `Fin n` and `Fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : Fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
@[simp]
theorem coe_orderIso_apply (e : Fin n ≃o Fin m) (i : Fin n) : (e i : ℕ) = i := by
  rcases i with ⟨i, hi⟩
  dsimp only
  induction' i using Nat.strong_induction_on with i h
  refine' le_antisymm (forall_lt_iff_le.1 fun j hj => _) (forall_lt_iff_le.1 fun j hj => _)
  · have := e.symm.lt_iff_lt.2 (mk_lt_of_lt_val hj)
    rw [e.symm_apply_apply] at this
    convert this
    simpa using h _ this (e.symm _).is_lt
  · rwa [← h j hj (hj.trans hi), ← lt_iff_val_lt_val, e.lt_iff_lt]
#align fin.coe_order_iso_apply Fin.coe_orderIso_apply

instance orderIso_subsingleton : Subsingleton (Fin n ≃o α) :=
  ⟨fun e e' => by
    ext i
    rw [← e.symm.apply_eq_iff_eq, e.symm_apply_apply, ← e'.trans_apply, ext_iff,
      coe_orderIso_apply]⟩
#align fin.order_iso_subsingleton Fin.orderIso_subsingleton

instance orderIso_subsingleton' : Subsingleton (α ≃o Fin n) :=
  OrderIso.symm_injective.subsingleton
#align fin.order_iso_subsingleton' Fin.orderIso_subsingleton'

instance orderIsoUnique : Unique (Fin n ≃o Fin n) :=
  Unique.mk' _
#align fin.order_iso_unique Fin.orderIsoUnique

/-- Two strictly monotone functions from `Fin n` are equal provided that their ranges
are equal. -/
theorem strictMono_unique {f g : Fin n → α} (hf : StrictMono f) (hg : StrictMono g)
    (h : range f = range g) : f = g :=
  have : (hf.orderIso f).trans (OrderIso.setCongr _ _ h) = hg.orderIso g := Subsingleton.elim _ _
  congr_arg (Function.comp (Subtype.val : range g → α)) (funext <| RelIso.ext_iff.1 this)
#align fin.strict_mono_unique Fin.strictMono_unique

/-- Two order embeddings of `Fin n` are equal provided that their ranges are equal. -/
theorem orderEmbedding_eq {f g : Fin n ↪o α} (h : range f = range g) : f = g :=
  RelEmbedding.ext <| funext_iff.1 <| strictMono_unique f.strictMono g.strictMono h
#align fin.order_embedding_eq Fin.orderEmbedding_eq

end

end Order

section Add

/-!
### addition, numerals, and coercion from nat
-/


/- warning: fin.of_nat' -> Fin.ofNat' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} [_inst_1 : NeZero.{0} Nat Nat.hasZero n], Nat -> (Fin n)
but is expected to have type
  forall {n : Nat}, Nat -> (GT.gt.{0} Nat instLTNat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Fin n)
Case conversion may be inaccurate. Consider using '#align fin.of_nat' Fin.ofNat'ₓ'. -/
/-- Given a positive `n`, `fin.of_nat' i` is `i % n` as an element of `fin n`. -/
def ofNat'' [NeZero n] (i : ℕ) : Fin n :=
  ⟨i % n, mod_lt _ <| NeZero.pos n⟩
#align fin.of_nat' Fin.ofNat''
-- porting note: `Fin.ofNat'` conflicts with something in core (there the hypothesis is `n > 0`),
-- so for now we make this double-prime `''`. This is also the reason for the dubious translation.

/- warning: fin.one_val -> Fin.one_val is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} Nat (Fin.val (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasOne n))))) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {n : Nat}, Eq.{1} Nat (Fin.val (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) 1 (Fin.instOfNatFinHAddNatInstHAddInstAddNatOfNat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align fin.one_val Fin.one_valₓ'. -/
theorem one_val' {n : ℕ} : (1 : Fin (n + 1)).val = 1 % (n + 1) := by
  cases n
  · simp only
  · simp only [OfNat.ofNat, Fin.ofNat]
    rw [Nat.mod_eq_of_lt, Fin.ofNat'_one, one_val]
    exact Nat.succ_lt_succ (Nat.zero_lt_succ _)
  -- used to be `rfl`
#align fin.one_val Fin.one_val'
-- porting note: this will conflict with the ad hoc port of `Fin.one_val`, for which the types
-- don't match

theorem coe_one' {n : ℕ} : ((1 : Fin (n + 1)) : ℕ) = 1 % (n + 1) :=
  rfl
#align fin.coe_one' Fin.coe_one'

@[simp]
theorem val_one {n : ℕ} : (1 : Fin (n + 2)).val = 1 :=
  rfl
#align fin.val_one Fin.val_one

@[simp]
theorem val_one' {n : ℕ} : ((1 : Fin (n + 2)) : ℕ) = 1 :=
  rfl
#align fin.coe_one Fin.val_one'
-- porting note: syntactically the same as `Fin.val_one` now.

@[simp]
theorem mk_one : (⟨1, Nat.succ_lt_succ (Nat.succ_pos n)⟩ : Fin (n + 2)) = (1 : Fin _) :=
  rfl
#align fin.mk_one Fin.mk_one

instance Fin.nontrivial {n : ℕ} : Nontrivial (Fin (n + 2)) where
  exists_pair_ne := ⟨0, 1, (ne_iff_vne 0 1).mpr (by simp only [val_one', val_zero])⟩

theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  rcases n with (_ | _ | n) <;>
  simp [←Nat.one_eq_succ_zero, Fin.nontrivial, not_nontrivial, Nat.succ_le_iff]
-- porting note: here and in the next lemma, had to use `←Nat.one_eq_succ_zero`.
#align fin.nontrivial_iff_two_le Fin.nontrivial_iff_two_le

theorem subsingleton_iff_le_one : Subsingleton (Fin n) ↔ n ≤ 1 := by
  rcases n with (_ | _ | n) <;>
  simp [IsEmpty.instSubsingleton, Unique.instSubsingleton, ←Nat.one_eq_succ_zero, not_subsingleton]
#align fin.subsingleton_iff_le_one Fin.subsingleton_iff_le_one

section Monoid

@[simp]
protected theorem add_zero (k : Fin (n + 1)) : k + 0 = k := by
  simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]
#align fin.add_zero Fin.add_zero

@[simp]
protected theorem zero_add (k : Fin (n + 1)) : (0 : Fin (n + 1)) + k = k := by
  simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]
#align fin.zero_add Fin.zero_add

instance addCommMonoid (n : ℕ) :
    AddCommMonoid (Fin (n + 1)) where
  add := (· + ·)
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc]
  zero := 0
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  add_comm := by simp [eq_iff_veq, add_def, add_comm]
#align fin.add_comm_monoid Fin.addCommMonoid

instance : AddMonoidWithOne (Fin (n + 1)) :=
  { Fin.addCommMonoid n with
    one := 1
    natCast := Fin.ofNat
    natCast_zero := rfl
    natCast_succ := fun _ => eq_of_veq (add_mod _ _ _) }

end Monoid

theorem val_add {n : ℕ} : ∀ a b : Fin n, (a + b).val = (a.val + b.val) % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl
#align fin.val_add Fin.val_add

-- porting note: this is the same as `val_add` because coercions unfold
theorem val_add' {n : ℕ} : ∀ a b : Fin n, ((a + b : Fin n) : ℕ) = (a + b) % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl
#align fin.coe_add Fin.val_add'

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
theorem val_bit1 {n : ℕ} (k : Fin (n + 1)) :
    ((bit1 k : Fin (n + 1)) : ℕ) = bit1 (k : ℕ) % (n + 1) := by
  cases n;
  · cases' k with k h
    cases k
    · show _ % _ = _
      simp
    cases' h with _ h
    cases h
  simp [bit1, Fin.val_bit0, Fin.val_add, Fin.val_one]
#align fin.coe_bit1 Fin.val_bit1

end deprecated

theorem val_add_one_of_lt {n : ℕ} {i : Fin n.succ} (h : i < last _) : (↑(i + 1) : ℕ) = i + 1 :=
  by
  -- First show that `((1 : fin n.succ) : ℕ) = 1`, because `n.succ` is at least 2.
  cases n
  · cases h
  -- Then just unfold the definitions.
  rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (Nat.succ_lt_succ _)]
  exact h
#align fin.coe_add_one_of_lt Fin.val_add_one_of_lt

@[simp]
theorem last_add_one : ∀ n, last n + 1 = 0
  | 0 => by simp only
  | n + 1 => by
    ext
    rw [val_add, val_zero, val_last, val_one, Nat.mod_self]
#align fin.last_add_one Fin.last_add_one

theorem val_add_one {n : ℕ} (i : Fin (n + 1)) :
    ((i + 1 : Fin (n + 1)) : ℕ) = if i = last _ then 0 else i + 1 := by
  rcases(le_last i).eq_or_lt with (rfl | h)
  · simp
  · simp [h.ne]
#align fin.coe_add_one Fin.val_add_one

section Bit
set_option linter.deprecated false

@[simp, deprecated]
theorem mk_bit0 {m n : ℕ} (h : bit0 m < n) :
    (⟨bit0 m, h⟩ : Fin n) = (bit0 ⟨m, (Nat.le_add_right m m).trans_lt h⟩ : Fin _) :=
  eq_of_veq (Nat.mod_eq_of_lt h).symm
#align fin.mk_bit0 Fin.mk_bit0

@[simp, deprecated]
theorem mk_bit1 {m n : ℕ} (h : bit1 m < n + 1) :
    (⟨bit1 m, h⟩ : Fin (n + 1)) =
      (bit1 ⟨m, (Nat.le_add_right m m).trans_lt ((m + m).lt_succ_self.trans h)⟩ : Fin _) :=
  by
  ext
  simp only [bit1, bit0] at h
  simp only [bit1, bit0, val_add, coe_one', ← Nat.add_mod, Nat.mod_eq_of_lt h]
#align fin.mk_bit1 Fin.mk_bit1

end Bit

@[simp]
theorem val_two {n : ℕ} : (2 : Fin (n + 3)).val = 2 :=
  rfl
#align fin.val_two Fin.val_two

--- porting note: syntactically the same as the above
@[simp]
theorem val_two' {n : ℕ} : ((2 : Fin (n + 3)) : ℕ) = 2 :=
  rfl
#align fin.coe_two Fin.val_two'

section OfNatCoe

@[simp]
theorem ofNat_eq_val (n : ℕ) (a : ℕ) : (Fin.ofNat a : Fin (n + 1)) = a :=
  rfl
#align fin.of_nat_eq_coe Fin.ofNat_eq_val

-- porting note: is this the right name for things involving `Nat.cast`?
/-- Converting an in-range number to `Fin (n + 1)` produces a result
whose value is the original number.  -/
theorem val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) : (a : Fin (n + 1)).val = a := by
  rw [← ofNat_eq_val]
  exact Nat.mod_eq_of_lt h
#align fin.coe_val_of_lt Fin.val_cast_of_lt

/-- Converting the value of a `Fin (n + 1)` to `Fin (n + 1)` results
in the same value.  -/
theorem cast_val_eq_self {n : ℕ} (a : Fin (n + 1)) : (a.val : Fin (n + 1)) = a := by
  rw [Fin.eq_iff_veq]
  exact val_cast_of_lt a.isLt
#align fin.coe_val_eq_self Fin.cast_val_eq_self

-- porting note: this is syntactically the same as `val_cast_of_lt`
/-- Coercing an in-range number to `Fin (n + 1)`, and converting back
to `ℕ`, results in that number. -/
theorem val_cast_of_lt' {n : ℕ} {a : ℕ} (h : a < n + 1) : ((a : Fin (n + 1)) : ℕ) = a :=
  val_cast_of_lt h
#align fin.coe_coe_of_lt Fin.val_cast_of_lt'

-- porting note: this is syntactically the same as `cast_val_of_lt`
/-- Converting a `Fin (n + 1)` to `ℕ` and back results in the same
value. -/
@[simp]
theorem cast_val_eq_self' {n : ℕ} (a : Fin (n + 1)) : ((a : ℕ) : Fin (n + 1)) = a :=
  cast_val_eq_self a
#align fin.coe_coe_eq_self Fin.cast_val_eq_self'

theorem cast_nat_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by
  rw [← Fin.ofNat_eq_val, Fin.ofNat, Fin.last]
  simp only [Nat.mod_eq_of_lt n.lt_succ_self]
#align fin.coe_nat_eq_last Fin.cast_nat_eq_last

theorem le_val_last (i : Fin (n + 1)) : i ≤ n := by
  rw [Fin.cast_nat_eq_last]
  exact Fin.le_last i
#align fin.le_coe_last Fin.le_val_last

end OfNatCoe

theorem add_one_pos (i : Fin (n + 1)) (h : i < Fin.last n) : (0 : Fin (n + 1)) < i + 1 := by
  cases n
  · exact absurd h (Nat.not_lt_zero _)
  · rw [lt_iff_val_lt_val, val_last, ← add_lt_add_iff_right 1] at h
    rw [lt_iff_val_lt_val, val_add, val_zero, val_one, Nat.mod_eq_of_lt h]
    exact Nat.zero_lt_succ _
#align fin.add_one_pos Fin.add_one_pos

theorem one_pos : (0 : Fin (n + 2)) < 1 :=
  succ_pos 0
#align fin.one_pos Fin.one_pos

theorem zero_ne_one : (0 : Fin (n + 2)) ≠ 1 :=
  ne_of_lt one_pos
#align fin.zero_ne_one Fin.zero_ne_one

@[simp]
theorem zero_eq_one_iff : (0 : Fin (n + 1)) = 1 ↔ n = 0 := by
  --clear a b-- porting note: this is necessary so that they don't show up in the type
  -- see Zulip: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/bug.20in.20included.20variables
  constructor
  · cases n <;> intro h
    · rfl
    · exact False.elim <| zero_ne_one h
  · rintro rfl
    rfl
#align fin.zero_eq_one_iff Fin.zero_eq_one_iff

@[simp]
theorem one_eq_zero_iff : (1 : Fin (n + 1)) = 0 ↔ n = 0 := by rw [eq_comm, zero_eq_one_iff]
#align fin.one_eq_zero_iff Fin.one_eq_zero_iff

end Add

section Succ

/-!
### succ and casts into larger fin types
-/

@[simp]
theorem val_succ (j : Fin n) : (j.succ : ℕ) = j + 1 := by cases j; simp [Fin.succ]
#align fin.coe_succ Fin.val_succ

@[simp]
theorem succ_pos (a : Fin n) : (0 : Fin (n + 1)) < a.succ := by simp [lt_iff_val_lt_val]
#align fin.succ_pos Fin.succ_pos

/-- `Fin.succ` as an `OrderEmbedding` -/
def succEmbedding (n : ℕ) : Fin n ↪o Fin (n + 1) :=
  (OrderEmbedding.ofStrictMono Fin.succ) fun _ _ h => succ_lt_succ h
#align fin.succ_embedding Fin.succEmbedding

@[simp]
theorem val_succEmbedding : ⇑(succEmbedding n) = Fin.succ :=
  rfl
#align fin.coe_succ_embedding Fin.val_succEmbedding

@[simp]
theorem succ_le_succ_iff {a b : Fin n} : a.succ ≤ b.succ ↔ a ≤ b :=
  (succEmbedding n).le_iff_le
#align fin.succ_le_succ_iff Fin.succ_le_succ_iff

@[simp]
theorem succ_lt_succ_iff {a b : Fin n} : a.succ < b.succ ↔ a < b :=
  (succEmbedding n).lt_iff_lt
#align fin.succ_lt_succ_iff Fin.succ_lt_succ_iff

theorem succ_injective (n : ℕ) : Injective (@Fin.succ n) :=
  (succEmbedding n).injective
#align fin.succ_injective Fin.succ_injective

@[simp]
theorem succ_inj {a b : Fin n} : a.succ = b.succ ↔ a = b :=
  (succ_injective n).eq_iff
#align fin.succ_inj Fin.succ_inj

theorem succ_ne_zero {n} : ∀ k : Fin n, Fin.succ k ≠ 0
  | ⟨k, hk⟩, heq => Nat.succ_ne_zero k <| by simpa using ext_iff.1 heq
  -- porting note: the `simpa` didn't used to be necessary
#align fin.succ_ne_zero Fin.succ_ne_zero

@[simp]
theorem succ_zero_eq_one : Fin.succ (0 : Fin (n + 1)) = 1 := by
  ext
  simp only [val_succ, val_zero, zero_add, one_val] -- porting note: was `rfl`
#align fin.succ_zero_eq_one Fin.succ_zero_eq_one

@[simp]
theorem succ_one_eq_two : Fin.succ (1 : Fin (n + 2)) = 2 :=
  rfl
#align fin.succ_one_eq_two Fin.succ_one_eq_two

@[simp]
theorem succ_mk (n i : ℕ) (h : i < n) : Fin.succ ⟨i, h⟩ = ⟨i + 1, Nat.succ_lt_succ h⟩ :=
  rfl
#align fin.succ_mk Fin.succ_mk

theorem mk_succ_pos (i : ℕ) (h : i < n) : (0 : Fin (n + 1)) < ⟨i.succ, add_lt_add_right h 1⟩ := by
  rw [lt_iff_val_lt_val, val_zero]
  exact Nat.succ_pos i
#align fin.mk_succ_pos Fin.mk_succ_pos

theorem one_lt_succ_succ (a : Fin n) : (1 : Fin (n + 2)) < a.succ.succ := by
  cases n
  · simp only [lt_iff_val_lt_val, one_val, zero_eq, val_succ, lt_add_iff_pos_left, add_pos_iff,
      or_true] -- porting note: was `exact finZeroElim a`
  · rw [← succ_zero_eq_one, succ_lt_succ_iff]
    exact succ_pos a
#align fin.one_lt_succ_succ Fin.one_lt_succ_succ

@[simp]
theorem add_one_lt_iff {n : ℕ} {k : Fin (n + 2)} : k + 1 < k ↔ k = last _ := by
  simp only [lt_iff_val_lt_val, val_add, val_last, ext_iff]
  cases' k with k hk
  rcases(le_of_lt_succ hk).eq_or_lt with (rfl | hk')
  · simp
  · simp [hk'.ne, mod_eq_of_lt (succ_lt_succ hk'), le_succ _]
#align fin.add_one_lt_iff Fin.add_one_lt_iff

@[simp]
theorem add_one_le_iff {n : ℕ} {k : Fin (n + 1)} : k + 1 ≤ k ↔ k = last _ := by
  cases n
  · simp [Subsingleton.elim (k + 1) k, Subsingleton.elim (Fin.last _) k]
  rw [← not_iff_not, ← add_one_lt_iff, lt_iff_le_and_ne, not_and']
  refine' ⟨fun h _ => h, fun h => h _⟩
  rw [Ne.def, ext_iff, val_add_one]
  split_ifs with hk hk <;> simp [hk, eq_comm]
#align fin.add_one_le_iff Fin.add_one_le_iff

@[simp]
theorem last_le_iff {n : ℕ} {k : Fin (n + 1)} : last n ≤ k ↔ k = last n :=
  top_le_iff
#align fin.last_le_iff Fin.last_le_iff

@[simp]
theorem lt_add_one_iff {n : ℕ} {k : Fin (n + 1)} : k < k + 1 ↔ k < last n := by
  rw [← not_iff_not]
  simp
#align fin.lt_add_one_iff Fin.lt_add_one_iff

@[simp]
theorem le_zero_iff {n : ℕ} {k : Fin (n + 1)} : k ≤ 0 ↔ k = 0 :=
  le_bot_iff
#align fin.le_zero_iff Fin.le_zero_iff

theorem succ_succ_ne_one (a : Fin n) : Fin.succ (Fin.succ a) ≠ 1 :=
  ne_of_gt (one_lt_succ_succ a)
#align fin.succ_succ_ne_one Fin.succ_succ_ne_one

/-- `cast_lt i h` embeds `i` into a `fin` where `h` proves it belongs into.  -/
def castLt (i : Fin m) (h : i.1 < n) : Fin n :=
  ⟨i.1, h⟩
#align fin.cast_lt Fin.castLt

@[simp]
theorem coe_cast_lt (i : Fin m) (h : i.1 < n) : (castLt i h : ℕ) = i :=
  rfl
#align fin.coe_cast_lt Fin.coe_cast_lt

@[simp]
theorem cast_lt_mk (i n m : ℕ) (hn : i < n) (hm : i < m) : castLt ⟨i, hn⟩ hm = ⟨i, hm⟩ :=
  rfl
#align fin.cast_lt_mk Fin.cast_lt_mk

/-- `cast_le h i` embeds `i` into a larger `fin` type.  -/
def castLe (h : n ≤ m) : Fin n ↪o Fin m :=
  (OrderEmbedding.ofStrictMono fun a => castLt a (lt_of_lt_of_le a.2 h)) fun _ _ h => h
#align fin.cast_le Fin.castLe

@[simp]
theorem coe_cast_le (h : n ≤ m) (i : Fin n) : (castLe h i : ℕ) = i :=
  rfl
#align fin.coe_cast_le Fin.coe_cast_le

@[simp]
theorem cast_le_mk (i n m : ℕ) (hn : i < n) (h : n ≤ m) :
    castLe h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h⟩ :=
  rfl
#align fin.cast_le_mk Fin.cast_le_mk

@[simp]
theorem cast_le_zero {n m : ℕ} (h : n.succ ≤ m.succ) : castLe h 0 = 0 := by simp [eq_iff_veq]
#align fin.cast_le_zero Fin.cast_le_zero

@[simp]
theorem range_cast_le {n k : ℕ} (h : n ≤ k) : Set.range (castLe h) = { i : Fin k | (i : ℕ) < n } :=
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, Fin.ext rfl⟩⟩
#align fin.range_cast_le Fin.range_cast_le

@[simp]
theorem coe_of_injective_cast_le_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLe h).injective).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_cast_le]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)
#align fin.coe_of_injective_cast_le_symm Fin.coe_of_injective_cast_le_symm

@[simp]
theorem cast_le_succ {m n : ℕ} (h : m + 1 ≤ n + 1) (i : Fin m) :
    castLe h i.succ = (castLe (Nat.succ_le_succ_iff.mp h) i).succ := by simp [Fin.eq_iff_veq]
#align fin.cast_le_succ Fin.cast_le_succ

@[simp]
theorem cast_le_cast_le {k m n} (km : k ≤ m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLe mn (Fin.castLe km i) = Fin.castLe (km.trans mn) i :=
  Fin.ext (by simp only [coe_cast_le])
#align fin.cast_le_cast_le Fin.cast_le_cast_le

@[simp]
theorem cast_le_comp_cast_le {k m n} (km : k ≤ m) (mn : m ≤ n) :
    Fin.castLe mn ∘ Fin.castLe km = Fin.castLe (km.trans mn) :=
  funext (cast_le_cast_le km mn)
#align fin.cast_le_comp_cast_le Fin.cast_le_comp_cast_le

/-- `cast eq i` embeds `i` into a equal `fin` type, see also `equiv.fin_congr`. -/
def cast (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨castLe eq.le, castLe eq.symm.le, fun _ => eq_of_veq rfl, fun _ => eq_of_veq rfl⟩
  map_rel_iff' := Iff.rfl
#align fin.cast Fin.cast

@[simp]
theorem symm_cast (h : n = m) : (cast h).symm = cast h.symm := by simp
#align fin.symm_cast Fin.symm_cast

/-- While `fin.coe_order_iso_apply` is a more general case of this, we mark this `simp` anyway
as it is eligible for `dsimp`. -/
@[simp]
theorem coe_cast (h : n = m) (i : Fin n) : (cast h i : ℕ) = i := by simp
#align fin.coe_cast Fin.coe_cast

@[simp]
theorem cast_zero {n' : ℕ} {h : n + 1 = n' + 1} : cast h (0 : Fin (n + 1)) = 0 := by
  ext
  simp
#align fin.cast_zero Fin.cast_zero

@[simp]
theorem cast_last {n' : ℕ} {h : n + 1 = n' + 1} : cast h (last n) = last n' :=
  ext (by rw [coe_cast, val_last, val_last, Nat.succ_injective h])
#align fin.cast_last Fin.cast_last

@[simp]
theorem cast_mk (h : n = m) (i : ℕ) (hn : i < n) :
    cast h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h.le⟩ := by
  ext
  simp
#align fin.cast_mk Fin.cast_mk

@[simp]
theorem cast_trans {k : ℕ} (h : n = m) (h' : m = k) {i : Fin n} :
    cast h' (cast h i) = cast (Eq.trans h h') i := by
  ext
  simp
#align fin.cast_trans Fin.cast_trans

@[simp]
theorem cast_refl (h : n = n := rfl) : cast h = OrderIso.refl (Fin n) := by
  ext
  simp
#align fin.cast_refl Fin.cast_refl

theorem cast_le_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} :
    (castLe h' : Fin m → Fin n) = Fin.cast h :=
  funext fun _ => by ext; simp
#align fin.cast_le_of_eq Fin.cast_le_of_eq

/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_to_equiv (h : n = m) : (cast h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h
  simp
#align fin.cast_to_equiv Fin.cast_to_equiv

/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_eq_cast (h : n = m) : (cast h : Fin n → Fin m) = cast (h ▸ rfl) := by
  subst h
  ext
  simp
#align fin.cast_eq_cast Fin.cast_eq_cast

/-- `cast_add m i` embeds `i : fin n` in `fin (n+m)`. See also `fin.nat_add` and `fin.add_nat`. -/
def castAdd (m) : Fin n ↪o Fin (n + m) :=
  castLe <| Nat.le_add_right n m
#align fin.cast_add Fin.castAdd

@[simp]
theorem coe_cast_add (m : ℕ) (i : Fin n) : (castAdd m i : ℕ) = i :=
  rfl
#align fin.coe_cast_add Fin.coe_cast_add

@[simp]
theorem cast_add_zero : (castAdd 0 : Fin n → Fin (n + 0)) = cast rfl := by
  ext
  simp only [Nat.add_zero, cast_refl, OrderIso.refl_apply]
  rfl
#align fin.cast_add_zero Fin.cast_add_zero

theorem cast_add_lt {m : ℕ} (n : ℕ) (i : Fin m) : (castAdd n i : ℕ) < m := by
  simp
#align fin.cast_add_lt Fin.cast_add_lt

set_option autoImplicit false

@[simp]
theorem cast_add_mk (m : ℕ) (i : ℕ) (h : i < n) : castAdd m ⟨i, h⟩ = ⟨i, Nat.lt_add_right i n m h⟩ :=
  rfl
#align fin.cast_add_mk Fin.cast_add_mk

@[simp]
theorem cast_add_cast_lt (m : ℕ) (i : Fin (n + m)) (hi : i.val < n) :
    castAdd m (castLt i hi) = i := by
  ext
  simp
#align fin.cast_add_cast_lt Fin.cast_add_cast_lt

@[simp]
theorem cast_lt_cast_add (m : ℕ) (i : Fin n) : castLt (castAdd m i) (cast_add_lt m i) = i := by
  ext
  simp
#align fin.cast_lt_cast_add Fin.cast_lt_cast_add

/-- For rewriting in the reverse direction, see `fin.cast_cast_add_left`. -/
theorem cast_add_cast {n n' : ℕ} (m : ℕ) (i : Fin n') (h : n' = n) :
    castAdd m (Fin.cast h i) = Fin.cast (congr_arg (. + m) h) (castAdd m i) :=
  ext rfl
#align fin.cast_add_cast Fin.cast_add_cast

theorem cast_cast_add_left {n n' m : ℕ} (i : Fin n') (h : n' + m = n + m) :
    cast h (castAdd m i) = castAdd m (cast (add_right_cancel h) i) := by
  ext
  simp
#align fin.cast_cast_add_left Fin.cast_cast_add_left

@[simp]
theorem cast_cast_add_right {n m m' : ℕ} (i : Fin n) (h : n + m' = n + m) :
    cast h (castAdd m' i) = castAdd m i := by
  ext
  simp
#align fin.cast_cast_add_right Fin.cast_cast_add_right

theorem cast_add_cast_add {m n p : ℕ} (i : Fin m) :
    castAdd p (castAdd n i) = cast (add_assoc _ _ _).symm (castAdd (n + p) i) := by
  ext
  simp
#align fin.cast_add_cast_add Fin.cast_add_cast_add

/-- The cast of the successor is the succesor of the cast. See `fin.succ_cast_eq` for rewriting in
the reverse direction. -/
@[simp]
theorem cast_succ_eq {n' : ℕ} (i : Fin n) (h : n.succ = n'.succ) :
    cast h i.succ = (cast (Nat.succ.inj h) i).succ :=
  ext <| by simp
#align fin.cast_succ_eq Fin.cast_succ_eq

theorem succ_cast_eq {n' : ℕ} (i : Fin n) (h : n = n') :
    (cast h i).succ = cast (by rw [h]) i.succ :=
  ext <| by simp
#align fin.succ_cast_eq Fin.succ_cast_eq

/-- `castSucc i` embeds `i : fin n` in `fin (n+1)`. -/
def castSucc : Fin n ↪o Fin (n + 1) :=
  castAdd 1
#align fin.cast_succ Fin.castSucc

@[simp]
theorem coe_cast_succ (i : Fin n) : (Fin.castSucc i : ℕ) = i :=
  rfl
#align fin.coe_cast_succ Fin.coe_cast_succ

@[simp]
theorem cast_succ_mk (n i : ℕ) (h : i < n) : castSucc ⟨i, h⟩ = ⟨i, Nat.lt.step h⟩ :=
  rfl
#align fin.cast_succ_mk Fin.cast_succ_mk

@[simp]
theorem cast_cast_succ {n' : ℕ} {h : n + 1 = n' + 1} {i : Fin n} :
    cast h (castSucc i) = castSucc (cast (Nat.succ_injective h) i) := by
  ext
  simp only [coe_cast, coe_cast_succ]
#align fin.cast_cast_succ Fin.cast_cast_succ

theorem cast_succ_lt_succ (i : Fin n) : Fin.castSucc i < i.succ :=
  lt_iff_val_lt_val.2 <| by simp only [coe_cast_succ, val_succ, Nat.lt_succ_self]
#align fin.cast_succ_lt_succ Fin.cast_succ_lt_succ

theorem le_cast_succ_iff {i : Fin (n + 1)} {j : Fin n} : i ≤ Fin.castSucc j ↔ i < j.succ := by
  simpa [lt_iff_val_lt_val, le_iff_val_le_val] using Nat.succ_le_succ_iff.symm
#align fin.le_cast_succ_iff Fin.le_cast_succ_iff

theorem cast_succ_lt_iff_succ_le {n : ℕ} {i : Fin n} {j : Fin (n + 1)} :
    Fin.castSucc i < j ↔ i.succ ≤ j := by
  simpa only [lt_iff_val_lt_val, le_iff_val_le_val, val_succ, Fin.coe_cast_succ] using
    Nat.lt_iff_add_one_le
#align fin.cast_succ_lt_iff_succ_le Fin.cast_succ_lt_iff_succ_le

@[simp]
theorem succ_last (n : ℕ) : (last n).succ = last n.succ :=
  rfl
#align fin.succ_last Fin.succ_last

@[simp]
theorem succ_eq_last_succ {n : ℕ} (i : Fin n.succ) : i.succ = last (n + 1) ↔ i = last n := by
  rw [← succ_last, (succ_injective _).eq_iff]
#align fin.succ_eq_last_succ Fin.succ_eq_last_succ

@[simp]
theorem castSucc_cast_lt (i : Fin (n + 1)) (h : (i : ℕ) < n) : castSucc (castLt i h) = i :=
  Fin.eq_of_veq rfl
#align fin.cast_succ_cast_lt Fin.castSucc_cast_lt

@[simp]
theorem cast_lt_castSucc {n : ℕ} (a : Fin n) (h : (a : ℕ) < n) : castLt (castSucc a) h = a := by
  cases a; rfl
#align fin.cast_lt_cast_succ Fin.cast_lt_castSucc

@[simp]
theorem castSucc_lt_castSucc_iff {a b : Fin n}: Fin.castSucc a < Fin.castSucc b ↔ a < b :=
  (@castSucc n).lt_iff_lt
#align fin.cast_succ_lt_cast_succ_iff Fin.castSucc_lt_castSucc_iff

theorem castSucc_injective (n : ℕ) : Injective (@Fin.castSucc n) :=
  (castSucc : Fin n ↪o _).injective
#align fin.cast_succ_injective Fin.castSucc_injective

theorem castSucc_inj {a b : Fin n} : castSucc a = castSucc b ↔ a = b :=
  (castSucc_injective n).eq_iff
#align fin.cast_succ_inj Fin.castSucc_inj

theorem castSucc_lt_last (a : Fin n) : castSucc a < last n :=
  lt_iff_val_lt_val.mpr a.is_lt
#align fin.cast_succ_lt_last Fin.castSucc_lt_last

@[simp]
theorem castSucc_zero : castSucc (0 : Fin (n + 1)) = 0 := by
  ext
  simp
#align fin.cast_succ_zero Fin.castSucc_zero

@[simp]
theorem castSucc_one {n : ℕ} : castSucc (1 : Fin (n + 2)) = 1 :=
  rfl
#align fin.cast_succ_one Fin.castSucc_one

/-- `cast_succ i` is positive when `i` is positive -/
theorem castSucc_pos {i : Fin (n + 1)} (h : 0 < i) : 0 < castSucc i := by
  simpa [lt_iff_val_lt_val] using h
#align fin.cast_succ_pos Fin.castSucc_pos

@[simp]
theorem castSucc_eq_zero_iff (a : Fin (n + 1)) : castSucc a = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| by simp).symm
#align fin.cast_succ_eq_zero_iff Fin.castSucc_eq_zero_iff

theorem castSucc_ne_zero_iff (a : Fin (n + 1)) : castSucc a ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| castSucc_eq_zero_iff a
#align fin.cast_succ_ne_zero_iff Fin.castSucc_ne_zero_iff

theorem castSucc_fin_succ (n : ℕ) (j : Fin n) : castSucc (Fin.succ j) = Fin.succ (castSucc j) := by
  simp [Fin.ext_iff]
#align fin.cast_succ_fin_succ Fin.castSucc_fin_succ

@[norm_cast, simp]
theorem coe_eq_castSucc {a : Fin n} : (a : Fin (n + 1)) = castSucc a := by
  ext
  exact val_cast_of_lt (Nat.lt.step a.is_lt)
#align fin.coe_eq_cast_succ Fin.coe_eq_castSucc

@[simp]
theorem coe_succ_eq_succ {a : Fin n} : (castSucc a) + 1 = a.succ := by
  cases n
  · exact @finZeroElim (fun _ => _) a
  · simp [a.is_lt, eq_iff_veq, add_def, Nat.mod_eq_of_lt]
#align fin.coe_succ_eq_succ Fin.coe_succ_eq_succ

theorem lt_succ {a : Fin n} : castSucc a < a.succ := by
  rw [castSucc, lt_iff_val_lt_val, coe_cast_add, val_succ]
  exact lt_add_one a.val
#align fin.lt_succ Fin.lt_succ

@[simp]
theorem range_cast_succ {n : ℕ} : Set.range (castSucc : Fin n → Fin n.succ) =
    ({ i | (i : ℕ) < n } : Set (Fin n.succ)) :=
  range_cast_le le_self_add
#align fin.range_cast_succ Fin.range_cast_succ

@[simp]
theorem coe_of_injective_cast_succ_symm {n : ℕ} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_cast_succ]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)
#align fin.coe_of_injective_cast_succ_symm Fin.coe_of_injective_cast_succ_symm

theorem succ_cast_succ {n : ℕ} (i : Fin n) : i.castSucc.succ = castSucc i.succ :=
  Fin.ext (by simp)
#align fin.succ_cast_succ Fin.succ_cast_succ

/-- `addNat m i` adds `m` to `i`, generalizes `fin.succ`. -/
def addNat (m) : Fin n ↪o Fin (n + m) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨(i : ℕ) + m, add_lt_add_right i.2 _⟩) fun i j h =>
    add_lt_add_right (show i.val < j.val from h) _
#align fin.add_nat Fin.addNat

@[simp]
theorem coe_addNat (m : ℕ) (i : Fin n) : (addNat m i : ℕ) = i + m :=
  rfl
#align fin.coe_add_nat Fin.coe_addNat

@[simp]
theorem addNat_one {i : Fin n} : addNat 1 i = i.succ := by
  ext
  rw [coe_addNat, val_succ]
#align fin.add_nat_one Fin.addNat_one

theorem le_coe_addNat (m : ℕ) (i : Fin n) : m ≤ addNat m i :=
  Nat.le_add_left _ _
#align fin.le_coe_add_nat Fin.le_coe_addNat

@[simp]
theorem addNat_mk (n i : ℕ) (hi : i < m) : addNat n ⟨i, hi⟩ = ⟨i + n, add_lt_add_right hi n⟩ :=
  rfl
#align fin.add_nat_mk Fin.addNat_mk

@[simp]
theorem cast_addNat_zero {n n' : ℕ} (i : Fin n) (h : n + 0 = n') :
    cast h (addNat 0 i) = cast ((add_zero _).symm.trans h) i :=
  ext <| add_zero _
#align fin.cast_add_nat_zero Fin.cast_addNat_zero

/-- For rewriting in the reverse direction, see `fin.cast_addNat_left`. -/
theorem addNat_cast {n n' m : ℕ} (i : Fin n') (h : n' = n) :
    addNat m (cast h i) = cast (congr_arg (. + m) h) (addNat m i) :=
  ext rfl
#align fin.add_nat_cast Fin.addNat_cast

theorem cast_addNat_left {n n' m : ℕ} (i : Fin n') (h : n' + m = n + m) :
    cast h (addNat m i) = addNat m (cast (add_right_cancel h) i) := by
  ext
  simp
#align fin.cast_add_nat_left Fin.cast_addNat_left

@[simp]
theorem cast_addNat_right {n m m' : ℕ} (i : Fin n) (h : n + m' = n + m) :
    cast h (addNat m' i) = addNat m i :=
  ext <| (congr_arg ((· + ·) (i : ℕ)) (add_left_cancel h) : _)
#align fin.cast_add_nat_right Fin.cast_addNat_right

/-- `natAdd n i` adds `n` to `i` "on the left". -/
def natAdd (n) {m} : Fin m ↪o Fin (n + m) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨n + (i : ℕ), add_lt_add_left i.2 _⟩) fun i j h =>
    add_lt_add_left (show i.val < j.val from h) _
#align fin.nat_add Fin.natAdd

@[simp]
theorem coe_nat_add (n : ℕ) {m : ℕ} (i : Fin m) : (natAdd n i : ℕ) = n + i :=
  rfl
#align fin.coe_nat_add Fin.coe_nat_add

@[simp]
theorem nat_add_mk (n i : ℕ) (hi : i < m) : natAdd n ⟨i, hi⟩ = ⟨n + i, add_lt_add_left hi n⟩ :=
  rfl
#align fin.nat_add_mk Fin.nat_add_mk

theorem le_coe_nat_add (m : ℕ) (i : Fin n) : m ≤ natAdd m i :=
  Nat.le_add_right _ _
#align fin.le_coe_nat_add Fin.le_coe_nat_add

theorem nat_add_zero {n : ℕ} : Fin.natAdd 0 = (Fin.cast (zero_add n).symm).toRelEmbedding := by
  ext
  simp
#align fin.nat_add_zero Fin.nat_add_zero

/-- For rewriting in the reverse direction, see `fin.cast_nat_add_right`. -/
theorem natAdd_cast {n n' : ℕ} (m : ℕ) (i : Fin n') (h : n' = n) :
    natAdd m (cast h i) = cast (congr_arg _ h) (natAdd m i) := by
  ext
  simp
#align fin.nat_add_cast Fin.natAdd_cast

theorem cast_nat_add_right {n n' m : ℕ} (i : Fin n') (h : m + n' = m + n) :
    cast h (natAdd m i) = natAdd m (cast (add_left_cancel h) i) := by
  ext
  simp
#align fin.cast_nat_add_right Fin.cast_nat_add_right

@[simp]
theorem cast_nat_add_left {n m m' : ℕ} (i : Fin n) (h : m' + n = m + n) :
    cast h (natAdd m' i) = natAdd m i :=
  ext <| (congr_arg (· + (i : ℕ)) (add_right_cancel h) : _)
#align fin.cast_nat_add_left Fin.cast_nat_add_left

theorem castAdd_natAdd (p m : ℕ) {n : ℕ} (i : Fin n) :
    castAdd p (natAdd m i) = cast (add_assoc _ _ _).symm (natAdd m (castAdd p i)) := by
  ext
  simp
#align fin.cast_add_nat_add Fin.castAdd_natAdd

theorem natAdd_castAdd (p m : ℕ) {n : ℕ} (i : Fin n) :
    natAdd m (castAdd p i) = cast (add_assoc _ _ _) (castAdd p (natAdd m i)) := by
  ext
  simp
#align fin.nat_add_cast_add Fin.natAdd_castAdd

theorem natAdd_natAdd (m n : ℕ) {p : ℕ} (i : Fin p) :
    natAdd m (natAdd n i) = cast (add_assoc _ _ _) (natAdd (m + n) i) :=
  ext <| (add_assoc _ _ _).symm
#align fin.nat_add_nat_add Fin.natAdd_natAdd

@[simp]
theorem cast_natAdd_zero {n n' : ℕ} (i : Fin n) (h : 0 + n = n') :
    cast h (natAdd 0 i) = cast ((zero_add _).symm.trans h) i :=
  ext <| zero_add _
#align fin.cast_nat_add_zero Fin.cast_natAdd_zero

@[simp]
theorem cast_natAdd (n : ℕ) {m : ℕ} (i : Fin m) : cast (add_comm _ _) (natAdd n i) = addNat n i :=
  ext <| add_comm _ _
#align fin.cast_nat_add Fin.cast_natAdd

@[simp]
theorem cast_addNat {n : ℕ} (m : ℕ) (i : Fin n) : cast (add_comm _ _) (addNat m i) = natAdd m i :=
  ext <| add_comm _ _
#align fin.cast_add_nat Fin.cast_addNat

@[simp]
theorem natAdd_last {m n : ℕ} : natAdd n (last m) = last (n + m) :=
  rfl
#align fin.nat_add_last Fin.natAdd_last

theorem natAdd_castSucc {m n : ℕ} {i : Fin m} : natAdd n (castSucc i) = castSucc (natAdd n i) :=
  rfl
#align fin.nat_add_cast_succ Fin.natAdd_castSucc

end Succ

section Pred

/-!
### pred
-/


-- Porting note: taken from lean3port
/-- Predecessor -/
def pred {n : ℕ} : ∀ i : Fin (n + 1), i ≠ 0 → Fin n
  | ⟨a, h₁⟩, h₂ =>
    ⟨a.pred,
      haveI : a ≠ 0 := by
        have aux₁ := vne_of_ne h₂
        dsimp at aux₁
        rw [val_zero] at aux₁
        exact aux₁
      Nat.pred_lt_pred this h₁⟩
#align fin.pred Fin.pred

@[simp]
theorem coe_pred (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : ℕ) = j - 1 := by
  cases j
  rfl
#align fin.coe_pred Fin.coe_pred

@[simp]
theorem succ_pred : ∀ (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ = i
  | ⟨0, h⟩, hi => by simp only [mk_zero, ne_eq, not_true] at hi
  | ⟨n + 1, h⟩, hi => rfl
#align fin.succ_pred Fin.succ_pred

@[simp]
theorem pred_succ (i : Fin n) {h : i.succ ≠ 0} : i.succ.pred h = i := by
  cases i
  rfl
#align fin.pred_succ Fin.pred_succ

theorem pred_eq_iff_eq_succ {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) (j : Fin n) :
    i.pred hi = j ↔ i = j.succ :=
  ⟨fun h => by simp only [← h, Fin.succ_pred], fun h => by simp only [h, Fin.pred_succ]⟩
#align fin.pred_eq_iff_eq_succ Fin.pred_eq_iff_eq_succ

@[simp]
theorem pred_mk_succ (i : ℕ) (h : i < n + 1) :
    Fin.pred ⟨i + 1, add_lt_add_right h 1⟩ (ne_of_vne (_root_.ne_of_gt (mk_succ_pos i h))) =
      ⟨i, h⟩ := by
  simp only [ext_iff, coe_pred, add_tsub_cancel_right]
#align fin.pred_mk_succ Fin.pred_mk_succ

-- This is not a simp lemma by default, because `pred_mk_succ` is nicer when it applies.
theorem pred_mk {n : ℕ} (i : ℕ) (h : i < n + 1) (w) : Fin.pred ⟨i, h⟩ w =
    ⟨i - 1, by
      rwa [tsub_lt_iff_right (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero
        (by simpa using Fin.vne_of_ne w))]⟩ :=
  rfl
#align fin.pred_mk Fin.pred_mk

@[simp]
theorem pred_le_pred_iff {n : ℕ} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha ≤ b.pred hb ↔ a ≤ b := by rw [← succ_le_succ_iff, succ_pred, succ_pred]
#align fin.pred_le_pred_iff Fin.pred_le_pred_iff

@[simp]
theorem pred_lt_pred_iff {n : ℕ} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha < b.pred hb ↔ a < b := by rw [← succ_lt_succ_iff, succ_pred, succ_pred]
#align fin.pred_lt_pred_iff Fin.pred_lt_pred_iff

@[simp]
theorem pred_inj : ∀ {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
  | ⟨0, _⟩, _, ha, _ => by simp only [mk_zero, ne_eq, not_true] at ha
  | ⟨i + 1, _⟩, ⟨0, _⟩, _, hb => by simp only [mk_zero, ne_eq, not_true] at hb
  | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, ha, hb => by simp [Fin.eq_iff_veq]
#align fin.pred_inj Fin.pred_inj

@[simp]
theorem pred_one {n : ℕ} : Fin.pred (1 : Fin (n + 2)) (Ne.symm (ne_of_lt one_pos)) = 0 := by
  ext
  simp
#align fin.pred_one Fin.pred_one

theorem pred_add_one (i : Fin (n + 2)) (h : (i : ℕ) < n + 1) :
    pred (i + 1) (_root_.ne_of_gt (add_one_pos _ (lt_iff_val_lt_val.2 h))) = castLt i h := by
  rw [ext_iff, coe_pred, coe_cast_lt, val_add', val_one', mod_eq_of_lt, add_tsub_cancel_right]
  exact add_lt_add_right h 1
#align fin.pred_add_one Fin.pred_add_one

/-- `sub_nat i h` subtracts `m` from `i`, generalizes `fin.pred`. -/
def subNat (m) (i : Fin (n + m)) (h : m ≤ (i : ℕ)) : Fin n :=
  ⟨(i : ℕ) - m, by
    rw [tsub_lt_iff_right h]
    exact i.is_lt⟩
#align fin.sub_nat Fin.subNat

@[simp]
theorem coe_sub_nat (i : Fin (n + m)) (h : m ≤ i) : (i.subNat m h : ℕ) = i - m :=
  rfl
#align fin.coe_sub_nat Fin.coe_sub_nat

@[simp]
theorem sub_nat_mk {i : ℕ} (h₁ : i < n + m) (h₂ : m ≤ i) :
    subNat m ⟨i, h₁⟩ h₂ = ⟨i - m, (tsub_lt_iff_right h₂).2 h₁⟩ :=
  rfl
#align fin.sub_nat_mk Fin.sub_nat_mk

@[simp]
theorem pred_castSucc_succ (i : Fin n) :
    pred (castSucc i.succ) (ne_of_gt (castSucc_pos i.succ_pos)) = castSucc i := by
  simp [eq_iff_veq]
#align fin.pred_cast_succ_succ Fin.pred_castSucc_succ

@[simp]
theorem addNat_subNat {i : Fin (n + m)} (h : m ≤ i) : addNat m (subNat m i h) = i :=
  ext <| tsub_add_cancel_of_le h
#align fin.add_nat_sub_nat Fin.addNat_subNat

@[simp]
theorem subNat_addNat (i : Fin n) (m : ℕ) (h : m ≤ addNat m i := le_coe_addNat m i) :
    subNat m (addNat m i) h = i :=
  ext <| add_tsub_cancel_right (i : ℕ) m
#align fin.sub_nat_add_nat Fin.subNat_addNat

@[simp]
theorem natAdd_subNat_cast {i : Fin (n + m)} (h : n ≤ i) :
    natAdd n (subNat n (cast (add_comm _ _) i) h) = i := by simp [← cast_addNat]
#align fin.nat_add_sub_nat_cast Fin.natAdd_subNat_cast

end Pred

section DivMod

/-- Compute `i / n`, where `n` is a `nat` and inferred the type of `i`. -/
def divNat (i : Fin (m * n)) : Fin m :=
  ⟨i / n, Nat.div_lt_of_lt_mul <| mul_comm m n ▸ i.prop⟩
#align fin.div_nat Fin.divNat

@[simp]
theorem coe_div_nat (i : Fin (m * n)) : (i.divNat : ℕ) = i / n :=
  rfl
#align fin.coe_div_nat Fin.coe_div_nat

/-- Compute `i % n`, where `n` is a `nat` and inferred the type of `i`. -/
def modNat (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ <| pos_of_mul_pos_right i.pos m.zero_le⟩
#align fin.mod_nat Fin.modNat

@[simp]
theorem coe_mod_nat (i : Fin (m * n)) : (i.modNat : ℕ) = i % n :=
  rfl
#align fin.coe_mod_nat Fin.coe_mod_nat

end DivMod

section Rec

/-!
### recursion and induction principles
-/


/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple. -/
@[elab_as_elim]
def succRec {C : ∀ n, Fin n → Sort _} (H0 : ∀ n, C n.succ (0 : Fin (n + 1)))
    (Hs : ∀ n i, C n i → C n.succ i.succ) : ∀ {n : ℕ} (i : Fin n), C n i
  | 0, i => i.elim0
  | Nat.succ n, ⟨0, _⟩ => by simpa using H0 n
  | Nat.succ n, ⟨Nat.succ i, h⟩ => Hs _ _ (succRec H0 Hs ⟨i, lt_of_succ_lt_succ h⟩)
#align fin.succ_rec Fin.succRec

/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple.

A version of `fin.succ_rec` taking `i : fin n` as the first argument. -/
@[elab_as_elim]
def succRecOn {n : ℕ} (i : Fin n) {C : ∀ n, Fin n → Sort _} (H0 : ∀ n, C (succ n) 0)
    (Hs : ∀ n i, C n i → C (Nat.succ n) i.succ) : C n i :=
  i.succRec H0 Hs
#align fin.succ_rec_on Fin.succRecOn

@[simp]
theorem succ_rec_on_zero {C : ∀ n, Fin n → Sort _} {H0 Hs} (n) :
    @Fin.succRecOn (succ n) 0 C H0 Hs = H0 n :=
  rfl
#align fin.succ_rec_on_zero Fin.succ_rec_on_zero

@[simp]
theorem succ_rec_on_succ {C : ∀ n, Fin n → Sort _} {H0 Hs} {n} (i : Fin n) :
    @Fin.succRecOn (succ n) i.succ C H0 Hs = Hs n i (Fin.succRecOn i H0 Hs) := by cases i <;> rfl
#align fin.succ_rec_on_succ Fin.succ_rec_on_succ

/-- Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.
-/
@[elab_as_elim]
--Porting note: marked noncomputable
noncomputable def induction {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C (castSucc i) → C i.succ) :
    ∀ i : Fin (n + 1), C i := by
  rintro ⟨i, hi⟩
  induction' i with i IH
  · rwa [Fin.mk_zero]
  · refine' hs ⟨i, lt_of_succ_lt_succ hi⟩ _
    exact IH (lt_of_succ_lt hi)
#align fin.induction Fin.induction

--Porting note: This proof became a lot more complicated
@[simp]
theorem induction_zero {C : Fin (n + 1) → Sort _} : ∀ (h0 : C 0)
    (hs : ∀ i : Fin n, C (castSucc i) → C i.succ),
    (induction h0 hs : ∀ i : Fin (n + 1), C i) 0 = h0 :=
  have : ⟨0, Nat.zero_lt_succ n⟩ = (0 : Fin (n + 1)) := by simp only [mk_zero]
  Eq.recOn (motive := fun (i : Fin (n + 1)) (h : ⟨0, Nat.zero_lt_succ n⟩ = i) =>
      ∀ (h0 : C i) (hs : ∀ i : Fin n, C (castSucc i) → C i.succ),
        (show ∀ i : Fin (n + 1), C i from induction
          (by simp [← h] at h0; exact h0) hs) i = h0)
    this
    (by intros h0 hs; simp [induction])
#align fin.induction_zero Fin.induction_zero

@[simp]
theorem induction_succ {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C (castSucc i) → C i.succ) (i : Fin n) :
    (induction h0 hs : ∀ i : Fin (n+1), C i) i.succ = hs i (induction h0 hs (castSucc i)) :=
  by cases i; rfl
#align fin.induction_succ Fin.induction_succ

/-- Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.

A version of `fin.induction` taking `i : fin (n + 1)` as the first argument.
-/
@[elab_as_elim]
noncomputable def inductionOn (i : Fin (n + 1)) {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C (castSucc i) → C i.succ) : C i :=
  induction h0 hs i
#align fin.induction_on Fin.inductionOn

/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
`i = j.succ`, `j : fin n`. -/
@[elab_as_elim]
def cases {C : Fin (succ n) → Sort _} (H0 : C 0) (Hs : ∀ i : Fin n, C i.succ) :
    ∀ i : Fin (succ n), C i :=
  induction H0 fun i _ => Hs i
#align fin.cases Fin.cases

@[simp]
theorem cases_zero {n} {C : Fin (succ n) → Sort _} {H0 Hs} : @Fin.cases n C H0 Hs 0 = H0 :=
  rfl
#align fin.cases_zero Fin.cases_zero

@[simp]
theorem cases_succ {n} {C : Fin (succ n) → Sort _} {H0 Hs} (i : Fin n) :
    @Fin.cases n C H0 Hs i.succ = Hs i := by cases i <;> rfl
#align fin.cases_succ Fin.cases_succ

@[simp]
theorem cases_succ' {n} {C : Fin (succ n) → Sort _} {H0 Hs} {i : ℕ} (h : i + 1 < n + 1) :
    @Fin.cases n C H0 Hs ⟨i.succ, h⟩ = Hs ⟨i, lt_of_succ_lt_succ h⟩ := by cases i <;> rfl
#align fin.cases_succ' Fin.cases_succ'

theorem forall_fin_succ {P : Fin (n + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin n, P i.succ :=
  ⟨fun H => ⟨H 0, fun i => H _⟩, fun ⟨H0, H1⟩ i => Fin.cases H0 H1 i⟩
#align fin.forall_fin_succ Fin.forall_fin_succ

theorem exists_fin_succ {P : Fin (n + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin n, P i.succ :=
  ⟨fun ⟨i, h⟩ => Fin.cases Or.inl (fun i hi => Or.inr ⟨i, hi⟩) i h, fun h =>
    (h.elim fun h => ⟨0, h⟩) fun ⟨i, hi⟩ => ⟨i.succ, hi⟩⟩
#align fin.exists_fin_succ Fin.exists_fin_succ

theorem forall_fin_one {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 :=
  @Unique.forall_iff (Fin 1) _ p
#align fin.forall_fin_one Fin.forall_fin_one

theorem exists_fin_one {p : Fin 1 → Prop} : (∃ i, p i) ↔ p 0 :=
  @Unique.exists_iff (Fin 1) _ p
#align fin.exists_fin_one Fin.exists_fin_one

theorem forall_fin_two {p : Fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 :=
  forall_fin_succ.trans <| and_congr_right fun _ => forall_fin_one
#align fin.forall_fin_two Fin.forall_fin_two

theorem exists_fin_two {p : Fin 2 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 :=
  exists_fin_succ.trans <| or_congr_right exists_fin_one
#align fin.exists_fin_two Fin.exists_fin_two

theorem fin_two_eq_of_eq_zero_iff {a b : Fin 2} (h : a = 0 ↔ b = 0) : a = b := by
  revert a b
  simp [forall_fin_two]
#align fin.fin_two_eq_of_eq_zero_iff Fin.fin_two_eq_of_eq_zero_iff

/--
Define `C i` by reverse induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `hlast` handles the base case on `C (fin.last n)`,
and `hs` defines the inductive step using `C i.succ`, inducting downwards.
-/
@[elab_as_elim]
def reverseInduction {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C (castSucc i)) : ∀ i : Fin (n + 1), C i
  | i =>
    if hi : i = Fin.last n then cast (by rw [hi]) hlast
    else
      let j : Fin n := ⟨i, lt_of_le_of_ne (Nat.le_of_lt_succ i.2) fun h => hi (Fin.ext h)⟩
      have wf : n + 1 - j.succ < n + 1 - i := by
        cases i
        rw [tsub_lt_tsub_iff_left_of_le] <;> simp [*, Nat.succ_le_iff]
      have hi : i = Fin.castSucc j := Fin.ext rfl
      cast (by rw [hi]) (hs _ (reverse_induction j.succ))termination_by'
  ⟨_, measure_wf fun i : Fin (n + 1) => n + 1 - i⟩
#align fin.reverse_induction Fin.reverseInduction

@[simp]
theorem reverse_induction_last {n : ℕ} {C : Fin (n + 1) → Sort _} (h0 : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C (castSucc i)) :
    (reverseInduction h0 hs (Fin.last n) : C (Fin.last n)) = h0 := by
  rw [reverseInduction] <;> simp
#align fin.reverse_induction_last Fin.reverse_induction_last

@[simp]
theorem reverse_induction_cast_succ {n : ℕ} {C : Fin (n + 1) → Sort _} (h0 : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C (castSucc i)) (i : Fin n) :
    (reverseInduction h0 hs (castSucc i) : C (castSucc i)) = hs i (reverseInduction h0 hs i.succ) :=
  by
  rw [reverseInduction, dif_neg (ne_of_lt (Fin.cast_succ_lt_last i))]
  cases i
  rfl
#align fin.reverse_induction_cast_succ Fin.reverse_induction_cast_succ

/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = fin.last n` and
`i = j.cast_succ`, `j : fin n`. -/
@[elab_as_elim, elab_strategy]
def lastCases {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C (castSucc i)) (i : Fin (n + 1)) : C i :=
  reverseInduction hlast (fun i _ => hcast i) i
#align fin.last_cases Fin.lastCases

@[simp]
theorem last_cases_last {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C (castSucc i)) :
    (Fin.lastCases hlast hcast (Fin.last n) : C (Fin.last n)) = hlast :=
  reverse_induction_last _ _
#align fin.last_cases_last Fin.last_cases_last

@[simp]
theorem last_cases_cast_succ {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C (castSucc i)) (i : Fin n) :
    (Fin.lastCases hlast hcast (Fin.castSucc i) : C (Fin.castSucc i)) = hcast i :=
  reverse_induction_cast_succ _ _ _
#align fin.last_cases_cast_succ Fin.last_cases_cast_succ

/-- Define `f : Π i : fin (m + n), C i` by separately handling the cases `i = cast_add n i`,
`j : fin m` and `i = nat_add m j`, `j : fin n`. -/
@[elab_as_elim, elab_strategy]
def addCases {m n : ℕ} {C : Fin (m + n) → Sort u} (hleft : ∀ i, C (castAdd n i))
    (hright : ∀ i, C (natAdd m i)) (i : Fin (m + n)) : C i :=
  if hi : (i : ℕ) < m then Eq.recOn (cast_add_cast_lt n i hi) (hleft (castLt i hi))
  else Eq.recOn (nat_add_sub_nat_cast (le_of_not_lt hi)) (hright _)
#align fin.add_cases Fin.addCases

@[simp]
theorem add_cases_left {m n : ℕ} {C : Fin (m + n) → Sort _} (hleft : ∀ i, C (castAdd n i))
    (hright : ∀ i, C (natAdd m i)) (i : Fin m) :
    addCases hleft hright (Fin.castAdd n i) = hleft i := by
  cases' i with i hi
  rw [addCases, dif_pos (cast_add_lt _ _)]
  rfl
#align fin.add_cases_left Fin.add_cases_left

@[simp]
theorem add_cases_right {m n : ℕ} {C : Fin (m + n) → Sort _} (hleft : ∀ i, C (castAdd n i))
    (hright : ∀ i, C (natAdd m i)) (i : Fin n) : addCases hleft hright (natAdd m i) = hright i := by
  have : ¬(natAdd m i : ℕ) < m := (le_coe_nat_add _ _).not_lt
  rw [addCases, dif_neg this]
  refine' eq_of_heq ((eq_rec_heq _ _).trans _)
  congr 1
  simp
#align fin.add_cases_right Fin.add_cases_right

end Rec

theorem lift_fun_iff_succ {α : Type _} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} :
    ((· < ·) ⇒ r) f f ↔ ∀ i : Fin n, r (f (castSucc i)) (f i.succ) := by
  constructor
  · intro H i
    exact H i.cast_succ_lt_succ
  · refine' fun H i => Fin.induction _ _
    · exact fun h => (h.not_le (zero_le i)).elim
    · intro j ihj hij
      rw [← le_cast_succ_iff] at hij
      rcases hij.eq_or_lt with (rfl | hlt)
      exacts[H j, trans (ihj hlt) (H j)]
#align fin.lift_fun_iff_succ Fin.lift_fun_iff_succ

/-- A function `f` on `fin (n + 1)` is strictly monotone if and only if `f i < f (i + 1)`
for all `i`. -/
theorem strict_mono_iff_lt_succ {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    StrictMono f ↔ ∀ i : Fin n, f (castSucc i) < f i.succ :=
  lift_fun_iff_succ (· < ·)
#align fin.strict_mono_iff_lt_succ Fin.strict_mono_iff_lt_succ

/-- A function `f` on `fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for all `i`. -/
theorem monotone_iff_le_succ {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    Monotone f ↔ ∀ i : Fin n, f (castSucc i) ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| lift_fun_iff_succ (· ≤ ·)
#align fin.monotone_iff_le_succ Fin.monotone_iff_le_succ

/-- A function `f` on `fin (n + 1)` is strictly antitone if and only if `f (i + 1) < f i`
for all `i`. -/
theorem strict_anti_iff_succ_lt {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    StrictAnti f ↔ ∀ i : Fin n, f i.succ < f (castSucc i) :=
  lift_fun_iff_succ (· > ·)
#align fin.strict_anti_iff_succ_lt Fin.strict_anti_iff_succ_lt

/-- A function `f` on `fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for all `i`. -/
theorem antitone_iff_succ_le {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f (castSucc i) :=
  antitone_iff_forall_lt.trans <| lift_fun_iff_succ (· ≥ ·)
#align fin.antitone_iff_succ_le Fin.antitone_iff_succ_le

section AddGroup

open Nat Int

/-- Negation on `fin n` -/
instance (n : ℕ) : Neg (Fin n) :=
  ⟨fun a => ⟨(n - a) % n, Nat.mod_lt _ a.pos⟩⟩

/-- Abelian group structure on `fin (n+1)`. -/
instance (n : ℕ) : AddCommGroup (Fin (n + 1)) :=
  { Fin.addCommMonoid n, Fin.hasNeg n.succ with
    add_left_neg := fun ⟨a, ha⟩ =>
      Fin.ext <|
        trans (Nat.mod_add_mod _ _ _) <| by
          rw [Fin.coe_mk, Fin.coe_zero, tsub_add_cancel_of_le, Nat.mod_self]
          exact le_of_lt ha
    sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
      Fin.ext <| show (a + (n + 1 - b)) % (n + 1) = (a + (n + 1 - b) % (n + 1)) % (n + 1) by simp
    sub := Fin.sub }

protected theorem coe_neg (a : Fin n) : ((-a : Fin n) : ℕ) = (n - a) % n :=
  rfl
#align fin.coe_neg Fin.coe_neg

protected theorem coe_sub (a b : Fin n) : ((a - b : Fin n) : ℕ) = (a + (n - b)) % n := by
  cases a; cases b; rfl
#align fin.coe_sub Fin.coe_sub

@[simp]
theorem coe_fin_one (a : Fin 1) : ↑a = 0 := by rw [Subsingleton.elim a 0]
#align fin.coe_fin_one Fin.coe_fin_one

@[simp]
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  · simp
  rw [Fin.coe_neg, Fin.val_one, Nat.succ_sub_one, Nat.mod_eq_of_lt]
  constructor
#align fin.coe_neg_one Fin.coe_neg_one

theorem coe_sub_one {n} (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  rw [sub_eq_add_neg, coe_add_eq_ite, coe_neg_one, if_pos, add_comm, add_tsub_add_eq_tsub_left]
  rw [add_comm ↑a, add_le_add_iff_left, Nat.one_le_iff_ne_zero]
  rwa [Fin.ext_iff] at h
#align fin.coe_sub_one Fin.coe_sub_one

theorem coe_sub_iff_le {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = a - b ↔ b ≤ a := by
  cases n; · exact @finZeroElim (fun _ => _) a
  rw [le_iff_val_le_val, Fin.coe_sub, ← add_tsub_assoc_of_le b.is_lt.le a]
  cases' le_or_lt (b : ℕ) a with h h
  · simp [← tsub_add_eq_add_tsub h, h, Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt a.is_lt)]
  · rw [Nat.mod_eq_of_lt, tsub_eq_zero_of_le h.le, tsub_eq_zero_iff_le, ← not_iff_not]
    · simpa [b.is_lt.trans_le le_add_self] using h
    · rwa [tsub_lt_iff_left (b.is_lt.le.trans le_add_self), add_lt_add_iff_right]
#align fin.coe_sub_iff_le Fin.coe_sub_iff_le

theorem coe_sub_iff_lt {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = n + a - b ↔ a < b := by
  cases n; · exact @finZeroElim (fun _ => _) a
  rw [lt_iff_val_lt_val, Fin.coe_sub, add_comm]
  cases' le_or_lt (b : ℕ) a with h h
  · sorry
    --simpa [add_tsub_assoc_of_le h, ← not_le, h] using
      --((Nat.mod_lt _ (Nat.succ_pos _)).trans_le le_self_add).ne
  · sorry
    --simp [← tsub_tsub_assoc b.is_lt.le h.le, ← tsub_add_eq_add_tsub b.is_lt.le,
      --Nat.mod_eq_of_lt (tsub_lt_self (Nat.succ_pos _) (tsub_pos_of_lt h)), h]
#align fin.coe_sub_iff_lt Fin.coe_sub_iff_lt

@[simp]
theorem lt_sub_one_iff {n : ℕ} {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  rcases k with ⟨_ | k, hk⟩
  simp [lt_iff_val_lt_val]
  have : (k + 1 + (n + 1)) % (n + 2) = k % (n + 2) := by
    rw [add_right_comm, add_assoc, add_mod_right]
  simp [lt_iff_val_lt_val, ext_iff, Fin.coe_sub, succ_eq_add_one, this,
    mod_eq_of_lt ((lt_succ_self _).trans hk)]
#align fin.lt_sub_one_iff Fin.lt_sub_one_iff

@[simp]
theorem le_sub_one_iff {n : ℕ} {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  · simp [Subsingleton.elim (k - 1) k, Subsingleton.elim 0 k]
  rw [← lt_sub_one_iff, le_iff_lt_or_eq, lt_sub_one_iff, or_iff_left_iff_imp, eq_comm,
    sub_eq_iff_eq_add]
  simp
#align fin.le_sub_one_iff Fin.le_sub_one_iff

@[simp]
theorem sub_one_lt_iff {n : ℕ} {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
  not_iff_not.1 <| by simp only [not_lt, le_sub_one_iff, le_zero_iff]
#align fin.sub_one_lt_iff Fin.sub_one_lt_iff

theorem last_sub (i : Fin (n + 1)) : last n - i = Fin.rev i :=
  ext <| by rw [coe_sub_iff_le.2 i.le_last, val_last, val_rev, Nat.succ_sub_succ_eq_sub]
#align fin.last_sub Fin.last_sub

end AddGroup

section SuccAbove

theorem succ_above_aux (p : Fin (n + 1)) :
    StrictMono fun i : Fin n => if (castSucc i) < p then (castSucc i) else i.succ :=
  (castSucc : Fin n ↪o _).StrictMono.ite (succEmbedding n).StrictMono
    (fun i j hij hj => lt_trans ((castSucc : Fin n ↪o _).lt_iff_lt.2 hij) hj) fun i =>
    (cast_succ_lt_succ i).le
#align fin.succ_above_aux Fin.succ_above_aux

/-- `succAbove p i` embeds `fin n` into `fin (n + 1)` with a hole around `p`. -/
def succAbove (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono _ p.succ_above_aux
#align fin.succ_above Fin.succAbove

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `cast_succ` when the resulting `i.cast_succ < p`. -/
theorem succAbove_below (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p) :
    p.succAbove i = castSucc i := if_pos h
#align fin.succ_above_below Fin.succAbove_below

@[simp]
theorem succAbove_ne_zero_zero {a : Fin (n + 2)} (ha : a ≠ 0) : a.succAbove 0 = 0 := by
  rw [Fin.succAbove_below]
  · simp
  · simp only [castSucc_zero]
    exact bot_lt_iff_ne_bot.mpr ha
#align fin.succ_above_ne_zero_zero Fin.succAbove_ne_zero_zero

theorem succAbove_eq_zero_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) :
    a.succAbove b = 0 ↔ b = 0 := by
  simp only [← succAbove_ne_zero_zero ha, OrderEmbedding.eq_iff_eq, iff_self]
#align fin.succ_above_eq_zero_iff Fin.succAbove_eq_zero_iff

theorem succAbove_ne_zero {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.succAbove b ≠ 0 :=
  mt (succAbove_eq_zero_iff ha).mp hb
#align fin.succ_above_ne_zero Fin.succAbove_ne_zero

/-- Embedding `fin n` into `fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp]
theorem succAbove_zero : ⇑(succAbove (0 : Fin (n + 1))) = Fin.succ :=
  rfl
#align fin.succ_above_zero Fin.succAbove_zero

/-- Embedding `fin n` into `fin (n + 1)` with a hole around `last n` embeds by `castSucc`. -/
@[simp]
theorem succAbove_last : succAbove (Fin.last n) = castSucc := by
  ext
  simp only [succAbove_below, castSucc_lt_last]
#align fin.succ_above_last Fin.succAbove_last

theorem succAbove_last_apply (i : Fin n) : succAbove (Fin.last n) i = castSucc i := by
  rw [succAbove_last]
#align fin.succ_above_last_apply Fin.succAbove_last_apply

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
theorem succAbove_above (p : Fin (n + 1)) (i : Fin n) (h : p ≤ castSucc i) :
    p.succAbove i = i.succ := by simp [succAbove, h.not_lt]
#align fin.succ_above_above Fin.succAbove_above

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
theorem succAbove_lt_ge (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p ≤ castSucc i :=
  lt_or_ge (castSucc i) p
#align fin.succ_above_lt_ge Fin.succAbove_lt_ge

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
theorem succAbove_lt_gt (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p < i.succ :=
  Or.casesOn (succAbove_lt_ge p i) (fun h => Or.inl h) fun h =>
    Or.inr (lt_of_le_of_lt h (cast_succ_lt_succ i))
#align fin.succ_above_lt_gt Fin.succAbove_lt_gt

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp]
theorem succAbove_lt_iff (p : Fin (n + 1)) (i : Fin n) : p.succAbove i < p ↔ castSucc i < p := by
  refine' Iff.intro _ _
  · intro h
    cases' succAbove_lt_ge p i with H H
    · exact H
    · rw [succAbove_above _ _ H] at h
      exact lt_trans (cast_succ_lt_succ i) h
  · intro h
    rw [succAbove_below _ _ h]
    exact h
#align fin.succ_above_lt_iff Fin.succAbove_lt_iff

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
theorem lt_succAbove_iff (p : Fin (n + 1)) (i : Fin n) : p < p.succAbove i ↔ p ≤ castSucc i := by
  refine' Iff.intro _ _
  · intro h
    cases' succAbove_lt_ge p i with H H
    · rw [succAbove_below _ _ H] at h
      exact le_of_lt h
    · exact H
  · intro h
    rw [succAbove_above _ _ h]
    exact lt_of_le_of_lt h (cast_succ_lt_succ i)
#align fin.lt_succ_above_iff Fin.lt_succAbove_iff

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
never results in `p` itself -/
theorem succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  intro eq
  by_cases H : castSucc i < p
  · simpa [lt_irrefl, ← succAbove_below _ _ H, Eq] using H
  · simpa [← succAbove_above _ _ (le_of_not_lt H), Eq] using castSucc_lt_succ i
#align fin.succ_above_ne Fin.succAbove_ne

/-- Embedding a positive `fin n` results in a positive fin (n + 1)` -/
theorem succAbove_pos (p : Fin (n + 2)) (i : Fin (n + 1)) (h : 0 < i) : 0 < p.succAbove i := by
  by_cases H : castSucc i < p
  · simpa [succAbove_below _ _ H] using castSucc_pos h
  · simp [succAbove_above _ _ (le_of_not_lt H)]
#align fin.succ_above_pos Fin.succAbove_pos

@[simp]
theorem succAbove_cast_lt {x y : Fin (n + 1)} (h : x < y)
    (hx : x.1 < n := lt_of_lt_of_le h y.le_last) : y.succAbove (x.castLt hx) = x := by
  rw [succAbove_below, castSucc_cast_lt]
  exact h
#align fin.succ_above_cast_lt Fin.succAbove_cast_lt

@[simp]
theorem succAbove_pred {x y : Fin (n + 1)} (h : x < y) (hy : y ≠ 0 := (x.zero_le.trans_lt h).ne') :
    x.succAbove (y.pred hy) = y := by
  rw [succAbove_above, succ_pred]
  simpa [le_iff_val_le_val] using Nat.le_pred_of_lt h
#align fin.succ_above_pred Fin.succAbove_pred

theorem cast_lt_succAbove {x : Fin n} {y : Fin (n + 1)} (h : castSucc x < y)
    (h' : (y.succAbove x).1 < n := lt_of_lt_of_le ((succAbove_lt_iff _ _).2 h) (le_last y)) :
    (y.succAbove x).castLt h' = x := by simp only [succAbove_below _ _ h, cast_lt_castSucc]
#align fin.cast_lt_succ_above Fin.cast_lt_succAbove

theorem pred_succAbove {x : Fin n} {y : Fin (n + 1)} (h : y ≤ castSucc x)
    (h' : y.succAbove x ≠ 0 := (y.zero_le.trans_lt <| (lt_succAbove_iff _ _).2 h).ne') :
    (y.succAbove x).pred h' = x := by simp only [succAbove_above _ _ h, pred_succ]
#align fin.pred_succ_above Fin.pred_succAbove

theorem exists_succAbove_eq {x y : Fin (n + 1)} (h : x ≠ y) : ∃ z, y.succAbove z = x := by
  cases' h.lt_or_lt with hlt hlt
  exacts[⟨_, succAbove_cast_lt hlt⟩, ⟨_, succAbove_pred hlt⟩]
#align fin.exists_succ_above_eq Fin.exists_succAbove_eq

@[simp]
theorem exists_succAbove_eq_iff {x y : Fin (n + 1)} : (∃ z, x.succAbove z = y) ↔ y ≠ x := by
  refine' ⟨_, exists_succAbove_eq⟩
  rintro ⟨y, rfl⟩
  exact succAbove_ne _ _
#align fin.exists_succ_above_eq_iff Fin.exists_succAbove_eq_iff

/-- The range of `p.succAbove` is everything except `p`. -/
@[simp]
theorem range_succAbove (p : Fin (n + 1)) : Set.range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff
#align fin.range_succ_above Fin.range_succAbove

@[simp]
theorem range_succ (n : ℕ) : Set.range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ := by
  rw [← succAbove_zero]
  exact range_succAbove (0 : Fin (n + 1))
#align fin.range_succ Fin.range_succ

@[simp]
theorem exists_succ_eq_iff {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 :=
  @exists_succAbove_eq_iff n 0 x
#align fin.exists_succ_eq_iff Fin.exists_succ_eq_iff

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_right_injective {x : Fin (n + 1)} : Injective (succAbove x) :=
  (succAbove x).injective
#align fin.succ_above_right_injective Fin.succAbove_right_injective

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_right_inj {x : Fin (n + 1)} : x.succAbove a = x.succAbove b ↔ a = b :=
  succAbove_right_injective.eq_iff
#align fin.succ_above_right_inj Fin.succAbove_right_inj

/-- `succAbove` is injective at the pivot -/
theorem succAbove_left_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n ↪o Fin (n + 1) => Set.range fᶜ) h
#align fin.succ_above_left_injective Fin.succAbove_left_injective

/-- `succAbove` is injective at the pivot -/
@[simp]
theorem succAbove_left_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succAbove_left_injective.eq_iff
#align fin.succ_above_left_inj Fin.succAbove_left_inj

@[simp]
theorem zero_succAbove {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)).succAbove i = i.succ := by
  ext
  simp
#align fin.zero_succ_above Fin.zero_succAbove

@[simp]
theorem succ_succAbove_zero {n : ℕ} (i : Fin n.succ) : succAbove i.succ 0 = 0 :=
  -- porting note: n + 1 times out, but n.succ works fine
  succAbove_below _ _ (succ_pos _)
#align fin.succ_succ_above_zero Fin.succ_succAbove_zero

@[simp]
theorem succ_succAbove_succ {n : ℕ} (i : Fin n.succ) (j : Fin n) :
  -- porting note: n + 1 times out, but n.succ works fine
    i.succ.succAbove j.succ = (i.succAbove j).succ :=
  (lt_or_ge (castSucc j) i).elim
    (fun h => by
      have h' : castSucc j.succ < i.succ := by simpa [lt_iff_val_lt_val] using h
      ext
      simp [succAbove_below _ _ h, succAbove_below _ _ h'])
    fun h => by
    have h' : i.succ ≤ castSucc j.succ := by simpa [le_iff_val_le_val] using h
    ext
    simp [succAbove_above _ _ h, succAbove_above _ _ h']
#align fin.succ_succ_above_succ Fin.succ_succAbove_succ

--@[simp] -- porting note: can be proved by `simp`
theorem one_succAbove_zero {n : ℕ} : (1 : Fin n.succ.succ).succAbove 0 = 0 := by
  simp
#align fin.one_succ_above_zero Fin.one_succAbove_zero

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succAbove_zero` or `succ_succAbove_zero`. -/
@[simp]
theorem succ_succAbove_one {n : ℕ} (i : Fin n.succ.succ) : i.succ.succAbove 1 = (i.succAbove 0).succ := by
  rw [← succ_zero_eq_one]
  exact succ_succAbove_succ i 0
#align fin.succ_succ_above_one Fin.succ_succAbove_one

@[simp]
theorem one_succAbove_succ {n : ℕ} (j : Fin n) :
    (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ := by
  have := succ_succAbove_succ 0 j
  rwa [succ_zero_eq_one, zero_succAbove] at this
#align fin.one_succ_above_succ Fin.one_succAbove_succ

@[simp]
theorem one_succAbove_one {n : ℕ} : (1 : Fin (n + 3)).succAbove 1 = 2 := by
  have := succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 2))
  simp only [succ_zero_eq_one, val_zero, Nat.cast_zero, zero_succAbove, succ_one_eq_two] at this
  exact this
#align fin.one_succ_above_one Fin.one_succAbove_one

end SuccAbove

section PredAbove

/-- `pred_above p i` embeds `i : fin (n+1)` into `fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i then i.pred (_root_.ne_of_lt (lt_of_le_of_lt (zero_le (castSucc p)) h)).symm
  else i.castLt (lt_of_le_of_lt (le_of_not_lt h) p.2)
#align fin.pred_above Fin.predAbove

theorem pred_above_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, coe_pred]
  · exact pred_le_pred H
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · simp at ha
    exact le_pred_of_lt (lt_of_le_of_lt ha hb)
  · exact H
#align fin.pred_above_right_monotone Fin.pred_above_right_monotone

theorem predAbove_left_monotone (i : Fin (n + 1)) : Monotone fun p => predAbove p i := fun a b H =>
  by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_le
  · rfl
#align fin.pred_above_left_monotone Fin.predAbove_left_monotone

/-- `cast_pred` embeds `i : fin (n + 2)` into `fin (n + 1)`
by lowering just `last (n + 1)` to `last n`. -/
def castPred (i : Fin (n + 2)) : Fin (n + 1) :=
  predAbove (last n) i
#align fin.cast_pred Fin.castPred

@[simp]
theorem cast_pred_zero : castPred (0 : Fin (n + 2)) = 0 := by
  ext
  simp only [val_zero]
  rfl
#align fin.cast_pred_zero Fin.cast_pred_zero

@[simp]
theorem cast_pred_one : castPred (1 : Fin (n + 2)) = 1 := by
  cases n
  · rfl
  · rfl
#align fin.cast_pred_one Fin.cast_pred_one

@[simp]
theorem pred_above_zero {i : Fin (n + 2)} (hi : i ≠ 0) : predAbove 0 i = i.pred hi := by
  dsimp [predAbove]
  rw [dif_pos]
  simp only [castSucc_zero]
  exact (pos_iff_ne_zero _).mpr hi
#align fin.pred_above_zero Fin.pred_above_zero

@[simp]
theorem cast_pred_last : castPred (last (n + 1)) = last n :=
  eq_of_veq (by simp [castPred, predAbove, castSucc_lt_last])
#align fin.cast_pred_last Fin.cast_pred_last

@[simp]
theorem cast_pred_mk (n i : ℕ) (h : i < n + 1) : castPred ⟨i, lt_succ_of_lt h⟩ = ⟨i, h⟩ := by
  have : ¬castSucc (last n) < ⟨i, lt_succ_of_lt h⟩ := by
    simpa [lt_iff_val_lt_val] using le_of_lt_succ h
  simp [castPred, predAbove, this]
#align fin.cast_pred_mk Fin.cast_pred_mk

theorem coe_cast_pred {n : ℕ} (a : Fin (n + 2)) (hx : a < Fin.last _) : (a.castPred : ℕ) = a := by
  rcases a with ⟨a, ha⟩
  rw [cast_pred_mk]
  exact hx
#align fin.coe_cast_pred Fin.coe_cast_pred

theorem pred_above_below (p : Fin (n + 1)) (i : Fin (n + 2)) (h : i ≤ castSucc p) :
    p.predAbove i = i.castPred := by
  have : i ≤ castSucc (last n) := h.trans p.le_last
  simp [predAbove, castPred, h.not_lt, this.not_lt]
#align fin.pred_above_below Fin.pred_above_below

@[simp]
theorem pred_above_last : predAbove (Fin.last n) = castPred :=
  rfl
#align fin.pred_above_last Fin.pred_above_last

theorem pred_above_last_apply (i : Fin n) : predAbove (Fin.last n) i = i.castPred := by
  rw [pred_above_last]
#align fin.pred_above_last_apply Fin.pred_above_last_apply

theorem pred_above_above (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i) :
    p.predAbove i = i.pred ((castSucc p).zero_le.trans_lt h).ne.symm := by simp [predAbove, h]
#align fin.pred_above_above Fin.pred_above_above

theorem cast_pred_monotone : Monotone (@castPred n) :=
  pred_above_right_monotone (last _)
#align fin.cast_pred_monotone Fin.cast_pred_monotone

/-- Sending `fin (n+1)` to `fin n` by subtracting one from anything above `p`
then back to `fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
theorem succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  dsimp [predAbove, succAbove]
  rcases p with ⟨p, _⟩
  rcases i with ⟨i, _⟩
  cases' lt_or_le i p with H H
  · rw [dif_neg]
    rw [if_pos]
    rfl
    exact H
    simp
    apply le_of_lt H
  · rw [dif_pos]
    rw [if_neg]
    · simp
    · simp only [pred, Fin.mk_lt_mk, not_lt]
      exact Nat.le_pred_of_lt (h.symm.lt_of_le H)
    · exact lt_of_le_of_ne H h.symm
#align fin.succ_above_pred_above Fin.succAbove_predAbove

/-- Sending `fin n` into `fin (n + 1)` with a gap at `p`
then back to `fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
theorem pred_above_succAbove (p : Fin n) (i : Fin n) :
    p.predAbove ((castSucc p).succAbove i) = i := by
  dsimp [predAbove, succAbove]
  rcases p with ⟨p, _⟩
  rcases i with ⟨i, _⟩
  dsimp
  split_ifs with h₁ h₂ h₃
  . simp only [← val_fin_lt, not_lt] at h₁ h₂
    exact (lt_le_antisymm h₁ (le_of_lt h₂)).elim
  . rfl
  . rfl
  . simp only [← val_fin_lt, not_lt] at h₁ h₃
    contradiction
#align fin.pred_above_succ_above Fin.pred_above_succAbove

theorem cast_succ_pred_eq_pred_cast_succ {a : Fin (n + 1)} (ha : a ≠ 0)
    (ha' := a.castSucc_ne_zero_iff.mpr ha) : castSucc (a.pred ha) = (castSucc a).pred ha' := by
  cases a
  rfl
#align fin.cast_succ_pred_eq_pred_cast_succ Fin.cast_succ_pred_eq_pred_cast_succ

/-- `pred` commutes with `succAbove`. -/
theorem pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succAbove_ne_zero ha hb) :
    (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  obtain hbelow | habove := lt_or_le (castSucc b) a
  -- `rwa` uses them
  · rw [Fin.succAbove_below]
    · rwa [cast_succ_pred_eq_pred_cast_succ, Fin.pred_inj, Fin.succAbove_below]
    · rwa [cast_succ_pred_eq_pred_cast_succ, pred_lt_pred_iff]
  · rw [Fin.succAbove_above]
    have : (b.pred hb).succ = b.succ.pred (Fin.succ_ne_zero _) := by rw [succ_pred, pred_succ]
    · rwa [this, Fin.pred_inj, Fin.succAbove_above]
    · rwa [cast_succ_pred_eq_pred_cast_succ, Fin.pred_le_pred_iff]
#align fin.pred_succ_above_pred Fin.pred_succAbove_pred

/-- `succ` commutes with `predAbove`. -/
@[simp]
theorem succ_pred_above_succ {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h₁ | h₂ := lt_or_le (castSucc a) b
  · rw [Fin.pred_above_above _ _ h₁, Fin.succ_pred, Fin.pred_above_above, Fin.pred_succ]
    simpa only [lt_iff_val_lt_val, coe_cast_succ, val_succ, add_lt_add_iff_right] using
      h₁
  · cases n
    · exfalso
      exact not_lt_zero' a.is_lt
    · rw [Fin.pred_above_below a b h₂,
        Fin.pred_above_below a.succ b.succ
          (by
            simpa only [le_iff_val_le_val, val_succ, coe_cast_succ, add_le_add_iff_right] using h₂)]
      ext
      have h₀ : (b : ℕ) < n + 1 := by
        simp only [le_iff_val_le_val, coe_cast_succ] at h₂
        simpa only [lt_succ_iff] using h₂.trans a.is_le
      have h₁ : (b.succ : ℕ) < n + 2 := by
        rw [← Nat.succ_lt_succ_iff] at h₀
        simpa only [val_succ] using h₀
      simp only [coe_cast_pred b h₀, coe_cast_pred b.succ h₁, coe_succ]
#align fin.succ_pred_above_succ Fin.succ_pred_above_succ

@[simp]
theorem cast_pred_castSucc (i : Fin (n + 1)) : castPred (castSucc i) = i := by
  simp [castPred, predAbove, le_last]
#align fin.cast_pred_cast_succ Fin.cast_pred_castSucc

theorem cast_succ_cast_pred {i : Fin (n + 2)} (h : i < last _) : castSucc i.castPred = i := by
  rw [castPred, predAbove, dif_neg]
  · simp [Fin.eq_iff_veq]
  · exact h.not_le
#align fin.cast_succ_cast_pred Fin.cast_succ_cast_pred

theorem coe_cast_pred_le_self (i : Fin (n + 2)) : (i.castPred : ℕ) ≤ i := by
  rcases i.le_last.eq_or_lt with (rfl | h)
  · simp
  · rw [castPred, predAbove, dif_neg]
    · simp
    · simpa [lt_iff_val_lt_val, le_iff_val_le_val, lt_succ_iff] using h
#align fin.coe_cast_pred_le_self Fin.coe_cast_pred_le_self

theorem coe_cast_pred_lt_iff {i : Fin (n + 2)} : (i.castPred : ℕ) < i ↔ i = Fin.last _ := by
  rcases i.le_last.eq_or_lt with (rfl | H)
  · simp
  · simp only [_root_.ne_of_lt H]
    rw [← cast_succ_cast_pred H]
    simp
#align fin.coe_cast_pred_lt_iff Fin.coe_cast_pred_lt_iff

theorem lt_last_iff_coe_cast_pred {i : Fin (n + 2)} : i < Fin.last _ ↔ (i.castPred : ℕ) = i := by
  rcases i.le_last.eq_or_lt with (rfl | H)
  · simp
  · simp only [H]
    rw [← cast_succ_cast_pred H]
    simp
#align fin.lt_last_iff_coe_cast_pred Fin.lt_last_iff_coe_cast_pred

end PredAbove

/-- `min n m` as an element of `fin (m + 1)` -/
def clamp (n m : ℕ) : Fin (m + 1) :=
  OfNat.ofNat <| min n m
#align fin.clamp Fin.clamp

@[simp]
theorem coe_clamp (n m : ℕ) : (clamp n m : ℕ) = min n m :=
  Nat.mod_eq_of_lt <| Nat.lt_succ_iff.mpr <| min_le_right _ _
#align fin.coe_clamp Fin.coe_clamp

-- Porting note: this is probably not needed anymore
/-@[simp]
theorem coe_of_nat_eq_mod (m n : ℕ) : ((n : Fin (succ m)) : ℕ) = n % succ m := by
  rw [← of_nat_eq_coe] <;> rfl
#align fin.coe_of_nat_eq_mod Fin.coe_of_nat_eq_mod-/
#noalign fin.coe_of_nat_eq_mod

@[simp]
theorem coe_of_nat_eq_mod' (m n : ℕ) [NeZero m] :
    (@Fin.ofNat' m n (Nat.pos_of_ne_zero (NeZero.ne m)) : ℕ) = n % m :=
    -- Porting note: this looks horrible
  rfl
#align fin.coe_of_nat_eq_mod' Fin.coe_of_nat_eq_mod'

section Mul

/-!
### mul
-/


theorem val_mul {n : ℕ} : ∀ a b : Fin n, (a * b).val = a.val * b.val % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl
#align fin.val_mul Fin.val_mul

theorem coe_mul {n : ℕ} : ∀ a b : Fin n, ((a * b : Fin n) : ℕ) = a * b % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl
#align fin.coe_mul Fin.coe_mul

@[simp]
protected theorem mul_one (k : Fin (n + 1)) : k * 1 = k := by
  cases n
  simp
  simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)]
#align fin.mul_one Fin.mul_one

@[simp]
protected theorem one_mul (k : Fin (n + 1)) : (1 : Fin (n + 1)) * k = k := by
  cases n
  simp
  simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)]
#align fin.one_mul Fin.one_mul

@[simp]
protected theorem mul_zero (k : Fin (n + 1)) : k * 0 = 0 := by simp [eq_iff_veq, mul_def]
#align fin.mul_zero Fin.mul_zero

@[simp]
protected theorem zero_mul (k : Fin (n + 1)) : (0 : Fin (n + 1)) * k = 0 := by
  simp [eq_iff_veq, mul_def]
#align fin.zero_mul Fin.zero_mul

end Mul

section

-- Note that here we are disabling the "safety" of reflected, to allow us to reuse `nat.mk_numeral`.
-- The usual way to provide the required `reflected` instance would be via rewriting to prove that
-- the expression we use here is equivalent.
attribute [local semireducible] reflected

unsafe instance reflect : ∀ n, has_reflect (Fin n)
  | 0 => finZeroElim
  | n + 1 =>
    nat.mk_numeral q(Fin n.succ) q((by infer_instance : Zero (Fin n.succ)))
        q((by infer_instance : One (Fin n.succ))) q((by infer_instance : Add (Fin n.succ))) ∘
      Fin.val
#align fin.reflect fin.reflect

end

end Fin
