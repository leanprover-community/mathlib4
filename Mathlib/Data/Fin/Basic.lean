/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.WithZero
import Mathlib.Init.Data.Fin.Basic
import Mathlib.Order.RelIso.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Order.Hom.Set
import Std.Data.Fin.Basic

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

### Order embeddings and an order isomorphism

* `Fin.orderIsoSubtype` : coercion to `{ i // i < n }` as an `OrderIso`;
* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.valOrderEmbedding` : coercion to natural numbers as an `OrderEmbedding`;
* `Fin.succEmbedding` : `Fin.succ` as an `OrderEmbedding`;
* `Fin.castLEEmb h` : `Fin.castLE` as an `OrderEmbedding`, embed `Fin n` into `Fin m`, `h : n ≤ m`;
* `Fin.castIso` : `Fin.cast` as an `OrderIso`, order isomorphism between `Fin n` and `Fin m`
  provided that `n = m`, see also `Equiv.finCongr`;
* `Fin.castAddEmb m` : `Fin.castAdd` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccEmb` : `Fin.castSucc` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.succAboveEmb p` : `Fin.succAbove` as an `OrderEmbedding`, embed `Fin n` into `Fin (n + 1)`
  with a hole around `p`;
* `Fin.addNatEmb m i` : `Fin.addNat` as an `OrderEmbedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddEmb n i` : `Fin.natAdd` as an `OrderEmbedding`, adds `n` on `i` on the left;

### Other casts

* `Fin.ofNat'`: given a positive number `n` (deduced from `[NeZero n]`), `Fin.ofNat' i` is
  `i % n` interpreted as an element of `Fin n`;
* `Fin.divNat i` : divides `i : Fin (m * n)` by `n`;
* `Fin.modNat i` : takes the mod of `i : Fin (m * n)` by `n`;

### Misc definitions

* `Fin.revPerm : Equiv.Perm (Fin n)` : `Fin.rev` as an `Equiv.Perm`, the antitone involution given
  by `i ↦ n-(i+1)`

-/

set_option autoImplicit true

universe u v

open Fin Nat Function

/-- Elimination principle for the empty set `Fin 0`, dependent version. -/
def finZeroElim {α : Fin 0 → Sort*} (x : Fin 0) : α x :=
  x.elim0
#align fin_zero_elim finZeroElim

namespace Fin

instance : CanLift ℕ (Fin n) Fin.val (· < n) where
  prf k hk := ⟨⟨k, hk⟩, rfl⟩

/-- A non-dependent variant of `elim0`. -/
def elim0' {α : Sort*} (x : Fin 0) : α :=
  x.elim0
#align fin.elim0' Fin.elim0'

variable {n m : ℕ}
--variable {a b : Fin n} -- this *really* breaks stuff

#align fin.fin_to_nat Fin.coeToNat

theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_veq n
#align fin.val_injective Fin.val_injective

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
lemma size_positive : Fin n → 0 < n
  | ⟨x, h⟩ =>
    match Nat.eq_or_lt_of_le (Nat.zero_le x) with
    | Or.inl h_eq => h_eq ▸ h
    | Or.inr h_lt => Nat.lt_trans h_lt h

lemma size_positive' [Nonempty (Fin n)] : 0 < n :=
  ‹Nonempty (Fin n)›.elim fun i ↦ Fin.size_positive i

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

theorem lt_iff_val_lt_val {a b : Fin n} : a < b ↔ (a : ℕ) < b :=
  Iff.rfl
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

instance {n : ℕ} : LinearOrder (Fin n) :=
  @LinearOrder.liftWithOrd (Fin n) _ _ ⟨fun x y => ⟨max x y, max_rec' (· < n) x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' (· < n) x.2 y.2⟩⟩ _ Fin.val Fin.val_injective (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

#align fin.mk_le_mk Fin.mk_le_mk
#align fin.mk_lt_mk Fin.mk_lt_mk

-- @[simp] -- Porting note: simp can prove this
theorem min_val {a : Fin n} : min (a : ℕ) n = a := by simp
#align fin.min_coe Fin.min_val

-- @[simp] -- Porting note: simp can prove this
theorem max_val {a : Fin n} : max (a : ℕ) n = n := by simp
#align fin.max_coe Fin.max_val

instance {n : ℕ} : PartialOrder (Fin n) := by infer_instance

theorem val_strictMono : StrictMono (val : Fin n → ℕ) := fun _ _ => id
#align fin.coe_strict_mono Fin.val_strictMono

/-- The equivalence `Fin n ≃ { i // i < n }` is an order isomorphism. -/
@[simps! apply symm_apply]
def orderIsoSubtype : Fin n ≃o { i // i < n } :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])
#align fin.order_iso_subtype Fin.orderIsoSubtype
#align fin.order_iso_subtype_symm_apply Fin.orderIsoSubtype_symm_apply
#align fin.order_iso_subtype_apply Fin.orderIsoSubtype_apply

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
@[simps! apply]
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
def factorial {n : ℕ} : Fin n → ℕ
  | ⟨0, _⟩ := 1
  | ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : ℕ} : WellFoundedRelation (Fin n) :=
  measure (val : Fin n → ℕ)

/-- Given a positive `n`, `Fin.ofNat' i` is `i % n` as an element of `Fin n`. -/
def ofNat'' [NeZero n] (i : ℕ) : Fin n :=
  ⟨i % n, mod_lt _ <| NeZero.pos n⟩
#align fin.of_nat' Fin.ofNat''ₓ
-- porting note: `Fin.ofNat'` conflicts with something in core (there the hypothesis is `n > 0`),
-- so for now we make this double-prime `''`. This is also the reason for the dubious translation.

instance {n : ℕ} [NeZero n] : Zero (Fin n) := ⟨ofNat'' 0⟩
instance {n : ℕ} [NeZero n] : One (Fin n) := ⟨ofNat'' 1⟩

#align fin.coe_zero Fin.val_zero

/--
The `Fin.val_zero` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem val_zero' (n : ℕ) [NeZero n] : ((0 : Fin n) : ℕ) = 0 :=
  rfl
#align fin.val_zero' Fin.val_zero'

#align fin.mk_zero Fin.mk_zero

/--
The `Fin.zero_le` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
protected theorem zero_le' [NeZero n] (a : Fin n) : 0 ≤ a :=
  Nat.zero_le a.val
#align fin.zero_le Fin.zero_le'

#align fin.zero_lt_one Fin.zero_lt_one
#align fin.not_lt_zero Fin.not_lt_zero

/--
The `Fin.pos_iff_ne_zero` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem pos_iff_ne_zero' [NeZero n] (a : Fin n) : 0 < a ↔ a ≠ 0 := by
  rw [← val_fin_lt, val_zero', _root_.pos_iff_ne_zero, Ne.def, Ne.def, ext_iff, val_zero']
#align fin.pos_iff_ne_zero Fin.pos_iff_ne_zero'

theorem lt_last_iff_ne_last {a : Fin (n + 1)}: a < last _ ↔ a ≠ last _ := (le_last _).lt_iff_ne

#align fin.eq_zero_or_eq_succ Fin.eq_zero_or_eq_succ
#align fin.eq_succ_of_ne_zero Fin.eq_succ_of_ne_zero

@[simp] lemma cast_eq_self (a : Fin n) : cast rfl a = a := rfl

theorem rev_involutive : Involutive (rev : Fin n → Fin n) := fun i =>
  ext <| by
    dsimp only [rev]
    rw [← tsub_tsub, tsub_tsub_cancel_of_le (Nat.add_one_le_iff.2 i.is_lt),
      add_tsub_cancel_right]
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

/-- `Fin.rev n` as an order-reversing isomorphism. -/
@[simps! apply toEquiv]
def revOrderIso {n} : (Fin n)ᵒᵈ ≃o Fin n :=
  ⟨OrderDual.ofDual.trans revPerm, rev_le_rev⟩
#align fin.rev_order_iso Fin.revOrderIso
#align fin.rev_order_iso_apply Fin.revOrderIso_apply
#align fin.rev_order_iso_to_equiv Fin.revOrderIso_toEquiv

@[simp]
theorem revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual (rev i) :=
  rfl
#align fin.rev_order_iso_symm_apply Fin.revOrderIso_symm_apply

theorem cast_rev (i : Fin n) (h : n = m) :
    cast h i.rev = (i.cast h).rev := by
  subst h; simp

theorem rev_eq_iff {i j : Fin n} : rev i = j ↔ i = rev j := by
  rw [← rev_inj, rev_rev]

theorem rev_ne_iff {i j : Fin n} : rev i ≠ j ↔ i ≠ rev j := rev_eq_iff.not

#align fin.last Fin.last
#align fin.coe_last Fin.val_last

-- porting note: this is now syntactically equal to `val_last`
#align fin.last_val Fin.val_last
#align fin.le_last Fin.le_last

instance : BoundedOrder (Fin (n + 1)) where
  top := last n
  le_top := le_last
  bot := 0
  bot_le := zero_le

instance : Lattice (Fin (n + 1)) :=
  LinearOrder.toLattice

#align fin.last_pos Fin.last_pos
#align fin.eq_last_of_not_lt Fin.eq_last_of_not_lt

theorem last_pos' [NeZero n] : 0 < last n := NeZero.pos n

theorem one_lt_last [NeZero n] : 1 < last (n + 1) := (lt_add_iff_pos_left 1).mpr (NeZero.pos n)

theorem top_eq_last (n : ℕ) : ⊤ = Fin.last n :=
  rfl
#align fin.top_eq_last Fin.top_eq_last

theorem bot_eq_zero (n : ℕ) : ⊥ = (0 : Fin (n + 1)) :=
  rfl
#align fin.bot_eq_zero Fin.bot_eq_zero

section

variable {α : Type*} [Preorder α]

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
    -- porting note: convert was abusing definitional equality
    have : _ < i := this
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
### addition, numerals, and coercion from Nat
-/

#align fin.val_one Fin.val_one
#align fin.coe_one Fin.val_one

@[simp]
theorem val_one' (n : ℕ) [NeZero n] : ((1 : Fin n) : ℕ) = 1 % n :=
  rfl
#align fin.coe_one' Fin.val_one'

--Porting note: Delete this lemma after porting
theorem val_one'' {n : ℕ} : ((1 : Fin (n + 1)) : ℕ) = 1 % (n + 1) :=
  rfl
#align fin.one_val Fin.val_one''

theorem castSucc_one' [NeZero n] : castSucc (1 : Fin (n + 1)) = 1 := by
  rw [ext_iff, coe_castSucc, val_one', val_one, mod_succ_eq_iff_lt, succ_eq_one_add,
  lt_add_iff_pos_right]
  exact NeZero.pos n

#align fin.mk_one Fin.mk_one

instance nontrivial {n : ℕ} : Nontrivial (Fin (n + 2)) where
  exists_pair_ne := ⟨0, 1, (ne_iff_vne 0 1).mpr (by simp [val_one, val_zero])⟩

theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  rcases n with (_ | _ | n) <;>
  simp [← Nat.one_eq_succ_zero, Fin.nontrivial, not_nontrivial, Nat.succ_le_iff]
-- porting note: here and in the next lemma, had to use `← Nat.one_eq_succ_zero`.
#align fin.nontrivial_iff_two_le Fin.nontrivial_iff_two_le

#align fin.subsingleton_iff_le_one Fin.subsingleton_iff_le_one

section Monoid

instance addCommSemigroup (n : ℕ) : AddCommSemigroup (Fin n) where
  add := (· + ·)
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc]
  add_comm := by simp [eq_iff_veq, add_def, add_comm]
#align fin.add_comm_semigroup Fin.addCommSemigroup

--Porting note: removing `simp`, `simp` can prove it with AddCommMonoid instance
protected theorem add_zero [NeZero n] (k : Fin n) : k + 0 = k := by
  simp only [add_def, val_zero', add_zero, mod_eq_of_lt (is_lt k)]
#align fin.add_zero Fin.add_zero

--Porting note: removing `simp`, `simp` can prove it with AddCommMonoid instance
protected theorem zero_add [NeZero n] (k : Fin n) : 0 + k = k := by
  simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]
#align fin.zero_add Fin.zero_add

instance [NeZero n] : OfNat (Fin n) a where
  ofNat := Fin.ofNat' a (NeZero.pos n)

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

@[simp] lemma ofNat'_zero [NeZero n] : (Fin.ofNat' 0 h : Fin n) = 0 := rfl
@[simp] lemma ofNat'_one [NeZero n] : (Fin.ofNat' 1 h : Fin n) = 1 := rfl

end from_ad_hoc

instance (n) : AddCommSemigroup (Fin n) where
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc]
  add_comm := by simp [eq_iff_veq, add_def, add_comm]

instance addCommMonoid (n : ℕ) [NeZero n] : AddCommMonoid (Fin n) where
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  __ := Fin.addCommSemigroup n
#align fin.add_comm_monoid Fin.addCommMonoid

instance instAddMonoidWithOne (n) [NeZero n] : AddMonoidWithOne (Fin n) where
  __ := inferInstanceAs (AddCommMonoid (Fin n))
  natCast n := Fin.ofNat'' n
  natCast_zero := rfl
  natCast_succ _ := eq_of_veq (add_mod _ _ _)
#align fin.add_monoid_with_one Fin.instAddMonoidWithOne

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
      simp
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
  eq_of_veq (Nat.mod_eq_of_lt h).symm
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

--- porting note: syntactically the same as the above
#align fin.coe_two Fin.val_two

section OfNatCoe

@[simp]
theorem ofNat''_eq_cast (n : ℕ) [NeZero n] (a : ℕ) : (Fin.ofNat'' a : Fin n) = a :=
  rfl
#align fin.of_nat_eq_coe Fin.ofNat''_eq_cast

@[simp] lemma val_nat_cast (a n : ℕ) [NeZero n] : (a : Fin n).val = a % n := rfl

-- porting note: is this the right name for things involving `Nat.cast`?
/-- Converting an in-range number to `Fin (n + 1)` produces a result
whose value is the original number.  -/
theorem val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) : (a : Fin n).val = a :=
  Nat.mod_eq_of_lt h
#align fin.coe_val_of_lt Fin.val_cast_of_lt

/-- Converting the value of a `Fin (n + 1)` to `Fin (n + 1)` results
in the same value.  -/
theorem cast_val_eq_self {n : ℕ} [NeZero n] (a : Fin n) : (a.val : Fin n) = a :=
  ext <| val_cast_of_lt a.isLt
#align fin.coe_val_eq_self Fin.cast_val_eq_self

-- porting note: this is syntactically the same as `val_cast_of_lt`
#align fin.coe_coe_of_lt Fin.val_cast_of_lt

-- porting note: this is syntactically the same as `cast_val_of_lt`
#align fin.coe_coe_eq_self Fin.cast_val_eq_self

@[simp] lemma nat_cast_self (n : ℕ) [NeZero n] : (n : Fin n) = 0 := by ext; simp

@[simp] lemma nat_cast_eq_zero {a n : ℕ} [NeZero n] : (a : Fin n) = 0 ↔ n ∣ a := by
  simp [eq_iff_veq, Nat.dvd_iff_mod_eq_zero]

@[simp]
theorem cast_nat_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by ext; simp
#align fin.coe_nat_eq_last Fin.cast_nat_eq_last

theorem le_val_last (i : Fin (n + 1)) : i ≤ n := by
  rw [Fin.cast_nat_eq_last]
  exact Fin.le_last i
#align fin.le_coe_last Fin.le_val_last

end OfNatCoe

#align fin.add_one_pos Fin.add_one_pos
#align fin.one_pos Fin.one_pos
#align fin.zero_ne_one Fin.zero_ne_one

@[simp]
theorem one_eq_zero_iff [NeZero n] : (1 : Fin n) = 0 ↔ n = 1 := by
  rw [← Nat.cast_one, nat_cast_eq_zero, Nat.dvd_one]
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

/-- `Fin.succ` as an `OrderEmbedding` -/
def succEmbedding (n : ℕ) : Fin n ↪o Fin (n + 1) :=
  (OrderEmbedding.ofStrictMono Fin.succ) fun _ _ h => succ_lt_succ h
#align fin.succ_embedding Fin.succEmbedding

lemma strictMono_succ {n : ℕ} : StrictMono (succ : Fin n → Fin (n + 1)) :=
  (succEmbedding _).strictMono

@[simp]
theorem val_succEmbedding : ⇑(succEmbedding n) = Fin.succ :=
  rfl
#align fin.coe_succ_embedding Fin.val_succEmbedding

#align fin.succ_le_succ_iff Fin.succ_le_succ_iff
#align fin.succ_lt_succ_iff Fin.succ_lt_succ_iff

theorem succ_injective (n : ℕ) : Injective (@Fin.succ n) :=
  (succEmbedding n).injective
#align fin.succ_injective Fin.succ_injective

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
The `Fin.succ_one_eq_two` in `Std` only applies in `Fin (n+2)`.
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
The `Fin.le_zero_iff` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem le_zero_iff' {n : ℕ} [NeZero n] {k : Fin n} : k ≤ 0 ↔ k = 0 :=
  ⟨fun h => Fin.eq_of_veq <| by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact le_refl _⟩
#align fin.le_zero_iff Fin.le_zero_iff'

#align fin.succ_succ_ne_one Fin.succ_succ_ne_one
#align fin.cast_lt Fin.castLT
#align fin.coe_cast_lt Fin.coe_castLT
#align fin.cast_lt_mk Fin.castLT_mk

-- Move to Std?
@[simp] theorem cast_refl {n : Nat} (h : n = n) :
    Fin.cast h = id := rfl

@[simp]
theorem castLT_lt_castLT_iff {m n: ℕ} {a b : Fin m} (ha : a < n) (hb : b < n) :
    castLT a ha < castLT b hb ↔ a < b := Iff.rfl

@[simp]
theorem castLT_le_castLT_iff {m n: ℕ} {a b : Fin m} (ha : a < n) (hb : b < n) :
    castLT a ha ≤ castLT b hb ↔ a ≤ b := Iff.rfl

theorem strictMono_castLE (h : n ≤ m) : StrictMono (castLE h : Fin n → Fin m) :=
  fun _ _ h => h

/-- `Fin.castLE` as an `OrderEmbedding`, `castLEEmb h i` embeds `i` into a larger `Fin` type.  -/
@[simps! apply toEmbedding]
def castLEEmb (h : n ≤ m) : Fin n ↪o Fin m :=
  OrderEmbedding.ofStrictMono (castLE h) (strictMono_castLE h)
#align fin.cast_le Fin.castLEEmb

#align fin.coe_cast_le Fin.coe_castLE
#align fin.cast_le_mk Fin.castLE_mk
#align fin.cast_le_zero Fin.castLE_zero

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
theorem coe_of_injective_castLEEmb_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLEEmb h).injective).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_castLE h]
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)
#align fin.coe_of_injective_cast_le_symm Fin.coe_of_injective_castLEEmb_symm

#align fin.cast_le_succ Fin.castLE_succ
#align fin.cast_le_cast_le Fin.castLE_castLE
#align fin.cast_le_comp_cast_le Fin.castLE_comp_castLE

theorem leftInverse_cast (eq : n = m) : LeftInverse (cast eq.symm) (cast eq) :=
  fun _ => eq_of_veq rfl

theorem rightInverse_cast (eq : n = m) : RightInverse (cast eq.symm) (cast eq) :=
  fun _ => eq_of_veq rfl

theorem cast_le_cast (eq : n = m) {a b : Fin n} : cast eq a ≤ cast eq b ↔ a ≤ b :=
  Iff.rfl

/-- `Fin.cast` as an `OrderIso`, `castIso eq i` embeds `i` into an equal `Fin` type,
see also `Equiv.finCongr`. -/
@[simps]
def castIso (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨cast eq, cast eq.symm, leftInverse_cast eq, rightInverse_cast eq⟩
  map_rel_iff' := cast_le_cast eq
#align fin.cast Fin.castIso

@[simp]
theorem symm_castIso (h : n = m) : (castIso h).symm = castIso h.symm := by
  simp [eq_iff_true_of_subsingleton]
#align fin.symm_cast Fin.symm_castIso

#align fin.coe_cast Fin.coe_castₓ

@[simp]
theorem cast_zero {n' : ℕ} [NeZero n] {h : n = n'} : cast h (0 : Fin n) =
    by { haveI : NeZero n' := by {rw [← h]; infer_instance}; exact 0} :=
  ext rfl
#align fin.cast_zero Fin.cast_zero

#align fin.cast_last Fin.cast_lastₓ

#align fin.cast_mk Fin.cast_mkₓ

#align fin.cast_trans Fin.cast_transₓ

@[simp]
theorem castIso_refl (h : n = n := rfl) : castIso h = OrderIso.refl (Fin n) := by
  ext
  simp
#align fin.cast_refl Fin.castIso_refl

#align fin.cast_le_of_eq Fin.castLE_of_eq

/-- While in many cases `Fin.castIso` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem castIso_to_equiv (h : n = m) : (castIso h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h
  simp
#align fin.cast_to_equiv Fin.castIso_to_equiv

/-- While in many cases `Fin.cast` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_eq_cast (h : n = m) : (cast h : Fin n → Fin m) = _root_.cast (h ▸ rfl) := by
  subst h
  ext
  rfl
#align fin.cast_eq_cast Fin.cast_eq_cast

theorem strictMono_castAdd (m) : StrictMono (castAdd m : Fin n → Fin (n + m)) :=
  strictMono_castLE (Nat.le_add_right n m)

/-- `Fin.castAdd` as an `OrderEmbedding`, `castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`.
See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
@[simps! apply toEmbedding]
def castAddEmb (m) : Fin n ↪o Fin (n + m) :=
  OrderEmbedding.ofStrictMono (castAdd m) (strictMono_castAdd m)
#align fin.cast_add Fin.castAddEmb

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

theorem strictMono_castSucc : StrictMono (castSucc : Fin n → Fin (n + 1)) :=
  strictMono_castAdd 1

/-- `Fin.castSucc` as an `OrderEmbedding`, `castSuccEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[simps! apply toEmbedding]
def castSuccEmb : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono castSucc strictMono_castSucc
#align fin.cast_succ Fin.castSuccEmb

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
theorem castSucc_le_castSucc_iff : castSucc a ≤ castSucc b ↔ a ≤ b := Iff.rfl
@[simp]
theorem succ_le_castSucc_iff : succ a ≤ castSucc b ↔ a < b :=
  by rw [le_castSucc_iff, succ_lt_succ_iff]
@[simp]
theorem castSucc_lt_succ_iff : castSucc a < succ b ↔ a ≤ b :=
  by rw [castSucc_lt_iff_succ_le, succ_le_succ_iff]

@[simp]
theorem castSucc_ne_succ : castSucc a ≠ succ a := (castSucc_lt_succ _).ne
@[simp]
theorem succ_ne_castSucc : succ a ≠ castSucc a := (castSucc_lt_succ _).ne'
@[simp]
theorem castSucc_castSucc_ne_succ_succ {a : Fin n} : castSucc a.castSucc ≠ succ a.succ :=
  (castSucc_lt_succ_iff.mpr (castSucc_lt_succ _).le).ne

theorem le_of_castSucc_lt_of_succ_lt {a b : Fin (n + 1)} {i : Fin n}
    (hl : castSucc i < a) (hu : b < succ i) : b < a := (castSucc_lt_iff_succ_le.mp hl).trans_lt' hu

theorem castSucc_lt_or_lt_succ (i : Fin n) (p : Fin (n + 1)) : castSucc i < p ∨ p < i.succ :=
  Or.casesOn (lt_or_le (castSucc i) p) (fun h => Or.inl h) fun h =>
    Or.inr (lt_of_le_of_lt h (castSucc_lt_succ i))
#align fin.succ_above_lt_gt Fin.castSucc_lt_or_lt_succ

theorem succ_le_or_le_castSucc (i : Fin n) (p : Fin (n + 1)) : succ i ≤ p ∨ p ≤ i.castSucc := by
  rw [le_castSucc_iff, ← castSucc_lt_iff_succ_le]
  exact i.castSucc_lt_or_lt_succ p

@[simp]
theorem exists_succ_eq {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 :=
  ⟨fun ⟨_, hy⟩ => hy ▸ succ_ne_zero _, x.cases (fun h => h.irrefl.elim) (fun _ _ => ⟨_, rfl⟩)⟩
#align fin.exists_succ_eq Fin.exists_succ_eq

theorem exists_succ_eq_of_ne_zero {x : Fin (n + 1)} (h : x ≠ 0) :
    ∃ y, Fin.succ y = x := exists_succ_eq.mpr h

theorem exists_castSucc_eq_of_ne_last {x : Fin (n + 1)} (h : x ≠ (last _)) :
    ∃ y, Fin.castSucc y = x := exists_castSucc_eq.mpr h

theorem castSucc_injective (n : ℕ) : Injective (@Fin.castSucc n) :=
  (castSuccEmb : Fin n ↪o _).injective
#align fin.cast_succ_injective Fin.castSucc_injective

#align fin.cast_succ_inj Fin.castSucc_inj
#align fin.cast_succ_lt_last Fin.castSucc_lt_last

/--
The `Fin.castSucc_zero` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem castSucc_zero' [NeZero n] : castSucc (0 : Fin n) = 0 :=
  ext rfl
#align fin.cast_succ_zero Fin.castSucc_zero'
#align fin.cast_succ_one Fin.castSucc_one

/-- `castSucc i` is positive when `i` is positive.

The `Fin.castSucc_pos` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.-/
theorem castSucc_pos' [NeZero n] {i : Fin n} (h : 0 < i) : 0 < castSucc i := by
  simpa [lt_iff_val_lt_val] using h
#align fin.cast_succ_pos Fin.castSucc_pos'

/--
The `Fin.castSucc_eq_zero_iff` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem castSucc_eq_zero_iff' [NeZero n] (a : Fin n) : castSucc a = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| by simp).symm
#align fin.cast_succ_eq_zero_iff Fin.castSucc_eq_zero_iff'

/--
The `Fin.castSucc_ne_zero_iff` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem castSucc_ne_zero_iff' [NeZero n] (a : Fin n) : castSucc a ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| castSucc_eq_zero_iff' a
#align fin.cast_succ_ne_zero_iff Fin.castSucc_ne_zero_iff

theorem succ_ne_last_iff (a : Fin (n + 1)) : succ a ≠ last (n + 1) ↔ a ≠ last n :=
  not_iff_not.mpr <| succ_eq_last_succ a

#align fin.cast_succ_fin_succ Fin.castSucc_fin_succ

@[norm_cast, simp]
theorem coe_eq_castSucc {a : Fin n} : (a : Fin (n + 1)) = castSucc a := by
  ext
  exact val_cast_of_lt (Nat.lt.step a.is_lt)
#align fin.coe_eq_cast_succ Fin.coe_eq_castSucc

#align fin.coe_succ_eq_succ Fin.coeSucc_eq_succ
#align fin.lt_succ Fin.lt_succ

@[simp]
theorem range_castSucc {n : ℕ} : Set.range (castSucc : Fin n → Fin n.succ) =
    ({ i | (i : ℕ) < n } : Set (Fin n.succ)) :=
  range_castLE le_self_add
#align fin.range_cast_succ Fin.range_castSucc

@[simp]
theorem coe_of_injective_castSucc_symm {n : ℕ} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_castSucc]
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)
#align fin.coe_of_injective_cast_succ_symm Fin.coe_of_injective_castSucc_symm

#align fin.succ_cast_succ Fin.succ_castSucc

theorem strictMono_addNat (m) : StrictMono ((addNat · m) : Fin n → Fin (n + m)) :=
  fun i j h => add_lt_add_right (show i.val < j.val from h) _

/-- `Fin.addNat` as an `OrderEmbedding`, `addNatEmb m i` adds `m` to `i`, generalizes
`Fin.succ`. -/
@[simps! apply toEmbedding]
def addNatEmb (m) : Fin n ↪o Fin (n + m) :=
  OrderEmbedding.ofStrictMono (addNat · m) (strictMono_addNat m)
#align fin.add_nat Fin.addNatEmb

#align fin.coe_add_nat Fin.coe_addNat
#align fin.add_nat_one Fin.addNat_one
#align fin.le_coe_add_nat Fin.le_coe_addNat
#align fin.add_nat_mk Fin.addNat_mk

#align fin.cast_add_nat_zero Fin.cast_addNat_zeroₓ

#align fin.add_nat_cast Fin.addNat_castₓ

#align fin.cast_add_nat_left Fin.cast_addNat_leftₓ

#align fin.cast_add_nat_right Fin.cast_addNat_rightₓ

theorem strictMono_natAdd (n) {m} : StrictMono (natAdd n : Fin m → Fin (n + m)) :=
  fun i j h => add_lt_add_left (show i.val < j.val from h) _

/-- `Fin.natAdd` as an `OrderEmbedding`, `natAddEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply toEmbedding]
def natAddEmb (n) {m} : Fin m ↪o Fin (n + m) :=
  OrderEmbedding.ofStrictMono (natAdd n) (strictMono_natAdd n)
#align fin.nat_add Fin.natAddEmb

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

theorem pred_one' [NeZero n] (h := (zero_ne_one' (n := n)).symm):
    Fin.pred (1 : Fin (n + 1)) h = 0 :=
    by simp_rw [Fin.ext_iff, coe_pred, val_one', val_zero',
      tsub_eq_zero_iff_le, Nat.mod_le]

theorem pred_last (h := last_pos'.ne') :
    pred (last (n + 1)) h = last n := by simp_rw [← succ_last, pred_succ]

theorem pred_lt_iff {i : Fin (n + 1)} (hi : i ≠ 0) : pred i hi < j ↔ i < succ j := by
  rw [← succ_lt_succ_iff, succ_pred]
theorem lt_pred_iff {i : Fin (n + 1)} (hi : i ≠ 0) : j < pred i hi ↔ succ j < i := by
  rw [← succ_lt_succ_iff, succ_pred]
theorem pred_le_iff {i : Fin (n + 1)} (hi : i ≠ 0) : pred i hi ≤ j ↔ i ≤ succ j := by
  rw [← succ_le_succ_iff, succ_pred]
theorem le_pred_iff {i : Fin (n + 1)} (hi : i ≠ 0) : j ≤ pred i hi ↔ succ j ≤ i := by
  rw [← succ_le_succ_iff, succ_pred]

theorem castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a ≠ 0)
    (ha' := a.castSucc_ne_zero_iff.mpr ha) :
    castSucc (a.pred ha) = (castSucc a).pred ha' := rfl
#align fin.cast_succ_pred_eq_pred_cast_succ Fin.castSucc_pred_eq_pred_castSucc

end Pred

section CastPred

/-- `castPred i` sends `i : Fin (n + 1)` to `Fin n` as long as i ≠ last n. -/
@[inline] def castPred (i : Fin (n + 1)) (h : i ≠ last n) : Fin n := castLT i (val_lt_last h)
#align fin.cast_pred Fin.castPred

@[simp]
lemma castLT_eq_castPred (i : Fin (n + 1)) (h : i < last _) (h' := h.ne) :
    castLT i h = castPred i h' := rfl

@[simp]
lemma coe_castPred (i : Fin (n + 1)) (h : i ≠ last _) : (castPred i h : ℕ) = i := rfl
#align fin.coe_cast_pred Fin.coe_castPred

@[simp]
theorem castPred_castSucc {i : Fin n} (h' := (castSucc_lt_last i).ne) :
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

theorem castPred_lt_iff {i : Fin (n + 1)} (hi : i ≠ last n) :
    castPred i hi < j ↔ i < castSucc j := by
  rw [← castSucc_lt_castSucc_iff, castSucc_castPred]

theorem lt_castPred_iff {i : Fin (n + 1)} (hi : i ≠ last n) :
    j < castPred i hi ↔ castSucc j < i := by
  rw [← castSucc_lt_castSucc_iff, castSucc_castPred]

theorem castPred_le_iff {i : Fin (n + 1)} (hi : i ≠ last n) :
    castPred i hi ≤ j ↔ i ≤ castSucc j := by
  rw [← castSucc_le_castSucc_iff, castSucc_castPred]

theorem le_castPred_iff {i : Fin (n + 1)} (hi : i ≠ last n) :
    j ≤ castPred i hi ↔ castSucc j ≤ i := by
  rw [← castSucc_le_castSucc_iff, castSucc_castPred]

theorem castPred_inj {i j : Fin (n + 1)} {hi : i ≠ last n} {hj : j ≠ last n} :
    castPred i hi = castPred j hj ↔ i = j := by
  simp_rw [le_antisymm_iff, castPred_le_castPred_iff]

theorem castPred_zero' [NeZero n] (h := last_pos'.ne) :
    castPred (0 : Fin (n + 1)) h = 0 := rfl

theorem castPred_zero (h := last_pos.ne)  :
    castPred (0 : Fin (n + 2)) h = 0 := rfl
#align fin.cast_pred_zero Fin.castPred_zero

@[simp]
theorem castPred_one [NeZero n] (h := one_lt_last.ne) : castPred (1 : Fin (n + 2)) h = 1 := by
  cases n
  · exact subsingleton_one.elim _ 1
  · rfl
#align fin.cast_pred_one Fin.castPred_one

theorem pred_lt_castPred (h₁ : i ≠ 0) (h₂ : i ≠ last n) : pred i h₁ < castPred i h₂ := by
  rw [← castSucc_lt_castSucc_iff, castSucc_castPred, castSucc_lt_iff_succ_le, succ_pred]

theorem rev_pred (h : i ≠ 0) (h' := rev_ne_iff.mpr ((rev_last _).symm ▸ h)) :
    rev (pred i h) = castPred (rev i) h' := by
  rw [← castSucc_inj, castSucc_castPred, ← rev_succ, succ_pred]

theorem rev_castPred (h : i ≠ last n) (h' := rev_ne_iff.mpr ((rev_zero _).symm ▸ h)) :
    rev (castPred i h) = pred (rev i) h' := by
  rw [← succ_inj, succ_pred, ← rev_castSucc, castSucc_castPred]

theorem succ_castPred_eq_castPred_succ {a : Fin (n + 1)} (ha : a ≠ last n)
    (ha' := a.succ_ne_last_iff.mpr ha) :
    succ (a.castPred ha) = (succ a).castPred ha' := rfl

end CastPred

section DivMod

/-- Compute `i / n`, where `n` is a `Nat` and inferred the type of `i`. -/
def divNat (i : Fin (m * n)) : Fin m :=
  ⟨i / n, Nat.div_lt_of_lt_mul <| mul_comm m n ▸ i.prop⟩
#align fin.div_nat Fin.divNat

@[simp]
theorem coe_divNat (i : Fin (m * n)) : (i.divNat : ℕ) = i / n :=
  rfl
#align fin.coe_div_nat Fin.coe_divNat

/-- Compute `i % n`, where `n` is a `Nat` and inferred the type of `i`. -/
def modNat (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ <| pos_of_mul_pos_right i.pos m.zero_le⟩
#align fin.mod_nat Fin.modNat

@[simp]
theorem coe_modNat (i : Fin (m * n)) : (i.modNat : ℕ) = i % n :=
  rfl
#align fin.coe_mod_nat Fin.coe_modNat

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
  · refine' fun H i => Fin.induction _ _
    · exact fun h => (h.not_le (zero_le i)).elim
    · intro j ihj hij
      rw [← le_castSucc_iff] at hij
      rcases hij.eq_or_lt with (rfl | hlt)
      exacts [H j, _root_.trans (ihj hlt) (H j)]
#align fin.lift_fun_iff_succ Fin.liftFun_iff_succ

/-- A function `f` on `Fin (n + 1)` is strictly monotone if and only if `f i < f (i + 1)`
for all `i`. -/
theorem strictMono_iff_lt_succ {α : Type*} [Preorder α] {f : Fin (n + 1) → α} :
    StrictMono f ↔ ∀ i : Fin n, f (castSucc i) < f i.succ :=
  liftFun_iff_succ (· < ·)
#align fin.strict_mono_iff_lt_succ Fin.strictMono_iff_lt_succ

/-- A function `f` on `Fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for all `i`. -/
theorem monotone_iff_le_succ {α : Type*} [Preorder α] {f : Fin (n + 1) → α} :
    Monotone f ↔ ∀ i : Fin n, f (castSucc i) ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| liftFun_iff_succ (· ≤ ·)
#align fin.monotone_iff_le_succ Fin.monotone_iff_le_succ

/-- A function `f` on `Fin (n + 1)` is strictly antitone if and only if `f (i + 1) < f i`
for all `i`. -/
theorem strictAnti_iff_succ_lt {α : Type*} [Preorder α] {f : Fin (n + 1) → α} :
    StrictAnti f ↔ ∀ i : Fin n, f i.succ < f (castSucc i) :=
  liftFun_iff_succ (· > ·)
#align fin.strict_anti_iff_succ_lt Fin.strictAnti_iff_succ_lt

/-- A function `f` on `Fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for all `i`. -/
theorem antitone_iff_succ_le {α : Type*} [Preorder α] {f : Fin (n + 1) → α} :
    Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f (castSucc i) :=
  antitone_iff_forall_lt.trans <| liftFun_iff_succ (· ≥ ·)
#align fin.antitone_iff_succ_le Fin.antitone_iff_succ_le

section AddGroup

open Nat Int

/-- Negation on `Fin n` -/
instance neg (n : ℕ) : Neg (Fin n) :=
  ⟨fun a => ⟨(n - a) % n, Nat.mod_lt _ a.pos⟩⟩

/-- Abelian group structure on `Fin n`. -/
instance addCommGroup (n : ℕ) [NeZero n] : AddCommGroup (Fin n) :=
  { Fin.addCommMonoid n, Fin.neg n with
    add_left_neg := fun ⟨a, ha⟩ =>
      Fin.ext <|
        _root_.trans (Nat.mod_add_mod _ _ _) <| by
          rw [Fin.val_zero', tsub_add_cancel_of_le, Nat.mod_self]
          exact le_of_lt ha
    sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
      Fin.ext <| show (a + (n - b)) % n = (a + (n - b) % n) % n by simp
    sub := Fin.sub }

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instInvolutiveNeg (n : ℕ) : InvolutiveNeg (Fin n) where
  neg := Neg.neg
  neg_neg := Nat.casesOn n finZeroElim fun _i => neg_neg
#align fin.involutive_neg Fin.instInvolutiveNeg

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instIsCancelAdd (n : ℕ) : IsCancelAdd (Fin n) where
  add_left_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ => add_left_cancel
  add_right_cancel := Nat.casesOn n finZeroElim fun _i _ _ _ => add_right_cancel
#align fin.is_cancel_add Fin.instIsCancelAdd

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instAddLeftCancelSemigroup (n : ℕ) : AddLeftCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }
#align fin.add_left_cancel_semigroup Fin.instAddLeftCancelSemigroup

/-- Note this is more general than `Fin.addCommGroup` as it applies (vacuously) to `Fin 0` too. -/
instance instAddRightCancelSemigroup (n : ℕ) : AddRightCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }
#align fin.add_right_cancel_semigroup Fin.instAddRightCancelSemigroup

protected theorem coe_neg (a : Fin n) : ((-a : Fin n) : ℕ) = (n - a) % n :=
  rfl
#align fin.coe_neg Fin.coe_neg

protected theorem coe_sub (a b : Fin n) : ((a - b : Fin n) : ℕ) = (a + (n - b)) % n := by
  cases a; cases b; rfl
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

theorem coe_sub_one {n} (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
  split_ifs with h
  · simp [h]
  rw [sub_eq_add_neg, val_add_eq_ite, coe_neg_one, if_pos, add_comm, add_tsub_add_eq_tsub_left]
  conv_rhs => rw [add_comm]
  rw [add_le_add_iff_left, Nat.one_le_iff_ne_zero]
  rwa [Fin.ext_iff] at h
#align fin.coe_sub_one Fin.coe_sub_one

theorem coe_sub_iff_le {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = a - b ↔ b ≤ a := by
  cases n; · exact @finZeroElim (fun _ => _) a
  rw [le_iff_val_le_val, Fin.coe_sub, ← add_tsub_assoc_of_le b.is_lt.le a]
  rcases le_or_lt (b : ℕ) a with h | h
  · simp [← tsub_add_eq_add_tsub h, val_fin_le.mp h,
      Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt a.is_lt)]
  · rw [Nat.mod_eq_of_lt, tsub_eq_zero_of_le h.le, tsub_eq_zero_iff_le, ← not_iff_not]
    · simpa [b.is_lt.trans_le le_add_self] using h
    · rwa [tsub_lt_iff_left (b.is_lt.le.trans le_add_self), add_lt_add_iff_right]
#align fin.coe_sub_iff_le Fin.coe_sub_iff_le

theorem coe_sub_iff_lt {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = n + a - b ↔ a < b := by
  cases' n with n
  · exact @finZeroElim (fun _ => _) a
  rw [lt_iff_val_lt_val, Fin.coe_sub, add_comm]
  rcases le_or_lt (b : ℕ) a with h | h
  · refine iff_of_false ?_ (not_lt_of_le h)
    simpa [add_tsub_assoc_of_le h] using
      ((Nat.mod_lt _ (Nat.succ_pos _)).trans_le le_self_add).ne
  · simp [← tsub_tsub_assoc b.is_lt.le h.le, ← tsub_add_eq_add_tsub b.is_lt.le,
      Nat.mod_eq_of_lt (tsub_lt_self (Nat.succ_pos _) (tsub_pos_of_lt h)), val_fin_le.mp _]
    exact h
#align fin.coe_sub_iff_lt Fin.coe_sub_iff_lt

@[simp]
theorem lt_sub_one_iff {n : ℕ} {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  rcases k with ⟨_ | k, hk⟩
  simp only [zero_eq, zero_eta, zero_sub, lt_iff_val_lt_val, val_zero, coe_neg_one, add_pos_iff,
    _root_.zero_lt_one, or_true]
  have : (k + 1 + (n + 1)) % (n + 2) = k % (n + 2) := by
    rw [add_right_comm, add_assoc, add_mod_right]
  simp [lt_iff_val_lt_val, ext_iff, Fin.coe_sub, succ_eq_add_one, this,
    mod_eq_of_lt ((lt_succ_self _).trans hk)]
#align fin.lt_sub_one_iff Fin.lt_sub_one_iff

@[simp]
theorem le_sub_one_iff {n : ℕ} {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  · simp [fin_one_eq_zero k]
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

theorem add_one_le_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) : a + 1 ≤ b := by
  cases' a with a ha
  cases' b with b hb
  cases n
  · simp only [Nat.zero_eq, zero_add, Nat.lt_one_iff] at ha hb
    simp [ha, hb]
  simp only [le_iff_val_le_val, val_add, lt_iff_val_lt_val, val_mk, val_one] at h ⊢
  rwa [Nat.mod_eq_of_lt, Nat.succ_le_iff]
  rw [Nat.succ_lt_succ_iff]
  exact h.trans_le (Nat.le_of_lt_succ hb)

theorem exists_eq_add_of_le {n : ℕ} {a b : Fin n} (h : a ≤ b) : ∃ k ≤ b, b = a + k := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k := Nat.exists_eq_add_of_le h
  have hkb : k ≤ b := le_add_self.trans hk.ge
  refine' ⟨⟨k, hkb.trans_lt b.is_lt⟩, hkb, _⟩
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

theorem exists_eq_add_of_lt {n : ℕ} {a b : Fin (n + 1)} (h : a < b) :
    ∃ k < b, k + 1 ≤ b ∧ b = a + k + 1 := by
  cases n
  · cases' a with a ha
    cases' b with b hb
    simp only [Nat.zero_eq, zero_add, Nat.lt_one_iff] at ha hb
    simp [ha, hb] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (b : ℕ) = a + k + 1 := Nat.exists_eq_add_of_lt h
  have hkb : k < b := by
    rw [hk, add_comm _ k, Nat.lt_succ_iff]
    exact le_self_add
  refine' ⟨⟨k, hkb.trans b.is_lt⟩, hkb, _, _⟩
  · rw [Fin.le_iff_val_le_val, Fin.val_add_one]
    split_ifs <;> simp [Nat.succ_le_iff, hkb]
  simp [Fin.ext_iff, Fin.val_add, ← hk, Nat.mod_eq_of_lt b.is_lt]

@[simp]
theorem neg_last (n : ℕ) : -Fin.last n = 1 := by simp [neg_eq_iff_add_eq_zero]

theorem neg_nat_cast_eq_one (n : ℕ) : -(n : Fin (n + 1)) = 1 := by
  simp only [cast_nat_eq_last, neg_last]

lemma pos_of_ne_zero {n : ℕ} {a : Fin (n + 1)} (h : a ≠ 0) :
    0 < a :=
  Nat.pos_of_ne_zero (val_ne_of_ne h)

end AddGroup

section SuccAbove

/-- `succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`. -/
def succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if castSucc i < p then i.castSucc else i.succ

theorem succAbove_eq_castSucc_or_succ (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i = i.castSucc ∨ p.succAbove i = i.succ := ite_eq_or_eq _ _ _

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `castSucc` when the resulting `i.castSucc < p`. -/
theorem succAbove_of_castSucc_lt {p : Fin (n + 1)} {i : Fin n} (h : castSucc i < p) :
    p.succAbove i = castSucc i := dif_pos h
#align fin.succ_above_below Fin.succAbove_of_castSucc_lt
theorem succAbove_of_succ_le {p : Fin (n + 1)} {i : Fin n} (h : succ i ≤ p) :
    p.succAbove i = castSucc i :=
  succAbove_of_castSucc_lt (castSucc_lt_iff_succ_le.mpr h)

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
theorem succAbove_of_le_castSucc {p : Fin (n + 1)} {i : Fin n} (h : p ≤ castSucc i) :
    p.succAbove i = succ i := dif_neg h.not_lt
#align fin.succ_above_above Fin.succAbove_of_le_castSucc
theorem succAbove_of_lt_succ {p : Fin (n + 1)} {i : Fin n} (h : p < succ i) :
    p.succAbove i = succ i := succAbove_of_le_castSucc (le_castSucc_iff.mpr h)

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself -/
theorem succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  rcases i.castSucc_lt_or_lt_succ p with (h | h)
  · rw [succAbove_of_castSucc_lt h]
    exact h.ne
  · rw [succAbove_of_lt_succ h]
    exact h.ne'
#align fin.succ_above_ne Fin.succAbove_ne
theorem ne_succAbove (p : Fin (n + 1)) (i : Fin n) : p ≠ p.succAbove i :=
(succAbove_ne _ _).symm

theorem succAbove_succ_of_le {p i : Fin n} (h : i ≤ p) :
    succAbove p.succ i = i.castSucc := succAbove_of_succ_le (succ_le_succ_iff.mpr h)
theorem succAbove_succ_of_lt {p i : Fin n} (h : p < i) :
    succAbove p.succ i = i.succ := succAbove_of_lt_succ (succ_lt_succ_iff.mpr h)
@[simp]
theorem succAbove_succ_self {n : ℕ} (j : Fin n) :
    j.succ.succAbove j = j.castSucc := succAbove_succ_of_le le_rfl

theorem succAbove_castSucc_of_lt {p i : Fin n} (h : i < p) :
    succAbove p.castSucc i = i.castSucc :=
  succAbove_of_castSucc_lt (castSucc_lt_castSucc_iff.mpr h)
theorem succAbove_castSucc_of_le {p i : Fin n} (h : p ≤ i) :
    succAbove p.castSucc i = i.succ :=
  succAbove_of_le_castSucc (castSucc_le_castSucc_iff.mpr h)
@[simp]
theorem succAbove_castSucc_self {n : ℕ} (j : Fin n) :
    succAbove j.castSucc j = j.succ := succAbove_castSucc_of_le le_rfl

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp]
theorem succAbove_zero : succAbove (0 : Fin (n + 1)) = Fin.succ := rfl
#align fin.succ_above_zero Fin.succAbove_zero
theorem succAbove_zero_apply {i} : succAbove (0 : Fin (n + 1)) i = i.succ := rfl

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around `last n` embeds by `castSucc`. -/
@[simp]
theorem succAbove_last : succAbove (last n) = Fin.castSucc :=
  funext (fun _ => succAbove_of_succ_le (le_last _))
#align fin.succ_above_last Fin.succAbove_last
theorem succAbove_last_apply {i} : succAbove (last n) i = i.castSucc :=
  congr_fun succAbove_last _
#align fin.succ_above_last_apply Fin.succAbove_last_apply

theorem rev_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    rev (succAbove p i) = succAbove (rev p) (rev i) := by
  rcases castSucc_lt_or_lt_succ i p with (h | h)
  · rw [succAbove_of_castSucc_lt h, rev_castSucc]
    exact (succAbove_of_lt_succ (rev_castSucc _ ▸ rev_lt_rev.mpr h)).symm
  · rw [succAbove_of_lt_succ h, rev_succ]
    exact (succAbove_of_castSucc_lt (rev_succ _ ▸ (rev_lt_rev.mpr h))).symm

theorem succAbove_succAbove_of_lt {p : Fin (n + 1)} {i j : Fin n} (hij : i < j):
    succAbove (succAbove p j) i = i.castSucc := by
  rcases succAbove_eq_castSucc_or_succ p j with (h | h)
  · rw [h, succAbove_castSucc_of_lt hij]
  · rw [h, succAbove_succ_of_le hij.le]

theorem succAbove_succAbove_of_gt {p : Fin (n + 1)} {i j : Fin n} (hij : j < i):
    succAbove (succAbove p j) i = i.succ := by
  rcases succAbove_eq_castSucc_or_succ p j with (h | h)
  · rw [h, succAbove_castSucc_of_le hij.le]
  · rw [h, succAbove_succ_of_lt hij]

theorem succAbove_succAbove {i j : Fin n} (p q : Fin (n + 1)) (hij : i ≠ j) :
    succAbove (succAbove p j) i = succAbove (succAbove q j) i := by
  rcases hij.lt_or_lt with (hij | hij)
  · simp_rw [succAbove_succAbove_of_lt hij]
  · simp_rw [succAbove_succAbove_of_gt hij]

theorem succAbove_on_comp_succAbove_on_const_succAbove_succ_of_ne {i j : Fin n} (hij : i ≠ j) :
    (succAbove · i) ∘ (succAbove · j) = Function.const _ (succAbove (succ j) i) := by
  ext k : 1
  simp_rw [comp_apply, const_apply, succAbove_succAbove k 0 hij, succAbove_zero]

theorem succAbove_on_comp_succAbove_on_const_succAbove_castSucc_of_ne {i j : Fin n} (hij : i ≠ j) :
    (succAbove · i) ∘ (succAbove · j) = Function.const _ (succAbove (castSucc j) i) := by
  ext k : 1
  simp_rw [comp_apply, const_apply, succAbove_succAbove k (last _) hij, succAbove_last]

@[simp]
theorem succAbove_succ_eq_succAbove_castSucc_of_ne {i j : Fin n} (h : i ≠ j) :
    succAbove (succ j) i = succAbove (castSucc j) i := by
  rw [← Function.const_inj (α := Fin (n + 1)),
  ← succAbove_on_comp_succAbove_on_const_succAbove_castSucc_of_ne h,
  ← succAbove_on_comp_succAbove_on_const_succAbove_succ_of_ne h]

theorem succAbove_succAbove_self_of_castSucc_lt {p : Fin (n + 1)} {i : Fin n}
    (h : castSucc i < p) : succAbove (succAbove p i) i = i.succ :=
  succAbove_of_le_castSucc (succAbove_of_castSucc_lt h ▸ le_rfl)

theorem succAbove_succAbove_self_of_succ_le {p : Fin (n + 1)} {i : Fin n}
    (h : succ i ≤ p) : succAbove (succAbove p i) i = i.succ :=
  succAbove_succAbove_self_of_castSucc_lt (castSucc_lt_iff_succ_le.mpr h)

theorem succAbove_succAbove_self_of_le_castSucc {p : Fin (n + 1)} {i : Fin n}
    (h : p ≤ castSucc i) : succAbove (succAbove p i) i = i.castSucc :=
  succAbove_of_succ_le (succAbove_of_le_castSucc h ▸ le_rfl)

theorem succAbove_succAbove_self_of_lt_succ {p : Fin (n + 1)} {i : Fin n}
    (h : p < succ i) : succAbove (succAbove p i) i = i.castSucc :=
  succAbove_succAbove_self_of_le_castSucc (le_castSucc_iff.mpr h)

theorem succAbove_succAbove_castSucc_of_le {p i : Fin n} (h : i ≤ p) :
    succAbove (succAbove (castSucc i) p) i = castSucc i := by
  rw [succAbove_castSucc_of_le h, succAbove_succ_of_le h]

theorem succAbove_succAbove_succ_of_le {p i : Fin n} (h : p ≤ i) :
    succAbove (succAbove (succ i) p) i = succ i := by
  rw [succAbove_succ_of_le h, succAbove_castSucc_of_le h]

@[simp]
theorem succAbove_succAbove_succAbove {p : Fin (n + 1)} {i : Fin n} :
    succAbove (succAbove (succAbove p i) i) i = succAbove p i := by
  rcases succAbove_eq_castSucc_or_succ p i with (h | h) <;>
  simp only [h, succAbove_castSucc_self, succAbove_succ_self]

theorem succAbove_triple {i : Fin n} :
    (succAbove · i) ∘ (succAbove · i) ∘ (succAbove · i) = (succAbove · i) :=
  funext (fun _ => succAbove_succAbove_succAbove)

@[simp]
theorem succAbove_succAbove_succAbove_succAbove {p : Fin (n + 1)} {i j : Fin n} :
    succAbove (succAbove (succAbove (succAbove p j) i) j) i = succAbove (succAbove p j) i := by
  rcases lt_trichotomy i j with (hij | rfl | hij)
  · simp_rw [succAbove_succAbove_of_lt hij]
  · rw [succAbove_succAbove_succAbove]
  · simp_rw [succAbove_succAbove_of_gt hij]

theorem succAbove_quad {i j : Fin n} :
    (succAbove · i) ∘ (succAbove · j) ∘ (succAbove · i) ∘ (succAbove · j) =
    (succAbove · i) ∘ (succAbove · j) :=
  funext (fun _ => succAbove_succAbove_succAbove_succAbove)

theorem succAbove_at_eq_iff_castSucc {p q : Fin (n + 1)} {r : Fin n} : p.succAbove r = q.succAbove r
    ↔ (p ≤ r.castSucc ∧ q ≤ r.castSucc) ∨ (r.castSucc < p ∧ r.castSucc < q) := by
  rcases le_or_lt p (r.castSucc) with (hp | hp) <;>
  rcases le_or_lt q (r.castSucc) with (hq | hq)
  · simp only [hp, hq, succAbove_of_le_castSucc, and_self, true_or]
  · simp only [hp, hq, hp.not_lt, hq.not_le, succAbove_of_le_castSucc, succAbove_of_castSucc_lt,
    (castSucc_lt_succ r).ne', and_false, and_true, or_self]
  · simp only [hp, hq, hp.not_le, hq.not_lt, succAbove_of_castSucc_lt, succAbove_of_le_castSucc,
    (castSucc_lt_succ r).ne, and_true, and_false, or_self]
  · simp only [hp ,hq, hp.not_le, hq.not_le, succAbove_of_castSucc_lt, and_self, or_true]
theorem succAbove_at_eq_iff_succ {p q : Fin (n + 1)} {r : Fin n} : p.succAbove r = q.succAbove r
    ↔ (p < r.succ ∧ q < r.succ) ∨ (r.succ ≤ p ∧ r.succ ≤ q) := by
  simp_rw [succAbove_at_eq_iff_castSucc, le_castSucc_iff, castSucc_lt_iff_succ_le]


theorem succAbove_eq_of_le_castSucc_le_castSucc {p q : Fin (n + 1)} {r : Fin n}
    (hp : p ≤ r.castSucc) (hq : q ≤ r.castSucc) : p.succAbove r = q.succAbove r :=
  succAbove_at_eq_iff_castSucc.mpr (Or.inl ⟨hp, hq⟩)
theorem succAbove_eq_of_lt_succ_lt_succ {p q : Fin (n + 1)} {r : Fin n}
    (hp : p < r.succ) (hq : q < r.succ) : p.succAbove r = q.succAbove r :=
  succAbove_at_eq_iff_succ.mpr (Or.inl ⟨hp, hq⟩)

theorem succAbove_eq_of_castSucc_lt_castSucc_lt {p q : Fin (n + 1)} {r : Fin n}
    (hp : r.castSucc < p) (hq : r.castSucc < q) : p.succAbove r = q.succAbove r :=
  succAbove_at_eq_iff_castSucc.mpr (Or.inr ⟨hp, hq⟩)
theorem succAbove_eq_of_succ_le_succ_le {p q : Fin (n + 1)} {r : Fin n}
    (hp : r.succ ≤ p) (hq : r.succ ≤ q) : p.succAbove r = q.succAbove r :=
  succAbove_at_eq_iff_succ.mpr (Or.inr ⟨hp, hq⟩)

theorem succAbove_castSucc_eq_succAbove_succ_iff {p q : Fin (n + 1)} {r : Fin n} :
    (p.succAbove r).castSucc = (q.succAbove r).succ ↔ p ≤ r.castSucc ∧ r.castSucc < q := by
  rcases le_or_lt p (r.castSucc) with (hp | hp) <;>
  rcases le_or_lt q (r.castSucc) with (hq | hq)
  · simp only [hp, succAbove_of_le_castSucc, hq, castSucc_ne_succ, hq.not_lt, and_false, hp.not_lt,
    and_true, or_self]
  · simp only [hp, succAbove_of_le_castSucc, hq, succAbove_of_castSucc_lt, succ_castSucc, and_self,
    hp.not_lt, hq.not_le, or_false]
  · simp only [hp, succAbove_of_castSucc_lt, hq, succAbove_of_le_castSucc,
    castSucc_castSucc_ne_succ_succ, hp.not_le, hq.not_lt, and_self]
  · simp only [hp, succAbove_of_castSucc_lt, hq, castSucc_ne_succ, hp.not_le, and_true]
theorem succAbove_castSucc_eq_succAbove_succ_iff_succ {p q : Fin (n + 1)} {r : Fin n} :
    (p.succAbove r).castSucc = (q.succAbove r).succ ↔ p < r.succ ∧ r.succ ≤ q := by
  simp_rw [succAbove_castSucc_eq_succAbove_succ_iff,
  le_castSucc_iff, castSucc_lt_iff_succ_le]

theorem succAbove_castSucc_eq_succ_of_le_castSucc_castSucc_lt {p q : Fin (n + 1)} {r : Fin n}
    (hp : p ≤ r.castSucc) (hq : r.castSucc < q) :
    (p.succAbove r).castSucc = (q.succAbove r).succ :=
  succAbove_castSucc_eq_succAbove_succ_iff.mpr ⟨hp, hq⟩
theorem succAbove_castSucc_eq_succ_of_lt_succ_succ_le {p q : Fin (n + 1)} {r : Fin n}
    (hp : p < r.succ) (hq : r.succ ≤ q) :
    (p.succAbove r).castSucc = (q.succAbove r).succ :=
  succAbove_castSucc_eq_succAbove_succ_iff_succ.mpr ⟨hp, hq⟩

theorem succAbove_strictMono (p : Fin (n + 1)) : StrictMono (succAbove p) :=
  strictMono_castSucc.ite strictMono_succ
  (fun _ _ hij hj => lt_trans ((castSucc_lt_castSucc_iff).mpr hij) hj)
  fun _ => (castSucc_lt_succ _).le

theorem succAbove_lt_succAbove_iff (p : Fin (n + 1)) :
    succAbove p i < succAbove p j ↔ i < j := (succAbove_strictMono p).lt_iff_lt
theorem succAbove_le_succAbove_iff (p : Fin (n + 1)) :
    succAbove p i ≤ succAbove p j ↔ i ≤ j := (succAbove_strictMono p).le_iff_le

theorem succAbove_lt_of_le_castSucc_castSucc_lt {p q : Fin (n + 1)} {r : Fin n}
    (hp : p ≤ r.castSucc) (hq : r.castSucc < q) :
    q.succAbove r < p.succAbove r := by
  rw [← castSucc_lt_castSucc_iff, succAbove_castSucc_eq_succ_of_le_castSucc_castSucc_lt hp hq]
  exact castSucc_lt_succ _

theorem succAbove_lt_of_lt_succ_succ_le {p q : Fin (n + 1)} {r : Fin n}
    (hp : p < r.succ) (hq : r.succ ≤ q) :
    q.succAbove r < p.succAbove r := by
  rw [← castSucc_lt_castSucc_iff, succAbove_castSucc_eq_succ_of_lt_succ_succ_le hp hq]
  exact castSucc_lt_succ _

theorem succAbove_le_of_ge {r : Fin n} {p q : Fin (n + 1)} (hpq : p ≤ q) :
    succAbove q r ≤ succAbove p r := by
  rcases le_or_lt p (r.castSucc) with (hp | hp) <;>
  rcases le_or_lt q (r.castSucc) with (hq | hq)
  · exact (succAbove_eq_of_le_castSucc_le_castSucc hp hq).ge
  · exact (succAbove_lt_of_le_castSucc_castSucc_lt hp hq).le
  · exact (hpq.not_lt (hq.trans_lt hp)).elim
  · exact (succAbove_eq_of_castSucc_lt_castSucc_lt hp hq).ge

theorem antitone_succAbove_at {r : Fin n} : Antitone (succAbove · r) :=
  fun _ _ => succAbove_le_of_ge

theorem antitone_succAbove : Antitone (succAbove (n := n)) :=
  fun _ _ h _ => antitone_succAbove_at h

/--  `Fin.succAbove` as an `OrderEmbedding`, `succAboveEmb p i` embeds `Fin n` into `Fin (n + 1)`
with a hole around `p`. -/
@[simps! apply toEmbedding]
def succAboveEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (succAbove p) (succAbove_strictMono p)
#align fin.succ_above Fin.succAboveEmb

/-- Given a fixed pivot `x : Fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_injective {x : Fin (n + 1)} : Injective (succAbove x) :=
  (succAbove_strictMono x).injective
#align fin.succ_above_right_injective Fin.succAbove_injective

/-- Given a fixed pivot `x : Fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_inj (x : Fin (n + 1)) : x.succAbove a = x.succAbove b ↔ a = b :=
  succAbove_injective.eq_iff
#align fin.succ_above_right_inj Fin.succAbove_inj

@[simp]
theorem succAbove_zero_of_ne_zero' [NeZero n] {a : Fin (n + 1)} (h : a ≠ 0) :
    a.succAbove 0 = 0 := by
  rcases exists_succ_eq_of_ne_zero h with ⟨i, rfl⟩
  exact succAbove_succ_of_le (i.zero_le')
theorem succAbove_ne_zero_eq_zero_iff' [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) :
    a.succAbove b = 0 ↔ b = 0 := by rw [← succAbove_zero_of_ne_zero' ha, succAbove_inj]
theorem succAbove_ne_zero_of_ne_zero_ne_zero' [NeZero n] {a : Fin (n + 1)} {b : Fin n}
    (ha : a ≠ 0) (hb : b ≠ 0) : a.succAbove b ≠ 0 := mt (succAbove_ne_zero_eq_zero_iff' ha).mp hb
@[simp]
theorem succAbove_succ_zero' {n : ℕ} [NeZero n] {i : Fin n} : succAbove i.succ 0 = 0 :=
  succAbove_zero_of_ne_zero' (succ_pos _).ne'
#align fin.succ_succ_above_zero Fin.succAbove_succ_zero'

theorem succAbove_zero_of_ne_zero {a : Fin (n + 2)} (h : a ≠ 0) : a.succAbove 0 = 0 :=
  succAbove_zero_of_ne_zero' h
theorem succAbove_ne_zero_eq_zero_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) :
    a.succAbove b = 0 ↔ b = 0 := succAbove_ne_zero_eq_zero_iff' ha
theorem succAbove_ne_zero_of_ne_zero_ne_zero {a : Fin (n + 2)} {b : Fin (n + 1)}
    (ha : a ≠ 0) (hb : b ≠ 0) : a.succAbove b ≠ 0 := succAbove_ne_zero_of_ne_zero_ne_zero' ha hb
theorem succAbove_succ_zero {i : Fin (n + 1)} : succAbove i.succ 0 = 0 := succAbove_succ_zero'

/-- Embedding a positive `Fin n` results in a positive `Fin (n + 1)` -/
theorem succAbove_pos_of_pos' [NeZero n] (p : Fin (n + 1)) {i : Fin n} (h : 0 < i) :
    0 < p.succAbove i := by
  cases p using cases
  · rw [succAbove_zero_apply]
    exact succ_pos _
  · rw [pos_iff_ne_zero]
    exact succAbove_ne_zero_of_ne_zero_ne_zero' (succ_pos _).ne' h.ne'
#align fin.succ_above_pos Fin.succAbove_pos_of_pos'
theorem succAbove_pos_of_pos (p : Fin (n + 2)) {i : Fin (n + 1)} (h : 0 < i) : 0 < p.succAbove i :=
  succAbove_pos_of_pos' _ h

@[simp]
theorem succAbove_last_of_ne_last {a : Fin (n + 2)} (h : a ≠ last _) :
    a.succAbove (last _) = last _ := by
  rcases exists_castSucc_eq_of_ne_last h with ⟨i, rfl⟩
  rw [succAbove_castSucc_of_le (le_last _), succ_last]
theorem succAbove_ne_last_eq_last_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last _) :
    a.succAbove b = last _ ↔ b = last _ :=
  by rw [← succAbove_last_of_ne_last ha, succAbove_inj]
theorem succAbove_ne_last_of_ne_last_ne_last {a : Fin (n + 2)} {b : Fin (n + 1)}
    (ha : a ≠ last _) (hb : b ≠ last _) : a.succAbove b ≠ last _ :=
  mt (succAbove_ne_last_eq_last_iff ha).mp hb
@[simp]
theorem succAbove_castSucc_last {p : Fin (n + 1)}: p.castSucc.succAbove (last _) = last _ :=
  succAbove_last_of_ne_last (castSucc_lt_last _).ne

theorem succAbove_lt_last_of_lt_last (p : Fin (n + 2)) {i : Fin (n + 1)} (h : i < last _) :
    p.succAbove i < last _ := by
  cases p using lastCases
  · rw [succAbove_last_apply]
    exact castSucc_lt_last _
  · rw [lt_last_iff_ne_last]
    exact succAbove_ne_last_of_ne_last_ne_last (castSucc_lt_last _).ne h.ne

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
theorem succAbove_lt_iff_castSucc_lt (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ castSucc i < p := by
  rcases i.castSucc_lt_or_lt_succ p with (h | h)
  · rw [succAbove_of_castSucc_lt h]
  · rw [succAbove_of_lt_succ h, castSucc_lt_iff_succ_le, h.ne'.le_iff_lt]
#align fin.succ_above_lt_iff Fin.succAbove_lt_iff_castSucc_lt
theorem succAbove_lt_iff_succ_le (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ succ i ≤ p := by
  rw [succAbove_lt_iff_castSucc_lt, ← castSucc_lt_iff_succ_le]
@[simp]
theorem succAbove_le_iff_succAbove_lt (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i ≤ p ↔ p.succAbove i < p := (succAbove_ne _ _).le_iff_lt

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
theorem lt_succAbove_iff_le_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p ≤ castSucc i := by
  rw [lt_iff_not_le, (succAbove_ne _ _).le_iff_lt, succAbove_lt_iff_castSucc_lt, not_lt]
#align fin.lt_succ_above_iff Fin.lt_succAbove_iff_le_castSucc
theorem lt_succAbove_iff_lt_succ (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p < succ i := by
  rw [lt_succAbove_iff_le_castSucc, le_castSucc_iff]
@[simp]
theorem le_succAbove_iff_lt_succAbove (p : Fin (n + 1)) (i : Fin n) :
    p ≤ p.succAbove i ↔ p < p.succAbove i := (ne_succAbove _ _).le_iff_lt

theorem succAbove_succAbove_le_iff_castSucc_le
    {i : Fin (n + 1)} {p : Fin n} : succAbove (succAbove i p) p ≤ i ↔ castSucc p ≤ i := by
  rcases castSucc_lt_or_lt_succ p i with (hpi | hpi)
  · rw [succAbove_of_castSucc_lt hpi, succAbove_castSucc_self,
    ← castSucc_lt_iff_succ_le, hpi.ne.le_iff_lt]
  · rw [succAbove_of_lt_succ hpi, succAbove_succ_self]

theorem le_succAbove_succAbove_iff_le_succ
    {i : Fin (n + 1)} {p : Fin n} : i ≤ succAbove (succAbove i p) p ↔ i ≤ succ p := by
  rcases castSucc_lt_or_lt_succ p i with (hpi | hpi)
  · rw [succAbove_of_castSucc_lt hpi, succAbove_castSucc_self]
  · rw [succAbove_of_lt_succ hpi, succAbove_succ_self, le_castSucc_iff, hpi.ne.le_iff_lt]

theorem succAbove_le_succ (p : Fin (n + 1)) : p.succAbove ≤ succ := fun i => by
  rcases succAbove_eq_castSucc_or_succ p i with (h | h) <;> rw [h]
  exact (castSucc_lt_succ _).le
theorem succAbove_apply_le_succ (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≤ succ i :=
  succAbove_le_succ _ _

theorem castSucc_le_succAbove (p : Fin (n + 1)) : castSucc ≤ p.succAbove := fun i => by
  rcases succAbove_eq_castSucc_or_succ p i with (h | h) <;> rw [h]
  exact (castSucc_lt_succ _).le
theorem castSucc_apply_le_succAbove (p : Fin (n + 1)) (i : Fin n) : castSucc i ≤ p.succAbove i :=
castSucc_le_succAbove _ _

/-- `succ` commutes with `succAbove`. -/
@[simp]
theorem succAbove_succ_succ {n : ℕ} {p : Fin (n + 1)} {i : Fin n} :
    succAbove (p.succ) (i.succ) = (p.succAbove i).succ := by
  rcases lt_or_le p (succ i) with (h | h)
  · rw [succAbove_succ_of_lt h, succAbove_of_lt_succ h]
  · rw [succAbove_succ_of_le h, succAbove_of_succ_le h, succ_castSucc]
#align fin.succ_succ_above_succ Fin.succAbove_succ_succ

theorem succAbove_succ_comp_succ_eq_succ_comp_succAbove {n : ℕ} (p : Fin (n + 1)) :
    (succAbove p.succ) ∘ succ = succ ∘ succAbove p :=
  funext (fun _ => succAbove_succ_succ)

/-- `castSucc` commutes with `succAbove`. -/
@[simp]
theorem succAbove_castSucc_castSucc {n : ℕ} {p : Fin (n + 1)} {i : Fin n} :
    succAbove (p.castSucc) (i.castSucc) = (p.succAbove i).castSucc := by
  rcases le_or_lt p (castSucc i) with (h | h)
  · rw [succAbove_castSucc_of_le h, succAbove_of_le_castSucc h, succ_castSucc]
  · rw [succAbove_castSucc_of_lt h, succAbove_of_castSucc_lt h]

theorem succAbove_castSucc_comp_castSucc_eq_castSucc_comp_succAbove {n : ℕ} (p : Fin (n + 1)) :
    (succAbove p.castSucc) ∘ castSucc = castSucc ∘ succAbove p :=
  funext (fun _ => succAbove_castSucc_castSucc)

@[simp]
theorem succAbove_castSucc_succ {n : ℕ} {p : Fin (n + 1)}
    {i : Fin n} (hip : p ≠ succ i) :
    succAbove p.castSucc i.succ = (succAbove p i).succ := by
  rw [← succAbove_succ_eq_succAbove_castSucc_of_ne hip.symm,
  succAbove_succ_succ]

@[simp]
theorem succAbove_succ_castSucc {n : ℕ} {p : Fin (n + 1)}
    {i : Fin n} (hip : p ≠ castSucc i) :
    succAbove p.succ i.castSucc = (succAbove p i).castSucc := by
  rw [succAbove_succ_eq_succAbove_castSucc_of_ne hip.symm,
  succAbove_castSucc_castSucc]

/-- `pred` commutes with `succAbove`. -/
theorem succAbove_pred_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succAbove_ne_zero_of_ne_zero_ne_zero ha hb) :
    (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  rw [← succ_inj, ← succAbove_succ_succ]
  simp_rw [succ_pred]
#align fin.pred_succ_above_pred Fin.succAbove_pred_pred

/-- `castPred` commutes with `succAbove`. -/
theorem succAbove_castPred_castPred {a : Fin (n + 2)} {b : Fin (n + 1)}
    (ha : a ≠ last (n + 1)) (hb : b ≠ last n)
    (hk := succAbove_ne_last_of_ne_last_ne_last ha hb) :
    (a.castPred ha).succAbove (b.castPred hb) = (a.succAbove b).castPred hk := by
  rw [← castSucc_inj, ← succAbove_castSucc_castSucc]
  simp_rw [castSucc_castPred]

theorem succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove {i : Fin (n + 1)} {k : Fin n} :
    succAbove (succ i) (succAbove i k) = succAbove (castSucc i) (succAbove i k) :=
  succAbove_succ_eq_succAbove_castSucc_of_ne (succAbove_ne _ _)

/- The special case of the first simplicial identity. -/
theorem succAbove_succ_comp_succAbove_eq
    {i : Fin (n + 1)} : succAbove (succ i) ∘ succAbove i = succAbove (castSucc i) ∘ succAbove i :=
  funext (fun _ => succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove)

theorem succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_succ_le {k : Fin n}
    {i j : Fin (n + 1)} (hj : succ k ≤ j) :
    succAbove (succ j) (succAbove i k) = succAbove (castSucc i) (succAbove j k) := by
  rw [succAbove_of_succ_le hj, succAbove_succ_of_le ((succAbove_le_succ _ _).trans hj),
    succAbove_castSucc_castSucc]

theorem succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_le_castSucc {k : Fin n}
    {i j : Fin (n + 1)} (hi : i ≤ castSucc k) :
    succAbove (succ j) (succAbove i k) = succAbove (castSucc i) (succAbove j k) := by
  rw [succAbove_of_le_castSucc hi,
    succAbove_castSucc_of_le (hi.trans (castSucc_le_succAbove _ _)),
    succAbove_succ_succ]

theorem succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_succ_lt_of_castSucc_lt
    {k : Fin n} {i j : Fin (n + 1)} (hi : succ k < i) (hj : j < castSucc k):
    succAbove (succ j) (succAbove i k) = succAbove (castSucc i) (succAbove j k) := by
  simp only [hi.le, succAbove_of_succ_le, ne_eq, hj.ne, not_false_eq_true,
    succAbove_succ_castSucc, hj.le, succAbove_of_le_castSucc,
    hi.ne', succAbove_castSucc_succ, succ_castSucc]

theorem succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_ne_succ_of_ne_castSucc
    {k : Fin n} {i j : Fin (n + 1)} (hine : i ≠ succ k) (hjne : j ≠ castSucc k) :
    succAbove (succ j) (succAbove i k) = succAbove (castSucc i) (succAbove j k) := by
  refine (le_or_lt i (castSucc k)).by_cases
    succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_le_castSucc (fun hi => ?_)
  refine (le_or_lt (succ k) j).by_cases
    succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_succ_le (fun hj => ?_)
  rw [castSucc_lt_iff_succ_le, hine.symm.le_iff_lt] at hi
  rw [← le_castSucc_iff, hjne.le_iff_lt] at hj
  exact succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_succ_lt_of_castSucc_lt hi hj

theorem succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_le {k : Fin n}
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    succAbove (succ j) (succAbove i k) = succAbove (castSucc i) (succAbove j k) := by
  refine (le_or_lt i (castSucc k)).by_cases
    succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_le_castSucc (fun hi => ?_)
  refine (le_or_lt (succ k) j).by_cases
    succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_succ_le (fun hj => ?_)
  exact ((le_of_castSucc_lt_of_succ_lt hi hj).not_le hij).elim

/- The general case of the first simplicial identity. -/
theorem succAbove_comp_succ_succAbove_eq_succAbove_castSucc_succAbove_of_le {i j : Fin (n + 1)}
    (hij : i ≤ j) : succAbove (succ j) ∘ (succAbove i) = succAbove (castSucc i) ∘ (succAbove j) :=
funext (fun _ => succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_le hij)

@[simp]
theorem succAbove_succ_one  (i : Fin (n + 2)) :
    i.succ.succAbove 1 = (i.succAbove 0).succ :=
    succ_zero_eq_one (n := n) ▸ succAbove_succ_succ

@[simp]
theorem succAbove_succ_one' {n : ℕ} [NeZero n] (i : Fin (n + 1)) :
    i.succ.succAbove 1 = (i.succAbove 0).succ :=
  succ_zero_eq_one' (n := n) ▸ succAbove_succ_succ
#align fin.succ_succ_above_one Fin.succAbove_succ_one'

@[simp]
theorem succAbove_one_of_succ {n : ℕ} (j : Fin n) :
    (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ := rfl
#align fin.one_succ_above_succ Fin.succAbove_one_of_succ

theorem succAbove_one_one {n : ℕ} : (1 : Fin (n + 3)).succAbove 1 = 2 := rfl
#align fin.one_succ_above_one Fin.succAbove_one_one

@[simp]
theorem succAbove_castPred_of_lt {i j : Fin (n + 1)} (h : i < j)
    (hi : i ≠ last _ := (j.le_last.trans_lt' h).ne) : j.succAbove (castPred i hi) = i := by
  rw [succAbove_of_castSucc_lt (castSucc_castPred _ _ ▸ h), castSucc_castPred]

@[simp]
theorem succAbove_pred_of_gt {i j : Fin (n + 1)} (h : j < i)
    (hi : i ≠ 0 := (j.zero_le.trans_lt h).ne') : j.succAbove (i.pred hi) = i := by
  rw [succAbove_of_lt_succ (succ_pred _ _ ▸ h), succ_pred]
#align fin.succ_above_pred Fin.succAbove_pred_of_gt

theorem castPred_succAbove_of_castSucc_lt {i : Fin n} {j : Fin (n + 1)} (h : castSucc i < j)
    (h' : (j.succAbove i) ≠ last n :=
    (j.le_last.trans_lt' ((succAbove_lt_iff_castSucc_lt _ _).2 h)).ne) :
    (j.succAbove i).castPred h' = i := by simp_rw [succAbove_of_castSucc_lt h, castPred_castSucc]

theorem castPred_succAbove_of_succ_le {i : Fin n} {j : Fin (n + 1)} (h : succ i ≤ j)
    (h' : (j.succAbove i) ≠ last n :=
    (j.le_last.trans_lt' ((succAbove_lt_iff_castSucc_lt _ _).2 h)).ne) :
    (j.succAbove i).castPred h' = i :=
  castPred_succAbove_of_castSucc_lt (castSucc_lt_iff_succ_le.mpr h)

theorem pred_succAbove_of_castSucc_le {i : Fin n} {j : Fin (n + 1)} (h : j ≤ castSucc i)
    (h' : (j.succAbove i) ≠ 0 := (j.zero_le.trans_lt <|
    (lt_succAbove_iff_le_castSucc _ _).2 h).ne') : (j.succAbove i).pred h' = i := by
  simp_rw [succAbove_of_le_castSucc h, pred_succ]
#align fin.pred_succ_above Fin.pred_succAbove_of_castSucc_le

theorem pred_succAbove_of_succ_lt {i : Fin n} {j : Fin (n + 1)} (h : j < succ i)
    (h' : (j.succAbove i) ≠ 0 := (j.zero_le.trans_lt <| (lt_succAbove_iff_lt_succ _ _).2 h).ne') :
    (j.succAbove i).pred h' = i :=
  pred_succAbove_of_castSucc_le (le_castSucc_iff.mpr h)

theorem exists_succAbove_eq {p i: Fin (n + 1)} (h : i ≠ p) : ∃ z, p.succAbove z = i := by
  cases' h.lt_or_lt with hlt hlt
  exacts [⟨_, succAbove_castPred_of_lt hlt⟩, ⟨_, succAbove_pred_of_gt hlt⟩]
#align fin.exists_succ_above_eq Fin.exists_succAbove_eq

@[simp]
theorem exists_succAbove_eq_iff_ne {p i: Fin (n + 1)} : (∃ z, p.succAbove z = i) ↔ i ≠ p :=
  ⟨fun ⟨_, h⟩ => h ▸ (succAbove_ne _ _), exists_succAbove_eq⟩
#align fin.exists_succ_above_eq_iff Fin.exists_succAbove_eq_iff_ne

/-- The range of `p.succAbove` is everything except `p`. -/
@[simp]
theorem range_succAbove (p : Fin (n + 1)) : Set.range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff_ne
#align fin.range_succ_above Fin.range_succAbove

theorem range_castSucc' {n : ℕ} : Set.range (castSucc : Fin n → Fin n.succ) = {Fin.last _}ᶜ :=
  succAbove_last ▸ range_succAbove _

@[simp]
theorem range_succ (n : ℕ) : Set.range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ :=
  succAbove_zero ▸ range_succAbove _
#align fin.range_succ Fin.range_succ

/-- `succAbove` is injective at the pivot -/
theorem succAbove_pivot_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n → Fin (n + 1) => (Set.range f)ᶜ) h
#align fin.succ_above_left_injective Fin.succAbove_pivot_injective

/-- `succAbove` is injective at the pivot -/
@[simp]
theorem succAbove_pivot_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succAbove_pivot_injective.eq_iff
#align fin.succ_above_left_inj Fin.succAbove_pivot_inj

theorem strictAnti_left_succAbove : StrictAnti (succAbove (n := n)) :=
antitone_succAbove.strictAnti_of_injective succAbove_pivot_injective

theorem succAbove_pivot_lt_succAbove_pivot_iff : succAbove p < succAbove q ↔ q < p :=
strictAnti_left_succAbove.lt_iff_lt

theorem succAbove_pivot_le_succAbove_pivot_iff : succAbove p ≤ succAbove q ↔ q ≤ p :=
strictAnti_left_succAbove.le_iff_le

theorem exists_unique_succAbove_eq {p i : Fin (n + 1)} (h : i ≠ p) : ∃! z, p.succAbove z = i :=
  exists_unique_of_exists_of_unique (exists_succAbove_eq h)
  (fun _ _ h₁ h₂ => succAbove_injective (x := p) (by rw [h₁, h₂]))

end SuccAbove

section PredAbove

/-- `predAbove p i` embeds `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i then pred i ((zero_le _).trans_lt h).ne'
  else castPred i ((le_of_not_lt h).trans_lt (castSucc_lt_last _)).ne

theorem predAbove_eq_pred_or_castPred (p : Fin n) (i : Fin (n + 1)) :
    (∃ h, p.predAbove i = i.pred h) ∨ (∃ h, p.predAbove i = i.castPred h) :=
  (lt_or_le p.castSucc i).by_cases
    (fun h => Or.inl ⟨((zero_le _).trans_lt h).ne', dif_pos h⟩)
    (fun h => Or.inr ⟨(h.trans_lt (castSucc_lt_last _)).ne, dif_neg h.not_lt⟩)

theorem pred_le_predAbove (p : Fin n) (i : Fin (n + 1)) (hi : i ≠ 0) :
    i.pred hi ≤ p.predAbove i := by
  rcases (p.predAbove_eq_pred_or_castPred i) with (⟨_, h⟩ | ⟨_, h⟩) <;> rw [h]
  exact (pred_lt_castPred _ _).le

theorem predAbove_le_castPred (p : Fin n) (i : Fin (n + 1)) (hi : i ≠ last n) :
    p.predAbove i ≤ i.castPred hi := by
  rcases (p.predAbove_eq_pred_or_castPred i) with (⟨_, h⟩ | ⟨_, h⟩) <;> rw [h]
  exact (pred_lt_castPred _ _).le

@[simp]
theorem predAbove_of_le_castSucc {p : Fin n} {i : Fin (n + 1)} (h : i ≤ castSucc p)
    (hi := (h.trans_lt (castSucc_lt_last _)).ne) :
    p.predAbove i = i.castPred hi := dif_neg h.not_lt
#align fin.pred_above_below Fin.predAbove_of_le_castSucc

@[simp]
theorem predAbove_of_lt_succ {p : Fin n} {i : Fin (n + 1)} (h : i < succ p)
    (hi := ((le_last _).trans_lt' h).ne) :
    p.predAbove i = i.castPred hi := predAbove_of_le_castSucc (le_castSucc_iff.mpr h)

@[simp]
theorem predAbove_of_castSucc_lt {p : Fin n} {i : Fin (n + 1)} (h : castSucc p < i)
    (hi := ((zero_le _).trans_lt h).ne') :
    p.predAbove i = i.pred hi := dif_pos h
#align fin.pred_above_above Fin.predAbove_of_castSucc_lt

@[simp]
theorem predAbove_of_succ_le {p : Fin n} {i : Fin (n + 1)} (h : succ p ≤ i)
    (hi := (h.trans_lt' (succ_pos _)).ne') :
    p.predAbove i = i.pred hi := predAbove_of_castSucc_lt (castSucc_lt_iff_succ_le.mpr h)

theorem rev_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    rev (predAbove p i) = predAbove (rev p) (rev i) := by
  rcases castSucc_lt_or_lt_succ p i with (h | h)
  · rw [predAbove_of_castSucc_lt h, rev_pred]
    exact (predAbove_of_lt_succ ((rev_castSucc _ ▸ rev_lt_rev.mpr h))).symm
  · rw [predAbove_of_lt_succ h, rev_castPred]
    exact (predAbove_of_castSucc_lt (rev_succ _ ▸ (rev_lt_rev.mpr h))).symm

lemma predAbove_eq_iff {p k : Fin n} {i : Fin (n + 1)} :
    predAbove p i = k ↔ i = succAbove (succAbove i p) k := by
  rcases castSucc_lt_or_lt_succ p i with (h | h)
  · rw [predAbove_of_castSucc_lt h, pred_eq_iff_eq_succ, succAbove_of_castSucc_lt h]
    refine Iff.intro ?_ ?_ <;>
    rintro rfl <;>
    [skip; rw [lt_succAbove_iff_lt_succ] at h] <;>
    (rw [castSucc_lt_succ_iff] at h; rw [succAbove_castSucc_of_le h])
  · rw [predAbove_of_lt_succ h, castPred_eq_iff_eq_castSucc, succAbove_of_lt_succ h]
    refine Iff.intro ?_ ?_ <;>
    rintro rfl <;>
    [skip; rw [succAbove_lt_iff_castSucc_lt] at h ] <;>
    (rw [castSucc_lt_succ_iff] at h; rw [succAbove_succ_of_le h])

lemma eq_predAbove_iff {p k : Fin n} {i : Fin (n + 1)} :
    k = predAbove p i ↔ succAbove (succAbove i p) k = i := by
  rw [eq_comm, predAbove_eq_iff, eq_comm]

lemma predAbove_lt_iff {p k : Fin n} {i : Fin (n + 1)} :
    predAbove p i < k ↔ i < succAbove (succAbove i p) k := by
  rcases lt_or_le (castSucc p) i with (hpi | hpi)
  · rw [predAbove_of_castSucc_lt hpi, succAbove_of_castSucc_lt hpi, pred_lt_iff]
    rcases le_or_lt p k with (hpk | hpk)
    · rw [succAbove_castSucc_of_le hpk]
    · rw [succAbove_castSucc_of_lt hpk, ← le_castSucc_iff]
      rw [← castSucc_lt_castSucc_iff] at hpk
      exact ((hpk.trans hpi).ne').le_iff_lt
  · rw [predAbove_of_le_castSucc hpi, succAbove_of_le_castSucc hpi, castPred_lt_iff]
    rcases le_or_lt k p with (hkp | hkp)
    · rw [succAbove_succ_of_le hkp]
    · rw [succAbove_succ_of_lt hkp, ← le_castSucc_iff]
      rw [← castSucc_lt_castSucc_iff] at hkp
      exact (((hpi.trans_lt hkp).ne).le_iff_lt).symm

lemma predAbove_le_iff {p k : Fin n} {i : Fin (n + 1)} :
    predAbove p i ≤ k ↔ i ≤ succAbove (succAbove i p) k := by
  simp_rw [le_iff_lt_or_eq, predAbove_lt_iff, predAbove_eq_iff]

lemma predAbove_gt_iff {p k : Fin n} {i : Fin (n + 1)} :
    k < predAbove p i ↔ succAbove (succAbove i p) k < i := by
  simp_rw [← not_le]
  exact predAbove_le_iff.not

lemma predAbove_ge_iff {p k : Fin n} {i : Fin (n + 1)} :
    k ≤ predAbove p i ↔ succAbove (succAbove i p) k ≤ i := by
  simp_rw [← not_lt]
  exact predAbove_lt_iff.not

lemma le_predAbove_iff_castSucc_le {i : Fin (n + 1)} {p : Fin n} :
    p ≤ predAbove p i ↔ castSucc p ≤ i := by
  rw [predAbove_ge_iff, succAbove_succAbove_le_iff_castSucc_le]

lemma predAbove_le_iff_le_succ {i : Fin (n + 1)} {p : Fin n} :
    predAbove p i ≤ p ↔ i ≤ succ p := by
  rw [predAbove_le_iff, le_succAbove_succAbove_iff_le_succ]

lemma predAbove_lt_iff_lt_castSucc {i : Fin (n + 1)} {p : Fin n} :
    predAbove p i < p ↔ i < castSucc p := by
  rw [← not_le, le_predAbove_iff_castSucc_le, not_le]

lemma lt_predAbove_iff_lt_castSucc {i : Fin (n + 1)} {p : Fin n} :
    p < predAbove p i ↔ succ p < i := by
  rw [← not_le, predAbove_le_iff_le_succ, not_le]

@[simp]
theorem predAbove_right_zero' [NeZero n] {i : Fin n} : predAbove (i : Fin n) 0 = 0 := by
  simp_rw [predAbove_eq_iff, succAbove_zero_apply, succAbove_succ_zero']
@[simp]
theorem predAbove_zero_succ' [NeZero n] {i : Fin n} : predAbove 0 (i.succ) = i := by
  simp_rw [predAbove_eq_iff, succAbove_succ_zero', succAbove_zero_apply]
@[simp]
theorem succ_predAbove_zero' [NeZero n] {j : Fin (n + 1)} (h : j ≠ 0) :
    succ (predAbove 0 j) = j := by
  rcases exists_succ_eq_of_ne_zero h with ⟨k, rfl⟩
  rw [predAbove_zero_succ']
@[simp]
theorem predAbove_zero_of_ne_zero' [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    predAbove 0 i = i.pred hi := by
  rw [← exists_succ_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_zero_succ'
#align fin.pred_above_zero Fin.predAbove_zero_of_ne_zero'
theorem predAbove_zero' [NeZero n] :
    predAbove (0 : Fin n) i = if hi : i = 0 then 0 else i.pred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_zero']
  · rw [predAbove_zero_of_ne_zero' hi]

theorem predAbove_right_zero {i : Fin (n + 1)} : predAbove i 0 = 0 := predAbove_right_zero'
theorem predAbove_zero_succ {i : Fin (n + 1)} : predAbove 0 (i.succ) = i := predAbove_zero_succ'
theorem succ_predAbove_zero {j : Fin (n + 2)} (h : j ≠ 0) : succ (predAbove 0 j) = j :=
  succ_predAbove_zero' h
@[simp]
<<<<<<< HEAD
theorem predAbove_zero_of_ne_zero {i : Fin (n + 2)} (hi : i ≠ 0) :
    predAbove 0 i = i.pred hi := by
  rw [← exists_succ_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_zero_succ
=======
theorem predAbove_zero {i : Fin (n + 2)} (hi : i ≠ 0) : predAbove 0 i = i.pred hi := by
  dsimp [predAbove]
  rw [dif_pos]
  exact pos_iff_ne_zero.mpr hi
#align fin.pred_above_zero Fin.predAbove_zero

theorem predAbove_below (p : Fin n) (i : Fin (n + 1)) (h : i ≤ castSucc p) :
    p.predAbove i = i.castLT (h.trans_lt (castSucc_lt_last _)) := by
  simp [predAbove, h.not_lt]
#align fin.pred_above_below Fin.predAbove_below
>>>>>>> Fix lint

theorem predAbove_zero : predAbove (0 : Fin (n + 1)) i = if hi : i = 0 then 0 else i.pred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_zero]
  · rw [predAbove_zero_of_ne_zero hi]

@[simp]
theorem predAbove_right_last : predAbove (i : Fin (n + 1)) (Fin.last (n + 1)) = last n := by
  simp_rw [predAbove_eq_iff, succAbove_last, succAbove_castSucc_last]
@[simp]
theorem predAbove_last_castSucc {i : Fin (n + 1)} :
    predAbove (Fin.last n) (i.castSucc) = i := by
  simp_rw [predAbove_eq_iff, succAbove_castSucc_last, succAbove_last_apply]
@[simp]
theorem predAbove_last_of_ne_last {i : Fin (n + 2)} (hi : i ≠ last _):
    predAbove (Fin.last n) i = castPred i hi := by
  rw [← exists_castSucc_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_last_castSucc
theorem predAbove_last :
    predAbove (last n) i = if hi : i = Fin.last _ then last _ else i.castPred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_last]
  · rw [predAbove_last_of_ne_last hi]
#align fin.pred_above_last_apply Fin.predAbove_last

@[simp]
lemma succAbove_succAbove_predAbove (p : Fin n) (i : Fin (n + 1)) :
    succAbove (succAbove i p) (predAbove p i) = i := by rw [← eq_predAbove_iff]

@[simp]
theorem predAbove_succAbove_succAbove {j : Fin (n + 1)} {p : Fin n} {i : Fin n} :
    predAbove p (succAbove (succAbove j p) i) = i := by
  rw [predAbove_eq_iff, succAbove_succAbove_succAbove_succAbove]

theorem predAbove_succAbove_id {j : Fin (n + 1)} {p : Fin n} :
    (predAbove p) ∘ (succAbove (succAbove j p)) = id :=
  funext (fun _ => predAbove_succAbove_succAbove)

@[simp]
lemma predAbove_predAbove_succAbove {p : Fin (n + 1)} {i : Fin n} :
    predAbove (predAbove i p) (succAbove p i) = i := by
  rw [predAbove_eq_iff, succAbove_succAbove_predAbove]

lemma predAbove_castSucc_of_le {p i : Fin n} (h : i ≤ p) : predAbove p (castSucc i) = i := by
  simp_rw [predAbove_eq_iff, succAbove_succAbove_castSucc_of_le h]

lemma predAbove_succ_of_le {p i : Fin n} (h : p ≤ i) : predAbove p (succ i) = i := by
  simp_rw [predAbove_eq_iff, succAbove_succAbove_succ_of_le h]

theorem succAbove_succAbove_succAbove_predAbove :
    succAbove (succAbove j i) (succAbove (predAbove i j) k) = succAbove j (succAbove i k) := by
  rcases castSucc_lt_or_lt_succ i j with (hij | hij)
  · cases' j using cases with j
    · exact (not_lt_bot hij).elim
    · rw [castSucc_lt_succ_iff] at hij
      rw [succAbove_succ_of_le hij, predAbove_succ_of_le hij,
      succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_le hij]
  · cases' j using lastCases with j
    · exact (not_top_lt hij).elim
    · rw [castSucc_lt_succ_iff] at hij
      rw [succAbove_castSucc_of_le hij, predAbove_castSucc_of_le hij,
      succAbove_succ_succAbove_eq_succAbove_castSucc_succAbove_of_le hij]

theorem succAbove_succAbove_comp_succAbove_predAbove :
    (succAbove (succAbove j i)) ∘ (succAbove (predAbove i j)) =
    succAbove j ∘ succAbove i :=
  funext (fun _ => succAbove_succAbove_succAbove_predAbove)

@[simp]
lemma predAbove_succ_self {i : Fin n} :
    predAbove i (succ i) = i := predAbove_succ_of_le le_rfl

@[simp]
lemma predAbove_castSucc_self {i : Fin n} :
    predAbove i (castSucc i) = i := predAbove_castSucc_of_le le_rfl

/-- `succ` commutes with `predAbove`. -/
@[simp]
theorem predAbove_succ_succ  (a : Fin n) (b : Fin (n + 1)) :
    predAbove (a.succ) (b.succ) = (a.predAbove b).succ := by
  simp_rw [predAbove_eq_iff, succAbove_succ_succ, succAbove_succAbove_predAbove]
#align fin.succ_pred_above_succ Fin.predAbove_succ_succ

/-- `castSucc` commutes with `predAbove`. -/
@[simp]
theorem predAbove_castSucc_castSucc {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    predAbove (a.castSucc) (b.castSucc) = (a.predAbove b).castSucc := by
  simp_rw [predAbove_eq_iff, succAbove_castSucc_castSucc,
  succAbove_succAbove_predAbove]

lemma succ_predAbove_of_succ_le {p : Fin n} {i : Fin (n + 1)} (h : succ p ≤ i) :
    succ (predAbove p i) = i := by rw [← predAbove_succ_succ, predAbove_succ_of_le h]

lemma succ_predAbove_of_castSucc_lt {p : Fin n} {i : Fin (n + 1)} (h : castSucc p < i) :
    succ (predAbove p i) = i := succ_predAbove_of_succ_le (castSucc_lt_iff_succ_le.mp h)

lemma castSucc_predAbove_of_le_castSucc {p : Fin n} {i : Fin (n + 1)} (h : i ≤ castSucc p) :
    castSucc (predAbove p i) = i :=
  by rw [← predAbove_castSucc_castSucc, predAbove_castSucc_of_le h]

lemma castSucc_predAbove_of_lt_succ {p : Fin n} {i : Fin (n + 1)} (h : i < succ p) :
    castSucc (predAbove p i) = i := castSucc_predAbove_of_le_castSucc (le_castSucc_iff.mpr h)

theorem castSucc_predAbove_lt_of_lt {i j : Fin (n + 1)} {p : Fin n}
    (h : i < j) : castSucc (predAbove p i) < j := by
  rcases castSucc_lt_or_lt_succ p i with (hpi | hpi)
  · rw [castSucc_lt_iff_succ_le, succ_predAbove_of_castSucc_lt hpi]
    exact h.le
  · rw [castSucc_predAbove_of_lt_succ hpi]
    exact h

theorem succ_predAbove_le_of_lt {i j : Fin (n + 1)} {p : Fin n}
    (h : i < j) : succ (predAbove p i) ≤ j := by
  rw [← castSucc_lt_iff_succ_le]
  exact castSucc_predAbove_lt_of_lt h

theorem le_castSucc_predAbove_of_lt {i j : Fin (n + 1)} {p : Fin n}
    (h : i < j) : i ≤ castSucc (predAbove p j)  := by
  rcases castSucc_lt_or_lt_succ p j with (hpj | hpj)
  · rw [le_castSucc_iff, succ_predAbove_of_castSucc_lt hpj]
    exact h
  · rw [castSucc_predAbove_of_lt_succ hpj]
    exact h.le

theorem lt_succ_predAbove_of_lt {i j : Fin (n + 1)} {p : Fin n}
    (h : i < j) : i < succ (predAbove p j)  := by
  rw [← le_castSucc_iff]
  exact le_castSucc_predAbove_of_lt h

lemma eq_or_castSucc_succ_of_predAbove_eq (h : predAbove k i = predAbove k j) :
    i = j ∨ (j = castSucc k ∧ i = succ k) ∨
    (j = succ k ∧ i = castSucc k) := by
  rcases castSucc_lt_or_lt_succ k i with (hki | hki) <;>
  rcases castSucc_lt_or_lt_succ k j with (hkj | hkj)
  · rw [← succ_inj, succ_predAbove_of_castSucc_lt hki, succ_predAbove_of_castSucc_lt hkj] at h
    exact Or.inl h
  · refine Or.inr (Or.inl ?_)
    rw [← succ_inj, succ_predAbove_of_castSucc_lt hki, ← castSucc_inj, ← succ_castSucc,
    castSucc_predAbove_of_lt_succ hkj] at h
    simp_rw [le_antisymm_iff, le_castSucc_iff, ← castSucc_lt_iff_succ_le]
    refine ⟨⟨hkj, ?_⟩, ⟨?_, hki⟩⟩
    · rw [← castSucc_lt_castSucc_iff, h, castSucc_lt_iff_succ_le, succ_le_succ_iff] at hki
      exact hki
    · rw [← succ_lt_succ_iff, ← h, castSucc_lt_iff_succ_le, succ_le_succ_iff] at hkj
      exact hkj
  · refine Or.inr (Or.inr ?_)
    rw [← succ_inj, succ_predAbove_of_castSucc_lt hkj, ← castSucc_inj, ← succ_castSucc,
    castSucc_predAbove_of_lt_succ hki] at h
    simp_rw [le_antisymm_iff, le_castSucc_iff, ← castSucc_lt_iff_succ_le]
    refine ⟨⟨?_, hkj⟩, ⟨hki, ?_⟩⟩
    · rw [← succ_lt_succ_iff, h, castSucc_lt_iff_succ_le, succ_le_succ_iff] at hki
      exact hki
    · rw [← castSucc_lt_castSucc_iff, ← h, castSucc_lt_iff_succ_le, succ_le_succ_iff] at hkj
      exact hkj
  · rw [← castSucc_inj, castSucc_predAbove_of_lt_succ hki, castSucc_predAbove_of_lt_succ hkj] at h
    exact Or.inl h

lemma predAbove_eq_iff_eq_or_castSucc_succ :
    predAbove k i = predAbove k j ↔ (i = j ∨ (j = castSucc k ∧ i = succ k) ∨
    (j = succ k ∧ i = castSucc k)) := by
  refine Iff.intro eq_or_castSucc_succ_of_predAbove_eq ?_
  rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · rfl
  · rw [predAbove_succ_self, predAbove_castSucc_self]
  · rw [predAbove_succ_self, predAbove_castSucc_self]

lemma predAbove_apply_eq_iff : predAbove i k = predAbove j k ↔
    (castSucc j < k ∧ castSucc i < k) ∨ (k ≤ castSucc j ∧ k ≤ castSucc i) := by
  simp_rw [predAbove_eq_iff]
  conv =>
    lhs
    lhs
    rw [← succAbove_succAbove_predAbove j k]
  simp_rw [succAbove_at_eq_iff_castSucc]
  rcases le_or_lt k (castSucc j) with (h | h)
  · simp_rw [castSucc_predAbove_of_le_castSucc h, succAbove_le_iff_succAbove_lt,
    lt_succAbove_iff_le_castSucc, succAbove_lt_iff_castSucc_lt]
  · simp_rw [le_castSucc_iff, castSucc_lt_iff_succ_le, succ_predAbove_of_castSucc_lt h,
    le_succAbove_iff_lt_succAbove, lt_succAbove_iff_lt_succ, succAbove_lt_iff_succ_le]

theorem predAbove_pred_eq_predAbove_castPred
    {i j : Fin (n + 1)} (h : i ≠ j) (h₁ : j ≠ 0) (h₂ : j ≠ last n) :
    predAbove (j.pred h₁) i = predAbove (j.castPred h₂) i := by
  simp_rw [predAbove_apply_eq_iff, castSucc_castPred, le_castSucc_iff,
  castSucc_lt_iff_succ_le, succ_pred]
  rcases h.lt_or_lt with (h | h)
  · exact Or.inr ⟨h.le, h⟩
  · exact Or.inl ⟨h, h.le⟩

lemma predAbove_castSucc_eq_iff : predAbove i (castSucc k) = predAbove j (castSucc k) ↔
    (j < k ∧ i < k) ∨ (k ≤ j ∧ k ≤ i) := by
  simp_rw [predAbove_apply_eq_iff, castSucc_lt_castSucc_iff, castSucc_le_castSucc_iff]

lemma predAbove_succ_eq_iff : predAbove i (succ k) = predAbove j (succ k) ↔
    (j ≤ k ∧ i ≤ k) ∨ (k < j ∧ k < i) := by
  simp_rw [predAbove_apply_eq_iff, castSucc_lt_succ_iff, succ_le_castSucc_iff]

theorem predAbove_predAbove {i j : Fin (n + 1)} (p q : Fin n) (hij : i ≠ j) :
    predAbove (predAbove p j) i = predAbove (predAbove q j) i := by
  rcases predAbove_eq_pred_or_castPred p j with (⟨h, heq⟩ | ⟨h, heq⟩) <;>
  rw [heq] <;>
  rcases predAbove_eq_pred_or_castPred q j with (⟨h₂, heq₂⟩ | ⟨h₂, heq₂⟩) <;>
  rw [heq₂]
  · rw [predAbove_pred_eq_predAbove_castPred hij h h₂]
  · rw [predAbove_pred_eq_predAbove_castPred hij h₂ h]

@[simp]
theorem succAbove_predAbove_predAbove {i j : Fin (n + 1)} (h : i ≠ j) (p : Fin n) :
    succAbove j (predAbove (predAbove p j) i) = i := by
  cases n
  · exact p.elim0
  · rw [predAbove_predAbove p 0 h]
    cases' j using cases with j
    · rw [succAbove_zero, predAbove_right_zero, succ_predAbove_zero h]
    · rw [predAbove_zero_succ]
      rcases lt_or_le (castSucc j) i with (hji | hji)
      · rw [← succ_inj, ← succAbove_succ_succ, succ_predAbove_of_castSucc_lt hji]
        rw [castSucc_lt_iff_succ_le, h.symm.le_iff_lt] at hji
        exact succAbove_succ_of_lt hji
      · rw [← castSucc_inj, ← succAbove_castSucc_castSucc, castSucc_predAbove_of_le_castSucc hji]
        rw [le_castSucc_iff] at hji
        exact succAbove_castSucc_of_lt hji

theorem succAbove_comp_predAbove_predAbove_left_cancel (f : α → Fin (n + 1))
    {j : Fin (n + 1)} (h : ∀ a, f a ≠ j) {p : Fin n} :
    (succAbove j) ∘ (predAbove (predAbove p j)) ∘ f = f :=
  funext (fun a => succAbove_predAbove_predAbove (h a) p)

lemma succAbove_eq_iff (h : i ≠ j) (k : Fin n) :
    succAbove j p = i ↔ p = predAbove (predAbove k j) i := by
  rw [← succAbove_inj j, succAbove_predAbove_predAbove h]

lemma eq_succAbove_iff (h : i ≠ j) (k : Fin n) :
    i = succAbove j p ↔ predAbove (predAbove k j) i = p := by
  rw [eq_comm, succAbove_eq_iff h, eq_comm]

theorem predAbove_predAbove_eq_choose_succAbove_exists {i j : Fin (n + 1)} (h : i ≠ j) {p : Fin n} :
    predAbove (predAbove p j) i = (exists_succAbove_eq h).choose := by
  rw [← succAbove_inj j, succAbove_predAbove_predAbove h, (exists_succAbove_eq h).choose_spec]

theorem predAbove_castSucc_succ {n : ℕ} {a : Fin n} {b : Fin (n + 1)} (h : b ≠ castSucc a) :
    predAbove (a.castSucc) (b.succ) = (a.predAbove b).succ := by
  simp_rw [← predAbove_succ_succ, predAbove_succ_eq_iff, ← castSucc_lt_iff_succ_le,
  ← le_castSucc_iff, h.le_iff_lt, h.symm.le_iff_lt, and_self, lt_or_lt_iff_ne]
  exact h.symm

theorem predAbove_succ_castSucc {n : ℕ} {a : Fin n} {b : Fin (n + 1)} (h : b ≠ succ a) :
    predAbove (a.succ) (b.castSucc) = (a.predAbove b).castSucc := by
  simp_rw [← predAbove_castSucc_castSucc, predAbove_castSucc_eq_iff, castSucc_lt_iff_succ_le,
  le_castSucc_iff, h.le_iff_lt, h.symm.le_iff_lt, and_self, lt_or_lt_iff_ne]
  exact h.symm

lemma predAbove_succ_succAbove_castSucc_of_le_castSucc {i k : Fin (n + 1)} {j : Fin n}
    (h : i ≤ castSucc j) : predAbove (succ j) (succAbove (castSucc i) k) =
    succAbove i (predAbove j k) := by
  rcases le_or_lt i k with (hik | hik)
  · rw [succAbove_castSucc_of_le hik, predAbove_succ_succ, succAbove_of_le_castSucc]
    rcases le_or_lt k (castSucc j) with (hjk | hjk)
    · rw [castSucc_predAbove_of_le_castSucc hjk]
      exact hik
    · rw [le_castSucc_iff, succ_predAbove_of_castSucc_lt hjk]
      exact h.trans_lt hjk
  · rw [succAbove_castSucc_of_lt hik,
      succAbove_of_castSucc_lt ((castSucc_predAbove_of_le_castSucc
    ((h.trans_lt' hik).le)).symm ▸ hik)]
    exact predAbove_succ_castSucc (((h.trans_lt' hik).trans (castSucc_lt_succ _)).ne)

/- The second simplicial identity. -/
lemma predAbove_succ_comp_succAbove_castSucc {i : Fin (n + 1)} {j : Fin n}
    (h : i ≤ castSucc j) :
    (predAbove (succ j)) ∘ (succAbove (castSucc i)) = (succAbove i) ∘ (predAbove j) :=
  funext (fun _ => predAbove_succ_succAbove_castSucc_of_le_castSucc h)

lemma predAbove_castSucc_succAbove_succ_of_castSucc_lt {i k : Fin (n + 1)} {j : Fin n}
    (h : castSucc j < i) : predAbove (castSucc j) (succAbove (succ i) k) =
  succAbove i (predAbove j k) := by
  rcases le_or_lt k i with (hik | hik)
  · rw [succAbove_succ_of_le hik, predAbove_castSucc_castSucc, succAbove_of_castSucc_lt]
    rcases le_or_lt k (castSucc j) with (hjk | hjk)
    · rw [castSucc_predAbove_of_le_castSucc hjk]
      exact hjk.trans_lt h
    · rw [castSucc_lt_iff_succ_le, succ_predAbove_of_castSucc_lt hjk]
      exact hik
  · rw [succAbove_succ_of_lt hik,
      succAbove_of_lt_succ ((succ_predAbove_of_castSucc_lt (h.trans hik)).symm ▸ hik)]
    exact predAbove_castSucc_succ (h.trans hik).ne'

/- The fourth simplicial identity. -/
lemma predAbove_castSucc_comp_succAbove_castSucc {i : Fin (n + 1)} {j : Fin n}
    (h : castSucc j < i) :
    (predAbove (castSucc j)) ∘ (succAbove (succ i)) = (succAbove i) ∘ (predAbove j) :=
  funext (fun _ => predAbove_castSucc_succAbove_succ_of_castSucc_lt h)

@[simp]
lemma predAbove_succAbove_succAbove_succAbove_castSucc_succ {i k : Fin (n + 1)} {j : Fin n} :
    predAbove (succAbove i j) (succAbove (succAbove j.succ.castSucc i) k) =
    succAbove i (predAbove j k) := by
  rcases le_or_lt i (castSucc j) with (hij | hij)
  · rw [succAbove_of_le_castSucc hij]
    rw [succAbove_castSucc_of_lt (le_castSucc_iff.mp hij)]
    exact predAbove_succ_succAbove_castSucc_of_le_castSucc hij
  · rw [succAbove_of_castSucc_lt hij]
    rw [succAbove_castSucc_of_le (castSucc_lt_iff_succ_le.mp hij)]
    exact predAbove_castSucc_succAbove_succ_of_castSucc_lt hij

lemma predAbove_succAbove_castSucc {k i : Fin n} :
    predAbove i (succAbove (castSucc i) k) = k := by
  rcases le_or_lt i k with (h | h)
  · rw [succAbove_castSucc_of_le h, predAbove_succ_of_le h]
  · rw [succAbove_castSucc_of_lt h, predAbove_castSucc_of_le h.le]

/- First part of the third simplicial identity. -/
lemma predAbove_comp_succAbove_castSucc {i : Fin n} :
    (predAbove i) ∘ (succAbove (castSucc i)) = id :=
  funext (fun _ => predAbove_succAbove_castSucc)

lemma predAbove_succAbove_succ {k i : Fin n} :
    predAbove i (succAbove (succ i) k) = k := by
  rcases le_or_lt k i with (h | h)
  · rw [succAbove_succ_of_le h, predAbove_castSucc_of_le h]
  · rw [succAbove_succ_of_lt h, predAbove_succ_of_le h.le]

/- Second part of the third simplicial identity. -/
lemma predAbove_comp_succAbove_succ {i : Fin n} :
    (predAbove i) ∘ (succAbove (succ i)) = id :=
  funext (fun _ => predAbove_succAbove_succ)

lemma predAbove_predAbove_castSucc_eq_predAbove_predAbove_succ_same {k : Fin (n + 2)} {i : Fin n} :
    predAbove i (predAbove (castSucc i) k) = predAbove i (predAbove (succ i) k) := by
  cases' k using lastCases with k
  · simp only [predAbove_right_last]
  · cases' k using cases with k
    · simp only [castSucc_zero, predAbove_right_zero]
    · rw [predAbove_castSucc_castSucc]
      rcases eq_or_ne i k with (rfl | h)
      · simp only [predAbove_succ_self, predAbove_castSucc_self]
      · rw [predAbove_succ_castSucc ((succ_injective _).ne_iff.mpr h.symm)]

/- The special case of the fifth simplicial identity. -/
lemma predAbove_comp_predAbove_castSucc_eq_predAbove_comp_predAbove_succ {i : Fin n} :
    (predAbove i) ∘ (predAbove (castSucc i)) = (predAbove i) ∘ (predAbove (succ i)) :=
  funext (fun _ => predAbove_predAbove_castSucc_eq_predAbove_predAbove_succ_same)

lemma predAbove_predAbove_castSucc_castSucc_succ_of_lt (hik : i < k) :
    predAbove j (predAbove (castSucc i) (castSucc (succ k))) =
    predAbove i (predAbove (succ j) (castSucc (succ k))) := by
  rw [← succ_castSucc, predAbove_succ_of_le ((castSucc_le_castSucc_iff).mpr hik.le)]
  rcases le_or_lt k j with (hkj | hkj)
  · rw [predAbove_succ_succ, predAbove_castSucc_of_le hkj,
    predAbove_succ_of_le hik.le]
  · rw [predAbove_succ_of_le ((succ_le_castSucc_iff).mpr hkj),
    predAbove_castSucc_eq_iff]
    exact Or.inl ⟨hik, hkj⟩

lemma predAbove_predAbove_castSucc_castSucc_succ_of_gt (hkj : k < j) :
    predAbove j (predAbove (castSucc i) (castSucc (succ k))) =
    predAbove i (predAbove (succ j) (castSucc (succ k))) := by
  rw [predAbove_castSucc_of_le ((succ_le_succ_iff).mpr hkj.le)]
  rcases le_or_lt i k with (hik | hik)
  · rw [← succ_castSucc, predAbove_succ_of_le ((castSucc_le_castSucc_iff).mpr hik),
    predAbove_succ_of_le hik, predAbove_castSucc_of_le hkj.le]
  · rw [predAbove_castSucc_of_le ((succ_le_castSucc_iff).mpr hik), predAbove_succ_eq_iff]
    exact Or.inr ⟨hik, hkj⟩

lemma predAbove_predAbove_castSucc_castSucc_succ_of_gt_of_lt (hik : k < i) (hjk : j < k) :
    predAbove j (predAbove (castSucc i) (castSucc (succ k))) =
    predAbove i (predAbove (succ j) (castSucc (succ k))) := by
  rw [predAbove_castSucc_of_le ((succ_le_castSucc_iff).mpr hik), predAbove_succ_of_le hjk.le,
      ← succ_castSucc, predAbove_succ_of_le ((succ_le_castSucc_iff).mpr hjk),
      predAbove_castSucc_of_le hik.le]

lemma predAbove_predAbove_castSucc_eq_predAbove_predAbove_succ {k : Fin (n + 2)} {i j : Fin n}
    (h : i ≤ j) : predAbove j (predAbove (castSucc i) k) = predAbove i (predAbove (succ j) k) := by
  cases n
  · exact i.elim0
  · cases' k using lastCases with k
    · simp only [predAbove_right_last]
    · cases' k using cases with k
      · simp only [castSucc_zero, predAbove_right_zero]
      · rcases lt_or_le i k with (hik | hik)
        · rw [predAbove_predAbove_castSucc_castSucc_succ_of_lt hik]
        · rcases lt_or_le k j with (hkj | hkj)
          · rw [predAbove_predAbove_castSucc_castSucc_succ_of_gt hkj]
          · rw [(le_antisymm h (hkj.trans hik)),
            predAbove_predAbove_castSucc_eq_predAbove_predAbove_succ_same]

/- The general case of the fifth simplicial identity. -/
lemma predAbove_comp {i j : Fin n} (h : i ≤ j) :
    (predAbove j) ∘ (predAbove (castSucc i)) = (predAbove i) ∘ (predAbove (succ j)) :=
  funext (fun _ => predAbove_predAbove_castSucc_eq_predAbove_predAbove_succ h)

@[simp]
<<<<<<< HEAD
theorem succAbove_succAbove_predAbove_succAbove {p : Fin n} {j : Fin (n + 1)} :
    succAbove (succAbove j p) (predAbove p (succAbove j p)) = succAbove (succAbove j p) p := by
  rcases castSucc_lt_or_lt_succ p j with (h | h)
  · rw [succAbove_of_castSucc_lt h, predAbove_castSucc_self]
  · rw [succAbove_of_lt_succ h, predAbove_succ_self]

/-- TODO -/
def succAbove_predAbove_equiv : Equiv.Perm (Fin (n + 1) × Fin n) where
  toFun := fun ⟨p, i⟩ => (p.succAbove i, i.predAbove p)
  invFun := fun ⟨p, i⟩ => (p.succAbove i, i.predAbove p)
  left_inv _ := by simp_rw [predAbove_predAbove_succAbove, succAbove_succAbove_predAbove]
  right_inv _ := by simp_rw [predAbove_predAbove_succAbove, succAbove_succAbove_predAbove]

theorem predAbove_le_predAbove_of_le (p : Fin n) (a b : Fin (n + 1)) (hab : a ≤ b) :
    predAbove p a ≤ predAbove p b := by
  rcases castSucc_lt_or_lt_succ p a with (hpa | hpa) <;>
  rcases castSucc_lt_or_lt_succ p b with (hpb | hpb)
  · rw [← succ_le_succ_iff, succ_predAbove_of_castSucc_lt hpa, succ_predAbove_of_castSucc_lt hpb]
    exact hab
  · exact (hab.not_lt (le_of_castSucc_lt_of_succ_lt hpa hpb)).elim
  · rw [← castSucc_le_castSucc_iff, castSucc_predAbove_of_lt_succ hpa, ← succ_le_succ_iff,
    succ_castSucc, succ_predAbove_of_castSucc_lt hpb, succ_le_castSucc_iff]
    exact le_of_castSucc_lt_of_succ_lt hpb hpa
  · rw [← castSucc_le_castSucc_iff, castSucc_predAbove_of_lt_succ hpa,
    castSucc_predAbove_of_lt_succ hpb]
    exact hab

theorem predAbove_right_monotone (p : Fin n) : Monotone p.predAbove :=
  predAbove_le_predAbove_of_le _
#align fin.pred_above_right_monotone Fin.predAbove_right_monotone

theorem predAbove_le_predAbove_of_le_right (i : Fin (n + 1)) (a b : Fin n) (hab : a ≤ b) :
    predAbove a i ≤ predAbove b i := by
  rcases castSucc_lt_or_lt_succ a i with (hai | hai) <;>
  rcases castSucc_lt_or_lt_succ b i with (hbi | hbi)
  · rw [← succ_le_succ_iff, succ_predAbove_of_castSucc_lt hai, succ_predAbove_of_castSucc_lt hbi]
  · rw [← castSucc_le_castSucc_iff, castSucc_predAbove_of_lt_succ hbi, ← succ_le_succ_iff,
    succ_castSucc, succ_predAbove_of_castSucc_lt hai]
    exact (castSucc_lt_succ _).le
  · rw [castSucc_lt_iff_succ_le] at hbi
    rw [← succ_le_succ_iff] at hab
    exact ((hab.trans hbi).not_lt hai).elim
  · rw [← castSucc_le_castSucc_iff, castSucc_predAbove_of_lt_succ hai,
    castSucc_predAbove_of_lt_succ hbi]

theorem predAbove_left_monotone (i : Fin (n + 1)) :
    Monotone fun p => predAbove p i := predAbove_le_predAbove_of_le_right _
#align fin.pred_above_left_monotone Fin.predAbove_left_monotone

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
theorem succAbove_castSucc_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  rw [succAbove_eq_iff h p, predAbove_castSucc_self]
#align fin.succ_above_pred_above Fin.succAbove_castSucc_predAbove

lemma succAbove_castSucc_predAbove_castSucc {p : Fin n} :
    succAbove (p.castSucc) (predAbove p (p.castSucc)) = succ p := by
  rw [predAbove_castSucc_self, succAbove_castSucc_self]

@[simp]
theorem succAbove_succ_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ succ p) :
    succAbove (p.succ) (predAbove p i) = i := by
  rw [succAbove_eq_iff h p, predAbove_succ_self]
lemma succAbove_succ_predAbove_succ {p : Fin n} :
    succAbove (p.succ) (predAbove p (succ p)) = castSucc p := by
  rw [predAbove_succ_self, succAbove_succ_self]

/-- Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
theorem predAbove_of_succAbove_castSucc (p : Fin n) (i : Fin n) :
    p.predAbove (p.castSucc.succAbove i) = i := by
  rw [← succAbove_succ_self, predAbove_succAbove_succAbove]
#align fin.pred_above_succ_above Fin.predAbove_of_succAbove_castSucc
@[simp]
theorem predAbove_of_succAbove_succ (p : Fin n) (i : Fin n) :
    p.predAbove (p.succ.succAbove i) = i := by
  rw [← succAbove_castSucc_self, predAbove_succAbove_succAbove]
=======
theorem succ_predAbove_succ {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h₁ | h₂ := lt_or_le (castSucc a) b
  · rw [Fin.predAbove_above _ _ h₁, Fin.succ_pred, Fin.predAbove_above, Fin.pred_succ]
    simpa only [lt_iff_val_lt_val, coe_castSucc, val_succ, add_lt_add_iff_right] using
      h₁
  · cases' n with n
    · exfalso
      exact not_lt_zero' a.is_lt
    · rw [Fin.predAbove_below a b h₂,
        Fin.predAbove_below a.succ b.succ
          (by
            simpa only [le_iff_val_le_val, val_succ, coe_castSucc, add_le_add_iff_right]
              using h₂)]
      ext
      simp only [val_last, coe_castLT, val_succ]
#align fin.succ_pred_above_succ Fin.succ_predAbove_succ
>>>>>>> Redefinition of castPred

end PredAbove

#align fin.coe_clamp Fin.coe_clamp

@[simp]
theorem coe_ofNat_eq_mod (m n : ℕ) [NeZero m] :
    ((n : Fin m) : ℕ) = n % m :=
  rfl
#align fin.coe_of_nat_eq_mod Fin.coe_ofNat_eq_mod

theorem forall_fin_succ' {P : Fin (n + 1) → Prop} :
    (∀ i, P i) ↔ (∀ i : Fin n, P i.castSucc) ∧ P (.last _) :=
  ⟨fun H => ⟨fun _ => H _, H _⟩, fun ⟨H0, H1⟩ i => Fin.lastCases H1 H0 i⟩

-- to match `Fin.eq_zero_or_eq_succ`
theorem eq_castSucc_or_eq_last {n : Nat} (i : Fin (n + 1)) :
    (∃ j : Fin n, i = j.castSucc) ∨ i = last n := by
  induction i using reverseInduction with
  | last => right; rfl
  | cast n => left; exact ⟨_, rfl⟩

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
  simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)]
#align fin.mul_one Fin.mul_one'

#align fin.mul_comm Fin.mul_comm

protected theorem one_mul' [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by
  rw [Fin.mul_comm, Fin.mul_one']
#align fin.one_mul Fin.one_mul'

protected theorem mul_zero' [NeZero n] (k : Fin n) : k * 0 = 0 := by simp [eq_iff_veq, mul_def]
#align fin.mul_zero Fin.mul_zero'

protected theorem zero_mul' [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by
  simp [eq_iff_veq, mul_def]
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
