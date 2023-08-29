/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.WithZero
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
* `Fin.succAboveEmb p` : `Fin.auccAbove` as an `OrderEmbedding`, embed `Fin n` into `Fin (n + 1)`
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
  -- ⊢ HEq f g ↔ ∀ (i : Fin k), f i = g { val := ↑i, isLt := (_ : ↑i < k) }
  simp [Function.funext_iff]
  -- 🎉 no goals
#align fin.heq_fun_iff Fin.heq_fun_iff

/-- Assume `k = l` and `k' = l'`.
If two functions `Fin k → Fin k' → α` and `Fin l → Fin l' → α` are equal on each pair,
then they coincide (in the heq sense). -/
protected theorem heq_fun₂_iff {α : Sort*} {k l k' l' : ℕ} (h : k = l) (h' : k' = l')
  {f : Fin k → Fin k' → α} {g : Fin l → Fin l' → α} :
    HEq f g ↔ ∀ (i : Fin k) (j : Fin k'), f i j = g ⟨(i : ℕ), h ▸ i.2⟩ ⟨(j : ℕ), h' ▸ j.2⟩ := by
  subst h
  -- ⊢ HEq f g ↔ ∀ (i : Fin k) (j : Fin k'), f i j = g { val := ↑i, isLt := (_ : ↑i …
  subst h'
  -- ⊢ HEq f g ↔ ∀ (i : Fin k) (j : Fin k'), f i j = g { val := ↑i, isLt := (_ : ↑i …
  simp [Function.funext_iff]
  -- 🎉 no goals

protected theorem heq_ext_iff {k l : ℕ} (h : k = l) {i : Fin k} {j : Fin l} :
    HEq i j ↔ (i : ℕ) = (j : ℕ) := by
  subst h
  -- ⊢ HEq i j ↔ ↑i = ↑j
  simp [val_eq_val]
  -- 🎉 no goals
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
                                                      -- 🎉 no goals
#align fin.min_coe Fin.min_val

-- @[simp] -- Porting note: simp can prove this
theorem max_val {a : Fin n} : max (a : ℕ) n = n := by simp
                                                      -- 🎉 no goals
#align fin.max_coe Fin.max_val

instance {n : ℕ} : PartialOrder (Fin n) := by infer_instance
                                              -- 🎉 no goals

theorem val_strictMono : StrictMono (val : Fin n → ℕ) := fun _ _ => id
#align fin.coe_strict_mono Fin.val_strictMono

/-- The equivalence `Fin n ≃ { i // i < n }` is an order isomorphism. -/
@[simps! apply symm_apply]
def orderIsoSubtype : Fin n ≃o { i // i < n } :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])
                              -- 🎉 no goals
                                                   -- 🎉 no goals
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
  -- 🎉 no goals
#align fin.pos_iff_ne_zero Fin.pos_iff_ne_zero'

#align fin.eq_zero_or_eq_succ Fin.eq_zero_or_eq_succ
#align fin.eq_succ_of_ne_zero Fin.eq_succ_of_ne_zero

/-- `Fin.rev` as an `Equiv.Perm`, the antitone involution `Fin n → Fin n` given by
`i ↦ n-(i+1)`. -/
def revPerm : Equiv.Perm (Fin n) :=
  (Involutive.toPerm fun i => ⟨n - (i + 1), tsub_lt_self i.pos (Nat.succ_pos _)⟩) fun i =>
    ext <| by
      dsimp only
      -- ⊢ n - (n - (↑i + 1) + 1) = ↑i
      rw [← tsub_tsub, tsub_tsub_cancel_of_le (Nat.add_one_le_iff.2 i.is_lt),
        add_tsub_cancel_right]
#align fin.rev Fin.revPerm

-- porting note: dot notation of the form `i.revPerm` is broken here and throughout
@[simp]
theorem val_revPerm (i : Fin n) : (revPerm i : ℕ) = n - (i + 1) :=
  rfl
#align fin.coe_rev Fin.val_revPerm

theorem revPerm_involutive : Involutive (@revPerm n) :=
  Involutive.toPerm_involutive _
#align fin.rev_involutive Fin.revPerm_involutive

theorem revPerm_injective : Injective (@revPerm n) :=
  revPerm_involutive.injective
#align fin.rev_injective Fin.revPerm_injective

theorem revPerm_surjective : Surjective (@revPerm n) :=
  revPerm_involutive.surjective
#align fin.rev_surjective Fin.revPerm_surjective

theorem revPerm_bijective : Bijective (@revPerm n) :=
  revPerm_involutive.bijective
#align fin.rev_bijective Fin.revPerm_bijective

-- @[simp] -- Porting note: simp can prove this
theorem revPerm_inj {i j : Fin n} : revPerm i = revPerm j ↔ i = j :=
  revPerm_injective.eq_iff
#align fin.rev_inj Fin.revPerm_inj

@[simp]
theorem revPerm_revPerm (i : Fin n) : revPerm (revPerm i) = i :=
  revPerm_involutive _
#align fin.rev_rev Fin.revPerm_revPerm

@[simp]
theorem revPerm_symm : (@revPerm n).symm = revPerm :=
  rfl
#align fin.rev_symm Fin.revPerm_symm

theorem revPerm_eq {n a : ℕ} (i : Fin (n + 1)) (h : n = a + i) :
    revPerm i = ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro h.symm)⟩ := by
  ext
  -- ⊢ ↑(↑revPerm i) = ↑{ val := a, isLt := (_ : a < Nat.succ n) }
  dsimp
  -- ⊢ n + 1 - (↑i + 1) = a
  conv_lhs =>
    congr
    rw [h]
  rw [add_assoc, add_tsub_cancel_right]
  -- 🎉 no goals
#align fin.rev_eq Fin.revPerm_eq

@[simp]
theorem revPerm_le_revPerm {i j : Fin n} : revPerm i ≤ revPerm j ↔ j ≤ i := by
  simp only [le_iff_val_le_val, val_revPerm, tsub_le_tsub_iff_left (Nat.add_one_le_iff.2 j.is_lt),
    add_le_add_iff_right, iff_self]
#align fin.rev_le_rev Fin.revPerm_le_revPerm

@[simp]
theorem revPerm_lt_revPerm {i j : Fin n} : revPerm i < revPerm j ↔ j < i :=
  lt_iff_lt_of_le_iff_le revPerm_le_revPerm
#align fin.rev_lt_rev Fin.revPerm_lt_revPerm

/-- `Fin.rev n` as an order-reversing isomorphism. -/
@[simps! apply toEquiv]
def revOrderIso {n} : (Fin n)ᵒᵈ ≃o Fin n :=
  ⟨OrderDual.ofDual.trans revPerm, revPerm_le_revPerm⟩
#align fin.rev_order_iso Fin.revOrderIso
#align fin.rev_order_iso_apply Fin.revOrderIso_apply
#align fin.rev_order_iso_to_equiv Fin.revOrderIso_toEquiv

@[simp]
theorem revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual (revPerm i) :=
  rfl
#align fin.rev_order_iso_symm_apply Fin.revOrderIso_symm_apply

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
  -- ⊢ ↑(↑e { val := i, isLt := hi }) = ↑{ val := i, isLt := hi }
  dsimp only
  -- ⊢ ↑(↑e { val := i, isLt := hi }) = i
  induction' i using Nat.strong_induction_on with i h
  -- ⊢ ↑(↑e { val := i, isLt := hi }) = i
  refine' le_antisymm (forall_lt_iff_le.1 fun j hj => _) (forall_lt_iff_le.1 fun j hj => _)
  -- ⊢ j < i
  · have := e.symm.lt_iff_lt.2 (mk_lt_of_lt_val hj)
    -- ⊢ j < i
    rw [e.symm_apply_apply] at this
    -- ⊢ j < i
    -- porting note: convert was abusing definitional equality
    have : _ < i := this
    -- ⊢ j < i
    convert this
    -- ⊢ j = ↑(↑(OrderIso.symm e) { val := j, isLt := (_ : j < m) })
    simpa using h _ this (e.symm _).is_lt
    -- 🎉 no goals
  · rwa [← h j hj (hj.trans hi), ← lt_iff_val_lt_val, e.lt_iff_lt]
    -- 🎉 no goals
#align fin.coe_order_iso_apply Fin.coe_orderIso_apply

instance orderIso_subsingleton : Subsingleton (Fin n ≃o α) :=
  ⟨fun e e' => by
    ext i
    -- ⊢ ↑e i = ↑e' i
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

#align fin.mk_one Fin.mk_one

instance nontrivial {n : ℕ} : Nontrivial (Fin (n + 2)) where
  exists_pair_ne := ⟨0, 1, (ne_iff_vne 0 1).mpr (by simp only [val_one, val_zero])⟩
                                                    -- 🎉 no goals

theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  rcases n with (_ | _ | n) <;>
  simp [←Nat.one_eq_succ_zero, Fin.nontrivial, not_nontrivial, Nat.succ_le_iff]
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
-- porting note: here and in the next lemma, had to use `←Nat.one_eq_succ_zero`.
#align fin.nontrivial_iff_two_le Fin.nontrivial_iff_two_le

#align fin.subsingleton_iff_le_one Fin.subsingleton_iff_le_one

section Monoid

instance addCommSemigroup (n : ℕ) : AddCommSemigroup (Fin n) where
  add := (· + ·)
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc]
                  -- 🎉 no goals
  add_comm := by simp [eq_iff_veq, add_def, add_comm]
                 -- 🎉 no goals
#align fin.add_comm_semigroup Fin.addCommSemigroup

--Porting note: removing `simp`, `simp` can prove it with AddCommMonoid instance
protected theorem add_zero [NeZero n] (k : Fin n) : k + 0 = k := by
  simp only [add_def, val_zero', add_zero, mod_eq_of_lt (is_lt k)]
  -- 🎉 no goals
#align fin.add_zero Fin.add_zero

--Porting note: removing `simp`, `simp` can prove it with AddCommMonoid instance
protected theorem zero_add [NeZero n] (k : Fin n) : 0 + k = k := by
  simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]
  -- 🎉 no goals
#align fin.zero_add Fin.zero_add

instance [NeZero n] : OfNat (Fin n) a where
  ofNat := Fin.ofNat' a (NeZero.pos n)

section from_ad_hoc

@[simp] lemma ofNat'_zero [NeZero n] : (Fin.ofNat' 0 h : Fin n) = 0 := rfl
@[simp] lemma ofNat'_one [NeZero n] : (Fin.ofNat' 1 h : Fin n) = 1 := rfl

end from_ad_hoc

instance (n) : AddCommSemigroup (Fin n) where
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc]
                  -- 🎉 no goals
  add_comm := by simp [eq_iff_veq, add_def, add_comm]
                 -- 🎉 no goals

instance addCommMonoid (n : ℕ) [NeZero n] : AddCommMonoid (Fin n) where
  add := (· + ·)
  zero := 0
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
  -- ⊢ ↑(bit0 { val := val✝, isLt := isLt✝ }) = bit0 ↑{ val := val✝, isLt := isLt✝  …
  rfl
  -- 🎉 no goals
#align fin.coe_bit0 Fin.val_bit0

@[deprecated]
theorem val_bit1 {n : ℕ} [NeZero n] (k : Fin n) :
    ((bit1 k : Fin n) : ℕ) = bit1 (k : ℕ) % n := by
  cases n;
  -- ⊢ ↑(bit1 k) = bit1 ↑k % zero
  · cases' k with k h
    -- ⊢ ↑(bit1 { val := k, isLt := h }) = bit1 ↑{ val := k, isLt := h } % zero
    cases k
    -- ⊢ ↑(bit1 { val := zero, isLt := h }) = bit1 ↑{ val := zero, isLt := h } % zero
    · show _ % _ = _
      -- ⊢ ((zero + zero) % zero + 1 % zero) % zero = bit1 ↑{ val := zero, isLt := h }  …
      simp
      -- 🎉 no goals
    cases' h with _ h
    -- 🎉 no goals
  simp [bit1, Fin.val_bit0, Fin.val_add, Fin.val_one]
  -- 🎉 no goals
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
  -- ⊢ ↑{ val := bit1 m, isLt := h } = ↑(bit1 { val := m, isLt := (_ : m < n) })
  simp only [bit1, bit0] at h
  -- ⊢ ↑{ val := bit1 m, isLt := h } = ↑(bit1 { val := m, isLt := (_ : m < n) })
  simp only [bit1, bit0, val_add, val_one', ← Nat.add_mod, Nat.mod_eq_of_lt h]
  -- 🎉 no goals
#align fin.mk_bit1 Fin.mk_bit1

end Bit

#align fin.val_two Fin.val_two

--- porting note: syntactically the same as the above
#align fin.coe_two Fin.val_two

section OfNatCoe

@[simp]
theorem ofNat_eq_val (n : ℕ) [NeZero n] (a : ℕ) : (Fin.ofNat'' a : Fin n) = a :=
  rfl
#align fin.of_nat_eq_coe Fin.ofNat_eq_val

-- porting note: is this the right name for things involving `Nat.cast`?
/-- Converting an in-range number to `Fin (n + 1)` produces a result
whose value is the original number.  -/
theorem val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) : (a : Fin n).val = a := by
  rw [← ofNat_eq_val]
  -- ⊢ ↑(ofNat'' a) = a
  exact Nat.mod_eq_of_lt h
  -- 🎉 no goals
#align fin.coe_val_of_lt Fin.val_cast_of_lt

/-- Converting the value of a `Fin (n + 1)` to `Fin (n + 1)` results
in the same value.  -/
theorem cast_val_eq_self {n : ℕ} [NeZero n] (a : Fin n) : (a.val : Fin n) = a := by
  rw [Fin.eq_iff_veq]
  -- ⊢ ↑↑↑a = ↑a
  exact val_cast_of_lt a.isLt
  -- 🎉 no goals
#align fin.coe_val_eq_self Fin.cast_val_eq_self

-- porting note: this is syntactically the same as `val_cast_of_lt`
#align fin.coe_coe_of_lt Fin.val_cast_of_lt

-- porting note: this is syntactically the same as `cast_val_of_lt`
#align fin.coe_coe_eq_self Fin.cast_val_eq_self

theorem cast_nat_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by
  rw [← Fin.ofNat_eq_val, Fin.ofNat'', Fin.last]
  -- ⊢ { val := n % (n + 1), isLt := (_ : n % (n + 1) < n + 1) } = { val := n, isLt …
  simp only [Nat.mod_eq_of_lt n.lt_succ_self]
  -- 🎉 no goals
#align fin.coe_nat_eq_last Fin.cast_nat_eq_last

theorem le_val_last (i : Fin (n + 1)) : i ≤ n := by
  rw [Fin.cast_nat_eq_last]
  -- ⊢ i ≤ last n
  exact Fin.le_last i
  -- 🎉 no goals
#align fin.le_coe_last Fin.le_val_last

end OfNatCoe

#align fin.add_one_pos Fin.add_one_pos
#align fin.one_pos Fin.one_pos
#align fin.zero_ne_one Fin.zero_ne_one

@[simp]
theorem zero_eq_one_iff [NeZero n] : (0 : Fin n) = 1 ↔ n = 1 := by
  constructor
  -- ⊢ 0 = 1 → n = 1
  · intro h
    -- ⊢ n = 1
    have := congr_arg ((↑) : Fin n → ℕ) h
    -- ⊢ n = 1
    simp only [val_zero', val_one', @eq_comm _ 0, ← Nat.dvd_iff_mod_eq_zero] at this
    -- ⊢ n = 1
    exact eq_one_of_dvd_one this
    -- 🎉 no goals
  · rintro rfl
    -- ⊢ 0 = 1
    rfl
    -- 🎉 no goals
#align fin.zero_eq_one_iff Fin.zero_eq_one_iff

@[simp]
theorem one_eq_zero_iff [NeZero n] : (1 : Fin n) = 0 ↔ n = 1 := by rw [eq_comm, zero_eq_one_iff]
                                                                   -- 🎉 no goals
#align fin.one_eq_zero_iff Fin.one_eq_zero_iff

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
  -- ⊢ succ 0 = 1
  · exact (NeZero.ne 0 rfl).elim
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align fin.succ_zero_eq_one Fin.succ_zero_eq_one'

#align fin.succ_zero_eq_one' Fin.succ_zero_eq_one

/--
The `Fin.succ_one_eq_two` in `Std` only applies in `Fin (n+2)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem succ_one_eq_two' [NeZero n] : Fin.succ (1 : Fin (n + 1)) = 2 := by
  cases n
  -- ⊢ succ 1 = 2
  · exact (NeZero.ne 0 rfl).elim
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
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
  ⟨fun h => Fin.eq_of_veq $ by rw [Nat.eq_zero_of_le_zero h]; rfl, by rintro rfl; exact le_refl _⟩
                               -- ⊢ 0 = ↑0
                                                              -- 🎉 no goals
                                                                      -- ⊢ 0 ≤ 0
                                                                                  -- 🎉 no goals
#align fin.le_zero_iff Fin.le_zero_iff'

#align fin.succ_succ_ne_one Fin.succ_succ_ne_one
#align fin.cast_lt Fin.castLT
#align fin.coe_cast_lt Fin.coe_castLT
#align fin.cast_lt_mk Fin.castLT_mk

-- Move to Std?
@[simp] theorem cast_refl {n : Nat} (h : n = n) :
    Fin.cast h = id := rfl

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

@[simp]
theorem range_castLE {n k : ℕ} (h : n ≤ k) : Set.range (castLE h) = { i : Fin k | (i : ℕ) < n } :=
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, Fin.ext rfl⟩⟩
#align fin.range_cast_le Fin.range_castLE

@[simp]
theorem coe_of_injective_castLEEmb_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLEEmb h).injective).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_castLE h]
  -- ⊢ ↑(castLE h (↑(Equiv.ofInjective ↑(castLEEmb h) (_ : Injective ↑(castLEEmb h) …
  exact congr_arg Fin.val (Equiv.apply_ofInjective_symm _ _)
  -- 🎉 no goals
#align fin.coe_of_injective_cast_le_symm Fin.coe_of_injective_castLEEmb_symm

#align fin.cast_le_succ Fin.castLE_succ
#align fin.cast_le_cast_le Fin.castLE_castLE
#align fin.cast_le_comp_cast_le Fin.castLE_comp_castLE

/-- `Fin.cast` as an `OrderIso`, `castIso eq i` embeds `i` into an equal `Fin` type,
see also `Equiv.finCongr`. -/
def castIso (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨castLE eq.le, castLE eq.symm.le, fun _ => eq_of_veq rfl, fun _ => eq_of_veq rfl⟩
  map_rel_iff' := Iff.rfl
#align fin.cast Fin.castIso

@[simp]
theorem symm_castIso (h : n = m) : (castIso h).symm = castIso h.symm := by simp
                                                                           -- 🎉 no goals
#align fin.symm_cast Fin.symm_castIso

theorem coe_castIso (h : n = m) (i : Fin n) : (castIso h i : ℕ) = i := by simp
                                                                          -- 🎉 no goals
#align fin.coe_cast Fin.coe_castIso

@[simp]
theorem castIso_zero {n' : ℕ} [NeZero n] {h : n = n'} : castIso h (0 : Fin n) =
    by { haveI : NeZero n' := by {rw [← h]; infer_instance}; exact 0} :=
       -- 🎉 no goals
  ext rfl
#align fin.cast_zero Fin.castIso_zero

@[simp]
theorem castIso_last {n' : ℕ} {h : n + 1 = n' + 1} : castIso h (last n) = last n' :=
  ext (by rw [coe_castIso, val_last, val_last, Nat.succ_injective h])
          -- 🎉 no goals
#align fin.cast_last Fin.castIso_last

@[simp]
theorem castIso_mk (h : n = m) (i : ℕ) (hn : i < n) :
    castIso h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h.le⟩ := by
  ext
  -- ⊢ ↑(↑(castIso h) { val := i, isLt := hn }) = ↑{ val := i, isLt := (_ : i < m) }
  simp
  -- 🎉 no goals
#align fin.cast_mk Fin.castIso_mk

@[simp]
theorem castIso_trans {k : ℕ} (h : n = m) (h' : m = k) {i : Fin n} :
    castIso h' (castIso h i) = castIso (Eq.trans h h') i := by
  ext
  -- ⊢ ↑(↑(castIso h') (↑(castIso h) i)) = ↑(↑(castIso (_ : n = k)) i)
  simp
  -- 🎉 no goals
#align fin.cast_trans Fin.castIso_trans

@[simp]
theorem castIso_refl (h : n = n := rfl) : castIso h = OrderIso.refl (Fin n) := by
  ext
  -- ⊢ ↑(↑(castIso h) x✝) = ↑(↑(OrderIso.refl (Fin n)) x✝)
  simp
  -- 🎉 no goals
#align fin.cast_refl Fin.castIso_refl

#align fin.cast_le_of_eq Fin.castLE_of_eq

/-- While in many cases `Fin.castIso` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem castIso_to_equiv (h : n = m) : (castIso h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h
  -- ⊢ (castIso (_ : n = n)).toEquiv = Equiv.cast (_ : Fin n = Fin n)
  simp
  -- 🎉 no goals
#align fin.cast_to_equiv Fin.castIso_to_equiv

/-- While in many cases `Fin.castIso` is better than `Equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem castIso_eq_cast (h : n = m) : (castIso h : Fin n → Fin m) = cast (h ▸ rfl) :=
  rfl
#align fin.cast_eq_cast Fin.castIso_eq_cast

theorem strictMono_castAdd (m) : StrictMono (castAdd m : Fin n → Fin (n + m)) :=
  strictMono_castLE (Nat.le_add_right n m)

/-- `Fin.castAdd` as an `OrderEmbedding`, `castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`.
See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
@[simps! apply toEmbedding]
def castAddEmb (m) : Fin n ↪o Fin (n + m) :=
  OrderEmbedding.ofStrictMono (castAdd m) (strictMono_castAdd m)
#align fin.cast_add Fin.castAddEmb

#align fin.coe_cast_add Fin.coe_castAdd
#align fin.cast_add_zero Fin.castAdd_zero
#align fin.cast_add_lt Fin.castAdd_lt
#align fin.cast_add_mk Fin.castAdd_mk
#align fin.cast_add_cast_lt Fin.castAdd_castLT
#align fin.cast_lt_cast_add Fin.castLT_castAdd

/-- For rewriting in the reverse direction, see `Fin.castIso_castAdd_left`. -/
theorem castAdd_castIso {n n' : ℕ} (m : ℕ) (i : Fin n') (h : n' = n) :
    castAdd m (Fin.castIso h i) = Fin.castIso (congr_arg (· + m) h) (castAdd m i) :=
  ext rfl
#align fin.cast_add_cast Fin.castAdd_castIso

theorem castIso_castAdd_left {n n' m : ℕ} (i : Fin n') (h : n' + m = n + m) :
    castIso h (castAdd m i) = castAdd m (castIso (add_right_cancel h) i) := by
  ext
  -- ⊢ ↑(↑(castIso h) (castAdd m i)) = ↑(castAdd m (↑(castIso (_ : n' = n)) i))
  simp
  -- 🎉 no goals
#align fin.cast_cast_add_left Fin.castIso_castAdd_left

@[simp]
theorem castIso_castAdd_right {n m m' : ℕ} (i : Fin n) (h : n + m' = n + m) :
    castIso h (castAdd m' i) = castAdd m i := by
  ext
  -- ⊢ ↑(↑(castIso h) (castAdd m' i)) = ↑(castAdd m i)
  simp
  -- 🎉 no goals
#align fin.cast_cast_add_right Fin.castIso_castAdd_right

#align fin.cast_add_cast_add Fin.castAdd_castAdd

/-- The cast of the successor is the successor of the cast.
See `Fin.succ_castIso_eq` for rewriting in the reverse direction. -/
@[simp]
theorem castIso_succ_eq {n' : ℕ} (i : Fin n) (h : n.succ = n'.succ) :
    castIso h i.succ = (castIso (Nat.succ.inj h) i).succ :=
  ext <| by simp
            -- 🎉 no goals
#align fin.cast_succ_eq Fin.castIso_succ_eq

theorem succ_castIso_eq {n' : ℕ} (i : Fin n) (h : n = n') :
    (castIso h i).succ = castIso (by rw [h]) i.succ :=
                                     -- 🎉 no goals
  ext <| by simp
            -- 🎉 no goals
#align fin.succ_cast_eq Fin.succ_castIso_eq

theorem strictMono_castSucc : StrictMono (castSucc : Fin n → Fin (n + 1)) :=
  strictMono_castAdd 1

/-- `Fin.castSucc` as an `OrderEmbedding`, `castSuccEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[simps! apply toEmbedding]
def castSuccEmb : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono castSucc strictMono_castSucc
#align fin.cast_succ Fin.castSuccEmb

#align fin.coe_cast_succ Fin.coe_castSucc
#align fin.cast_succ_mk Fin.castSucc_mk

@[simp]
theorem castIso_castSucc {n' : ℕ} {h : n + 1 = n' + 1} {i : Fin n} :
    castIso h (castSucc i) = castSucc (castIso (Nat.succ_injective h) i) := by
  ext
  -- ⊢ ↑(↑(castIso h) (castSucc i)) = ↑(castSucc (↑(castIso (_ : n = n')) i))
  simp only [coe_castIso, coe_castSucc]
  -- 🎉 no goals
#align fin.cast_cast_succ Fin.castIso_castSucc

#align fin.cast_succ_lt_succ Fin.castSucc_lt_succ
#align fin.le_cast_succ_iff Fin.le_castSucc_iff
#align fin.cast_succ_lt_iff_succ_le Fin.castSucc_lt_iff_succ_le
#align fin.succ_last Fin.succ_last
#align fin.succ_eq_last_succ Fin.succ_eq_last_succ
#align fin.cast_succ_cast_lt Fin.castSucc_castLT
#align fin.cast_lt_cast_succ Fin.castLT_castSucc
#align fin.cast_succ_lt_cast_succ_iff Fin.castSucc_lt_castSucc_iff

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
  -- 🎉 no goals
#align fin.cast_succ_pos Fin.castSucc_pos'

/--
The `Fin.castSucc_eq_zero_iff` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
@[simp]
theorem castSucc_eq_zero_iff' [NeZero n] (a : Fin n) : castSucc a = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| by simp).symm
                                                -- 🎉 no goals
#align fin.cast_succ_eq_zero_iff Fin.castSucc_eq_zero_iff'

/--
The `Fin.castSucc_ne_zero_iff` in `Std` only applies in `Fin (n+1)`.
This one instead uses a `NeZero n` typeclass hypothesis.
-/
theorem castSucc_ne_zero_iff' [NeZero n] (a : Fin n) : castSucc a ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| castSucc_eq_zero_iff' a
#align fin.cast_succ_ne_zero_iff Fin.castSucc_ne_zero_iff

#align fin.cast_succ_fin_succ Fin.castSucc_fin_succ

@[norm_cast, simp]
theorem coe_eq_castSucc {a : Fin n} : (a : Fin (n + 1)) = castSucc a := by
  ext
  -- ⊢ ↑↑↑a = ↑(castSucc a)
  exact val_cast_of_lt (Nat.lt.step a.is_lt)
  -- 🎉 no goals
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
  -- ⊢ ↑(castSucc (↑(Equiv.ofInjective castSucc (_ : Injective castSucc)).symm { va …
  exact congr_arg val (Equiv.apply_ofInjective_symm _ _)
  -- 🎉 no goals
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

@[simp]
theorem castIso_addNat_zero {n n' : ℕ} (i : Fin n) (h : n + 0 = n') :
    castIso h (addNat i 0) = castIso ((add_zero _).symm.trans h) i :=
  ext <| add_zero _
#align fin.cast_add_nat_zero Fin.castIso_addNat_zero

/-- For rewriting in the reverse direction, see `Fin.castIso_addNat_left`. -/
theorem addNat_castIso {n n' m : ℕ} (i : Fin n') (h : n' = n) :
    addNat (castIso h i) m = castIso (congr_arg (· + m) h) (addNat i m) :=
  ext rfl
#align fin.add_nat_cast Fin.addNat_castIso

theorem castIso_addNat_left {n n' m : ℕ} (i : Fin n') (h : n' + m = n + m) :
    castIso h (addNat i m) = addNat (castIso (add_right_cancel h) i) m := by
  ext
  -- ⊢ ↑(↑(castIso h) (addNat i m)) = ↑(addNat (↑(castIso (_ : n' = n)) i) m)
  simp
  -- 🎉 no goals
#align fin.cast_add_nat_left Fin.castIso_addNat_left

@[simp]
theorem castIso_addNat_right {n m m' : ℕ} (i : Fin n) (h : n + m' = n + m) :
    castIso h (addNat i m') = addNat i m :=
  ext <| (congr_arg ((· + ·) (i : ℕ)) (add_left_cancel h) : _)
#align fin.cast_add_nat_right Fin.castIso_addNat_right

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
#align fin.nat_add_zero Fin.natAdd_zero

/-- For rewriting in the reverse direction, see `Fin.castIso_natAdd_right`. -/
theorem natAdd_castIso {n n' : ℕ} (m : ℕ) (i : Fin n') (h : n' = n) :
    natAdd m (castIso h i) = castIso (congr_arg _ h) (natAdd m i) := by
  ext
  -- ⊢ ↑(natAdd m (↑(castIso h) i)) = ↑(↑(castIso (_ : m + n' = m + n)) (natAdd m i))
  simp
  -- 🎉 no goals
#align fin.nat_add_cast Fin.natAdd_castIso

theorem castIso_natAdd_right {n n' m : ℕ} (i : Fin n') (h : m + n' = m + n) :
    castIso h (natAdd m i) = natAdd m (castIso (add_left_cancel h) i) := by
  ext
  -- ⊢ ↑(↑(castIso h) (natAdd m i)) = ↑(natAdd m (↑(castIso (_ : n' = n)) i))
  simp
  -- 🎉 no goals
#align fin.cast_nat_add_right Fin.castIso_natAdd_right

@[simp]
theorem castIso_natAdd_left {n m m' : ℕ} (i : Fin n) (h : m' + n = m + n) :
    castIso h (natAdd m' i) = natAdd m i :=
  ext <| (congr_arg (· + (i : ℕ)) (add_right_cancel h) : _)
#align fin.cast_nat_add_left Fin.castIso_natAdd_left

#align fin.cast_add_nat_add Fin.castAdd_natAdd
#align fin.nat_add_cast_add Fin.natAdd_castAdd
#align fin.nat_add_nat_add Fin.natAdd_natAdd

@[simp]
theorem castIso_natAdd_zero {n n' : ℕ} (i : Fin n) (h : 0 + n = n') :
    castIso h (natAdd 0 i) = castIso ((zero_add _).symm.trans h) i :=
  ext <| zero_add _
#align fin.cast_nat_add_zero Fin.castIso_natAdd_zero

@[simp]
theorem castIso_natAdd (n : ℕ) {m : ℕ} (i : Fin m) :
    castIso (add_comm _ _) (natAdd n i) = addNat i n :=
  ext <| add_comm _ _
#align fin.cast_nat_add Fin.castIso_natAdd

@[simp]
theorem castIso_addNat {n : ℕ} (m : ℕ) (i : Fin n) :
    castIso (add_comm _ _) (addNat i m) = natAdd m i :=
  ext <| add_comm _ _
#align fin.cast_add_nat Fin.castIso_addNat

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

@[simp]
theorem natAdd_subNat_castIso {i : Fin (n + m)} (h : n ≤ i) :
    natAdd n (subNat n (castIso (add_comm _ _) i) h) = i := by simp [← castIso_addNat]
                                                               -- 🎉 no goals
#align fin.nat_add_sub_nat_cast Fin.natAdd_subNat_castIso

end Pred

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
  -- ⊢ ((fun x x_1 => x < x_1) ⇒ r) f f → ∀ (i : Fin n), r (f (castSucc i)) (f (suc …
  · intro H i
    -- ⊢ r (f (castSucc i)) (f (succ i))
    exact H i.castSucc_lt_succ
    -- 🎉 no goals
  · refine' fun H i => Fin.induction _ _
    -- ⊢ (fun x x_1 => x < x_1) i 0 → r (f i) (f 0)
    · exact fun h => (h.not_le (zero_le i)).elim
      -- 🎉 no goals
    · intro j ihj hij
      -- ⊢ r (f i) (f (succ j))
      rw [← le_castSucc_iff] at hij
      -- ⊢ r (f i) (f (succ j))
      rcases hij.eq_or_lt with (rfl | hlt)
      -- ⊢ r (f (castSucc j)) (f (succ j))
      exacts [H j, _root_.trans (ihj hlt) (H j)]
      -- 🎉 no goals
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
          -- ⊢ ↑{ val := a, isLt := ha } ≤ n
          exact le_of_lt ha
          -- 🎉 no goals
                                                                   -- 🎉 no goals
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
  -- ⊢ ↑({ val := val✝, isLt := isLt✝ } - b) = (↑{ val := val✝, isLt := isLt✝ } + ( …
           -- ⊢ ↑({ val := val✝¹, isLt := isLt✝¹ } - { val := val✝, isLt := isLt✝ }) = (↑{ v …
                    -- 🎉 no goals
#align fin.coe_sub Fin.coe_sub

@[simp]
theorem coe_fin_one (a : Fin 1) : (a : ℕ) = 0 := by simp [Subsingleton.elim a 0]
                                                    -- 🎉 no goals
#align fin.coe_fin_one Fin.coe_fin_one

@[simp]
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  -- ⊢ ↑(-1) = zero
  · simp
    -- 🎉 no goals
  rw [Fin.coe_neg, Fin.val_one, Nat.succ_sub_one, Nat.mod_eq_of_lt]
  -- ⊢ n✝ + 1 < Nat.succ n✝ + 1
  constructor
  -- 🎉 no goals
#align fin.coe_neg_one Fin.coe_neg_one

theorem coe_sub_one {n} (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  -- ⊢ ↑(a - 1) = if a = 0 then zero else ↑a - 1
  · simp
    -- 🎉 no goals
  split_ifs with h
  -- ⊢ ↑(a - 1) = Nat.succ n✝
  · simp [h]
    -- 🎉 no goals
  rw [sub_eq_add_neg, val_add_eq_ite, coe_neg_one, if_pos, add_comm, add_tsub_add_eq_tsub_left]
  -- ⊢ Nat.succ n✝ + 1 ≤ ↑a + (n✝ + 1)
  conv_rhs => rw [add_comm]
  -- ⊢ Nat.succ n✝ + 1 ≤ n✝ + 1 + ↑a
  rw [add_le_add_iff_left, Nat.one_le_iff_ne_zero]
  -- ⊢ ↑a ≠ 0
  rwa [Fin.ext_iff] at h
  -- 🎉 no goals
#align fin.coe_sub_one Fin.coe_sub_one

theorem coe_sub_iff_le {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = a - b ↔ b ≤ a := by
  cases n; · exact @finZeroElim (fun _ => _) a
  -- ⊢ ↑(a - b) = ↑a - ↑b ↔ b ≤ a
             -- 🎉 no goals
  rw [le_iff_val_le_val, Fin.coe_sub, ← add_tsub_assoc_of_le b.is_lt.le a]
  -- ⊢ (↑a + Nat.succ n✝ - ↑b) % Nat.succ n✝ = ↑a - ↑b ↔ ↑b ≤ ↑a
  cases' le_or_lt (b : ℕ) a with h h
  -- ⊢ (↑a + Nat.succ n✝ - ↑b) % Nat.succ n✝ = ↑a - ↑b ↔ ↑b ≤ ↑a
  · simp [← tsub_add_eq_add_tsub h, val_fin_le.mp h,
      Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt a.is_lt)]
  · rw [Nat.mod_eq_of_lt, tsub_eq_zero_of_le h.le, tsub_eq_zero_iff_le, ← not_iff_not]
    -- ⊢ ¬↑a + Nat.succ n✝ ≤ ↑b ↔ ¬↑b ≤ ↑a
    · simpa [b.is_lt.trans_le le_add_self] using h
      -- 🎉 no goals
    · rwa [tsub_lt_iff_left (b.is_lt.le.trans le_add_self), add_lt_add_iff_right]
      -- 🎉 no goals
#align fin.coe_sub_iff_le Fin.coe_sub_iff_le

theorem coe_sub_iff_lt {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = n + a - b ↔ a < b := by
  cases' n with n
  -- ⊢ ↑(a - b) = zero + ↑a - ↑b ↔ a < b
  · exact @finZeroElim (fun _ => _) a
    -- 🎉 no goals
  rw [lt_iff_val_lt_val, Fin.coe_sub, add_comm]
  -- ⊢ (Nat.succ n - ↑b + ↑a) % Nat.succ n = Nat.succ n + ↑a - ↑b ↔ ↑a < ↑b
  cases' le_or_lt (b : ℕ) a with h h
  -- ⊢ (Nat.succ n - ↑b + ↑a) % Nat.succ n = Nat.succ n + ↑a - ↑b ↔ ↑a < ↑b
  · refine iff_of_false ?_ (not_lt_of_le h)
    -- ⊢ ¬(Nat.succ n - ↑b + ↑a) % Nat.succ n = Nat.succ n + ↑a - ↑b
    simpa [add_tsub_assoc_of_le h] using
      ((Nat.mod_lt _ (Nat.succ_pos _)).trans_le le_self_add).ne
  · simp [← tsub_tsub_assoc b.is_lt.le h.le, ← tsub_add_eq_add_tsub b.is_lt.le,
      Nat.mod_eq_of_lt (tsub_lt_self (Nat.succ_pos _) (tsub_pos_of_lt h)), val_fin_le.mp _]
    exact h
    -- 🎉 no goals
#align fin.coe_sub_iff_lt Fin.coe_sub_iff_lt

@[simp]
theorem lt_sub_one_iff {n : ℕ} {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  rcases k with ⟨_ | k, hk⟩
  -- ⊢ { val := zero, isLt := hk } < { val := zero, isLt := hk } - 1 ↔ { val := zer …
  simp [lt_iff_val_lt_val]
  -- ⊢ { val := Nat.succ k, isLt := hk } < { val := Nat.succ k, isLt := hk } - 1 ↔  …
  have : (k + 1 + (n + 1)) % (n + 2) = k % (n + 2) := by
    rw [add_right_comm, add_assoc, add_mod_right]
  simp [lt_iff_val_lt_val, ext_iff, Fin.coe_sub, succ_eq_add_one, this,
    mod_eq_of_lt ((lt_succ_self _).trans hk)]
#align fin.lt_sub_one_iff Fin.lt_sub_one_iff

@[simp]
theorem le_sub_one_iff {n : ℕ} {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  -- ⊢ k ≤ k - 1 ↔ k = 0
  · simp [fin_one_eq_zero k]
    -- 🎉 no goals
  rw [← lt_sub_one_iff, le_iff_lt_or_eq, lt_sub_one_iff, or_iff_left_iff_imp, eq_comm,
    sub_eq_iff_eq_add]
  simp
  -- 🎉 no goals
#align fin.le_sub_one_iff Fin.le_sub_one_iff

@[simp]
theorem sub_one_lt_iff {n : ℕ} {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
  not_iff_not.1 <| by simp only [not_lt, le_sub_one_iff, le_zero_iff]
                      -- 🎉 no goals
#align fin.sub_one_lt_iff Fin.sub_one_lt_iff

theorem last_sub (i : Fin (n + 1)) : last n - i = Fin.revPerm i :=
  ext <| by rw [coe_sub_iff_le.2 i.le_last, val_last, val_revPerm, Nat.succ_sub_succ_eq_sub]
            -- 🎉 no goals
#align fin.last_sub Fin.last_sub

end AddGroup

section SuccAbove

/-- `succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`. -/
def succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if i.1 < p.1 then castSucc i else succ i

theorem strictMono_succAbove (p : Fin (n + 1)) : StrictMono (succAbove p) :=
  (castSuccEmb : Fin n ↪o _).strictMono.ite (succEmbedding n).strictMono
    (fun _ _ hij hj => lt_trans ((castSuccEmb : Fin n ↪o _).lt_iff_lt.2 hij) hj) fun i =>
    (castSucc_lt_succ i).le
#align fin.succ_above_aux Fin.strictMono_succAbove

/--  `Fin.auccAbove` as an `OrderEmbedding`, `succAboveEmb p i` embeds `Fin n` into `Fin (n + 1)`
with a hole around `p`. -/
@[simps! apply toEmbedding]
def succAboveEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)
#align fin.succ_above Fin.succAboveEmb

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `castSucc` when the resulting `i.castSucc < p`. -/
theorem succAbove_below (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p) :
    p.succAbove i = castSucc i := if_pos h
#align fin.succ_above_below Fin.succAbove_below

@[simp]
theorem succAbove_ne_zero_zero [NeZero n] {a : Fin (n + 1)} (ha : a ≠ 0) : a.succAbove 0 = 0 := by
  rw [Fin.succAbove_below]
  -- ⊢ castSucc 0 = 0
  · simp
    -- 🎉 no goals
  · exact bot_lt_iff_ne_bot.mpr ha
    -- 🎉 no goals
#align fin.succ_above_ne_zero_zero Fin.succAbove_ne_zero_zero

theorem succAbove_eq_zero_iff [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) :
    a.succAbove b = 0 ↔ b = 0 := by
  simp only [← succAbove_ne_zero_zero ha, ← succAboveEmb_apply, OrderEmbedding.eq_iff_eq, iff_self]
  -- 🎉 no goals
#align fin.succ_above_eq_zero_iff Fin.succAbove_eq_zero_iff

theorem succAbove_ne_zero [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.succAbove b ≠ 0 :=
  mt (succAbove_eq_zero_iff ha).mp hb
#align fin.succ_above_ne_zero Fin.succAbove_ne_zero

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp]
theorem succAbove_zero : succAbove (0 : Fin (n + 1)) = Fin.succ :=
  rfl
#align fin.succ_above_zero Fin.succAbove_zero

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around `last n` embeds by `castSucc`. -/
@[simp]
theorem succAbove_last : succAbove (Fin.last n) = castSucc := by
  ext
  -- ⊢ ↑(succAbove (last n) x✝) = ↑(castSucc x✝)
  simp only [succAbove_below, castSucc_lt_last]
  -- 🎉 no goals
#align fin.succ_above_last Fin.succAbove_last

theorem succAbove_last_apply (i : Fin n) : succAbove (Fin.last n) i = castSucc i := by
  rw [succAbove_last]
  -- 🎉 no goals
#align fin.succ_above_last_apply Fin.succAbove_last_apply

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
theorem succAbove_above (p : Fin (n + 1)) (i : Fin n) (h : p ≤ castSucc i) :
    p.succAbove i = i.succ := by simp [le_iff_val_le_val] at h; simp [succAbove, h.not_lt]
                                 -- ⊢ succAbove p i = succ i
                                                                -- 🎉 no goals
#align fin.succ_above_above Fin.succAbove_above

/-- Embedding `i : Fin n` into `Fin (n + 1)` is always about some hole `p`. -/
theorem succAbove_lt_ge (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p ≤ castSucc i :=
  lt_or_ge (castSucc i) p
#align fin.succ_above_lt_ge Fin.succAbove_lt_ge

/-- Embedding `i : Fin n` into `Fin (n + 1)` is always about some hole `p`. -/
theorem succAbove_lt_gt (p : Fin (n + 1)) (i : Fin n) : castSucc i < p ∨ p < i.succ :=
  Or.casesOn (succAbove_lt_ge p i) (fun h => Or.inl h) fun h =>
    Or.inr (lt_of_le_of_lt h (castSucc_lt_succ i))
#align fin.succ_above_lt_gt Fin.succAbove_lt_gt

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp]
theorem succAbove_lt_iff (p : Fin (n + 1)) (i : Fin n) : p.succAbove i < p ↔ castSucc i < p := by
  refine' Iff.intro _ _
  -- ⊢ succAbove p i < p → castSucc i < p
  · intro h
    -- ⊢ castSucc i < p
    cases' succAbove_lt_ge p i with H H
    -- ⊢ castSucc i < p
    · exact H
      -- 🎉 no goals
    · rw [succAbove_above _ _ H] at h
      -- ⊢ castSucc i < p
      exact lt_trans (castSucc_lt_succ i) h
      -- 🎉 no goals
  · intro h
    -- ⊢ succAbove p i < p
    rw [succAbove_below _ _ h]
    -- ⊢ castSucc i < p
    exact h
    -- 🎉 no goals
#align fin.succ_above_lt_iff Fin.succAbove_lt_iff

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
theorem lt_succAbove_iff (p : Fin (n + 1)) (i : Fin n) : p < p.succAbove i ↔ p ≤ castSucc i := by
  refine' Iff.intro _ _
  -- ⊢ p < succAbove p i → p ≤ castSucc i
  · intro h
    -- ⊢ p ≤ castSucc i
    cases' succAbove_lt_ge p i with H H
    -- ⊢ p ≤ castSucc i
    · rw [succAbove_below _ _ H] at h
      -- ⊢ p ≤ castSucc i
      exact le_of_lt h
      -- 🎉 no goals
    · exact H
      -- 🎉 no goals
  · intro h
    -- ⊢ p < succAbove p i
    rw [succAbove_above _ _ h]
    -- ⊢ p < succ i
    exact lt_of_le_of_lt h (castSucc_lt_succ i)
    -- 🎉 no goals
#align fin.lt_succ_above_iff Fin.lt_succAbove_iff

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself -/
theorem succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  intro eq
  -- ⊢ False
  by_cases H : castSucc i < p
  -- ⊢ False
  · simp [lt_irrefl, ← succAbove_below _ _ H, eq] at H
    -- 🎉 no goals
  · simpa [← succAbove_above _ _ (le_of_not_lt H), eq, H] using castSucc_lt_succ i
    -- 🎉 no goals
#align fin.succ_above_ne Fin.succAbove_ne

/-- Embedding a positive `Fin n` results in a positive `Fin (n + 1)` -/
theorem succAbove_pos [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i) : 0 < p.succAbove i := by
  by_cases H : castSucc i < p
  -- ⊢ 0 < succAbove p i
  · simpa [succAbove_below _ _ H] using castSucc_pos' h
    -- 🎉 no goals
  · simp [succAbove_above _ _ (le_of_not_lt H)]
    -- 🎉 no goals
#align fin.succ_above_pos Fin.succAbove_pos

@[simp]
theorem succAbove_castLT {x y : Fin (n + 1)} (h : x < y)
    (hx : x.1 < n := lt_of_lt_of_le h y.le_last) : y.succAbove (x.castLT hx) = x := by
  rw [succAbove_below, castSucc_castLT]
  -- ⊢ castSucc (castLT x hx) < y
  exact h
  -- 🎉 no goals
#align fin.succ_above_cast_lt Fin.succAbove_castLT

@[simp]
theorem succAbove_pred {x y : Fin (n + 1)} (h : x < y)
    (hy : y ≠ 0 := (x.zero_le.trans_lt h).ne') : x.succAbove (y.pred hy) = y := by
  rw [succAbove_above, succ_pred]
  -- ⊢ x ≤ castSucc (pred y hy)
  simpa [le_iff_val_le_val] using Nat.le_pred_of_lt h
  -- 🎉 no goals
#align fin.succ_above_pred Fin.succAbove_pred

theorem castLT_succAbove {x : Fin n} {y : Fin (n + 1)} (h : castSucc x < y)
    (h' : (y.succAbove x).1 < n := lt_of_lt_of_le ((succAbove_lt_iff _ _).2 h) (le_last y)) :
    (y.succAbove x).castLT h' = x := by simp only [succAbove_below _ _ h, castLT_castSucc]
                                        -- 🎉 no goals
#align fin.cast_lt_succ_above Fin.castLT_succAbove

theorem pred_succAbove {x : Fin n} {y : Fin (n + 1)} (h : y ≤ castSucc x)
    (h' : (y.succAbove x) ≠ 0 := (y.zero_le.trans_lt <| (lt_succAbove_iff _ _).2 h).ne') :
    (y.succAbove x).pred h' = x := by simp only [succAbove_above _ _ h, pred_succ]
                                      -- 🎉 no goals
#align fin.pred_succ_above Fin.pred_succAbove

theorem exists_succAbove_eq {x y : Fin (n + 1)} (h : x ≠ y) : ∃ z, y.succAbove z = x := by
  cases' h.lt_or_lt with hlt hlt
  -- ⊢ ∃ z, succAbove y z = x
  exacts [⟨_, succAbove_castLT hlt⟩, ⟨_, succAbove_pred hlt⟩]
  -- 🎉 no goals
#align fin.exists_succ_above_eq Fin.exists_succAbove_eq

@[simp]
theorem exists_succAbove_eq_iff {x y : Fin (n + 1)} : (∃ z, x.succAbove z = y) ↔ y ≠ x := by
  refine' ⟨_, exists_succAbove_eq⟩
  -- ⊢ (∃ z, succAbove x z = y) → y ≠ x
  rintro ⟨y, rfl⟩
  -- ⊢ succAbove x y ≠ x
  exact succAbove_ne _ _
  -- 🎉 no goals
#align fin.exists_succ_above_eq_iff Fin.exists_succAbove_eq_iff

/-- The range of `p.succAbove` is everything except `p`. -/
@[simp]
theorem range_succAbove (p : Fin (n + 1)) : Set.range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff
#align fin.range_succ_above Fin.range_succAbove

@[simp]
theorem range_succ (n : ℕ) : Set.range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ := by
  rw [← succAbove_zero]
  -- ⊢ Set.range (succAbove 0) = {0}ᶜ
  exact range_succAbove (0 : Fin (n + 1))
  -- 🎉 no goals
#align fin.range_succ Fin.range_succ

@[simp]
theorem exists_succ_eq_iff {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 := by
  convert @exists_succAbove_eq_iff n 0 x
  -- 🎉 no goals
#align fin.exists_succ_eq_iff Fin.exists_succ_eq_iff

/-- Given a fixed pivot `x : Fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_right_injective {x : Fin (n + 1)} : Injective (succAbove x) :=
  (succAboveEmb x).injective
#align fin.succ_above_right_injective Fin.succAbove_right_injective

/-- Given a fixed pivot `x : Fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_right_inj {x : Fin (n + 1)} : x.succAbove a = x.succAbove b ↔ a = b :=
  succAbove_right_injective.eq_iff
#align fin.succ_above_right_inj Fin.succAbove_right_inj

/-- `succAbove` is injective at the pivot -/
theorem succAbove_left_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n → Fin (n + 1) => (Set.range f)ᶜ) h
  -- 🎉 no goals
#align fin.succ_above_left_injective Fin.succAbove_left_injective

/-- `succAbove` is injective at the pivot -/
@[simp]
theorem succAbove_left_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succAbove_left_injective.eq_iff
#align fin.succ_above_left_inj Fin.succAbove_left_inj

@[simp]
theorem zero_succAbove {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)).succAbove i = i.succ := by
  rfl
  -- 🎉 no goals
#align fin.zero_succ_above Fin.zero_succAbove

@[simp]
theorem succ_succAbove_zero {n : ℕ} [NeZero n] (i : Fin n) : succAbove i.succ 0 = 0 :=
  succAbove_below i.succ 0 (by simp only [castSucc_zero', succ_pos])
                               -- 🎉 no goals
#align fin.succ_succ_above_zero Fin.succ_succAbove_zero

@[simp]
theorem succ_succAbove_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.succ.succAbove j.succ = (i.succAbove j).succ :=
  (lt_or_ge (castSucc j) i).elim
    (fun h => by
      have h' : castSucc j.succ < i.succ := by simpa [lt_iff_val_lt_val] using h
      -- ⊢ succAbove (succ i) (succ j) = succ (succAbove i j)
      ext
      -- ⊢ ↑(succAbove (succ i) (succ j)) = ↑(succ (succAbove i j))
      simp [succAbove_below _ _ h, succAbove_below _ _ h'])
      -- 🎉 no goals
    fun h => by
    have h' : i.succ ≤ castSucc j.succ := by simpa [le_iff_val_le_val] using h
    -- ⊢ succAbove (succ i) (succ j) = succ (succAbove i j)
    ext
    -- ⊢ ↑(succAbove (succ i) (succ j)) = ↑(succ (succAbove i j))
    simp [succAbove_above _ _ h, succAbove_above _ _ h']
    -- 🎉 no goals
#align fin.succ_succ_above_succ Fin.succ_succAbove_succ

--@[simp] -- porting note: can be proved by `simp`
theorem one_succAbove_zero {n : ℕ} : (1 : Fin (n + 2)).succAbove 0 = 0 := by
  rfl
  -- 🎉 no goals
#align fin.one_succ_above_zero Fin.one_succAbove_zero

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succAbove_zero` or `succ_succAbove_zero`. -/
@[simp]
theorem succ_succAbove_one {n : ℕ} [NeZero n] (i : Fin (n + 1)) :
    i.succ.succAbove 1 = (i.succAbove 0).succ := by
  rw [← succ_zero_eq_one']
  -- ⊢ succAbove (succ i) (succ 0) = succ (succAbove i 0)
  convert succ_succAbove_succ i 0
  -- 🎉 no goals
#align fin.succ_succ_above_one Fin.succ_succAbove_one

@[simp]
theorem one_succAbove_succ {n : ℕ} (j : Fin n) :
    (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ := by
  have := succ_succAbove_succ 0 j
  -- ⊢ succAbove 1 (succ j) = succ (succ j)
  rwa [succ_zero_eq_one, zero_succAbove] at this
  -- 🎉 no goals
#align fin.one_succ_above_succ Fin.one_succAbove_succ

@[simp]
theorem one_succAbove_one {n : ℕ} : (1 : Fin (n + 3)).succAbove 1 = 2 := by
  have := succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 2))
  -- ⊢ succAbove 1 1 = 2
  simp only [succ_zero_eq_one, val_zero, Nat.cast_zero, zero_succAbove, succ_one_eq_two] at this
  -- ⊢ succAbove 1 1 = 2
  exact this
  -- 🎉 no goals
#align fin.one_succ_above_one Fin.one_succAbove_one

end SuccAbove

section PredAbove

/-- `predAbove p i` embeds `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i then i.pred ((ne_iff_vne i 0).mpr (Nat.not_eq_zero_of_lt h))
  else i.castLT (Nat.lt_of_le_of_lt (Nat.ge_of_not_lt h) p.2)
#align fin.pred_above Fin.predAbove

theorem predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  -- ⊢ (if h : castSucc p < a then pred a (_ : a ≠ 0) else castLT a (_ : ↑a < n)) ≤ …
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, coe_pred]
  · exact pred_le_pred H
    -- 🎉 no goals
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · simp at ha
    -- ⊢ ↑(castLT a (_ : ↑a < n)) ≤ ↑b - 1
    exact le_pred_of_lt (lt_of_le_of_lt ha hb)
    -- 🎉 no goals
  · exact H
    -- 🎉 no goals
#align fin.pred_above_right_monotone Fin.predAbove_right_monotone

theorem predAbove_left_monotone (i : Fin (n + 1)) :
    Monotone fun p => predAbove p i := fun a b H => by
  dsimp [predAbove]
  -- ⊢ (if h : castSucc a < i then pred i (_ : i ≠ 0) else castLT i (_ : ↑i < n)) ≤ …
  split_ifs with ha hb hb
  · rfl
    -- 🎉 no goals
  · exact pred_le _
    -- 🎉 no goals
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    -- ⊢ castLT i (_ : ↑i < n) ≤ pred i (_ : i ≠ 0)
    exact absurd H this.not_le
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align fin.pred_above_left_monotone Fin.predAbove_left_monotone

/-- `castPred` embeds `i : Fin (n + 2)` into `Fin (n + 1)`
by lowering just `last (n + 1)` to `last n`. -/
def castPred (i : Fin (n + 2)) : Fin (n + 1) := predAbove (last n) i
#align fin.cast_pred Fin.castPred

@[simp]
theorem castPred_zero : castPred (0 : Fin (n + 2)) = 0 :=
  rfl
#align fin.cast_pred_zero Fin.castPred_zero

@[simp]
theorem castPred_one : castPred (1 : Fin (n + 2)) = 1 := by
  cases n
  -- ⊢ castPred 1 = 1
  · rfl
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
#align fin.cast_pred_one Fin.castPred_one

@[simp]
theorem predAbove_zero {i : Fin (n + 2)} (hi : i ≠ 0) : predAbove 0 i = i.pred hi := by
  dsimp [predAbove]
  -- ⊢ (if h : 0 < i then pred i (_ : i ≠ 0) else castLT i (_ : ↑i < n + 1)) = pred …
  rw [dif_pos]
  -- ⊢ 0 < i
  exact pos_iff_ne_zero.mpr hi
  -- 🎉 no goals
#align fin.pred_above_zero Fin.predAbove_zero

@[simp]
theorem castPred_last : castPred (last (n + 1)) = last n :=
  eq_of_veq (by simp [castPred, predAbove, castSucc_lt_last])
                -- 🎉 no goals
#align fin.cast_pred_last Fin.castPred_last

--Porting note: removing @[simp]. `castPred_mk'` has `simp` attribute instead
theorem castPred_mk (n i : ℕ) (h : i < n + 1) : castPred ⟨i, lt_succ_of_lt h⟩ = ⟨i, h⟩ := by
  have : ¬castSucc (last n) < ⟨i, lt_succ_of_lt h⟩ := by
    simpa [lt_iff_val_lt_val] using le_of_lt_succ h
  simp [castPred, predAbove, this]
  -- 🎉 no goals
#align fin.cast_pred_mk Fin.castPred_mk

--Porting note: new lemma
@[simp]
theorem castPred_mk' (n i : ℕ) (h₁ : i < n + 2) (h₂ : i < n + 1) : castPred ⟨i, h₁⟩ = ⟨i, h₂⟩ :=
  castPred_mk _ _ _

theorem coe_castPred {n : ℕ} (a : Fin (n + 2)) (hx : a < Fin.last _) :
  (a.castPred : ℕ) = a := by
  rcases a with ⟨a, ha⟩
  -- ⊢ ↑(castPred { val := a, isLt := ha }) = ↑{ val := a, isLt := ha }
  rw [castPred_mk]
  -- ⊢ a < n + 1
  exact hx
  -- 🎉 no goals
#align fin.coe_cast_pred Fin.coe_castPred

theorem predAbove_below (p : Fin (n + 1)) (i : Fin (n + 2)) (h : i ≤ castSucc p) :
    p.predAbove i = i.castPred := by
  have : i ≤ castSucc (last n) := h.trans p.le_last
  -- ⊢ predAbove p i = castPred i
  simp [predAbove, castPred, h.not_lt, this.not_lt]
  -- 🎉 no goals
#align fin.pred_above_below Fin.predAbove_below

@[simp]
theorem predAbove_last : predAbove (Fin.last n) = castPred :=
  rfl
#align fin.pred_above_last Fin.predAbove_last

theorem predAbove_last_apply (i : Fin n) : predAbove (Fin.last n) i = i.castPred := by
  rw [predAbove_last]
  -- 🎉 no goals
#align fin.pred_above_last_apply Fin.predAbove_last_apply

theorem predAbove_above (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i) :
    p.predAbove i = i.pred ((zero_le <| castSucc p).trans_lt h).ne.symm := by
  simp [predAbove, h]
  -- 🎉 no goals
#align fin.pred_above_above Fin.predAbove_above

theorem castPred_monotone : Monotone (@castPred n) :=
  predAbove_right_monotone (last _)
#align fin.cast_pred_monotone Fin.castPred_monotone

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
theorem succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  dsimp [predAbove, succAbove]
  -- ⊢ (if ↑(if h : castSucc p < i then pred i (_ : i ≠ 0) else castLT i (_ : ↑i <  …
  rcases p with ⟨p, _⟩
  -- ⊢ (if ↑(if h : castSucc { val := p, isLt := isLt✝ } < i then pred i (_ : i ≠ 0 …
  rcases i with ⟨i, _⟩
  -- ⊢ (if ↑(if h : castSucc { val := p, isLt := isLt✝¹ } < { val := i, isLt := isL …
  cases' lt_or_le i p with H H
  -- ⊢ (if ↑(if h : castSucc { val := p, isLt := isLt✝¹ } < { val := i, isLt := isL …
  · rw [dif_neg]
    -- ⊢ (if ↑(castLT { val := i, isLt := isLt✝ } (_ : ↑{ val := i, isLt := isLt✝ } < …
    rw [if_pos]
    rfl
    exact H
    -- ⊢ ¬castSucc { val := p, isLt := isLt✝¹ } < { val := i, isLt := isLt✝ }
    simp
    -- ⊢ i ≤ p
    apply le_of_lt H
    -- 🎉 no goals
  · rw [dif_pos]
    -- ⊢ (if ↑(pred { val := i, isLt := isLt✝ } (_ : { val := i, isLt := isLt✝ } ≠ 0) …
    rw [if_neg]
    · simp
      -- 🎉 no goals
    · simp only [pred, Fin.mk_lt_mk, not_lt]
      -- ⊢ p ≤ ↑(subNat 1 { val := i, isLt := isLt✝ } (_ : 0 < ↑{ val := i, isLt := isL …
      exact Nat.le_pred_of_lt (h.symm.lt_of_le H)
      -- 🎉 no goals
    · exact lt_of_le_of_ne H h.symm
      -- 🎉 no goals
#align fin.succ_above_pred_above Fin.succAbove_predAbove

/-- Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
theorem predAbove_succAbove (p : Fin n) (i : Fin n) :
    p.predAbove ((castSucc p).succAbove i) = i := by
  dsimp [predAbove, succAbove]
  -- ⊢ (if h : castSucc p < if ↑i < ↑p then castSucc i else succ i then pred (if ↑i …
  rcases p with ⟨p, _⟩
  -- ⊢ (if h : castSucc { val := p, isLt := isLt✝ } < if ↑i < ↑{ val := p, isLt :=  …
  rcases i with ⟨i, _⟩
  -- ⊢ (if h : castSucc { val := p, isLt := isLt✝¹ } < if ↑{ val := i, isLt := isLt …
  dsimp
  -- ⊢ (if h : { val := p, isLt := (_ : p < Nat.succ n) } < if i < p then { val :=  …
  split_ifs with h₁ h₂ h₃
  · simp only [← val_fin_lt, not_lt] at h₁ h₂
    -- ⊢ pred { val := i, isLt := (_ : i < Nat.succ n) } (_ : { val := i, isLt := (_  …
    exact (lt_le_antisymm h₁ (le_of_lt h₂)).elim
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
  · simp only [← val_fin_lt, not_lt] at h₁ h₃
    -- ⊢ castLT { val := i + 1, isLt := (_ : Nat.succ i < Nat.succ n) } (_ : ↑{ val : …
    contradiction
    -- 🎉 no goals
#align fin.pred_above_succ_above Fin.predAbove_succAbove

theorem castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a ≠ 0)
    (ha' := a.castSucc_ne_zero_iff.mpr ha) :
    castSucc (a.pred ha) = (castSucc a).pred ha' := by
  cases a
  -- ⊢ castSucc (pred { val := val✝, isLt := isLt✝ } ha) = pred (castSucc { val :=  …
  rfl
  -- 🎉 no goals
#align fin.cast_succ_pred_eq_pred_cast_succ Fin.castSucc_pred_eq_pred_castSucc

/-- `pred` commutes with `succAbove`. -/
theorem pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succAbove_ne_zero ha hb) :
    (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  obtain hbelow | habove := lt_or_le (castSucc b) a
  -- ⊢ succAbove (pred a ha) (pred b hb) = pred (succAbove a b) hk
  -- `rwa` uses them
  · rw [Fin.succAbove_below]
    -- ⊢ castSucc (pred b hb) = pred (succAbove a b) hk
    · rwa [castSucc_pred_eq_pred_castSucc, Fin.pred_inj, Fin.succAbove_below]
      -- 🎉 no goals
    · rwa [castSucc_pred_eq_pred_castSucc, pred_lt_pred_iff]
      -- 🎉 no goals
  · rw [Fin.succAbove_above]
    -- ⊢ succ (pred b hb) = pred (succAbove a b) hk
    have : (b.pred hb).succ = b.succ.pred (succ_ne_zero _) := by rw [succ_pred, pred_succ]
    -- ⊢ succ (pred b hb) = pred (succAbove a b) hk
    · rwa [this, Fin.pred_inj, Fin.succAbove_above]
      -- 🎉 no goals
    · rwa [castSucc_pred_eq_pred_castSucc, Fin.pred_le_pred_iff]
      -- 🎉 no goals
#align fin.pred_succ_above_pred Fin.pred_succAbove_pred

/-- `succ` commutes with `predAbove`. -/
@[simp]
theorem succ_predAbove_succ {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h₁ | h₂ := lt_or_le (castSucc a) b
  -- ⊢ predAbove (succ a) (succ b) = succ (predAbove a b)
  · rw [Fin.predAbove_above _ _ h₁, Fin.succ_pred, Fin.predAbove_above, Fin.pred_succ]
    -- ⊢ castSucc (succ a) < succ b
    simpa only [lt_iff_val_lt_val, coe_castSucc, val_succ, add_lt_add_iff_right] using
      h₁
  · cases' n with n
    -- ⊢ predAbove (succ a) (succ b) = succ (predAbove a b)
    · exfalso
      -- ⊢ False
      exact not_lt_zero' a.is_lt
      -- 🎉 no goals
    · rw [Fin.predAbove_below a b h₂,
        Fin.predAbove_below a.succ b.succ
          (by
            simpa only [le_iff_val_le_val, val_succ, coe_castSucc, add_le_add_iff_right]
              using h₂)]
      ext
      -- ⊢ ↑(castPred (succ b)) = ↑(succ (castPred b))
      have h₀ : (b : ℕ) < n + 1 := by
        simp only [le_iff_val_le_val, coe_castSucc] at h₂
        simpa only [lt_succ_iff] using h₂.trans a.is_le
      have h₁ : (b.succ : ℕ) < n + 2 := by
        rw [← Nat.succ_lt_succ_iff] at h₀
        simpa only [val_succ] using h₀
      simp only [coe_castPred b h₀, coe_castPred b.succ h₁, val_succ]
      -- 🎉 no goals
#align fin.succ_pred_above_succ Fin.succ_predAbove_succ

@[simp]
theorem castPred_castSucc (i : Fin (n + 1)) : castPred (castSucc i) = i := by
  simp [castPred, predAbove, not_lt.mpr (le_last i)]
  -- 🎉 no goals
#align fin.cast_pred_cast_succ Fin.castPred_castSucc

theorem castSucc_castPred {i : Fin (n + 2)} (h : i < last (n + 1)) :
    castSucc i.castPred = i := by
  rw [castPred, predAbove, dif_neg]
  -- ⊢ castSucc (castLT i (_ : ↑i < n + 1)) = i
  · simp [Fin.eq_iff_veq]
    -- 🎉 no goals
  · exact h.not_le
    -- 🎉 no goals
#align fin.cast_succ_cast_pred Fin.castSucc_castPred

theorem coe_castPred_le_self (i : Fin (n + 2)) : (i.castPred : ℕ) ≤ i := by
  rcases i.le_last.eq_or_lt with (rfl | h)
  -- ⊢ ↑(castPred (last (n + 1))) ≤ ↑(last (n + 1))
  · simp
    -- 🎉 no goals
  · rw [castPred, predAbove, dif_neg]
    -- ⊢ ↑(castLT i (_ : ↑i < n + 1)) ≤ ↑i
    · simp
      -- 🎉 no goals
    · simpa [lt_iff_val_lt_val, le_iff_val_le_val, lt_succ_iff] using h
      -- 🎉 no goals
#align fin.coe_cast_pred_le_self Fin.coe_castPred_le_self

theorem coe_castPred_lt_iff {i : Fin (n + 2)} : (i.castPred : ℕ) < i ↔ i = Fin.last _ := by
  rcases i.le_last.eq_or_lt with (rfl | H)
  -- ⊢ ↑(castPred (last (n + 1))) < ↑(last (n + 1)) ↔ last (n + 1) = last (n + 1)
  · simp
    -- 🎉 no goals
  · simp only [_root_.ne_of_lt H]
    -- ⊢ ↑(castPred i) < ↑i ↔ False
    rw [← castSucc_castPred H]
    -- ⊢ ↑(castPred (castSucc (castPred i))) < ↑(castSucc (castPred i)) ↔ False
    simp
    -- 🎉 no goals
#align fin.coe_cast_pred_lt_iff Fin.coe_castPred_lt_iff

theorem lt_last_iff_coe_castPred {i : Fin (n + 2)} :
    i < Fin.last _ ↔ (i.castPred : ℕ) = i := by
  rcases i.le_last.eq_or_lt with (rfl | H)
  -- ⊢ last (n + 1) < last (n + 1) ↔ ↑(castPred (last (n + 1))) = ↑(last (n + 1))
  · simp
    -- 🎉 no goals
  · simp only [H]
    -- ⊢ True ↔ ↑(castPred i) = ↑i
    rw [← castSucc_castPred H]
    -- ⊢ True ↔ ↑(castPred (castSucc (castPred i))) = ↑(castSucc (castPred i))
    simp
    -- 🎉 no goals
#align fin.lt_last_iff_coe_cast_pred Fin.lt_last_iff_coe_castPred

end PredAbove

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
  -- ⊢ k * 1 = k
  · simp
    -- 🎉 no goals
  cases n
  -- ⊢ k * 1 = k
  · simp [fin_one_eq_zero]
    -- 🎉 no goals
  simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)]
  -- 🎉 no goals
#align fin.mul_one Fin.mul_one'

#align fin.mul_comm Fin.mul_comm

protected theorem one_mul' [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by
  rw [Fin.mul_comm, Fin.mul_one']
  -- 🎉 no goals
#align fin.one_mul Fin.one_mul'

protected theorem mul_zero' [NeZero n] (k : Fin n) : k * 0 = 0 := by simp [eq_iff_veq, mul_def]
                                                                     -- 🎉 no goals
#align fin.mul_zero Fin.mul_zero'

protected theorem zero_mul' [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by
  simp [eq_iff_veq, mul_def]
  -- 🎉 no goals
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
                                                            -- 🎉 no goals
      q(OfNat.ofNat $i)
#align fin.reflect Fin.toExprₓ

end Fin
