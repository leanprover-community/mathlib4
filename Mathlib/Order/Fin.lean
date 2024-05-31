/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Hom.Set

#align_import data.fin.basic from "leanprover-community/mathlib"@"3a2b5524a138b5d0b818b858b516d4ac8a484b03"

/-!
# `Fin n` forms a bounded linear order

This file contains the linear ordered instance on `Fin n`.

`Fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

* `Fin.orderIsoSubtype` : coercion to `{i // i < n}` as an `OrderIso`;
* `Fin.valEmbedding` : coercion to natural numbers as an `Embedding`;
* `Fin.valOrderEmb` : coercion to natural numbers as an `OrderEmbedding`;
* `Fin.succOrderEmb` : `Fin.succ` as an `OrderEmbedding`;
* `Fin.castLEOrderEmb h` : `Fin.castLE` as an `OrderEmbedding`, embed `Fin n` into `Fin m` when
  `h : n ≤ m`;
* `Fin.castOrderIso` : `Fin.cast` as an `OrderIso`, order isomorphism between `Fin n` and `Fin m`
  provided that `n = m`, see also `Equiv.finCongr`;
* `Fin.castAddOrderEmb m` : `Fin.castAdd` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+m)`;
* `Fin.castSuccOrderEmb` : `Fin.castSucc` as an `OrderEmbedding`, embed `Fin n` into `Fin (n+1)`;
* `Fin.addNatOrderEmb m i` : `Fin.addNat` as an `OrderEmbedding`, add `m` on `i` on the right,
  generalizes `Fin.succ`;
* `Fin.natAddOrderEmb n i` : `Fin.natAdd` as an `OrderEmbedding`, adds `n` on `i` on the left;
* `Fin.revOrderIso`: `Fin.rev` as an `OrderIso`, the antitone involution given by `i ↦ n-(i+1)`
-/

assert_not_exists Monoid

open Function Nat Set

namespace Fin
variable {m n : ℕ}

/-! ### Instances -/

instance instLinearOrder : LinearOrder (Fin n) :=
  @LinearOrder.liftWithOrd (Fin n) _ _ ⟨fun x y => ⟨max x y, max_rec' (· < n) x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' (· < n) x.2 y.2⟩⟩ _ Fin.val Fin.val_injective (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instBoundedOrder : BoundedOrder (Fin (n + 1)) where
  top := last n
  le_top := le_last
  bot := 0
  bot_le := zero_le

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instPartialOrder : PartialOrder (Fin n) := inferInstance
instance instLattice      : Lattice (Fin n)      := inferInstance

/-! ### Miscellaneous lemmas -/

lemma top_eq_last (n : ℕ) : ⊤ = Fin.last n := rfl
#align fin.top_eq_last Fin.top_eq_last

lemma bot_eq_zero (n : ℕ) : ⊥ = (0 : Fin (n + 1)) := rfl
#align fin.bot_eq_zero Fin.bot_eq_zero

section ToFin
variable {α : Type*} [Preorder α] {f : α → Fin (n + 1)}

lemma strictMono_pred_comp (hf : ∀ a, f a ≠ 0) (hf₂ : StrictMono f) :
    StrictMono (fun a => pred (f a) (hf a)) := fun _ _ h => pred_lt_pred_iff.2 (hf₂ h)

lemma monotone_pred_comp (hf : ∀ a, f a ≠ 0) (hf₂ : Monotone f) :
    Monotone (fun a => pred (f a) (hf a)) := fun _ _ h => pred_le_pred_iff.2 (hf₂ h)

lemma strictMono_castPred_comp (hf : ∀ a, f a ≠ last n) (hf₂ : StrictMono f) :
    StrictMono (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_lt_castPred_iff.2 (hf₂ h)

lemma monotone_castPred_comp (hf : ∀ a, f a ≠ last n) (hf₂ : Monotone f) :
    Monotone (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_le_castPred_iff.2 (hf₂ h)

end ToFin

section FromFin
variable {α : Type*} [Preorder α] {f : Fin (n + 1) → α}

/-- A function `f` on `Fin (n + 1)` is strictly monotone if and only if `f i < f (i + 1)`
for all `i`. -/
lemma strictMono_iff_lt_succ : StrictMono f ↔ ∀ i : Fin n, f (castSucc i) < f i.succ :=
  liftFun_iff_succ (· < ·)
#align fin.strict_mono_iff_lt_succ Fin.strictMono_iff_lt_succ

/-- A function `f` on `Fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for all `i`. -/
lemma monotone_iff_le_succ : Monotone f ↔ ∀ i : Fin n, f (castSucc i) ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| liftFun_iff_succ (· ≤ ·)
#align fin.monotone_iff_le_succ Fin.monotone_iff_le_succ

/-- A function `f` on `Fin (n + 1)` is strictly antitone if and only if `f (i + 1) < f i`
for all `i`. -/
lemma strictAnti_iff_succ_lt : StrictAnti f ↔ ∀ i : Fin n, f i.succ < f (castSucc i) :=
  liftFun_iff_succ (· > ·)
#align fin.strict_anti_iff_succ_lt Fin.strictAnti_iff_succ_lt

/-- A function `f` on `Fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for all `i`. -/
lemma antitone_iff_succ_le : Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f (castSucc i) :=
  antitone_iff_forall_lt.trans <| liftFun_iff_succ (· ≥ ·)
#align fin.antitone_iff_succ_le Fin.antitone_iff_succ_le

end FromFin

/-! #### Monotonicity -/

lemma val_strictMono : StrictMono (val : Fin n → ℕ) := fun _ _ ↦ id
#align fin.coe_strict_mono Fin.val_strictMono

lemma strictMono_succ : StrictMono (succ : Fin n → Fin (n + 1)) := fun _ _ ↦ succ_lt_succ
lemma strictMono_castLE (h : n ≤ m) : StrictMono (castLE h : Fin n → Fin m) := fun _ _ ↦ id
lemma strictMono_castAdd (m) : StrictMono (castAdd m : Fin n → Fin (n + m)) := strictMono_castLE _
lemma strictMono_castSucc : StrictMono (castSucc : Fin n → Fin (n + 1)) := strictMono_castAdd _
lemma strictMono_natAdd (n) : StrictMono (natAdd n : Fin m → Fin (n + m)) :=
  fun i j h ↦ Nat.add_lt_add_left (show i.val < j.val from h) _
lemma strictMono_addNat (m) : StrictMono ((addNat · m) : Fin n → Fin (n + m)) :=
  fun i j h ↦ Nat.add_lt_add_right (show i.val < j.val from h) _

lemma strictMono_succAbove (p : Fin (n + 1)) : StrictMono (succAbove p) :=
  strictMono_castSucc.ite strictMono_succ
    (fun _ _ hij hj => (castSucc_lt_castSucc_iff.mpr hij).trans hj) fun i =>
    (castSucc_lt_succ i).le
#align fin.succ_above_aux Fin.strictMono_succAbove

variable {p : Fin (n + 1)} {i j : Fin n}

lemma succAbove_lt_succAbove_iff : succAbove p i < succAbove p j ↔ i < j :=
  (strictMono_succAbove p).lt_iff_lt

lemma succAbove_le_succAbove_iff : succAbove p i ≤ succAbove p j ↔ i ≤ j :=
  (strictMono_succAbove p).le_iff_le

lemma predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, coe_pred]
  · exact pred_le_pred H
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · exact le_pred_of_lt ((not_lt.mp ha).trans_lt hb)
  · exact H
#align fin.pred_above_right_monotone Fin.predAbove_right_monotone

lemma predAbove_left_monotone (i : Fin (n + 1)) : Monotone fun p ↦ predAbove p i := fun a b H ↦ by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_le
  · rfl
#align fin.pred_above_left_monotone Fin.predAbove_left_monotone

/--  `Fin.predAbove p` as an `OrderHom`. -/
@[simps!] def predAboveOrderHom (p : Fin n) : Fin (n + 1) →o Fin n :=
  ⟨p.predAbove, p.predAbove_right_monotone⟩

/-! #### Order isomorphisms -/

/-- The equivalence `Fin n ≃ {i // i < n}` is an order isomorphism. -/
@[simps! apply symm_apply]
def orderIsoSubtype : Fin n ≃o {i // i < n} :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])
#align fin.order_iso_subtype Fin.orderIsoSubtype
#align fin.order_iso_subtype_symm_apply Fin.orderIsoSubtype_symm_apply
#align fin.order_iso_subtype_apply Fin.orderIsoSubtype_apply

/-- `Fin.cast` as an `OrderIso`.

`castOrderIso eq i` embeds `i` into an equal `Fin` type. -/
@[simps]
def castOrderIso (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨cast eq, cast eq.symm, leftInverse_cast eq, rightInverse_cast eq⟩
  map_rel_iff' := cast_le_cast eq
#align fin.cast Fin.castOrderIso

@[deprecated (since := "2024-05-23")] alias castIso := castOrderIso

@[simp]
lemma symm_castOrderIso (h : n = m) : (castOrderIso h).symm = castOrderIso h.symm := by subst h; rfl
#align fin.symm_cast Fin.symm_castOrderIso

@[deprecated (since := "2024-05-23")] alias symm_castIso := symm_castOrderIso

@[simp]
lemma castOrderIso_refl (h : n = n := rfl) : castOrderIso h = OrderIso.refl (Fin n) := by ext; simp
#align fin.cast_refl Fin.castOrderIso_refl

@[deprecated (since := "2024-05-23")] alias castIso_refl := castOrderIso_refl

/-- While in many cases `Fin.castOrderIso` is better than `Equiv.cast`/`cast`, sometimes we want to
apply a generic lemma about `cast`. -/
lemma castOrderIso_toEquiv (h : n = m) : (castOrderIso h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h; rfl
#align fin.cast_to_equiv Fin.castOrderIso_toEquiv

@[deprecated (since := "2024-05-23")] alias castIso_to_equiv := castOrderIso_toEquiv

/-- `Fin.rev n` as an order-reversing isomorphism. -/
@[simps! apply toEquiv]
def revOrderIso : (Fin n)ᵒᵈ ≃o Fin n := ⟨OrderDual.ofDual.trans revPerm, rev_le_rev⟩
#align fin.rev_order_iso Fin.revOrderIso
#align fin.rev_order_iso_apply Fin.revOrderIso_apply
#align fin.rev_order_iso_to_equiv Fin.revOrderIso_toEquiv

@[simp]
lemma revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual (rev i) := rfl
#align fin.rev_order_iso_symm_apply Fin.revOrderIso_symm_apply

/-! #### Order embeddings -/

/-- The inclusion map `Fin n → ℕ` is an order embedding. -/
@[simps! apply]
def valOrderEmb (n) : Fin n ↪o ℕ := ⟨valEmbedding, Iff.rfl⟩
#align fin.coe_order_embedding Fin.valOrderEmb

/-- The ordering on `Fin n` is a well order. -/
instance Lt.isWellOrder (n) : IsWellOrder (Fin n) (· < ·) := (valOrderEmb n).isWellOrder
#align fin.fin.lt.is_well_order Fin.Lt.isWellOrder

/-- `Fin.succ` as an `OrderEmbedding` -/
def succOrderEmb (n : ℕ) : Fin n ↪o Fin (n + 1) := .ofStrictMono succ strictMono_succ
#align fin.succ_embedding Fin.succEmb

@[simp, norm_cast] lemma coe_succOrderEmb : ⇑(succOrderEmb n) = Fin.succ := rfl
#align fin.coe_succ_embedding Fin.coe_succOrderEmb

/-- `Fin.castLE` as an `OrderEmbedding`.

`castLEEmb h i` embeds `i` into a larger `Fin` type. -/
@[simps! apply toEmbedding]
def castLEOrderEmb (h : n ≤ m) : Fin n ↪o Fin m := .ofStrictMono (castLE h) (strictMono_castLE h)
#align fin.cast_le Fin.castLEOrderEmb

/-- `Fin.castAdd` as an `OrderEmbedding`.

`castAddEmb m i` embeds `i : Fin n` in `Fin (n+m)`. See also `Fin.natAddEmb` and `Fin.addNatEmb`. -/
@[simps! apply toEmbedding]
def castAddOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (castAdd m) (strictMono_castAdd m)
#align fin.cast_add Fin.castAddOrderEmb

/-- `Fin.castSucc` as an `OrderEmbedding`.

`castSuccOrderEmb i` embeds `i : Fin n` in `Fin (n+1)`. -/
@[simps! apply toEmbedding]
def castSuccOrderEmb : Fin n ↪o Fin (n + 1) := .ofStrictMono castSucc strictMono_castSucc
#align fin.cast_succ Fin.castSuccEmb

/-- `Fin.addNat` as an `OrderEmbedding`.

`addNatOrderEmb m i` adds `m` to `i`, generalizes `Fin.succ`. -/
@[simps! apply toEmbedding]
def addNatOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (addNat · m) (strictMono_addNat m)
#align fin.add_nat Fin.addNatOrderEmb

/-- `Fin.natAdd` as an `OrderEmbedding`.

`natAddOrderEmb n i` adds `n` to `i` "on the left". -/
@[simps! apply toEmbedding]
def natAddOrderEmb (n) : Fin m ↪o Fin (n + m) := .ofStrictMono (natAdd n) (strictMono_natAdd n)
#align fin.nat_add Fin.natAddOrderEmb

/--  `Fin.succAbove p` as an `OrderEmbedding`. -/
@[simps! apply toEmbedding]
def succAboveOrderEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)
#align fin.succ_above Fin.succAboveOrderEmb

/-! ### Uniqueness of order isomorphisms -/

variable {α : Type*} [Preorder α]

/-- If `e` is an `orderIso` between `Fin n` and `Fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : Fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
@[simp] lemma coe_orderIso_apply (e : Fin n ≃o Fin m) (i : Fin n) : (e i : ℕ) = i := by
  rcases i with ⟨i, hi⟩
  dsimp only
  induction' i using Nat.strong_induction_on with i h
  refine le_antisymm (forall_lt_iff_le.1 fun j hj => ?_) (forall_lt_iff_le.1 fun j hj => ?_)
  · have := e.symm.lt_iff_lt.2 (mk_lt_of_lt_val hj)
    rw [e.symm_apply_apply] at this
    -- Porting note: convert was abusing definitional equality
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

instance orderIso_subsingleton' : Subsingleton (α ≃o Fin n) := OrderIso.symm_injective.subsingleton
#align fin.order_iso_subsingleton' Fin.orderIso_subsingleton'

instance orderIsoUnique : Unique (Fin n ≃o Fin n) := Unique.mk' _
#align fin.order_iso_unique Fin.orderIsoUnique

/-- Two strictly monotone functions from `Fin n` are equal provided that their ranges
are equal. -/
lemma strictMono_unique {f g : Fin n → α} (hf : StrictMono f) (hg : StrictMono g)
    (h : range f = range g) : f = g :=
  have : (hf.orderIso f).trans (OrderIso.setCongr _ _ h) = hg.orderIso g := Subsingleton.elim _ _
  congr_arg (Function.comp (Subtype.val : range g → α)) (funext <| RelIso.ext_iff.1 this)
#align fin.strict_mono_unique Fin.strictMono_unique

/-- Two order embeddings of `Fin n` are equal provided that their ranges are equal. -/
lemma orderEmbedding_eq {f g : Fin n ↪o α} (h : range f = range g) : f = g :=
  RelEmbedding.ext <| funext_iff.1 <| strictMono_unique f.strictMono g.strictMono h
#align fin.order_embedding_eq Fin.orderEmbedding_eq

end Fin
