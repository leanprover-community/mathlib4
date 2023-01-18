/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.of_fn
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Tuple.Basic
import Mathbin.Data.List.Basic
import Mathbin.Data.List.Join

/-!
# Lists from functions

Theorems and lemmas for dealing with `list.of_fn`, which converts a function on `fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `of_fn`

- `list.length_of_fn`, which tells us the length of such a list
- `list.nth_of_fn`, which tells us the nth element of such a list
- `list.array_eq_of_fn`, which interprets the list form of an array as such a list.
- `list.equiv_sigma_tuple`, which is an `equiv` between lists and the functions that generate them
  via `list.of_fn`.
-/


universe u

variable {α : Type u}

open Nat

namespace List

/- warning: list.length_of_fn_aux clashes with [anonymous] -> [anonymous]
warning: list.length_of_fn_aux -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {n : Nat} (f : (Fin n) -> α) (m : Nat) (h : LE.le.{0} Nat Nat.hasLe m n) (l : List.{u} α), Eq.{1} Nat (List.length.{u} α (List.ofFnAux.{u} α n f m h l)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (List.length.{u} α l) m)
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.length_of_fn_aux [anonymous]ₓ'. -/
theorem [anonymous] {n} (f : Fin n → α) : ∀ m h l, length (ofFnAux f m h l) = length l + m
  | 0, h, l => rfl
  | succ m, h, l => (length_of_fn_aux m _ _).trans (succ_add _ _)
#align list.length_of_fn_aux[anonymous]

#print List.length_ofFn /-
/-- The length of a list converted from a function is the size of the domain. -/
@[simp]
theorem length_ofFn {n} (f : Fin n → α) : length (ofFn f) = n :=
  ([anonymous] f _ _ _).trans (zero_add _)
#align list.length_of_fn List.length_ofFn
-/

/- warning: list.nth_of_fn_aux clashes with [anonymous] -> [anonymous]
warning: list.nth_of_fn_aux -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {n : Nat} (f : (Fin n) -> α) (i : Nat) (m : Nat) (h : LE.le.{0} Nat Nat.hasLe m n) (l : List.{u} α), (forall (i : Nat), Eq.{succ u} (Option.{u} α) (List.get?.{u} α l i) (List.ofFnNthVal.{u} α n f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i m))) -> (Eq.{succ u} (Option.{u} α) (List.get?.{u} α (List.ofFnAux.{u} α n f m h l) i) (List.ofFnNthVal.{u} α n f i))
but is expected to have type
  forall {α : Type.{u}} {n : Type.{v}}, (Nat -> α -> n) -> Nat -> (List.{u} α) -> (List.{v} n)
Case conversion may be inaccurate. Consider using '#align list.nth_of_fn_aux [anonymous]ₓ'. -/
theorem [anonymous] {n} (f : Fin n → α) (i) :
    ∀ m h l, (∀ i, get? l i = ofFnNthVal f (i + m)) → get? (ofFnAux f m h l) i = ofFnNthVal f i
  | 0, h, l, H => H i
  | succ m, h, l, H =>
    nth_of_fn_aux m _ _
      (by
        intro j; cases' j with j
        · simp only [nth, of_fn_nth_val, zero_add, dif_pos (show m < n from h)]
        · simp only [nth, H, add_succ, succ_add])
#align list.nth_of_fn_aux[anonymous]

#print List.get?_ofFn /-
/-- The `n`th element of a list -/
@[simp]
theorem get?_ofFn {n} (f : Fin n → α) (i) : get? (ofFn f) i = ofFnNthVal f i :=
  [anonymous] f _ _ _ _ fun i => by
    simp only [of_fn_nth_val, dif_neg (not_lt.2 (Nat.le_add_left n i))] <;> rfl
#align list.nth_of_fn List.get?_ofFn
-/

#print List.nthLe_ofFn /-
theorem nthLe_ofFn {n} (f : Fin n → α) (i : Fin n) :
    nthLe (ofFn f) i ((length_ofFn f).symm ▸ i.2) = f i :=
  Option.some.inj <| by
    rw [← nth_le_nth] <;> simp only [List.get?_ofFn, of_fn_nth_val, Fin.eta, dif_pos i.is_lt]
#align list.nth_le_of_fn List.nthLe_ofFn
-/

#print List.nthLe_ofFn' /-
@[simp]
theorem nthLe_ofFn' {n} (f : Fin n → α) {i : ℕ} (h : i < (ofFn f).length) :
    nthLe (ofFn f) i h = f ⟨i, length_ofFn f ▸ h⟩ :=
  nthLe_ofFn f ⟨i, length_ofFn f ▸ h⟩
#align list.nth_le_of_fn' List.nthLe_ofFn'
-/

/- warning: list.map_of_fn -> List.map_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {n : Nat} (f : (Fin n) -> α) (g : α -> β), Eq.{succ u2} (List.{u2} β) (List.map.{u1, u2} α β g (List.ofFn.{u1} α n f)) (List.ofFn.{u2} β n (Function.comp.{1, succ u1, succ u2} (Fin n) α β g f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {n : Nat} (f : (Fin n) -> α) (g : α -> β), Eq.{succ u1} (List.{u1} β) (List.map.{u2, u1} α β g (List.ofFn.{u2} α n f)) (List.ofFn.{u1} β n (Function.comp.{1, succ u2, succ u1} (Fin n) α β g f))
Case conversion may be inaccurate. Consider using '#align list.map_of_fn List.map_ofFnₓ'. -/
@[simp]
theorem map_ofFn {β : Type _} {n : ℕ} (f : Fin n → α) (g : α → β) : map g (ofFn f) = ofFn (g ∘ f) :=
  ext_nthLe (by simp) fun i h h' => by simp
#align list.map_of_fn List.map_ofFn

/-- Arrays converted to lists are the same as `of_fn` on the indexing function of the array. -/
theorem array_eq_of_fn {n} (a : Array' n α) : a.toList = ofFn a.read :=
  by
  suffices ∀ {m h l}, DArray.revIterateAux a (fun i => cons) m h l = ofFnAux (DArray.read a) m h l
    from this
  intros ; induction' m with m IH generalizing l; · rfl
  simp only [DArray.revIterateAux, of_fn_aux, IH]
#align list.array_eq_of_fn List.array_eq_of_fn

/- warning: list.of_fn_congr -> List.ofFn_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Nat} {n : Nat} (h : Eq.{1} Nat m n) (f : (Fin m) -> α), Eq.{succ u1} (List.{u1} α) (List.ofFn.{u1} α m f) (List.ofFn.{u1} α n (fun (i : Fin n) => f (coeFn.{1, 1} (OrderIso.{0, 0} (Fin n) (Fin m) (Fin.hasLe n) (Fin.hasLe m)) (fun (_x : RelIso.{0, 0} (Fin n) (Fin m) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin m) (Fin.hasLe m))) => (Fin n) -> (Fin m)) (RelIso.hasCoeToFun.{0, 0} (Fin n) (Fin m) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin m) (Fin.hasLe m))) (Fin.cast n m (Eq.symm.{1} Nat m n h)) i)))
but is expected to have type
  forall {α : Type.{u1}} {m : Nat} {n : Nat} (h : Eq.{1} Nat m n) (f : (Fin m) -> α), Eq.{succ u1} (List.{u1} α) (List.ofFn.{u1} α m f) (List.ofFn.{u1} α n (fun (i : Fin n) => f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin m)) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin m) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin m)) (Fin n) (Fin m) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin m))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin m) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{0, 0} (Fin n) (Fin m) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (Fin.cast n m (Eq.symm.{1} Nat m n h)))) i)))
Case conversion may be inaccurate. Consider using '#align list.of_fn_congr List.ofFn_congrₓ'. -/
@[congr]
theorem ofFn_congr {m n : ℕ} (h : m = n) (f : Fin m → α) :
    ofFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i) :=
  by
  subst h
  simp_rw [Fin.cast_refl, OrderIso.refl_apply]
#align list.of_fn_congr List.ofFn_congr

#print List.ofFn_zero /-
/-- `of_fn` on an empty domain is the empty list. -/
@[simp]
theorem ofFn_zero (f : Fin 0 → α) : ofFn f = [] :=
  rfl
#align list.of_fn_zero List.ofFn_zero
-/

/- warning: list.of_fn_succ -> List.ofFn_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} (f : (Fin (Nat.succ n)) -> α), Eq.{succ u1} (List.{u1} α) (List.ofFn.{u1} α (Nat.succ n) f) (List.cons.{u1} α (f (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))) (List.ofFn.{u1} α n (fun (i : Fin n) => f (Fin.succ n i))))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} (f : (Fin (Nat.succ n)) -> α), Eq.{succ u1} (List.{u1} α) (List.ofFn.{u1} α (Nat.succ n) f) (List.cons.{u1} α (f (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) (List.ofFn.{u1} α n (fun (i : Fin n) => f (Fin.succ n i))))
Case conversion may be inaccurate. Consider using '#align list.of_fn_succ List.ofFn_succₓ'. -/
@[simp]
theorem ofFn_succ {n} (f : Fin (succ n) → α) : ofFn f = f 0 :: ofFn fun i => f i.succ :=
  by
  suffices
    ∀ {m h l}, ofFnAux f (succ m) (succ_le_succ h) l = f 0 :: ofFnAux (fun i => f i.succ) m h l from
    this
  intros ; induction' m with m IH generalizing l; · rfl
  rw [of_fn_aux, IH]; rfl
#align list.of_fn_succ List.ofFn_succ

/- warning: list.of_fn_succ' -> List.ofFn_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} (f : (Fin (Nat.succ n)) -> α), Eq.{succ u1} (List.{u1} α) (List.ofFn.{u1} α (Nat.succ n) f) (List.concat.{u1} α (List.ofFn.{u1} α n (fun (i : Fin n) => f (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i))) (f (Fin.last n)))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} (f : (Fin (Nat.succ n)) -> α), Eq.{succ u1} (List.{u1} α) (List.ofFn.{u1} α (Nat.succ n) f) (List.concat.{u1} α (List.ofFn.{u1} α n (fun (i : Fin n) => f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) (Fin.castSucc n)) i))) (f (Fin.last n)))
Case conversion may be inaccurate. Consider using '#align list.of_fn_succ' List.ofFn_succ'ₓ'. -/
theorem ofFn_succ' {n} (f : Fin (succ n) → α) :
    ofFn f = (ofFn fun i => f i.cast_succ).concat (f (Fin.last _)) :=
  by
  induction' n with n IH
  · rw [of_fn_zero, concat_nil, of_fn_succ, of_fn_zero]
    rfl
  · rw [of_fn_succ, IH, of_fn_succ, concat_cons, Fin.castSucc_zero]
    congr 3
    simp_rw [Fin.castSucc_fin_succ]
#align list.of_fn_succ' List.ofFn_succ'

#print List.ofFn_eq_nil_iff /-
@[simp]
theorem ofFn_eq_nil_iff {n : ℕ} {f : Fin n → α} : ofFn f = [] ↔ n = 0 := by
  cases n <;> simp only [of_fn_zero, of_fn_succ, eq_self_iff_true, Nat.succ_ne_zero]
#align list.of_fn_eq_nil_iff List.ofFn_eq_nil_iff
-/

#print List.last_ofFn /-
theorem last_ofFn {n : ℕ} (f : Fin n → α) (h : ofFn f ≠ [])
    (hn : n - 1 < n := Nat.pred_lt <| ofFn_eq_nil_iff.Not.mp h) :
    getLast (ofFn f) h = f ⟨n - 1, hn⟩ := by simp [last_eq_nth_le]
#align list.last_of_fn List.last_ofFn
-/

#print List.last_ofFn_succ /-
theorem last_ofFn_succ {n : ℕ} (f : Fin n.succ → α)
    (h : ofFn f ≠ [] := mt ofFn_eq_nil_iff.mp (Nat.succ_ne_zero _)) :
    getLast (ofFn f) h = f (Fin.last _) :=
  last_ofFn f h
#align list.last_of_fn_succ List.last_ofFn_succ
-/

/- warning: list.of_fn_add -> List.ofFn_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Nat} {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) -> α), Eq.{succ u1} (List.{u1} α) (List.ofFn.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n) f) (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) (List.ofFn.{u1} α m (fun (i : Fin m) => f (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe m) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (fun (_x : RelEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) => (Fin m) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin m) (Fin.hasLe m)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) (Fin.castAdd m n) i))) (List.ofFn.{u1} α n (fun (j : Fin n) => f (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)))) (Fin.natAdd m n) j))))
but is expected to have type
  forall {α : Type.{u1}} {m : Nat} {n : Nat} (f : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) -> α), Eq.{succ u1} (List.{u1} α) (List.ofFn.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n) f) (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) (List.ofFn.{u1} α m (fun (i : Fin m) => f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin m) (fun (_x : Fin m) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin m) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)))) (RelEmbedding.toEmbedding.{0, 0} (Fin m) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : Fin m) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : Fin m) => LE.le.{0} (Fin m) (instLEFin m) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) (Fin.castAdd m n)) i))) (List.ofFn.{u1} α n (fun (j : Fin n) => f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) (Fin.natAdd m n)) j))))
Case conversion may be inaccurate. Consider using '#align list.of_fn_add List.ofFn_addₓ'. -/
/-- Note this matches the convention of `list.of_fn_succ'`, putting the `fin m` elements first. -/
theorem ofFn_add {m n} (f : Fin (m + n) → α) :
    List.ofFn f =
      (List.ofFn fun i => f (Fin.castAdd n i)) ++ List.ofFn fun j => f (Fin.natAdd m j) :=
  by
  induction' n with n IH
  · rw [of_fn_zero, append_nil, Fin.castAdd_zero, Fin.cast_refl]
    rfl
  · rw [of_fn_succ', of_fn_succ', IH, append_concat]
    rfl
#align list.of_fn_add List.ofFn_add

#print List.ofFn_mul /-
/-- This breaks a list of `m*n` items into `m` groups each containing `n` elements. -/
theorem ofFn_mul {m n} (f : Fin (m * n) → α) :
    List.ofFn f =
      List.join
        (List.ofFn fun i : Fin m =>
          List.ofFn fun j : Fin n =>
            f
              ⟨i * n + j,
                calc
                  ↑i * n + j < (i + 1) * n :=
                    (add_lt_add_left j.Prop _).trans_eq (add_one_mul _ _).symm
                  _ ≤ _ := Nat.mul_le_mul_right _ i.Prop
                  ⟩) :=
  by
  induction' m with m IH
  · simp_rw [of_fn_zero, zero_mul, of_fn_zero, join]
  · simp_rw [of_fn_succ', succ_mul, join_concat, of_fn_add, IH]
    rfl
#align list.of_fn_mul List.ofFn_mul
-/

#print List.ofFn_mul' /-
/-- This breaks a list of `m*n` items into `n` groups each containing `m` elements. -/
theorem ofFn_mul' {m n} (f : Fin (m * n) → α) :
    List.ofFn f =
      List.join
        (List.ofFn fun i : Fin n =>
          List.ofFn fun j : Fin m =>
            f
              ⟨m * i + j,
                calc
                  m * i + j < m * (i + 1) :=
                    (add_lt_add_left j.Prop _).trans_eq (mul_add_one _ _).symm
                  _ ≤ _ := Nat.mul_le_mul_left _ i.Prop
                  ⟩) :=
  by simp_rw [mul_comm m n, mul_comm m, of_fn_mul, Fin.cast_mk]
#align list.of_fn_mul' List.ofFn_mul'
-/

#print List.ofFn_nthLe /-
theorem ofFn_nthLe : ∀ l : List α, (ofFn fun i => nthLe l i i.2) = l
  | [] => rfl
  | a :: l => by
    rw [of_fn_succ]
    congr
    simp only [Fin.val_succ]
    exact of_fn_nth_le l
#align list.of_fn_nth_le List.ofFn_nthLe
-/

#print List.mem_ofFn /-
-- not registered as a simp lemma, as otherwise it fires before `forall_mem_of_fn_iff` which
-- is much more useful
theorem mem_ofFn {n} (f : Fin n → α) (a : α) : a ∈ ofFn f ↔ a ∈ Set.range f :=
  by
  simp only [mem_iff_nth_le, Set.mem_range, nth_le_of_fn']
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨_, h⟩, fun ⟨i, hi⟩ => ⟨i.1, (length_of_fn f).symm ▸ i.2, by simpa using hi⟩⟩
#align list.mem_of_fn List.mem_ofFn
-/

#print List.forall_mem_ofFn_iff /-
@[simp]
theorem forall_mem_ofFn_iff {n : ℕ} {f : Fin n → α} {P : α → Prop} :
    (∀ i ∈ ofFn f, P i) ↔ ∀ j : Fin n, P (f j) := by simp only [mem_of_fn, Set.forall_range_iff]
#align list.forall_mem_of_fn_iff List.forall_mem_ofFn_iff
-/

#print List.ofFn_const /-
@[simp]
theorem ofFn_const (n : ℕ) (c : α) : (ofFn fun i : Fin n => c) = replicate n c :=
  Nat.recOn n (by simp) fun n ihn => by simp [ihn]
#align list.of_fn_const List.ofFn_const
-/

#print List.equivSigmaTuple /-
/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
def equivSigmaTuple : List α ≃ Σn, Fin n → α
    where
  toFun l := ⟨l.length, fun i => l.nthLe (↑i) i.2⟩
  invFun f := List.ofFn f.2
  left_inv := List.ofFn_nthLe
  right_inv := fun ⟨n, f⟩ =>
    Fin.sigma_eq_of_eq_comp_cast (length_ofFn _) <| funext fun i => nthLe_ofFn' f i.Prop
#align list.equiv_sigma_tuple List.equivSigmaTuple
-/

#print List.ofFnRec /-
/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using list.of_fn_rec`. -/
@[elab_as_elim]
def ofFnRec {C : List α → Sort _} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) (l : List α) : C l :=
  cast (congr_arg _ l.of_fn_nth_le) <| h l.length fun i => l.nthLe (↑i) i.2
#align list.of_fn_rec List.ofFnRec
-/

/- warning: list.of_fn_rec_of_fn -> List.ofFnRec_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {C : (List.{u1} α) -> Sort.{u2}} (h : forall (n : Nat) (f : (Fin n) -> α), C (List.ofFn.{u1} α n f)) {n : Nat} (f : (Fin n) -> α), Eq.{u2} (C (List.ofFn.{u1} α n f)) (List.ofFnRec.{u1, u2} α C h (List.ofFn.{u1} α n f)) (h n f)
but is expected to have type
  forall {α : Type.{u2}} {C : (List.{u2} α) -> Sort.{u1}} (h : forall (n : Nat) (f : (Fin n) -> α), C (List.ofFn.{u2} α n f)) {n : Nat} (f : (Fin n) -> α), Eq.{u1} (C (List.ofFn.{u2} α n f)) (List.ofFnRec.{u2, u1} α C h (List.ofFn.{u2} α n f)) (h n f)
Case conversion may be inaccurate. Consider using '#align list.of_fn_rec_of_fn List.ofFnRec_ofFnₓ'. -/
@[simp]
theorem ofFnRec_ofFn {C : List α → Sort _} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) {n : ℕ}
    (f : Fin n → α) : @ofFnRec _ C h (List.ofFn f) = h _ f :=
  equivSigmaTuple.right_inverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩
#align list.of_fn_rec_of_fn List.ofFnRec_ofFn

#print List.exists_iff_exists_tuple /-
theorem exists_iff_exists_tuple {P : List α → Prop} :
    (∃ l : List α, P l) ↔ ∃ (n : _)(f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.Surjective.exists.trans Sigma.exists
#align list.exists_iff_exists_tuple List.exists_iff_exists_tuple
-/

#print List.forall_iff_forall_tuple /-
theorem forall_iff_forall_tuple {P : List α → Prop} :
    (∀ l : List α, P l) ↔ ∀ (n) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.Surjective.forall.trans Sigma.forall
#align list.forall_iff_forall_tuple List.forall_iff_forall_tuple
-/

#print List.ofFn_inj' /-
/-- `fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expression. -/
theorem ofFn_inj' {m n : ℕ} {f : Fin m → α} {g : Fin n → α} :
    ofFn f = ofFn g ↔ (⟨m, f⟩ : Σn, Fin n → α) = ⟨n, g⟩ :=
  Iff.symm <| equivSigmaTuple.symm.Injective.eq_iff.symm
#align list.of_fn_inj' List.ofFn_inj'
-/

#print List.ofFn_injective /-
/-- Note we can only state this when the two functions are indexed by defeq `n`. -/
theorem ofFn_injective {n : ℕ} : Function.Injective (ofFn : (Fin n → α) → List α) := fun f g h =>
  eq_of_heq <| by injection of_fn_inj'.mp h
#align list.of_fn_injective List.ofFn_injective
-/

#print List.ofFn_inj /-
/-- A special case of `list.of_fn_inj'` for when the two functions are indexed by defeq `n`. -/
@[simp]
theorem ofFn_inj {n : ℕ} {f g : Fin n → α} : ofFn f = ofFn g ↔ f = g :=
  ofFn_injective.eq_iff
#align list.of_fn_inj List.ofFn_inj
-/

end List

