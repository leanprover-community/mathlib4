/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Function.Basic

/-!
# Alternate definition of `Vector` in terms of `Fin2`
This file provides a locale `Vector3` which overrides the `[a, b, c]` notation to create a `Vector3`
instead of a `List`.
The `::` notation is also overloaded by this file to mean `Vector3.cons`.
-/


open Fin2 Nat

universe u

variable {α : Type _} {m n : ℕ}

/-- Alternate definition of `Vector` based on `fin2`. -/
def Vector3 (α : Type u) (n : ℕ) : Type u :=
  Fin2 n → α
#align Vector3 Vector3

instance [Inhabited α] : Inhabited (Vector3 α n) :=
  instInhabitedForAll_1 (Fin2 n)

namespace Vector3

/-- The empty Vector -/
@[match_pattern]
def nil : Vector3 α 0 :=
  fun.
#align Vector3.nil Vector3.nil

/-- The Vector cons operation -/
@[match_pattern]
def cons (a : α) (v : Vector3 α n) : Vector3 α (succ n) := fun i => by
  refine' i.cases' _ _
  exact a
  exact v
#align Vector3.cons Vector3.cons

/- We do not want to make the following notation global, because then these expressions will be
overloaded, and only the expected type will be able to disambiguate the meaning. Worse: Lean will
try to insert a coercion from `Vector3 α _` to `List α`, if a list is expected. -/
macro_rules
  | `([ $elems,* ]) => do
    let rec expandVector3Lit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandVector3Lit i false result
      | i+1, false => expandVector3Lit i true  (← ``(cons $(⟨elems.elemsAndSeps.get! i⟩) $result))
    if elems.elemsAndSeps.size < 64 then
      expandVector3Lit elems.elemsAndSeps.size false (← ``(nil))
    else
      `(%[ $elems,* | nil ])

-- Hack, since the previous code doesn't work
macro_rules
  | `([]) => `(nil)

-- mathport name: Vector.cons
notation a "::" b => cons a b

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_fz (a : α) (v : Vector3 α n) : (a::v) fz = a :=
  rfl
#align Vector3.cons_fz Vector3.cons_fz

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_fs (a : α) (v : Vector3 α n) (i) : (a::v) (fs i) = v i :=
  rfl
#align Vector3.cons_fs Vector3.cons_fs

/-- Get the `i`th element of a Vector -/
@[reducible]
def nth (i : Fin2 n) (v : Vector3 α n) : α :=
  v i
#align Vector3.nth Vector3.nth

/-- Construct a Vector from a function on `fin2`. -/
@[reducible]
def ofFn (f : Fin2 n → α) : Vector3 α n :=
  f
#align Vector3.of_fn Vector3.ofFn

/-- Get the head of a nonempty Vector. -/
def head (v : Vector3 α (succ n)) : α :=
  v fz
#align Vector3.head Vector3.head

/-- Get the tail of a nonempty Vector. -/
def tail (v : Vector3 α (succ n)) : Vector3 α n := fun i => v (fs i)
#align Vector3.tail Vector3.tail

theorem eq_nil (v : Vector3 α 0) : v = [] :=
  funext $ fun i => nomatch i
#align Vector3.eq_nil Vector3.eq_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_head_tail (v : Vector3 α (succ n)) : (head v::tail v) = v :=
  funext $ fun i => Fin2.cases' rfl (fun _ => rfl) i
#align Vector3.cons_head_tail Vector3.cons_head_tail

/-- Eliminator for an empty Vector. -/
def nilElim {C : Vector3 α 0 → Sort u} (H : C []) (v : Vector3 α 0) : C v := by rw [eq_nil v]; apply H
#align Vector3.nil_elim Vector3.nilElim

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Recursion principle for a nonempty Vector. -/
def consElim {C : Vector3 α (succ n) → Sort u} (H : ∀ (a : α) (t : Vector3 α n), C (a::t)) (v : Vector3 α (succ n)) :
    C v := by rw [← cons_head_tail v]; apply H
#align Vector3.cons_elim Vector3.consElim

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_elim_cons {C H a t} : @consElim α n C H (a::t) = H a t :=
  rfl
#align Vector3.cons_elim_cons Vector3.cons_elim_cons

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Recursion principle with the Vector as first argument. -/
@[elab_as_elim]
protected def recOn {C : ∀ {n}, Vector3 α n → Sort u} {n} (v : Vector3 α n) (H0 : C [])
    (Hs : ∀ {n} (a) (w : Vector3 α n), C w → C (a::w)) : C v :=
  Nat.recOn n (fun v => v.nilElim H0) (fun n IH v => v.consElim fun a t => Hs _ _ (IH _)) v
#align Vector3.rec_on Vector3.recOn

@[simp]
theorem rec_on_nil {C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0 :=
  rfl
#align Vector3.rec_on_nil Vector3.rec_on_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem rec_on_cons {C H0 Hs n a v} :
    @Vector3.recOn α (@C) (succ n) (a::v) H0 @Hs = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs) :=
  rfl
#align Vector3.rec_on_cons Vector3.rec_on_cons

/-- Append two Vectors -/
def append (v : Vector3 α m) (w : Vector3 α n) : Vector3 α (n + m) :=
  Nat.recOn m (fun _ => w) (fun m IH v => v.consElim $ fun a t => @Fin2.cases' (n + m) (fun _ => α) a (IH t)) v
#align Vector3.append Vector3.append

-- mathport name: «expr +-+ »
local infixl:65 " +-+ " => Vector3.append

@[simp]
theorem append_nil (w : Vector3 α n) : [] +-+ w = w :=
  rfl
#align Vector3.append_nil Vector3.append_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem append_cons (a : α) (v : Vector3 α m) (w : Vector3 α n) : (a::v) +-+ w = a::v +-+ w :=
  rfl
#align Vector3.append_cons Vector3.append_cons

@[simp]
theorem append_left : ∀ {m} (i : Fin2 m) (v : Vector3 α m) {n} (w : Vector3 α n), (v +-+ w) (left n i) = v i
  | _, @fz m, v, n, w => v.consElim fun a t => by simp [*, left]
  | _, @fs m i, v, n, w => v.consElim fun a t => by simp [*, left]
#align Vector3.append_left Vector3.append_left

@[simp]
theorem append_add : ∀ {m} (v : Vector3 α m) {n} (w : Vector3 α n) (i : Fin2 n), (v +-+ w) (add i m) = w i
  | 0, v, n, w, i => rfl
  | succ m, v, n, w, i => v.consElim fun a t => by simp [*, add]
#align Vector3.append_add Vector3.append_add

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Insert `a` into `v` at index `i`. -/
def insert (a : α) (v : Vector3 α n) (i : Fin2 (succ n)) : Vector3 α (succ n) := fun j => (a::v) (insertPerm i j)
#align Vector3.insert Vector3.insert

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem insert_fz (a : α) (v : Vector3 α n) : insert a v fz = a::v := by
  refine' funext fun j => j.cases' _ _ <;> intros <;> rfl
#align Vector3.insert_fz Vector3.insert_fz

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (succ n)) : insert a (b::v) (fs i) = b::insert a v i :=
  funext $ fun j => by
    refine' j.cases' _ fun j => _ <;> simp [insert, insert_perm]
    refine' Fin2.cases' _ _ (insert_perm i j) <;> simp [insert_perm]
#align Vector3.insert_fs Vector3.insert_fs

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem append_insert (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (succ n)) (e : succ n + m = succ (n + m)) :
    insert a (t +-+ v) (Eq.recOn e (i.add m)) = Eq.recOn e (t +-+ insert a v i) := by
  refine' Vector3.recOn t (fun e => _) (fun k b t IH e => _) e
  rfl
  have e' := succ_add n k
  change
    insert a (b::t +-+ v) (Eq.recOn (congr_arg succ e') (fs (add i k))) =
      Eq.recOn (congr_arg succ e') (b::t +-+ insert a v i)
  rw [←
    (Eq.drecOn e' rfl : fs (Eq.recOn e' (i.add k) : Fin2 (succ (n + k))) = Eq.recOn (congr_arg succ e') (fs (i.add k)))]
  simp
  rw [IH]
  exact Eq.drecOn e' rfl
#align Vector3.append_insert Vector3.append_insert

end Vector3

section Vector3

open Vector3

open Vector3

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- "Curried" exists, i.e. `∃ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def VectorEx : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∃ x : α, VectorEx k fun v => f (x::v)
#align Vector_ex VectorEx

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- "Curried" forall, i.e. `∀ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def VectorAll : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∀ x : α, VectorAll k fun v => f (x::v)
#align Vector_all VectorAll

theorem exists_Vector_zero (f : Vector3 α 0 → Prop) : Exists f ↔ f [] :=
  ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v] <;> exact fv, fun f0 => ⟨[], f0⟩⟩
#align exists_Vector_zero exists_Vector_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x v) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem exists_Vector_succ (f : Vector3 α (succ n) → Prop) : Exists f ↔ ∃ (x) (v), f (x::v) :=
  ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v] <;> exact fv⟩, fun ⟨x, v, fxv⟩ => ⟨_, fxv⟩⟩
#align exists_Vector_succ exists_Vector_succ

theorem Vector_ex_iff_exists : ∀ {n} (f : Vector3 α n → Prop), VectorEx n f ↔ Exists f
  | 0, f => (exists_Vector_zero f).symm
  | succ n, f => Iff.trans (exists_congr fun x => Vector_ex_iff_exists _) (exists_Vector_succ f).symm
#align Vector_ex_iff_exists Vector_ex_iff_exists

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Vector_all_iff_forall : ∀ {n} (f : Vector3 α n → Prop), VectorAll n f ↔ ∀ v, f v
  | 0, f => ⟨fun f0 v => v.nilElim f0, fun al => al []⟩
  | succ n, f =>
    (forall_congr' fun x => Vector_all_iff_forall fun v => f (x::v)).trans
      ⟨fun al v => v.consElim al, fun al x v => al (x::v)⟩
#align Vector_all_iff_forall Vector_all_iff_forall

/-- `Vector_allp p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `Vector_allp p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def VectorAllp (p : α → Prop) (v : Vector3 α n) : Prop :=
  Vector3.recOn v True fun n a v IH => @Vector3.recOn _ (fun n v => Prop) _ v (p a) fun n b v' _ => p a ∧ IH
#align Vector_allp VectorAllp

@[simp]
theorem Vector_allp_nil (p : α → Prop) : VectorAllp p [] = True :=
  rfl
#align Vector_allp_nil Vector_allp_nil

@[simp]
theorem Vector_allp_singleton (p : α → Prop) (x : α) : VectorAllp p [x] = p x :=
  rfl
#align Vector_allp_singleton Vector_allp_singleton

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem Vector_allp_cons (p : α → Prop) (x : α) (v : Vector3 α n) : VectorAllp p (x::v) ↔ p x ∧ VectorAllp p v :=
  Vector3.recOn v (and_true_iff _).symm fun n a v IH => Iff.rfl
#align Vector_allp_cons Vector_allp_cons

theorem Vector_allp_iff_forall (p : α → Prop) (v : Vector3 α n) : VectorAllp p v ↔ ∀ i, p (v i) := by
  refine' v.rec_on _ _
  · exact ⟨fun _ => Fin2.elim0, fun _ => trivial⟩

  · simp
    refine' fun n a v IH =>
      (and_congr_right fun _ => IH).trans
        ⟨fun ⟨pa, h⟩ i => by
          refine' i.cases' _ _
          exacts[pa, h], fun h => ⟨_, fun i => _⟩⟩
    · have h0 := h fz
      simp at h0
      exact h0

    · have hs := h (fs i)
      simp at hs
      exact hs


#align Vector_allp_iff_forall Vector_allp_iff_forall

theorem VectorAllp.imp {p q : α → Prop} (h : ∀ x, p x → q x) {v : Vector3 α n} (al : VectorAllp p v) : VectorAllp q v :=
  (Vector_allp_iff_forall _ _).2 fun i => h _ $ (Vector_allp_iff_forall _ _).1 al _
#align Vector_allp.imp VectorAllp.imp

end Vector3
