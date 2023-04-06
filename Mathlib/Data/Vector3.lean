/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.vector3
! leanprover-community/mathlib commit 3d7987cda72abc473c7cdbbb075170e9ac620042
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Fin2
import Mathbin.Tactic.Localized

/-!
# Alternate definition of `vector` in terms of `fin2`

This file provides a locale `vector3` which overrides the `[a, b, c]` notation to create a `vector3`
instead of a `list`.

The `::` notation is also overloaded by this file to mean `vector3.cons`.
-/


open Fin2 Nat

universe u

variable {α : Type _} {m n : ℕ}

/-- Alternate definition of `vector` based on `fin2`. -/
def Vector3 (α : Type u) (n : ℕ) : Type u :=
  Fin2 n → α
#align vector3 Vector3

instance [Inhabited α] : Inhabited (Vector3 α n) :=
  Pi.inhabited _

namespace Vector3

/-- The empty vector -/
@[match_pattern]
def nil : Vector3 α 0 :=
  fun.
#align vector3.nil Vector3.nil

/-- The vector cons operation -/
@[match_pattern]
def cons (a : α) (v : Vector3 α n) : Vector3 α (succ n) := fun i =>
  by
  refine' i.cases' _ _
  exact a
  exact v
#align vector3.cons Vector3.cons

-- mathport name: vector.list
/- We do not want to make the following notation global, because then these expressions will be
overloaded, and only the expected type will be able to disambiguate the meaning. Worse: Lean will
try to insert a coercion from `vector3 α _` to `list α`, if a list is expected. -/
scoped notation3"["(l", "* => foldr (h t => Vector3.cons h t) Vector3.nil)"]" => l

-- mathport name: vector.cons
notation a "::" b => cons a b

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_fz (a : α) (v : Vector3 α n) : (a::v) fz = a :=
  rfl
#align vector3.cons_fz Vector3.cons_fz

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem cons_fs (a : α) (v : Vector3 α n) (i) : (a::v) (fs i) = v i :=
  rfl
#align vector3.cons_fs Vector3.cons_fs

/-- Get the `i`th element of a vector -/
@[reducible]
def nth (i : Fin2 n) (v : Vector3 α n) : α :=
  v i
#align vector3.nth Vector3.nth

/-- Construct a vector from a function on `fin2`. -/
@[reducible]
def ofFn (f : Fin2 n → α) : Vector3 α n :=
  f
#align vector3.of_fn Vector3.ofFn

/-- Get the head of a nonempty vector. -/
def head (v : Vector3 α (succ n)) : α :=
  v fz
#align vector3.head Vector3.head

/-- Get the tail of a nonempty vector. -/
def tail (v : Vector3 α (succ n)) : Vector3 α n := fun i => v (fs i)
#align vector3.tail Vector3.tail

theorem eq_nil (v : Vector3 α 0) : v = [] :=
  funext fun i => nomatch i
#align vector3.eq_nil Vector3.eq_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_head_tail (v : Vector3 α (succ n)) : (head v::tail v) = v :=
  funext fun i => Fin2.cases' rfl (fun _ => rfl) i
#align vector3.cons_head_tail Vector3.cons_head_tail

/-- Eliminator for an empty vector. -/
def nilElim {C : Vector3 α 0 → Sort u} (H : C []) (v : Vector3 α 0) : C v := by
  rw [eq_nil v] <;> apply H
#align vector3.nil_elim Vector3.nilElim

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Recursion principle for a nonempty vector. -/
def consElim {C : Vector3 α (succ n) → Sort u} (H : ∀ (a : α) (t : Vector3 α n), C (a::t))
    (v : Vector3 α (succ n)) : C v := by rw [← cons_head_tail v] <;> apply H
#align vector3.cons_elim Vector3.consElim

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem consElim_cons {C H a t} : @consElim α n C H (a::t) = H a t :=
  rfl
#align vector3.cons_elim_cons Vector3.consElim_cons

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Recursion principle with the vector as first argument. -/
@[elab_as_elim]
protected def recOn {C : ∀ {n}, Vector3 α n → Sort u} {n} (v : Vector3 α n) (H0 : C [])
    (Hs : ∀ {n} (a) (w : Vector3 α n), C w → C (a::w)) : C v :=
  Nat.recOn n (fun v => v.nilElim H0) (fun n IH v => v.consElim fun a t => Hs _ _ (IH _)) v
#align vector3.rec_on Vector3.recOn

@[simp]
theorem recOn_nil {C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0 :=
  rfl
#align vector3.rec_on_nil Vector3.recOn_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem recOn_cons {C H0 Hs n a v} :
    @Vector3.recOn α (@C) (succ n) (a::v) H0 @Hs = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs) :=
  rfl
#align vector3.rec_on_cons Vector3.recOn_cons

/-- Append two vectors -/
def append (v : Vector3 α m) (w : Vector3 α n) : Vector3 α (n + m) :=
  Nat.recOn m (fun _ => w)
    (fun m IH v => v.consElim fun a t => @Fin2.cases' (n + m) (fun _ => α) a (IH t)) v
#align vector3.append Vector3.append

-- mathport name: «expr +-+ »
local infixl:65 " +-+ " => Vector3.append

@[simp]
theorem append_nil (w : Vector3 α n) : [] +-+ w = w :=
  rfl
#align vector3.append_nil Vector3.append_nil

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem append_cons (a : α) (v : Vector3 α m) (w : Vector3 α n) : (a::v) +-+ w = a::v +-+ w :=
  rfl
#align vector3.append_cons Vector3.append_cons

@[simp]
theorem append_left :
    ∀ {m} (i : Fin2 m) (v : Vector3 α m) {n} (w : Vector3 α n), (v +-+ w) (left n i) = v i
  | _, @fz m, v, n, w => v.consElim fun a t => by simp [*, left]
  | _, @fs m i, v, n, w => v.consElim fun a t => by simp [*, left]
#align vector3.append_left Vector3.append_left

@[simp]
theorem append_add :
    ∀ {m} (v : Vector3 α m) {n} (w : Vector3 α n) (i : Fin2 n), (v +-+ w) (add i m) = w i
  | 0, v, n, w, i => rfl
  | succ m, v, n, w, i => v.consElim fun a t => by simp [*, add]
#align vector3.append_add Vector3.append_add

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Insert `a` into `v` at index `i`. -/
def insert (a : α) (v : Vector3 α n) (i : Fin2 (succ n)) : Vector3 α (succ n) := fun j =>
  (a::v) (insertPerm i j)
#align vector3.insert Vector3.insert

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem insert_fz (a : α) (v : Vector3 α n) : insert a v fz = a::v := by
  refine' funext fun j => j.cases' _ _ <;> intros <;> rfl
#align vector3.insert_fz Vector3.insert_fz

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (succ n)) :
    insert a (b::v) (fs i) = b::insert a v i :=
  funext fun j => by
    refine' j.cases' _ fun j => _ <;> simp [insert, insert_perm]
    refine' Fin2.cases' _ _ (insert_perm i j) <;> simp [insert_perm]
#align vector3.insert_fs Vector3.insert_fs

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem append_insert (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (succ n))
    (e : succ n + m = succ (n + m)) :
    insert a (t +-+ v) (Eq.recOn e (i.add m)) = Eq.recOn e (t +-+ insert a v i) :=
  by
  refine' Vector3.recOn t (fun e => _) (fun k b t IH e => _) e; rfl
  have e' := succ_add n k
  change
    insert a (b::t +-+ v) (Eq.recOn (congr_arg succ e') (fs (add i k))) =
      Eq.recOn (congr_arg succ e') (b::t +-+ insert a v i)
  rw [←
    (Eq.drecOn e' rfl :
      fs (Eq.recOn e' (i.add k) : Fin2 (succ (n + k))) =
        Eq.recOn (congr_arg succ e') (fs (i.add k)))]
  simp; rw [IH]; exact Eq.drecOn e' rfl
#align vector3.append_insert Vector3.append_insert

end Vector3

section Vector3

open Vector3

open Vector3

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- "Curried" exists, i.e. `∃ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def VectorEx : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∃ x : α, VectorEx k fun v => f (x::v)
#align vector_ex VectorEx

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- "Curried" forall, i.e. `∀ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def VectorAll : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∀ x : α, VectorAll k fun v => f (x::v)
#align vector_all VectorAll

theorem exists_vector_zero (f : Vector3 α 0 → Prop) : Exists f ↔ f [] :=
  ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v] <;> exact fv, fun f0 => ⟨[], f0⟩⟩
#align exists_vector_zero exists_vector_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem exists_vector_succ (f : Vector3 α (succ n) → Prop) : Exists f ↔ ∃ x v, f (x::v) :=
  ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v] <;> exact fv⟩, fun ⟨x, v, fxv⟩ => ⟨_, fxv⟩⟩
#align exists_vector_succ exists_vector_succ

theorem vectorEx_iff_exists : ∀ {n} (f : Vector3 α n → Prop), VectorEx n f ↔ Exists f
  | 0, f => (exists_vector_zero f).symm
  | succ n, f => Iff.trans (exists_congr fun x => vectorEx_iff_exists _) (exists_vector_succ f).symm
#align vector_ex_iff_exists vectorEx_iff_exists

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem vectorAll_iff_forall : ∀ {n} (f : Vector3 α n → Prop), VectorAll n f ↔ ∀ v, f v
  | 0, f => ⟨fun f0 v => v.nilElim f0, fun al => al []⟩
  | succ n, f =>
    (forall_congr' fun x => vectorAll_iff_forall fun v => f (x::v)).trans
      ⟨fun al v => v.consElim al, fun al x v => al (x::v)⟩
#align vector_all_iff_forall vectorAll_iff_forall

/-- `vector_allp p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `vector_allp p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def VectorAllp (p : α → Prop) (v : Vector3 α n) : Prop :=
  Vector3.recOn v True fun n a v IH =>
    @Vector3.recOn _ (fun n v => Prop) _ v (p a) fun n b v' _ => p a ∧ IH
#align vector_allp VectorAllp

@[simp]
theorem vectorAllp_nil (p : α → Prop) : VectorAllp p [] = True :=
  rfl
#align vector_allp_nil vectorAllp_nil

@[simp]
theorem vectorAllp_singleton (p : α → Prop) (x : α) : VectorAllp p [x] = p x :=
  rfl
#align vector_allp_singleton vectorAllp_singleton

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem vectorAllp_cons (p : α → Prop) (x : α) (v : Vector3 α n) :
    VectorAllp p (x::v) ↔ p x ∧ VectorAllp p v :=
  Vector3.recOn v (and_true_iff _).symm fun n a v IH => Iff.rfl
#align vector_allp_cons vectorAllp_cons

theorem vectorAllp_iff_forall (p : α → Prop) (v : Vector3 α n) : VectorAllp p v ↔ ∀ i, p (v i) :=
  by
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
#align vector_allp_iff_forall vectorAllp_iff_forall

theorem VectorAllp.imp {p q : α → Prop} (h : ∀ x, p x → q x) {v : Vector3 α n}
    (al : VectorAllp p v) : VectorAllp q v :=
  (vectorAllp_iff_forall _ _).2 fun i => h _ <| (vectorAllp_iff_forall _ _).1 al _
#align vector_allp.imp VectorAllp.imp

end Vector3

