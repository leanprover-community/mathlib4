/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fin.Fin2
import Mathlib.Init.Logic
import Mathlib.Mathport.Notation
import Mathlib.Tactic.TypeStar

#align_import data.vector3 from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!
# Alternate definition of `Vector` in terms of `Fin2`

This file provides a locale `Vector3` which overrides the `[a, b, c]` notation to create a `Vector3`
instead of a `List`.

The `::` notation is also overloaded by this file to mean `Vector3.cons`.
-/

open Fin2 Nat

universe u

variable {α : Type*} {m n : ℕ}

/-- Alternate definition of `Vector` based on `Fin2`. -/
def Vector3 (α : Type u) (n : ℕ) : Type u :=
  Fin2 n → α
#align vector3 Vector3

instance [Inhabited α] : Inhabited (Vector3 α n) where
  default := fun _ => default

namespace Vector3

/-- The empty vector -/
@[match_pattern]
def nil : Vector3 α 0 :=
  nofun
#align vector3.nil Vector3.nil

/-- The vector cons operation -/
@[match_pattern]
def cons (a : α) (v : Vector3 α n) : Vector3 α (n + 1) := fun i => by
  refine i.cases' ?_ ?_
  · exact a
  · exact v
#align vector3.cons Vector3.cons

section
open Lean

-- Porting note: was
-- scoped notation3 "["(l", "* => foldr (h t => cons h t) nil)"]" => l
scoped macro_rules | `([$l,*]) => `(expand_foldr% (h t => cons h t) nil [$(.ofElems l),*])

-- this is copied from `src/Init/NotationExtra.lean`
@[app_unexpander Vector3.nil] def unexpandNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `([])

-- this is copied from `src/Init/NotationExtra.lean`
@[app_unexpander Vector3.cons] def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x [])      => `([$x])
  | `($(_) $x [$xs,*]) => `([$x, $xs,*])
  | _                  => throw ()

end

-- Overloading the usual `::` notation for `List.cons` with `Vector3.cons`.
@[inherit_doc]
scoped notation a " :: " b => cons a b

@[simp]
theorem cons_fz (a : α) (v : Vector3 α n) : (a :: v) fz = a :=
  rfl
#align vector3.cons_fz Vector3.cons_fz

@[simp]
theorem cons_fs (a : α) (v : Vector3 α n) (i) : (a :: v) (fs i) = v i :=
  rfl
#align vector3.cons_fs Vector3.cons_fs

/-- Get the `i`th element of a vector -/
abbrev nth (i : Fin2 n) (v : Vector3 α n) : α :=
  v i
#align vector3.nth Vector3.nth

/-- Construct a vector from a function on `Fin2`. -/
abbrev ofFn (f : Fin2 n → α) : Vector3 α n :=
  f
#align vector3.of_fn Vector3.ofFn

/-- Get the head of a nonempty vector. -/
def head (v : Vector3 α (n + 1)) : α :=
  v fz
#align vector3.head Vector3.head

/-- Get the tail of a nonempty vector. -/
def tail (v : Vector3 α (n + 1)) : Vector3 α n := fun i => v (fs i)
#align vector3.tail Vector3.tail

theorem eq_nil (v : Vector3 α 0) : v = [] :=
  funext fun i => nomatch i
#align vector3.eq_nil Vector3.eq_nil

theorem cons_head_tail (v : Vector3 α (n + 1)) : (head v :: tail v) = v :=
  funext fun i => Fin2.cases' rfl (fun _ => rfl) i
#align vector3.cons_head_tail Vector3.cons_head_tail

/-- Eliminator for an empty vector. -/
@[elab_as_elim]  -- Porting note: add `elab_as_elim`
def nilElim {C : Vector3 α 0 → Sort u} (H : C []) (v : Vector3 α 0) : C v := by
  rw [eq_nil v]; apply H
#align vector3.nil_elim Vector3.nilElim

/-- Recursion principle for a nonempty vector. -/
@[elab_as_elim]  -- Porting note: add `elab_as_elim`
def consElim {C : Vector3 α (n + 1) → Sort u} (H : ∀ (a : α) (t : Vector3 α n), C (a :: t))
    (v : Vector3 α (n + 1)) : C v := by rw [← cons_head_tail v]; apply H
#align vector3.cons_elim Vector3.consElim

@[simp]
theorem consElim_cons {C H a t} : @consElim α n C H (a :: t) = H a t :=
  rfl
#align vector3.cons_elim_cons Vector3.consElim_cons

/-- Recursion principle with the vector as first argument. -/
@[elab_as_elim]
protected def recOn {C : ∀ {n}, Vector3 α n → Sort u} {n} (v : Vector3 α n) (H0 : C [])
    (Hs : ∀ {n} (a) (w : Vector3 α n), C w → C (a :: w)) : C v :=
  match n with
  | 0 => v.nilElim H0
  | _ + 1 => v.consElim fun a t => Hs a t (Vector3.recOn t H0 Hs)
#align vector3.rec_on Vector3.recOn

@[simp]
theorem recOn_nil {C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0 :=
  rfl
#align vector3.rec_on_nil Vector3.recOn_nil

@[simp]
theorem recOn_cons {C H0 Hs n a v} :
    @Vector3.recOn α (@C) (n + 1) (a :: v) H0 @Hs = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs) :=
  rfl
#align vector3.rec_on_cons Vector3.recOn_cons

/-- Append two vectors -/
def append (v : Vector3 α m) (w : Vector3 α n) : Vector3 α (n + m) :=
  v.recOn w (fun a _ IH => a :: IH)
#align vector3.append Vector3.append

/--
A local infix notation for `Vector3.append`
-/
local infixl:65 " +-+ " => Vector3.append

@[simp]
theorem append_nil (w : Vector3 α n) : [] +-+ w = w :=
  rfl
#align vector3.append_nil Vector3.append_nil

@[simp]
theorem append_cons (a : α) (v : Vector3 α m) (w : Vector3 α n) : (a :: v) +-+ w = a :: v +-+ w :=
  rfl
#align vector3.append_cons Vector3.append_cons

@[simp]
theorem append_left :
    ∀ {m} (i : Fin2 m) (v : Vector3 α m) {n} (w : Vector3 α n), (v +-+ w) (left n i) = v i
  | _, @fz m, v, n, w => v.consElim fun a _t => by simp [*, left]
  | _, @fs m i, v, n, w => v.consElim fun _a t => by simp [append_left, left]
#align vector3.append_left Vector3.append_left

@[simp]
theorem append_add :
    ∀ {m} (v : Vector3 α m) {n} (w : Vector3 α n) (i : Fin2 n), (v +-+ w) (add i m) = w i
  | 0, v, n, w, i => rfl
  | m + 1, v, n, w, i => v.consElim fun _a t => by simp [append_add, add]
#align vector3.append_add Vector3.append_add

/-- Insert `a` into `v` at index `i`. -/
def insert (a : α) (v : Vector3 α n) (i : Fin2 (n + 1)) : Vector3 α (n + 1) := fun j =>
  (a :: v) (insertPerm i j)
#align vector3.insert Vector3.insert

@[simp]
theorem insert_fz (a : α) (v : Vector3 α n) : insert a v fz = a :: v := by
  refine funext fun j => j.cases' ?_ ?_ <;> intros <;> rfl
#align vector3.insert_fz Vector3.insert_fz

@[simp]
theorem insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (n + 1)) :
    insert a (b :: v) (fs i) = b :: insert a v i :=
  funext fun j => by
    refine j.cases' ?_ fun j => ?_ <;> simp [insert, insertPerm]
    refine Fin2.cases' ?_ ?_ (insertPerm i j) <;> simp [insertPerm]
#align vector3.insert_fs Vector3.insert_fs

theorem append_insert (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1))
    (e : (n + 1) + m = (n + m) + 1) :
    insert a (t +-+ v) (Eq.recOn e (i.add m)) = Eq.recOn e (t +-+ insert a v i) := by
  refine Vector3.recOn t (fun e => ?_) (@fun k b t IH _ => ?_) e
  · rfl
  have e' : (n + 1) + k = (n + k) + 1 := by omega
  change
    insert a (b :: t +-+ v)
      (Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (add i k))) =
      Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (b :: t +-+ insert a v i)
  rw [←
    (Eq.recOn e' rfl :
      fs (Eq.recOn e' (i.add k) : Fin2 ((n + k) + 1)) =
        Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (i.add k)))]
  simp; rw [IH]; exact Eq.recOn e' rfl
#align vector3.append_insert Vector3.append_insert

end Vector3

section Vector3

open Vector3

/-- "Curried" exists, i.e. `∃ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def VectorEx : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∃ x : α, VectorEx k fun v => f (x :: v)
#align vector_ex VectorEx

/-- "Curried" forall, i.e. `∀ x₁ ... xₙ, f [x₁, ..., xₙ]`. -/
def VectorAll : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∀ x : α, VectorAll k fun v => f (x :: v)
#align vector_all VectorAll

theorem exists_vector_zero (f : Vector3 α 0 → Prop) : Exists f ↔ f [] :=
  ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v]; exact fv, fun f0 => ⟨[], f0⟩⟩
#align exists_vector_zero exists_vector_zero

theorem exists_vector_succ (f : Vector3 α (succ n) → Prop) : Exists f ↔ ∃ x v, f (x :: v) :=
  ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v]; exact fv⟩, fun ⟨x, v, fxv⟩ => ⟨_, fxv⟩⟩
#align exists_vector_succ exists_vector_succ

theorem vectorEx_iff_exists : ∀ {n} (f : Vector3 α n → Prop), VectorEx n f ↔ Exists f
  | 0, f => (exists_vector_zero f).symm
  | succ _, f =>
    Iff.trans (exists_congr fun _ => vectorEx_iff_exists _) (exists_vector_succ f).symm
#align vector_ex_iff_exists vectorEx_iff_exists

theorem vectorAll_iff_forall : ∀ {n} (f : Vector3 α n → Prop), VectorAll n f ↔ ∀ v, f v
  | 0, _ => ⟨fun f0 v => v.nilElim f0, fun al => al []⟩
  | succ _, f =>
    (forall_congr' fun x => vectorAll_iff_forall fun v => f (x :: v)).trans
      ⟨fun al v => v.consElim al, fun al x v => al (x :: v)⟩
#align vector_all_iff_forall vectorAll_iff_forall

/-- `VectorAllP p v` is equivalent to `∀ i, p (v i)`, but unfolds directly to a conjunction,
  i.e. `VectorAllP p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
def VectorAllP (p : α → Prop) (v : Vector3 α n) : Prop :=
  Vector3.recOn v True fun a v IH =>
    @Vector3.recOn _ (fun _ => Prop) _ v (p a) fun _ _ _ => p a ∧ IH
#align vector_allp VectorAllP

@[simp]
theorem vectorAllP_nil (p : α → Prop) : VectorAllP p [] = True :=
  rfl
#align vector_allp_nil vectorAllP_nil

@[simp, nolint simpNF] -- Porting note (#10675): dsimp cannot prove this
theorem vectorAllP_singleton (p : α → Prop) (x : α) : VectorAllP p (cons x []) = p x :=
  rfl
#align vector_allp_singleton vectorAllP_singleton

@[simp]
theorem vectorAllP_cons (p : α → Prop) (x : α) (v : Vector3 α n) :
    VectorAllP p (x :: v) ↔ p x ∧ VectorAllP p v :=
  Vector3.recOn v (and_true_iff _).symm fun _ _ _ => Iff.rfl
#align vector_allp_cons vectorAllP_cons

theorem vectorAllP_iff_forall (p : α → Prop) (v : Vector3 α n) :
    VectorAllP p v ↔ ∀ i, p (v i) := by
  refine v.recOn ?_ ?_
  · exact ⟨fun _ => Fin2.elim0, fun _ => trivial⟩
  · simp only [vectorAllP_cons]
    refine fun {n} a v IH =>
      (and_congr_right fun _ => IH).trans
        ⟨fun ⟨pa, h⟩ i => by
          refine i.cases' ?_ ?_
          exacts [pa, h], fun h => ⟨?_, fun i => ?_⟩⟩
    · simpa using h fz
    · simpa using h (fs i)
#align vector_allp_iff_forall vectorAllP_iff_forall

theorem VectorAllP.imp {p q : α → Prop} (h : ∀ x, p x → q x) {v : Vector3 α n}
    (al : VectorAllP p v) : VectorAllP q v :=
  (vectorAllP_iff_forall _ _).2 fun _ => h _ <| (vectorAllP_iff_forall _ _).1 al _
#align vector_allp.imp VectorAllP.imp

end Vector3
