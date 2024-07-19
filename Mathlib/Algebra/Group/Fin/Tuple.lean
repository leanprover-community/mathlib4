/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fin.VecNotation

#align_import data.fin.tuple.basic from "leanprover-community/mathlib"@"ef997baa41b5c428be3fb50089a7139bf4ee886b"

/-!
# Algebraic properties of tuples
-/

namespace Fin
variable {m n : ℕ} {α : Fin (n + 1) → Type*}

@[to_additive (attr := simp)]
lemma insertNth_one_right [∀ j, One (α j)] (i : Fin (n + 1)) (x : α i) :
    i.insertNth x 1 = Pi.mulSingle i x :=
  insertNth_eq_iff.2 <| by unfold removeNth; simp [succAbove_ne, Pi.one_def]
#align fin.insert_nth_zero_right Fin.insertNth_zero_right

@[to_additive (attr := simp)]
lemma insertNth_mul [∀ j, Mul (α j)] (i : Fin (n + 1)) (x y : α i) (p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x * y) (p * q) = i.insertNth x p * i.insertNth y q :=
  insertNth_binop (fun _ ↦ (· * ·)) i x y p q
#align fin.insert_nth_mul Fin.insertNth_mul
#align fin.insert_nth_add Fin.insertNth_add

@[to_additive (attr := simp)]
lemma insertNth_div [∀ j, Div (α j)] (i : Fin (n + 1)) (x y : α i)(p q : ∀ j, α (i.succAbove j)) :
    i.insertNth (x / y) (p / q) = i.insertNth x p / i.insertNth y q :=
  insertNth_binop (fun _ ↦ (· / ·)) i x y p q
#align fin.insert_nth_div Fin.insertNth_div
#align fin.insert_nth_sub Fin.insertNth_sub

@[to_additive (attr := simp)]
lemma insertNth_div_same [∀ j, Group (α j)] (i : Fin (n + 1)) (x y : α i)
    (p : ∀ j, α (i.succAbove j)) : i.insertNth x p / i.insertNth y p = Pi.mulSingle i (x / y) := by
  simp_rw [← insertNth_div, ← insertNth_one_right, Pi.div_def, div_self', Pi.one_def]
#align fin.insert_nth_sub_same Fin.insertNth_sub_same

end Fin

namespace Matrix

variable {α M : Type*} {n : ℕ}

section SMul
variable [SMul M α]

@[simp] lemma smul_empty (x : M) (v : Fin 0 → α) : x • v = ![] := empty_eq _
#align matrix.smul_empty Matrix.smul_empty

@[simp] lemma smul_cons (x : M) (y : α) (v : Fin n → α) :
    x • vecCons y v = vecCons (x • y) (x • v) := by ext i; refine i.cases ?_ ?_ <;> simp
#align matrix.smul_cons Matrix.smul_cons

end SMul

section Add
variable [Add α]

@[simp] lemma empty_add_empty (v w : Fin 0 → α) : v + w = ![] := empty_eq _
#align matrix.empty_add_empty Matrix.empty_add_empty

@[simp] lemma cons_add (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v + w = vecCons (x + vecHead w) (v + vecTail w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
#align matrix.cons_add Matrix.cons_add

@[simp] lemma add_cons (v : Fin n.succ → α) (y : α) (w : Fin n → α) :
    v + vecCons y w = vecCons (vecHead v + y) (vecTail v + w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
#align matrix.add_cons Matrix.add_cons

lemma cons_add_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v + vecCons y w = vecCons (x + y) (v + w) := by simp
#align matrix.cons_add_cons Matrix.cons_add_cons

@[simp] lemma head_add (a b : Fin n.succ → α) : vecHead (a + b) = vecHead a + vecHead b := rfl
#align matrix.head_add Matrix.head_add

@[simp] lemma tail_add (a b : Fin n.succ → α) : vecTail (a + b) = vecTail a + vecTail b := rfl
#align matrix.tail_add Matrix.tail_add

end Add

section Sub
variable [Sub α]

@[simp] lemma empty_sub_empty (v w : Fin 0 → α) : v - w = ![] := empty_eq _
#align matrix.empty_sub_empty Matrix.empty_sub_empty

@[simp] lemma cons_sub (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v - w = vecCons (x - vecHead w) (v - vecTail w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
#align matrix.cons_sub Matrix.cons_sub

@[simp] lemma sub_cons (v : Fin n.succ → α) (y : α) (w : Fin n → α) :
    v - vecCons y w = vecCons (vecHead v - y) (vecTail v - w) := by
  ext i; refine i.cases ?_ ?_ <;> simp [vecHead, vecTail]
#align matrix.sub_cons Matrix.sub_cons

lemma cons_sub_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v - vecCons y w = vecCons (x - y) (v - w) := by simp
#align matrix.cons_sub_cons Matrix.cons_sub_cons

@[simp] lemma head_sub (a b : Fin n.succ → α) : vecHead (a - b) = vecHead a - vecHead b := rfl
#align matrix.head_sub Matrix.head_sub

@[simp] lemma tail_sub (a b : Fin n.succ → α) : vecTail (a - b) = vecTail a - vecTail b := rfl
#align matrix.tail_sub Matrix.tail_sub

end Sub

section Zero
variable [Zero α]

@[simp] lemma zero_empty : (0 : Fin 0 → α) = ![] := empty_eq _
#align matrix.zero_empty Matrix.zero_empty

@[simp] lemma cons_zero_zero : vecCons (0 : α) (0 : Fin n → α) = 0 := by
  ext i; exact i.cases rfl (by simp)
#align matrix.cons_zero_zero Matrix.cons_zero_zero

@[simp] lemma head_zero : vecHead (0 : Fin n.succ → α) = 0 := rfl
#align matrix.head_zero Matrix.head_zero

@[simp] lemma tail_zero : vecTail (0 : Fin n.succ → α) = 0 := rfl
#align matrix.tail_zero Matrix.tail_zero

@[simp] lemma cons_eq_zero_iff {v : Fin n → α} {x : α} : vecCons x v = 0 ↔ x = 0 ∧ v = 0 where
  mp h := ⟨congr_fun h 0, by convert congr_arg vecTail h⟩
  mpr := fun ⟨hx, hv⟩ ↦ by simp [hx, hv]
#align matrix.cons_eq_zero_iff Matrix.cons_eq_zero_iff

lemma cons_nonzero_iff {v : Fin n → α} {x : α} : vecCons x v ≠ 0 ↔ x ≠ 0 ∨ v ≠ 0 where
  mp h := not_and_or.mp (h ∘ cons_eq_zero_iff.mpr)
  mpr h := mt cons_eq_zero_iff.mp (not_and_or.mpr h)
#align matrix.cons_nonzero_iff Matrix.cons_nonzero_iff

end Zero

section Neg
variable [Neg α]

@[simp] lemma neg_empty (v : Fin 0 → α) : -v = ![] := empty_eq _
#align matrix.neg_empty Matrix.neg_empty

@[simp] lemma neg_cons (x : α) (v : Fin n → α) : -vecCons x v = vecCons (-x) (-v) := by
  ext i; refine i.cases ?_ ?_ <;> simp
#align matrix.neg_cons Matrix.neg_cons

@[simp] lemma head_neg (a : Fin n.succ → α) : vecHead (-a) = -vecHead a := rfl
#align matrix.head_neg Matrix.head_neg

@[simp] lemma tail_neg (a : Fin n.succ → α) : vecTail (-a) = -vecTail a := rfl
#align matrix.tail_neg Matrix.tail_neg

end Neg
end Matrix
