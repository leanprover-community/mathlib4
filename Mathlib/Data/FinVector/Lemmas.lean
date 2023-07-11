/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.FinVector.Defs

/-!
  Basic lemmas for `FinVector`
-/

namespace FinVector




/-
## Induction and case distinction
-/

@[eliminator, elab_as_elim]
def inductionOn {motive : ∀{n}, FinVector α n → Sort v} {m : Nat} (v : FinVector α m)
    (nil : motive nil)
    (cons : ∀{n}, (hd : α) → (tl : FinVector α n) → motive tl → motive (cons hd tl)) :
    motive v :=
  v.rec nil cons

@[elab_as_elim]
def inductionOn₂ {motive : ∀{n}, FinVector α n → FinVector β n → Sort v} {m : Nat}
    (xs : FinVector α m) (ys : FinVector β m)
    (nil : motive nil nil)
    (cons : ∀{n}, (x : α) → (y : β) → (xs : FinVector α n) → (ys : FinVector β n)
            → motive xs ys → motive (cons x xs) (cons y ys)) :
    motive xs ys :=
  match m with
   | 0 => cast (by simp[elim_nil]) nil
   | m+1 =>
      cast (by simp) <|
        cons xs.head ys.head xs.tail ys.tail (inductionOn₂ xs.tail ys.tail nil cons)

/--
  Case distinction in terms of `nil` and `cons` constructors
-/
@[elab_as_elim]
def cases {motive : ∀{n}, FinVector α n → Sort v} (nil : motive nil)
    (cons : ∀{n}, (hd : α) → (tl : FinVector α n) → motive (cons hd tl))
    {m : Nat} (v : FinVector α m) :
    motive v :=
  rec nil (fun hd tl _ => cons hd tl) v





/-!
## Basic operations
-/
variable {xs : FinVector α n}

@[simp]
theorem reverse_nil : reverse nil = @nil α :=
  elim_nil _

@[simp]
theorem reverse_reverse : reverse (reverse v) = v :=
  by simp[reverse]

section Append
variable {ys : FinVector α m}

-- @[simp]
-- theorem append_cons :
--     HEq (append (x ::ᵥ xs) ys) (x ::ᵥ (append xs ys)) := by
--   have : n+1+m = n+m+1 := Nat.add_right_comm ..
--   cases n
--   . simp[append]

@[simp]
theorem append_nil :
    append xs nil = xs := by
  simp[append]

end Append

@[simp]
theorem cons_zero : (x ::ᵥ xs) 0 = x :=
  rfl

@[simp]
theorem cons_succ : (x ::ᵥ xs) (Fin.succ i) = xs i :=
  rfl

@[simp]
theorem concat_cons : (x ::ᵥ xs).concat y = x ::ᵥ (xs.concat y) := by
  simp[concat, append]
  funext i
  cases i using Fin.cases
  . simp[Fin.splitAt]
  next i =>
    simp only [Fin.splitAt, Fin.val_succ, add_lt_add_iff_right, cons_succ]
    split_ifs
    . simp[cons]
    . rfl

@[simp]
theorem concat_nil : (nil.concat x) = x ::ᵥ nil := by
  funext i; cases i using Fin.cases
  next => rfl
  next i => exact Fin.elim0 i

@[simp]
theorem reverse_cons : reverse (x ::ᵥ xs) = (reverse xs).concat x := by
  funext i
  simp [reverse, cons, concat, Fin.rev, append]
  sorry



@[simp]
theorem reverse_concat : reverse (xs.concat x) = x ::ᵥ (reverse xs) := by
  cases xs
  simp only [reverse, concat, cons, toList_mk]
  congr
  simp [toList, (·++·), Vector.append, Append.append]
  rfl

/-!
## Reverse Induction
-/

/--
  Reverse induction principle
-/
def revInductionOn {motive : ∀ {n : ℕ}, FinVector α n → Sort _} {n : ℕ} (v : FinVector α n)
    (nil : motive nil)
    (concat : ∀ {n : ℕ} (xs : FinVector α n) (x : α), motive xs → motive (xs.concat x)) :
    motive v :=
  cast (by simp) <| inductionOn
    (motive := fun v => motive v.reverse)
    v.reverse
    (cast (by simp only [reverse_nil]) nil)
    (@fun n x xs (r : motive xs.reverse) => cast (by simp) <| concat xs.reverse x r)

/-!
## Folds
-/
@[simp] theorem foldl_reverse (l : FinVector α n) (f : β → α → β) (b) :
    l.reverse.foldl f b = l.foldr (fun x y => f y x) b := by
  induction l
  . rfl
  . simp_all

@[simp] theorem foldr_reverse (l : List α) (f : α → β → β) (b) :
    l.reverse.foldr f b = l.foldl (fun x y => f y x) b :=
  (foldl_reverse ..).symm.trans <| by simp

@[simp] theorem foldrM_append [Monad m] [LawfulMonad m] (f : α → β → m β) (b) (l l' : List α) :
    (l ++ l').foldrM f b = l'.foldrM f b >>= l.foldrM f := by
  induction l <;> simp [*]

@[simp] theorem foldl_append {β : Type _} (f : β → α → β) (b) (l l' : List α) :
    (l ++ l').foldl f b = l'.foldl f (l.foldl f b) := by simp [foldl_eq_foldlM]

@[simp] theorem foldr_append (f : α → β → β) (b) (l l' : List α) :
    (l ++ l').foldr f b = l.foldr f (l'.foldr f b) := by simp [foldr_eq_foldrM]

@[simp] theorem foldr_self_append (l : List α) : l.foldr cons l' = l ++ l' := by
  induction l <;> simp [*]

end FinVector
