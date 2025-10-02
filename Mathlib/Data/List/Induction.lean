/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-! ### Induction principles for lists -/

variable {α : Type*}

namespace List

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
def reverseRecOn {motive : List α → Sort*} (l : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : motive l :=
  match h : reverse l with
  | [] => cast (congr_arg motive <| by simpa using congr(reverse $h.symm)) <|
      nil
  | head :: tail =>
    cast (congr_arg motive <| by simpa using congr(reverse $h.symm)) <|
      append_singleton _ head <| reverseRecOn (reverse tail) nil append_singleton
termination_by l.length
decreasing_by
  simp_wf
  rw [← length_reverse (as := l), h, length_cons]
  simp

@[simp]
theorem reverseRecOn_nil {motive : List α → Sort*} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    reverseRecOn [] nil append_singleton = nil := reverseRecOn.eq_1 ..

-- `unusedHavesSuffices` is getting confused by the unfolding of `reverseRecOn`
@[simp, nolint unusedHavesSuffices]
theorem reverseRecOn_concat {motive : List α → Sort*} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    reverseRecOn (motive := motive) (xs ++ [x]) nil append_singleton =
      append_singleton _ _ (reverseRecOn (motive := motive) xs nil append_singleton) := by
  suffices ∀ ys (h : reverse (reverse xs) = ys),
      reverseRecOn (motive := motive) (xs ++ [x]) nil append_singleton =
        cast (by simp [(reverse_reverse _).symm.trans h])
          (append_singleton _ x (reverseRecOn (motive := motive) ys nil append_singleton)) by
    exact this _ (reverse_reverse xs)
  intro ys hy
  conv_lhs => unfold reverseRecOn
  grind

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
@[elab_as_elim]
def bidirectionalRec {motive : List α → Sort*} (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) :
    ∀ l, motive l
  | [] => nil
  | [a] => singleton a
  | a :: b :: l =>
    let l' := dropLast (b :: l)
    let b' := getLast (b :: l) (cons_ne_nil _ _)
    cast (by rw [← dropLast_append_getLast (cons_ne_nil b l)]) <|
      cons_append a l' b' (bidirectionalRec nil singleton cons_append l')
termination_by l => l.length

@[simp]
theorem bidirectionalRec_nil {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) :
    bidirectionalRec nil singleton cons_append [] = nil := bidirectionalRec.eq_1 ..


@[simp]
theorem bidirectionalRec_singleton {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) (a : α) :
    bidirectionalRec nil singleton cons_append [a] = singleton a := by
  simp [bidirectionalRec]

@[simp]
theorem bidirectionalRec_cons_append {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b])))
    (a : α) (l : List α) (b : α) :
    bidirectionalRec nil singleton cons_append (a :: (l ++ [b])) =
      cons_append a l b (bidirectionalRec nil singleton cons_append l) := by
  conv_lhs => unfold bidirectionalRec
  cases l with grind

/-- Like `bidirectionalRec`, but with the list parameter placed first. -/
@[elab_as_elim]
abbrev bidirectionalRecOn {C : List α → Sort*} (l : List α) (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
  bidirectionalRec H0 H1 Hn l

/--
A dependent recursion principle for nonempty lists. Useful for dealing with
operations like `List.head` which are not defined on the empty list.
-/
@[elab_as_elim]
def recNeNil {motive : (l : List α) → l ≠ [] → Sort*}
    (singleton : ∀ x, motive [x] (cons_ne_nil x []))
    (cons : ∀ x xs h, motive xs h → motive (x :: xs) (cons_ne_nil x xs))
    (l : List α) (h : l ≠ []) : motive l h :=
  match l with
  | [x] => singleton x
  | x :: y :: xs =>
    cons x (y :: xs) (cons_ne_nil y xs) (recNeNil singleton cons (y :: xs) (cons_ne_nil y xs))

@[simp]
theorem recNeNil_singleton {motive : (l : List α) → l ≠ [] → Sort*} (x : α)
    (singleton : ∀ x, motive [x] (cons_ne_nil x []))
    (cons : ∀ x xs h, motive xs h → motive (x :: xs) (cons_ne_nil x xs)) :
    recNeNil singleton cons [x] (cons_ne_nil x []) = singleton x := rfl

@[simp]
theorem recNeNil_cons {motive : (l : List α) → l ≠ [] → Sort*} (x : α) (xs : List α) (h : xs ≠ [])
    (singleton : ∀ x, motive [x] (cons_ne_nil x []))
    (cons : ∀ x xs h, motive xs h → motive (x :: xs) (cons_ne_nil x xs)) :
    recNeNil singleton cons (x :: xs) (cons_ne_nil x xs) =
      cons x xs h (recNeNil singleton cons xs h) :=
  match xs with
  | _ :: _ => rfl

/--
A dependent recursion principle for nonempty lists. Useful for dealing with
operations like `List.head` which are not defined on the empty list.
Same as `List.recNeNil`, with a more convenient argument order.
-/
@[elab_as_elim, simp]
abbrev recOnNeNil {motive : (l : List α) → l ≠ [] → Sort*} (l : List α) (h : l ≠ [])
    (singleton : ∀ x, motive [x] (cons_ne_nil x []))
    (cons : ∀ x xs h, motive xs h → motive (x :: xs) (cons_ne_nil x xs)) :
    motive l h := recNeNil singleton cons l h

/--
A recursion principle for lists which separates the singleton case.
-/
@[elab_as_elim]
def twoStepInduction {motive : (l : List α) → Sort*} (nil : motive [])
    (singleton : ∀ x, motive [x])
    (cons_cons : ∀ x y xs, motive xs → (∀ y, motive (y :: xs)) → motive (x :: y :: xs))
    (l : List α) : motive l := match l with
  | [] => nil
  | [x] => singleton x
  | x :: y :: xs =>
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs))

@[simp]
theorem twoStepInduction_nil {motive : (l : List α) → Sort*} (nil : motive [])
    (singleton : ∀ x, motive [x])
    (cons_cons : ∀ x y xs, motive xs → (∀ y, motive (y :: xs)) → motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons [] = nil := twoStepInduction.eq_1 ..

@[simp]
theorem twoStepInduction_singleton {motive : (l : List α) → Sort*} (x : α) (nil : motive [])
    (singleton : ∀ x, motive [x])
    (cons_cons : ∀ x y xs, motive xs → (∀ y, motive (y :: xs)) → motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons [x] = singleton x := twoStepInduction.eq_2 ..

@[simp]
theorem twoStepInduction_cons_cons {motive : (l : List α) → Sort*} (x y : α) (xs : List α)
    (nil : motive []) (singleton : ∀ x, motive [x])
    (cons_cons : ∀ x y xs, motive xs → (∀ y, motive (y :: xs)) → motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons (x :: y :: xs)  =
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs)) := twoStepInduction.eq_3 ..

end List
