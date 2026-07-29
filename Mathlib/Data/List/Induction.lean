/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common
public import Mathlib.Util.CompileInductive

/-! ### Induction principles for lists -/

@[expose] public section

variable {α : Type*}

namespace List

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
def reverseRec {motive : List α → Sort*} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : ∀ l, motive l
  | [] => nil
  | a :: l => (dropLast_concat_getLast (cons_ne_nil a l)) ▸
    append_singleton _ _ ((a :: l).dropLast.reverseRec nil append_singleton)
  termination_by l => l.length

@[simp]
theorem reverseRec_nil {motive : List α → Sort*} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    [].reverseRec nil append_singleton = nil := by grind [reverseRec]

@[simp]
theorem reverseRec_concat {motive : List α → Sort*} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    (xs ++ [x]).reverseRec nil append_singleton =
    append_singleton xs x (xs.reverseRec nil append_singleton) := by
  grind [reverseRec, cases List]

/-- Like `reverseRec`, but with the list parameter placed first. -/
@[elab_as_elim]
abbrev reverseRecOn {motive : List α → Sort*} (l : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : motive l :=
  reverseRec nil append_singleton l

theorem reverseRecOn_nil {motive : List α → Sort*} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    reverseRecOn [] nil append_singleton = nil := by simp

theorem reverseRecOn_concat {motive : List α → Sort*} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    (xs ++ [x]).reverseRecOn nil append_singleton =
      append_singleton xs x (reverseRecOn xs nil append_singleton) := by simp

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
    (dropLast_concat_getLast (cons_ne_nil b l)) ▸
    cons_append a ((b :: l).dropLast) ((b :: l).getLast (cons_ne_nil _ _))
    ((b :: l).dropLast.bidirectionalRec nil singleton cons_append)
termination_by l => l.length

@[simp]
theorem bidirectionalRec_nil {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) :
    bidirectionalRec nil singleton cons_append [] = nil := by grind [bidirectionalRec]


@[simp]
theorem bidirectionalRec_singleton {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) (a : α) :
    bidirectionalRec nil singleton cons_append [a] = singleton a := by
  grind [bidirectionalRec]

@[simp]
theorem bidirectionalRec_cons_append {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b])))
    (a : α) (l : List α) (b : α) :
    bidirectionalRec nil singleton cons_append (a :: (l ++ [b])) =
      cons_append a l b (bidirectionalRec nil singleton cons_append l) := by
  grind [bidirectionalRec, cases List]

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
    twoStepInduction nil singleton cons_cons (x :: y :: xs) =
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs)) := twoStepInduction.eq_3 ..

end List
