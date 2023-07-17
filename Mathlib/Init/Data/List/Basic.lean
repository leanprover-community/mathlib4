/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

! This file was ported from Lean 3 source module init.data.list.basic
! leanprover-community/lean commit 7cb84a2a93c1e2d37b3ad5017fc5372973dbb9fb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Mathlib.Init.Logic
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Bool.Basic
import Mathlib.Init.Propext

open Decidable List

universe u v w

instance (α : Type u) : Inhabited (List α) :=
  ⟨List.nil⟩

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

#print List.hasDecEq /-
protected def hasDecEq [s : DecidableEq α] : DecidableEq (List α)
  | [], [] => isTrue rfl
  | a :: as, [] => isFalse fun h => List.noConfusion h
  | [], b :: bs => isFalse fun h => List.noConfusion h
  | a :: as, b :: bs =>
    match s a b with
    | is_true hab =>
      match has_dec_eq as bs with
      | is_true habs => isTrue (Eq.subst hab (Eq.subst habs rfl))
      | is_false nabs => isFalse fun h => List.noConfusion h fun _ habs => absurd habs nabs
    | is_false nab => isFalse fun h => List.noConfusion h fun hab _ => absurd hab nab
#align list.has_dec_eq List.hasDecEq
-/

instance [DecidableEq α] : DecidableEq (List α) :=
  List.hasDecEq

#print List.append /-
@[simp]
protected def append : List α → List α → List α
  | [], l => l
  | h :: s, t => h :: append s t
#align list.append List.append
-/

instance : Append (List α) :=
  ⟨List.append⟩

#print List.Mem /-
protected def Mem : α → List α → Prop
  | a, [] => False
  | a, b :: l => a = b ∨ mem a l
#align list.mem List.Mem
-/

instance : Membership α (List α) :=
  ⟨List.Mem⟩

instance decidableMem [DecidableEq α] (a : α) : ∀ l : List α, Decidable (a ∈ l)
  | [] => isFalse not_false
  | b :: l =>
    if h₁ : a = b then isTrue (Or.inl h₁)
    else
      match decidable_mem l with
      | is_true h₂ => isTrue (Or.inr h₂)
      | is_false h₂ => isFalse (not_or_of_not h₁ h₂)
#align list.decidable_mem List.decidableMem

instance : EmptyCollection (List α) :=
  ⟨List.nil⟩

protected def erase {α} [DecidableEq α] : List α → α → List α
  | [], b => []
  | a :: l, b => if a = b then l else a :: erase l b
#align list.erase List.eraseₓ

protected def bagInter {α} [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: l₁, l₂ => if a ∈ l₂ then a :: bag_inter l₁ (l₂.eraseₓ a) else bag_inter l₁ l₂
#align list.bag_inter List.bagInterₓ

protected def diff {α} [DecidableEq α] : List α → List α → List α
  | l, [] => l
  | l₁, a :: l₂ => if a ∈ l₁ then diff (l₁.eraseₓ a) l₂ else diff l₁ l₂
#align list.diff List.diffₓ

#print List.length /-
@[simp]
def length : List α → Nat
  | [] => 0
  | a :: l => length l + 1
#align list.length List.length
-/

#print List.isEmpty /-
def isEmpty : List α → Bool
  | [] => true
  | _ :: _ => false
#align list.empty List.isEmpty
-/

open Option Nat

#print List.get? /-
@[simp]
def get? : List α → Nat → Option α
  | [], n => none
  | a :: l, 0 => some a
  | a :: l, n + 1 => nth l n
#align list.nth List.get?
-/

#print List.nthLe /-
@[simp]
def nthLe : ∀ (l : List α) (n), n < l.length → α
  | [], n, h => absurd h n.not_lt_zero
  | a :: l, 0, h => a
  | a :: l, n + 1, h => nth_le l n (le_of_succ_le_succ h)
#align list.nth_le List.nthLe
-/

#print List.headI /-
@[simp]
def headI [Inhabited α] : List α → α
  | [] => default
  | a :: l => a
#align list.head List.headI
-/

#print List.tail /-
@[simp]
def tail : List α → List α
  | [] => []
  | a :: l => l
#align list.tail List.tail
-/

#print List.reverseAux /-
def reverseAux : List α → List α → List α
  | [], r => r
  | a :: l, r => reverse_core l (a :: r)
#align list.reverse_core List.reverseAux
-/

#print List.reverse /-
def reverse : List α → List α := fun l => reverseAux l []
#align list.reverse List.reverse
-/

#print List.map /-
@[simp]
def map (f : α → β) : List α → List β
  | [] => []
  | a :: l => f a :: map l
#align list.map List.map
-/

#print List.zipWith /-
@[simp]
def zipWith (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => f x y :: map₂ xs ys
#align list.map₂ List.zipWith
-/

def mapWithIndexCore (f : ℕ → α → β) : ℕ → List α → List β
  | k, [] => []
  | k, a :: as => f k a :: map_with_index_core (k + 1) as
#align list.map_with_index_core List.mapWithIndexCore

#print List.mapIdx /-
/-- Given a function `f : ℕ → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
def mapIdx (f : ℕ → α → β) (as : List α) : List β :=
  mapWithIndexCore f 0 as
#align list.map_with_index List.mapIdx
-/

#print List.join /-
def join : List (List α) → List α
  | [] => []
  | l :: ls => l ++ join ls
#align list.join List.join
-/

#print List.filterMap /-
def filterMap (f : α → Option β) : List α → List β
  | [] => []
  | a :: l =>
    match f a with
    | none => filter_map l
    | some b => b :: filter_map l
#align list.filter_map List.filterMap
-/

def filter (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | a :: l => if p a then a :: Filter l else Filter l
#align list.filter List.filterₓ

def partition (p : α → Prop) [DecidablePred p] : List α → List α × List α
  | [] => ([], [])
  | a :: l =>
    let (l₁, l₂) := partition l
    if p a then (a :: l₁, l₂) else (l₁, a :: l₂)
#align list.partition List.partitionₓ

def dropWhile (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | a :: l => if p a then drop_while l else a :: l
#align list.drop_while List.dropWhileₓ

/-- `after p xs` is the suffix of `xs` after the first element that satisfies
  `p`, not including that element.

  ```lean
  after      (eq 1)       [0, 1, 2, 3] = [2, 3]
  drop_while (not ∘ eq 1) [0, 1, 2, 3] = [1, 2, 3]
  ```
-/
def after (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | x :: xs => if p x then xs else after xs
#align list.after List.afterₓ

def span (p : α → Prop) [DecidablePred p] : List α → List α × List α
  | [] => ([], [])
  | a :: xs =>
    if p a then
      let (l, r) := span xs
      (a :: l, r)
    else ([], a :: xs)
#align list.span List.spanₓ

#print List.findIndex /-
def findIndex (p : α → Prop) [DecidablePred p] : List α → Nat
  | [] => 0
  | a :: l => if p a then 0 else succ (find_index l)
#align list.find_index List.findIndex
-/

def indexOf [DecidableEq α] (a : α) : List α → Nat :=
  findIndex (Eq a)
#align list.index_of List.indexOfₓ

def removeAll [DecidableEq α] (xs ys : List α) : List α :=
  filter (· ∉ ys) xs
#align list.remove_all List.removeAllₓ

#print List.set /-
def set : List α → ℕ → α → List α
  | x :: xs, 0, a => a :: xs
  | x :: xs, i + 1, a => x :: update_nth xs i a
  | [], _, _ => []
#align list.update_nth List.set
-/

#print List.removeNth /-
def removeNth : List α → ℕ → List α
  | [], _ => []
  | x :: xs, 0 => xs
  | x :: xs, i + 1 => x :: remove_nth xs i
#align list.remove_nth List.removeNth
-/

#print List.drop /-
@[simp]
def drop : ℕ → List α → List α
  | 0, a => a
  | succ n, [] => []
  | succ n, x :: r => drop n r
#align list.drop List.drop
-/

#print List.take /-
@[simp]
def take : ℕ → List α → List α
  | 0, a => []
  | succ n, [] => []
  | succ n, x :: r => x :: take n r
#align list.take List.take
-/

#print List.foldl /-
@[simp]
def foldl (f : α → β → α) : α → List β → α
  | a, [] => a
  | a, b :: l => foldl (f a b) l
#align list.foldl List.foldl
-/

#print List.foldr /-
@[simp]
def foldr (f : α → β → β) (b : β) : List α → β
  | [] => b
  | a :: l => f a (foldr l)
#align list.foldr List.foldr
-/

#print List.any /-
def any (l : List α) (p : α → Bool) : Bool :=
  foldr (fun a r => p a || r) false l
#align list.any List.any
-/

#print List.all /-
def all (l : List α) (p : α → Bool) : Bool :=
  foldr (fun a r => p a && r) true l
#align list.all List.all
-/

#print List.or /-
def or (l : List Bool) : Bool :=
  any l id
#align list.bor List.or
-/

#print List.and /-
def and (l : List Bool) : Bool :=
  all l id
#align list.band List.and
-/

/- warning: list.zip_with clashes with list.map₂ -> List.zipWith
Case conversion may be inaccurate. Consider using '#align list.zip_with List.zipWithₓ'. -/
#print List.zipWith /-
def zipWith (f : α → β → γ) : List α → List β → List γ
  | x :: xs, y :: ys => f x y :: zip_with xs ys
  | _, _ => []
#align list.zip_with List.zipWith
-/

#print List.zip /-
def zip : List α → List β → List (Prod α β) :=
  zipWith Prod.mk
#align list.zip List.zip
-/

#print List.unzip /-
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (a, b) :: t =>
    match unzip t with
    | (al, bl) => (a :: al, b :: bl)
#align list.unzip List.unzip
-/

#print List.insert /-
protected def insert [DecidableEq α] (a : α) (l : List α) : List α :=
  if a ∈ l then l else a :: l
#align list.insert List.insert
-/

instance [DecidableEq α] : Insert α (List α) :=
  ⟨List.insert⟩

instance : Singleton α (List α) :=
  ⟨fun x => [x]⟩

instance [DecidableEq α] : IsLawfulSingleton α (List α) :=
  ⟨fun x => show (if x ∈ ([] : List α) then [] else [x]) = [x] from if_neg not_false⟩

#print List.union /-
protected def union [DecidableEq α] (l₁ l₂ : List α) : List α :=
  foldr insert l₂ l₁
#align list.union List.union
-/

instance [DecidableEq α] : Union (List α) :=
  ⟨List.union⟩

#print List.inter /-
protected def inter [DecidableEq α] (l₁ l₂ : List α) : List α :=
  filter (· ∈ l₂) l₁
#align list.inter List.inter
-/

instance [DecidableEq α] : Inter (List α) :=
  ⟨List.inter⟩

@[simp]
def repeat (a : α) : ℕ → List α
  | 0 => []
  | succ n => a :: repeat n
#align list.repeat List.repeat

#print List.range.loop /-
def List.range.loop : ℕ → List ℕ → List ℕ
  | 0, l => l
  | succ n, l => range_core n (n :: l)
#align list.range_core List.range.loop
-/

#print List.range /-
def range (n : ℕ) : List ℕ :=
  List.range.loop n []
#align list.range List.range
-/

#print List.iota /-
def iota : ℕ → List ℕ
  | 0 => []
  | succ n => succ n :: iota n
#align list.iota List.iota
-/

#print List.enumFrom /-
def enumFrom : ℕ → List α → List (ℕ × α)
  | n, [] => nil
  | n, x :: xs => (n, x) :: enum_from (n + 1) xs
#align list.enum_from List.enumFrom
-/

#print List.enum /-
def enum : List α → List (ℕ × α) :=
  enumFrom 0
#align list.enum List.enum
-/

#print List.getLast /-
@[simp]
def getLast : ∀ l : List α, l ≠ [] → α
  | [], h => absurd rfl h
  | [a], h => a
  | a :: b :: l, h => last (b :: l) fun h => List.noConfusion h
#align list.last List.getLast
-/

#print List.getLastI /-
def getLastI [Inhabited α] : List α → α
  | [] => Inhabited.default α
  | [a] => a
  | [a, b] => b
  | a :: b :: l => ilast l
#align list.ilast List.getLastI
-/

#print List.dropLast /-
def dropLast : List α → List α
  | [] => []
  | [a] => []
  | a :: l => a :: init l
#align list.init List.dropLast
-/

#print List.intersperse /-
def intersperse (sep : α) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: xs => x :: sep :: intersperse xs
#align list.intersperse List.intersperse
-/

#print List.intercalate /-
def intercalate (sep : List α) (xs : List (List α)) : List α :=
  join (intersperse sep xs)
#align list.intercalate List.intercalate
-/

#print List.bind /-
@[inline]
protected def bind {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β :=
  join (map b a)
#align list.bind List.bind
-/

#print List.ret /-
@[inline]
protected def ret {α : Type u} (a : α) : List α :=
  [a]
#align list.ret List.ret
-/

#print List.lt /-
protected def lt [LT α] : List α → List α → Prop
  | [], [] => False
  | [], b :: bs => True
  | a :: as, [] => False
  | a :: as, b :: bs => a < b ∨ ¬b < a ∧ lt as bs
#align list.lt List.lt
-/

instance [LT α] : LT (List α) :=
  ⟨List.lt⟩

#print List.hasDecidableLt /-
instance hasDecidableLt [LT α] [h : DecidableRel ((· < ·) : α → α → Prop)] :
    ∀ l₁ l₂ : List α, Decidable (l₁ < l₂)
  | [], [] => isFalse not_false
  | [], b :: bs => isTrue trivial
  | a :: as, [] => isFalse not_false
  | a :: as, b :: bs =>
    match h a b with
    | is_true h₁ => isTrue (Or.inl h₁)
    | is_false h₁ =>
      match h b a with
      | is_true h₂ => isFalse fun h => Or.elim h (fun h => absurd h h₁) fun ⟨h, _⟩ => absurd h₂ h
      | is_false h₂ =>
        match has_decidable_lt as bs with
        | is_true h₃ => isTrue (Or.inr ⟨h₂, h₃⟩)
        | is_false h₃ => isFalse fun h => Or.elim h (fun h => absurd h h₁) fun ⟨_, h⟩ => absurd h h₃
#align list.has_decidable_lt List.hasDecidableLt
-/

@[reducible]
protected def Le [LT α] (a b : List α) : Prop :=
  ¬b < a
#align list.le List.Le

instance [LT α] : LE (List α) :=
  ⟨List.Le⟩

instance hasDecidableLe [LT α] [h : DecidableRel ((· < ·) : α → α → Prop)] :
    ∀ l₁ l₂ : List α, Decidable (l₁ ≤ l₂) := fun a b => Not.decidable
#align list.has_decidable_le List.hasDecidableLe

#print List.le_eq_not_gt /-
theorem le_eq_not_gt [LT α] : ∀ l₁ l₂ : List α, (l₁ ≤ l₂) = ¬l₂ < l₁ := fun l₁ l₂ => rfl
#align list.le_eq_not_gt List.le_eq_not_gt
-/

theorem lt_eq_not_ge [LT α] [DecidableRel ((· < ·) : α → α → Prop)] :
    ∀ l₁ l₂ : List α, (l₁ < l₂) = ¬l₂ ≤ l₁ := fun l₁ l₂ =>
  show (l₁ < l₂) = ¬¬l₁ < l₂ from Eq.subst (propext (not_not_iff (l₁ < l₂))).symm rfl
#align list.lt_eq_not_ge List.lt_eq_not_ge

/-- `is_prefix_of l₁ l₂` returns `tt` iff `l₁` is a prefix of `l₂`. -/
def isPrefixOf [DecidableEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => decide (a = b) && is_prefix_of as bs
#align list.is_prefix_of List.isPrefixOfₓ

/-- `is_suffix_of l₁ l₂` returns `tt` iff `l₁` is a suffix of `l₂`. -/
def isSuffixOf [DecidableEq α] (l₁ l₂ : List α) : Bool :=
  isPrefixOf l₁.reverse l₂.reverse
#align list.is_suffix_of List.isSuffixOfₓ

end List

namespace BinTree

private def to_list_aux : BinTree α → List α → List α
  | Empty, as => as
  | leaf a, as => a :: as
  | node l r, as => to_list_aux l (to_list_aux r as)

def toList (t : BinTree α) : List α :=
  toListAux t []
#align bin_tree.to_list BinTree.toList

end BinTree

