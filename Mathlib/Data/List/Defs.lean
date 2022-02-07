/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Lean
import Mathlib.Init.Data.List.Instances
import Mathlib.Init.Data.Nat.Basic

/-!
## Definitions on Lists

This file contains various definitions on `List`. It does not contain
proofs about these definitions, those are contained in other files in `Mathlib.Data.List`.
-/

namespace List

/-- Split a list at an index.
```
splitAt 2 [a, b, c] = ([a, b], [c])
``` -/
def splitAt : ℕ → List α → List α × List α
| n+1, x :: xs => let (l, r) := splitAt n xs; (x :: l, r)
| _, xs => ([], xs)

/-- Split a list at an index. Ensures the left list always has the specified length
by right padding with the provided default element.
```
splitAtD 2 [a, b, c] x = ([a, b], [c])
splitAtD 4 [a, b, c] x = ([a, b, c, x], [])
``` -/
def splitAtD : ℕ → List α → α → List α × List α
| 0, xs, a => ([], xs)
| n+1, [], a => let (l, r) := splitAtD n [] a; (a :: l, r)
| n+1, x :: xs, a => let (l, r) := splitAtD n xs a; (x :: l, r)

/-- An auxiliary function for `splitOnP`. -/
def splitOnPAux {α : Type u} (P : α → Prop) [DecidablePred P] : List α → (List α → List α) → List (List α)
| [], f => [f []]
| h :: t, f => if P h then f [] :: splitOnPAux P t id else splitOnPAux P t fun l => f (h :: l)

/-- Split a list at every element satisfying a predicate. -/
def splitOnP {α : Type u} (P : α → Prop) [DecidablePred P] (l : List α) : List (List α) :=
  splitOnPAux P l id

/-- Split a list at every occurrence of an element.
```
[1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]]
``` -/
def splitOn {α : Type u} [DecidableEq α] (a : α) (as : List α) : List (List α) :=
  as.splitOnP (· = a)

/-- Apply a function to the nth tail of `l`. Returns the input without
  using `f` if the index is larger than the length of the List.
```
modifyNthTail f 2 [a, b, c] = [a, b] ++ f [c]
``` -/
@[simp]
def modifyNthTail (f : List α → List α) : ℕ → List α → List α
| 0, l => f l
| n+1, [] => []
| n+1, a :: l => a :: modifyNthTail f n l

/-- Apply `f` to the head of the list, if it exists. -/
@[simp]
def modifyHead (f : α → α) : List α → List α
| [] => []
| a :: l => f a :: l

/-- Apply `f` to the nth element of the list, if it exists. -/
def modifyNth (f : α → α) : ℕ → List α → List α :=
  modifyNthTail (modifyHead f)

/-- Apply `f` to the last element of `l`, if it exists. -/
@[simp]
def modifyLast (f : α → α) : List α → List α
| [] => []
| [x] => [f x]
| x :: xs => x :: modifyLast f xs

/-- `insertNth n a l` inserts `a` into the list `l` after the first `n` elements of `l`
```
insertNth 2 1 [1, 2, 3, 4] = [1, 2, 1, 3, 4]
``` -/
def insertNth (n : ℕ) (a : α) : List α → List α :=
  modifyNthTail (cons a) n

/-- Take `n` elements from a list `l`. If `l` has less than `n` elements, append `n - length l`
elements `x`. -/
def takeD : ∀ n : ℕ, List α → α → List α
| 0, l, _ => []
| n+1, l, x => l.headD x :: takeD n l.tail x

/-- Fold a function `f` over the list from the left, returning the list
  of partial results.
```
scanl (+) 0 [1, 2, 3] = [0, 1, 3, 6]
``` -/
def scanl (f : α → β → α) : α → List β → List α
| a, [] => [a]
| a, b :: l => a :: scanl f (f a b) l

/-- Auxiliary definition used to define `scanr`. If `scanrAux f b l = (b', l')`
then `scanr f b l = b' :: l'` -/
def scanrAux (f : α → β → β) (b : β) : List α → β × List β
| [] => (b, [])
| a :: l =>
  let (b', l') := scanrAux f b l
  (f a b', b' :: l')

/-- Fold a function `f` over the list from the right, returning the list of partial results.
```
scanr (+) 0 [1, 2, 3] = [6, 5, 3, 0]
``` -/
def scanr (f : α → β → β) (b : β) (l : List α) : List β :=
  let (b', l') := scanrAux f b l
  b' :: l'

/-- Given a function `f : α → β ⊕ γ`, `partitionMap f l` maps the list by `f`
  whilst partitioning the result it into a pair of lists, `list β × list γ`,
  partitioning the `sum.inl _` into the left list, and the `sum.inr _` into the right List.
  `partitionMap (id : ℕ ⊕ ℕ → ℕ ⊕ ℕ) [inl 0, inr 1, inl 2] = ([0,2], [1])`    -/
def partitionMap (f : α → β ⊕ γ) : List α → List β × List γ
| [] => ([], [])
| x :: xs =>
  match f x with
  | Sum.inr r => Prod.map id (cons r) $ partitionMap f xs
  | Sum.inl l => Prod.map (cons l) id $ partitionMap f xs

/-- `find p l` is the first element of `l` satisfying `p`, or `none` if no such
  element exists. -/
def find (p : α → Prop) [DecidablePred p] : List α → Option α
| [] => none
| a :: l => if p a then some a else find p l

/-- Auxiliary definition for `foldlIdx`. -/
def foldlIdxAux (f : ℕ → α → β → α) : ℕ → α → List β → α
| _, a, [] => a
| i, a, b :: l => foldlIdxAux f (i+1) (f i a b) l

/-- Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index. -/
def foldlIdx (f : ℕ → α → β → α) (a : α) (l : List β) : α :=
  foldlIdxAux f 0 a l

/-- Auxiliary definition for `foldrIdx`. -/
def foldrIdxAux (f : ℕ → α → β → β) : ℕ → β → List α → β
| _, b, [] => b
| i, b, a :: l => f i a (foldrIdxAux f (i+1) b l)

/-- Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index. -/
def foldrIdx (f : ℕ → α → β → β) (b : β) (l : List α) : β :=
  foldrIdxAux f 0 b l

/-- `findIdxs p l` is the list of indexes of elements of `l` that satisfy `p`. -/
def findIdxs (p : α → Prop) [DecidablePred p] (l : List α) : List Nat :=
  foldrIdx (fun i a is => if p a then i :: is else is) [] l

/-- Returns the elements of `l` that satisfy `p` together with their indexes in
`l`. The returned list is ordered by index. -/
def indexesValues (p : α → Prop) [DecidablePred p] (l : List α) : List (ℕ × α) :=
  foldrIdx (fun i a l => if p a then (i, a) :: l else l) [] l

/-- `indexesOf a l` is the list of all indexes of `a` in `l`. For example:

    indexesOf a [a, b, a, a] = [0, 2, 3] -/
def indexesOf [DecidableEq α] (a : α) : List α → List Nat :=
  findIdxs (Eq a)

/-- `lookmap` is a combination of `lookup` and `filterMap`.
  `lookmap f l` will apply `f : α → option α` to each element of the list,
  replacing `a → b` at the first value `a` in the list such that `f a = some b`. -/
def lookmap (f : α → Option α) : List α → List α
| [] => []
| a :: l =>
  match f a with
  | some b => b :: l
  | none => a :: lookmap f l

/-- `countp p l` is the number of elements of `l` that satisfy `p`. -/
def countp (p : α → Prop) [DecidablePred p] : List α → Nat
| [] => 0
| x :: xs => if p x then countp p xs + 1 else countp p xs

/-- `count a l` is the number of occurrences of `a` in `l`. -/
def count [DecidableEq α] (a : α) : List α → Nat :=
  countp (Eq a)

/-- `isPrefix l₁ l₂`, or `l₁ <+: l₂`, means that `l₁` is a prefix of `l₂`,
  that is, `l₂` has the form `l₁ ++ t` for some `t`. -/
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

/-- `isSuffix l₁ l₂`, or `l₁ <:+ l₂`, means that `l₁` is a suffix of `l₂`,
  that is, `l₂` has the form `t ++ l₁` for some `t`. -/
def isSuffix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, t ++ l₁ = l₂

/-- `isInfix l₁ l₂`, or `l₁ <:+: l₂`, means that `l₁` is a contiguous
  substring of `l₂`, that is, `l₂` has the form `s ++ l₁ ++ t` for some `s, t`. -/
def isInfix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ s t, s ++ l₁ ++ t = l₂

infixl:50 " <+: " => isPrefix

infixl:50 " <:+ " => isSuffix

infixl:50 " <:+: " => isInfix

/-- `inits l` is the list of initial segments of `l`.
```
inits [1, 2, 3] = [[], [1], [1, 2], [1, 2, 3]]
``` -/
@[simp] def inits : List α → List (List α)
| [] => [[]]
| a :: l => [] :: map (fun t => a :: t) (inits l)

/-- `tails l` is the list of terminal segments of `l`.
```
tails [1, 2, 3] = [[1, 2, 3], [2, 3], [3], []]
``` -/
@[simp] def tails : List α → List (List α)
| [] => [[]]
| a :: l => (a :: l) :: tails l

def sublists'Aux : List α → (List α → List β) → List (List β) → List (List β)
| [], f, r => f [] :: r
| a :: l, f, r => sublists'Aux l f (sublists'Aux l (f ∘ cons a) r)

/-- `sublists' l` is the list of all (non-contiguous) sublists of `l`.
  It differs from `sublists` only in the order of appearance of the sublists;
  `sublists'` uses the first element of the list as the MSB,
  `sublists` uses the first element of the list as the LSB.
```
sublists' [1, 2, 3] = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]]
``` -/
def sublists' (l : List α) : List (List α) :=
  sublists'Aux l id []

def sublistsAux : List α → (List α → List β → List β) → List β
| [], f => []
| a :: l, f => f [a] (sublistsAux l fun ys r => f ys (f (a :: ys) r))

/-- `sublists l` is the list of all (non-contiguous) sublists of `l`; cf. `sublists'`
  for a different ordering.
```
sublists [1, 2, 3] = [[], [1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]]
``` -/
def sublists (l : List α) : List (List α) :=
  [] :: sublistsAux l cons

def sublistsAux₁ : List α → (List α → List β) → List β
| [], f => []
| a :: l, f => f [a] ++ sublistsAux₁ l fun ys => f ys ++ f (a :: ys)

section Forall₂

variable {r : α → β → Prop} {p : γ → δ → Prop}

/-- `Forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length,
  and whenever `a` is the nth element of `l₁`, and `b` is the nth element of `l₂`,
  then `R a b` is satisfied. -/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {a b l₁ l₂} : R a b → Forall₂ R l₁ l₂ → Forall₂ R (a :: l₁) (b :: l₂)

attribute [simp] Forall₂.nil

end Forall₂

/-- Auxiliary definition used to define `transpose`.
  `transposeAux l L` takes each element of `l` and appends it to the start of
  each element of `L`.
  `transposeAux [a, b, c] [l₁, l₂, l₃] = [a::l₁, b::l₂, c::l₃]` -/
def transposeAux : List α → List (List α) → List (List α)
| [], ls => ls
| a :: i, [] => [a] :: transposeAux i []
| a :: i, l :: ls => (a :: l) :: transposeAux i ls

/-- transpose of a list of lists, treated as a matrix.
```
transpose [[1, 2], [3, 4], [5, 6]] = [[1, 3, 5], [2, 4, 6]]
``` -/
def transpose : List (List α) → List (List α)
| [] => []
| l :: ls => transposeAux l (transpose ls)

/-- List of all sections through a list of lists. A section
  of `[L₁, L₂, ..., Lₙ]` is a list whose first element comes from
  `L₁`, whose second element comes from `L₂`, and so on. -/
def sections : List (List α) → List (List α)
| [] => [[]]
| l :: L => (sections L).bind fun s => l.map fun a => a :: s

/-- `erasep p l` removes the first element of `l` satisfying the predicate `p`. -/
def erasep (p : α → Prop) [DecidablePred p] : List α → List α
| [] => []
| a :: l => if p a then l else a :: erasep p l

/-- `extractp p l` returns a pair of an element `a` of `l` satisfying the predicate
  `p`, and `l`, with `a` removed. If there is no such element `a` it returns `(none, l)`. -/
def extractp (p : α → Prop) [DecidablePred p] : List α → Option α × List α
| [] => (none, [])
| a :: l =>
  if p a then (some a, l) else
    let (a', l') := extractp p l
    (a', a :: l')

/-- `revzip l` returns a list of pairs of the elements of `l` paired
  with the elements of `l` in reverse order.
```
revzip [1,2,3,4,5] = [(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)]
``` -/
def revzip (l : List α) : List (α × α) :=
  zip l l.reverse

/-- `product l₁ l₂` is the list of pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂`.
```
product [1, 2] [5, 6] = [(1, 5), (1, 6), (2, 5), (2, 6)]
``` -/
def product (l₁ : List α) (l₂ : List β) : List (α × β) :=
  l₁.bind $ fun a => l₂.map $ Prod.mk a

/-- `sigma l₁ l₂` is the list of dependent pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂ a`.
```
sigma [1, 2] (λ_, [(5 : ℕ), 6]) = [(1, 5), (1, 6), (2, 5), (2, 6)]
``` -/
protected def sigma {σ : α → Type _} (l₁ : List α) (l₂ : ∀ a, List (σ a)) : List (Σ a, σ a) :=
  l₁.bind $ fun a => (l₂ a).map $ Sigma.mk a

/-- Auxliary definition used to define `ofFn`.
  `ofFnAux f m h l` returns the first `m` elements of `ofFn f`
  appended to `l` -/
def ofFnAux {n} (f : Fin n → α) : ∀ m, m ≤ n → List α → List α
| 0, h, l => l
| m+1, h, l => ofFnAux f m (Nat.le_of_lt h) (f ⟨m, h⟩ :: l)

/-- `ofFn f` with `f : fin n → α` returns the list whose ith element is `f i`
```
ofFn f = [f 0, f 1, ... , f(n - 1)]
``` -/
def ofFn {n} (f : Fin n → α) : List α :=
  ofFnAux f n (Nat.le_refl _) []

/-- `ofFnNthVal f i` returns `some (f i)` if `i < n` and `none` otherwise. -/
def ofFnNthVal {n} (f : Fin n → α) (i : ℕ) : Option α :=
  if h : i < n then some (f ⟨i, h⟩) else none

/-- `disjoint l₁ l₂` means that `l₁` and `l₂` have no elements in common. -/
def disjoint (l₁ l₂ : List α) : Prop :=
  ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False

section Pairwise

variable (R : α → α → Prop)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a' «expr ∈ » l)
/-- `Pairwise R l` means that all the elements with earlier indexes are
  `R`-related to all the elements with later indexes.
     Pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
  For example if `R = (≠)` then it asserts `l` has no duplicates,
  and if `R = (<)` then it asserts that `l` is (strictly) sorted. -/
inductive Pairwise : List α → Prop
  | nil : Pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, R a a') → Pairwise l → Pairwise (a :: l)

end Pairwise

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » IH)
/-- `pwFilter R l` is a maximal sublist of `l` which is `Pairwise R`.
  `pwFilter (≠)` is the erase duplicates function (cf. `eraseDup`), and `pwFilter (<)` finds
  a maximal increasing subsequence in `l`. For example,
     pwFilter (<) [0, 1, 5, 2, 6, 3, 4] = [0, 1, 2, 3, 4] -/
def pwFilter (R : α → α → Prop) [DecidableRel R] : List α → List α
| [] => []
| x :: xs =>
  let IH := pwFilter R xs
  if ∀ y ∈ IH, R x y then x :: IH else IH

section Chain

variable (R : α → α → Prop)

/-- `Chain R a l` means that `R` holds between adjacent elements of `a::l`.
```
Chain R a [b, c, d] ↔ R a b ∧ R b c ∧ R c d
``` -/
inductive Chain : α → List α → Prop
  | nil {a : α} : Chain a []
  | cons : ∀ {a b : α} {l : List α}, R a b → Chain b l → Chain a (b :: l)

/-- `Chain' R l` means that `R` holds between adjacent elements of `l`.
```
Chain' R [a, b, c, d] ↔ R a b ∧ R b c ∧ R c d
``` -/
def Chain' : List α → Prop
| [] => True
| a :: l => Chain R a l

end Chain

/-- `Nodup l` means that `l` has no duplicates, that is, any element appears at most
  once in the List. It is defined as `Pairwise (≠)`. -/
def Nodup : List α → Prop :=
  Pairwise (· ≠ ·)

/-- `eraseDup l` removes duplicates from `l` (taking only the first occurrence).
  Defined as `pwFilter (≠)`.

    eraseDup [1, 0, 2, 2, 1] = [0, 2, 1] -/
def eraseDup [DecidableEq α] : List α → List α :=
  pwFilter (· ≠ ·)

/-- `range' s n` is the list of numbers `[s, s+1, ..., s+n-1]`.
  It is intended mainly for proving properties of `range` and `iota`. -/
@[simp]
def range' : ℕ → ℕ → List ℕ
| s, 0 => []
| s, n+1 => s :: range' (s+1) n

/-- Drop `none`s from a list, and replace each remaining `some a` with `a`. -/
def reduceOption {α} : List (Option α) → List α :=
  List.filterMap id

/-- `ilast' x xs` returns the last element of `xs` if `xs` is non-empty;
it returns `x` otherwise -/
@[simp]
def ilast' {α} : α → List α → α
| a, [] => a
| a, b :: l => ilast' b l

/-- `last' xs` returns the last element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp]
def last' {α} : List α → Option α
| [] => none
| [a] => some a
| b :: l => last' l

/-- `rotate l n` rotates the elements of `l` to the left by `n`
```
rotate [0, 1, 2, 3, 4, 5] 2 = [2, 3, 4, 5, 0, 1]
``` -/
def rotate (l : List α) (n : ℕ) : List α :=
  let (l₁, l₂) := List.splitAt (n % l.length) l
  l₂ ++ l₁

/-- rotate' is the same as `rotate`, but slower. Used for proofs about `rotate`-/
def rotate' : List α → ℕ → List α
| [], n => []
| l, 0 => l
| a :: l, n+1 => rotate' (l ++ [a]) n

def mmap {m : Type u → Type v} [Monad m] {α β} (f : α → m β) : List α → m (List β)
| [] => pure []
| h :: t => return (← f h) :: (← mmap f t)

def mmap' {m : Type → Type v} [Monad m] {α β} (f : α → m β) : List α → m Unit
| [] => pure ()
| h :: t => f h *> t.mmap' f

/-- Filters and maps elements of a list -/
def mmapFilter {m : Type → Type v} [Monad m] {α β} (f : α → m (Option β)) : List α → m (List β)
| [] => pure []
| h :: t => do
  let b ← f h
  let t' ← t.mmapFilter f
  pure $ match b with
  | none => t'
  | some x => x :: t'

/--
`mmapUpperTriangle f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.
```
mmapUpperTriangle f [1, 2, 3] =
  return [← f 1 1, ← f 1 2, ← f 1 3, ← f 2 2, ← f 2 3, ← f 3 3]
``` -/
def mmapUpperTriangle {m} [Monad m] {α β : Type u} (f : α → α → m β) : List α → m (List β)
| [] => pure []
| h :: t => return (← f h h) :: (← t.mmap (f h)) ++ (← t.mmapUpperTriangle f)

/--
`mmap'Diag f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.
```
mmap'Diag f [1, 2, 3] = do f 1 1; f 1 2; f 1 3; f 2 2; f 2 3; f 3 3
``` -/
def mmap'Diag {m} [Monad m] {α} (f : α → α → m Unit) : List α → m Unit
| [] => return ()
| h :: t => do f h h; t.mmap' (f h); t.mmap'Diag f

protected def traverse {F : Type u → Type v} [Applicative F] {α β} (f : α → F β) : List α → F (List β)
| [] => pure []
| x :: xs => cons <$> f x <*> List.traverse f xs

/-- `getRest l l₁` returns `some l₂` if `l = l₁ ++ l₂`.
  If `l₁` is not a prefix of `l`, returns `none` -/
def getRest [DecidableEq α] : List α → List α → Option (List α)
| l, [] => some l
| [], _ => none
| x :: l, y :: l₁ => if x = y then getRest l l₁ else none

/--
`List.slice n m xs` removes a slice of length `m` at index `n` in list `xs`.
-/
def slice {α} : ℕ → ℕ → List α → List α
| 0, n, xs => xs.drop n
| n+1, m, [] => []
| n+1, m, x :: xs => x :: slice n m xs

/--
Left-biased version of `List.map₂`. `map₂Left' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.
```
map₂Left' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])
map₂Left' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
@[simp]
def map₂Left' (f : α → Option β → γ) : List α → List β → List γ × List β
| [], bs => ([], bs)
| a :: as, [] => ((a :: as).map fun a => f a none, [])
| a :: as, b :: bs => let r := map₂Left' f as bs; (f a (some b) :: r.1, r.2)

/--
Right-biased version of `List.map₂`. `map₂Right' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.
```
map₂Right' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])
map₂Right' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
def map₂Right' (f : Option α → β → γ) (as : List α) (bs : List β) : List γ × List α :=
  map₂Left' (flip f) bs as

/--
Left-biased version of `List.zip`. `zipLeft' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`. Also returns the remaining `bs`.
```
zipLeft' [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])
zipLeft' [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
zipLeft' = map₂Left' prod.mk
```
-/
def zipLeft' : List α → List β → List (α × Option β) × List β :=
  map₂Left' Prod.mk

/--
Right-biased version of `List.zip`. `zipRight' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`. Also returns the remaining `as`.
```
zipRight' [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])
zipRight' [1, 2] ['a'] = ([(some 1, 'a')], [2])
zipRight' = map₂Right' prod.mk
```
-/
def zipRight' : List α → List β → List (Option α × β) × List α :=
  map₂Right' Prod.mk

/--
Left-biased version of `List.map₂`. `map₂Left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.
```
map₂Left prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]
map₂Left prod.mk [1] ['a', 'b'] = [(1, some 'a')]
map₂Left f as bs = (map₂Left' f as bs).fst
```
-/
@[simp]
def map₂Left (f : α → Option β → γ) : List α → List β → List γ
| [], _ => []
| a :: as, [] => (a :: as).map fun a => f a none
| a :: as, b :: bs => f a (some b) :: map₂Left f as bs

/--
Right-biased version of `List.map₂`. `map₂Right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.
```
map₂Right prod.mk [1, 2] ['a'] = [(some 1, 'a')]
map₂Right prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]
map₂Right f as bs = (map₂Right' f as bs).fst
```
-/
def map₂Right (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  map₂Left (flip f) bs as

/--
Left-biased version of `List.zip`. `zipLeft as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`.
```
zipLeft [1, 2] ['a'] = [(1, some 'a'), (2, none)]
zipLeft [1] ['a', 'b'] = [(1, some 'a')]
zipLeft = map₂Left prod.mk
```
-/
def zipLeft : List α → List β → List (α × Option β) :=
  map₂Left Prod.mk

/--
Right-biased version of `List.zip`. `zipRight as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`.
```
zipRight [1, 2] ['a'] = [(some 1, 'a')]
zipRight [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]
zipRight = map₂Right prod.mk
```
-/
def zipRight : List α → List β → List (Option α × β) :=
  map₂Right Prod.mk

/--
If all elements of `xs` are `some xᵢ`, `allSome xs` returns the `xᵢ`. Otherwise
it returns `none`.
```
allSome [some 1, some 2] = some [1, 2]
allSome [some 1, none  ] = none
```
-/
def allSome : List (Option α) → Option (List α)
| [] => some []
| some a :: as => cons a <$> allSome as
| none :: as => none

/--
`fillNones xs ys` replaces the `none`s in `xs` with elements of `ys`. If there
are not enough `ys` to replace all the `none`s, the remaining `none`s are
dropped from `xs`.
```
fillNones [none, some 1, none, none] [2, 3] = [2, 1, 3]
```
-/
def fillNones {α} : List (Option α) → List α → List α
| [], _ => []
| some a :: as, as' => a :: fillNones as as'
| none :: as, [] => as.reduceOption
| none :: as, a :: as' => a :: fillNones as as'

/--
`takeList as ns` extracts successive sublists from `as`. For `ns = n₁ ... nₘ`,
it first takes the `n₁` initial elements from `as`, then the next `n₂` ones,
etc. It returns the sublists of `as` -- one for each `nᵢ` -- and the remaining
elements of `as`. If `as` does not have at least as many elements as the sum of
the `nᵢ`, the corresponding sublists will have less than `nᵢ` elements.
```
takeList ['a', 'b', 'c', 'd', 'e'] [2, 1, 1] = ([['a', 'b'], ['c'], ['d']], ['e'])
takeList ['a', 'b'] [3, 1] = ([['a', 'b'], []], [])
```
-/
def takeList {α} : List α → List ℕ → List (List α) × List α
| xs, [] => ([], xs)
| xs, n :: ns =>
  let ⟨xs₁, xs₂⟩ := xs.splitAt n
  let ⟨xss, rest⟩ := takeList xs₂ ns
  (xs₁ :: xss, rest)

/-- Auxliary definition used to define `toChunks`.
  `toChunksAux n xs i` returns `(xs.take i, (xs.drop i).toChunks (n+1))`,
  that is, the first `i` elements of `xs`, and the remaining elements chunked into
  sublists of length `n+1`. -/
def toChunksAux {α} (n : ℕ) : List α → ℕ → List α × List (List α)
| [], i => ([], [])
| x :: xs, 0 =>
  let (l, L) := toChunksAux n xs n
  ([], (x :: l) :: L)
| x :: xs, i+1 =>
  let (l, L) := toChunksAux n xs i
  (x :: l, L)

/--
`xs.toChunks n` splits the list into sublists of size at most `n`,
such that `(xs.toChunks n).join = xs`.
```
[1, 2, 3, 4, 5, 6, 7, 8].toChunks 10 = [[1, 2, 3, 4, 5, 6, 7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].toChunks 3 = [[1, 2, 3], [4, 5, 6], [7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].toChunks 2 = [[1, 2], [3, 4], [5, 6], [7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].toChunks 0 = [[1, 2, 3, 4, 5, 6, 7, 8]]
```
-/
def toChunks {α} : ℕ → List α → List (List α)
| _, [] => []
| 0, xs => [xs]
| n+1, x :: xs =>
  let (l, L) := toChunksAux n xs n
  (x :: l) :: L

/-!
We add some n-ary versions of `List.zipWith` for functions with more than two arguments.
These can also be written in terms of `List.zip` or `List.zipWith`.
For example, `zipWith₃ f xs ys zs` could also be written as
`zipWith id (zipWith f xs ys) zs`
or as
`(zip xs $ zip ys zs).map $ λ ⟨x, y, z⟩, f x y z`.
-/


/-- Ternary version of `List.zipWith`. -/
def zipWith₃ (f : α → β → γ → δ) : List α → List β → List γ → List δ
| x :: xs, y :: ys, z :: zs => f x y z :: zipWith₃ f xs ys zs
| _, _, _ => []

/-- Quaternary version of `List.zipWith`. -/
def zipWith₄ (f : α → β → γ → δ → ε) : List α → List β → List γ → List δ → List ε
| x :: xs, y :: ys, z :: zs, u :: us => f x y z u :: zipWith₄ f xs ys zs us
| _, _, _, _ => []

/-- Quinary version of `List.zipWith`. -/
def zipWith₅ (f : α → β → γ → δ → ε → ζ) : List α → List β → List γ → List δ → List ε → List ζ
| x :: xs, y :: ys, z :: zs, u :: us, v :: vs => f x y z u v :: zipWith₅ f xs ys zs us vs
| _, _, _, _, _ => []

/-- An auxiliary function for `List.mapWithPrefixSuffix`. -/
def mapWithPrefixSuffixAux {α β} (f : List α → α → List α → β) : List α → List α → List β
| prev, [] => []
| prev, h :: t => f prev h t :: mapWithPrefixSuffixAux f (prev.concat h) t

/--
`List.mapWithPrefixSuffix f l` maps `f` across a list `l`.
For each `a ∈ l` with `l = pref ++ [a] ++ suff`, `a` is mapped to `f pref a suff`.
Example: if `f : list ℕ → ℕ → list ℕ → β`,
`List.mapWithPrefixSuffix f [1, 2, 3]` will produce the list
`[f [] 1 [2, 3], f [1] 2 [3], f [1, 2] 3 []]`.
-/
def mapWithPrefixSuffix {α β} (f : List α → α → List α → β) (l : List α) : List β :=
  mapWithPrefixSuffixAux f [] l

/--
`List.mapWithComplement f l` is a variant of `List.mapWithPrefixSuffix`
that maps `f` across a list `l`.
For each `a ∈ l` with `l = pref ++ [a] ++ suff`, `a` is mapped to `f a (pref ++ suff)`,
i.e., the list input to `f` is `l` with `a` removed.
Example: if `f : ℕ → list ℕ → β`, `List.mapWithComplement f [1, 2, 3]` will produce the list
`[f 1 [2, 3], f 2 [1, 3], f 3 [1, 2]]`.
-/
def mapWithComplement {α β} (f : α → List α → β) : List α → List β :=
  mapWithPrefixSuffix fun pref a suff => f a (pref ++ suff)

end List
