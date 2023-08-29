/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Control.Functor
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.SProd
import Mathlib.Util.CompileInductive
import Std.Tactic.Lint.Basic
import Std.Data.RBMap.Basic

#align_import data.list.defs from "leanprover-community/mathlib"@"d2d8742b0c21426362a9dacebc6005db895ca963"

/-!
## Definitions on lists

This file contains various definitions on lists. It does not contain
proofs about these definitions, those are contained in other files in `Data.List`
-/

set_option autoImplicit true

-- Porting notes
-- Many of the definitions in `Data.List.Defs` were already defined upstream in `Std4`
-- These have been annotated with `#align`s
-- To make this easier for review, the `#align`s have been placed in order of occurrence
-- in `mathlib`

namespace List

open Function Nat

universe u v w x

variable {α β γ δ ε ζ : Type*}

instance [DecidableEq α] : SDiff (List α) :=
  ⟨List.diff⟩

#align list.replicate List.replicate
#align list.split_at List.splitAt
#align list.split_on_p List.splitOnP
#align list.split_on List.splitOn
#align list.concat List.concat
#align list.head' List.head?

-- mathlib3 `array` is not ported.
#noalign list.to_array

#align list.nthd List.getD
-- porting notes: see
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/List.2Ehead/near/313204716
-- for the fooI naming convention.
/-- "Inhabited" `get` function: returns `default` instead of `none` in the case
  that the index is out of bounds. -/
def getI [Inhabited α] (l : List α) (n : Nat) : α :=
  getD l n default
#align list.inth List.getI

/-- "Inhabited" `take` function: Take `n` elements from a list `l`. If `l` has less than `n`
  elements, append `n - length l` elements `default`. -/
def takeI [Inhabited α] (n : Nat) (l : List α) : List α :=
  takeD n l default
#align list.take' List.takeI

#align list.modify_nth_tail List.modifyNthTail
#align list.modify_head List.modifyHead
#align list.modify_nth List.modifyNth
#align list.modify_last List.modifyLast
#align list.insert_nth List.insertNth
#align list.take_while List.takeWhile
#align list.scanl List.scanl
#align list.scanr List.scanr

/-- Product of a list.

     `List.prod [a, b, c] = ((1 * a) * b) * c` -/
def prod [Mul α] [One α] : List α → α :=
  foldl (· * ·) 1
#align list.prod List.prod

-- Later this will be tagged with `to_additive`, but this can't be done yet because of imports.
-- dependencies.
/-- Sum of a list.

     `List.sum [a, b, c] = ((0 + a) + b) + c` -/
def sum [Add α] [Zero α] : List α → α :=
  foldl (· + ·) 0
#align list.sum List.sum

/-- The alternating sum of a list. -/
def alternatingSum {G : Type*} [Zero G] [Add G] [Neg G] : List G → G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternatingSum t
#align list.alternating_sum List.alternatingSum

/-- The alternating product of a list. -/
def alternatingProd {G : Type*} [One G] [Mul G] [Inv G] : List G → G
  | [] => 1
  | g :: [] => g
  | g :: h :: t => g * h⁻¹ * alternatingProd t
#align list.alternating_prod List.alternatingProd

#align list.partition_map List.partitionMap
#align list.find List.find?

/-- `findM tac l` returns the first element of `l` on which `tac` succeeds, and
fails otherwise. -/
def findM {α} {m : Type u → Type v} [Alternative m] (tac : α → m PUnit) : List α → m α :=
  List.firstM <| fun a => (tac a) $> a
#align list.mfind List.findM

/-- `findM? p l` returns the first element `a` of `l` for which `p a` returns
true. `findM?` short-circuits, so `p` is not necessarily run on every `a` in
`l`. This is a monadic version of `List.find`. -/
def findM?'
    {m : Type u → Type v}
    [Monad m] {α : Type u}
    (p : α → m (ULift Bool)) : List α → m (Option α)
  | [] => pure none
  | x :: xs => do
    let ⟨px⟩ ← p x
    if px then pure (some x) else findM?' p xs
#align list.mbfind' List.findM?'

#align list.mbfind List.findM?
#align list.many List.anyM
#align list.mall List.allM

section

variable {m : Type → Type v} [Monad m]

/-- `orM xs` runs the actions in `xs`, returning true if any of them returns
true. `orM` short-circuits, so if an action returns true, later actions are
not run. -/
def orM : List (m Bool) → m Bool :=
  anyM id
#align list.mbor List.orM

/-- `andM xs` runs the actions in `xs`, returning true if all of them return
true. `andM` short-circuits, so if an action returns false, later actions are
not run. -/
def andM : List (m Bool) → m Bool :=
  allM id
#align list.mband List.andM

end

#align list.foldr_with_index List.foldrIdx
#align list.foldl_with_index List.foldlIdx
#align list.find_indexes List.findIdxs
#align list.indexes_values List.indexesValues
#align list.indexes_of List.indexesOf

section foldIdxM

variable {m : Type v → Type w} [Monad m]

/-- Monadic variant of `foldlIdx`. -/
def foldlIdxM {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) : m β :=
  as.foldlIdx
    (fun i ma b => do
      let a ← ma
      f i a b)
    (pure b)
#align list.mfoldl_with_index List.foldlIdxM

/-- Monadic variant of `foldrIdx`. -/
def foldrIdxM {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) : m β :=
  as.foldrIdx
    (fun i a mb => do
      let b ← mb
      f i a b)
    (pure b)
#align list.mfoldr_with_index List.foldrIdxM

end foldIdxM


section mapIdxM

-- porting notes: This was defined in `mathlib` with an `Applicative`
-- constraint on `m` and have been `#align`ed to the `Std` versions defined
-- with a `Monad` typeclass constraint.
-- Since all `Monad`s are `Applicative` this won't cause issues
-- downstream & `Monad`ic code is more performant per Mario C
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Applicative.20variants.20of.20Monadic.20functions/near/313213172
#align list.mmap_with_index List.mapIdxM

variable {m : Type v → Type w} [Monad m]

/-- Auxiliary definition for `mapIdxM'`. -/
def mapIdxMAux' {α} (f : ℕ → α → m PUnit) : ℕ → List α → m PUnit
  | _, [] => pure ⟨⟩
  | i, a :: as => f i a *> mapIdxMAux' f (i + 1) as
#align list.mmap_with_index'_aux List.mapIdxMAux'

/-- A variant of `mapIdxM` specialised to applicative actions which
return `Unit`. -/
def mapIdxM' {α} (f : ℕ → α → m PUnit) (as : List α) : m PUnit :=
  mapIdxMAux' f 0 as
#align list.mmap_with_index' List.mapIdxM'

end mapIdxM

#align list.lookmap List.lookmap
#align list.countp List.countP
#align list.count List.count
#align list.is_prefix List.isPrefix
#align list.is_suffix List.isSuffix
#align list.is_infix List.isInfix
#align list.inits List.inits
#align list.tails List.tails
#align list.sublists' List.sublists'
#align list.sublists List.sublists
#align list.forall₂ List.Forall₂

/-- `l.all₂ p` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction, i.e.
`List.All₂ p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp]
def All₂ (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ All₂ p l
#align list.all₂ List.All₂

#align list.transpose List.transpose
#align list.sections List.sections

section Permutations

/-- An auxiliary function for defining `permutations`. `permutationsAux2 t ts r ys f` is equal to
`(ys ++ ts, (insert_left ys t ts).map f ++ r)`, where `insert_left ys t ts` (not explicitly
defined) is the list of lists of the form `insert_nth n t (ys ++ ts)` for `0 ≤ n < length ys`.

    permutations_aux2 10 [4, 5, 6] [] [1, 2, 3] id =
      ([1, 2, 3, 4, 5, 6],
       [[10, 1, 2, 3, 4, 5, 6],
        [1, 10, 2, 3, 4, 5, 6],
        [1, 2, 10, 3, 4, 5, 6]]) -/
def permutationsAux2 (t : α) (ts : List α) (r : List β) : List α → (List α → β) → List α × List β
  | [], _ => (ts, r)
  | y :: ys, f =>
    let (us, zs) := permutationsAux2 t ts r ys (fun x: List α => f (y :: x))
    (y :: us, f (t :: y :: us) :: zs)
#align list.permutations_aux2 List.permutationsAux2

-- porting note: removed `[elab_as_elim]` per Mario C
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Status.20of.20data.2Elist.2Edefs.3F/near/313571979
/-- A recursor for pairs of lists. To have `C l₁ l₂` for all `l₁`, `l₂`, it suffices to have it for
`l₂ = []` and to be able to pour the elements of `l₁` into `l₂`. -/
def permutationsAux.rec {C : List α → List α → Sort v} (H0 : ∀ is, C [] is)
    (H1 : ∀ t ts is, C ts (t :: is) → C is [] → C (t :: ts) is) : ∀ l₁ l₂, C l₁ l₂
  | [], is => H0 is
  | t :: ts, is =>
      H1 t ts is (permutationsAux.rec H0 H1 ts (t :: is)) (permutationsAux.rec H0 H1 is [])
  termination_by _ ts is => (length ts + length is, length ts)
  decreasing_by simp_wf; simp [Nat.succ_add]; decreasing_tactic
                -- ⊢ Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (length ts + succ (le …
                         -- ⊢ Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (length ts + succ (le …
                                              -- 🎉 no goals
                -- ⊢ Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (length is, length is …
                         -- ⊢ Prod.Lex (fun a₁ a₂ => a₁ < a₂) (fun a₁ a₂ => a₁ < a₂) (length is, length is …
                                              -- 🎉 no goals
#align list.permutations_aux.rec List.permutationsAux.rec

/-- An auxiliary function for defining `permutations`. `permutationsAux ts is` is the set of all
permutations of `is ++ ts` that do not fix `ts`. -/
def permutationsAux : List α → List α → List (List α) :=
  permutationsAux.rec (fun _ => []) fun t ts is IH1 IH2 =>
    foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)
#align list.permutations_aux List.permutationsAux

/-- List of all permutations of `l`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]] -/
def permutations (l : List α) : List (List α) :=
  l :: permutationsAux l []
#align list.permutations List.permutations

/-- `permutations'Aux t ts` inserts `t` into every position in `ts`, including the last.
This function is intended for use in specifications, so it is simpler than `permutationsAux2`,
which plays roughly the same role in `permutations`.

Note that `(permutationsAux2 t [] [] ts id).2` is similar to this function, but skips the last
position:

    permutations'Aux 10 [1, 2, 3] =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3], [1, 2, 3, 10]]
    (permutationsAux2 10 [] [] [1, 2, 3] id).2 =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3]] -/
@[simp]
def permutations'Aux (t : α) : List α → List (List α)
  | [] => [[t]]
  | y :: ys => (t :: y :: ys) :: (permutations'Aux t ys).map (cons y)
#align list.permutations'_aux List.permutations'Aux

/-- List of all permutations of `l`. This version of `permutations` is less efficient but has
simpler definitional equations. The permutations are in a different order,
but are equal up to permutation, as shown by `list.permutations_perm_permutations'`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 3, 2], [3, 1, 2], [3, 2, 1]] -/
@[simp]
def permutations' : List α → List (List α)
  | [] => [[]]
  | t :: ts => (permutations' ts).bind <| permutations'Aux t
#align list.permutations' List.permutations'

end Permutations

#align list.erasep List.erasePₓ -- prop -> bool

/-- `extractp p l` returns a pair of an element `a` of `l` satisfying the predicate
  `p`, and `l`, with `a` removed. If there is no such element `a` it returns `(none, l)`. -/
def extractp (p : α → Prop) [DecidablePred p] : List α → Option α × List α
  | [] => (none, [])
  | a :: l =>
    if p a then (some a, l)
    else
      let (a', l') := extractp p l
      (a', a :: l')
#align list.extractp List.extractp

#align list.revzip List.revzip
#align list.product List.product

/-- Notation for calculating the product of a `List`
-/

instance instSProd : SProd (List α) (List β) (List (α × β)) where
  sprod := List.product

#align list.sigma List.sigma
#align list.of_fn List.ofFn
#align list.of_fn_nth_val List.ofFnNthVal
#align list.disjoint List.Disjoint
#align list.pairwise List.Pairwise
#align list.pairwise_cons List.pairwise_cons
#align list.decidable_pairwise List.instDecidablePairwise
#align list.pw_filter List.pwFilter
#align list.chain List.Chain
#align list.chain' List.Chain'
#align list.chain_cons List.chain_cons

section Chain

instance decidableChain [DecidableRel R] (a : α) (l : List α) :
    Decidable (Chain R a l) := by
  induction l generalizing a with
  | nil => simp only [List.Chain.nil]; infer_instance
  | cons a as ih => haveI := ih; simp only [List.chain_cons]; infer_instance
#align list.decidable_chain List.decidableChain

instance decidableChain' [DecidableRel R] (l : List α) : Decidable (Chain' R l) := by
  cases l <;> dsimp only [List.Chain'] <;> infer_instance
  -- ⊢ Decidable (Chain' R [])
              -- ⊢ Decidable True
              -- ⊢ Decidable (Chain R head✝ tail✝)
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align list.decidable_chain' List.decidableChain'

end Chain

#align list.nodup List.Nodup
#align list.nodup_decidable List.nodupDecidable

/-- `dedup l` removes duplicates from `l` (taking only the last occurrence).
  Defined as `pwFilter (≠)`.

     dedup [1, 0, 2, 2, 1] = [0, 2, 1] -/
def dedup [DecidableEq α] : List α → List α :=
  pwFilter (· ≠ ·)
#align list.dedup List.dedup

/-- Greedily create a sublist of `a :: l` such that, for every two adjacent elements `a, b`,
`R a b` holds. Mostly used with ≠; for example, `destutter' (≠) 1 [2, 2, 1, 1] = [1, 2, 1]`,
`destutter' (≠) 1, [2, 3, 3] = [1, 2, 3]`, `destutter' (<) 1 [2, 5, 2, 3, 4, 9] = [1, 2, 5, 9]`. -/
def destutter' (R : α → α → Prop) [DecidableRel R] : α → List α → List α
  | a, [] => [a]
  | a, h :: l => if R a h then a :: destutter' R h l else destutter' R a l
#align list.destutter' List.destutter'

-- TODO: should below be "lazily"?
/-- Greedily create a sublist of `l` such that, for every two adjacent elements `a, b ∈ l`,
`R a b` holds. Mostly used with ≠; for example, `destutter (≠) [1, 2, 2, 1, 1] = [1, 2, 1]`,
`destutter (≠) [1, 2, 3, 3] = [1, 2, 3]`, `destutter (<) [1, 2, 5, 2, 3, 4, 9] = [1, 2, 5, 9]`. -/
def destutter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | h :: l => destutter' R h l
  | [] => []
#align list.destutter List.destutter

#align list.range' List.range'
#align list.reduce_option List.reduceOption
-- Porting note: replace ilast' by getLastD
#align list.ilast' List.ilast'
-- Porting note: remove last' from Std
#align list.last' List.getLast?
#align list.rotate List.rotate
#align list.rotate' List.rotate'


section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns both `a` and proofs
of `a ∈ l` and `p a`. -/
def chooseX : ∀ l : List α, ∀ _ : ∃ a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a }
  | [], hp => False.elim (Exists.elim hp fun a h => not_mem_nil a h.left)
  | l :: ls, hp =>
    if pl : p l then ⟨l, ⟨mem_cons.mpr <| Or.inl rfl, pl⟩⟩
    else
      let ⟨a, ⟨a_mem_ls, pa⟩⟩ :=
        chooseX ls
          (hp.imp fun _ ⟨o, h₂⟩ => ⟨(mem_cons.mp o).resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
      ⟨a, ⟨mem_cons.mpr <| Or.inr a_mem_ls, pa⟩⟩
#align list.choose_x List.chooseX

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns `a : α`, and properties
are given by `choose_mem` and `choose_property`. -/
def choose (hp : ∃ a, a ∈ l ∧ p a) : α :=
  chooseX p l hp
#align list.choose List.choose

end Choose

#align list.mmap_filter List.filterMapM
#align list.mmap_upper_triangle List.mapDiagM

/-- `mapDiagM' f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mapDiagM' f l` will evaluate, in this order,
`f 1 1`, `f 1 2`, `f 1 3`, `f 2 2`, `f 2 3`, `f 3 3`.
-/
def mapDiagM' {m} [Monad m] {α} (f : α → α → m Unit) : List α → m Unit
-- as ported:
--   | [] => return ()
--   | h :: t => (f h h >> t.mapM' (f h)) >> t.mapDiagM'
  | [] => return ()
  | h :: t => do
    _ ← f h h
    _ ← t.mapM' (f h)
    t.mapDiagM' f
#align list.mmap'_diag List.mapDiagM'

/-- Map each element of a `List` to an action, evaluate these actions in order,
    and collect the results.
-/
protected def traverse {F : Type u → Type v} [Applicative F] {α β : Type _} (f : α → F β)
    : List α → F (List β)
  | [] => pure []
  | x :: xs => List.cons <$> f x <*> List.traverse f xs
#align list.traverse List.traverse

#align list.get_rest List.getRest
#align list.slice List.dropSlice

/-- Left-biased version of `List.map₂`. `map₂Left' f as bs` applies `f` to each
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
  | a :: as, b :: bs =>
    let rec' := map₂Left' f as bs
    (f a (some b) :: rec'.fst, rec'.snd)
#align list.map₂_left' List.map₂Left'

/-- Right-biased version of `List.map₂`. `map₂Right' f as bs` applies `f` to each
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
#align list.map₂_right' List.map₂Right'


/-- Left-biased version of `List.map₂`. `map₂Left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.

```
map₂Left Prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]

map₂Left Prod.mk [1] ['a', 'b'] = [(1, some 'a')]

map₂Left f as bs = (map₂Left' f as bs).fst
```
-/
@[simp]
def map₂Left (f : α → Option β → γ) : List α → List β → List γ
  | [], _ => []
  | a :: as, [] => (a :: as).map fun a => f a none
  | a :: as, b :: bs => f a (some b) :: map₂Left f as bs
#align list.map₂_left List.map₂Left

/-- Right-biased version of `List.map₂`. `map₂Right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.

```
map₂Right Prod.mk [1, 2] ['a'] = [(some 1, 'a')]

map₂Right Prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

map₂Right f as bs = (map₂Right' f as bs).fst
```
-/
def map₂Right (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  map₂Left (flip f) bs as
#align list.map₂_right List.map₂Right

#align list.zip_right List.zipRight
#align list.zip_left' List.zipLeft'
#align list.zip_right' List.zipRight'
#align list.zip_left List.zipLeft
#align list.all_some List.allSome
#align list.fill_nones List.fillNones
#align list.take_list List.takeList
#align list.to_rbmap List.toRBMap
#align list.to_chunks_aux List.toChunksAux
#align list.to_chunks List.toChunks

-- porting notes -- was `unsafe` but removed for Lean 4 port
-- TODO: naming is awkward...
/-- Asynchronous version of `List.map`.
-/
def mapAsyncChunked {α β} (f : α → β) (xs : List α) (chunk_size := 1024) : List β :=
  ((xs.toChunks chunk_size).map fun xs => Task.spawn fun _ => List.map f xs).bind Task.get
#align list.map_async_chunked List.mapAsyncChunked


/-!
We add some n-ary versions of `List.zipWith` for functions with more than two arguments.
These can also be written in terms of `List.zip` or `List.zipWith`.
For example, `zipWith3 f xs ys zs` could also be written as
`zipWith id (zipWith f xs ys) zs`
or as
`(zip xs $ zip ys zs).map $ λ ⟨x, y, z⟩, f x y z`.
-/

/-- Ternary version of `List.zipWith`. -/
def zipWith3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: zipWith3 f xs ys zs
  | _, _, _ => []
#align list.zip_with3 List.zipWith3

/-- Quaternary version of `list.zipWith`. -/
def zipWith4 (f : α → β → γ → δ → ε) : List α → List β → List γ → List δ → List ε
  | x :: xs, y :: ys, z :: zs, u :: us => f x y z u :: zipWith4 f xs ys zs us
  | _, _, _, _ => []
#align list.zip_with4 List.zipWith4

/-- Quinary version of `list.zipWith`. -/
def zipWith5 (f : α → β → γ → δ → ε → ζ) : List α → List β → List γ → List δ → List ε → List ζ
  | x :: xs, y :: ys, z :: zs, u :: us, v :: vs => f x y z u v :: zipWith5 f xs ys zs us vs
  | _, _, _, _, _ => []
#align list.zip_with5 List.zipWith5

/-- Given a starting list `old`, a list of booleans and a replacement list `new`,
read the items in `old` in succession and either replace them with the next element of `new` or
not, according as to whether the corresponding boolean is `true` or `false`. -/
def replaceIf : List α → List Bool → List α → List α
  | l, _, [] => l
  | [], _, _ => []
  | l, [], _ => l
  | n :: ns, tf :: bs, e@(c :: cs) => if tf then c :: ns.replaceIf bs cs else n :: ns.replaceIf bs e
#align list.replace_if List.replaceIf

#align list.map_with_prefix_suffix_aux List.mapWithPrefixSuffixAux
#align list.map_with_prefix_suffix List.mapWithPrefixSuffix
#align list.map_with_complement List.mapWithComplement

end List
