/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.Num.Lemmas
public import Mathlib.Tactic.DeriveFintype  -- shake: keep (deriving handlers not tracked yet)
public import Mathlib.Computability.TuringMachine.Config

/-!
# Modelling partial recursive functions using Turing machines

The files `Config` and `ToPartrec` define a simplified basis for partial recursive functions,
and a `Turing.TM2` model
Turing machine for evaluating these functions. This amounts to a constructive proof that every
`Partrec` function can be evaluated by a Turing machine.

## Main definitions

* `PartrecToTM2.tr`: A TM2 Turing machine which can evaluate `code` programs

-/

@[expose] public section

open List (Vector)

open Function (update)

open Relation StateTransition

namespace Turing

/-!
## Simulating sequentialized partial recursive functions in TM2

At this point we have a sequential model of partial recursive functions: the `Cfg` type and
`step : Cfg → Option Cfg` function from `TMConfig.lean`. The key feature of this model is that
it does a finite amount of computation (in fact, an amount which is statically bounded by the size
of the program) between each step, and no individual step can diverge (unlike the compositional
semantics, where every sub-part of the computation is potentially divergent). So we can utilize the
same techniques as in the other TM simulations in `Computability.TuringMachine` to prove that
each step corresponds to a finite number of steps in a lower level model. (We don't prove it here,
but in anticipation of the complexity class P, the simulation is actually polynomial-time as well.)

The target model is `Turing.TM2`, which has a fixed finite set of stacks, a bit of local storage,
with programs selected from a potentially infinite (but finitely accessible) set of program
positions, or labels `Λ`, each of which executes a finite sequence of basic stack commands.

For this program we will need four stacks, each on an alphabet `Γ'` like so:

```
    inductive Γ'  | consₗ | cons | bit0 | bit1
```

We represent a number as a bit sequence, lists of numbers by putting `cons` after each element, and
lists of lists of natural numbers by putting `consₗ` after each list. For example:

```
    0 ~> []
    1 ~> [bit1]
    6 ~> [bit0, bit1, bit1]
    [1, 2] ~> [bit1, cons, bit0, bit1, cons]
    [[], [1, 2]] ~> [consₗ, bit1, cons, bit0, bit1, cons, consₗ]
```

The four stacks are `main`, `rev`, `aux`, `stack`. In normal mode, `main` contains the input to the
current program (a `List ℕ`) and `stack` contains data (a `List (List ℕ)`) associated to the
current continuation, and in `ret` mode `main` contains the value that is being passed to the
continuation and `stack` contains the data for the continuation. The `rev` and `aux` stacks are
usually empty; `rev` is used to store reversed data when e.g. moving a value from one stack to
another, while `aux` is used as a temporary for a `main`/`stack` swap that happens during `cons₁`
evaluation.

The only local store we need is `Option Γ'`, which stores the result of the last pop
operation. (Most of our working data are natural numbers, which are too large to fit in the local
store.)

The continuations from the previous section are data-carrying, containing all the values that have
been computed and are awaiting other arguments. In order to have only a finite number of
continuations appear in the program so that they can be used in machine states, we separate the
data part (anything with type `List ℕ`) from the `Cont` type, producing a `Cont'` type that lacks
this information. The data is kept on the `stack` stack.

Because we want to have subroutines for e.g. moving an entire stack to another place, we use an
infinite inductive type `Λ'` so that we can execute a program and then return to do something else
without having to define too many different kinds of intermediate states. (We must nevertheless
prove that only finitely many labels are accessible.) The labels are:

* `move p k₁ k₂ q`: move elements from stack `k₁` to `k₂` while `p` holds of the value being moved.
  The last element, that fails `p`, is placed in neither stack but left in the local store.
  At the end of the operation, `k₂` will have the elements of `k₁` in reverse order. Then do `q`.
* `clear p k q`: delete elements from stack `k` until `p` is true. Like `move`, the last element is
  left in the local storage. Then do `q`.
* `copy q`: Move all elements from `rev` to both `main` and `stack` (in reverse order),
  then do `q`. That is, it takes `(a, b, c, d)` to `(b.reverse ++ a, [], c, b.reverse ++ d)`.
* `push k f q`: push `f s`, where `s` is the local store, to stack `k`, then do `q`. This is a
  duplicate of the `push` instruction that is part of the TM2 model, but by having a subroutine
  just for this purpose we can build up programs to execute inside a `goto` statement, where we
  have the flexibility to be general recursive.
* `read (f : Option Γ' → Λ')`: go to state `f s` where `s` is the local store. Again this is only
  here for convenience.
* `succ q`: perform a successor operation. Assuming `[n]` is encoded on `main` before,
  `[n+1]` will be on main after. This implements successor for binary natural numbers.
* `pred q₁ q₂`: perform a predecessor operation or `case` statement. If `[]` is encoded on
  `main` before, then we transition to `q₁` with `[]` on main; if `(0 :: v)` is on `main` before
  then `v` will be on `main` after and we transition to `q₁`; and if `(n+1 :: v)` is on `main`
  before then `n :: v` will be on `main` after and we transition to `q₂`.
* `ret k`: call continuation `k`. Each continuation has its own interpretation of the data in
  `stack` and sets up the data for the next continuation.
  * `ret (cons₁ fs k)`: `v :: KData` on `stack` and `ns` on `main`, and the next step expects
    `v` on `main` and `ns :: KData` on `stack`. So we have to do a little dance here with six
    reverse-moves using the `aux` stack to perform a three-point swap, each of which involves two
    reversals.
  * `ret (cons₂ k)`: `ns :: KData` is on `stack` and `v` is on `main`, and we have to put
    `ns.headI :: v` on `main` and `KData` on `stack`. This is done using the `head` subroutine.
  * `ret (fix f k)`: This stores no data, so we just check if `main` starts with `0` and
    if so, remove it and call `k`, otherwise `clear` the first value and call `f`.
  * `ret halt`: the stack is empty, and `main` has the output. Do nothing and halt.

In addition to these basic states, we define some additional subroutines that are used in the
above:
* `push'`, `peek'`, `pop'` are special versions of the builtins that use the local store to supply
  inputs and outputs.
* `unrev`: special case `move false rev main` to move everything from `rev` back to `main`. Used as
  a cleanup operation in several functions.
* `moveExcl p k₁ k₂ q`: same as `move` but pushes the last value read back onto the source stack.
* `move₂ p k₁ k₂ q`: double `move`, so that the result comes out in the right order at the target
  stack. Implemented as `moveExcl p k rev; move false rev k₂`. Assumes that neither `k₁` nor `k₂`
  is `rev` and `rev` is initially empty.
* `head k q`: get the first natural number from stack `k` and reverse-move it to `rev`, then clear
  the rest of the list at `k` and then `unrev` to reverse-move the head value to `main`. This is
  used with `k = main` to implement regular `head`, i.e. if `v` is on `main` before then `[v.headI]`
  will be on `main` after; and also with `k = stack` for the `cons` operation, which has `v` on
  `main` and `ns :: KData` on `stack`, and results in `KData` on `stack` and `ns.headI :: v` on
  `main`.
* `trNormal` is the main entry point, defining states that perform a given `code` computation.
  It mostly just dispatches to functions written above.

The main theorem of this section is `tr_eval`, which asserts that for each that for each code `c`,
the state `init c v` steps to `halt v'` in finitely many steps if and only if
`Code.eval c v = some v'`.
-/



namespace PartrecToTM2

section

open ToPartrec

set_option backward.isDefEq.respectTransparency false in
/-- The alphabet for the stacks in the program. `bit0` and `bit1` are used to represent `ℕ` values
as lists of binary digits, `cons` is used to separate `List ℕ` values, and `consₗ` is used to
separate `List (List ℕ)` values. See the section documentation. -/
inductive Γ'
  | consₗ
  | cons
  | bit0
  | bit1
  deriving DecidableEq, Inhabited, Fintype

-- A proof below relies on the value of that `deriving Inhabited` picks here.
@[simp] theorem default_Γ' : (default : Γ') = .consₗ := rfl

/-- The four stacks used by the program. `main` is used to store the input value in `trNormal`
mode and the output value in `Λ'.ret` mode, while `stack` is used to keep all the data for the
continuations. `rev` is used to store reversed lists when transferring values between stacks, and
`aux` is only used once in `cons₁`. See the section documentation. -/
inductive K'
  | main
  | rev
  | aux
  | stack
  deriving DecidableEq, Inhabited

open K'

/-- Continuations as in `ToPartrec.Cont` but with the data removed. This is done because we want
the set of all continuations in the program to be finite (so that it can ultimately be encoded into
the finite state machine of a Turing machine), but a continuation can handle a potentially infinite
number of data values during execution. -/
inductive Cont'
  | halt
  | cons₁ : Code → Cont' → Cont'
  | cons₂ : Cont' → Cont'
  | comp : Code → Cont' → Cont'
  | fix : Code → Cont' → Cont'
  deriving DecidableEq, Inhabited

/-- The set of program positions. We make extensive use of inductive types here to let us describe
"subroutines"; for example `clear p k q` is a program that clears stack `k`, then does `q` where
`q` is another label. In order to prevent this from resulting in an infinite number of distinct
accessible states, we are careful to be non-recursive (although loops are okay). See the section
documentation for a description of all the programs. -/
inductive Λ'
  | move (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
  | clear (p : Γ' → Bool) (k : K') (q : Λ')
  | copy (q : Λ')
  | push (k : K') (s : Option Γ' → Option Γ') (q : Λ')
  | read (f : Option Γ' → Λ')
  | succ (q : Λ')
  | pred (q₁ q₂ : Λ')
  | ret (k : Cont')

compile_inductive% Code
compile_inductive% Cont'
compile_inductive% K'
compile_inductive% Λ'

instance Λ'.instInhabited : Inhabited Λ' :=
  ⟨Λ'.ret Cont'.halt⟩

instance Λ'.instDecidableEq : DecidableEq Λ' := fun a b => by
  induction a generalizing b <;> cases b
  case move.move p k₁ k₂ q _ p' k₁' k₂' q' =>
    exact decidable_of_iff' (p = p' ∧ k₁ = k₁' ∧ k₂ = k₂' ∧ q = q') (by simp)
  case clear.clear p k q _ p' k' q' => exact decidable_of_iff' (p = p' ∧ k = k' ∧ q = q') (by simp)
  case copy.copy q _ q' => exact decidable_of_iff' (q = q') (by simp)
  case push.push k s q _ k' s' q' => exact decidable_of_iff' (k = k' ∧ s = s' ∧ q = q') (by simp)
  case read.read f _ f' => exact decidable_of_iff' (∀ a, f a = f' a) (by simp [funext_iff])
  case succ.succ q _ q' => exact decidable_of_iff' (q = q') (by simp)
  case pred.pred q₁ q₂ _ _ q₁' q₂' => exact decidable_of_iff' (q₁ = q₁' ∧ q₂ = q₂') (by simp)
  case ret.ret k k' => exact decidable_of_iff' (k = k') (by simp)
  all_goals exact .isFalse (by rintro ⟨⟨⟩⟩)

/-- The type of TM2 statements used by this machine. -/
def Stmt' :=
  TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

/-- The type of TM2 configurations used by this machine. -/
def Cfg' :=
  TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

open TM2.Stmt

/-- A predicate that detects the end of a natural number, either `Γ'.cons` or `Γ'.consₗ` (or
implicitly the end of the list), for use in predicate-taking functions like `move` and `clear`. -/
@[simp]
def natEnd : Γ' → Bool
  | Γ'.consₗ => true
  | Γ'.cons => true
  | _ => false
attribute [nolint simpNF] natEnd.eq_3

/-- Pop a value from the stack and place the result in local store. -/
@[simp]
def pop' (k : K') : Stmt' → Stmt' :=
  pop k fun _ v => v

/-- Peek a value from the stack and place the result in local store. -/
@[simp]
def peek' (k : K') : Stmt' → Stmt' :=
  peek k fun _ v => v

/-- Push the value in the local store to the given stack. -/
@[simp]
def push' (k : K') : Stmt' → Stmt' :=
  push k fun x => x.getD default

/-- Move everything from the `rev` stack to the `main` stack (reversed). -/
def unrev :=
  Λ'.move (fun _ => false) rev main

/-- Move elements from `k₁` to `k₂` while `p` holds, with the last element being left on `k₁`. -/
def moveExcl (p k₁ k₂ q) :=
  Λ'.move p k₁ k₂ <| Λ'.push k₁ id q

/-- Move elements from `k₁` to `k₂` without reversion, by performing a double move via the `rev`
stack. -/
def move₂ (p k₁ k₂ q) :=
  moveExcl p k₁ rev <| Λ'.move (fun _ => false) rev k₂ q

/-- Assuming `trList v` is on the front of stack `k`, remove it, and push `v.headI` onto `main`.
See the section documentation. -/
def head (k : K') (q : Λ') : Λ' :=
  Λ'.move natEnd k rev <|
    (Λ'.push rev fun _ => some Γ'.cons) <|
      Λ'.read fun s =>
        (if s = some Γ'.consₗ then id else Λ'.clear (fun x => x = Γ'.consₗ) k) <| unrev q

/-- The program that evaluates code `c` with continuation `k`. This expects an initial state where
`trList v` is on `main`, `trContStack k` is on `stack`, and `aux` and `rev` are empty.
See the section documentation for details. -/
@[simp]
def trNormal : Code → Cont' → Λ'
  | Code.zero', k => (Λ'.push main fun _ => some Γ'.cons) <| Λ'.ret k
  | Code.succ, k => head main <| Λ'.succ <| Λ'.ret k
  | Code.tail, k => Λ'.clear natEnd main <| Λ'.ret k
  | Code.cons f fs, k =>
    (Λ'.push stack fun _ => some Γ'.consₗ) <|
      Λ'.move (fun _ => false) main rev <| Λ'.copy <| trNormal f (Cont'.cons₁ fs k)
  | Code.comp f g, k => trNormal g (Cont'.comp f k)
  | Code.case f g, k => Λ'.pred (trNormal f k) (trNormal g k)
  | Code.fix f, k => trNormal f (Cont'.fix f k)

/-- The main program. See the section documentation for details. -/
def tr : Λ' → Stmt'
  | Λ'.move p k₁ k₂ q =>
    pop' k₁ <|
      branch (fun s => s.elim true p) (goto fun _ => q)
        (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)
  | Λ'.push k f q =>
    branch (fun s => (f s).isSome) ((push k fun s => (f s).getD default) <| goto fun _ => q)
      (goto fun _ => q)
  | Λ'.read q => goto q
  | Λ'.clear p k q =>
    pop' k <| branch (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)
  | Λ'.copy q =>
    pop' rev <|
      branch Option.isSome (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)
  | Λ'.succ q =>
    pop' main <|
      branch (fun s => s = some Γ'.bit1) ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q) <|
        branch (fun s => s = some Γ'.cons)
          ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
          ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
  | Λ'.pred q₁ q₂ =>
    pop' main <|
      branch (fun s => s = some Γ'.bit0)
          ((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂) <|
        branch (fun s => natEnd (s.getD default)) (goto fun _ => q₁)
          (peek' main <|
            branch (fun s => natEnd (s.getD default)) (goto fun _ => unrev q₂)
              ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))
  | Λ'.ret (Cont'.cons₁ fs k) =>
    goto fun _ =>
      move₂ (fun _ => false) main aux <|
        move₂ (fun s => s = Γ'.consₗ) stack main <|
          move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)
  | Λ'.ret (Cont'.cons₂ k) => goto fun _ => head stack <| Λ'.ret k
  | Λ'.ret (Cont'.comp f k) => goto fun _ => trNormal f k
  | Λ'.ret (Cont'.fix f k) =>
    pop' main <|
      goto fun s =>
        cond (natEnd (s.getD default)) (Λ'.ret k) <|
          Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)
  | Λ'.ret Cont'.halt => (load fun _ => none) <| halt

@[simp]
theorem tr_move (p k₁ k₂ q) : tr (Λ'.move p k₁ k₂ q) =
    pop' k₁ (branch (fun s => s.elim true p) (goto fun _ => q)
      (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)) := rfl

@[simp]
theorem tr_push (k f q) : tr (Λ'.push k f q) = branch (fun s => (f s).isSome)
    ((push k fun s => (f s).getD default) <| goto fun _ => q) (goto fun _ => q) := rfl

@[simp]
theorem tr_read (q) : tr (Λ'.read q) = goto q := rfl

@[simp]
theorem tr_clear (p k q) : tr (Λ'.clear p k q) = pop' k (branch
    (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)) := rfl

@[simp]
theorem tr_copy (q) : tr (Λ'.copy q) = pop' rev (branch Option.isSome
    (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)) := rfl

@[simp]
theorem tr_succ (q) : tr (Λ'.succ q) = pop' main (branch (fun s => s = some Γ'.bit1)
    ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q) <|
      branch (fun s => s = some Γ'.cons)
        ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
        ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)) := rfl

@[simp]
theorem tr_pred (q₁ q₂) : tr (Λ'.pred q₁ q₂) = pop' main (branch (fun s => s = some Γ'.bit0)
    ((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂) <|
    branch (fun s => natEnd (s.getD default)) (goto fun _ => q₁)
      (peek' main <|
        branch (fun s => natEnd (s.getD default)) (goto fun _ => unrev q₂)
          ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))) := rfl

@[simp]
theorem tr_ret_cons₁ (fs k) : tr (Λ'.ret (Cont'.cons₁ fs k)) = goto fun _ =>
    move₂ (fun _ => false) main aux <|
      move₂ (fun s => s = Γ'.consₗ) stack main <|
        move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k) := rfl

@[simp]
theorem tr_ret_cons₂ (k) : tr (Λ'.ret (Cont'.cons₂ k)) =
    goto fun _ => head stack <| Λ'.ret k := rfl

@[simp]
theorem tr_ret_comp (f k) : tr (Λ'.ret (Cont'.comp f k)) = goto fun _ => trNormal f k := rfl

@[simp]
theorem tr_ret_fix (f k) : tr (Λ'.ret (Cont'.fix f k)) = pop' main (goto fun s =>
    cond (natEnd (s.getD default)) (Λ'.ret k) <|
      Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) := rfl

@[simp]
theorem tr_ret_halt : tr (Λ'.ret Cont'.halt) = (load fun _ => none) halt := rfl

/-- Translating a `Cont` continuation to a `Cont'` continuation simply entails dropping all the
data. This data is instead encoded in `trContStack` in the configuration. -/
def trCont : Cont → Cont'
  | Cont.halt => Cont'.halt
  | Cont.cons₁ c _ k => Cont'.cons₁ c (trCont k)
  | Cont.cons₂ _ k => Cont'.cons₂ (trCont k)
  | Cont.comp c k => Cont'.comp c (trCont k)
  | Cont.fix c k => Cont'.fix c (trCont k)

/-- We use `PosNum` to define the translation of binary natural numbers. A natural number is
represented as a little-endian list of `bit0` and `bit1` elements:

```
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
```

In particular, this representation guarantees no trailing `bit0`'s at the end of the list. -/
def trPosNum : PosNum → List Γ'
  | PosNum.one => [Γ'.bit1]
  | PosNum.bit0 n => Γ'.bit0 :: trPosNum n
  | PosNum.bit1 n => Γ'.bit1 :: trPosNum n

/-- We use `Num` to define the translation of binary natural numbers. Positive numbers are
translated using `trPosNum`, and `trNum 0 = []`. So there are never any trailing `bit0`'s in
a translated `Num`.

```
    0 = []
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
```
-/
def trNum : Num → List Γ'
  | Num.zero => []
  | Num.pos n => trPosNum n

/-- Because we use binary encoding, we define `trNat` in terms of `trNum`, using `Num`, which are
binary natural numbers. (We could also use `Nat.binaryRecOn`, but `Num` and `PosNum` make for
easy inductions.) -/
def trNat (n : ℕ) : List Γ' :=
  trNum n

@[simp]
theorem trNat_zero : trNat 0 = [] := by rw [trNat, Nat.cast_zero]; rfl

theorem trNat_default : trNat default = [] :=
  trNat_zero

/-- Lists are translated with a `cons` after each encoded number.
For example:

```
    [] = []
    [0] = [cons]
    [1] = [bit1, cons]
    [6, 0] = [bit0, bit1, bit1, cons, cons]
```
-/
@[simp]
def trList : List ℕ → List Γ'
  | [] => []
  | n::ns => trNat n ++ Γ'.cons :: trList ns

/-- Lists of lists are translated with a `consₗ` after each encoded list.
For example:

```
    [] = []
    [[]] = [consₗ]
    [[], []] = [consₗ, consₗ]
    [[0]] = [cons, consₗ]
    [[1, 2], [0]] = [bit1, cons, bit0, bit1, cons, consₗ, cons, consₗ]
```
-/
@[simp]
def trLList : List (List ℕ) → List Γ'
  | [] => []
  | l::ls => trList l ++ Γ'.consₗ :: trLList ls

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `trLList`. -/
@[simp]
def contStack : Cont → List (List ℕ)
  | Cont.halt => []
  | Cont.cons₁ _ ns k => ns :: contStack k
  | Cont.cons₂ ns k => ns :: contStack k
  | Cont.comp _ k => contStack k
  | Cont.fix _ k => contStack k

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `trLList`. -/
def trContStack (k : Cont) :=
  trLList (contStack k)

/-- This is the nondependent eliminator for `K'`, but we use it specifically here in order to
represent the stack data as four lists rather than as a function `K' → List Γ'`, because this makes
rewrites easier. The theorems `K'.elim_update_main` et. al. show how such a function is updated
after an `update` to one of the components. -/
def K'.elim (a b c d : List Γ') : K' → List Γ'
  | K'.main => a
  | K'.rev => b
  | K'.aux => c
  | K'.stack => d

-- The equation lemma of `elim` simplifies to `match` structures.

theorem K'.elim_main (a b c d) : K'.elim a b c d K'.main = a := rfl

theorem K'.elim_rev (a b c d) : K'.elim a b c d K'.rev = b := rfl

theorem K'.elim_aux (a b c d) : K'.elim a b c d K'.aux = c := rfl

theorem K'.elim_stack (a b c d) : K'.elim a b c d K'.stack = d := rfl

attribute [simp] K'.elim

@[simp]
theorem K'.elim_update_main {a b c d a'} : update (K'.elim a b c d) main a' = K'.elim a' b c d := by
  funext x; cases x <;> rfl

@[simp]
theorem K'.elim_update_rev {a b c d b'} : update (K'.elim a b c d) rev b' = K'.elim a b' c d := by
  funext x; cases x <;> rfl

@[simp]
theorem K'.elim_update_aux {a b c d c'} : update (K'.elim a b c d) aux c' = K'.elim a b c' d := by
  funext x; cases x <;> rfl

@[simp]
theorem K'.elim_update_stack {a b c d d'} :
    update (K'.elim a b c d) stack d' = K'.elim a b c d' := by funext x; cases x <;> rfl

/-- The halting state corresponding to a `List ℕ` output value. -/
def halt (v : List ℕ) : Cfg' :=
  ⟨none, none, K'.elim (trList v) [] [] []⟩

/-- The `Cfg` states map to `Cfg'` states almost one to one, except that in normal operation the
local store contains an arbitrary garbage value. To make the final theorem cleaner we explicitly
clear it in the halt state so that there is exactly one configuration corresponding to output `v`.
-/
def TrCfg : Cfg → Cfg' → Prop
  | Cfg.ret k v, c' =>
    ∃ s, c' = ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩
  | Cfg.halt v, c' => c' = halt v

/-- This could be a general list definition, but it is also somewhat specialized to this
application. `splitAtPred p L` will search `L` for the first element satisfying `p`.
If it is found, say `L = l₁ ++ a :: l₂` where `a` satisfies `p` but `l₁` does not, then it returns
`(l₁, some a, l₂)`. Otherwise, if there is no such element, it returns `(L, none, [])`. -/
def splitAtPred {α} (p : α → Bool) : List α → List α × Option α × List α
  | [] => ([], none, [])
  | a :: as =>
    cond (p a) ([], some a, as) <|
      let ⟨l₁, o, l₂⟩ := splitAtPred p as
      ⟨a::l₁, o, l₂⟩

theorem splitAtPred_eq {α} (p : α → Bool) :
    ∀ L l₁ o l₂,
      (∀ x ∈ l₁, p x = false) →
        Option.elim' (L = l₁ ∧ l₂ = []) (fun a => p a = true ∧ L = l₁ ++ a::l₂) o →
          splitAtPred p L = (l₁, o, l₂)
  | [], _, none, _, _, ⟨rfl, rfl⟩ => rfl
  | [], l₁, some o, l₂, _, ⟨_, h₃⟩ => by simp at h₃
  | a :: L, l₁, o, l₂, h₁, h₂ => by
    rw [splitAtPred]
    have IH := splitAtPred_eq p L
    rcases o with - | o
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨⟨⟩, rfl⟩
      rw [h₁ a (List.Mem.head _), cond, IH L none [] _ ⟨rfl, rfl⟩]
      exact fun x h => h₁ x (List.Mem.tail _ h)
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨h₂, ⟨⟩⟩
      · rw [h₂, cond]
      rw [h₁ a (List.Mem.head _), cond, IH l₁ (some o) l₂ _ ⟨h₂, _⟩] <;> try rfl
      exact fun x h => h₁ x (List.Mem.tail _ h)

theorem splitAtPred_false {α} (L : List α) : splitAtPred (fun _ => false) L = (L, none, []) :=
  splitAtPred_eq _ _ _ _ _ (fun _ _ => rfl) ⟨rfl, rfl⟩

theorem move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ k₂)
    (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.move p k₁ k₂ q), s, S⟩
      ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverseAux (S k₂))⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    swap
    · rw [Function.update_of_ne h₁.symm, List.reverseAux_nil]
    refine TransGen.head' rfl ?_
    simp only [tr_move, pop', TM2.stepAux]
    grind [splitAtPred.eq_def]
  | cons a L₁ IH =>
    refine TransGen.head rfl ?_
    rw [tr]; simp only [pop', Option.elim, TM2.stepAux, push']
    rcases e₁ : S k₁ with - | ⟨a', Sk⟩ <;> rw [e₁, splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, cond_false]
    convert! @IH _ (update (update S k₁ Sk) k₂ (a :: S k₂)) _ using 2 <;>
      simp [Function.update_of_ne, h₁, h₁.symm, e₃, List.reverseAux]
    simp [Function.update_comm h₁.symm]

theorem unrev_ok {q s} {S : K' → List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (unrev q), s, S⟩
      ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (S main))⟩ :=
  move_ok (by decide) <| splitAtPred_false _

theorem move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂)
    (h₂ : S rev = []) (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (move₂ p k₁ k₂ q), s, S⟩
      ⟨some q, none, update (update S k₁ (o.elim id List.cons L₂)) k₂ (L₁ ++ S k₂)⟩ := by
  refine (move_ok h₁.1 e).trans (TransGen.head rfl ?_)
  simp only [TM2.step, Option.mem_def, Option.elim]
  cases o <;> simp only <;> rw [tr]
    <;> simp only [id, TM2.stepAux, Option.isSome, cond_true, cond_false]
  · convert! move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [Function.update_comm h₁.1, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.2.2.symm, Function.update_of_ne h₁.2.1,
      Function.update_of_ne h₁.1.symm, List.reverseAux_eq, h₂, Function.update_self,
      List.append_nil, List.reverse_reverse]
  · simp only [Option.getD_some]
    convert! move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [h₂, Function.update_comm h₁.1, List.reverseAux_eq, Function.update_self,
      List.append_nil, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.1.symm, Function.update_of_ne h₁.2.2.symm,
      Function.update_of_ne h₁.2.1, Function.update_self, List.reverse_reverse]

theorem clear_ok {p k q s L₁ o L₂} {S : K' → List Γ'} (e : splitAtPred p (S k) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.clear p k q), s, S⟩ ⟨some q, o, update S k L₂⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    refine TransGen.head' rfl ?_
    rw [tr]; simp only [pop', TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    revert e; rcases S k with - | ⟨a, Sk⟩ <;> intro e
    · cases e
      rfl
    simp only [splitAtPred, List.head?, List.tail_cons] at e ⊢
    revert e; cases p a <;> intro e <;>
      simp only [cond_false, cond_true, Prod.mk.injEq, true_and, false_and, reduceCtorEq] at e ⊢
    rcases e with ⟨e₁, e₂⟩
    rw [e₁, e₂]
  | cons a L₁ IH =>
    refine TransGen.head rfl ?_
    rw [tr]; simp only [pop', TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    rcases e₁ : S k with - | ⟨a', Sk⟩ <;> rw [e₁, splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, cond_false]
    convert! @IH _ (update S k Sk) _ using 2 <;> simp [e₃]

set_option backward.isDefEq.respectTransparency false in
theorem copy_ok (q s a b c d) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.copy q), s, K'.elim a b c d⟩
      ⟨some q, none, K'.elim (List.reverseAux b a) [] c (List.reverseAux b d)⟩ := by
  induction b generalizing a d s with
  | nil =>
    refine TransGen.single ?_
    simp
  | cons x b IH =>
    refine TransGen.head rfl ?_
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_rev, List.head?_cons, Option.isSome_some,
      List.tail_cons, elim_update_rev, elim_main, elim_update_main,
      elim_stack, elim_update_stack, cond_true, List.reverseAux_cons, pop', push']
    exact IH _ _ _

theorem trPosNum_natEnd : ∀ (n), ∀ x ∈ trPosNum n, natEnd x = false
  | PosNum.one, _, List.Mem.head _ => rfl
  | PosNum.bit0 _, _, List.Mem.head _ => rfl
  | PosNum.bit0 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h
  | PosNum.bit1 _, _, List.Mem.head _ => rfl
  | PosNum.bit1 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h

theorem trNum_natEnd : ∀ (n), ∀ x ∈ trNum n, natEnd x = false
  | Num.pos n, x, h => trPosNum_natEnd n x h

theorem trNat_natEnd (n) : ∀ x ∈ trNat n, natEnd x = false :=
  trNum_natEnd _

theorem trList_ne_consₗ : ∀ (l), ∀ x ∈ trList l, x ≠ Γ'.consₗ
  | a :: l, x, h => by
    simp only [trList, List.mem_append, List.mem_cons] at h
    obtain h | rfl | h := h
    · rintro rfl
      cases trNat_natEnd _ _ h
    · rintro ⟨⟩
    · exact trList_ne_consₗ l _ h

theorem head_main_ok {q s L} {c d : List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (head main q), s, K'.elim (trList L) [] c d⟩
      ⟨some q, none, K'.elim (trList [L.headI]) [] c d⟩ := by
  let o : Option Γ' := List.casesOn L none fun _ _ => some Γ'.cons
  refine
    (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat L.headI) o (trList L.tail) (trNat_natEnd _) ?_)).trans
      (TransGen.head rfl (TransGen.head rfl ?_))
  · cases L <;> simp [o]
  rw [tr]
  simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_update_main, elim_rev, elim_update_rev,
    Function.update_self, trList]
  rw [if_neg (show o ≠ some Γ'.consₗ by cases L <;> simp [o])]
  refine (clear_ok (splitAtPred_eq _ _ _ none [] ?_ ⟨rfl, rfl⟩)).trans ?_
  · exact fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)
  convert! unrev_ok using 2; simp [List.reverseAux_eq]

theorem head_stack_ok {q s L₁ L₂ L₃} :
    Reaches₁ (TM2.step tr)
      ⟨some (head stack q), s, K'.elim (trList L₁) [] [] (trList L₂ ++ Γ'.consₗ :: L₃)⟩
      ⟨some q, none, K'.elim (trList (L₂.headI :: L₁)) [] [] L₃⟩ := by
  rcases L₂ with - | ⟨a, L₂⟩
  · refine
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ [] (some Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
        (TransGen.head rfl (TransGen.head rfl ?_))
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, ite_true, id_eq, trList, List.nil_append,
      elim_update_stack, elim_rev, List.reverseAux_nil, elim_update_rev, Function.update_self,
      List.headI_nil, trNat_default]
    convert! unrev_ok using 2
    simp
  · refine
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat a) (some Γ'.cons) (trList L₂ ++ Γ'.consₗ :: L₃)
            (trNat_natEnd _) ⟨rfl, by simp⟩))
        (TransGen.head rfl (TransGen.head rfl ?_))
    simp only [TM2.step, Option.mem_def, trList, List.append_assoc,
      List.cons_append, elim_update_stack, elim_rev, elim_update_rev, Function.update_self,
      List.headI_cons]
    refine
      TransGen.trans
        (clear_ok
          (splitAtPred_eq _ _ (trList L₂) (some Γ'.consₗ) L₃
            (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, by simp⟩))
        ?_
    convert! unrev_ok using 2
    simp [List.reverseAux_eq]

set_option backward.isDefEq.respectTransparency false in
theorem succ_ok {q s n} {c d : List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.succ q), s, K'.elim (trList [n]) [] c d⟩
      ⟨some q, none, K'.elim (trList [n.succ]) [] c d⟩ := by
  simp only [trList, trNat.eq_1, Nat.cast_succ, Num.add_one]
  rcases (n : Num) with - | a
  · refine TransGen.head rfl ?_
    simp only [Option.mem_def]
    convert! unrev_ok using 1
    simp only [elim_update_rev, elim_rev, elim_main, List.reverseAux_nil, elim_update_main]
    rfl
  simp only [trNum, Num.succ, Num.succ']
  suffices ∀ l₁, ∃ l₁' l₂' s',
      List.reverseAux l₁ (trPosNum a.succ) = List.reverseAux l₁' l₂' ∧
        Reaches₁ (TM2.step tr) ⟨some q.succ, s, K'.elim (trPosNum a ++ [Γ'.cons]) l₁ c d⟩
          ⟨some (unrev q), s', K'.elim (l₂' ++ [Γ'.cons]) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp only [List.reverseAux] at e
    refine h.trans ?_
    convert! unrev_ok using 2
    simp [e, List.reverseAux_eq]
  induction a generalizing s with intro l₁
  | one =>
    refine ⟨Γ'.bit0 :: l₁, [Γ'.bit1], some Γ'.cons, rfl, TransGen.head rfl (TransGen.single ?_)⟩
    simp [trPosNum]
  | bit1 m IH =>
    obtain ⟨l₁', l₂', s', e, h⟩ := IH (Γ'.bit0 :: l₁)
    refine ⟨l₁', l₂', s', e, TransGen.head ?_ h⟩
    simp [trPosNum]
    rfl
  | bit0 m _ =>
    refine ⟨l₁, _, some Γ'.bit0, rfl, TransGen.single ?_⟩
    simp only [TM2.step]; rw [tr]
    simp only [TM2.stepAux, pop', elim_main, elim_update_main,
      elim_rev, elim_update_rev, Function.update_self, Option.mem_def, Option.some.injEq]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem pred_ok (q₁ q₂ s v) (c d : List Γ') : ∃ s',
    Reaches₁ (TM2.step tr) ⟨some (Λ'.pred q₁ q₂), s, K'.elim (trList v) [] c d⟩
      (v.headI.rec ⟨some q₁, s', K'.elim (trList v.tail) [] c d⟩ fun n _ =>
        ⟨some q₂, s', K'.elim (trList (n::v.tail)) [] c d⟩) := by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine ⟨none, TransGen.single ?_⟩
    simp
  · refine ⟨some Γ'.cons, TransGen.single ?_⟩
    simp
  refine ⟨none, ?_⟩
  simp only [trList, trNat.eq_1, trNum, Nat.cast_succ, Num.add_one, Num.succ,
    List.tail_cons, List.headI_cons]
  rcases (n : Num) with - | a
  · simp only [trPosNum, Num.succ', List.singleton_append, List.nil_append]
    refine TransGen.head rfl ?_
    rw [tr]; simp only [pop', TM2.stepAux]
    convert! unrev_ok using 2
    simp
  simp only [Num.succ']
  suffices ∀ l₁, ∃ l₁' l₂' s',
    List.reverseAux l₁ (trPosNum a) = List.reverseAux l₁' l₂' ∧
      Reaches₁ (TM2.step tr)
        ⟨some (q₁.pred q₂), s, K'.elim (trPosNum a.succ ++ Γ'.cons :: trList v) l₁ c d⟩
        ⟨some (unrev q₂), s', K'.elim (l₂' ++ Γ'.cons :: trList v) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp only [List.reverseAux] at e
    refine h.trans ?_
    convert! unrev_ok using 2
    simp [e, List.reverseAux_eq]
  induction a generalizing s with intro l₁
  | one =>
    refine ⟨Γ'.bit1::l₁, [], some Γ'.cons, rfl, TransGen.head rfl (TransGen.single ?_)⟩
    simp [trPosNum, show PosNum.one.succ = PosNum.one.bit0 from rfl]
  | bit1 m IH =>
    obtain ⟨l₁', l₂', s', e, h⟩ := IH (some Γ'.bit0) (Γ'.bit1 :: l₁)
    refine ⟨l₁', l₂', s', e, TransGen.head ?_ h⟩
    simp
    rfl
  | bit0 m IH =>
    obtain ⟨a, l, e, h⟩ : ∃ a l, (trPosNum m = a::l) ∧ natEnd a = false := by
      cases m <;> refine ⟨_, _, rfl, rfl⟩
    refine ⟨Γ'.bit0 :: l₁, _, some a, rfl, TransGen.single ?_⟩
    simp [trPosNum, PosNum.succ, e, h, show some Γ'.bit1 ≠ some Γ'.bit0 by decide,
      Option.getD, -natEnd]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem trNormal_respects (c k v s) :
    ∃ b₂,
      TrCfg (stepNormal c k v) b₂ ∧
        Reaches₁ (TM2.step tr)
          ⟨some (trNormal c (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩ b₂ := by
  induction c generalizing k v s with
  | zero' => refine ⟨_, ⟨s, rfl⟩, TransGen.single ?_⟩; simp
  | succ => refine ⟨_, ⟨none, rfl⟩, head_main_ok.trans succ_ok⟩
  | tail =>
    let o : Option Γ' := List.casesOn v none fun _ _ => some Γ'.cons
    refine ⟨_, ⟨o, rfl⟩, ?_⟩; convert! clear_ok _ using 2
    · simp; rfl
    swap
    refine splitAtPred_eq _ _ (trNat v.headI) _ _ (trNat_natEnd _) ?_
    cases v <;> simp [o]
  | cons f fs IHf _ =>
    obtain ⟨c, h₁, h₂⟩ := IHf (Cont.cons₁ fs v k) v none
    refine ⟨c, h₁, TransGen.head rfl <| (move_ok (by decide) (splitAtPred_false _)).trans ?_⟩
    simp only [TM2.step, Option.mem_def, elim_stack, elim_update_stack, elim_update_main,
      elim_main, elim_rev, elim_update_rev]
    refine (copy_ok _ none [] (trList v).reverse _ _).trans ?_
    convert! h₂ using 2
    simp [List.reverseAux_eq, trContStack]
  | comp f _ _ IHg => exact IHg (Cont.comp f k) v s
  | case f g IHf IHg =>
    rw [stepNormal]
    simp only
    obtain ⟨s', h⟩ := pred_ok _ _ s v _ _
    revert h; rcases v.headI with - | n <;> intro h
    · obtain ⟨c, h₁, h₂⟩ := IHf k _ s'
      exact ⟨_, h₁, h.trans h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := IHg k _ s'
      exact ⟨_, h₁, h.trans h₂⟩
  | fix f IH => apply IH

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
theorem tr_ret_respects (k v s) : ∃ b₂,
    TrCfg (stepRet k v) b₂ ∧
      Reaches₁ (TM2.step tr)
        ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩ b₂ := by
  induction k generalizing v s with
  | halt => exact ⟨_, rfl, TransGen.single rfl⟩
  | cons₁ fs as k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects fs (Cont.cons₂ v k) as none
    refine ⟨s', h₁, TransGen.head rfl ?_⟩; simp
    refine (move₂_ok (by decide) ?_ (splitAtPred_false _)).trans ?_; · rfl
    simp only [TM2.step, Option.mem_def, Option.elim, id_eq, elim_update_main, elim_main, elim_aux,
      List.append_nil, elim_update_aux]
    refine (move₂_ok (L₁ := ?_) (o := ?_) (L₂ := ?_) (by decide) rfl ?_).trans ?_
    pick_goal 4
    · exact splitAtPred_eq _ _ _ (some Γ'.consₗ) _
        (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, rfl⟩
    refine (move₂_ok (by decide) ?_ (splitAtPred_false _)).trans ?_; · rfl
    simp only [TM2.step, Option.mem_def, Option.elim, elim_update_stack, elim_main,
      List.append_nil, elim_update_main, id_eq, elim_update_aux,
      elim_aux, elim_stack]
    exact h₂
  | cons₂ ns k IH =>
    obtain ⟨c, h₁, h₂⟩ := IH (ns.headI :: v) none
    exact ⟨c, h₁, TransGen.head rfl <| head_stack_ok.trans h₂⟩
  | comp f k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects f k v s
    exact ⟨_, h₁, TransGen.head rfl h₂⟩
  | fix f k IH =>
    rw [stepRet]
    have :
      if v.headI = 0 then natEnd ((trList v).head?.getD default) = true ∧
          (trList v).tail = trList v.tail
      else
        natEnd ((trList v).head?.getD default) = false ∧
          (trList v).tail = (trNat v.headI).tail ++ Γ'.cons :: trList v.tail := by
      obtain - | n := v
      · exact ⟨rfl, rfl⟩
      rcases n with - | n
      · simp
      rw [trList, List.headI, trNat, Nat.cast_succ, Num.add_one, Num.succ, List.tail]
      cases (n : Num).succ' <;> exact ⟨rfl, rfl⟩
    by_cases h : v.headI = 0 <;> simp only [h, ite_true, ite_false] at this ⊢
    · obtain ⟨c, h₁, h₂⟩ := IH v.tail (trList v).head?
      refine ⟨c, h₁, TransGen.head rfl ?_⟩
      rw [trCont, tr]; simp only [pop', TM2.stepAux, elim_main, this, elim_update_main]
      exact h₂
    · obtain ⟨s', h₁, h₂⟩ := trNormal_respects f (Cont.fix f k) v.tail (some Γ'.cons)
      refine ⟨_, h₁, TransGen.head rfl <| TransGen.trans ?_ h₂⟩
      rw [trCont, tr]; simp only [pop', TM2.stepAux, elim_main, this.1]
      convert! clear_ok (splitAtPred_eq _ _ (trNat v.headI).tail (some Γ'.cons) _ _ _) using 2
      · simp
        convert! rfl
      · exact fun x h => trNat_natEnd _ _ (List.tail_subset _ h)
      · exact ⟨rfl, this.2⟩

theorem tr_respects : Respects step (TM2.step tr) TrCfg
  | Cfg.ret _ _, _, ⟨_, rfl⟩ => tr_ret_respects _ _ _
  | Cfg.halt _, _, rfl => rfl

/-- The initial state, evaluating function `c` on input `v`. -/
def init (c : Code) (v : List ℕ) : Cfg' :=
  ⟨some (trNormal c Cont'.halt), none, K'.elim (trList v) [] [] []⟩

theorem tr_init (c v) :
    ∃ b, TrCfg (stepNormal c Cont.halt v) b ∧ Reaches₁ (TM2.step tr) (init c v) b :=
  trNormal_respects _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem tr_eval (c v) : eval (TM2.step tr) (init c v) = halt <$> Code.eval c v := by
  obtain ⟨i, h₁, h₂⟩ := tr_init c v
  refine Part.ext fun x => ?_
  rw [reaches_eval h₂.to_reflTransGen]; simp only [Part.map_eq_map, Part.mem_map_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, hc₁, hc₂⟩ := tr_eval_rev tr_respects h₁ h
    simp only [stepNormal_eval, Part.map_eq_map, Part.mem_map_iff] at hc₂
    obtain ⟨v', hv, rfl⟩ := hc₂
    exact ⟨_, hv, hc₁.symm⟩
  · rintro ⟨v', hv, rfl⟩
    have := StateTransition.tr_eval (b₁ := Cfg.halt v') tr_respects h₁
    simp only [stepNormal_eval, Part.map_eq_map, Part.mem_map_iff, Cfg.halt.injEq,
      exists_eq_right] at this
    obtain ⟨_, ⟨⟩, h⟩ := this hv
    exact h

/-- The set of machine states reachable via downward label jumps, discounting jumps via `ret`. -/
def trStmts₁ : Λ' → Finset Λ'
  | Q@(Λ'.move _ _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.push _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.read q) => insert Q <| Finset.univ.biUnion fun s => trStmts₁ (q s)
  | Q@(Λ'.clear _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.copy q) => insert Q <| trStmts₁ q
  | Q@(Λ'.succ q) => insert Q <| insert (unrev q) <| trStmts₁ q
  | Q@(Λ'.pred q₁ q₂) => insert Q <| trStmts₁ q₁ ∪ insert (unrev q₂) (trStmts₁ q₂)
  | Q@(Λ'.ret _) => {Q}

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
theorem trStmts₁_trans {q q'} : q' ∈ trStmts₁ q → trStmts₁ q' ⊆ trStmts₁ q := by
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
  all_goals
    simp +contextual only [trStmts₁, Finset.mem_insert, Finset.mem_union,
      or_imp, Finset.mem_singleton, Finset.Subset.refl, imp_true_iff, true_and]
    repeat exact fun h => Finset.Subset.trans (q_ih h) (Finset.subset_insert _ _)
  · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, forall_exists_index]
    intro s h x h'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert]
    exact Or.inr ⟨_, q_ih s h h'⟩
  · constructor
    · rintro rfl
      apply Finset.subset_insert
    · intro h x h'
      simp only [Finset.mem_insert]
      exact Or.inr (Or.inr <| q_ih h h')
  · refine ⟨fun h x h' => ?_, fun _ x h' => ?_, fun h x h' => ?_⟩ <;> simp
    · exact Or.inr (Or.inr <| Or.inl <| q₁_ih h h')
    · rcases Finset.mem_insert.1 h' with h' | h' <;> simp [h', unrev]
    · exact Or.inr (Or.inr <| Or.inr <| q₂_ih h h')

theorem trStmts₁_self (q) : q ∈ trStmts₁ q := by
  induction q <;> · first | apply Finset.mem_singleton_self | apply Finset.mem_insert_self

/-- The (finite!) set of machine states visited during the course of evaluation of `c`,
including the state `ret k` but not any states after that (that is, the states visited while
evaluating `k`). -/
def codeSupp' : Code → Cont' → Finset Λ'
  | c@Code.zero', k => trStmts₁ (trNormal c k)
  | c@Code.succ, k => trStmts₁ (trNormal c k)
  | c@Code.tail, k => trStmts₁ (trNormal c k)
  | c@(Code.cons f fs), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' f (Cont'.cons₁ fs k) ∪
        (trStmts₁
            (move₂ (fun _ => false) main aux <|
              move₂ (fun s => s = Γ'.consₗ) stack main <|
                move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
          (codeSupp' fs (Cont'.cons₂ k) ∪ trStmts₁ (head stack <| Λ'.ret k))))
  | c@(Code.comp f g), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' g (Cont'.comp f k) ∪ (trStmts₁ (trNormal f k) ∪ codeSupp' f k))
  | c@(Code.case f g), k => trStmts₁ (trNormal c k) ∪ (codeSupp' f k ∪ codeSupp' g k)
  | c@(Code.fix f), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' f (Cont'.fix f k) ∪
        (trStmts₁ (Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) ∪ {Λ'.ret k}))

@[simp]
theorem codeSupp'_self (c k) : trStmts₁ (trNormal c k) ⊆ codeSupp' c k := by
  cases c <;> first | rfl | exact Finset.union_subset_left (fun _ a ↦ a)

/-- The (finite!) set of machine states visited during the course of evaluation of a continuation
`k`, not including the initial state `ret k`. -/
def contSupp : Cont' → Finset Λ'
  | Cont'.cons₁ fs k =>
    trStmts₁
        (move₂ (fun _ => false) main aux <|
          move₂ (fun s => s = Γ'.consₗ) stack main <|
            move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
      (codeSupp' fs (Cont'.cons₂ k) ∪ (trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k))
  | Cont'.cons₂ k => trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k
  | Cont'.comp f k => codeSupp' f k ∪ contSupp k
  | Cont'.fix f k => codeSupp' (Code.fix f) k ∪ contSupp k
  | Cont'.halt => ∅

/-- The (finite!) set of machine states visited during the course of evaluation of `c` in
continuation `k`. This is actually closed under forward simulation (see `tr_supports`), and the
existence of this set means that the machine constructed in this section is in fact a proper
Turing machine, with a finite set of states. -/
def codeSupp (c : Code) (k : Cont') : Finset Λ' :=
  codeSupp' c k ∪ contSupp k

@[simp]
theorem codeSupp_self (c k) : trStmts₁ (trNormal c k) ⊆ codeSupp c k :=
  Finset.Subset.trans (codeSupp'_self _ _) (Finset.union_subset_left fun _ a ↦ a)

@[simp]
theorem codeSupp_zero (k) : codeSupp Code.zero' k = trStmts₁ (trNormal Code.zero' k) ∪ contSupp k :=
  rfl

@[simp]
theorem codeSupp_succ (k) : codeSupp Code.succ k = trStmts₁ (trNormal Code.succ k) ∪ contSupp k :=
  rfl

@[simp]
theorem codeSupp_tail (k) : codeSupp Code.tail k = trStmts₁ (trNormal Code.tail k) ∪ contSupp k :=
  rfl

@[simp]
theorem codeSupp_cons (f fs k) :
    codeSupp (Code.cons f fs) k =
      trStmts₁ (trNormal (Code.cons f fs) k) ∪ codeSupp f (Cont'.cons₁ fs k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]

@[simp]
theorem codeSupp_comp (f g k) :
    codeSupp (Code.comp f g) k =
      trStmts₁ (trNormal (Code.comp f g) k) ∪ codeSupp g (Cont'.comp f k) := by
  simp only [codeSupp, codeSupp', trNormal, Finset.union_assoc, contSupp]
  rw [← Finset.union_assoc _ _ (contSupp k),
    Finset.union_eq_right.2 (codeSupp'_self _ _)]

@[simp]
theorem codeSupp_case (f g k) :
    codeSupp (Code.case f g) k =
      trStmts₁ (trNormal (Code.case f g) k) ∪ (codeSupp f k ∪ codeSupp g k) := by
  simp [codeSupp, codeSupp', Finset.union_assoc, Finset.union_left_comm]

@[simp]
theorem codeSupp_fix (f k) :
    codeSupp (Code.fix f) k = trStmts₁ (trNormal (Code.fix f) k) ∪ codeSupp f (Cont'.fix f k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm,
    Finset.union_left_idem]

@[simp]
theorem contSupp_cons₁ (fs k) :
    contSupp (Cont'.cons₁ fs k) =
      trStmts₁
          (move₂ (fun _ => false) main aux <|
            move₂ (fun s => s = Γ'.consₗ) stack main <|
              move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
        codeSupp fs (Cont'.cons₂ k) := by
  simp [codeSupp, contSupp]

@[simp]
theorem contSupp_cons₂ (k) :
    contSupp (Cont'.cons₂ k) = trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k :=
  rfl

@[simp]
theorem contSupp_comp (f k) : contSupp (Cont'.comp f k) = codeSupp f k :=
  rfl

theorem contSupp_fix (f k) : contSupp (Cont'.fix f k) = codeSupp f (Cont'.fix f k) := by
  simp +contextual [codeSupp, codeSupp', contSupp, Finset.union_assoc,
    Finset.subset_iff, -Finset.singleton_union, -Finset.union_singleton]

@[simp]
theorem contSupp_halt : contSupp Cont'.halt = ∅ :=
  rfl

/-- The statement `Λ'.Supports S q` means that `contSupp k ⊆ S` for any `ret k`
reachable from `q`.
(This is a technical condition used in the proof that the machine is supported.) -/
def Λ'.Supports (S : Finset Λ') : Λ' → Prop
  | Λ'.move _ _ _ q => Λ'.Supports S q
  | Λ'.push _ _ q => Λ'.Supports S q
  | Λ'.read q => ∀ s, Λ'.Supports S (q s)
  | Λ'.clear _ _ q => Λ'.Supports S q
  | Λ'.copy q => Λ'.Supports S q
  | Λ'.succ q => Λ'.Supports S q
  | Λ'.pred q₁ q₂ => Λ'.Supports S q₁ ∧ Λ'.Supports S q₂
  | Λ'.ret k => contSupp k ⊆ S

/-- A shorthand for the predicate that we are proving in the main theorems `trStmts₁_supports`,
`codeSupp'_supports`, `contSupp_supports`, `codeSupp_supports`. The set `S` is fixed throughout
the proof, and denotes the full set of states in the machine, while `K` is a subset that we are
currently proving a property about. The predicate asserts that every state in `K` is closed in `S`
under forward simulation, i.e. stepping forward through evaluation starting from any state in `K`
stays entirely within `S`. -/
def Supports (K S : Finset Λ') :=
  ∀ q ∈ K, TM2.SupportsStmt S (tr q)

theorem supports_insert {K S q} :
    Supports (insert q K) S ↔ TM2.SupportsStmt S (tr q) ∧ Supports K S := by simp [Supports]

theorem supports_singleton {S q} : Supports {q} S ↔ TM2.SupportsStmt S (tr q) := by simp [Supports]

theorem supports_union {K₁ K₂ S} : Supports (K₁ ∪ K₂) S ↔ Supports K₁ S ∧ Supports K₂ S := by
  simp [Supports, or_imp, forall_and]

theorem supports_biUnion {K : Option Γ' → Finset Λ'} {S} :
    Supports (Finset.univ.biUnion K) S ↔ ∀ a, Supports (K a) S := by
  simpa [Supports] using forall_comm

theorem head_supports {S k q} (H : (q : Λ').Supports S) : (head k q).Supports S := fun _ => by
  dsimp only; split_ifs <;> exact H

theorem ret_supports {S k} (H₁ : contSupp k ⊆ S) : TM2.SupportsStmt S (tr (Λ'.ret k)) := by
  have W := fun {q} => trStmts₁_self q
  cases k with
  | halt => trivial
  | cons₁ => rw [contSupp_cons₁, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | cons₂ => rw [contSupp_cons₂, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | comp => rw [contSupp_comp] at H₁; exact fun _ => H₁ (codeSupp_self _ _ W)
  | fix =>
    rw [contSupp_fix] at H₁
    have L := @Finset.mem_union_left; have R := @Finset.mem_union_right
    intro s; dsimp only; cases natEnd (s.getD default)
    · refine H₁ (R _ <| L _ <| R _ <| R _ <| L _ W)
    · exact H₁ (R _ <| L _ <| R _ <| R _ <| R _ <| Finset.mem_singleton_self _)

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
-- simp acts on multiple goals at the same time
theorem trStmts₁_supports {S q} (H₁ : (q : Λ').Supports S) (HS₁ : trStmts₁ q ⊆ S) :
    Supports (trStmts₁ q) S := by
  have W := fun {q} => trStmts₁_self q
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
    simp [trStmts₁, -Finset.singleton_subset_iff] at HS₁ ⊢
  any_goals
    obtain ⟨h₁, h₂⟩ := Finset.insert_subset_iff.1 HS₁
    first | have h₃ := h₂ W | try simp [Finset.subset_iff] at h₂
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₁⟩, q_ih H₁ h₂⟩ -- move
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₁⟩, q_ih H₁ h₂⟩ -- clear
  · exact supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₃⟩, q_ih H₁ h₂⟩ -- copy
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₃⟩, q_ih H₁ h₂⟩ -- push
  · refine supports_insert.2 ⟨fun _ => h₂ _ W, ?_⟩ -- read
    exact supports_biUnion.2 fun _ => q_ih _ (H₁ _) fun _ h => h₂ _ h
  · refine supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₂.1, fun _ => h₂.1⟩, ?_⟩ -- succ
    exact supports_insert.2 ⟨⟨fun _ => h₂.2 _ W, fun _ => h₂.1⟩, q_ih H₁ h₂.2⟩
  · refine -- pred
      supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₂.2 _ (Or.inl W),
                          fun _ => h₂.1, fun _ => h₂.1⟩, ?_⟩
    refine supports_insert.2 ⟨⟨fun _ => h₂.2 _ (Or.inr W), fun _ => h₂.1⟩, ?_⟩
    refine supports_union.2 ⟨?_, ?_⟩
    · exact q₁_ih H₁.1 fun _ h => h₂.2 _ (Or.inl h)
    · exact q₂_ih H₁.2 fun _ h => h₂.2 _ (Or.inr h)
  · exact supports_singleton.2 (ret_supports H₁)  -- ret

theorem trStmts₁_supports' {S q K} (H₁ : (q : Λ').Supports S) (H₂ : trStmts₁ q ∪ K ⊆ S)
    (H₃ : K ⊆ S → Supports K S) : Supports (trStmts₁ q ∪ K) S := by
  simp only [Finset.union_subset_iff] at H₂
  exact supports_union.2 ⟨trStmts₁_supports H₁ H₂.1, H₃ H₂.2⟩

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
theorem trNormal_supports {S c k} (Hk : codeSupp c k ⊆ S) : (trNormal c k).Supports S := by
  induction c generalizing k with simp [Λ'.Supports, head]
  | zero' => exact Finset.union_subset_right Hk
  | succ => intro; split_ifs <;> exact Finset.union_subset_right Hk
  | tail => exact Finset.union_subset_right Hk
  | cons f fs IHf _ =>
    apply IHf
    rw [codeSupp_cons] at Hk
    exact Finset.union_subset_right Hk
  | comp f g _ IHg => apply IHg; rw [codeSupp_comp] at Hk; exact Finset.union_subset_right Hk
  | case f g IHf IHg =>
    simp only [codeSupp_case, Finset.union_subset_iff] at Hk
    exact ⟨IHf Hk.2.1, IHg Hk.2.2⟩
  | fix f IHf => apply IHf; rw [codeSupp_fix] at Hk; exact Finset.union_subset_right Hk

theorem codeSupp'_supports {S c k} (H : codeSupp c k ⊆ S) : Supports (codeSupp' c k) S := by
  induction c generalizing k with
  | cons f fs IHf IHfs =>
    have H' := H; simp only [codeSupp_cons, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHf H'.2, ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun h => ?_
    · simp only [codeSupp, Finset.union_subset_iff, contSupp] at h H ⊢
      exact ⟨h.2.2.1, h.2.2.2, H.2⟩
    refine supports_union.2 ⟨IHfs ?_, ?_⟩
    · rw [codeSupp, contSupp_cons₁] at H'
      exact Finset.union_subset_right (Finset.union_subset_right H'.2)
    exact
      trStmts₁_supports (head_supports <| Finset.union_subset_right H)
        (Finset.union_subset_right h)
  | comp f g IHf IHg =>
    have H' := H; rw [codeSupp_comp] at H'; have H' := Finset.union_subset_right H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHg H', ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun _ => ?_
    · simp only [codeSupp', codeSupp, Finset.union_subset_iff] at h H ⊢
      exact ⟨h.2.2, H.2⟩
    exact IHf (Finset.union_subset_right H')
  | case f g IHf IHg =>
    have H' := H; simp only [codeSupp_case, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun _ => ?_
    exact supports_union.2 ⟨IHf H'.2.1, IHg H'.2.2⟩
  | fix f IHf =>
    have H' := H; simp only [codeSupp_fix, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHf H'.2, ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun _ => ?_
    · simp only [codeSupp', codeSupp, Finset.union_subset_iff, contSupp, trStmts₁,
        Finset.insert_subset_iff] at h H ⊢
      exact ⟨h.1, ⟨H.1.1, h⟩, H.2⟩
    exact supports_singleton.2 (ret_supports <| Finset.union_subset_right H)
  | _ => exact trStmts₁_supports (trNormal_supports H) (Finset.Subset.trans (codeSupp_self _ _) H)

theorem contSupp_supports {S k} (H : contSupp k ⊆ S) : Supports (contSupp k) S := by
  induction k with
  | halt => simp [contSupp_halt, Supports]
  | cons₁ f k IH =>
    have H₁ := H; rw [contSupp_cons₁] at H₁; have H₂ := Finset.union_subset_right H₁
    refine trStmts₁_supports' (trNormal_supports H₂) H₁ fun h => ?_
    refine supports_union.2 ⟨codeSupp'_supports H₂, ?_⟩
    simp only [codeSupp, contSupp_cons₂, Finset.union_subset_iff] at H₂
    exact trStmts₁_supports' (head_supports H₂.2.2) (Finset.union_subset_right h) IH
  | cons₂ k IH =>
    have H' := H; rw [contSupp_cons₂] at H'
    exact trStmts₁_supports' (head_supports <| Finset.union_subset_right H') H' IH
  | comp f k IH =>
    have H' := H; rw [contSupp_comp] at H'; have H₂ := Finset.union_subset_right H'
    exact supports_union.2 ⟨codeSupp'_supports H', IH H₂⟩
  | fix f k IH =>
    rw [contSupp] at H
    exact supports_union.2 ⟨codeSupp'_supports H, IH (Finset.union_subset_right H)⟩

theorem codeSupp_supports {S c k} (H : codeSupp c k ⊆ S) : Supports (codeSupp c k) S :=
  supports_union.2 ⟨codeSupp'_supports H, contSupp_supports (Finset.union_subset_right H)⟩

/-- The set `codeSupp c k` is a finite set that witnesses the effective finiteness of the `tr`
Turing machine. Starting from the initial state `trNormal c k`, forward simulation uses only
states in `codeSupp c k`, so this is a finite state machine. Even though the underlying type of
state labels `Λ'` is infinite, for a given partial recursive function `c` and continuation `k`,
only finitely many states are accessed, corresponding roughly to subterms of `c`. -/
theorem tr_supports (c k) : @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (codeSupp c k) :=
  ⟨codeSupp_self _ _ (trStmts₁_self _), fun _ => codeSupp_supports (Finset.Subset.refl _) _⟩

end

end PartrecToTM2

end Turing
