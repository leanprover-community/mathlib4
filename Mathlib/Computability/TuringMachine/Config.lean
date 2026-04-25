/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.PartrecBasis
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Modelling partial recursive functions using Turing machines

The files `Config` and `ToPartrec` define a simplified basis for partial recursive functions,
and a `Turing.TM2` model
Turing machine for evaluating these functions.
This amounts to a constructive proof that every
`Partrec` function can be evaluated by a Turing machine.

## Main definitions

* `ToPartrec.Code`: a simplified basis for partial recursive functions,
 valued in `List ℕ →. List ℕ`.
* `ToPartrec.Code.eval`: semantics for a `ToPartrec.Code` program
-/

@[expose] public section

open List (Vector)

open Function (update)

open Relation

namespace Turing

/-!
## A simplified basis for partrec

This section constructs the type `Code`, which is a data type of programs with `List ℕ` input and
output, with enough expressivity to write any partial recursive function.
The primitives are:

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there
  is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether
  it is zero or a successor (similar to `Nat.casesOn`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether
  to call `f` again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)

This basis is convenient because it is closer to the Turing machine model - the key operations are
splitting and merging of lists of unknown length, while the messy `n`-ary composition operation
from the traditional basis for partial recursive functions is absent - but it retains a
compositional semantics.
The first step in transitioning to Turing machines is to make a sequential
evaluator for this basis, which we take up in the next section.
-/


namespace ToPartrec

/-- The type of codes for primitive recursive functions. Unlike `Nat.Partrec.Code`, this uses a set
of operations on `List ℕ`.
See `Code.eval` for a description of the behavior of the primitives. -/
inductive Code
  | zero'
  | succ
  | tail
  | cons : Code → Code → Code
  | comp : Code → Code → Code
  | case : Code → Code → Code
  | fix : Code → Code
  deriving DecidableEq, Inhabited

/-- The semantics of the `Code` primitives, as partial functions `List ℕ →. List ℕ`.
By convention, functions that return a single result return a singleton `[n]`,
or in some cases `n :: v` where `v` will be ignored by a subsequent function.

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there
  is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether
  it is zero or a successor (similar to `Nat.casesOn`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether
  to call `f` again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)
-/
def Code.eval : Code → List ℕ →. List ℕ
  | Code.zero' => PFun.lift fun v => 0 :: v
  | Code.succ => PFun.lift fun v => [v.headI.succ]
  | Code.tail => PFun.lift fun v => v.tail
  | Code.cons f fs => PFun.mk fun v =>
    f.eval v >>= fun n => fs.eval v >>= fun ns => pure (n.headI :: ns)
  | Code.comp f g => PFun.mk fun v => g.eval v >>= fun x => f.eval x
  | Code.case f g => PFun.mk fun v => v.headI.rec (f.eval v.tail) (fun y _ => g.eval (y::v.tail))
  | Code.fix f =>
    PFun.fix (PFun.mk fun v => (f.eval v).map fun v' =>
      if v'.headI = 0 then Sum.inl v'.tail else Sum.inr v'.tail)

namespace Code

@[simp] theorem zero'_eval (v) : zero'.eval v = pure (0 :: v) := rfl

@[simp] theorem succ_eval (v) : succ.eval v = pure [v.headI.succ] := rfl

@[simp] theorem tail_eval (v) : tail.eval v = pure v.tail := rfl

@[simp] theorem cons_eval (f fs v) :
    (cons f fs).eval v = (f.eval v >>= fun n => fs.eval v >>= fun ns => pure (n.headI :: ns)) := rfl

@[simp] theorem comp_eval (f g v) :
    (comp f g).eval v = (g.eval v >>= fun x => f.eval x) := rfl

@[simp] theorem case_eval (f g v) :
    (case f g).eval v = v.headI.rec (f.eval v.tail) (fun y _ => g.eval (y::v.tail)) := rfl

@[simp] theorem fix_eval (f v) :
    (fix f).eval v =
      PFun.fix (PFun.mk fun v' => (f.eval v').map fun v'' =>
        if v''.headI = 0 then Sum.inl v''.tail else Sum.inr v''.tail) v := rfl

/-- `nil` is the constant nil function: `nil v = []`. -/
def nil : Code :=
  tail.comp succ

@[simp]
theorem nil_eval (v) : nil.eval v = pure [] := by simp [nil]

/-- `id` is the identity function: `id v = v`. -/
def id : Code :=
  tail.comp zero'

@[simp]
theorem id_eval (v) : id.eval v = pure v := by simp [id]

/-- `head` gets the head of the input list: `head [] = [0]`, `head (n :: v) = [n]`. -/
def head : Code :=
  cons id nil

@[simp]
theorem head_eval (v) : head.eval v = pure [v.headI] := by simp [head]

/-- `zero` is the constant zero function: `zero v = [0]`. -/
def zero : Code :=
  cons zero' nil

@[simp]
theorem zero_eval (v) : zero.eval v = pure [0] := by simp [zero]

/-- `pred` returns the predecessor of the head of the input:
`pred [] = [0]`, `pred (0 :: v) = [0]`, `pred (n+1 :: v) = [n]`.
-/
def pred : Code :=
  case zero head

@[simp]
theorem pred_eval (v) : pred.eval v = pure [v.headI.pred] := by
  simp [pred];
  cases v.headI <;> simp

/-- `rfind f` performs the function of the `rfind` primitive of partial recursive functions.
`rfind f v` returns the smallest `n` such that `(f (n :: v)).head = 0`.

It is implemented as:

    rfind f v = pred (fix (fun (n::v) => f (n::v) :: n+1 :: v) (0 :: v))

The idea is that the initial state is `0 :: v`, and the `fix` keeps `n :: v` as its internal state;
it calls `f (n :: v)` as the exit test and `n+1 :: v` as the next state.
At the end we get
`n+1 :: v` where `n` is the desired output, and `pred (n+1 :: v) = [n]` returns the result.
-/
def rfind (f : Code) : Code :=
  comp pred <|
    comp (fix <| cons f <| cons succ tail) zero'

/-- `prec f g` implements the `prec` (primitive recursion) operation of partial recursive
functions.
`prec f g` evaluates as:

* `prec f g [] = [f []]`
* `prec f g (0 :: v) = [f v]`
* `prec f g (n+1 :: v) = [g (n :: prec f g (n :: v) :: v)]`

It is implemented as:

    G (a :: b :: IH :: v) = (b :: a+1 :: b-1 :: g (a :: IH :: v) :: v)
    F (0 :: f_v :: v) = (f_v :: v)
    F (n+1 :: f_v :: v) = (fix G (0 :: n :: f_v :: v)).tail.tail

    prec f g (a :: v) = [(F (a :: f v :: v)).head]

Because `fix` always evaluates its body at least once, we must special case the `0` case to avoid
calling `g` more times than necessary (which could be bad if `g` diverges).
If the input is
`0 :: v`, then `F (0 :: f v :: v) = (f v :: v)` so we return `[f v]`.
If the input is `n+1 :: v`,
we evaluate the function from the bottom up, with initial state `0 :: n :: f v :: v`.
The first
number counts up, providing arguments for the applications to `g`, while the second number counts
down, providing the exit condition (this is the initial `b` in the return value of `G`, which is
stripped by `fix`).
After the `fix` is complete, the final state is `n :: 0 :: res :: v` where
`res` is the desired result, and the rest reduces this to `[res]`.
-/
def prec (f g : Code) : Code :=
  let G :=
    cons tail <|
      cons succ <|
        cons (comp pred tail) <|
          cons (comp g <| cons id <| comp tail tail) <|
            comp tail <| comp tail tail
  let F := case id <|
    comp (comp (comp tail tail) (fix G)) zero'
  cons (comp F (cons head <| cons (comp f tail) tail)) nil

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

-- TODO: golf this proof (PFun refactor)
theorem exists_code.comp {m n} {f : List.Vector ℕ n →. ℕ} {g : Fin n → List.Vector ℕ m →. ℕ}
    (hf : ∃ c : Code, ∀ v : List.Vector ℕ n, c.eval v.1 = pure <$> f v)
    (hg : ∀ i, ∃ c : Code, ∀ v : List.Vector ℕ m, c.eval v.1 = pure <$> g i v) :
    ∃ c : Code, ∀ v : List.Vector ℕ m,
      c.eval v.1 = pure <$> ((List.Vector.mOfFn fun i => g i v) >>= f) := by
  rsuffices ⟨cg, hg⟩ :
    ∃ c : Code, ∀ v : List.Vector ℕ m,
      c.eval v.1 = Subtype.val <$> List.Vector.mOfFn fun i => g i v
  · obtain ⟨cf, hf⟩ := hf
    exact
      ⟨cf.comp cg, fun v => by
        simp [hg, hf, map_bind]
        rfl⟩
  clear hf f
  induction n with
  | zero => exact ⟨nil, fun v => by simp [Vector.mOfFn]; rfl⟩
  | succ n IH =>
    obtain ⟨cg, hg₁⟩ := hg 0
    obtain ⟨cl, hl⟩ := IH fun i => hg i.succ
    exact
      ⟨cons cg cl, fun v => by
        simp [Vector.mOfFn, hg₁, hl]
        rfl⟩

-- TODO: fix non-terminal simp (operates on two goals, with long simp sets)
set_option backward.isDefEq.respectTransparency false in
theorem exists_code {n} {f : List.Vector ℕ n →. ℕ} (hf : Nat.Partrec' f) :
    ∃ c : Code, ∀ v : List.Vector ℕ n, c.eval v.1 = pure <$> f v := by
  induction hf with
  | prim hf =>
    induction hf with
    | zero => exact ⟨zero', fun ⟨[], _⟩ => rfl⟩
    | succ => exact ⟨succ, fun ⟨[v], _⟩ => rfl⟩
    | get i =>
      refine Fin.succRec (fun n => ?_) (fun n i IH => ?_) i
      · exact ⟨head, fun ⟨List.cons a as, _⟩ => by simp [Code.head_eval]; rfl⟩
      · obtain ⟨c, h⟩ := IH
        exact ⟨c.comp tail, fun v => by simpa [← Vector.get_tail, Bind.bind] using h v.tail⟩
    | comp g hf hg IHf IHg =>
      simpa [Part.bind_eq_bind] using exists_code.comp IHf IHg
    | @prec n' f g _ _ IHf IHg =>
      obtain ⟨cf, hf⟩ := IHf
      obtain ⟨cg, hg⟩ := IHg
      simp only [Part.map_eq_map, Part.map_some, PFun.coe_val] at hf hg
      refine ⟨prec cf cg, fun v => ?_⟩
      rw [← v.cons_head_tail]
      specialize hf v.tail
      replace hg := fun a b => hg (a ::ᵥ b ::ᵥ v.tail)
      simp only [Vector.cons_val, Vector.tail_val] at hf hg
      simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, Vector.tail_cons,
        Vector.head_cons, PFun.coe_val, Vector.tail_val]
      simp only [← Part.pure_eq_some] at hf hg ⊢
      induction v.head with
      | zero =>
        simp [prec, Code.fix_eval, Code.cons_eval, Code.comp_eval, Code.tail_eval,
          Code.succ_eval, Code.pred_eval, Code.id_eval, Code.case_eval, Code.zero'_eval,
          Part.bind_assoc, ← Part.bind_some_eq_map, Bind.bind, hf, Part.bind_some]
      | succ n' _ =>
        simp only [prec, Code.case_eval, Code.cons_eval, Code.comp_eval, Code.fix_eval,
          Code.tail_eval, Code.succ_eval, Code.pred_eval, Code.id_eval, Code.zero'_eval,
          Part.bind_assoc, ← Part.bind_some_eq_map, Bind.bind]
        suffices ∀ a b, a + b = n' →
          (n'.succ :: 0 ::
            g (n' ::ᵥ Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) n' ::ᵥ
              v.tail) ::
            v.val.tail : List ℕ) ∈
            PFun.fix
              (PFun.mk fun v : List ℕ => Part.bind (cg.eval (v.headI :: v.tail.tail))
                (fun x => Part.some (if v.tail.headI = 0
                  then Sum.inl
                    (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail : List ℕ)
                  else Sum.inr
                    (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail))))
              (a :: b :: Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) a :: v.val.tail)
                by
          have := Part.eq_some_iff.mpr (this _ _ (zero_add _))
          simp_all
        intro a b e
        induction b generalizing a with
        | zero =>
          have : a = n' := by omega
          subst this
          refine PFun.mem_fix_iff.2 (Or.inl ?_)
          simp only [hg, PFun.coe_mk, pure, Part.bind_some, List.tail_cons,
            List.headI, Nat.pred_zero, Part.mem_some_iff]
          rfl
        | succ b' IH =>
          refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, IH (a + 1) (by omega)⟩)
          simp only [hg, PFun.coe_mk, pure, Part.bind_some, List.tail_cons,
            List.headI, if_neg (Nat.succ_ne_zero b'), Part.mem_some_iff]
          congr 3
  | comp g _ _ IHf IHg => exact exists_code.comp IHf IHg
  | @rfind n_val f _ IHf =>
    obtain ⟨cf, hf⟩ := IHf
    refine ⟨rfind cf, fun v => ?_⟩
    replace hf := fun a => hf (a ::ᵥ v)
    simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val,
      show ∀ x, pure x = [x] from fun _ => rfl] at hf ⊢
    refine Part.ext fun x => ?_
    simp only [rfind, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some,
      Code.cons_eval, Code.comp_eval, Code.fix_eval, Code.tail_eval, Code.succ_eval,
      Code.zero'_eval, Code.pred_eval, Part.map_some, Part.mem_bind_iff, Part.mem_map_iff,
      List.tail_cons, Part.mem_some_iff, Part.map_bind]
    constructor
    · rintro ⟨v', h1, rfl⟩
      suffices ∀ v₁ : List ℕ, v' ∈ PFun.fix
        (PFun.mk fun v => (cf.eval v).bind fun y => Part.some <|
          if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
            else Sum.inr (v.headI.succ :: v.tail)) v₁ →
        ∀ n', (v₁ = n' :: v.val) → (∀ m < n', ¬f (m ::ᵥ v) = 0) →
          ∃ a : ℕ,
            (f (a ::ᵥ v) = 0 ∧ ∀ {m : ℕ}, m < a → ¬f (m ::ᵥ v) = 0) ∧ [a] = [v'.headI.pred]
        by
          obtain ⟨a, ⟨ha1, ha2⟩, eq⟩ := this _ h1 0 rfl (fun m hm => (Nat.not_lt_zero m hm).elim)
          refine ⟨a, ?_, eq⟩
          apply Nat.mem_rfind.mpr
          constructor
          · simp only [PFun.lift, PFun.coe_mk, Part.mem_some_iff]
            exact (decide_eq_true ha1).symm
          · intro m hm
            simp only [PFun.lift, PFun.coe_mk, Part.mem_some_iff]
            exact (decide_eq_false (ha2 hm)).symm
      intro v₀ h1
      refine PFun.fixInduction h1 fun v₁ h2 IH => ?_
      rintro n' rfl hm
      have := PFun.mem_fix_iff.1 h2
      simp only [PFun.coe_mk, hf n', Part.bind_some] at this
      split_ifs at this with h
      · simp only [exists_false, or_false, Part.mem_some_iff,
          List.tail_cons, false_and, Sum.inl.injEq, reduceCtorEq, List.headI] at this
        subst this
        exact ⟨n', ⟨h, fun {m} => hm m⟩, rfl⟩
      · refine IH (n'.succ::v.val) (by simp_all) _ rfl fun m h_lt => ?_
        obtain h_eq | rfl := Nat.lt_succ_iff_lt_or_eq.1 h_lt
        · exact hm m h_eq
        · exact h
    · rintro ⟨n', hn_mem, rfl⟩
      have h_zero : f (n' ::ᵥ v) = 0 := by
        have h_spec := Nat.rfind_spec hn_mem
        simp only [PFun.lift, PFun.coe_mk, Part.mem_some_iff] at h_spec
        exact of_decide_eq_true h_spec.symm
      have h_min : ∀ m < n', ¬f (m ::ᵥ v) = 0 := by
        intro m hm
        have h_min_spec := Nat.rfind_min hn_mem hm
        simp only [PFun.lift, PFun.coe_mk, Part.mem_some_iff] at h_min_spec
        exact of_decide_eq_false h_min_spec.symm
      refine ⟨n'.succ::v.1, ?_, rfl⟩
      have : (n'.succ::v.1 : List ℕ) ∈
        PFun.fix (PFun.mk fun v =>
          (cf.eval v).bind fun y =>
            Part.some <|
              if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
                else Sum.inr (v.headI.succ :: v.tail))
            (n'::v.val) :=
        PFun.mem_fix_iff.2 (Or.inl (by simp [hf, h_zero]))
      generalize (n'.succ :: v.1 : List ℕ) = w at this ⊢
      clear h_zero hn_mem
      revert h_min this
      induction n' with
      | zero =>
        intro _ h_this
        exact h_this
      | succ n'' IH =>
        intro h_min h_this
        have h_rec := IH (fun m h_lt => h_min m (Nat.lt_succ_of_lt h_lt))
        refine h_rec (PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, h_this⟩))
        have h_nz : f (n'' ::ᵥ v) ≠ 0 := h_min n'' (Nat.lt_succ_self n'')
        simp only [hf, PFun.coe_mk, Part.bind_some, List.headI, List.tail_cons]
        split_ifs with h_eq
        · exact False.elim (h_nz h_eq)
        · exact Part.mem_some_iff.2 rfl
end Code

/-!
## From compositional semantics to sequential semantics

Our initial sequential model is designed to be as similar as possible to the compositional
semantics in terms of its primitives, but it is a sequential semantics, meaning that rather than
defining an `eval c : List ℕ →. List ℕ` function for each program, defined by recursion on
programs, we have a type `Cfg` with a step function `step : Cfg → Option cfg` that provides a
deterministic evaluation order.
In order to do this, we introduce the notion of a *continuation*,
which can be viewed as a `Code` with a hole in it where evaluation is currently taking place.
Continuations can be assigned a `List ℕ →. List ℕ` semantics as well, with the interpretation
being that given a `List ℕ` result returned from the code in the hole, the remainder of the
program will evaluate to a `List ℕ` final value.

The continuations are:

* `halt`: the empty continuation: the hole is the whole program, whatever is returned is the
  final result.
In our notation this is just `_`.
* `cons₁ fs v k`: evaluating the first part of a `cons`, that is `k (_ :: fs v)`, where `k` is the
  outer continuation.
* `cons₂ ns k`: evaluating the second part of a `cons`: `k (ns.headI :: _)`.
  (Technically we don't
  need to hold on to all of `ns` here since we are already committed to taking the head, but this
  is more regular.)
* `comp f k`: evaluating the first part of a composition: `k (f _)`.
* `fix f k`: waiting for the result of `f` in a `fix f` expression:
  `k (if _.headI = 0 then _.tail else fix f (_.tail))`

The type `Cfg` of evaluation states is:

* `halt v`: The machine is about to stop and `v : List ℕ` is the result.
* `ret k v`: The machine is about to pass `v : List ℕ` to continuation `k : Cont`.
We don't have a state corresponding to normal evaluation because these are evaluated immediately
to a `ret` "in zero steps" using the `stepNormal` function.
-/


/-- The type of continuations, built up during evaluation of a `Code` expression. -/
inductive Cont
  | halt
  | cons₁ : Code → List ℕ → Cont → Cont
  | cons₂ : List ℕ → Cont → Cont
  | comp : Code → Cont → Cont
  | fix : Code → Cont → Cont
  deriving Inhabited

/-- The semantics of a continuation.
-/
def Cont.eval : Cont → List ℕ →. List ℕ
  | Cont.halt => PFun.id _
  | Cont.cons₁ fs as k => PFun.mk fun v =>
    Code.eval fs as >>= fun ns => Cont.eval k (v.headI :: ns)
  | Cont.cons₂ ns k => PFun.mk fun v => Cont.eval k (ns.headI :: v)
  | Cont.comp f k => PFun.mk fun v => Code.eval f v >>= Cont.eval k
  | Cont.fix f k => PFun.mk fun v =>
    if v.headI = 0 then k.eval v.tail else f.fix.eval v.tail >>= k.eval

namespace Cont

@[simp, grind =] theorem halt_eval (v) : halt.eval v = pure v := rfl

@[simp, grind =] theorem cons₁_eval (fs as k v) :
    (cons₁ fs as k).eval v = (Code.eval fs as >>= fun ns => k.eval (v.headI :: ns)) := rfl

@[simp, grind =] theorem cons₂_eval (ns k v) :
 (cons₂ ns k).eval v = k.eval (ns.headI :: v) := rfl

@[simp, grind =] theorem comp_eval (f k v) : (comp f k).eval v = (Code.eval f v >>= k.eval) := rfl

@[simp, grind =] theorem fix_eval (f k v) :
    (fix f k).eval v =
      (if v.headI = 0 then k.eval v.tail else f.fix.eval v.tail >>= k.eval) := rfl

end Cont

/-- The set of configurations of the machine:

* `halt v`: The machine is about to stop and `v : List ℕ` is the result.
* `ret k v`: The machine is about to pass `v : List ℕ` to continuation `k : Cont`.
We don't have a state corresponding to normal evaluation because these are evaluated immediately
to a `ret` "in zero steps" using the `stepNormal` function.
-/
inductive Cfg
  | halt : List ℕ → Cfg
  | ret : Cont → List ℕ → Cfg
  deriving Inhabited

/-- Evaluating `c : Code` in a continuation `k : Cont` and input `v : List ℕ`.
This goes by
recursion on `c`, building an augmented continuation and a value to pass to it.
* `zero' v = 0 :: v` evaluates immediately, so we return it to the parent continuation
* `succ v = [v.headI.succ]` evaluates immediately, so we return it to the parent continuation
* `tail v = v.tail` evaluates immediately, so we return it to the parent continuation
* `cons f fs v = (f v).headI :: fs v` requires two sub-evaluations, so we evaluate
  `f v` in the continuation `k (_.headI :: fs v)` (called `Cont.cons₁ fs v k`)
* `comp f g v = f (g v)` requires two sub-evaluations, so we evaluate
  `g v` in the continuation `k (f _)` (called `Cont.comp f k`)
* `case f g v = v.head.casesOn (f v.tail) (fun n => g (n :: v.tail))` has the information needed
  to evaluate the case statement, so we do that and transition to either
  `f v` or `g (n :: v.tail)`.
* `fix f v = let v' := f v; if v'.headI = 0 then k v'.tail else fix f v'.tail`
  needs to first evaluate `f v`, so we do that and leave the rest for the continuation (called
  `Cont.fix f k`)
-/
def stepNormal : Code → Cont → List ℕ → Cfg
  | Code.zero' => fun k v => Cfg.ret k (0::v)
  | Code.succ => fun k v => Cfg.ret k [v.headI.succ]
  | Code.tail => fun k v => Cfg.ret k v.tail
  | Code.cons f fs => fun k v => stepNormal f (Cont.cons₁ fs v k) v
  | Code.comp f g => fun k v => stepNormal g (Cont.comp f k) v
  | Code.case f g => fun k v =>
    v.headI.rec (stepNormal f k v.tail) fun y _ => stepNormal g k (y::v.tail)
  | Code.fix f => fun k v => stepNormal f (Cont.fix f k) v

/-- Evaluating a continuation `k : Cont` on input `v : List ℕ`.
This is the second part of
evaluation, when we receive results from continuations built by `stepNormal`.
* `Cont.halt v = v`, so we are done and transition to the `Cfg.halt v` state
* `Cont.cons₁ fs as k v = k (v.headI :: fs as)`, so we evaluate `fs as` now with the continuation
  `k (v.headI :: _)` (called `cons₂ v k`).
* `Cont.cons₂ ns k v = k (ns.headI :: v)`, where we now have everything we need to evaluate
  `ns.headI :: v`, so we return it to `k`.
* `Cont.comp f k v = k (f v)`, so we call `f v` with `k` as the continuation.
* `Cont.fix f k v = k (if v.headI = 0 then k v.tail else fix f v.tail)`, where `v` is a
  value, so we evaluate the if statement and either call `k` with `v.tail`, or call
  `fix f v` with `k` as the continuation (which immediately calls `f` with
  `Cont.fix f k` as the continuation).
-/
def stepRet : Cont → List ℕ → Cfg
  | Cont.halt, v => Cfg.halt v
  | Cont.cons₁ fs as k, v => stepNormal fs (Cont.cons₂ v k) as
  | Cont.cons₂ ns k, v => stepRet k (ns.headI :: v)
  | Cont.comp f k, v => stepNormal f k v
  | Cont.fix f k, v => if v.headI = 0 then stepRet k v.tail else stepNormal f (Cont.fix f k) v.tail

/-- If we are not done (in `Cfg.halt` state), then we must be still stuck on a continuation, so
this main loop calls `stepRet` with the new continuation.
The overall `step` function transitions
from one `Cfg` to another, only halting at the `Cfg.halt` state.
-/
def step : Cfg → Option Cfg
  | Cfg.halt _ => none
  | Cfg.ret k v => some (stepRet k v)

/-- In order to extract a compositional semantics from the sequential execution behavior of
configurations, we observe that continuations have a monoid structure, with `Cont.halt` as the unit
and `Cont.then` as the multiplication.
`Cont.then k₁ k₂` runs `k₁` until it halts, and then takes
the result of `k₁` and passes it to `k₂`.
We will not prove it is associative (although it is), but we are instead interested in the
associativity law `k₂ (eval c k₁) = eval c (k₁.then k₂)`.
This holds at both the sequential and
compositional levels, and allows us to express running a machine without the ambient continuation
and relate it to the original machine's evaluation steps.
In the literature this is usually
where one uses Turing machines embedded inside other Turing machines, but this approach allows us
to avoid changing the ambient type `Cfg` in the middle of the recursion.
-/
def Cont.then : Cont → Cont → Cont
  | Cont.halt => fun k' => k'
  | Cont.cons₁ fs as k => fun k' => Cont.cons₁ fs as (k.then k')
  | Cont.cons₂ ns k => fun k' => Cont.cons₂ ns (k.then k')
  | Cont.comp f k => fun k' => Cont.comp f (k.then k')
  | Cont.fix f k => fun k' => Cont.fix f (k.then k')

theorem Cont.then_eval {k k' : Cont} {v} : (k.then k').eval v = k.eval v >>= k'.eval := by
  induction k generalizing v with
  | halt => simp only [Cont.halt_eval, Cont.then, pure_bind]
  | cons₁ fs as k k_ih => simp only [Cont.cons₁_eval, Cont.then, bind_assoc, k_ih]
  | cons₂ ns k k_ih => simp only [Cont.cons₂_eval, Cont.then, k_ih]
  | comp f k k_ih =>
    simp only [Cont.comp_eval, Cont.then, bind_assoc]
    congr 1
    funext x
    exact k_ih
  | fix f k k_ih =>
    simp only [Cont.fix_eval, Cont.then]
    split_ifs
    · exact k_ih
    · simp only [bind_assoc]
      congr 1
      funext x
      exact k_ih

/-- The `then k` function is a "configuration homomorphism".
Its operation on states is to append
`k` to the continuation of a `Cfg.ret` state, and to run `k` on `v` if we are in the `Cfg.halt v`
state.
-/
def Cfg.then : Cfg → Cont → Cfg
  | Cfg.halt v => fun k' => stepRet k' v
  | Cfg.ret k v => fun k' => Cfg.ret (k.then k') v

/-- The `stepNormal` function respects the `then k'` homomorphism.
Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state.
-/
theorem stepNormal_then (c) (k k' : Cont) (v) :
    stepNormal c (k.then k') v = (stepNormal c k v).then k' := by
  induction c generalizing k v with simp only [stepNormal, *]
  | cons c c' ih _ => rw [← ih, Cont.then]
  | comp c c' _ ih' => rw [← ih', Cont.then]
  | case => cases v.headI <;> simp only [Nat.rec_zero]
  | fix c ih => rw [← ih, Cont.then]
  | _ => simp only [Cfg.then]

/-- The `stepRet` function respects the `then k'` homomorphism.
Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state.
-/
theorem stepRet_then {k k' : Cont} {v} : stepRet (k.then k') v = (stepRet k v).then k' := by
  induction k generalizing v with simp only [Cont.then, stepRet, *]
  | cons₁ =>
    rw [← stepNormal_then]
    rfl
  | comp =>
    rw [← stepNormal_then]
  | fix _ _ k_ih =>
    split_ifs
    · rw [← k_ih]
    · rw [← stepNormal_then]
      rfl
  | _ => simp only [Cfg.then]

open StateTransition

/-- This is a temporary definition, because we will prove in `code_is_ok` that it always holds.
It asserts that `c` is semantically correct; that is, for any `k` and `v`,
`eval (stepNormal c k v) = eval (Cfg.ret k (Code.eval c v))`, as an equality of partial values
(so one diverges iff the other does).
In particular, we can let `k = Cont.halt`, and then this asserts that `stepNormal c Cont.halt v`
evaluates to `Cfg.halt (Code.eval c v)`.
-/
def Code.Ok (c : Code) :=
  ∀ k v, StateTransition.eval step (stepNormal c k v) =
    Code.eval c v >>= fun v => StateTransition.eval step (Cfg.ret k v)

theorem Code.Ok.zero {c} (h : Code.Ok c) {v} :
    StateTransition.eval step (stepNormal c Cont.halt v) = Cfg.halt <$> Code.eval c v := by
  rw [h, ← bind_pure_comp];
  congr; funext v
  exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.single rfl, rfl⟩)

theorem stepNormal.is_ret (c : Code) (k : Cont) (v : List ℕ) :
    ∃ k' v', stepNormal c k v = Cfg.ret k' v' := by
  induction c generalizing k v <;> try exact ⟨_, _, rfl⟩
  case cons IHf _ => apply IHf
  case comp _ IHg => apply IHg
  case case IHf IHg => unfold stepNormal; cases v.headI <;> [apply IHf; apply IHg]
  case fix IHf => apply IHf

-- TODO: golf this proof (PFun refactor)
theorem cont_eval_fix {f k v} (fok : Code.Ok f) :
    eval step (stepNormal f (Cont.fix f k) v) =
      f.fix.eval v >>= fun v => eval step (Cfg.ret k v) := by
  refine Part.ext fun x => ?_
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · suffices ∀ c, x ∈ eval step c → ∀ v c', c = Cfg.then c' (Cont.fix f k) →
      Reaches step (stepNormal f Cont.halt v) c' →
        ∃ v₁ ∈ f.eval v, ∃ v₂ ∈ if v₁.headI = 0 then pure v₁.tail else f.fix.eval v₁.tail,
          x ∈ eval step (Cfg.ret k v₂) by
      intro h
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (stepNormal_then _ Cont.halt _ _) ReflTransGen.refl
      refine ⟨v₂, PFun.mem_fix_iff.2 ?_, h₃⟩
      -- We explicitly unfold the PFun structure here
      simp only [PFun.coe_mk, Part.eq_some_iff.2 hv₁, Part.map_some]
      split_ifs at hv₂ ⊢
      · rw [Part.mem_some_iff.1 hv₂]
        exact Or.inl (Part.mem_some _)
      · exact Or.inr ⟨_, Part.mem_some _, hv₂⟩
    refine fun c he => evalInduction he fun y h IH => ?_
    rintro v (⟨v'⟩ | ⟨k', v'⟩) rfl hr <;> rw [Cfg.then] at h IH <;> simp only [] at h IH
    · have := mem_eval.2 ⟨hr, rfl⟩
      rw [fok, Part.bind_eq_bind, Part.mem_bind_iff] at this
      obtain ⟨v'', h₁, h₂⟩ := this
      rw [reaches_eval] at h₂
      swap
      · exact ReflTransGen.single rfl
      cases Part.mem_unique h₂ (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
      refine ⟨v', h₁, ?_⟩
      rw [stepRet] at h
      revert h
      by_cases he : v'.headI = 0 <;> simp only [if_pos, if_false, he] <;> intro h
      · refine ⟨_, Part.mem_some _, ?_⟩
        rw [reaches_eval]
        · exact h
        exact ReflTransGen.single rfl
      · obtain ⟨k₀, v₀, e₀⟩ := stepNormal.is_ret f Cont.halt v'.tail
        have e₁ := stepNormal_then f Cont.halt (Cont.fix f k) v'.tail
        rw [e₀, Cont.then, Cfg.then] at e₁
        simp only [] at e₁
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (stepRet (k₀.then (Cont.fix f k)) v₀)
            (by rw [stepRet, if_neg he, e₁]; rfl) v'.tail _ stepRet_then
            (by apply ReflTransGen.single; rw [e₀]; rfl)
        refine ⟨_, PFun.mem_fix_iff.2 ?_, h₃⟩
        simp only [PFun.coe_mk, Part.eq_some_iff.2 hv₁, Part.map_some, Part.mem_some_iff]
        split_ifs at hv₂ ⊢ <;> [exact Or.inl (congr_arg Sum.inl (Part.mem_some_iff.1 hv₂));
        exact Or.inr ⟨_, rfl, hv₂⟩]
    · exact IH _ rfl _ _ stepRet_then (ReflTransGen.tail hr rfl)
  · rintro ⟨v', he, hr⟩
    rw [reaches_eval] at hr
    swap
    · exact ReflTransGen.single rfl
    refine PFun.fixInduction he fun v (he : v' ∈ f.fix.eval v) IH => ?_
    rw [fok, Part.bind_eq_bind, Part.mem_bind_iff]
    have he_fix := PFun.mem_fix_iff.1 he
    simp only [PFun.coe_mk] at he_fix
    obtain he | ⟨v'', he₁', _⟩ := he_fix
    · obtain ⟨v_tmp, he₁, he₂⟩ := (Part.mem_map_iff _).1 he
      split_ifs at he₂ with h;
      cases he₂
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rwa [stepRet, if_pos h]
    · obtain ⟨v₁, he₁, he₂⟩ := (Part.mem_map_iff _).1 he₁'
      split_ifs at he₂ with h;
      cases he₂
      clear he₁'
      refine ⟨_, he₁, ?_⟩
      rw [reaches_eval]
      swap
      · exact ReflTransGen.single rfl
      rw [stepRet, if_neg h]
      exact IH v₁.tail ((Part.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩)

theorem code_is_ok (c) : Code.Ok c := by
  induction c with (intro k v; rw [stepNormal])
  | cons f fs IHf IHfs =>
    rw [Code.cons_eval, IHf]
    simp only [bind_assoc, pure_bind]; congr;
    funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet, IHfs];
    congr; funext v''
    refine Eq.trans (b := eval step (stepRet (Cont.cons₂ v' k) v'')) ?_ (Eq.symm ?_) <;>
      exact reaches_eval (ReflTransGen.single rfl)
  | comp f g IHf IHg =>
    rw [Code.comp_eval, IHg]
    simp only [bind_assoc]; congr;
    funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet, IHf]
  | case f g IHf IHg =>
    rw [Code.case_eval]
    dsimp only
    generalize he : v.headI = h
    cases h with
    | zero => exact IHf k v.tail
    | succ n => exact IHg k (n :: v.tail)
  | fix f IHf => rw [cont_eval_fix IHf]
  | zero' => rw [Code.zero'_eval]; exact (pure_bind _ _).symm
  | succ => rw [Code.succ_eval]; exact (pure_bind _ _).symm
  | tail => rw [Code.tail_eval]; exact (pure_bind _ _).symm

theorem stepNormal_eval (c v) : eval step (stepNormal c Cont.halt v) = Cfg.halt <$> c.eval v :=
  (code_is_ok c).zero

theorem stepRet_eval {k v} : eval step (stepRet k v) = Cfg.halt <$> k.eval v := by
  induction k generalizing v with
  | halt =>
    rw [Cont.halt_eval, map_pure]
    exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
  | cons₁ fs as k IH =>
    rw [Cont.cons₁_eval, stepRet, code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]
    congr
    funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [stepRet, IH, bind_pure_comp]
  | cons₂ ns k IH =>
    rw [Cont.cons₂_eval, stepRet]
    exact IH
  | comp f k IH =>
    rw [Cont.comp_eval, stepRet, code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]
    congr
    funext v'
    rw [reaches_eval]; swap
    · exact ReflTransGen.single rfl
    rw [IH, bind_pure_comp]
  | fix f k IH =>
    rw [Cont.fix_eval, stepRet]
    split_ifs
    · exact IH
    · rw [cont_eval_fix (code_is_ok f)]
      simp only [← bind_pure_comp, bind_assoc]
      congr;
      funext x; rw [bind_pure_comp, ← IH]
      exact reaches_eval (ReflTransGen.single rfl)

end ToPartrec

end Turing
