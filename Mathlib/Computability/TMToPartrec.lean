/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Computability.Halting
import Mathlib.Computability.TuringMachine
import Mathlib.Data.Num.Lemmas
import Mathlib.Tactic.DeriveFintype

#align_import computability.tm_to_partrec from "leanprover-community/mathlib"@"6155d4351090a6fad236e3d2e4e0e4e7342668e8"

/-!
# Modelling partial recursive functions using Turing machines

This file defines a simplified basis for partial recursive functions, and a `Turing.TM2` model
Turing machine for evaluating these functions. This amounts to a constructive proof that every
`Partrec` function can be evaluated by a Turing machine.

## Main definitions

* `ToPartrec.Code`: a simplified basis for partial recursive functions, valued in
  `List ℕ →. List ℕ`.
  * `ToPartrec.Code.eval`: semantics for a `ToPartrec.Code` program
* `PartrecToTM2.tr`: A TM2 turing machine which can evaluate `code` programs
-/


open Function (update)

open Relation

namespace Turing

/-!
## A simplified basis for partrec

This section constructs the type `Code`, which is a data type of programs with `List ℕ` input and
output, with enough expressivity to write any partial recursive function. The primitives are:

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `nat.cases_on`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)

This basis is convenient because it is closer to the Turing machine model - the key operations are
splitting and merging of lists of unknown length, while the messy `n`-ary composition operation
from the traditional basis for partial recursive functions is absent - but it retains a
compositional semantics. The first step in transitioning to Turing machines is to make a sequential
evaluator for this basis, which we take up in the next section.
-/


namespace ToPartrec

/-- The type of codes for primitive recursive functions. Unlike `Nat.Partrec.Code`, this uses a set
of operations on `List ℕ`. See `Code.eval` for a description of the behavior of the primitives. -/
inductive Code
  | zero'
  | succ
  | tail
  | cons : Code → Code → Code
  | comp : Code → Code → Code
  | case : Code → Code → Code
  | fix : Code → Code
  deriving DecidableEq, Inhabited
#align turing.to_partrec.code Turing.ToPartrec.Code
#align turing.to_partrec.code.zero' Turing.ToPartrec.Code.zero'
#align turing.to_partrec.code.succ Turing.ToPartrec.Code.succ
#align turing.to_partrec.code.tail Turing.ToPartrec.Code.tail
#align turing.to_partrec.code.cons Turing.ToPartrec.Code.cons
#align turing.to_partrec.code.comp Turing.ToPartrec.Code.comp
#align turing.to_partrec.code.case Turing.ToPartrec.Code.case
#align turing.to_partrec.code.fix Turing.ToPartrec.Code.fix

/-- The semantics of the `Code` primitives, as partial functions `List ℕ →. List ℕ`. By convention
we functions that return a single result return a singleton `[n]`, or in some cases `n :: v` where
`v` will be ignored by a subsequent function.

* `zero'` appends a `0` to the input. That is, `zero' v = 0 :: v`.
* `succ` returns the successor of the head of the input, defaulting to zero if there is no head:
  * `succ [] = [1]`
  * `succ (n :: v) = [n + 1]`
* `tail` returns the tail of the input
  * `tail [] = []`
  * `tail (n :: v) = v`
* `cons f fs` calls `f` and `fs` on the input and conses the results:
  * `cons f fs v = (f v).head :: fs v`
* `comp f g` calls `f` on the output of `g`:
  * `comp f g v = f (g v)`
* `case f g` cases on the head of the input, calling `f` or `g` depending on whether it is zero or
  a successor (similar to `Nat.casesOn`).
  * `case f g [] = f []`
  * `case f g (0 :: v) = f v`
  * `case f g (n+1 :: v) = g (n :: v)`
* `fix f` calls `f` repeatedly, using the head of the result of `f` to decide whether to call `f`
  again or finish:
  * `fix f v = []` if `f v = []`
  * `fix f v = w` if `f v = 0 :: w`
  * `fix f v = fix f w` if `f v = n+1 :: w` (the exact value of `n` is discarded)
-/
def Code.eval : Code → List ℕ →. List ℕ
  | Code.zero' => fun v => pure (0 :: v)
  | Code.succ => fun v => pure [v.headI.succ]
  | Code.tail => fun v => pure v.tail
  | Code.cons f fs => fun v => do
    let n ← Code.eval f v
    let ns ← Code.eval fs v
    pure (n.headI :: ns)
  | Code.comp f g => fun v => g.eval v >>= f.eval
  | Code.case f g => fun v => v.headI.rec (f.eval v.tail) fun y _ => g.eval (y::v.tail)
  | Code.fix f =>
    PFun.fix fun v => (f.eval v).map fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail
#align turing.to_partrec.code.eval Turing.ToPartrec.Code.eval

namespace Code

/- Porting note: The equation lemma of `eval` is too strong; it simplifies terms like the LHS of
`pred_eval`. Even `eqns` can't fix this. We removed `simp` attr from `eval` and prepare new simp
lemmas for `eval`. -/

@[simp]
theorem zero'_eval : zero'.eval = fun v => pure (0 :: v) := by simp [eval]
                                                               -- 🎉 no goals

@[simp]
theorem succ_eval : succ.eval = fun v => pure [v.headI.succ] := by simp [eval]
                                                                   -- 🎉 no goals

@[simp]
theorem tail_eval : tail.eval = fun v => pure v.tail := by simp [eval]
                                                           -- 🎉 no goals

@[simp]
theorem cons_eval (f fs) : (cons f fs).eval = fun v => do {
    let n ← Code.eval f v
    let ns ← Code.eval fs v
    pure (n.headI :: ns) } := by simp [eval]
                                 -- 🎉 no goals

@[simp]
theorem comp_eval (f g) : (comp f g).eval = fun v => g.eval v >>= f.eval := by simp [eval]
                                                                               -- 🎉 no goals

@[simp]
theorem case_eval (f g) :
    (case f g).eval = fun v => v.headI.rec (f.eval v.tail) fun y _ => g.eval (y::v.tail) := by
  simp [eval]
  -- 🎉 no goals

@[simp]
theorem fix_eval (f) : (fix f).eval =
    PFun.fix fun v => (f.eval v).map fun v =>
      if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail := by
  simp [eval]
  -- 🎉 no goals

/-- `nil` is the constant nil function: `nil v = []`. -/
def nil : Code :=
  tail.comp succ
#align turing.to_partrec.code.nil Turing.ToPartrec.Code.nil

@[simp]
theorem nil_eval (v) : nil.eval v = pure [] := by simp [nil]
                                                  -- 🎉 no goals
#align turing.to_partrec.code.nil_eval Turing.ToPartrec.Code.nil_eval

/-- `id` is the identity function: `id v = v`. -/
def id : Code :=
  tail.comp zero'
#align turing.to_partrec.code.id Turing.ToPartrec.Code.id

@[simp]
theorem id_eval (v) : id.eval v = pure v := by simp [id]
                                               -- 🎉 no goals
#align turing.to_partrec.code.id_eval Turing.ToPartrec.Code.id_eval

/-- `head` gets the head of the input list: `head [] = [0]`, `head (n :: v) = [n]`. -/
def head : Code :=
  cons id nil
#align turing.to_partrec.code.head Turing.ToPartrec.Code.head

@[simp]
theorem head_eval (v) : head.eval v = pure [v.headI] := by simp [head]
                                                           -- 🎉 no goals
#align turing.to_partrec.code.head_eval Turing.ToPartrec.Code.head_eval

/-- `zero` is the constant zero function: `zero v = [0]`. -/
def zero : Code :=
  cons zero' nil
#align turing.to_partrec.code.zero Turing.ToPartrec.Code.zero

@[simp]
theorem zero_eval (v) : zero.eval v = pure [0] := by simp [zero]
                                                     -- 🎉 no goals
#align turing.to_partrec.code.zero_eval Turing.ToPartrec.Code.zero_eval

/-- `pred` returns the predecessor of the head of the input:
`pred [] = [0]`, `pred (0 :: v) = [0]`, `pred (n+1 :: v) = [n]`. -/
def pred : Code :=
  case zero head
#align turing.to_partrec.code.pred Turing.ToPartrec.Code.pred

@[simp]
theorem pred_eval (v) : pred.eval v = pure [v.headI.pred] := by
  simp [pred]; cases v.headI <;> simp
  -- ⊢ Nat.rec (Part.some [0]) (fun y x => Part.some [y]) (List.headI v) = Part.som …
               -- ⊢ Nat.rec (Part.some [0]) (fun y x => Part.some [y]) Nat.zero = Part.some [Nat …
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align turing.to_partrec.code.pred_eval Turing.ToPartrec.Code.pred_eval

/-- `rfind f` performs the function of the `rfind` primitive of partial recursive functions.
`rfind f v` returns the smallest `n` such that `(f (n :: v)).head = 0`.

It is implemented as:

    rfind f v = pred (fix (fun (n::v) => f (n::v) :: n+1 :: v) (0 :: v))

The idea is that the initial state is `0 :: v`, and the `fix` keeps `n :: v` as its internal state;
it calls `f (n :: v)` as the exit test and `n+1 :: v` as the next state. At the end we get
`n+1 :: v` where `n` is the desired output, and `pred (n+1 :: v) = [n]` returns the result.
 -/
def rfind (f : Code) : Code :=
  comp pred <| comp (fix <| cons f <| cons succ tail) zero'
#align turing.to_partrec.code.rfind Turing.ToPartrec.Code.rfind

/-- `prec f g` implements the `prec` (primitive recursion) operation of partial recursive
functions. `prec f g` evaluates as:

* `prec f g [] = [f []]`
* `prec f g (0 :: v) = [f v]`
* `prec f g (n+1 :: v) = [g (n :: prec f g (n :: v) :: v)]`

It is implemented as:

    G (a :: b :: IH :: v) = (b :: a+1 :: b-1 :: g (a :: IH :: v) :: v)
    F (0 :: f_v :: v) = (f_v :: v)
    F (n+1 :: f_v :: v) = (fix G (0 :: n :: f_v :: v)).tail.tail
    prec f g (a :: v) = [(F (a :: f v :: v)).head]

Because `fix` always evaluates its body at least once, we must special case the `0` case to avoid
calling `g` more times than necessary (which could be bad if `g` diverges). If the input is
`0 :: v`, then `F (0 :: f v :: v) = (f v :: v)` so we return `[f v]`. If the input is `n+1 :: v`,
we evaluate the function from the bottom up, with initial state `0 :: n :: f v :: v`. The first
number counts up, providing arguments for the applications to `g`, while the second number counts
down, providing the exit condition (this is the initial `b` in the return value of `G`, which is
stripped by `fix`). After the `fix` is complete, the final state is `n :: 0 :: res :: v` where
`res` is the desired result, and the rest reduces this to `[res]`. -/
def prec (f g : Code) : Code :=
  let G :=
    cons tail <|
      cons succ <|
        cons (comp pred tail) <|
          cons (comp g <| cons id <| comp tail tail) <| comp tail <| comp tail tail
  let F := case id <| comp (comp (comp tail tail) (fix G)) zero'
  cons (comp F (cons head <| cons (comp f tail) tail)) nil
#align turing.to_partrec.code.prec Turing.ToPartrec.Code.prec

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some

theorem exists_code.comp {m n} {f : Vector ℕ n →. ℕ} {g : Fin n → Vector ℕ m →. ℕ}
    (hf : ∃ c : Code, ∀ v : Vector ℕ n, c.eval v.1 = pure <$> f v)
    (hg : ∀ i, ∃ c : Code, ∀ v : Vector ℕ m, c.eval v.1 = pure <$> g i v) :
    ∃ c : Code, ∀ v : Vector ℕ m, c.eval v.1 = pure <$> ((Vector.mOfFn fun i => g i v) >>= f) := by
  rsuffices ⟨cg, hg⟩ :
    ∃ c : Code, ∀ v : Vector ℕ m, c.eval v.1 = Subtype.val <$> Vector.mOfFn fun i => g i v
  · obtain ⟨cf, hf⟩ := hf
    -- ⊢ ∃ c, ∀ (v : Vector ℕ m), eval c ↑v = pure <$> ((Vector.mOfFn fun i => g i v) …
    exact
      ⟨cf.comp cg, fun v => by
        simp [hg, hf, map_bind, seq_bind_eq, Function.comp]
        rfl⟩
  clear hf f; induction' n with n IH
  -- ⊢ ∃ c, ∀ (v : Vector ℕ m), eval c ↑v = Subtype.val <$> Vector.mOfFn fun i => g …
              -- ⊢ ∃ c, ∀ (v : Vector ℕ m), eval c ↑v = Subtype.val <$> Vector.mOfFn fun i => g …
  · exact ⟨nil, fun v => by simp [Vector.mOfFn, Bind.bind]; rfl⟩
    -- 🎉 no goals
  · obtain ⟨cg, hg₁⟩ := hg 0
    -- ⊢ ∃ c, ∀ (v : Vector ℕ m), eval c ↑v = Subtype.val <$> Vector.mOfFn fun i => g …
    obtain ⟨cl, hl⟩ := IH fun i => hg i.succ
    -- ⊢ ∃ c, ∀ (v : Vector ℕ m), eval c ↑v = Subtype.val <$> Vector.mOfFn fun i => g …
    exact
      ⟨cons cg cl, fun v => by
        simp [Vector.mOfFn, hg₁, map_bind, seq_bind_eq, bind_assoc, (· ∘ ·), hl]
        rfl⟩
#align turing.to_partrec.code.exists_code.comp Turing.ToPartrec.Code.exists_code.comp

theorem exists_code {n} {f : Vector ℕ n →. ℕ} (hf : Nat.Partrec' f) :
    ∃ c : Code, ∀ v : Vector ℕ n, c.eval v.1 = pure <$> f v := by
  induction' hf with n f hf
  induction hf
  case prim.zero => exact ⟨zero', fun ⟨[], _⟩ => rfl⟩
  -- 🎉 no goals
  case prim.succ => exact ⟨succ, fun ⟨[v], _⟩ => rfl⟩
  -- 🎉 no goals
  case prim.get n i =>
    refine' Fin.succRec (fun n => _) (fun n i IH => _) i
    · exact ⟨head, fun ⟨List.cons a as, _⟩ => by simp [Bind.bind]; rfl⟩
    · obtain ⟨c, h⟩ := IH
      exact ⟨c.comp tail, fun v => by simpa [← Vector.get_tail, Bind.bind] using h v.tail⟩
  case prim.comp m n f g hf hg IHf IHg =>
    simpa [Part.bind_eq_bind] using exists_code.comp IHf IHg
  case prim.prec n f g _ _ IHf IHg =>
    obtain ⟨cf, hf⟩ := IHf
    obtain ⟨cg, hg⟩ := IHg
    simp only [Part.map_eq_map, Part.map_some, PFun.coe_val] at hf hg
    refine' ⟨prec cf cg, fun v => _⟩
    rw [← v.cons_head_tail]
    specialize hf v.tail
    replace hg := fun a b => hg (a ::ᵥ b ::ᵥ v.tail)
    simp only [Vector.cons_val, Vector.tail_val] at hf hg
    simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, Vector.tail_cons, Vector.head_cons,
      PFun.coe_val, Vector.tail_val]
    simp only [← Part.pure_eq_some] at hf hg ⊢
    induction' v.head with n _ <;>
      simp [prec, hf, Part.bind_assoc, ← Part.bind_some_eq_map, Part.bind_some,
        show ∀ x, pure x = [x] from fun _ => rfl, Bind.bind, Functor.map]
    suffices ∀ a b, a + b = n →
      (n.succ :: 0 ::
        g (n ::ᵥ Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) n ::ᵥ v.tail)
          :: v.val.tail : List ℕ) ∈
        PFun.fix
          (fun v : List ℕ => Part.bind (cg.eval (v.headI :: v.tail.tail))
            (fun x => Part.some (if v.tail.headI = 0
              then Sum.inl
                (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail : List ℕ)
              else Sum.inr
                (v.headI.succ :: v.tail.headI.pred :: x.headI :: v.tail.tail.tail))))
          (a :: b :: Nat.rec (f v.tail) (fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) a :: v.val.tail) by
      erw [Part.eq_some_iff.2 (this 0 n (zero_add n))]
      simp only [List.headI, Part.bind_some, List.tail_cons]
    intro a b e
    induction' b with b IH generalizing a
    · refine' PFun.mem_fix_iff.2 (Or.inl <| Part.eq_some_iff.1 _)
      simp only [hg, ← e, Part.bind_some, List.tail_cons, pure]
      rfl
    · refine' PFun.mem_fix_iff.2 (Or.inr ⟨_, _, IH (a + 1) (by rwa [add_right_comm])⟩)
      simp only [hg, eval, Part.bind_some, Nat.rec_add_one, List.tail_nil, List.tail_cons, pure]
      exact Part.mem_some_iff.2 rfl
  case comp m n f g _ _ IHf IHg => exact exists_code.comp IHf IHg
  -- ⊢ ∃ c, ∀ (v : Vector ℕ n✝), eval c ↑v = pure <$> (fun v => Nat.rfind fun n =>  …
  -- 🎉 no goals
  case rfind n f _ IHf =>
    obtain ⟨cf, hf⟩ := IHf; refine' ⟨rfind cf, fun v => _⟩
    replace hf := fun a => hf (a ::ᵥ v)
    simp only [Part.map_eq_map, Part.map_some, Vector.cons_val, PFun.coe_val,
      show ∀ x, pure x = [x] from fun _ => rfl] at hf ⊢
    refine' Part.ext fun x => _
    simp only [rfind, Part.bind_eq_bind, Part.pure_eq_some, Part.map_eq_map, Part.bind_some,
      exists_prop, cons_eval, comp_eval, fix_eval, tail_eval, succ_eval, zero'_eval,
      List.headI_nil, List.headI_cons, pred_eval, Part.map_some, Bool.false_eq_decide_iff,
      Part.mem_bind_iff, List.length, Part.mem_map_iff, Nat.mem_rfind, List.tail_nil,
      List.tail_cons, Bool.true_eq_decide_iff, Part.mem_some_iff, Part.map_bind]
    constructor
    · rintro ⟨v', h1, rfl⟩
      suffices ∀ v₁ : List ℕ, v' ∈ PFun.fix
        (fun v => (cf.eval v).bind fun y => Part.some <|
          if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
            else Sum.inr (v.headI.succ :: v.tail)) v₁ →
        ∀ n, (v₁ = n :: v.val) → (∀ m < n, ¬f (m ::ᵥ v) = 0) →
          ∃ a : ℕ,
            (f (a ::ᵥ v) = 0 ∧ ∀ {m : ℕ}, m < a → ¬f (m ::ᵥ v) = 0) ∧ [a] = [v'.headI.pred]
        by exact this _ h1 0 rfl (by rintro _ ⟨⟩)
      clear h1
      intro v₀ h1
      refine' PFun.fixInduction h1 fun v₁ h2 IH => _
      clear h1
      rintro n rfl hm
      have := PFun.mem_fix_iff.1 h2
      simp only [hf, Part.bind_some] at this
      split_ifs at this with h
      · simp only [List.headI_nil, List.headI_cons, exists_false, or_false_iff, Part.mem_some_iff,
          List.tail_cons, false_and_iff, Sum.inl.injEq] at this
        subst this
        exact ⟨_, ⟨h, @(hm)⟩, rfl⟩
      · refine' IH (n.succ::v.val) (by simp_all) _ rfl fun m h' => _
        obtain h | rfl := Nat.lt_succ_iff_lt_or_eq.1 h'
        exacts [hm _ h, h]
    · rintro ⟨n, ⟨hn, hm⟩, rfl⟩
      refine' ⟨n.succ::v.1, _, rfl⟩
      have : (n.succ::v.1 : List ℕ) ∈
        PFun.fix (fun v =>
          (cf.eval v).bind fun y =>
            Part.some <|
              if y.headI = 0 then Sum.inl (v.headI.succ :: v.tail)
                else Sum.inr (v.headI.succ :: v.tail))
            (n::v.val) :=
        PFun.mem_fix_iff.2 (Or.inl (by simp [hf, hn]))
      generalize (n.succ :: v.1 : List ℕ) = w at this ⊢
      clear hn
      induction' n with n IH
      · exact this
      refine' IH (fun {m} h' => hm (Nat.lt_succ_of_lt h'))
        (PFun.mem_fix_iff.2 (Or.inr ⟨_, _, this⟩))
      simp only [hf, hm n.lt_succ_self, Part.bind_some, List.headI, eq_self_iff_true, if_false,
        Part.mem_some_iff, and_self_iff, List.tail_cons]
#align turing.to_partrec.code.exists_code Turing.ToPartrec.Code.exists_code

end Code

/-!
## From compositional semantics to sequential semantics

Our initial sequential model is designed to be as similar as possible to the compositional
semantics in terms of its primitives, but it is a sequential semantics, meaning that rather than
defining an `eval c : List ℕ →. List ℕ` function for each program, defined by recursion on
programs, we have a type `Cfg` with a step function `step : Cfg → Option cfg` that provides a
deterministic evaluation order. In order to do this, we introduce the notion of a *continuation*,
which can be viewed as a `Code` with a hole in it where evaluation is currently taking place.
Continuations can be assigned a `List ℕ →. List ℕ` semantics as well, with the interpretation
being that given a `List ℕ` result returned from the code in the hole, the remainder of the
program will evaluate to a `List ℕ` final value.

The continuations are:

* `halt`: the empty continuation: the hole is the whole program, whatever is returned is the
  final result. In our notation this is just `_`.
* `cons₁ fs v k`: evaluating the first part of a `cons`, that is `k (_ :: fs v)`, where `k` is the
  outer continuation.
* `cons₂ ns k`: evaluating the second part of a `cons`: `k (ns.headI :: _)`. (Technically we don't
  need to hold on to all of `ns` here since we are already committed to taking the head, but this
  is more regular.)
* `comp f k`: evaluating the first part of a composition: `k (f _)`.
* `fix f k`: waiting for the result of `f` in a `fix f` expression:
  `k (if _.headI = 0 then _.tail else fix f (_.tail))`

The type `Cfg` of evaluation states is:

* `ret k v`: we have received a result, and are now evaluating the continuation `k` with result
  `v`; that is, `k v` where `k` is ready to evaluate.
* `halt v`: we are done and the result is `v`.

The main theorem of this section is that for each code `c`, the state `stepNormal c halt v` steps
to `v'` in finitely many steps if and only if `Code.eval c v = some v'`.
-/


/-- The type of continuations, built up during evaluation of a `Code` expression. -/
inductive Cont
  | halt
  | cons₁ : Code → List ℕ → Cont → Cont
  | cons₂ : List ℕ → Cont → Cont
  | comp : Code → Cont → Cont
  | fix : Code → Cont → Cont
  deriving Inhabited
#align turing.to_partrec.cont Turing.ToPartrec.Cont
#align turing.to_partrec.cont.halt Turing.ToPartrec.Cont.halt
#align turing.to_partrec.cont.cons₁ Turing.ToPartrec.Cont.cons₁
#align turing.to_partrec.cont.cons₂ Turing.ToPartrec.Cont.cons₂
#align turing.to_partrec.cont.comp Turing.ToPartrec.Cont.comp
#align turing.to_partrec.cont.fix Turing.ToPartrec.Cont.fix

/-- The semantics of a continuation. -/
def Cont.eval : Cont → List ℕ →. List ℕ
  | Cont.halt => pure
  | Cont.cons₁ fs as k => fun v => do
    let ns ← Code.eval fs as
    Cont.eval k (v.headI :: ns)
  | Cont.cons₂ ns k => fun v => Cont.eval k (ns.headI :: v)
  | Cont.comp f k => fun v => Code.eval f v >>= Cont.eval k
  | Cont.fix f k => fun v => if v.headI = 0 then k.eval v.tail else f.fix.eval v.tail >>= k.eval
#align turing.to_partrec.cont.eval Turing.ToPartrec.Cont.eval

/-- The set of configurations of the machine:

* `halt v`: The machine is about to stop and `v : List ℕ` is the result.
* `ret k v`: The machine is about to pass `v : List ℕ` to continuation `k : cont`.

We don't have a state corresponding to normal evaluation because these are evaluated immediately
to a `ret` "in zero steps" using the `stepNormal` function. -/
inductive Cfg
  | halt : List ℕ → Cfg
  | ret : Cont → List ℕ → Cfg
  deriving Inhabited
#align turing.to_partrec.cfg Turing.ToPartrec.Cfg
#align turing.to_partrec.cfg.halt Turing.ToPartrec.Cfg.halt
#align turing.to_partrec.cfg.ret Turing.ToPartrec.Cfg.ret

/-- Evaluating `c : Code` in a continuation `k : Cont` and input `v : List ℕ`. This goes by
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
#align turing.to_partrec.step_normal Turing.ToPartrec.stepNormal

/-- Evaluating a continuation `k : Cont` on input `v : List ℕ`. This is the second part of
evaluation, when we receive results from continuations built by `stepNormal`.

* `Cont.halt v = v`, so we are done and transition to the `Cfg.halt v` state
* `Cont.cons₁ fs as k v = k (v.headI :: fs as)`, so we evaluate `fs as` now with the continuation
  `k (v.headI :: _)` (called `cons₂ v k`).
* `Cont.cons₂ ns k v = k (ns.headI :: v)`, where we now have everything we need to evaluate
  `ns.headI :: v`, so we return it to `k`.
* `Cont.comp f k v = k (f v)`, so we call `f v` with `k` as the continuation.
* `Cont.fix f k v = k (if v.headI = 0 then k v.tail else fix f v.tail)`, where `v` is a value,
  so we evaluate the if statement and either call `k` with `v.tail`, or call `fix f v` with `k` as
  the continuation (which immediately calls `f` with `Cont.fix f k` as the continuation).
-/
def stepRet : Cont → List ℕ → Cfg
  | Cont.halt, v => Cfg.halt v
  | Cont.cons₁ fs as k, v => stepNormal fs (Cont.cons₂ v k) as
  | Cont.cons₂ ns k, v => stepRet k (ns.headI :: v)
  | Cont.comp f k, v => stepNormal f k v
  | Cont.fix f k, v => if v.headI = 0 then stepRet k v.tail else stepNormal f (Cont.fix f k) v.tail
#align turing.to_partrec.step_ret Turing.ToPartrec.stepRet

/-- If we are not done (in `Cfg.halt` state), then we must be still stuck on a continuation, so
this main loop calls `stepRet` with the new continuation. The overall `step` function transitions
from one `Cfg` to another, only halting at the `Cfg.halt` state. -/
def step : Cfg → Option Cfg
  | Cfg.halt _ => none
  | Cfg.ret k v => some (stepRet k v)
#align turing.to_partrec.step Turing.ToPartrec.step

/-- In order to extract a compositional semantics from the sequential execution behavior of
configurations, we observe that continuations have a monoid structure, with `Cont.halt` as the unit
and `Cont.then` as the multiplication. `Cont.then k₁ k₂` runs `k₁` until it halts, and then takes
the result of `k₁` and passes it to `k₂`.

We will not prove it is associative (although it is), but we are instead interested in the
associativity law `k₂ (eval c k₁) = eval c (k₁.then k₂)`. This holds at both the sequential and
compositional levels, and allows us to express running a machine without the ambient continuation
and relate it to the original machine's evaluation steps. In the literature this is usually
where one uses Turing machines embedded inside other Turing machines, but this approach allows us
to avoid changing the ambient type `Cfg` in the middle of the recursion.
-/
def Cont.then : Cont → Cont → Cont
  | Cont.halt => fun k' => k'
  | Cont.cons₁ fs as k => fun k' => Cont.cons₁ fs as (k.then k')
  | Cont.cons₂ ns k => fun k' => Cont.cons₂ ns (k.then k')
  | Cont.comp f k => fun k' => Cont.comp f (k.then k')
  | Cont.fix f k => fun k' => Cont.fix f (k.then k')
#align turing.to_partrec.cont.then Turing.ToPartrec.Cont.then

theorem Cont.then_eval {k k' : Cont} {v} : (k.then k').eval v = k.eval v >>= k'.eval := by
  induction' k with _ _ _ _ _ _ _ _ _ k_ih _ _ k_ih generalizing v <;>
    simp only [Cont.eval, Cont.then, bind_assoc, pure_bind, *]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- ⊢ Code.eval a✝¹ v >>= eval (then a✝ k') = Code.eval a✝¹ v >>= fun x => eval a✝ …
    -- ⊢ (if List.headI v = 0 then eval a✝ (List.tail v) >>= eval k' else Code.eval ( …
  · simp only [← k_ih]
    -- 🎉 no goals
  · split_ifs <;> [rfl; simp only [← k_ih, bind_assoc]]
    -- 🎉 no goals
#align turing.to_partrec.cont.then_eval Turing.ToPartrec.Cont.then_eval

/-- The `then k` function is a "configuration homomorphism". Its operation on states is to append
`k` to the continuation of a `Cfg.ret` state, and to run `k` on `v` if we are in the `Cfg.halt v`
state. -/
def Cfg.then : Cfg → Cont → Cfg
  | Cfg.halt v => fun k' => stepRet k' v
  | Cfg.ret k v => fun k' => Cfg.ret (k.then k') v
#align turing.to_partrec.cfg.then Turing.ToPartrec.Cfg.then

/-- The `stepNormal` function respects the `then k'` homomorphism. Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state. -/
theorem stepNormal_then (c) (k k' : Cont) (v) :
    stepNormal c (k.then k') v = (stepNormal c k v).then k' := by
  induction c generalizing k v <;> simp only [Cont.then, stepNormal, *] <;>
                                   -- ⊢ Cfg.ret (Cont.then k k') (0 :: v) = Cfg.then (Cfg.ret k (0 :: v)) k'
                                   -- ⊢ Cfg.ret (Cont.then k k') [Nat.succ (List.headI v)] = Cfg.then (Cfg.ret k [Na …
                                   -- ⊢ Cfg.ret (Cont.then k k') (List.tail v) = Cfg.then (Cfg.ret k (List.tail v)) k'
                                   -- ⊢ stepNormal a✝¹ (Cont.cons₁ a✝ v (Cont.then k k')) v = Cfg.then (stepNormal a …
                                   -- ⊢ stepNormal a✝ (Cont.comp a✝¹ (Cont.then k k')) v = Cfg.then (stepNormal a✝ ( …
                                   -- ⊢ Nat.rec (Cfg.then (stepNormal a✝¹ k (List.tail v)) k') (fun y x => Cfg.then  …
                                   -- ⊢ stepNormal a✝ (Cont.fix a✝ (Cont.then k k')) v = Cfg.then (stepNormal a✝ (Co …
    try { simp only [Cfg.then]; done }
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- ⊢ stepNormal a✝¹ (Cont.cons₁ a✝ v (Cont.then k k')) v = Cfg.then (stepNormal a …
    -- ⊢ stepNormal a✝ (Cont.comp a✝¹ (Cont.then k k')) v = Cfg.then (stepNormal a✝ ( …
    -- ⊢ Nat.rec (Cfg.then (stepNormal a✝¹ k (List.tail v)) k') (fun y x => Cfg.then  …
    -- ⊢ stepNormal a✝ (Cont.fix a✝ (Cont.then k k')) v = Cfg.then (stepNormal a✝ (Co …
  case cons c c' ih _ => rw [← ih, Cont.then]
  -- 🎉 no goals
  case comp c c' _ ih' => rw [← ih', Cont.then]
  -- ⊢ Nat.rec (Cfg.then (stepNormal a✝¹ k (List.tail v)) k') (fun y x => Cfg.then  …
  -- 🎉 no goals
  · cases v.headI <;> simp only [Nat.rec]
    -- ⊢ Nat.rec (Cfg.then (stepNormal a✝¹ k (List.tail v)) k') (fun y x => Cfg.then  …
                      -- 🎉 no goals
                      -- 🎉 no goals
  case fix c ih => rw [← ih, Cont.then]
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.to_partrec.step_normal_then Turing.ToPartrec.stepNormal_then

/-- The `stepRet` function respects the `then k'` homomorphism. Note that this is an exact
equality, not a simulation; the original and embedded machines move in lock-step until the
embedded machine reaches the halt state. -/
theorem stepRet_then {k k' : Cont} {v} : stepRet (k.then k') v = (stepRet k v).then k' := by
  induction k generalizing v <;> simp only [Cont.then, stepRet, *] <;>
                                 -- ⊢ stepRet k' v = Cfg.then (Cfg.halt v) k'
                                 -- ⊢ stepNormal a✝² (Cont.cons₂ v (Cont.then a✝ k')) a✝¹ = Cfg.then (stepNormal a …
                                 -- 🎉 no goals
                                 -- ⊢ stepNormal a✝¹ (Cont.then a✝ k') v = Cfg.then (stepNormal a✝¹ a✝ v) k'
                                 -- ⊢ (if List.headI v = 0 then Cfg.then (stepRet a✝ (List.tail v)) k' else stepNo …
    try { simp only [Cfg.then]; done }
    -- 🎉 no goals
    -- ⊢ stepNormal a✝² (Cont.cons₂ v (Cont.then a✝ k')) a✝¹ = Cfg.then (stepNormal a …
    -- ⊢ stepNormal a✝¹ (Cont.then a✝ k') v = Cfg.then (stepNormal a✝¹ a✝ v) k'
    -- ⊢ (if List.headI v = 0 then Cfg.then (stepRet a✝ (List.tail v)) k' else stepNo …
  case cons₁ =>
    rw [← stepNormal_then]
    rfl
  case comp =>
    rw [← stepNormal_then]
  case fix _ k_ih =>
    split_ifs
    · rw [← k_ih]
    · rw [← stepNormal_then]
      rfl
#align turing.to_partrec.step_ret_then Turing.ToPartrec.stepRet_then

/-- This is a temporary definition, because we will prove in `code_is_ok` that it always holds.
It asserts that `c` is semantically correct; that is, for any `k` and `v`,
`eval (stepNormal c k v) = eval (Cfg.ret k (Code.eval c v))`, as an equality of partial values
(so one diverges iff the other does).

In particular, we can let `k = Cont.halt`, and then this asserts that `stepNormal c Cont.halt v`
evaluates to `Cfg.halt (Code.eval c v)`. -/
def Code.Ok (c : Code) :=
  ∀ k v, Turing.eval step (stepNormal c k v) =
    Code.eval c v >>= fun v => Turing.eval step (Cfg.ret k v)
#align turing.to_partrec.code.ok Turing.ToPartrec.Code.Ok

theorem Code.Ok.zero {c} (h : Code.Ok c) {v} :
    Turing.eval step (stepNormal c Cont.halt v) = Cfg.halt <$> Code.eval c v := by
  rw [h, ← bind_pure_comp]; congr; funext v
  -- ⊢ (do
                            -- ⊢ (fun v => Turing.eval step (Cfg.ret Cont.halt v)) = fun a => pure (Cfg.halt a)
                                   -- ⊢ Turing.eval step (Cfg.ret Cont.halt v) = pure (Cfg.halt v)
  exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.single rfl, rfl⟩)
  -- 🎉 no goals
#align turing.to_partrec.code.ok.zero Turing.ToPartrec.Code.Ok.zero

theorem stepNormal.is_ret (c k v) : ∃ k' v', stepNormal c k v = Cfg.ret k' v' := by
  induction c generalizing k v
  iterate 3 exact ⟨_, _, rfl⟩
  case cons _f fs IHf _IHfs => apply IHf
  -- 🎉 no goals
  case comp f _g _IHf IHg => apply IHg
  -- ⊢ ∃ k' v', stepNormal (Code.case a✝¹ a✝) k v = Cfg.ret k' v'
  -- 🎉 no goals
  case case f g IHf IHg =>
    rw [stepNormal]
    simp only []
    cases v.headI <;> simp only [] <;> [apply IHf; apply IHg]
  case fix f IHf => apply IHf
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.to_partrec.step_normal.is_ret Turing.ToPartrec.stepNormal.is_ret

theorem cont_eval_fix {f k v} (fok : Code.Ok f) :
    Turing.eval step (stepNormal f (Cont.fix f k) v) =
      f.fix.eval v >>= fun v => Turing.eval step (Cfg.ret k v) := by
  refine' Part.ext fun x => _
  -- ⊢ x ∈ eval step (stepNormal f (Cont.fix f k) v) ↔
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  -- ⊢ x ∈ eval step (stepNormal f (Cont.fix f k) v) ↔ ∃ a, a ∈ Code.eval (Code.fix …
  constructor
  -- ⊢ x ∈ eval step (stepNormal f (Cont.fix f k) v) → ∃ a, a ∈ Code.eval (Code.fix …
  · suffices ∀ c, x ∈ eval step c → ∀ v c', c = Cfg.then c' (Cont.fix f k) →
      Reaches step (stepNormal f Cont.halt v) c' →
        ∃ v₁ ∈ f.eval v, ∃ v₂ ∈ if List.headI v₁ = 0 then pure v₁.tail else f.fix.eval v₁.tail,
          x ∈ eval step (Cfg.ret k v₂) by
      intro h
      obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
        this _ h _ _ (stepNormal_then _ Cont.halt _ _) ReflTransGen.refl
      refine' ⟨v₂, PFun.mem_fix_iff.2 _, h₃⟩
      simp only [Part.eq_some_iff.2 hv₁, Part.map_some]
      split_ifs at hv₂ ⊢
      · rw [Part.mem_some_iff.1 hv₂]
        exact Or.inl (Part.mem_some _)
      · exact Or.inr ⟨_, Part.mem_some _, hv₂⟩
    refine' fun c he => evalInduction he fun y h IH => _
    -- ⊢ ∀ (v : List ℕ) (c' : Cfg), y = Cfg.then c' (Cont.fix f k) → Reaches step (st …
    rintro v (⟨v'⟩ | ⟨k', v'⟩) rfl hr <;> rw [Cfg.then] at h IH <;> simp only [] at h IH
    -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
                                          -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
                                          -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
                                                                    -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
                                                                    -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
    · have := mem_eval.2 ⟨hr, rfl⟩
      -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
      rw [fok, Part.bind_eq_bind, Part.mem_bind_iff] at this
      -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
      obtain ⟨v'', h₁, h₂⟩ := this
      -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
      rw [reaches_eval] at h₂
      swap
      exact ReflTransGen.single rfl
      -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
      cases Part.mem_unique h₂ (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
      -- ⊢ ∃ v₁, v₁ ∈ Code.eval f v ∧ ∃ v₂, (v₂ ∈ if List.headI v₁ = 0 then pure (List. …
      refine' ⟨v', h₁, _⟩
      -- ⊢ ∃ v₂, (v₂ ∈ if List.headI v' = 0 then pure (List.tail v') else Code.eval (Co …
      rw [stepRet] at h
      -- ⊢ ∃ v₂, (v₂ ∈ if List.headI v' = 0 then pure (List.tail v') else Code.eval (Co …
      revert h
      -- ⊢ x ∈ eval step (if List.headI v' = 0 then stepRet k (List.tail v') else stepN …
      by_cases he : v'.headI = 0 <;> simp only [exists_prop, if_pos, if_false, he] <;> intro h
      -- ⊢ x ∈ eval step (if List.headI v' = 0 then stepRet k (List.tail v') else stepN …
                                     -- ⊢ x ∈ eval step (stepRet k (List.tail v')) → ∃ v₂, v₂ ∈ pure (List.tail v') ∧  …
                                     -- ⊢ x ∈ eval step (stepNormal f (Cont.fix f k) (List.tail v')) → ∃ v₂, v₂ ∈ Code …
                                                                                       -- ⊢ ∃ v₂, v₂ ∈ pure (List.tail v') ∧ x ∈ eval step (Cfg.ret k v₂)
                                                                                       -- ⊢ ∃ v₂, v₂ ∈ Code.eval (Code.fix f) (List.tail v') ∧ x ∈ eval step (Cfg.ret k  …
      · refine' ⟨_, Part.mem_some _, _⟩
        -- ⊢ x ∈ eval step (Cfg.ret k (List.tail v'))
        rw [reaches_eval]
        exact h
        -- ⊢ Reaches step (Cfg.ret k (List.tail v')) (stepRet k (List.tail v'))
        exact ReflTransGen.single rfl
        -- 🎉 no goals
      · obtain ⟨k₀, v₀, e₀⟩ := stepNormal.is_ret f Cont.halt v'.tail
        -- ⊢ ∃ v₂, v₂ ∈ Code.eval (Code.fix f) (List.tail v') ∧ x ∈ eval step (Cfg.ret k  …
        have e₁ := stepNormal_then f Cont.halt (Cont.fix f k) v'.tail
        -- ⊢ ∃ v₂, v₂ ∈ Code.eval (Code.fix f) (List.tail v') ∧ x ∈ eval step (Cfg.ret k  …
        rw [e₀, Cont.then, Cfg.then] at e₁
        -- ⊢ ∃ v₂, v₂ ∈ Code.eval (Code.fix f) (List.tail v') ∧ x ∈ eval step (Cfg.ret k  …
        simp only [] at e₁
        -- ⊢ ∃ v₂, v₂ ∈ Code.eval (Code.fix f) (List.tail v') ∧ x ∈ eval step (Cfg.ret k  …
        obtain ⟨v₁, hv₁, v₂, hv₂, h₃⟩ :=
          IH (stepRet (k₀.then (Cont.fix f k)) v₀) (by rw [stepRet, if_neg he, e₁]; rfl)
            v'.tail _ stepRet_then (by apply ReflTransGen.single; rw [e₀]; rfl)
        · refine' ⟨_, PFun.mem_fix_iff.2 _, h₃⟩
          -- ⊢ Sum.inl v₂ ∈ Part.map (fun v => if List.headI v = 0 then Sum.inl (List.tail  …
          simp only [Part.eq_some_iff.2 hv₁, Part.map_some, Part.mem_some_iff]
          -- ⊢ (Sum.inl v₂ = if List.headI v₁ = 0 then Sum.inl (List.tail v₁) else Sum.inr  …
          split_ifs at hv₂ ⊢ <;> [exact Or.inl (congr_arg Sum.inl (Part.mem_some_iff.1 hv₂));
            exact Or.inr ⟨_, rfl, hv₂⟩]
    · exact IH _ rfl _ _ stepRet_then (ReflTransGen.tail hr rfl)
      -- 🎉 no goals
  · rintro ⟨v', he, hr⟩
    -- ⊢ x ∈ eval step (stepNormal f (Cont.fix f k) v)
    rw [reaches_eval] at hr
    swap
    exact ReflTransGen.single rfl
    -- ⊢ x ∈ eval step (stepNormal f (Cont.fix f k) v)
    refine' PFun.fixInduction he fun v (he : v' ∈ f.fix.eval v) IH => _
    -- ⊢ x ∈ eval step (stepNormal f (Cont.fix f k) v)
    rw [fok, Part.bind_eq_bind, Part.mem_bind_iff]
    -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
    obtain he | ⟨v'', he₁', _⟩ := PFun.mem_fix_iff.1 he
    -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
    · obtain ⟨v', he₁, he₂⟩ := (Part.mem_map_iff _).1 he
      -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
      split_ifs at he₂ with h; cases he₂
      -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
                               -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
      refine' ⟨_, he₁, _⟩
      -- ⊢ x ∈ eval step (Cfg.ret (Cont.fix f k) v')
      rw [reaches_eval]
      swap
      exact ReflTransGen.single rfl
      -- ⊢ x ∈ eval step (stepRet (Cont.fix f k) v')
      rwa [stepRet, if_pos h]
      -- 🎉 no goals
    · obtain ⟨v₁, he₁, he₂⟩ := (Part.mem_map_iff _).1 he₁'
      -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
      split_ifs at he₂ with h; cases he₂
      -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
                               -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
      clear he₁'
      -- ⊢ ∃ a, a ∈ Code.eval f v ∧ x ∈ eval step (Cfg.ret (Cont.fix f k) a)
      refine' ⟨_, he₁, _⟩
      -- ⊢ x ∈ eval step (Cfg.ret (Cont.fix f k) v₁)
      rw [reaches_eval]
      swap
      exact ReflTransGen.single rfl
      -- ⊢ x ∈ eval step (stepRet (Cont.fix f k) v₁)
      rw [stepRet, if_neg h]
      -- ⊢ x ∈ eval step (stepNormal f (Cont.fix f k) (List.tail v₁))
      exact IH v₁.tail ((Part.mem_map_iff _).2 ⟨_, he₁, if_neg h⟩)
      -- 🎉 no goals
#align turing.to_partrec.cont_eval_fix Turing.ToPartrec.cont_eval_fix

theorem code_is_ok (c) : Code.Ok c := by
  induction c <;> intro k v <;> rw [stepNormal]
                  -- ⊢ eval step (stepNormal Code.zero' k v) = do
                  -- ⊢ eval step (stepNormal Code.succ k v) = do
                  -- ⊢ eval step (stepNormal Code.tail k v) = do
                  -- ⊢ eval step (stepNormal (Code.cons a✝¹ a✝) k v) = do
                  -- ⊢ eval step (stepNormal (Code.comp a✝¹ a✝) k v) = do
                  -- ⊢ eval step (stepNormal (Code.case a✝¹ a✝) k v) = do
                  -- ⊢ eval step (stepNormal (Code.fix a✝) k v) = do
                                -- ⊢ eval step ((fun k v => Cfg.ret k (0 :: v)) k v) = do
                                -- ⊢ eval step ((fun k v => Cfg.ret k [Nat.succ (List.headI v)]) k v) = do
                                -- ⊢ eval step ((fun k v => Cfg.ret k (List.tail v)) k v) = do
                                -- ⊢ eval step ((fun k v => stepNormal a✝¹ (Cont.cons₁ a✝ v k) v) k v) = do
                                -- ⊢ eval step ((fun k v => stepNormal a✝ (Cont.comp a✝¹ k) v) k v) = do
                                -- ⊢ eval step ((fun k v => Nat.rec (stepNormal a✝¹ k (List.tail v)) (fun y x =>  …
                                -- ⊢ eval step ((fun k v => stepNormal a✝ (Cont.fix a✝ k) v) k v) = do
  iterate 3 simp only [Code.eval, pure_bind]
  case cons f fs IHf IHfs =>
    rw [Code.eval, IHf]
    simp only [bind_assoc, Cont.eval, pure_bind]; congr; funext v
    rw [reaches_eval]; swap; exact ReflTransGen.single rfl
    rw [stepRet, IHfs]; congr; funext v'
    refine' Eq.trans _ (Eq.symm _) <;> try exact reaches_eval (ReflTransGen.single rfl)
  case comp f g IHf IHg =>
    rw [Code.eval, IHg]
    simp only [bind_assoc, Cont.eval, pure_bind]; congr; funext v
    rw [reaches_eval]; swap; exact ReflTransGen.single rfl
    rw [stepRet, IHf]
  case case f g IHf IHg =>
    simp only [Code.eval]
    cases v.headI <;> simp only [Code.eval] <;> [apply IHf; apply IHg]
  case fix f IHf => rw [cont_eval_fix IHf]
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.to_partrec.code_is_ok Turing.ToPartrec.code_is_ok

theorem stepNormal_eval (c v) : eval step (stepNormal c Cont.halt v) = Cfg.halt <$> c.eval v :=
  (code_is_ok c).zero
#align turing.to_partrec.step_normal_eval Turing.ToPartrec.stepNormal_eval

theorem stepRet_eval {k v} : eval step (stepRet k v) = Cfg.halt <$> k.eval v := by
  induction k generalizing v
  case halt =>
    simp only [mem_eval, Cont.eval, map_pure]
    exact Part.eq_some_iff.2 (mem_eval.2 ⟨ReflTransGen.refl, rfl⟩)
  case cons₁ fs as k IH =>
    rw [Cont.eval, stepRet, code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap; exact ReflTransGen.single rfl
    rw [stepRet, IH, bind_pure_comp]
  case cons₂ ns k IH => rw [Cont.eval, stepRet]; exact IH
  -- ⊢ eval step (stepRet (Cont.comp a✝¹ a✝) v) = Cfg.halt <$> Cont.eval (Cont.comp …
  -- 🎉 no goals
  case comp f k IH =>
    rw [Cont.eval, stepRet, code_is_ok]
    simp only [← bind_pure_comp, bind_assoc]; congr; funext v'
    rw [reaches_eval]; swap; exact ReflTransGen.single rfl
    rw [IH, bind_pure_comp]
  case fix f k IH =>
    rw [Cont.eval, stepRet]; simp only [bind_pure_comp]
    split_ifs; · exact IH
    simp only [← bind_pure_comp, bind_assoc, cont_eval_fix (code_is_ok _)]
    congr; funext; rw [bind_pure_comp, ← IH]
    exact reaches_eval (ReflTransGen.single rfl)
#align turing.to_partrec.step_ret_eval Turing.ToPartrec.stepRet_eval

end ToPartrec

/-!
## Simulating sequentialized partial recursive functions in TM2

At this point we have a sequential model of partial recursive functions: the `Cfg` type and
`step : Cfg → Option Cfg` function from the previous section. The key feature of this model is that
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

    inductive Γ'  | consₗ | cons | bit0 | bit1

We represent a number as a bit sequence, lists of numbers by putting `cons` after each element, and
lists of lists of natural numbers by putting `consₗ` after each list. For example:

    0 ~> []
    1 ~> [bit1]
    6 ~> [bit0, bit1, bit1]
    [1, 2] ~> [bit1, cons, bit0, bit1, cons]
    [[], [1, 2]] ~> [consₗ, bit1, cons, bit0, bit1, cons, consₗ]

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


set_option linter.uppercaseLean3 false

namespace PartrecToTM2

section

open ToPartrec

/-- The alphabet for the stacks in the program. `bit0` and `bit1` are used to represent `ℕ` values
as lists of binary digits, `cons` is used to separate `List ℕ` values, and `consₗ` is used to
separate `List (List ℕ)` values. See the section documentation. -/
inductive Γ'
  | consₗ
  | cons
  | bit0
  | bit1
  deriving DecidableEq, Inhabited, Fintype
#align turing.partrec_to_TM2.Γ' Turing.PartrecToTM2.Γ'
#align turing.partrec_to_TM2.Γ'.Cons Turing.PartrecToTM2.Γ'.consₗ
#align turing.partrec_to_TM2.Γ'.cons Turing.PartrecToTM2.Γ'.cons
#align turing.partrec_to_TM2.Γ'.bit0 Turing.PartrecToTM2.Γ'.bit0
#align turing.partrec_to_TM2.Γ'.bit1 Turing.PartrecToTM2.Γ'.bit1

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
#align turing.partrec_to_TM2.K' Turing.PartrecToTM2.K'
#align turing.partrec_to_TM2.K'.main Turing.PartrecToTM2.K'.main
#align turing.partrec_to_TM2.K'.rev Turing.PartrecToTM2.K'.rev
#align turing.partrec_to_TM2.K'.aux Turing.PartrecToTM2.K'.aux
#align turing.partrec_to_TM2.K'.stack Turing.PartrecToTM2.K'.stack

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
#align turing.partrec_to_TM2.cont' Turing.PartrecToTM2.Cont'
#align turing.partrec_to_TM2.cont'.halt Turing.PartrecToTM2.Cont'.halt
#align turing.partrec_to_TM2.cont'.cons₁ Turing.PartrecToTM2.Cont'.cons₁
#align turing.partrec_to_TM2.cont'.cons₂ Turing.PartrecToTM2.Cont'.cons₂
#align turing.partrec_to_TM2.cont'.comp Turing.PartrecToTM2.Cont'.comp
#align turing.partrec_to_TM2.cont'.fix Turing.PartrecToTM2.Cont'.fix

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
#align turing.partrec_to_TM2.Λ' Turing.PartrecToTM2.Λ'
#align turing.partrec_to_TM2.Λ'.move Turing.PartrecToTM2.Λ'.move
#align turing.partrec_to_TM2.Λ'.clear Turing.PartrecToTM2.Λ'.clear
#align turing.partrec_to_TM2.Λ'.copy Turing.PartrecToTM2.Λ'.copy
#align turing.partrec_to_TM2.Λ'.push Turing.PartrecToTM2.Λ'.push
#align turing.partrec_to_TM2.Λ'.read Turing.PartrecToTM2.Λ'.read
#align turing.partrec_to_TM2.Λ'.succ Turing.PartrecToTM2.Λ'.succ
#align turing.partrec_to_TM2.Λ'.pred Turing.PartrecToTM2.Λ'.pred
#align turing.partrec_to_TM2.Λ'.ret Turing.PartrecToTM2.Λ'.ret

-- Porting note: `Turing.PartrecToTM2.Λ'.rec` is noncomputable in Lean4, so we make it computable.
compile_inductive% Code
compile_inductive% Cont'
compile_inductive% K'
compile_inductive% Λ'

instance Λ'.instInhabited : Inhabited Λ' :=
  ⟨Λ'.ret Cont'.halt⟩
#align turing.partrec_to_TM2.Λ'.inhabited Turing.PartrecToTM2.Λ'.instInhabited

instance Λ'.instDecidableEq : DecidableEq Λ' := fun a b => by
  induction a generalizing b <;> cases b <;> try apply Decidable.isFalse; rintro ⟨⟨⟩⟩; done
                                             -- ⊢ Decidable (move p✝¹ k₁✝¹ k₂✝¹ q✝¹ = move p✝ k₁✝ k₂✝ q✝)
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ Decidable (clear p✝¹ k✝¹ q✝¹ = clear p✝ k✝ q✝)
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ Decidable (copy q✝¹ = copy q✝)
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ Decidable (push k✝¹ s✝¹ q✝¹ = push k✝ s✝ q✝)
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ Decidable (read f✝¹ = read f✝)
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ Decidable (succ q✝¹ = succ q✝)
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ Decidable (pred q₁✝¹ q₂✝¹ = pred q₁✝ q₂✝)
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- 🎉 no goals
                                             -- ⊢ Decidable (ret k✝¹ = ret k✝)
  case move.move _ _ _ _ I _ _ _ _ =>
    letI := I
    exact decidable_of_iff' _ (by simp [Function.funext_iff]; rfl)
  case clear.clear _ _ _ I _ _ _ =>
    letI := I
    exact decidable_of_iff' _ (by simp [Function.funext_iff]; rfl)
  case copy.copy _ I _ =>
    letI := I
    exact decidable_of_iff' _ (by simp [Function.funext_iff]; rfl)
  case push.push _ _ _ I _ _ _ =>
    letI := I
    exact decidable_of_iff' _ (by simp [Function.funext_iff]; rfl)
  case read.read _ I _ =>
    letI := I
    exact decidable_of_iff' _ (by simp [Function.funext_iff]; rfl)
  case succ.succ _ I _ =>
    letI := I
    exact decidable_of_iff' _ (by simp [Function.funext_iff]; rfl)
  case pred.pred _ _ I₁ I₂ _ _ =>
    letI := I₁
    letI := I₂
    exact decidable_of_iff' _ (by simp [Function.funext_iff]; rfl)
  case ret.ret _ _ =>
    exact decidable_of_iff' _ (by simp [Function.funext_iff]; rfl)
#align turing.partrec_to_TM2.Λ'.decidable_eq Turing.PartrecToTM2.Λ'.instDecidableEq

/-- The type of TM2 statements used by this machine. -/
def Stmt' :=
  TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited
#align turing.partrec_to_TM2.stmt' Turing.PartrecToTM2.Stmt'

/-- The type of TM2 configurations used by this machine. -/
def Cfg' :=
  TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited
#align turing.partrec_to_TM2.cfg' Turing.PartrecToTM2.Cfg'

open TM2.Stmt

/-- A predicate that detects the end of a natural number, either `Γ'.cons` or `Γ'.consₗ` (or
implicitly the end of the list), for use in predicate-taking functions like `move` and `clear`. -/
@[simp]
def natEnd : Γ' → Bool
  | Γ'.consₗ => true
  | Γ'.cons => true
  | _ => false
#align turing.partrec_to_TM2.nat_end Turing.PartrecToTM2.natEnd

/-- Pop a value from the stack and place the result in local store. -/
@[simp]
def pop' (k : K') : Stmt' → Stmt' :=
  pop k fun _ v => v
#align turing.partrec_to_TM2.pop' Turing.PartrecToTM2.pop'

/-- Peek a value from the stack and place the result in local store. -/
@[simp]
def peek' (k : K') : Stmt' → Stmt' :=
  peek k fun _ v => v
#align turing.partrec_to_TM2.peek' Turing.PartrecToTM2.peek'

/-- Push the value in the local store to the given stack. -/
@[simp]
def push' (k : K') : Stmt' → Stmt' :=
  push k fun x => x.iget
#align turing.partrec_to_TM2.push' Turing.PartrecToTM2.push'

/-- Move everything from the `rev` stack to the `main` stack (reversed). -/
def unrev :=
  Λ'.move (fun _ => false) rev main
#align turing.partrec_to_TM2.unrev Turing.PartrecToTM2.unrev

/-- Move elements from `k₁` to `k₂` while `p` holds, with the last element being left on `k₁`. -/
def moveExcl (p k₁ k₂ q) :=
  Λ'.move p k₁ k₂ <| Λ'.push k₁ id q
#align turing.partrec_to_TM2.move_excl Turing.PartrecToTM2.moveExcl

/-- Move elements from `k₁` to `k₂` without reversion, by performing a double move via the `rev`
stack. -/
def move₂ (p k₁ k₂ q) :=
  moveExcl p k₁ rev <| Λ'.move (fun _ => false) rev k₂ q
#align turing.partrec_to_TM2.move₂ Turing.PartrecToTM2.move₂

/-- Assuming `trList v` is on the front of stack `k`, remove it, and push `v.headI` onto `main`.
See the section documentation. -/
def head (k : K') (q : Λ') : Λ' :=
  Λ'.move natEnd k rev <|
    (Λ'.push rev fun _ => some Γ'.cons) <|
      Λ'.read fun s =>
        (if s = some Γ'.consₗ then id else Λ'.clear (fun x => x = Γ'.consₗ) k) <| unrev q
#align turing.partrec_to_TM2.head Turing.PartrecToTM2.head

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
#align turing.partrec_to_TM2.tr_normal Turing.PartrecToTM2.trNormal

/-- The main program. See the section documentation for details. -/
def tr : Λ' → Stmt'
  | Λ'.move p k₁ k₂ q =>
    pop' k₁ <|
      branch (fun s => s.elim true p) (goto fun _ => q)
        (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)
  | Λ'.push k f q =>
    branch (fun s => (f s).isSome) ((push k fun s => (f s).iget) <| goto fun _ => q)
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
        branch (fun s => natEnd s.iget) (goto fun _ => q₁)
          (peek' main <|
            branch (fun s => natEnd s.iget) (goto fun _ => unrev q₂)
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
        cond (natEnd s.iget) (Λ'.ret k) <| Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)
  | Λ'.ret Cont'.halt => (load fun _ => none) <| halt
#align turing.partrec_to_TM2.tr Turing.PartrecToTM2.tr

/- Porting note: The equation lemma of `tr` simplifies to `match` structures. To prevent this,
we replace equation lemmas of `tr`. -/

theorem tr_move (p k₁ k₂ q) : tr (Λ'.move p k₁ k₂ q) =
  pop' k₁ (branch (fun s => s.elim true p) (goto fun _ => q)
      (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)) := rfl

theorem tr_push (k f q) : tr (Λ'.push k f q) = branch (fun s => (f s).isSome)
    ((push k fun s => (f s).iget) <| goto fun _ => q) (goto fun _ => q) := rfl

theorem tr_read (q) : tr (Λ'.read q) = goto q := rfl

theorem tr_clear (p k q) : tr (Λ'.clear p k q) = pop' k (branch
    (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)) := rfl

theorem tr_copy (q) : tr (Λ'.copy q) = pop' rev (branch Option.isSome
    (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)) := rfl

theorem tr_succ (q) : tr (Λ'.succ q) = pop' main (branch (fun s => s = some Γ'.bit1)
    ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q) <|
      branch (fun s => s = some Γ'.cons)
        ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
        ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)) := rfl

theorem tr_pred (q₁ q₂) : tr (Λ'.pred q₁ q₂) = pop' main (branch (fun s => s = some Γ'.bit0)
      ((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂) <|
    branch (fun s => natEnd s.iget) (goto fun _ => q₁)
      (peek' main <|
        branch (fun s => natEnd s.iget) (goto fun _ => unrev q₂)
          ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))) := rfl

theorem tr_ret_cons₁ (fs k) : tr (Λ'.ret (Cont'.cons₁ fs k)) = goto fun _ =>
    move₂ (fun _ => false) main aux <|
      move₂ (fun s => s = Γ'.consₗ) stack main <|
        move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k) := rfl

theorem tr_ret_cons₂ (k) : tr (Λ'.ret (Cont'.cons₂ k)) =
    goto fun _ => head stack <| Λ'.ret k := rfl

theorem tr_ret_comp (f k) : tr (Λ'.ret (Cont'.comp f k)) = goto fun _ => trNormal f k := rfl

theorem tr_ret_fix (f k) : tr (Λ'.ret (Cont'.fix f k)) = pop' main (goto fun s =>
    cond (natEnd s.iget) (Λ'.ret k) <| Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) := rfl

theorem tr_ret_halt : tr (Λ'.ret Cont'.halt) = (load fun _ => none) halt := rfl

attribute
  [eqns tr_move tr_push tr_read tr_clear tr_copy tr_succ tr_pred tr_ret_cons₁
    tr_ret_cons₂ tr_ret_comp tr_ret_fix tr_ret_halt] tr
attribute [simp] tr

/-- Translating a `Cont` continuation to a `Cont'` continuation simply entails dropping all the
data. This data is instead encoded in `trContStack` in the configuration. -/
def trCont : Cont → Cont'
  | Cont.halt => Cont'.halt
  | Cont.cons₁ c _ k => Cont'.cons₁ c (trCont k)
  | Cont.cons₂ _ k => Cont'.cons₂ (trCont k)
  | Cont.comp c k => Cont'.comp c (trCont k)
  | Cont.fix c k => Cont'.fix c (trCont k)
#align turing.partrec_to_TM2.tr_cont Turing.PartrecToTM2.trCont

/-- We use `PosNum` to define the translation of binary natural numbers. A natural number is
represented as a little-endian list of `bit0` and `bit1` elements:

    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]

In particular, this representation guarantees no trailing `bit0`'s at the end of the list. -/
def trPosNum : PosNum → List Γ'
  | PosNum.one => [Γ'.bit1]
  | PosNum.bit0 n => Γ'.bit0 :: trPosNum n
  | PosNum.bit1 n => Γ'.bit1 :: trPosNum n
#align turing.partrec_to_TM2.tr_pos_num Turing.PartrecToTM2.trPosNum

/-- We use `Num` to define the translation of binary natural numbers. Positive numbers are
translated using `trPosNum`, and `trNum 0 = []`. So there are never any trailing `bit0`'s in
a translated `Num`.

    0 = []
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
-/
def trNum : Num → List Γ'
  | Num.zero => []
  | Num.pos n => trPosNum n
#align turing.partrec_to_TM2.tr_num Turing.PartrecToTM2.trNum

/-- Because we use binary encoding, we define `trNat` in terms of `trNum`, using `Num`, which are
binary natural numbers. (We could also use `Nat.binaryRecOn`, but `Num` and `PosNum` make for
easy inductions.) -/
def trNat (n : ℕ) : List Γ' :=
  trNum n
#align turing.partrec_to_TM2.tr_nat Turing.PartrecToTM2.trNat

@[simp]
theorem trNat_zero : trNat 0 = [] := by rw [trNat, Nat.cast_zero]; rfl
                                        -- ⊢ trNum 0 = []
                                                                   -- 🎉 no goals
#align turing.partrec_to_TM2.tr_nat_zero Turing.PartrecToTM2.trNat_zero

@[simp]
theorem trNat_default : trNat default = [] :=
  trNat_zero
#align turing.partrec_to_TM2.tr_nat_default Turing.PartrecToTM2.trNat_default

/-- Lists are translated with a `cons` after each encoded number.
For example:

    [] = []
    [0] = [cons]
    [1] = [bit1, cons]
    [6, 0] = [bit0, bit1, bit1, cons, cons]
-/
@[simp]
def trList : List ℕ → List Γ'
  | [] => []
  | n::ns => trNat n ++ Γ'.cons :: trList ns
#align turing.partrec_to_TM2.tr_list Turing.PartrecToTM2.trList

/-- Lists of lists are translated with a `consₗ` after each encoded list.
For example:

    [] = []
    [[]] = [consₗ]
    [[], []] = [consₗ, consₗ]
    [[0]] = [cons, consₗ]
    [[1, 2], [0]] = [bit1, cons, bit0, bit1, cons, consₗ, cons, consₗ]
-/
@[simp]
def trLList : List (List ℕ) → List Γ'
  | [] => []
  | l::ls => trList l ++ Γ'.consₗ :: trLList ls
#align turing.partrec_to_TM2.tr_llist Turing.PartrecToTM2.trLList

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `trLList`. -/
@[simp]
def contStack : Cont → List (List ℕ)
  | Cont.halt => []
  | Cont.cons₁ _ ns k => ns :: contStack k
  | Cont.cons₂ ns k => ns :: contStack k
  | Cont.comp _ k => contStack k
  | Cont.fix _ k => contStack k
#align turing.partrec_to_TM2.cont_stack Turing.PartrecToTM2.contStack

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `trLList`. -/
def trContStack (k : Cont) :=
  trLList (contStack k)
#align turing.partrec_to_TM2.tr_cont_stack Turing.PartrecToTM2.trContStack

/-- This is the nondependent eliminator for `K'`, but we use it specifically here in order to
represent the stack data as four lists rather than as a function `K' → List Γ'`, because this makes
rewrites easier. The theorems `K'.elim_update_main` et. al. show how such a function is updated
after an `update` to one of the components. -/
def K'.elim (a b c d : List Γ') : K' → List Γ'
  | K'.main => a
  | K'.rev => b
  | K'.aux => c
  | K'.stack => d
#align turing.partrec_to_TM2.K'.elim Turing.PartrecToTM2.K'.elim

/- Porting note: The equation lemma of `elim` simplifies to `match` structures. To prevent this,
we replace equation lemmas of `elim`. -/

theorem K'.elim_main (a b c d) : K'.elim a b c d K'.main = a := rfl

theorem K'.elim_rev (a b c d) : K'.elim a b c d K'.rev = b := rfl

theorem K'.elim_aux (a b c d) : K'.elim a b c d K'.aux = c := rfl

theorem K'.elim_stack (a b c d) : K'.elim a b c d K'.stack = d := rfl

attribute [eqns K'.elim_main K'.elim_rev K'.elim_aux K'.elim_stack] K'.elim
attribute [simp] K'.elim

@[simp]
theorem K'.elim_update_main {a b c d a'} : update (K'.elim a b c d) main a' = K'.elim a' b c d := by
  funext x; cases x <;> rfl
  -- ⊢ update (elim a b c d) main a' x = elim a' b c d x
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
#align turing.partrec_to_TM2.K'.elim_update_main Turing.PartrecToTM2.K'.elim_update_main

@[simp]
theorem K'.elim_update_rev {a b c d b'} : update (K'.elim a b c d) rev b' = K'.elim a b' c d := by
  funext x; cases x <;> rfl
  -- ⊢ update (elim a b c d) rev b' x = elim a b' c d x
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
#align turing.partrec_to_TM2.K'.elim_update_rev Turing.PartrecToTM2.K'.elim_update_rev

@[simp]
theorem K'.elim_update_aux {a b c d c'} : update (K'.elim a b c d) aux c' = K'.elim a b c' d := by
  funext x; cases x <;> rfl
  -- ⊢ update (elim a b c d) aux c' x = elim a b c' d x
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
#align turing.partrec_to_TM2.K'.elim_update_aux Turing.PartrecToTM2.K'.elim_update_aux

@[simp]
theorem K'.elim_update_stack {a b c d d'} : update (K'.elim a b c d) stack d' = K'.elim a b c d' :=
  by funext x; cases x <;> rfl
     -- ⊢ update (elim a b c d) stack d' x = elim a b c d' x
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
#align turing.partrec_to_TM2.K'.elim_update_stack Turing.PartrecToTM2.K'.elim_update_stack

/-- The halting state corresponding to a `List ℕ` output value. -/
def halt (v : List ℕ) : Cfg' :=
  ⟨none, none, K'.elim (trList v) [] [] []⟩
#align turing.partrec_to_TM2.halt Turing.PartrecToTM2.halt

/-- The `Cfg` states map to `Cfg'` states almost one to one, except that in normal operation the
local store contains an arbitrary garbage value. To make the final theorem cleaner we explicitly
clear it in the halt state so that there is exactly one configuration corresponding to output `v`.
-/
def TrCfg : Cfg → Cfg' → Prop
  | Cfg.ret k v, c' =>
    ∃ s, c' = ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩
  | Cfg.halt v, c' => c' = halt v
#align turing.partrec_to_TM2.tr_cfg Turing.PartrecToTM2.TrCfg

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
#align turing.partrec_to_TM2.split_at_pred Turing.PartrecToTM2.splitAtPred

theorem splitAtPred_eq {α} (p : α → Bool) :
    ∀ L l₁ o l₂,
      (∀ x ∈ l₁, p x = false) →
        Option.elim' (L = l₁ ∧ l₂ = []) (fun a => p a = true ∧ L = l₁ ++ a::l₂) o →
          splitAtPred p L = (l₁, o, l₂)
  | [], _, none, _, _, ⟨rfl, rfl⟩ => rfl
  | [], l₁, some o, l₂, _, ⟨_, h₃⟩ => by simp at h₃
                                         -- 🎉 no goals
  | a :: L, l₁, o, l₂, h₁, h₂ => by
    rw [splitAtPred]
    -- ⊢ (bif p a then ([], some a, L)
    have IH := splitAtPred_eq p L
    -- ⊢ (bif p a then ([], some a, L)
    cases' o with o
    · cases' l₁ with a' l₁ <;> rcases h₂ with ⟨⟨⟩, rfl⟩
                               -- 🎉 no goals
                               -- ⊢ (bif p a then ([], some a, L)
      rw [h₁ a (List.Mem.head _), cond, IH L none [] _ ⟨rfl, rfl⟩]
      -- ⊢ ∀ (x : α), x ∈ L → p x = false
      exact fun x h => h₁ x (List.Mem.tail _ h)
      -- 🎉 no goals
    · cases' l₁ with a' l₁ <;> rcases h₂ with ⟨h₂, ⟨⟩⟩
                               -- ⊢ (bif p a then ([], some a, L)
                               -- ⊢ (bif p a then ([], some a, List.append l₁ (o :: l₂))
      · rw [h₂, cond]
        -- 🎉 no goals
      rw [h₁ a (List.Mem.head _), cond, IH l₁ (some o) l₂ _ ⟨h₂, _⟩] <;> try rfl
      -- ⊢ ∀ (x : α), x ∈ l₁ → p x = false
                                                                         -- ⊢ ∀ (x : α), x ∈ l₁ → p x = false
                                                                         -- 🎉 no goals
      exact fun x h => h₁ x (List.Mem.tail _ h)
      -- 🎉 no goals
#align turing.partrec_to_TM2.split_at_pred_eq Turing.PartrecToTM2.splitAtPred_eq

theorem splitAtPred_false {α} (L : List α) : splitAtPred (fun _ => false) L = (L, none, []) :=
  splitAtPred_eq _ _ _ _ _ (fun _ _ => rfl) ⟨rfl, rfl⟩
#align turing.partrec_to_TM2.split_at_pred_ff Turing.PartrecToTM2.splitAtPred_false

theorem move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ k₂)
    (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.move p k₁ k₂ q), s, S⟩
      ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverseAux (S k₂))⟩ := by
  induction' L₁ with a L₁ IH generalizing S s
  -- ⊢ Reaches₁ (TM2.step tr) { l := some (Λ'.move p k₁ k₂ q), var := s, stk := S } …
  · rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    -- ⊢ Reaches₁ (TM2.step tr) { l := some (Λ'.move p k₁ k₂ q), var := s, stk := S } …
    swap
    -- ⊢ List.reverseAux [] (S k₂) = update S k₁ L₂ k₂
    · rw [Function.update_noteq h₁.symm]
      -- ⊢ List.reverseAux [] (S k₂) = S k₂
      rfl
      -- 🎉 no goals
    refine' TransGen.head' rfl _
    -- ⊢ ReflTransGen (fun a b => b ∈ TM2.step tr a) (TM2.stepAux (tr (Λ'.move p k₁ k …
    simp
    -- ⊢ ReflTransGen
    revert e; cases' S k₁ with a Sk <;> intro e
    -- ⊢ splitAtPred p (S k₁) = ([], o, L₂) →
                                        -- ⊢ ReflTransGen
                                        -- ⊢ ReflTransGen
    · cases e
      -- ⊢ ReflTransGen
      rfl
      -- 🎉 no goals
    simp only [splitAtPred, Option.elim, List.head?, List.tail_cons, Option.iget_some] at e ⊢
    -- ⊢ ReflTransGen
    revert e; cases p a <;> intro e <;>
    -- ⊢ (bif p a then ([], some a, Sk) else (a :: (splitAtPred p Sk).fst, (splitAtPr …
                            -- ⊢ ReflTransGen
                            -- ⊢ ReflTransGen
      simp only [cond_false, cond_true, Prod.mk.injEq, true_and, false_and] at e ⊢
      -- 🎉 no goals
      -- ⊢ ReflTransGen
    · simp only [e]
      -- ⊢ ReflTransGen
      rfl
      -- 🎉 no goals
  · refine' TransGen.head rfl _
    -- ⊢ TransGen (fun a b => b ∈ TM2.step tr a) (TM2.stepAux (tr (Λ'.move p k₁ k₂ q) …
    simp
    -- ⊢ TransGen
    cases' e₁ : S k₁ with a' Sk <;> rw [e₁, splitAtPred] at e
                                    -- ⊢ TransGen
                                    -- ⊢ TransGen
    · cases e
      -- 🎉 no goals
    cases e₂ : p a' <;> simp only [e₂, cond] at e
                        -- ⊢ TransGen
                        -- ⊢ TransGen
    swap
    · cases e
      -- 🎉 no goals
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    -- ⊢ TransGen
    rw [e₃] at e
    -- ⊢ TransGen
    cases e
    -- ⊢ TransGen
    simp [e₂]
    -- ⊢ TransGen
    convert @IH _ (update (update S k₁ Sk) k₂ (a :: S k₂)) _ using 2 <;>
      simp [Function.update_noteq, h₁, h₁.symm, e₃, List.reverseAux]
      -- 🎉 no goals
      -- ⊢ update (update S k₁ snd✝) k₂ (List.reverseAux fst✝¹ (a :: S k₂)) = update (u …
      -- 🎉 no goals
    simp [Function.update_comm h₁.symm]
    -- 🎉 no goals
#align turing.partrec_to_TM2.move_ok Turing.PartrecToTM2.move_ok

theorem unrev_ok {q s} {S : K' → List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (unrev q), s, S⟩
      ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (S main))⟩ :=
  move_ok (by decide) <| splitAtPred_false _
              -- 🎉 no goals
#align turing.partrec_to_TM2.unrev_ok Turing.PartrecToTM2.unrev_ok

theorem move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂)
    (h₂ : S rev = []) (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (move₂ p k₁ k₂ q), s, S⟩
      ⟨some q, none, update (update S k₁ (o.elim id List.cons L₂)) k₂ (L₁ ++ S k₂)⟩ := by
  refine' (move_ok h₁.1 e).trans (TransGen.head rfl _)
  -- ⊢ TransGen (fun a b => b ∈ TM2.step tr a) (TM2.stepAux (tr (Λ'.push k₁ id (Λ'. …
  simp
  -- ⊢ TransGen
  cases o <;> simp only [Option.elim, id.def]
              -- ⊢ TransGen
              -- ⊢ TransGen
  · simp only [TM2.stepAux, Option.isSome, cond_false]
    -- ⊢ TransGen
    convert move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    -- ⊢ update (update S k₁ L₂) k₂ (L₁ ++ S k₂) = update (update (update (update S k …
    simp only [Function.update_comm h₁.1, Function.update_idem]
    -- ⊢ update (update S k₁ L₂) k₂ (L₁ ++ S k₂) = update (update (update S rev []) k …
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    -- ⊢ update (update S k₁ L₂) k₂ (L₁ ++ S k₂) = update (update S k₁ L₂) k₂ (List.r …
    simp only [Function.update_noteq h₁.2.2.symm, Function.update_noteq h₁.2.1,
      Function.update_noteq h₁.1.symm, List.reverseAux_eq, h₂, Function.update_same,
      List.append_nil, List.reverse_reverse]
  · simp only [TM2.stepAux, Option.isSome, cond_true]
    -- ⊢ TransGen
    convert move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    -- ⊢ update (update S k₁ (val✝ :: L₂)) k₂ (L₁ ++ S k₂) = update (update (update ( …
    simp only [h₂, Function.update_comm h₁.1, List.reverseAux_eq, Function.update_same,
      List.append_nil, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    -- ⊢ update (update S k₁ (val✝ :: L₂)) k₂ (L₁ ++ S k₂) = update (update S k₁ (Opt …
    simp only [Function.update_noteq h₁.1.symm, Function.update_noteq h₁.2.2.symm,
      Function.update_noteq h₁.2.1, Function.update_same, List.reverse_reverse]
#align turing.partrec_to_TM2.move₂_ok Turing.PartrecToTM2.move₂_ok

theorem clear_ok {p k q s L₁ o L₂} {S : K' → List Γ'} (e : splitAtPred p (S k) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.clear p k q), s, S⟩ ⟨some q, o, update S k L₂⟩ := by
  induction' L₁ with a L₁ IH generalizing S s
  -- ⊢ Reaches₁ (TM2.step tr) { l := some (Λ'.clear p k q), var := s, stk := S } {  …
  · refine' TransGen.head' rfl _
    -- ⊢ ReflTransGen (fun a b => b ∈ TM2.step tr a) (TM2.stepAux (tr (Λ'.clear p k q …
    simp
    -- ⊢ ReflTransGen
    revert e; cases' S k with a Sk <;> intro e
    -- ⊢ splitAtPred p (S k) = ([], o, L₂) →
                                       -- ⊢ ReflTransGen
                                       -- ⊢ ReflTransGen
    · cases e
      -- ⊢ ReflTransGen
      rfl
      -- 🎉 no goals
    simp only [splitAtPred, Option.elim, List.head?, List.tail_cons] at e ⊢
    -- ⊢ ReflTransGen
    revert e; cases p a <;> intro e <;>
    -- ⊢ (bif p a then ([], some a, Sk) else (a :: (splitAtPred p Sk).fst, (splitAtPr …
                            -- ⊢ ReflTransGen
                            -- ⊢ ReflTransGen
      simp only [cond_false, cond_true, Prod.mk.injEq, true_and, false_and] at e ⊢
      -- 🎉 no goals
      -- ⊢ ReflTransGen
    · rcases e with ⟨e₁, e₂⟩
      -- ⊢ ReflTransGen
      rw [e₁, e₂]
      -- 🎉 no goals
  · refine' TransGen.head rfl _
    -- ⊢ TransGen (fun a b => b ∈ TM2.step tr a) (TM2.stepAux (tr (Λ'.clear p k q)) s …
    simp
    -- ⊢ TransGen
    cases' e₁ : S k with a' Sk <;> rw [e₁, splitAtPred] at e
                                   -- ⊢ TransGen
                                   -- ⊢ TransGen
    · cases e
      -- 🎉 no goals
    cases e₂ : p a' <;> simp only [e₂, cond] at e
                        -- ⊢ TransGen
                        -- ⊢ TransGen
    swap
    · cases e
      -- 🎉 no goals
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    -- ⊢ TransGen
    rw [e₃] at e
    -- ⊢ TransGen
    cases e
    -- ⊢ TransGen
    simp [e₂]
    -- ⊢ TransGen
    convert @IH _ (update S k Sk) _ using 2 <;> simp [e₃]
    -- ⊢ update S k snd✝ = update (update S k Sk) k (fst✝¹, fst✝, snd✝).2.snd
                                                -- 🎉 no goals
                                                -- 🎉 no goals
#align turing.partrec_to_TM2.clear_ok Turing.PartrecToTM2.clear_ok

theorem copy_ok (q s a b c d) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.copy q), s, K'.elim a b c d⟩
      ⟨some q, none, K'.elim (List.reverseAux b a) [] c (List.reverseAux b d)⟩ := by
  induction' b with x b IH generalizing a d s
  -- ⊢ Reaches₁ (TM2.step tr) { l := some (Λ'.copy q), var := s, stk := elim a [] c …
  · refine' TransGen.single _
    -- ⊢ { l := some q, var := none, stk := elim (List.reverseAux [] a) [] c (List.re …
    simp
    -- 🎉 no goals
  refine' TransGen.head rfl _
  -- ⊢ TransGen (fun a b => b ∈ TM2.step tr a) (TM2.stepAux (tr (Λ'.copy q)) s (eli …
  simp
  -- ⊢ TransGen
  exact IH _ _ _
  -- 🎉 no goals
#align turing.partrec_to_TM2.copy_ok Turing.PartrecToTM2.copy_ok

theorem trPosNum_natEnd : ∀ (n), ∀ x ∈ trPosNum n, natEnd x = false
  | PosNum.one, _, List.Mem.head _ => rfl
  | PosNum.bit0 _, _, List.Mem.head _ => rfl
  | PosNum.bit0 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h
  | PosNum.bit1 _, _, List.Mem.head _ => rfl
  | PosNum.bit1 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h
#align turing.partrec_to_TM2.tr_pos_num_nat_end Turing.PartrecToTM2.trPosNum_natEnd

theorem trNum_natEnd : ∀ (n), ∀ x ∈ trNum n, natEnd x = false
  | Num.pos n, x, h => trPosNum_natEnd n x h
#align turing.partrec_to_TM2.tr_num_nat_end Turing.PartrecToTM2.trNum_natEnd

theorem trNat_natEnd (n) : ∀ x ∈ trNat n, natEnd x = false :=
  trNum_natEnd _
#align turing.partrec_to_TM2.tr_nat_nat_end Turing.PartrecToTM2.trNat_natEnd

theorem trList_ne_consₗ : ∀ (l), ∀ x ∈ trList l, x ≠ Γ'.consₗ
  | a :: l, x, h => by
    simp [trList] at h
    -- ⊢ x ≠ Γ'.consₗ
    obtain h | rfl | h := h
    · rintro rfl
      -- ⊢ False
      cases trNat_natEnd _ _ h
      -- 🎉 no goals
    · rintro ⟨⟩
      -- 🎉 no goals
    · exact trList_ne_consₗ l _ h
      -- 🎉 no goals
#align turing.partrec_to_TM2.tr_list_ne_Cons Turing.PartrecToTM2.trList_ne_consₗ

theorem head_main_ok {q s L} {c d : List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (head main q), s, K'.elim (trList L) [] c d⟩
      ⟨some q, none, K'.elim (trList [L.headI]) [] c d⟩ := by
  let o : Option Γ' := List.casesOn L none fun _ _ => some Γ'.cons
  -- ⊢ Reaches₁ (TM2.step tr) { l := some (head main q), var := s, stk := elim (trL …
  refine'
    (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat L.headI) o (trList L.tail) (trNat_natEnd _) _)).trans
      (TransGen.head rfl (TransGen.head rfl _))
  · cases L <;> simp
    -- ⊢ Option.elim' (elim (trList []) [] c d main = trNat (List.headI []) ∧ trList  …
                -- 🎉 no goals
                -- 🎉 no goals
  simp
  -- ⊢ TransGen
  rw [if_neg (show o ≠ some Γ'.consₗ by cases L <;> simp)]
  -- ⊢ TransGen
  refine' (clear_ok (splitAtPred_eq _ _ _ none [] _ ⟨rfl, rfl⟩)).trans _
  -- ⊢ ∀ (x : Γ'), x ∈ elim (trList (List.tail L)) (Option.iget (some Γ'.cons) :: L …
  · exact fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)
    -- 🎉 no goals
  convert unrev_ok using 2; simp [List.reverseAux_eq]
  -- ⊢ elim (trNat (List.headI L) ++ [Γ'.cons]) [] c d = update (update (update (el …
                            -- 🎉 no goals
#align turing.partrec_to_TM2.head_main_ok Turing.PartrecToTM2.head_main_ok

theorem head_stack_ok {q s L₁ L₂ L₃} :
    Reaches₁ (TM2.step tr)
      ⟨some (head stack q), s, K'.elim (trList L₁) [] [] (trList L₂ ++ Γ'.consₗ :: L₃)⟩
      ⟨some q, none, K'.elim (trList (L₂.headI :: L₁)) [] [] L₃⟩ := by
  cases' L₂ with a L₂
  -- ⊢ Reaches₁ (TM2.step tr) { l := some (head stack q), var := s, stk := elim (tr …
  · refine'
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ [] (some Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
        (TransGen.head rfl (TransGen.head rfl _))
    simp
    -- ⊢ TransGen
    convert unrev_ok using 2
    -- ⊢ elim (Γ'.cons :: trList L₁) [] [] L₃ = update (update (elim (trList L₁) [Opt …
    simp
    -- 🎉 no goals
  · refine'
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat a) (some Γ'.cons) (trList L₂ ++ Γ'.consₗ :: L₃)
            (trNat_natEnd _) ⟨rfl, by simp⟩))
        (TransGen.head rfl (TransGen.head rfl _))
    simp
    -- ⊢ TransGen
    refine'
      TransGen.trans
        (clear_ok
          (splitAtPred_eq _ _ (trList L₂) (some Γ'.consₗ) L₃
            (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, by simp⟩))
        _
    convert unrev_ok using 2
    -- ⊢ elim (trNat a ++ Γ'.cons :: trList L₁) [] [] L₃ = update (update (update (el …
    simp [List.reverseAux_eq]
    -- 🎉 no goals
#align turing.partrec_to_TM2.head_stack_ok Turing.PartrecToTM2.head_stack_ok

theorem succ_ok {q s n} {c d : List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.succ q), s, K'.elim (trList [n]) [] c d⟩
      ⟨some q, none, K'.elim (trList [n.succ]) [] c d⟩ := by
  simp [trNat, Num.add_one]
  -- ⊢ Reaches₁
  cases' (n : Num) with a
  · refine' TransGen.head rfl _
    -- ⊢ TransGen
    simp
    -- ⊢ TransGen
    convert unrev_ok using 2
    -- ⊢ elim (trNum (Num.succ Num.zero) ++ [Γ'.cons]) [] c d = update (update (elim  …
    simp
    -- ⊢ elim (trNum (Num.succ Num.zero) ++ [Γ'.cons]) [] c d = elim (Γ'.bit1 :: Γ'.c …
    rfl
    -- 🎉 no goals
  simp [Num.succ, trNum, Num.succ']
  -- ⊢ Reaches₁
  suffices ∀ l₁, ∃ l₁' l₂' s',
      List.reverseAux l₁ (trPosNum a.succ) = List.reverseAux l₁' l₂' ∧
        Reaches₁ (TM2.step tr) ⟨some q.succ, s, K'.elim (trPosNum a ++ [Γ'.cons]) l₁ c d⟩
          ⟨some (unrev q), s', K'.elim (l₂' ++ [Γ'.cons]) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp [List.reverseAux] at e
    refine' h.trans _
    convert unrev_ok using 2
    simp [e, List.reverseAux_eq]
  induction' a with m IH m _ generalizing s <;> intro l₁
                                                -- ⊢ ∃ l₁' l₂' s', List.reverseAux l₁ (trPosNum (PosNum.succ PosNum.one)) = List. …
                                                -- ⊢ ∃ l₁' l₂' s', List.reverseAux l₁ (trPosNum (PosNum.succ (PosNum.bit1 m))) =  …
                                                -- ⊢ ∃ l₁' l₂' s', List.reverseAux l₁ (trPosNum (PosNum.succ (PosNum.bit0 m))) =  …
  · refine' ⟨Γ'.bit0 :: l₁, [Γ'.bit1], some Γ'.cons, rfl, TransGen.head rfl (TransGen.single _)⟩
    -- ⊢ { l := some (unrev q), var := some Γ'.cons, stk := elim ([Γ'.bit1] ++ [Γ'.co …
    simp [trPosNum]
    -- 🎉 no goals
  · obtain ⟨l₁', l₂', s', e, h⟩ := IH (Γ'.bit0 :: l₁)
    -- ⊢ ∃ l₁' l₂' s', List.reverseAux l₁ (trPosNum (PosNum.succ (PosNum.bit1 m))) =  …
    refine' ⟨l₁', l₂', s', e, TransGen.head _ h⟩
    -- ⊢ Option Γ'
    swap
    -- ⊢ { l := some (Λ'.succ q), var := ?pos.bit1.intro.intro.intro.intro.refine'_1, …
    simp [PosNum.succ, trPosNum]
    -- ⊢ some Γ'.bit1 = ?pos.bit1.intro.intro.intro.intro.refine'_1
    rfl
    -- 🎉 no goals
  · refine' ⟨l₁, _, some Γ'.bit0, rfl, TransGen.single _⟩
    -- ⊢ { l := some (unrev q), var := some Γ'.bit0, stk := elim (trPosNum (PosNum.su …
    simp
    -- ⊢ (bif decide (List.head? (trPosNum (PosNum.bit0 m) ++ [Γ'.cons]) = some Γ'.bi …
    rfl
    -- 🎉 no goals
#align turing.partrec_to_TM2.succ_ok Turing.PartrecToTM2.succ_ok

theorem pred_ok (q₁ q₂ s v) (c d : List Γ') : ∃ s',
    Reaches₁ (TM2.step tr) ⟨some (Λ'.pred q₁ q₂), s, K'.elim (trList v) [] c d⟩
      (v.headI.rec ⟨some q₁, s', K'.elim (trList v.tail) [] c d⟩ fun n _ =>
        ⟨some q₂, s', K'.elim (trList (n::v.tail)) [] c d⟩) := by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine' ⟨none, TransGen.single _⟩
    -- ⊢ Nat.rec { l := some q₁, var := none, stk := elim (trList (List.tail [])) []  …
    simp
    -- ⊢ { l := some q₁, var := none, stk := elim [] [] c d } = Nat.rec { l := some q …
    rfl
    -- 🎉 no goals
  · refine' ⟨some Γ'.cons, TransGen.single _⟩
    -- ⊢ Nat.rec { l := some q₁, var := some Γ'.cons, stk := elim (trList (List.tail  …
    simp
    -- 🎉 no goals
  refine' ⟨none, _⟩
  -- ⊢ Reaches₁ (TM2.step tr) { l := some (Λ'.pred q₁ q₂), var := s, stk := elim (t …
  simp [trNat, Num.add_one, Num.succ, trNum]
  -- ⊢ Reaches₁
  cases' (n : Num) with a
  · simp [trPosNum, trNum, show Num.zero.succ' = PosNum.one from rfl]
    -- ⊢ Reaches₁
    refine' TransGen.head rfl _
    -- ⊢ TransGen
    simp
    -- ⊢ TransGen
    convert unrev_ok using 2
    -- ⊢ elim (Γ'.cons :: trList v) [] c d = update (update (elim (Γ'.cons :: trList  …
    simp
    -- 🎉 no goals
  simp [trNum, Num.succ']
  -- ⊢ Reaches₁
  suffices ∀ l₁, ∃ l₁' l₂' s',
    List.reverseAux l₁ (trPosNum a) = List.reverseAux l₁' l₂' ∧
      Reaches₁ (TM2.step tr)
        ⟨some (q₁.pred q₂), s, K'.elim (trPosNum a.succ ++ Γ'.cons :: trList v) l₁ c d⟩
        ⟨some (unrev q₂), s', K'.elim (l₂' ++ Γ'.cons :: trList v) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp [List.reverseAux] at e
    refine' h.trans _
    convert unrev_ok using 2
    simp [e, List.reverseAux_eq]
  induction' a with m IH m IH generalizing s <;> intro l₁
                                                 -- ⊢ ∃ l₁' l₂' s', List.reverseAux l₁ (trPosNum PosNum.one) = List.reverseAux l₁' …
                                                 -- ⊢ ∃ l₁' l₂' s', List.reverseAux l₁ (trPosNum (PosNum.bit1 m)) = List.reverseAu …
                                                 -- ⊢ ∃ l₁' l₂' s', List.reverseAux l₁ (trPosNum (PosNum.bit0 m)) = List.reverseAu …
  · refine' ⟨Γ'.bit1::l₁, [], some Γ'.cons, rfl, TransGen.head rfl (TransGen.single _)⟩
    -- ⊢ { l := some (unrev q₂), var := some Γ'.cons, stk := elim ([] ++ Γ'.cons :: t …
    simp [trPosNum, show PosNum.one.succ = PosNum.one.bit0 from rfl]
    -- 🎉 no goals
  · obtain ⟨l₁', l₂', s', e, h⟩ := IH (some Γ'.bit0) (Γ'.bit1 :: l₁)
    -- ⊢ ∃ l₁' l₂' s', List.reverseAux l₁ (trPosNum (PosNum.bit1 m)) = List.reverseAu …
    refine' ⟨l₁', l₂', s', e, TransGen.head _ h⟩
    -- ⊢ { l := some (Λ'.pred q₁ q₂), var := some Γ'.bit0, stk := elim (trPosNum (Pos …
    simp
    -- ⊢ (bif decide (List.head? (trPosNum (PosNum.succ (PosNum.bit1 m)) ++ Γ'.cons : …
    rfl
    -- 🎉 no goals
  · obtain ⟨a, l, e, h⟩ : ∃ a l, (trPosNum m = a::l) ∧ natEnd a = false := by
      cases m <;> refine' ⟨_, _, rfl, rfl⟩
    refine' ⟨Γ'.bit0 :: l₁, _, some a, rfl, TransGen.single _⟩
    -- ⊢ { l := some (unrev q₂), var := some a, stk := elim (trPosNum m ++ Γ'.cons :: …
    simp [trPosNum, PosNum.succ, e, h, show some Γ'.bit1 ≠ some Γ'.bit0 by decide,
      Option.iget, -natEnd]
    rfl
    -- 🎉 no goals
#align turing.partrec_to_TM2.pred_ok Turing.PartrecToTM2.pred_ok

theorem trNormal_respects (c k v s) :
    ∃ b₂,
      TrCfg (stepNormal c k v) b₂ ∧
        Reaches₁ (TM2.step tr)
          ⟨some (trNormal c (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩ b₂ := by
  induction c generalizing k v s
  case zero' => refine' ⟨_, ⟨s, rfl⟩, TransGen.single _⟩; simp
  -- 🎉 no goals
  case succ => refine' ⟨_, ⟨none, rfl⟩, head_main_ok.trans succ_ok⟩
  -- 🎉 no goals
  case tail =>
    let o : Option Γ' := List.casesOn v none fun _ _ => some Γ'.cons
    refine' ⟨_, ⟨o, rfl⟩, _⟩; convert clear_ok _ using 2; simp; rfl; swap
    refine' splitAtPred_eq _ _ (trNat v.headI) _ _ (trNat_natEnd _) _
    cases v <;> simp
  case
    cons f fs IHf _ =>
    obtain ⟨c, h₁, h₂⟩ := IHf (Cont.cons₁ fs v k) v none
    refine' ⟨c, h₁, TransGen.head rfl <| (move_ok (by decide) (splitAtPred_false _)).trans _⟩
    simp [stepNormal]
    refine' (copy_ok _ none [] (trList v).reverse _ _).trans _
    convert h₂ using 2
    simp [List.reverseAux_eq, trContStack]
  case comp f _ _ IHg => exact IHg (Cont.comp f k) v s
  -- ⊢ ∃ b₂, TrCfg (stepNormal (Code.case a✝¹ a✝) k v) b₂ ∧ Reaches₁ (TM2.step tr)  …
  -- 🎉 no goals
  case case f g IHf IHg =>
    rw [stepNormal]
    simp only
    obtain ⟨s', h⟩ := pred_ok _ _ s v _ _
    revert h; cases' v.headI with n <;> intro h
    · obtain ⟨c, h₁, h₂⟩ := IHf k _ s'
      exact ⟨_, h₁, h.trans h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := IHg k _ s'
      exact ⟨_, h₁, h.trans h₂⟩
  case fix f IH => apply IH
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.partrec_to_TM2.tr_normal_respects Turing.PartrecToTM2.trNormal_respects

theorem tr_ret_respects (k v s) : ∃ b₂,
    TrCfg (stepRet k v) b₂ ∧
      Reaches₁ (TM2.step tr)
        ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩ b₂ := by
  induction k generalizing v s
  case halt => exact ⟨_, rfl, TransGen.single rfl⟩
  -- 🎉 no goals
  case
    cons₁ fs as k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects fs (Cont.cons₂ v k) as none
    refine' ⟨s', h₁, TransGen.head rfl _⟩; simp
    refine' (move₂_ok (by decide) _ (splitAtPred_false _)).trans _; · rfl
    simp
    refine' (move₂_ok (by decide) _ _).trans _; pick_goal 4; · rfl
    pick_goal 4;
    · exact
        splitAtPred_eq _ _ _ (some Γ'.consₗ) _
          (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, rfl⟩
    refine' (move₂_ok (by decide) _ (splitAtPred_false _)).trans _; · rfl
    simp
    exact h₂
  case cons₂ ns k IH =>
    obtain ⟨c, h₁, h₂⟩ := IH (ns.headI :: v) none
    exact ⟨c, h₁, TransGen.head rfl <| head_stack_ok.trans h₂⟩
  case comp f k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects f k v s
    exact ⟨_, h₁, TransGen.head rfl h₂⟩
  case fix f k IH =>
    rw [stepRet]
    have :
      if v.headI = 0 then natEnd (trList v).head?.iget = true ∧ (trList v).tail = trList v.tail
      else
        natEnd (trList v).head?.iget = false ∧
          (trList v).tail = (trNat v.headI).tail ++ Γ'.cons :: trList v.tail := by
      cases' v with n
      · exact ⟨rfl, rfl⟩
      cases' n with n
      · simp
      rw [trList, List.headI, trNat, Nat.cast_succ, Num.add_one, Num.succ, List.tail]
      cases (n : Num).succ' <;> exact ⟨rfl, rfl⟩
    by_cases v.headI = 0 <;> simp only [h, ite_true, ite_false] at this ⊢
    · obtain ⟨c, h₁, h₂⟩ := IH v.tail (trList v).head?
      refine' ⟨c, h₁, TransGen.head rfl _⟩
      simp [trCont, trContStack, this, -TM2.step, -natEnd]
      exact h₂
    · obtain ⟨s', h₁, h₂⟩ := trNormal_respects f (Cont.fix f k) v.tail (some Γ'.cons)
      refine' ⟨_, h₁, TransGen.head rfl <| TransGen.trans _ h₂⟩
      simp [trCont, this.1, -TM2.step, -natEnd]
      convert clear_ok (splitAtPred_eq _ _ (trNat v.headI).tail (some Γ'.cons) _ _ _) using 2
      · simp
        convert rfl
      · exact fun x h => trNat_natEnd _ _ (List.tail_subset _ h)
      · exact ⟨rfl, this.2⟩
#align turing.partrec_to_TM2.tr_ret_respects Turing.PartrecToTM2.tr_ret_respects

theorem tr_respects : Respects step (TM2.step tr) TrCfg
  | Cfg.ret _ _, _, ⟨_, rfl⟩ => tr_ret_respects _ _ _
  | Cfg.halt _, _, rfl => rfl
#align turing.partrec_to_TM2.tr_respects Turing.PartrecToTM2.tr_respects

/-- The initial state, evaluating function `c` on input `v`. -/
def init (c : Code) (v : List ℕ) : Cfg' :=
  ⟨some (trNormal c Cont'.halt), none, K'.elim (trList v) [] [] []⟩
#align turing.partrec_to_TM2.init Turing.PartrecToTM2.init

theorem tr_init (c v) :
    ∃ b, TrCfg (stepNormal c Cont.halt v) b ∧ Reaches₁ (TM2.step tr) (init c v) b :=
  trNormal_respects _ _ _ _
#align turing.partrec_to_TM2.tr_init Turing.PartrecToTM2.tr_init

theorem tr_eval (c v) : eval (TM2.step tr) (init c v) = halt <$> Code.eval c v := by
  obtain ⟨i, h₁, h₂⟩ := tr_init c v
  -- ⊢ eval (TM2.step tr) (init c v) = halt <$> Code.eval c v
  refine' Part.ext fun x => _
  -- ⊢ x ∈ eval (TM2.step tr) (init c v) ↔ x ∈ halt <$> Code.eval c v
  rw [reaches_eval h₂.to_reflTransGen]; simp [-TM2.step]
  -- ⊢ x ∈ eval (fun a => TM2.step tr a) i ↔ x ∈ halt <$> Code.eval c v
                                        -- ⊢ x ∈ eval (fun a => TM2.step tr a) i ↔ ∃ a, a ∈ Code.eval c v ∧ halt a = x
  refine' ⟨fun h => _, _⟩
  -- ⊢ ∃ a, a ∈ Code.eval c v ∧ halt a = x
  · obtain ⟨c, hc₁, hc₂⟩ := tr_eval_rev tr_respects h₁ h
    -- ⊢ ∃ a, a ∈ Code.eval c✝ v ∧ halt a = x
    simp [stepNormal_eval] at hc₂
    -- ⊢ ∃ a, a ∈ Code.eval c✝ v ∧ halt a = x
    obtain ⟨v', hv, rfl⟩ := hc₂
    -- ⊢ ∃ a, a ∈ Code.eval c v ∧ halt a = x
    exact ⟨_, hv, hc₁.symm⟩
    -- 🎉 no goals
  · rintro ⟨v', hv, rfl⟩
    -- ⊢ halt v' ∈ eval (fun a => TM2.step tr a) i
    have := Turing.tr_eval (b₁ := Cfg.halt v') tr_respects h₁
    -- ⊢ halt v' ∈ eval (fun a => TM2.step tr a) i
    simp [stepNormal_eval, -TM2.step] at this
    -- ⊢ halt v' ∈ eval (fun a => TM2.step tr a) i
    obtain ⟨_, ⟨⟩, h⟩ := this hv
    -- ⊢ halt v' ∈ eval (fun a => TM2.step tr a) i
    exact h
    -- 🎉 no goals
#align turing.partrec_to_TM2.tr_eval Turing.PartrecToTM2.tr_eval

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
#align turing.partrec_to_TM2.tr_stmts₁ Turing.PartrecToTM2.trStmts₁

theorem trStmts₁_trans {q q'} : q' ∈ trStmts₁ q → trStmts₁ q' ⊆ trStmts₁ q := by
  induction' q with _ _ _ q q_ih _ _ q q_ih q q_ih _ _ q q_ih q q_ih q q_ih q₁ q₂ q₁_ih q₂_ih _ <;>
    simp (config := { contextual := true }) only [trStmts₁, Finset.mem_insert, Finset.mem_union,
      or_imp, Finset.mem_singleton, Finset.Subset.refl, imp_true_iff, true_and_iff]
  iterate 4 exact fun h => Finset.Subset.trans (q_ih h) (Finset.subset_insert _ _)
  · simp
    -- ⊢ ∀ (x : Option Γ'), q' ∈ trStmts₁ (q x) → trStmts₁ q' ⊆ insert (Λ'.read q) (F …
    intro s h x h'
    -- ⊢ x ∈ insert (Λ'.read q) (Finset.biUnion Finset.univ fun s => trStmts₁ (q s))
    simp
    -- ⊢ x = Λ'.read q ∨ ∃ a, x ∈ trStmts₁ (q a)
    exact Or.inr ⟨_, q_ih s h h'⟩
    -- 🎉 no goals
  · constructor
    -- ⊢ q' = unrev q → insert (Λ'.move (fun x => false) rev main q) (trStmts₁ q) ⊆ i …
    · rintro rfl
      -- ⊢ insert (Λ'.move (fun x => false) rev main q) (trStmts₁ q) ⊆ insert (Λ'.succ  …
      apply Finset.subset_insert
      -- 🎉 no goals
    · intro h x h'
      -- ⊢ x ∈ insert (Λ'.succ q) (insert (unrev q) (trStmts₁ q))
      simp
      -- ⊢ x = Λ'.succ q ∨ x = unrev q ∨ x ∈ trStmts₁ q
      exact Or.inr (Or.inr <| q_ih h h')
      -- 🎉 no goals
  · refine' ⟨fun h x h' => _, fun _ x h' => _, fun h x h' => _⟩ <;> simp
                                                                    -- ⊢ x = Λ'.pred q₁ q₂ ∨ x = unrev q₂ ∨ x ∈ trStmts₁ q₁ ∨ x ∈ trStmts₁ q₂
                                                                    -- ⊢ x = Λ'.pred q₁ q₂ ∨ x = unrev q₂ ∨ x ∈ trStmts₁ q₁ ∨ x ∈ trStmts₁ q₂
                                                                    -- ⊢ x = Λ'.pred q₁ q₂ ∨ x = unrev q₂ ∨ x ∈ trStmts₁ q₁ ∨ x ∈ trStmts₁ q₂
    · exact Or.inr (Or.inr <| Or.inl <| q₁_ih h h')
      -- 🎉 no goals
    · cases' Finset.mem_insert.1 h' with h' h' <;> simp [h', unrev]
      -- ⊢ x = Λ'.pred q₁ q₂ ∨ x = unrev q₂ ∨ x ∈ trStmts₁ q₁ ∨ x ∈ trStmts₁ q₂
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
    · exact Or.inr (Or.inr <| Or.inr <| q₂_ih h h')
      -- 🎉 no goals
#align turing.partrec_to_TM2.tr_stmts₁_trans Turing.PartrecToTM2.trStmts₁_trans

theorem trStmts₁_self (q) : q ∈ trStmts₁ q := by
  induction q <;> · first |apply Finset.mem_singleton_self|apply Finset.mem_insert_self
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
                    -- 🎉 no goals
#align turing.partrec_to_TM2.tr_stmts₁_self Turing.PartrecToTM2.trStmts₁_self

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
#align turing.partrec_to_TM2.code_supp' Turing.PartrecToTM2.codeSupp'

@[simp]
theorem codeSupp'_self (c k) : trStmts₁ (trNormal c k) ⊆ codeSupp' c k := by
  cases c <;> first |rfl|exact Finset.subset_union_left _ _
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
              -- 🎉 no goals
#align turing.partrec_to_TM2.code_supp'_self Turing.PartrecToTM2.codeSupp'_self

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
#align turing.partrec_to_TM2.cont_supp Turing.PartrecToTM2.contSupp

/-- The (finite!) set of machine states visited during the course of evaluation of `c` in
continuation `k`. This is actually closed under forward simulation (see `tr_supports`), and the
existence of this set means that the machine constructed in this section is in fact a proper
Turing machine, with a finite set of states. -/
def codeSupp (c : Code) (k : Cont') : Finset Λ' :=
  codeSupp' c k ∪ contSupp k
#align turing.partrec_to_TM2.code_supp Turing.PartrecToTM2.codeSupp

@[simp]
theorem codeSupp_self (c k) : trStmts₁ (trNormal c k) ⊆ codeSupp c k :=
  Finset.Subset.trans (codeSupp'_self _ _) (Finset.subset_union_left _ _)
#align turing.partrec_to_TM2.code_supp_self Turing.PartrecToTM2.codeSupp_self

@[simp]
theorem codeSupp_zero (k) : codeSupp Code.zero' k = trStmts₁ (trNormal Code.zero' k) ∪ contSupp k :=
  rfl
#align turing.partrec_to_TM2.code_supp_zero Turing.PartrecToTM2.codeSupp_zero

@[simp]
theorem codeSupp_succ (k) : codeSupp Code.succ k = trStmts₁ (trNormal Code.succ k) ∪ contSupp k :=
  rfl
#align turing.partrec_to_TM2.code_supp_succ Turing.PartrecToTM2.codeSupp_succ

@[simp]
theorem codeSupp_tail (k) : codeSupp Code.tail k = trStmts₁ (trNormal Code.tail k) ∪ contSupp k :=
  rfl
#align turing.partrec_to_TM2.code_supp_tail Turing.PartrecToTM2.codeSupp_tail

@[simp]
theorem codeSupp_cons (f fs k) :
    codeSupp (Code.cons f fs) k =
      trStmts₁ (trNormal (Code.cons f fs) k) ∪ codeSupp f (Cont'.cons₁ fs k) :=
  by simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]
     -- 🎉 no goals
#align turing.partrec_to_TM2.code_supp_cons Turing.PartrecToTM2.codeSupp_cons

@[simp]
theorem codeSupp_comp (f g k) :
    codeSupp (Code.comp f g) k =
      trStmts₁ (trNormal (Code.comp f g) k) ∪ codeSupp g (Cont'.comp f k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]
  -- ⊢ trStmts₁ (trNormal g (Cont'.comp f k)) ∪ (codeSupp' g (Cont'.comp f k) ∪ (tr …
  rw [← Finset.union_assoc _ _ (contSupp k),
    Finset.union_eq_right_iff_subset.2 (codeSupp'_self _ _)]
#align turing.partrec_to_TM2.code_supp_comp Turing.PartrecToTM2.codeSupp_comp

@[simp]
theorem codeSupp_case (f g k) :
    codeSupp (Code.case f g) k =
      trStmts₁ (trNormal (Code.case f g) k) ∪ (codeSupp f k ∪ codeSupp g k) :=
  by simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm]
     -- 🎉 no goals
#align turing.partrec_to_TM2.code_supp_case Turing.PartrecToTM2.codeSupp_case

@[simp]
theorem codeSupp_fix (f k) :
    codeSupp (Code.fix f) k = trStmts₁ (trNormal (Code.fix f) k) ∪ codeSupp f (Cont'.fix f k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm,
    Finset.union_left_idem]
#align turing.partrec_to_TM2.code_supp_fix Turing.PartrecToTM2.codeSupp_fix

@[simp]
theorem contSupp_cons₁ (fs k) :
    contSupp (Cont'.cons₁ fs k) =
      trStmts₁
          (move₂ (fun _ => false) main aux <|
            move₂ (fun s => s = Γ'.consₗ) stack main <|
              move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
        codeSupp fs (Cont'.cons₂ k) :=
  by simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]
     -- 🎉 no goals
#align turing.partrec_to_TM2.cont_supp_cons₁ Turing.PartrecToTM2.contSupp_cons₁

@[simp]
theorem contSupp_cons₂ (k) :
    contSupp (Cont'.cons₂ k) = trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k :=
  rfl
#align turing.partrec_to_TM2.cont_supp_cons₂ Turing.PartrecToTM2.contSupp_cons₂

@[simp]
theorem contSupp_comp (f k) : contSupp (Cont'.comp f k) = codeSupp f k :=
  rfl
#align turing.partrec_to_TM2.cont_supp_comp Turing.PartrecToTM2.contSupp_comp

theorem contSupp_fix (f k) : contSupp (Cont'.fix f k) = codeSupp f (Cont'.fix f k) := by
  simp (config := { contextual := true }) [codeSupp, codeSupp', contSupp, Finset.union_assoc,
    Finset.subset_iff]
#align turing.partrec_to_TM2.cont_supp_fix Turing.PartrecToTM2.contSupp_fix

@[simp]
theorem contSupp_halt : contSupp Cont'.halt = ∅ :=
  rfl
#align turing.partrec_to_TM2.cont_supp_halt Turing.PartrecToTM2.contSupp_halt

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
#align turing.partrec_to_TM2.Λ'.supports Turing.PartrecToTM2.Λ'.Supports

/-- A shorthand for the predicate that we are proving in the main theorems `trStmts₁_supports`,
`codeSupp'_supports`, `contSupp_supports`, `codeSupp_supports`. The set `S` is fixed throughout
the proof, and denotes the full set of states in the machine, while `K` is a subset that we are
currently proving a property about. The predicate asserts that every state in `K` is closed in `S`
under forward simulation, i.e. stepping forward through evaluation starting from any state in `K`
stays entirely within `S`. -/
def Supports (K S : Finset Λ') :=
  ∀ q ∈ K, TM2.SupportsStmt S (tr q)
#align turing.partrec_to_TM2.supports Turing.PartrecToTM2.Supports

theorem supports_insert {K S q} :
    Supports (insert q K) S ↔ TM2.SupportsStmt S (tr q) ∧ Supports K S := by simp [Supports]
                                                                             -- 🎉 no goals
#align turing.partrec_to_TM2.supports_insert Turing.PartrecToTM2.supports_insert

theorem supports_singleton {S q} : Supports {q} S ↔ TM2.SupportsStmt S (tr q) := by simp [Supports]
                                                                                    -- 🎉 no goals
#align turing.partrec_to_TM2.supports_singleton Turing.PartrecToTM2.supports_singleton

theorem supports_union {K₁ K₂ S} : Supports (K₁ ∪ K₂) S ↔ Supports K₁ S ∧ Supports K₂ S := by
  simp [Supports, or_imp, forall_and]
  -- 🎉 no goals
#align turing.partrec_to_TM2.supports_union Turing.PartrecToTM2.supports_union

theorem supports_biUnion {K : Option Γ' → Finset Λ'} {S} :
    Supports (Finset.univ.biUnion K) S ↔ ∀ a, Supports (K a) S := by
  simp [Supports]; apply forall_swap
  -- ⊢ (∀ (q : Λ') (x : Option Γ'), q ∈ K x → TM2.SupportsStmt S (tr q)) ↔ ∀ (a : O …
                   -- 🎉 no goals
#align turing.partrec_to_TM2.supports_bUnion Turing.PartrecToTM2.supports_biUnion

theorem head_supports {S k q} (H : (q : Λ').Supports S) : (head k q).Supports S := fun _ => by
  dsimp only; split_ifs <;> exact H
  -- ⊢ Λ'.Supports S (ite (x✝ = some Γ'.consₗ) id (Λ'.clear (fun x => decide (x = Γ …
              -- ⊢ Λ'.Supports S (id (unrev q))
                            -- 🎉 no goals
                            -- 🎉 no goals
#align turing.partrec_to_TM2.head_supports Turing.PartrecToTM2.head_supports

theorem ret_supports {S k} (H₁ : contSupp k ⊆ S) : TM2.SupportsStmt S (tr (Λ'.ret k)) := by
  have W := fun {q} => trStmts₁_self q
  -- ⊢ TM2.SupportsStmt S (tr (Λ'.ret k))
  cases k
  case halt => trivial
  -- 🎉 no goals
  case cons₁ => rw [contSupp_cons₁, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  -- 🎉 no goals
  case cons₂ => rw [contSupp_cons₂, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  -- ⊢ TM2.SupportsStmt S (tr (Λ'.ret (Cont'.comp a✝¹ a✝)))
  -- 🎉 no goals
  case comp => rw [contSupp_comp] at H₁; exact fun _ => H₁ (codeSupp_self _ _ W)
  -- ⊢ TM2.SupportsStmt S (tr (Λ'.ret (Cont'.fix a✝¹ a✝)))
  -- 🎉 no goals
  case fix =>
    rw [contSupp_fix] at H₁
    have L := @Finset.mem_union_left; have R := @Finset.mem_union_right
    intro s; dsimp only; cases natEnd s.iget
    · refine' H₁ (R _ <| L _ <| R _ <| R _ <| L _ W)
    · exact H₁ (R _ <| L _ <| R _ <| R _ <| R _ <| Finset.mem_singleton_self _)
#align turing.partrec_to_TM2.ret_supports Turing.PartrecToTM2.ret_supports

theorem trStmts₁_supports {S q} (H₁ : (q : Λ').Supports S) (HS₁ : trStmts₁ q ⊆ S) :
    Supports (trStmts₁ q) S := by
  have W := fun {q} => trStmts₁_self q
  -- ⊢ Supports (trStmts₁ q) S
  induction' q with _ _ _ q q_ih _ _ q q_ih q q_ih _ _ q q_ih q q_ih q q_ih q₁ q₂ q₁_ih q₂_ih _ <;>
    simp [trStmts₁, -Finset.singleton_subset_iff] at HS₁ ⊢
    -- ⊢ Supports (insert (Λ'.move p✝ k₁✝ k₂✝ q) (trStmts₁ q)) S
    -- ⊢ Supports (insert (Λ'.clear p✝ k✝ q) (trStmts₁ q)) S
    -- ⊢ Supports (insert (Λ'.copy q) (trStmts₁ q)) S
    -- ⊢ Supports (insert (Λ'.push k✝ s✝ q) (trStmts₁ q)) S
    -- ⊢ Supports (insert (Λ'.read q) (Finset.biUnion Finset.univ fun s => trStmts₁ ( …
    -- ⊢ Supports (insert (Λ'.succ q) (insert (unrev q) (trStmts₁ q))) S
    -- ⊢ Supports (insert (Λ'.pred q₁ q₂) (insert (unrev q₂) (trStmts₁ q₁ ∪ trStmts₁  …
    -- ⊢ Supports {Λ'.ret k✝} S
  any_goals
    cases' Finset.insert_subset_iff.1 HS₁ with h₁ h₂
    first | have h₃ := h₂ W | try simp [Finset.subset_iff] at h₂
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₁⟩, q_ih H₁ h₂⟩ -- move
    -- 🎉 no goals
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₁⟩, q_ih H₁ h₂⟩ -- clear
    -- 🎉 no goals
  · exact supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₃⟩, q_ih H₁ h₂⟩ -- copy
    -- 🎉 no goals
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₃⟩, q_ih H₁ h₂⟩ -- push
    -- 🎉 no goals
  · refine' supports_insert.2 ⟨fun _ => h₂ _ W, _⟩ -- read
    -- ⊢ Supports (Finset.biUnion Finset.univ fun s => trStmts₁ (q s)) S
    exact supports_biUnion.2 fun _ => q_ih _ (H₁ _) fun _ h => h₂ _ h
    -- 🎉 no goals
  · refine' supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₂.1, fun _ => h₂.1⟩, _⟩ -- succ
    -- ⊢ Supports (insert (unrev q) (trStmts₁ q)) S
    exact supports_insert.2 ⟨⟨fun _ => h₂.2 _ W, fun _ => h₂.1⟩, q_ih H₁ h₂.2⟩
    -- 🎉 no goals
  · refine' -- pred
      supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₂.2 _ (Or.inl W), fun _ => h₂.1, fun _ => h₂.1⟩, _⟩
    refine' supports_insert.2 ⟨⟨fun _ => h₂.2 _ (Or.inr W), fun _ => h₂.1⟩, _⟩
    -- ⊢ Supports (trStmts₁ q₁ ∪ trStmts₁ q₂) S
    refine' supports_union.2 ⟨_, _⟩
    -- ⊢ Supports (trStmts₁ q₁) S
    · exact q₁_ih H₁.1 fun _ h => h₂.2 _ (Or.inl h)
      -- 🎉 no goals
    · exact q₂_ih H₁.2 fun _ h => h₂.2 _ (Or.inr h)
      -- 🎉 no goals
  · exact supports_singleton.2 (ret_supports H₁)  -- ret
    -- 🎉 no goals
#align turing.partrec_to_TM2.tr_stmts₁_supports Turing.PartrecToTM2.trStmts₁_supports

theorem trStmts₁_supports' {S q K} (H₁ : (q : Λ').Supports S) (H₂ : trStmts₁ q ∪ K ⊆ S)
    (H₃ : K ⊆ S → Supports K S) : Supports (trStmts₁ q ∪ K) S := by
  simp [Finset.union_subset_iff] at H₂
  -- ⊢ Supports (trStmts₁ q ∪ K) S
  exact supports_union.2 ⟨trStmts₁_supports H₁ H₂.1, H₃ H₂.2⟩
  -- 🎉 no goals
#align turing.partrec_to_TM2.tr_stmts₁_supports' Turing.PartrecToTM2.trStmts₁_supports'

theorem trNormal_supports {S c k} (Hk : codeSupp c k ⊆ S) : (trNormal c k).Supports S := by
  induction c generalizing k <;> simp [Λ'.Supports, head]
                                 -- ⊢ contSupp k ⊆ S
                                 -- ⊢ ∀ (s : Option Γ'), Λ'.Supports S (ite (s = some Γ'.consₗ) id (Λ'.clear (fun  …
                                 -- ⊢ contSupp k ⊆ S
                                 -- ⊢ Λ'.Supports S (trNormal a✝¹ (Cont'.cons₁ a✝ k))
                                 -- ⊢ Λ'.Supports S (trNormal a✝ (Cont'.comp a✝¹ k))
                                 -- ⊢ Λ'.Supports S (trNormal a✝¹ k) ∧ Λ'.Supports S (trNormal a✝ k)
                                 -- ⊢ Λ'.Supports S (trNormal a✝ (Cont'.fix a✝ k))
  case zero' => exact Finset.union_subset_right Hk
  -- 🎉 no goals
  case succ => intro; split_ifs <;> exact Finset.union_subset_right Hk
  -- 🎉 no goals
  case tail => exact Finset.union_subset_right Hk
  -- 🎉 no goals
  case cons f fs IHf _ =>
    apply IHf
    rw [codeSupp_cons] at Hk
    exact Finset.union_subset_right Hk
  case comp f g _ IHg => apply IHg; rw [codeSupp_comp] at Hk; exact Finset.union_subset_right Hk
  -- ⊢ Λ'.Supports S (trNormal a✝¹ k) ∧ Λ'.Supports S (trNormal a✝ k)
  -- 🎉 no goals
  case
    case f g IHf IHg =>
    simp only [codeSupp_case, Finset.union_subset_iff] at Hk
    exact ⟨IHf Hk.2.1, IHg Hk.2.2⟩
  case fix f IHf => apply IHf; rw [codeSupp_fix] at Hk; exact Finset.union_subset_right Hk
  -- 🎉 no goals
  -- 🎉 no goals
#align turing.partrec_to_TM2.tr_normal_supports Turing.PartrecToTM2.trNormal_supports

theorem codeSupp'_supports {S c k} (H : codeSupp c k ⊆ S) : Supports (codeSupp' c k) S := by
  induction c generalizing k
  iterate 3
    exact trStmts₁_supports (trNormal_supports H) (Finset.Subset.trans (codeSupp_self _ _) H)
  case cons f fs IHf IHfs =>
    have H' := H; simp only [codeSupp_cons, Finset.union_subset_iff] at H'
    refine' trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => _
    refine' supports_union.2 ⟨IHf H'.2, _⟩
    refine' trStmts₁_supports' (trNormal_supports _) (Finset.union_subset_right h) fun h => _
    · simp only [codeSupp, Finset.union_subset_iff, contSupp] at h H ⊢
      exact ⟨h.2.2.1, h.2.2.2, H.2⟩
    refine' supports_union.2 ⟨IHfs _, _⟩
    · rw [codeSupp, contSupp_cons₁] at H'
      exact Finset.union_subset_right (Finset.union_subset_right H'.2)
    exact
      trStmts₁_supports (head_supports <| Finset.union_subset_right H)
        (Finset.union_subset_right h)
  case comp f g IHf IHg =>
    have H' := H; rw [codeSupp_comp] at H'; have H' := Finset.union_subset_right H'
    refine' trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => _
    refine' supports_union.2 ⟨IHg H', _⟩
    refine' trStmts₁_supports' (trNormal_supports _) (Finset.union_subset_right h) fun _ => _
    · simp only [codeSupp', codeSupp, Finset.union_subset_iff, contSupp] at h H ⊢
      exact ⟨h.2.2, H.2⟩
    exact IHf (Finset.union_subset_right H')
  case case f g IHf IHg =>
    have H' := H; simp only [codeSupp_case, Finset.union_subset_iff] at H'
    refine' trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun _ => _
    exact supports_union.2 ⟨IHf H'.2.1, IHg H'.2.2⟩
  case fix f IHf =>
    have H' := H; simp only [codeSupp_fix, Finset.union_subset_iff] at H'
    refine' trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => _
    refine' supports_union.2 ⟨IHf H'.2, _⟩
    refine' trStmts₁_supports' (trNormal_supports _) (Finset.union_subset_right h) fun _ => _
    · simp only [codeSupp', codeSupp, Finset.union_subset_iff, contSupp, trStmts₁,
        Finset.insert_subset_iff] at h H ⊢
      exact ⟨h.1, ⟨H.1.1, h⟩, H.2⟩
    exact supports_singleton.2 (ret_supports <| Finset.union_subset_right H)
#align turing.partrec_to_TM2.code_supp'_supports Turing.PartrecToTM2.codeSupp'_supports

theorem contSupp_supports {S k} (H : contSupp k ⊆ S) : Supports (contSupp k) S := by
  induction k
  · simp [contSupp_halt, Supports]
    -- 🎉 no goals
  case cons₁ f k IH =>
    have H₁ := H; rw [contSupp_cons₁] at H₁; have H₂ := Finset.union_subset_right H₁
    refine' trStmts₁_supports' (trNormal_supports H₂) H₁ fun h => _
    refine' supports_union.2 ⟨codeSupp'_supports H₂, _⟩
    simp only [codeSupp, contSupp_cons₂, Finset.union_subset_iff] at H₂
    exact trStmts₁_supports' (head_supports H₂.2.2) (Finset.union_subset_right h) IH
  case cons₂ k IH =>
    have H' := H; rw [contSupp_cons₂] at H'
    exact trStmts₁_supports' (head_supports <| Finset.union_subset_right H') H' IH
  case comp f k IH =>
    have H' := H; rw [contSupp_comp] at H'; have H₂ := Finset.union_subset_right H'
    exact supports_union.2 ⟨codeSupp'_supports H', IH H₂⟩
  case fix f k IH =>
    rw [contSupp] at H
    exact supports_union.2 ⟨codeSupp'_supports H, IH (Finset.union_subset_right H)⟩
#align turing.partrec_to_TM2.cont_supp_supports Turing.PartrecToTM2.contSupp_supports

theorem codeSupp_supports {S c k} (H : codeSupp c k ⊆ S) : Supports (codeSupp c k) S :=
  supports_union.2 ⟨codeSupp'_supports H, contSupp_supports (Finset.union_subset_right H)⟩
#align turing.partrec_to_TM2.code_supp_supports Turing.PartrecToTM2.codeSupp_supports

/-- The set `codeSupp c k` is a finite set that witnesses the effective finiteness of the `tr`
Turing machine. Starting from the initial state `trNormal c k`, forward simulation uses only
states in `codeSupp c k`, so this is a finite state machine. Even though the underlying type of
state labels `Λ'` is infinite, for a given partial recursive function `c` and continuation `k`,
only finitely many states are accessed, corresponding roughly to subterms of `c`. -/
theorem tr_supports (c k) : @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (codeSupp c k) :=
  ⟨codeSupp_self _ _ (trStmts₁_self _), fun _ => codeSupp_supports (Finset.Subset.refl _) _⟩
#align turing.partrec_to_TM2.tr_supports Turing.PartrecToTM2.tr_supports

end

end PartrecToTM2

end Turing
