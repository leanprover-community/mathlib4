/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Degree.Lemmas
import Mathlib.Data.Polynomial.EraseLead

/-!

# `compute_degree` a tactic for computing degrees of polynomials

This file defines the tactic `compute_degree`.

Using `compute_degree` when the goal is of one of the five forms
*  `natDegree f ≤ d`,
*  `degree f ≤ d`,
*  `natDegree f = d`,
*  `degree f = d`,
*  `coeff f n = r`,
tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Currently, the tactic does not deal correctly with some edge cases.  For instance,
  ```lean
  example [Semiring R] : natDegree (C 0 : R[X]) = 0 := by
    compute_degree
  --  ⊢ 0 ≠ 0
  ```
  Still, it may not be worth to provide special support for `natDegree f = 0`.
* Make sure that numerals in coefficients are treated correctly.
* Make sure that `compute_degree` works with goals of the form `degree f ≤ ↑d`, with an
  explicit coercion from `ℕ` on the RHS.
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree`, `natDegree` and `coeff` are equally supported.

##  Implementation details

Assume that `f : R[X]` is a polynomial with coefficients in a semiring `R` and
`d` is either in `ℕ` or in `WithBot ℕ`.
If the goal has the form `natDegree f = d`, then we convert it to three separate goals:
* `natDegree f ≤ d`;
* `coeff f d = r`;
* `r ≠ 0`.

Similarly, an initial goal of the form `degree f = d` gives rise to goals of the form
* `degree f ≤ d`;
* `coeff f d = r`;
* `r ≠ 0`.

Next, we apply successively lemmas whose side-goals all have the shape
* `natDegree f ≤ d`;
* `degree f ≤ d`;
* `coeff f d = r`;

plus possibly "numerical" identities and choices of elements in `ℕ`, `WithBot ℕ`, and `R`.

Recursing into `f`, we break apart additions, multiplications, powers, subtractions,...
The leaves of the process are
* numerals, `C a`, `X` and `monomial a n`, to which we assign degree `0`, `1` and `a` respectively;
* `fvar`s `f`, to which we tautologically assign degree `natDegree f`.
-/

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section recursion_lemmas
/-!
###  Simple lemmas about `natDegree`

The lemmas in this section all have the form `natDegree <some form of cast> ≤ 0`.
Their proofs are weakenings of the stronger lemmas `natDegree <same> = 0`.
These are the lemmas called by `compute_degree` on (almost) all the leaves of its recursion.
-/

variable {R : Type _}

section semiring
variable [Semiring R]

section PRed_lemmas

/- `Data.Polynomial.Basic` -/
theorem coeff_nat_cast_ite {n a : ℕ} : (Nat.cast a : R[X]).coeff n = ite (n = 0) a 0 := by
  simp only [← C_eq_nat_cast, coeff_C, Nat.cast_ite, Nat.cast_zero]

/- `Data.Polynomial.EraseLead` -/
theorem coeff_mul_add_of_le_natDegree_of_eq {df dg : ℕ} {f g : R[X]}
    (hdf : natDegree f ≤ df) (hdg : natDegree g ≤ dg) :
    (f * g).coeff (df + dg) = f.coeff df * g.coeff dg := by
  revert hdg g
  apply f.induction_with_natDegree_le (P_0 := by simp)
  · intros n r _r0 hn g hdg
    rw [mul_assoc, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow,
      if_pos (le_add_right hn)]
    split_ifs with H
    · simp [H]
    · rw [mul_zero, zero_mul]
      apply mul_eq_zero_of_right
      apply coeff_eq_zero_of_natDegree_lt
      apply hdg.trans_lt
      rw [add_comm, Nat.add_sub_assoc hn]
      apply Nat.lt_add_of_pos_right
      apply Nat.sub_pos_of_lt
      exact Ne.lt_of_le' H hn
  · intros f g _fg _gle hf hg h hle
    rw [add_mul, coeff_add, coeff_add, add_mul]
    congr <;> solve_by_elim
  · assumption

/- `Mathlib.Data.Polynomial.Degree.Lemmas` -/
theorem coeff_pow_of_natDegree_le_of_eq_ite [Semiring R] {m n o : ℕ} {p : R[X]}
    (pn : natDegree p ≤ n) (mno : m * n ≤ o) :
    coeff (p ^ m) o = if o = m * n then (coeff p n) ^ m else 0 := by
  split_ifs with h
  · subst h
    rw [mul_comm]
    apply coeff_pow_of_natDegree_le pn
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne mno ?_)
    · exact natDegree_pow_le_of_le m pn
    · exact Iff.mp ne_comm h

end PRed_lemmas

theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le

theorem natDegree_nat_cast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le

theorem coeff_add_of_eq {n : ℕ} {a b : R} {f g : R[X]}
    (h_add_left : f.coeff n = a) (h_add_right : g.coeff n = b) :
    (f + g).coeff n = a + b := by subst ‹_› ‹_›; apply coeff_add

theorem coeff_mul_add_of_le_natDegree_of_eq_ite {d df dg : ℕ} {a b : R} {f g : R[X]}
    (h_mul_left : natDegree f ≤ df) (h_mul_right : natDegree g ≤ dg)
    (h_mul_left : f.coeff df = a) (h_mul_right : g.coeff dg = b) (ddf : df + dg ≤ d) :
    (f * g).coeff d = if d = df + dg then a * b else 0 := by
  split_ifs with h
  · subst h_mul_left h_mul_right h
    exact coeff_mul_add_of_le_natDegree_of_eq ‹_› ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le ‹_› ‹_›
    · exact ne_comm.mp h

theorem coeff_pow_of_natDegree_le_of_eq_ite' [Semiring R] {m n o : ℕ} {a : R} {p : R[X]}
    (h_pow : natDegree p ≤ n) (h_exp : m * n ≤ o) (h_pow_bas : coeff p n = a) :
    coeff (p ^ m) o = if o = m * n then a ^ m else 0 := by
  split_ifs with h
  · subst h h_pow_bas
    rw [mul_comm]
    exact coeff_pow_of_natDegree_le ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ‹_› ?_)
    · exact natDegree_pow_le_of_le m ‹_›
    · exact Iff.mp ne_comm h

section congr_lemmas

/--  The following two lemmas should be viewed as a hand-made "congr"-lemmas.
They achieve the following goals.
* They introduce *two* fresh metavariables replacing the given one `deg`,
  one for the `natDegree ≤` computation and one for the `coeff =` computation.
  This helps `compute_degree`, since it does not "pre-estimate" the degree,
  but it "picks it up along the way".
* They split checking the inequality `coeff p n ≠ 0` into the task of
  finding a value `c` for the `coeff` and then
  proving that this value is non-zero by `coeff_ne_zero`.
-/
theorem natDegree_eq_of_le_of_coeff_ne_zero' {deg m o : ℕ} {c : R} {p : R[X]}
    (h_natDeg_le : natDegree p ≤ m) (coeff_eq : coeff p o = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    natDegree p = deg := by
  subst coeff_eq deg_eq_deg coeff_eq_deg
  exact natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

theorem degree_eq_of_le_of_coeff_ne_zero' {deg : WithBot ℕ} {m o : ℕ} {c : R} {p : R[X]}
    (h_deg_le : degree p ≤ m) (coeff_eq : coeff p o = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    degree p = deg := by
  subst coeff_eq coeff_eq_deg
  rw [Nat.cast_inj] at deg_eq_deg
  subst ‹_›
  exact degree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

variable {m n : ℕ} {f : R[X]} {r : R} (h : coeff f m = r) (natDeg_eq_coeff : m = n)

theorem coeff_congr_lhs : coeff f n = r := natDeg_eq_coeff ▸ h
theorem coeff_congr {s : R} (rs : r = s) : coeff f n = s := natDeg_eq_coeff ▸ rs ▸ h

end congr_lemmas

end semiring

section ring
variable [Ring R]

theorem natDegree_int_cast_le (n : ℤ) : natDegree (n : R[X]) ≤ 0 := (natDegree_int_cast _).le

theorem coeff_sub_of_eq {n : ℕ} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg : g.coeff n = b) :
    (f - g).coeff n = a - b := by subst hf hg; apply coeff_sub

theorem coeff_int_cast_ite {n : ℕ} {a : ℤ} : (Int.cast a : R[X]).coeff n = ite (n = 0) a 0 := by
  simp only [← C_eq_int_cast, coeff_C, Int.cast_ite, Int.cast_zero]

end ring

end recursion_lemmas

section Tactic

open Lean Elab Tactic Meta Expr

/--  `Lean.Name.getTail name` takes `name : Name` as input.
If `name = .str _ tail`, then it returns `tail`.
For instance,
```lean
#eval Lean.Name.getTail `first.second.third  -- "third"
```
-/
def _root_.Lean.Name.getTail : Name → String
  | .str _ tail => tail
  | _ => ""

/--  `Lean.Name.getHead name` takes `name : Name` as input.
If `name = .str head _`, then it returns `head`.
For instance,
```lean
#eval Lean.Name.getHead `first.second.third  -- "first.second"
```
-/
def _root_.Lean.Name.getHead : Name → Name
  | .str head _ => head
  | _ => .anonymous

@[inline] def _root_.Lean.Expr.le? (p : Expr) : Option (Expr × Expr × Expr) := do
  let (type, _, lhs, rhs) := ← p.app4? ``LE.le
  return (type, lhs, rhs)

open ConstantInfo Command in
/-- `declNameInThm thm tag` takes two `Name`s as input.  It checks that the declaration called
`thm` exists and that one of its hypotheses is called `tag`.
Since `compute_degree` finds goals by referring to their tags, this check makes sure that
the tactic continues working and highlights potential problems.
-/
def declNameInThm (thm tag : Name) : CommandElabM Unit := do
  let tail :=  m!"\n\n  `{thm.getTail}`\n\nchange name?"
  match (← getEnv).find? thm with
    | none => throwError m!"Did lemma" ++ tail
    | some decl => do
      let stat := (toConstantVal decl).type
      let listBinderNames := stat.getForallBinderNames
      if (! tag ∈ listBinderNames) then
        throwError m!"Did the hypothesis\n\n  `{tag}`\n\nof lemma" ++ tail

/--  `CDtags` is the list containing the three tags that `compute_degree` uses to report errors
relating to the degree-computations. -/
private def CDtags : List String := ["deg_eq_deg", "coeff_eq_deg", "coeff_ne_zero"]

/-! Check that both theorems
`natDegree_eq_of_le_of_coeff_ne_zero'` and `degree_eq_of_le_of_coeff_ne_zero'` contain hypotheses
called `exp_deg_eq_deg` and `natDeg_eq_coeff`. -/
run_cmd
  for thm in [``natDegree_eq_of_le_of_coeff_ne_zero', ``degree_eq_of_le_of_coeff_ne_zero'] do
  for tag in CDtags do
    declNameInThm thm tag

/-- `twoHeadsArgs e` takes an `Expr`ession `e` as input and recurses into `e` to make sure
the `e` looks like `lhs ≤ rhs` or `lhs = rhs` and that `lhs` is one of
`natDegree f, degree f, coeff f n`.
It also returns
* the head symbol of `f` and
* the list of answers to the question of whether `rhs` and, if present, `n` are metavariables.

This is all the data needed to figure out whether `compute_degree` can make progress on `e`
and, if so, which lemma it should apply.

Sample outputs:
* `natDegree (f + g) ≤ d => (natDegree, LE.le, HAdd.hAdd, [d.isMVar])` (similarly for `=`);
* `degree (f * g) = d => (degree, Eq, HMul.hMul, [d.isMVar])` (similarly for `≤`);
* `coeff (1 : ℕ[X]) c = x => (coeff, Eq, one, [x.isMVar, c.isMVar])` (no `≤` option!).
-/
def twoHeadsArgs (e : Expr) : Name × Name × Name × List Bool :=
let (eq_or_le, lhs, rhs) := match e.getAppFnArgs with
  | (na@``Eq, #[_, lhs, rhs])       => (na, lhs, rhs)
  | (na@``LE.le, #[_, _, lhs, rhs]) => (na, lhs, rhs)
  | (na, _) => (na, default)
if eq_or_le ∉ [``Eq, ``LE.le] then (.anonymous, eq_or_le, lhs.getAppFnArgs.1, []) else
let (ndeg_or_deg_or_coeff, pol, and?) := match lhs.getAppFnArgs with
  | (na@``Polynomial.natDegree, #[_, _, pol]) => (na, pol, [rhs])
  | (na@``Polynomial.degree, #[_, _, pol])    => (na, pol, [rhs])
  | (na@``Polynomial.coeff, #[_, _, pol, c])  => (na, pol, [rhs, c])
  | (na@_, _) => (na, default)
if pol == default then (ndeg_or_deg_or_coeff, .anonymous, pol.getAppFnArgs.1, []) else
let head := match pol.numeral? with
  -- can I avoid the tri-splitting `n = 0`, `n = 1`, and generic `n`?
  | some 0 => `zero
  | some 1 => `one
  | some _ => `many
  | none => match pol.getAppFnArgs with
  --  unusual indentation to improve legibility of the following block of pairs of lemmas
  | (``FunLike.coe, #[_, _, _, _, polFun, _]) => match polFun.getAppFnArgs with
    | (na@``Polynomial.monomial, _) => na
    | (na@``Polynomial.C, _) => na
    | _ => `error
  | (na, _) => na
(ndeg_or_deg_or_coeff, eq_or_le, head, and?.map isMVar)

/--
`getCongrLemma (lhs_name, rel_name, Mvars?)` returns the name of a lemma that preprocesses
one of the five target
*  `natDegree f ≤ d`;
*  `natDegree f = d`.
*  `degree f ≤ d`;
*  `degree f = d`.
*  `coeff f n = r`.

The end goals are of the form
* `natDegree f ≤ ?_`, `degree f ≤ ?_`, `coeff f ?_ = ?_`, with fresh metavariables;
* `coeff f m ≠ s` with `m, s` not necessarily metavariables;
* several equalities/inequalities between expressions and assignments for metavariables.

`getCongrLemma` gets called at the very beginning of `compute_degree` and whenever an intermediate
goal does not have the right metavariables.
Note that the side-goals of the congruence lemma are neither of the form `natDegree f = d` nor
of the form `degree f = d`.

`getCongrLemma` admits an optional "debug" flag: `getCongrLemma data true` prints the name of
the congruence lemma that it returns.
-/
def getCongrLemma (twoH : Name × Name × List Bool) (debug : Bool := false) : Name :=
let nam := match twoH with
  | (_,           ``LE.le, [rhs]) => if rhs then ``id else ``le_trans
  | (``natDegree, ``Eq, [rhs])    => if rhs then ``id else ``natDegree_eq_of_le_of_coeff_ne_zero'
  | (``degree,    ``Eq, [rhs])    => if rhs then ``id else ``degree_eq_of_le_of_coeff_ne_zero'
  | (``coeff,     ``Eq, [rhs, c]) => match rhs, c with
    | false, false => ``coeff_congr
    | false, true  => ``Eq.trans
    | true, false  => ``coeff_congr_lhs
    | true, true   => ``id
  | _ => ``id
if debug then
  let natr := if nam.getTail == `trans then nam else nam.getTail
  dbg_trace f!"congr lemma: '{natr}'"
  nam
else
  nam

/--
`dispatchLemma twoH` takes its input `twoH` from the output of `twoHeadsArgs`.

Using the information contained in `twoH`, it decides which lemma is the most appropriate.

`dispatchLemma` is essentially the main dictionary for `compute_degree`.
-/
--  Internally, `dispatchLemma` produces 3 names: these are the lemmas that are appropriate
--  for goals of the form `natDegree f ≤ d`, `degree f ≤ d`, `coeff f n = a`, in this order.
def dispatchLemma (twoH : Name × Name × Name × List Bool) (debug : Bool := false) : Name :=
match twoH with
  | (.anonymous, _, _, _) => ``id -- `twoH` gave default value, so we do nothing
  | (_, .anonymous, _, _) => ``id -- `twoH` gave default value, so we do nothing
  | (na1, na2, head, bools) =>
    let msg := f!"\ndispatchLemma:\n  {head}"
    -- if there is some non-metavariable on the way, we "congr" it away
    if false ∈ bools then getCongrLemma (na1, na2, bools) debug
    else
    -- otherwise, we select either the first, second or third element of the triple in `nas` below
    let π : Name × Name × Name → Name := match na1, na2 with
      | ``natDegree, ``LE.le => Prod.fst
      | ``degree, ``LE.le => Prod.fst ∘ Prod.snd
      | _, _ => Prod.snd ∘ Prod.snd
    let nas := match head with
      | `zero => (``natDegree_zero_le, ``degree_zero_le, ``coeff_zero)
      | `one => (``natDegree_one_le, ``degree_one_le, ``coeff_one)
      | `many => (``natDegree_nat_cast_le, ``degree_nat_cast_le, ``coeff_nat_cast_ite)
      | ``HAdd.hAdd =>
        (``natDegree_add_le_of_le, ``degree_add_le_of_le, ``coeff_add_of_eq)
      | ``HSub.hSub =>
        (``natDegree_sub_le_of_le, ``degree_sub_le_of_le, ``coeff_sub_of_eq)
      | ``HMul.hMul =>
        (``natDegree_mul_le_of_le, ``degree_mul_le_of_le, ``coeff_mul_add_of_le_natDegree_of_eq_ite)
      | ``HPow.hPow =>
        (``natDegree_pow_le_of_le, ``degree_pow_le_of_le, ``coeff_pow_of_natDegree_le_of_eq_ite')
      | ``Neg.neg =>
        (``natDegree_neg_le_of_le, ``degree_neg_le_of_le, ``coeff_neg)
      | ``Polynomial.X =>
        (``natDegree_X_le, ``degree_X_le, ``coeff_X)
      | ``Nat.cast =>
        (``natDegree_nat_cast_le, ``degree_nat_cast_le, ``coeff_nat_cast_ite)
      | ``NatCast.natCast =>
        (``natDegree_nat_cast_le, ``degree_nat_cast_le, ``coeff_nat_cast_ite)
      | ``Int.cast =>
        (``natDegree_int_cast_le, ``degree_int_cast_le, ``coeff_int_cast_ite)
      | ``IntCast.intCast =>
        (``natDegree_int_cast_le, ``degree_int_cast_le, ``coeff_int_cast_ite)
      | ``Polynomial.monomial =>
        (``natDegree_monomial_le, ``degree_monomial_le, ``coeff_monomial)
      | ``Polynomial.C =>
        (``natDegree_C_le, ``degree_C_le, ``coeff_C)
      | `error => (.anonymous, .anonymous, .anonymous)
      | _ => (``le_rfl, ``le_rfl, ``rfl)
    if debug then dbg_trace f!"{(π nas).getTail}\n{msg}"; π nas else π nas

/-- `try_rfl mvs` takes as input a list of `MVarId`s, scans them partitioning them into two
lists: the goals containing some metavariables and the goal not containing any metavariable.

If a goal containing a metavariable has the form `?_ = x`, `x = ?_`, where `?_` is a metavariable
and `x` is an expression that does not involve metavariables, then it closes this goal using `rfl`,
effectively assigning the metavariable to `x`.

If a goal does not contain metavariables, it tries `rfl` on it.

It returns the corresponding list of `MVarId`s, first the ones that initially involved (`Expr`)
metavariables followed by the rest.
-/
def try_rfl (mvs : List MVarId) : MetaM (List MVarId) := do
  let (mv, nmv) := ← mvs.partitionM fun mv => return hasExprMVar (← mv.getDecl).type
  let nrfl := ← nmv.mapM fun g => g.applyConst ``rfl <|> return [g]
  let assignable := ← mv.mapM fun g => do
    let tgt := ← instantiateMVars (← g.getDecl).type
    match tgt.eq? with
      | some (_, lhs, rhs) =>
        if (isMVar rhs && (! hasExprMVar lhs)) ||
           (isMVar lhs && (! hasExprMVar rhs)) then
           g.applyConst ``rfl
        else pure [g]
      | none =>
        return [g]
  return (assignable.join ++ nrfl.join)

/--
`splitApply mvs static` takes two lists of `MVarId`s.  The first list, `mvs`,
corresponds to goals that are potentially within the scope of `compute_degree`:
namely, goals of the form
`natDegree f ≤ d`, `degree f ≤ d`, `natDegree f = d`, `degree f = d`, `coeff f n = r`.

`splitApply` determines which of these goals are actually within the scope, it applies the relevant
lemma and returns two lists: the left-over goals of all the applications, followed by the
concatenation of the previous `static` list, followed by the newly discovered goals outside of the
scope of `compute_degree`. -/
def splitApply (mvs static : List MVarId) : MetaM ((List MVarId) × (List MVarId)) := do
let (can_progress, curr_static) := ← mvs.partitionM fun mv => do
  return dispatchLemma (twoHeadsArgs (← mv.getType'')) != ``id
let progress := ← can_progress.mapM fun mv => do
  let lem := dispatchLemma <| twoHeadsArgs (← mv.getType'')
  mv.applyConst <| lem
return (progress.join, static ++ curr_static)

/--
`compute_degree` is a tactic to solve goals of the form `natDegree f ≤ d` or `degree f ≤ d`.

The tactic first replaces `natDegree f ≤ d` with `d' ≤ d`,
where `d'` is an internally computed guess for which the tactic proves the inequality
`natDegree f ≤ d'`.

Next, it applies `norm_num` to `d'`, in the hope of closing also the `d' ≤ d` goal.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on the whole inequality `d' ≤ d` and tries `assumption`.
-/
syntax (name := computeDegree) "compute_degree" "!"? "-debug"? : tactic

@[inherit_doc computeDegree]
macro "compute_degree!" "-debug"? : tactic => `(tactic| compute_degree ! -debug)
@[inherit_doc computeDegree]
macro "compute_degree!" : tactic => `(tactic| compute_degree !)

/-- `miscomputedDegree? deg false_goals` takes as input
*  an `Expr`ession `deg`, representing the degree of a polynomial
   (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`);
*  a list of `MVarId`s `false_goals`.

Although inconsecuential for this function, the list of goals `false_goals` reduces to `False`
if `norm_num`med.
`miscomputedDegree?` extracts error information from goals of the form
*  `a ≠ b`, assuming it comes from `⊢ coeff_of_given_degree ≠ 0`
   -- reducing to `False` means that the coefficient that was supposed to vanish, does not;
*  `a ≤ b`, assuming it comes from `⊢ degree_of_subterm ≤ degree_of_polynomial`
   -- reducing to `False` means that there is a term of degree that is apparently too large.

The case `a ≠ b` is not a perfect match with the top coefficient: reducing to `False` is not
exactly correlated with a coefficient being non-zero.
It still means that the goal is unsolvable, unless there was already a contradiction in the
hypotheses before applying `compute_degree`.
-/
def miscomputedDegree? (deg : Expr) : List Expr → List MessageData
  | tgt::tgts =>
    let rest := miscomputedDegree? deg tgts
    if tgt.ne?.isSome then
      m!"* the coefficient of degree {deg} may be zero" :: rest
    else if let some ((Expr.const ``Nat []), lhs, _) := tgt.le? then
      m!"* there is at least one term of naïve degree {lhs}" :: rest
    else rest
  | [] => []

elab_rules : tactic | `(tactic| compute_degree $[!%$bang]? $[-debug%$dbg]?) => focus do
  let dbg := dbg.isSome
  let goal := ← getMainGoal
  let gt := ← goal.getType''
  let deg := match gt.eq? with
    | some (_, _, rhs) => some rhs
    | _ => none
  let twoH := twoHeadsArgs gt
  match twoH with
    | (.anonymous, na, _, _) => throwError
        (m!"'compute_degree' inapplicable.  The goal\n\n   {gt}\n\nis expected to be '≤' or " ++
          m!"'=', instead of '{na}'.")
    | (na, .anonymous, _, _) => throwError
        (m!"'compute_degree' inapplicable.  The LHS of\n\n   {gt}\n\nbegins with '{na}'.  " ++
          m!"There is support only for\n\n   'natDegree'   'degree'   or   'coeff'")
    | _ =>
      let lem := dispatchLemma twoH
      if dbg then logInfo f!"'compute_degree' first applies lemma '{lem.getTail}'"
      let mut (gls, static) := (← goal.applyConst lem, [])
      while (! gls == []) do (gls, static) := ← splitApply gls static
      let rfled := ← try_rfl static
      setGoals rfled
      --  simplify the left-hand sides, since this is where the degree computations leave
      --  expressions such as `max (0 * 1) (max (1 + 0 + 3 * 4) (7 * 0))`
      evalTactic (← `(tactic| any_goals conv_lhs => norm_num)) <|> pure ()
      -- we save in `final_gls` the list of goals *before* `norm_num` has a chance
      -- to reduce them to `False`, so that we can get an informed error message
      let final_gls := ← getGoals
      if bang.isSome then
        evalTactic (← `(tactic| any_goals norm_num <;> try assumption)) <|> pure ()
      done <|> unless deg.isNone do
        -- we extract, from the list `final_gls` of stored goals, the ones that are now `False`
        let false_goals := ← final_gls.filterM fun mv_before => do
          let mv_after? := (← getMCtx).userNames.find? (← mv_before.getTag)
          match mv_after? with
            | some mv_after => return ((← mv_after.getType'') == (Expr.const ``False []))
            | none => return false
        -- we compute the error message
        let errors := miscomputedDegree? deg.get! (← false_goals.mapM (MVarId.getType'' ·))
        if errors.length != 0 then
          throwError (Lean.MessageData.joinSep
            (m!"The given degree is '{deg}'.  However,\n" :: errors) "\n")

end Tactic

end Mathlib.Tactic.ComputeDegree
