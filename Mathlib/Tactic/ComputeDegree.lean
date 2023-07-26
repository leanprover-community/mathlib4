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

theorem natDegree_C_le /-(n : ℕ)-/ (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le --.trans n.zero_le

theorem natDegree_nat_cast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le

theorem coeff_nat_cast_ite {n a : ℕ} : (Nat.cast a : R[X]).coeff n = ite (n = 0) a 0 := by
  simp only [← C_eq_nat_cast, coeff_C, Nat.cast_ite, Nat.cast_zero]

theorem coeff_add_of_eq {n : ℕ} {a b : R} {f g : R[X]}
    (hf : f.coeff n = a) (hg : g.coeff n = b) :
    (f + g).coeff n = a + b := by subst ‹_› ‹_› ; apply coeff_add

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

theorem coeff_mul_add_of_le_natDegree_of_eq_ite {d df dg : ℕ} {a b : R} {f g : R[X]}
    (hdf : natDegree f ≤ df) (hdg : natDegree g ≤ dg)
    (hf : f.coeff df = a) (hg : g.coeff dg = b) (ddf : df + dg ≤ d) :
    (f * g).coeff d = if d = df + dg then a * b else 0 := by
  split_ifs with h
  · subst hf hg h
    exact coeff_mul_add_of_le_natDegree_of_eq hdf hdg
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le hdf hdg
    · exact ne_comm.mp h

theorem coeff_pow_of_natDegree_le_of_eq_ite [Semiring R] {m n o : ℕ} {a : R} {p : R[X]}
    (pn : natDegree p ≤ n) (mno : m * n ≤ o) (ha : coeff p n = a) :
    coeff (p ^ m) o = if o = m * n then a ^ m else 0 := by
  split_ifs with h
  · subst h ha
    rw [mul_comm]
    apply coeff_pow_of_natDegree_le pn
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne mno ?_)
    · exact natDegree_pow_le_of_le m pn
    · exact Iff.mp ne_comm h

section congr_lemmas

--  The following two lemmas should be viewed as a hand-made "congr"-lemmas.
--  They achieve the following goals:
--  * they introduce fresh metavariables for several of the important variables --
--    this helps `compute_degree`, since it does not "pre-estimate" the degree,
--    but it "picks it up along the way";
--  * they split checking the inequality `coeff p n ≠ 0` into the task of
--    finding a value `c` for the `coeff` and then
--    proving that this value is non-zero by `coeff_ne_zero`.
theorem natDegree_eq_of_le_of_coeff_ne_zero' {m deg o : ℕ} {c : R} {p : R[X]}
    (pn : natDegree p ≤ m) (coeff_eq : coeff p o = c)
    (coeff_ne_zero : c ≠ 0) (exp_deg_eq_deg : m = deg) (natDeg_eq_coeff : m = o) :
    natDegree p = deg := by
  subst coeff_eq exp_deg_eq_deg natDeg_eq_coeff
  exact natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

theorem degree_eq_of_le_of_coeff_ne_zero' {n : WithBot ℕ} {m o : ℕ} {c : R} {p : R[X]}
    (pn : natDegree p ≤ m) (coeff_eq : coeff p o = c)
    (coeff_ne_zero : c ≠ 0) (exp_deg_eq_deg : m = n) (natDeg_eq_coeff : m = o) :
    degree p = n := by
  subst coeff_eq exp_deg_eq_deg natDeg_eq_coeff
  rcases eq_or_ne p 0 with (rfl|H)
  · exact False.elim (coeff_ne_zero rfl)
  · apply (degree_eq_iff_natDegree_eq ‹_›).mpr
    apply natDegree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

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

open Lean Elab Tactic Meta

/--  `Lean.Name.getTail name` takes `name : Name` as input.  If `name = .str _ tail`,
the it returns `tail`.  For instance,
```lean
#eval Lean.Name.getTail ``Lean.Expr.bvar  -- "bvar"
```
-/
def _root_.Lean.Name.getTail : Name → String
  | .str _ tail => tail
  | _ => ""

/-! `isDegLE e` checks whether `e` is an `Expr`ession representing an inequality whose LHS is
the `natDegree/degree` of a polynomial with coefficients in a semiring `R`.
If `e` represents
*  `natDegree f ≤ d`, then it returns `(true,  f)`;
*  `degree f ≤ d`,    then it returns `(false, f)`;
*  anything else, then it throws an error.
-/

/-! `computeDegreeLECore pol mv π` takes as input
* an `Expr`ession `pol` representing a polynomial;
* an `MVarId` `mv`;
* a function `π : Name × Name → Name`, typically
* * `pi = Prod.fst` if the goal is `natDegree f ≤ d`,
* * `pi = Prod.snd` if the goal is `degree f ≤ d`.

It recurses into `pol` matching each step with the appropriate pair of lemmas:
the first if the goal involves `natDegree`, the second if it involves `degree`.
It applies the lemma at each stage and continues until it reaches a "leaf":
either the final goal asks for the degree of a "cast" of some sort, of `X`, of `monomial n r`
or of an `fvar`.
In each case it closes the goal, assuming that the goal is `natDegree f ≤ natDegree f` or
`degree f ≤ degree f`, in the case of an `fvar`.
-/

open Lean Meta Elab Expr Tactic

open ConstantInfo in
/-- `declNameInThm thm tag` takes two `Name`s as input.  It checks that the declaration called
`thm` exists and that one of its hypotheses is called `tag`.
Since `compute_degree` finds goals by referring to their tags, this check makes sure that
the tactic continues working and highlights potential problems.
-/
def declNameInThm (thm tag : Name) : MetaM Unit := do
  let tail :=  m!"\n\n  `{thm.getTail}`\n\nchange name?"
  match (← getEnv).find? thm with
    | none => throwError m!"Did lemma" ++ tail
    | some decl => do
      let stat := (toConstantVal decl).type
      let listBinderNames := stat.getForallBinderNames
      guard (tag ∈ listBinderNames) <|>
        throwError m!"Did the hypothesis\n\n  `{tag}`\n\nof lemma" ++ tail

/-! Check that the theorems
`natDegree_eq_of_le_of_coeff_ne_zero'` and `degree_eq_of_le_of_coeff_ne_zero'` contain hypotheses
called `exp_deg_eq_deg` and `natDeg_eq_coeff`. -/
#eval do
  let tags := [`exp_deg_eq_deg, `natDeg_eq_coeff]
  let thms := [``natDegree_eq_of_le_of_coeff_ne_zero', ``degree_eq_of_le_of_coeff_ne_zero']
  let _ := ← (tags.zip thms).mapM fun (tag, thm) => declNameInThm thm tag

/-- `twoHeadsArgs e` takes an `Expr`ession `e` as input and recurses into `e` to make sure
the `e` looks like `lhs ≤ _` or `lhs = _` and that `lhs` is one of `natDegree, degree, coeff`.
Returns `none` if any one of the checks fails.

Sample outputs:
* `natDegree f ≤ d => (natDegree, LE.le, f, [d])` (similarly for `=`);
* `degree f = d => (degree, Eq, f, [d])` (similarly for `≤`);
* `coeff f c = x => (coeff, Eq, f, [x, c])` (no `≤` option!).
-/
def twoHeadsArgs (e : Expr) : Option (Name × Name × Expr × List Expr) := do
let (eq_or_le, lhs, rhs) := ← match e.getAppFnArgs with
  | (na@``Eq, #[_, lhs, rhs])       => return (na, lhs, rhs)
  | (na@``LE.le, #[_, _, lhs, rhs]) => return (na, lhs, rhs)
  | _ => none
let (ndeg_or_deg_or_coeff, pol, and?) := ← match lhs.getAppFnArgs with
  | (na@``Polynomial.natDegree, #[_, _, pol]) => return (na, pol, [rhs])
  | (na@``Polynomial.degree, #[_, _, pol])    => return (na, pol, [rhs])
  | (na@``Polynomial.coeff, #[_, _, pol, c])  => return (na, pol, [rhs, c])
  | _ => none
return (ndeg_or_deg_or_coeff, eq_or_le, pol, and?)

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

The 3 output names are the lemmas appropriate for a goal of the form
`natDegree f ≤ d`, `degree f ≤ d`, `coeff f n = a`, in this order.
-/
def dispatchLemma (twoH : Option (Name × Name × Expr × List Expr)) (debug : Bool := false) : Name :=
match twoH with
  | none => ``id
  | some (na1, na2, pol, lexpr) =>
    let bools := lexpr.map isMVar
    if false ∈ bools then getCongrLemma (na1, na2, bools)
    else
      let msg := f!"\ndispatchLemma:\n  numeral?: {pol.numeral?}\n  name: {pol.getAppFnArgs.1}"
      let nas := match pol.numeral? with
        -- can I avoid the tri-splitting `n = 0`, `n = 1`, and generic `n`?
        | some 0 => (``natDegree_zero_le, ``degree_zero_le, ``coeff_zero)
        | some 1 => (``natDegree_one_le, ``degree_one_le, ``coeff_nat_cast_ite)
        | some _ => (``natDegree_nat_cast_le, ``degree_nat_cast_le, ``coeff_nat_cast_ite)
        | none => match pol.getAppFnArgs with
  --  unusual indentation to improve legibility of the following block of pairs of lemmas
  | (``HAdd.hAdd, _) =>
    (``natDegree_add_le_of_le, ``degree_add_le_of_le, ``coeff_add_of_eq)
  | (``HSub.hSub, _) =>
    (``natDegree_sub_le_of_le, ``degree_sub_le_of_le, ``coeff_sub_of_eq)
  | (``HMul.hMul, _) =>
    (``natDegree_mul_le_of_le, ``degree_mul_le_of_le, ``coeff_mul_add_of_le_natDegree_of_eq_ite)
  | (``HPow.hPow, _) =>
    (``natDegree_pow_le_of_le, ``degree_pow_le_of_le, ``coeff_pow_of_natDegree_le_of_eq_ite)
  | (``Neg.neg, _) =>
    (``natDegree_neg_le_of_le, ``degree_neg_le_of_le, ``coeff_neg)
  | (``Polynomial.X, _) =>
    (``natDegree_X_le, ``degree_X_le, ``coeff_X)
  | (``Nat.cast, _) =>
    (``natDegree_nat_cast_le, ``degree_nat_cast_le, ``coeff_nat_cast_ite)
  | (``NatCast.natCast, _) =>
    (``natDegree_nat_cast_le, ``degree_nat_cast_le, ``coeff_nat_cast_ite)
  | (``Int.cast, _) =>
    (``natDegree_int_cast_le, ``degree_int_cast_le, ``coeff_int_cast_ite)
  | (``IntCast.intCast, _) =>
    (``natDegree_int_cast_le, ``degree_int_cast_le, ``coeff_int_cast_ite)
  | (``FunLike.coe, #[_, _, _, _, polFun, _]) => match polFun.getAppFnArgs with
    | (``Polynomial.monomial, _) =>
      (``natDegree_monomial_le, ``degree_monomial_le, ``coeff_monomial)
    | (``Polynomial.C, _) =>
      (``natDegree_C_le, ``degree_C_le, ``coeff_C)
    | _ => ((.anonymous, .anonymous, .anonymous))
  | _ => (``le_rfl, ``le_rfl, ``rfl)
let π : Name × Name × Name → Name := match na1, na2 with
  | ``natDegree, ``LE.le => Prod.fst
  | ``degree, ``LE.le => Prod.fst ∘ Prod.snd
  | _, _ => Prod.snd ∘ Prod.snd
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
`recOrd mvs static` takes two lists of `MVarId`s.  The first list, `mvs`, corresponds to goals that
are potentially within the scope of `compute_degree`: namely, goals of the form
`natDegree f ≤ d`, `degree f ≤ d`, `natDegree f = d`, `degree f = d`, `coeff f n = r`.

`recOrd` determines which of these goals are actually within the scope, it applies the relevant
lemma and returns two lists: the left-over goals of all the applications, followed by the
concatenation of the previous `static` list, followed by the newly discovered goals outside of the
scope of `compute_degree`. -/
def recOrd (mvs : List MVarId) (static : List MVarId) : MetaM ((List MVarId) × (List MVarId)) := do
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

open Elab.Tactic Mathlib.Meta.NormNum Lean.Meta.Simp.Context in
elab_rules : tactic | `(tactic| compute_degree $[!%$stx]? $[-debug%$dbg]?) => focus do
  let dbg := dbg.isSome
  let goal := ← getMainGoal
  let gt := ← goal.getType''
  let twoH := twoHeadsArgs gt
  if twoH.isNone then
    let cd := "'compute_degree' inapplicable.  The "
    let lhs := ← match gt.getAppFnArgs with
      | (``Eq, #[_, lhs, _])       => return lhs
      | (``LE.le, #[_, _, lhs, _]) => return lhs
      | (na, _) => throwError (cd ++ m!"goal\n\n   {gt}\n\n" ++
                               m!"is expected to be '≤' or '=', instead of '{na}'.")
    ← match lhs.getAppFnArgs with
      | (na, _) => throwError (cd ++ m!"LHS of\n\n   {gt}\n\nbegins with '{na}'.  " ++
          m!"There is support only for\n\n   'natDegree'   'degree'   or   'coeff'")
  let (lhs_head, eq_or_le, _, _) := twoH.getD default
  let lem := dispatchLemma twoH
  if dbg then logInfo f!"'compute_degree' first applies lemma '{lem.getTail}'"
  let mut (gls, static) := (← goal.applyConst lem, [])
  let tag := "exp_deg_eq_deg"
  let deg_eq_deg := ← gls.findM? fun mv => return (← mv.getTag).getTail == tag

  let (tag, deg_eq_deg) := if deg_eq_deg.isNone then
      ("natDeg_eq_coeff", ← gls.findM? fun mv => return (← mv.getTag).getTail == "natDeg_eq_coeff")
    else (tag, deg_eq_deg)
  while (! gls == []) do
    (gls, static) := ← recOrd gls static
  let rfled := ← try_rfl static
  if ((eq_or_le == ``Eq) && lhs_head != ``coeff) then match deg_eq_deg with
    | none => throwError m!"Did the tag '{tag}' disappear from '{lem.getTail}'?"
    | some deg_eq_deg =>
      let soluble? : Bool := ← withNewMCtxDepth do
        let solved? := ← normNumAt deg_eq_deg (← mkDefault) #[]
        if solved?.isSome then
          return !((← solved?.get!.2.getType) == .const ``False [])
        else return true
      guard soluble? <|> do
        let deg_trans_deg := ← deg_eq_deg.applyConst ``Eq.trans
        let nnmd := ← deg_trans_deg.mapM fun g => do normNumAt g (← mkDefault) #[]
        if let [computedDegree, givenDegree, _] := nnmd.map fun x => (x.get!).2 then
        let cdeg := (← computedDegree.getType).eq?.get!.2.1
        let gdeg := (← givenDegree.getType).eq?.get!.2.2
        throwError m!"The expected degree is '{gdeg}'\nThe computed degree is '{cdeg}'"
  setGoals rfled
  if stx.isSome then
    evalTactic (← `(tactic| any_goals norm_num <;> try assumption)) <|> pure ()
  else
    evalTactic (← `(tactic| any_goals conv_lhs => norm_num)) <|> pure ()

end Tactic

end Mathlib.Tactic.ComputeDegree

open Polynomial

section native_mathlib4_tests

/--  Add `natDegree (C a * X + X) = 1`to the test suite!
The expected degree for `natDegree (C a * X + X) ≤ 1` ends up being `max (0 + 1) 1`.
The expected degree for `coeff (C a * X + X) ?? = ??` ends up being `max (0 + 1) 1`.
 -/
example [Semiring R] {a : R} (ha : a + 1 ≠ 0) : natDegree (C a * X + X) = 1 := by
  --apply natDegree_eq_of_le_of_coeff_ne_zero
  --apply le_trans
  compute_degree! --debug


variable {n : ℕ} {z : ℤ} {f : ℤ[X]} (hn : natDegree f ≤ 5) (hd : degree f ≤ 5)

/--  This example flows through all the matches in `direct` with a `natDegree` goal. -/
example : natDegree (0 + 0 - C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : ℤ[X]) + (n : ℤ[X]) + f) ≤ 5 := by
  compute_degree!

example [Semiring R] : natDegree (OfNat.ofNat (OfNat.ofNat 0) : R[X]) ≤ 0 := by
  compute_degree

/--  This example flows through all the matches in `direct` with a `degree` goal. -/
example : degree (- C z * X ^ 5 + (monomial 2 5) ^ 2 - 0 + 1 + IntCast.intCast 1 +
    NatCast.natCast 1 + (z : ℤ[X]) + (n : ℤ[X]) + f + X ^ 6) = 6 := by
  set k := f with _h₀
  compute_degree! --debug
  simp only [ge_iff_le, hn, max_eq_left, max_eq_right, Nat.succ.injEq, not_false_eq_true, if_neg, add_zero, zero_add,
    hn.trans (Nat.le_succ 5), not_true, ite_true]
  rw [coeff_eq_zero_of_natDegree_lt]
  norm_num
  exact Iff.mpr Nat.lt_succ hn
  rw [max_eq_right]
  norm_num
  rw [max_eq_left]
  norm_num
  assumption

/-!  The following examples exhaust all the match-leaves in `direct`. -/

--  OfNat.ofNat 0
example : natDegree (0 : ℤ[X]) = 0 := by
  apply Nat.le_zero.mp
  compute_degree

--  OfNat.ofNat (non-zero)
example : natDegree (1 : ℤ[X]) = 0 := by
  compute_degree!

--  NatCast.natCast
example : natDegree (NatCast.natCast 4 : ℤ[X]) = 0 := by
  compute_degree!

--  Nat.cast
example : natDegree (Nat.cast n : ℤ[X]) ≤ 5 := by
  compute_degree!

--  IntCast.intCast
example : natDegree (IntCast.intCast 4 : ℤ[X]) ≤ 5 := by
  compute_degree!

--  Int.cast
example : natDegree (Int.cast z : ℤ[X]) ≤ 5 := by
  compute_degree!

--  Polynomial.X
example : natDegree (X : ℤ[X]) ≤ 5 := by
  compute_degree!

--  Polynomial.C
example : natDegree (C n) ≤ 5 := by
  compute_degree!

--  Polynomial.monomial
example (h : n ≤ 5) : natDegree (monomial n (5 + n)) ≤ 5 := by
  compute_degree!

--  Expr.fvar
example {f : ℕ[X]} : natDegree f ≤ natDegree f := by
  compute_degree

variable [Ring R]

--  OfNat.ofNat 0
example : natDegree (0 : R[X]) ≤ 5 := by
  compute_degree!

--  OfNat.ofNat (non-zero)
example : natDegree (1 : R[X]) ≤ 5 := by
  compute_degree!

--  NatCast.natCast
example : natDegree (NatCast.natCast 4 : R[X]) ≤ 5 := by
  compute_degree!

--  Nat.cast
example : natDegree (n : R[X]) ≤ 5 := by
  compute_degree!

--  IntCast.intCast
example : natDegree (IntCast.intCast 4 : R[X]) ≤ 5 := by
  compute_degree!

--  Int.cast
example : natDegree (z : R[X]) ≤ 5 := by
  compute_degree!

--  Polynomial.X
example : natDegree (X : R[X]) ≤ 5 := by
  compute_degree!

--  Polynomial.C
example : natDegree (C n) ≤ 5 := by
  compute_degree!

--  Polynomial.monomial
example (h : n ≤ 5) : natDegree (monomial n (5 + n : R)) ≤ 5 := by
  compute_degree!

--  Expr.fvar
example {f : R[X]} : natDegree f ≤ natDegree f := by
  compute_degree

end native_mathlib4_tests

section tests_from_mathlib3
variable {R : Type _} [Semiring R] {a b c d e : R}

-- test that `mdata` does not get in the way of the tactic
example : natDegree (7 * X : R[X]) ≤ 1 := by
  have : 0 ≤ 1 := zero_le_one
  compute_degree

-- possibly only a vestigial test from mathlib3: maybe to check for `instantiateMVars`?
example {R : Type _} [Ring R] (h : ∀ {p q : R[X]}, p.natDegree ≤ 0 → (p * q).natDegree = 0) :
    natDegree (- 1 * 1 : R[X]) = 0 := by
  apply h _
  compute_degree

-- check for making sure that `compute_degree_le` is `focus`ed
example : Polynomial.natDegree (Polynomial.C 4) ≤ 1 ∧ True := by
  constructor
  compute_degree!
  trivial

example {R : Type _} [Ring R] :
    natDegree (- 1 * 1 : R[X]) ≤ 0 := by
  compute_degree

example {F} [Ring F] {a : F} :
    natDegree (X ^ 9 - C a * X ^ 10 : F[X]) ≤ 10 := by
  compute_degree

example :
    degree (X + (X * monomial 2 1 + X * X) ^ 2) ≤ 10 := by
  compute_degree!

example : natDegree (7 * X : R[X]) ≤ 1 := by
  compute_degree

example : natDegree (0 : R[X]) ≤ 0 := by
  compute_degree

example : natDegree (1 : R[X]) ≤ 0 := by
  compute_degree

example : natDegree (2 : R[X]) ≤ 0 := by
  compute_degree

example : natDegree ((n : Nat) : R[X]) ≤ 0 := by
  compute_degree

example {R} [Ring R] {n : ℤ} : natDegree ((n : ℤ) : R[X]) ≤ 0 := by
  compute_degree

example {R} [Ring R] {n : ℕ} : natDegree ((- n : ℤ) : R[X]) ≤ 0 := by
  compute_degree

example : natDegree (monomial 5 c * monomial 1 c + monomial 7 d +
    C a * X ^ 0 + C b * X ^ 5 + C c * X ^ 2 + X ^ 10 + C e * X) ≤ 10 := by
  compute_degree

example :
    natDegree (monomial 0 c * (monomial 0 c * C 1) + monomial 0 d + C 1 + C a * X ^ 0) ≤ 0 := by
  compute_degree

example {F} [Ring F] : natDegree (X ^ 4 + 3 : F[X]) ≤ 4 := by
  compute_degree

example : natDegree ((5 * X * C 3 : _root_.Rat[X]) ^ 4) ≤ 4 := by
  compute_degree

example : natDegree ((C a * X) ^ 4) ≤ 4 := by
  compute_degree

example : degree ((X : ℤ[X]) ^ 4) ≤ 4 := by
  compute_degree

example : natDegree (monomial 4 5 * (X : ℤ[X]) ^ 4) ≤ 40 := by
  compute_degree!

example : natDegree (C a * C b + X + monomial 3 4 * X) ≤ 4 := by
  compute_degree

variable {R : Type _} [Semiring R] {a b c d e : R}

example {F} [Ring F] {a : F} :
    natDegree (X ^ 3 + C a * X ^ 10 : F[X]) ≤ 10 := by
  compute_degree

example : natDegree (7 * X : R[X]) ≤ 1 := by
  compute_degree

end tests_from_mathlib3

example [Semiring R] {a b _c d : R} (hd : (2 : R) ≠ 0) :
    natDegree ((C a * X + C b) * X ^ 2 + C d * X ^ 3 + C b * X ^ 1 + C 1 * X ^ 0 * monomial 4 2) = 4 := by
  compute_degree!

example [Semiring R] {a b c d : R} (hd : (2 : R) ≠ 0) :
    natDegree (C a * X ^ 0 + C c * X ^ 2 + C d * X ^ 3 + C b * X ^ 1 + monomial 4 2) = 4 := by
  compute_degree!



example [Ring R] {_f : R[X]} {a _b _c : R} {_m _n _o : ℕ} {ha : (1 : R) ≠ 0} :
  natDegree (monomial 1 a * X ^ 1 + X ^ 1 * X ^ 1 + X + X * X ^ 1 * X ^ 1 : R[X]) = 3 := by
  compute_degree!
--  any_goals norm_num
--  assumption

example [Ring R] {_f : R[X]} {a _b _c : R} {_m _n _o : ℕ} {ha : a + 1 ≠ 0} :
--  natDegree (C a * X ^ m + C b * X ^ n - C c * X ^ o : R[X]) = 8 := by
  natDegree (C a * X ^ 3 + X ^ 2 * X ^ 1 + X + X ^ 2 : R[X]) = 3 := by
  compute_degree!
#lint
