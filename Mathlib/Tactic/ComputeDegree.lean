/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!

# `compute_degree` and `monicity`: tactics for explicit polynomials

This file defines two related tactics: `compute_degree` and `monicity`.

Using `compute_degree` when the goal is of one of the seven forms
*  `natDegree f ≤ d` (or `<`),
*  `degree f ≤ d` (or `<`),
*  `natDegree f = d`,
*  `degree f = d`,
*  `coeff f d = r`, if `d` is the degree of `f`,
tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

Using `monicity` when the goal is of the form `Monic f` tries to solve the goal.
It may leave side-goals, in case it is not entirely successful.

Both tactics admit a `!` modifier (`compute_degree!` and `monicity!`) instructing
Lean to try harder to close the goal.

See the doc-strings for more details.

##  Future work

* Currently, `compute_degree` does not deal correctly with some edge cases.  For instance,
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

If the goal has the form `natDegree f < d`, then we convert it to two separate goals:
* `natDegree f ≤ ?_`, on which we apply the following steps;
* `?_ < d`;
where `?_` is a metavariable that `compute_degree` computes in its process.
We proceed similarly for `degree f < d`.

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

variable {R : Type*}

section semiring
variable [Semiring R]

theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le

theorem natDegree_natCast_le (n : ℕ) : natDegree (n : R[X]) ≤ 0 := (natDegree_natCast _).le
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
    exact coeff_mul_of_natDegree_le ‹_› ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ddf ?_)
    · exact natDegree_mul_le_of_le ‹_› ‹_›
    · exact ne_comm.mp h

theorem coeff_pow_of_natDegree_le_of_eq_ite' {m n o : ℕ} {a : R} {p : R[X]}
    (h_pow : natDegree p ≤ n) (h_exp : m * n ≤ o) (h_pow_bas : coeff p n = a) :
    coeff (p ^ m) o = if o = m * n then a ^ m else 0 := by
  split_ifs with h
  · subst h h_pow_bas
    exact coeff_pow_of_natDegree_le ‹_›
  · apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt ?_ (lt_of_le_of_ne ‹_› ?_)
    · exact natDegree_pow_le_of_le m ‹_›
    · exact Iff.mp ne_comm h

section SMul

variable {S : Type*} [SMulZeroClass S R] {n : ℕ} {a : S} {f : R[X]}

theorem natDegree_smul_le_of_le (hf : natDegree f ≤ n) :
    natDegree (a • f) ≤ n :=
  (natDegree_smul_le a f).trans hf

theorem degree_smul_le_of_le (hf : degree f ≤ n) :
    degree (a • f) ≤ n :=
  (degree_smul_le a f).trans hf

theorem coeff_smul : (a • f).coeff n = a • f.coeff n := rfl

end SMul

section congr_lemmas

/-- The following two lemmas should be viewed as a hand-made "congr"-lemmas.
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

theorem degree_eq_of_le_of_coeff_ne_zero' {deg m o : WithBot ℕ} {c : R} {p : R[X]}
    (h_deg_le : degree p ≤ m) (coeff_eq : coeff p (WithBot.unbotD 0 deg) = c)
    (coeff_ne_zero : c ≠ 0) (deg_eq_deg : m = deg) (coeff_eq_deg : o = deg) :
    degree p = deg := by
  subst coeff_eq coeff_eq_deg deg_eq_deg
  rcases eq_or_ne m ⊥ with rfl | hh
  · exact bot_unique h_deg_le
  · obtain ⟨m, rfl⟩ := WithBot.ne_bot_iff_exists.mp hh
    exact degree_eq_of_le_of_coeff_ne_zero ‹_› ‹_›

variable {m n : ℕ} {f : R[X]} {r : R}

theorem coeff_congr_lhs (h : coeff f m = r) (natDeg_eq_coeff : m = n) : coeff f n = r :=
  natDeg_eq_coeff ▸ h
theorem coeff_congr (h : coeff f m = r) (natDeg_eq_coeff : m = n) {s : R} (rs : r = s) :
    coeff f n = s :=
  natDeg_eq_coeff ▸ rs ▸ h

end congr_lemmas

end semiring

section ring
variable [Ring R]

theorem natDegree_intCast_le (n : ℤ) : natDegree (n : R[X]) ≤ 0 := (natDegree_intCast _).le

theorem coeff_sub_of_eq {n : ℕ} {a b : R} {f g : R[X]} (hf : f.coeff n = a) (hg : g.coeff n = b) :
    (f - g).coeff n = a - b := by subst hf hg; apply coeff_sub

theorem coeff_intCast_ite {n : ℕ} {a : ℤ} : (Int.cast a : R[X]).coeff n = ite (n = 0) a 0 := by
  simp only [← C_eq_intCast, coeff_C, Int.cast_ite, Int.cast_zero]

end ring

end recursion_lemmas

section Tactic

open Lean Elab Tactic Meta Expr

/-- `twoHeadsArgs e` takes an `Expr`ession `e` as input and recurses into `e` to make sure
that `e` looks like `lhs ≤ rhs`, `lhs < rhs` or `lhs = rhs` and that `lhs` is one of
`natDegree f, degree f, coeff f d`.
It returns
* the function being applied on the LHS (`natDegree`, `degree`, or `coeff`),
  or else `.anonymous` if it's none of these;
* the name of the relation (`Eq`, `LE.le` or `LT.lt`), or else `.anonymous` if it's none of these;
* either
  * `.inl zero`, `.inl one`, or `.inl many` if the polynomial in a numeral;
  * or `.inr` of the head symbol of `f`;
  * or `.inl .anonymous` if inapplicable;
* if it exists, whether the `rhs` is a metavariable;
* if the LHS is `coeff f d`, whether `d` is a metavariable.

This is all the data needed to figure out whether `compute_degree` can make progress on `e`
and, if so, which lemma it should apply.

Sample outputs:
* `natDegree (f + g) ≤ d => (natDegree, LE.le, HAdd.hAdd, d.isMVar, none)` (similarly for `=`);
* `degree (f * g) = d => (degree, Eq, HMul.hMul, d.isMVar, none)` (similarly for `≤`);
* `coeff (1 : ℕ[X]) c = x => (coeff, Eq, one, x.isMVar, c.isMVar)` (no `≤` option!).
-/
def twoHeadsArgs (e : Expr) : Name × Name × (Name ⊕ Name) × List Bool := Id.run do
  let (eq_or_le, lhs, rhs) ← match e.getAppFnArgs with
    | (na@``Eq, #[_, lhs, rhs])       => pure (na, lhs, rhs)
    | (na@``LE.le, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | (na@``LT.lt, #[_, _, lhs, rhs]) => pure (na, lhs, rhs)
    | _ => return (.anonymous, .anonymous, .inl .anonymous, [])
  let (ndeg_or_deg_or_coeff, pol, and?) ← match lhs.getAppFnArgs with
    | (na@``Polynomial.natDegree, #[_, _, pol])     => (na, pol, [rhs.isMVar])
    | (na@``Polynomial.degree,    #[_, _, pol])     => (na, pol, [rhs.isMVar])
    | (na@``Polynomial.coeff,     #[_, _, pol, c])  => (na, pol, [rhs.isMVar, c.isMVar])
    | _ => return (.anonymous, eq_or_le, .inl .anonymous, [])
  let head := match pol.numeral? with
    -- can I avoid the tri-splitting `n = 0`, `n = 1`, and generic `n`?
    | some 0 => .inl `zero
    | some 1 => .inl `one
    | some _ => .inl `many
    | none => match pol.getAppFnArgs with
      | (``DFunLike.coe, #[_, _, _, _, polFun, _]) =>
        let na := polFun.getAppFn.constName
        if na ∈ [``Polynomial.monomial, ``Polynomial.C] then
          .inr na
        else
          .inl .anonymous
      | (na, _) => .inr na
  (ndeg_or_deg_or_coeff, eq_or_le, head, and?)

/--
`getCongrLemma (lhs_name, rel_name, Mvars?)` returns the name of a lemma that preprocesses
one of the seven targets
*  `natDegree f ≤ d`;
*  `natDegree f < d`;
*  `natDegree f = d`;
*  `degree f ≤ d`;
*  `degree f < d`;
*  `degree f = d`.
*  `coeff f d = r`.

The end goals are of the form
* `natDegree f ≤ ?_`, `degree f ≤ ?_`, `coeff f ?_ = ?_`, or `?_ < d` with fresh metavariables;
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
    | (_,           ``LT.lt, [rhs]) => if rhs then ``id else ``lt_of_le_of_lt
    | (``natDegree, ``Eq, [rhs])    => if rhs then ``id else ``natDegree_eq_of_le_of_coeff_ne_zero'
    | (``degree,    ``Eq, [rhs])    => if rhs then ``id else ``degree_eq_of_le_of_coeff_ne_zero'
    | (``coeff,     ``Eq, [rhs, c]) =>
      match rhs, c with
      | false, false => ``coeff_congr
      | false, true  => ``Eq.trans
      | true, false  => ``coeff_congr_lhs
      | true, true   => ``id
    | _ => ``id
  if debug then
    let last := nam.lastComponentAsString
    let natr := if last == "trans" then nam.toString else last
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
--  for goals of the form `natDegree f ≤ d`, `degree f ≤ d`, `coeff f d = a`, in this order.
def dispatchLemma
    (twoH : Name × Name × (Name ⊕ Name) × List Bool) (debug : Bool := false) : Name :=
  match twoH with
    | (.anonymous, _, _) => ``id -- `twoH` gave default value, so we do nothing
    | (_, .anonymous, _) => ``id -- `twoH` gave default value, so we do nothing
    | (na1, na2, head, bools) =>
      let msg := f!"\ndispatchLemma:\n  {head}"
      -- if there is some non-metavariable on the way, we "congr" it away
      if false ∈ bools then getCongrLemma (na1, na2, bools) debug
      else
      -- otherwise, we select either the first, second or third element of the triple in `nas` below
      let π (natDegLE : Name) (degLE : Name) (coeff : Name) : Name := Id.run do
        let lem := match na1, na2 with
          | ``natDegree, ``LE.le => natDegLE
          | ``degree, ``LE.le => degLE
          | ``coeff, ``Eq => coeff
          | _, ``LE.le => ``le_rfl
          | _, _ => ``rfl
        if debug then
          dbg_trace f!"{lem.lastComponentAsString}\n{msg}"
        lem
      match head with
        | .inl `zero => π ``natDegree_zero_le ``degree_zero_le ``coeff_zero
        | .inl `one  => π ``natDegree_one_le ``degree_one_le ``coeff_one
        | .inl `many => π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inl .anonymous => π ``le_rfl ``le_rfl ``rfl
        | .inr ``HAdd.hAdd =>
          π ``natDegree_add_le_of_le ``degree_add_le_of_le ``coeff_add_of_eq
        | .inr ``HSub.hSub =>
          π ``natDegree_sub_le_of_le ``degree_sub_le_of_le ``coeff_sub_of_eq
        | .inr ``HMul.hMul =>
          π ``natDegree_mul_le_of_le ``degree_mul_le_of_le ``coeff_mul_add_of_le_natDegree_of_eq_ite
        | .inr ``HPow.hPow =>
          π ``natDegree_pow_le_of_le ``degree_pow_le_of_le ``coeff_pow_of_natDegree_le_of_eq_ite'
        | .inr ``Neg.neg =>
          π ``natDegree_neg_le_of_le ``degree_neg_le_of_le ``coeff_neg
        | .inr ``Polynomial.X =>
          π ``natDegree_X_le ``degree_X_le ``coeff_X
        | .inr ``Nat.cast =>
          π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inr ``NatCast.natCast =>
          π ``natDegree_natCast_le ``degree_natCast_le ``coeff_natCast_ite
        | .inr ``Int.cast =>
          π ``natDegree_intCast_le ``degree_intCast_le ``coeff_intCast_ite
        | .inr ``IntCast.intCast =>
          π ``natDegree_intCast_le ``degree_intCast_le ``coeff_intCast_ite
        | .inr ``Polynomial.monomial =>
          π ``natDegree_monomial_le ``degree_monomial_le ``coeff_monomial
        | .inr ``Polynomial.C =>
          π ``natDegree_C_le ``degree_C_le ``coeff_C
        | .inr ``HSMul.hSMul =>
          π ``natDegree_smul_le_of_le ``degree_smul_le_of_le ``coeff_smul
        | _ => π ``le_rfl ``le_rfl ``rfl

/-- `try_rfl mvs` takes as input a list of `MVarId`s, scans them partitioning them into two
lists: the goals containing some metavariables and the goals not containing any metavariable.

If a goal containing a metavariable has the form `?_ = x`, `x = ?_`, where `?_` is a metavariable
and `x` is an expression that does not involve metavariables, then it closes this goal using `rfl`,
effectively assigning the metavariable to `x`.

If a goal does not contain metavariables, it tries `rfl` on it.

It returns the list of `MVarId`s, beginning with the ones that initially involved (`Expr`)
metavariables followed by the rest.
-/
def try_rfl (mvs : List MVarId) : MetaM (List MVarId) := do
  let (yesMV, noMV) := ← mvs.partitionM fun mv =>
                          return hasExprMVar (← instantiateMVars (← mv.getDecl).type)
  let tried_rfl := ← noMV.mapM fun g => g.applyConst ``rfl <|> return [g]
  let assignable := ← yesMV.mapM fun g => do
    let tgt := ← instantiateMVars (← g.getDecl).type
    match tgt.eq? with
      | some (_, lhs, rhs) =>
        if (isMVar rhs && (! hasExprMVar lhs)) ||
           (isMVar lhs && (! hasExprMVar rhs)) then
           g.applyConst ``rfl
        else pure [g]
      | none =>
        return [g]
  return (assignable.flatten ++ tried_rfl.flatten)

/--
`splitApply mvs static` takes two lists of `MVarId`s.  The first list, `mvs`,
corresponds to goals that are potentially within the scope of `compute_degree`:
namely, goals of the form
`natDegree f ≤ d`, `degree f ≤ d`, `natDegree f = d`, `degree f = d`, `coeff f d = r`.

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
  return (progress.flatten, static ++ curr_static)

/-- `miscomputedDegree? deg false_goals` takes as input
*  an `Expr`ession `deg`, representing the degree of a polynomial
  (i.e. an `Expr`ession of inferred type either `ℕ` or `WithBot ℕ`);
*  a list of `MVarId`s `false_goals`.

Although inconsequential for this function, the list of goals `false_goals` reduces to `False`
if `norm_num`med.
`miscomputedDegree?` extracts error information from goals of the form
*  `a ≠ b`, assuming it comes from `⊢ coeff_of_given_degree ≠ 0`
  --- reducing to `False` means that the coefficient that was supposed to vanish, does not;
*  `a ≤ b`, assuming it comes from `⊢ degree_of_subterm ≤ degree_of_polynomial`
  --- reducing to `False` means that there is a term of degree that is apparently too large;
*  `a = b`, assuming it comes from `⊢ computed_degree ≤ given_degree`
  --- reducing to `False` means that there is a term of degree that is apparently too large.

The cases `a ≠ b` and `a = b` are not a perfect match with the top coefficient:
reducing to `False` is not exactly correlated with a coefficient being non-zero.
It does mean that `compute_degree` reduced the initial goal to an unprovable state
(unless there was already a contradiction in the initial hypotheses!), but it is indicative that
there may be some problem.
-/
def miscomputedDegree? (deg : Expr) : List Expr → List MessageData
  | tgt::tgts =>
    let rest := miscomputedDegree? deg tgts
    if tgt.ne?.isSome then
      m!"* the coefficient of degree {deg} may be zero" :: rest
    else if let some ((Expr.const ``Nat []), lhs, _) := tgt.le? then
      m!"* there is at least one term of naïve degree {lhs}" :: rest
    else if let some (_, lhs, _) := tgt.eq? then
      m!"* there may be a term of naïve degree {lhs}" :: rest
    else rest
  | [] => []

/--
`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d` (or `<`),
*  `degree f ≤ d` (or `<`),
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d`, `d' ≤ d`, `d' < d`, or `r ≠ 0`, where `d'` in `ℕ`
or `WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to close them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the remaining goals and tries `assumption`.
-/
syntax (name := computeDegree) "compute_degree" "!"? : tactic

initialize registerTraceClass `Tactic.compute_degree

@[inherit_doc computeDegree]
macro "compute_degree!" : tactic => `(tactic| compute_degree !)

elab_rules : tactic | `(tactic| compute_degree $[!%$bang]?) => focus <| withMainContext do
  let goal ← getMainGoal
  let gt ← goal.getType''
  let deg? := match gt.eq? with
    | some (_, _, rhs) => some rhs
    | _ => none
  let twoH := twoHeadsArgs gt
  match twoH with
    | (_, .anonymous, _) => throwError m!"'compute_degree' inapplicable. \
        The goal{indentD gt}\nis expected to be '≤', '<' or '='."
    | (.anonymous, _, _) => throwError m!"'compute_degree' inapplicable. \
        The LHS must be an application of 'natDegree', 'degree', or 'coeff'."
    | _ =>
      let lem := dispatchLemma twoH
      trace[Tactic.compute_degree]
        f!"'compute_degree' first applies lemma '{lem.lastComponentAsString}'"
      let mut (gls, static) := (← goal.applyConst lem, [])
      while gls != [] do (gls, static) ← splitApply gls static
      let rfled ← try_rfl static
      setGoals rfled
      --  simplify the left-hand sides, since this is where the degree computations leave
      --  expressions such as `max (0 * 1) (max (1 + 0 + 3 * 4) (7 * 0))`
      evalTactic
        (← `(tactic| try any_goals conv_lhs =>
                       (simp +decide only [Nat.cast_withBot]; norm_num)))
      if bang.isSome then
        let mut false_goals : Array MVarId := #[]
        let mut new_goals : Array MVarId := #[]
        for g in ← getGoals do
          let gs' ← run g do evalTactic (←
            `(tactic| try (any_goals norm_num <;> norm_cast <;> try assumption)))
          new_goals := new_goals ++ gs'.toArray
          if ← gs'.anyM fun g' => g'.withContext do return (← g'.getType'').isConstOf ``False then
            false_goals := false_goals.push g
        setGoals new_goals.toList
        if let some deg := deg? then
          let errors := miscomputedDegree? deg (← false_goals.mapM (MVarId.getType'' ·)).toList
          unless errors.isEmpty do
            throwError Lean.MessageData.joinSep
              (m!"The given degree is '{deg}'.  However,\n" :: errors) "\n"

/-- `monicity` tries to solve a goal of the form `Monic f`.
It converts the goal into a goal of the form `natDegree f ≤ n` and one of the form `f.coeff n = 1`
and calls `compute_degree` on those two goals.

The variant `monicity!` starts like `monicity`, but calls `compute_degree!` on the two side-goals.
-/
macro (name := monicityMacro) "monicity" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree))

@[inherit_doc monicityMacro]
macro "monicity!" : tactic =>
  `(tactic| (apply monic_of_natDegree_le_of_coeff_eq_one <;> compute_degree!))

end Tactic

end Mathlib.Tactic.ComputeDegree

/-!
 We register `compute_degree` with the `hint` tactic.
 -/
register_hint compute_degree
