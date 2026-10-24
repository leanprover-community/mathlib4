/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.MvReflect
public import Mathlib.RingTheory.Ideal.Span

/-!
# `mv_mem`: axiom-free ideal membership for `MvPolynomial`

Proves `p ∈ Ideal.span {g₁, …, gₖ}` by a kernel-reducible multidivisor reduction: cancel the
leading term of the running polynomial by the first generator whose leading monomial divides it,
recording the cofactor; if the remainder reaches `0`, the recorded telescoping identity
`p = Σ cofactorᵢ · gᵢ` exhibits `p` as an explicit combination of the generators, hence in their
span (`mem_span_of_mReduce`) — checked by kernel `decide +kernel`, **axiom-free** (no
`native_decide`). Sound for any generators; it succeeds whenever the reduction terminates at `0`
(e.g. when the generators form a Gröbner basis for the lexicographic order).
-/

@[expose] public section

namespace MvSparsePoly.Kernel

open MvSparsePoly

variable {R : Type} [CommRing R] [DecidableEq R] {nvars : ℕ}

/-! ### Axiom-free ideal membership (`p ∈ Ideal.span {g₁,…,gₖ}`)

A kernel-reducible multivariate multidivisor reduction. At each step we cancel the leading term of
the running polynomial using the first generator whose leading monomial divides it, **recording**
the `(cofactor, generator)` pair. By telescoping, `p = Σ (cofactorᵢ · genᵢ) + remainder` holds
*for any* ring (`toPolyCore_mReduceK`), so if the remainder is `0` then `p` is an explicit
combination of the
generators, hence in their span. Sound regardless of whether the generators form a Gröbner basis
(it just may fail to reach `0` if they do not). No `native_decide`. -/

/-- Kernel-reducible monomial exponent subtraction (componentwise `Nat` subtraction). -/
def subMonK (a b : MvDegrees nvars) : MvDegrees nvars where
  degrees := ⟨List.zipWith (· - ·) a.degrees.toList b.degrees.toList⟩
  correct := by simp [a.correct, b.correct]
  totalDegree :=
    (⟨List.zipWith (· - ·) a.degrees.toList b.degrees.toList⟩ : Array ℕ).foldl (· + ·) 0
  totalDegree_eq := rfl

/-- Kernel-reducible monomial divisibility: `b` divides `a` iff `b` is componentwise `≤ a`. -/
def dvdMonK (b a : MvDegrees nvars) : Bool :=
  (List.zipWith (fun x y => decide (x ≤ y)) b.degrees.toList a.degrees.toList).all (·)

/-- First generator whose leading monomial divides `dp`, with its leading `(monomial, coeff)`. -/
def findDiv (dp : MvDegrees nvars) :
    List (TL R nvars) → Option (TL R nvars × MvDegrees nvars × R)
  | [] => none
  | g :: gs =>
    match g with
    | [] => findDiv dp gs
    | (dg, cg) :: _ => if dvdMonK dg dp then some (g, dg, cg) else findDiv dp gs

omit [CommRing R] [DecidableEq R] in
lemma findDiv_mem (dp : MvDegrees nvars) :
    ∀ {gs : List (TL R nvars)} {g dg cg}, findDiv dp gs = some (g, dg, cg) → g ∈ gs
  | [], _, _, _, h => by simp [findDiv] at h
  | [] :: gs, g, dg, cg, h => by
    simp only [findDiv] at h
    exact List.mem_cons_of_mem _ (findDiv_mem dp h)
  | ((d, c) :: rest) :: gs, g, dg, cg, h => by
    simp only [findDiv] at h
    by_cases hd : dvdMonK d dp
    · rw [if_pos hd] at h
      simp only [Option.some.injEq] at h
      obtain ⟨rfl, _, _⟩ := h; exact List.mem_cons_self ..
    · rw [if_neg hd] at h; exact List.mem_cons_of_mem _ (findDiv_mem dp h)

/-- Multidivisor reduction. Returns the recorded `(cofactor, generator)` steps and the remainder. -/
def mReduceK [Div R] :
    ℕ → TL R nvars → List (TL R nvars) → List (TL R nvars × TL R nvars) × TL R nvars
  | 0, p, _ => ([], p)
  | fuel + 1, p, gs =>
    match p with
    | [] => ([], [])
    | (dp, cp) :: pt =>
      if cp = 0 then mReduceK fuel pt gs    -- drop a spurious zero leading term
      else
        match findDiv dp gs with
        | none => ([], (dp, cp) :: pt)      -- leading term irreducible: stop (sound, maybe
                                            -- incomplete)
        | some (g, _, cg) =>
          let term : TL R nvars := [(subMonK dp ((g.headD (0, 0)).1), cp / cg)]
          let r := mReduceK fuel (kSub ((dp, cp) :: pt) (kMul term g)) gs
          ((term, g) :: r.1, r.2)

/-- The reduction identity, through `toPolyCore` (holds for *any* fuel and `R`). -/
lemma toPolyCore_mReduceK [Div R] : ∀ (n : ℕ) (p : TL R nvars) (gs : List (TL R nvars)),
    toPolyCore p =
      (mReduceK n p gs).1.foldr (fun s acc => toPolyCore s.1 * toPolyCore s.2 + acc) 0
        + toPolyCore (mReduceK n p gs).2
  | 0, p, _ => by simp [mReduceK]
  | n + 1, p, gs => by
    match p with
    | [] => simp [mReduceK, toPolyCore]
    | (dp, cp) :: pt =>
      by_cases hz : cp = 0
      · simp only [mReduceK, toPolyCore_cons, hz, map_zero, zero_add]
        exact toPolyCore_mReduceK n pt gs
      · simp only [mReduceK, if_neg hz]
        match hf : findDiv dp gs with
        | none => simp [toPolyCore]
        | some (g, dg, cg) =>
          simp only [List.foldr_cons]
          have ih := toPolyCore_mReduceK n
            (kSub ((dp, cp) :: pt) (kMul [(subMonK dp ((g.headD (0, 0)).1), cp / cg)] g)) gs
          rw [toPolyCore_kSub, toPolyCore_kMul] at ih
          linear_combination ih

/-- Every generator recorded in the reduction came from `gs`. -/
lemma mReduceK_gens_mem [Div R] : ∀ (n : ℕ) (p : TL R nvars) (gs : List (TL R nvars))
    (s : TL R nvars × TL R nvars), s ∈ (mReduceK n p gs).1 → s.2 ∈ gs
  | 0, p, gs, s, h => by simp [mReduceK] at h
  | n + 1, p, gs, s, h => by
    match p with
    | [] => simp [mReduceK] at h
    | (dp, cp) :: pt =>
      by_cases hz : cp = 0
      · rw [mReduceK, if_pos hz] at h; exact mReduceK_gens_mem n pt gs s h
      · rw [mReduceK, if_neg hz] at h
        match hf : findDiv dp gs with
        | none => rw [hf] at h; simp at h
        | some (g, dg, cg) =>
          rw [hf] at h
          simp only [List.mem_cons] at h
          rcases h with h | h
          · subst h; exact findDiv_mem dp hf
          · exact mReduceK_gens_mem n _ gs s h

omit [DecidableEq R] in
/-- A recorded combination `Σ cofactorᵢ · genᵢ` lies in the span of the generators. -/
lemma foldr_mem_span {S : Set (MvPolynomial (Fin nvars) R)}
    (steps : List (TL R nvars × TL R nvars)) (h : ∀ s ∈ steps, toPolyCore s.2 ∈ S) :
    (steps.foldr (fun s acc => toPolyCore s.1 * toPolyCore s.2 + acc) 0) ∈ Ideal.span S := by
  induction steps with
  | nil => simp only [List.foldr_nil]; exact Ideal.zero_mem _
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    refine Ideal.add_mem _ ?_ (ih fun s hs => h s (List.mem_cons_of_mem _ hs))
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (h hd (List.mem_cons_self ..)))

/-- Fuel bound: large enough that the reduction terminates for the goals we run (each step strictly
lowers the leading monomial); since `mReduceK` stops as soon as the polynomial is empty or
irreducible, an overestimate costs nothing. -/
def mReduce [Div R] (p : TL R nvars) (gs : List (TL R nvars)) :
    List (TL R nvars × TL R nvars) × TL R nvars :=
  let fuel := ((p.map (fun t => t.1.totalDegree)).foldr Nat.max 0 + 1) ^ (nvars + 1) + p.length + 2
  mReduceK fuel p gs

/-- The reduction identity for `mReduce`. -/
lemma toPolyCore_mReduce [Div R] (p : TL R nvars) (gs : List (TL R nvars)) :
    toPolyCore p =
      (mReduce p gs).1.foldr (fun s acc => toPolyCore s.1 * toPolyCore s.2 + acc) 0
        + toPolyCore (mReduce p gs).2 :=
  toPolyCore_mReduceK _ p gs

/-- **Soundness of `mv_mem`**: if the multidivisor reduction of `p` by the generators leaves no
nonzero remainder, then `p` is in the ideal they span. -/
theorem mem_span_of_mReduce [Div R] {p : MvPolynomial (Fin nvars) R}
    {S : Set (MvPolynomial (Fin nvars) R)} (lp : TL R nvars) (lgs : List (TL R nvars))
    (h_p : toPolyCore lp = p) (h_gs : ∀ lg ∈ lgs, toPolyCore lg ∈ S)
    (h : (mReduce lp lgs).2.filter (·.2 ≠ 0) = []) : p ∈ Ideal.span S := by
  have hrem : toPolyCore (mReduce lp lgs).2 = 0 := by
    rw [← toPolyCore_filter_nonzero, h]; rfl
  rw [← h_p, toPolyCore_mReduce lp lgs, hrem, add_zero]
  exact foldr_mem_span _ fun s hs => h_gs s.2 (mReduceK_gens_mem _ _ _ s hs)


end MvSparsePoly.Kernel

public meta section

open Lean Elab Tactic Meta MvSparsePoly.Kernel

/-- Extract the generator expressions from a set literal `{g₁, …, gₖ}`
(`insert`/singleton/empty). -/
partial def extractGens (S : Expr) : MetaM (List Expr) := do
  match (← whnfR S).getAppFnArgs with
  | (``Insert.insert, #[_, _, _, a, s]) => return a :: (← extractGens s)
  | (``Singleton.singleton, #[_, _, _, a]) => return [a]
  | (``EmptyCollection.emptyCollection, _) => return []
  | _ => throwError "mv_mem: cannot read generators from the span set {S}"

/-- Prove `p ∈ Ideal.span {g₁, …, gₖ}` for `MvPolynomial`s by a kernel-reducible multidivisor
reduction (`mReduce`): reflect `p` and the generators, then `decide +kernel` that the reduction
remainder is `0`. **Axiom-free** (no `native_decide`). Sound always; succeeds when the generators
reduce `p` to `0` (e.g. when they form a Gröbner basis for the relevant order). -/
elab "mv_mem" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let (``Membership.mem, args) := tgt.getAppFnArgs
    | throwError "mv_mem: goal is not `p ∈ Ideal.span S`"
  let a1 := args[args.size - 1]!
  let a2 := args[args.size - 2]!
  let (coll, elem) ←
    if a1.getAppFnArgs.1 == ``Ideal.span then pure (a1, a2)
    else if a2.getAppFnArgs.1 == ``Ideal.span then pure (a2, a1)
    else throwError "mv_mem: goal is not membership in an `Ideal.span`"
  let S := coll.appArg!
  let (``MvPolynomial, #[σ, R, _]) := (← inferType elem).getAppFnArgs
    | throwError "mv_mem: element is not an MvPolynomial (Fin n) R"
  let n := (← whnfR σ).appArg!
  let mkBridge (l orig : Expr) : MetaM Expr := do
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``MvSparsePoly.toPolyCore #[l]) orig)
    let (res, _) ← simpGoal m.mvarId! (← bridgeSimpK)
    if let some (_, m2) := res then m2.refl
    instantiateMVars m
  let lp ← reifyK R n elem
  let hp ← mkBridge lp elem
  let gens ← extractGens S
  let lgs ← gens.mapM (fun gExpr => reifyK R n gExpr)
  let elemTy ← inferType (lgs.headD lp)
  let lgsLit ← mkListLit elemTy lgs
  -- `mem_span_of_mReduce lp lgs hp` leaves two goals: `h_gs` (generators in `S`) and the remainder.
  -- `S` is implicit, so supply it explicitly (positions: R,inst,inst,nvars,inst,p,S,lp,lgs,h_p).
  let pf ← mkAppOptM ``MvSparsePoly.Kernel.mem_span_of_mReduce
    #[none, none, none, none, none, none, some S, some lp, some lgsLit, some hp]
  let goals ← g.apply pf
  let (m_gs, m_h) ← match goals with
    | [a, b] => pure (a, b)
    | _ => throwError "mv_mem: expected two residual goals, got {goals.length}"
  -- 1) every reflected generator's image is in the span set `S`
  replaceMainGoal [m_gs]
  evalTactic (← `(tactic| intro lg hlg; fin_cases hlg <;>
    simp only [MvSparsePoly.Kernel.toPolyCore_kAdd, MvSparsePoly.Kernel.toPolyCore_kMul,
      MvSparsePoly.Kernel.toPolyCore_kSub, MvSparsePoly.Kernel.toPolyCore_kNeg,
      MvSparsePoly.Kernel.toPolyCore_kPow, MvSparsePoly.Kernel.toPolyCore_X_terms,
      MvSparsePoly.Kernel.toPolyCore_C_terms, MvSparsePoly.Kernel.toPolyCore_one_terms,
      MvSparsePoly.Kernel.toPolyCore_zero_terms, map_ofNat, map_one, map_zero,
      Set.mem_insert_iff, Set.mem_singleton_iff, eq_self_iff_true, true_or, or_true, or_false]))
  let rem ← getGoals
  unless rem.isEmpty do throwError "mv_mem h_gs residual: {← rem.mapM fun x => x.getType}"
  -- 2) the kernel-decided remainder is empty
  setGoals [m_h]
  evalTactic (← `(tactic| decide +kernel))

attribute [nolint defsWithUnderscore] tacticMv_mem
