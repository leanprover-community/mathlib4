/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.MvRing
public import Mathlib.Tactic.LinearCombination

/-!
# Axiom-free reflection: kernel-reducible normal forms for `MvPolynomial`

This is the reflection tactic for `MvPolynomial`: `mv_decide` (and its synonym `mv_compute`) prove
an equality or inequality of Mathlib's noncomputable `MvPolynomial` by reflecting onto
`MvSparsePoly` and closing with kernel `decide +kernel` — **axiom-free** (no
`native_decide`/`Lean.ofReduceBool`, which Mathlib forbids; its `lean4checker` rejects the extra
axiom).

The subtlety is that our *runtime* arithmetic (`addCore`, `mulCore`, `ofList`)
is defined by **well-founded recursion**, which the kernel does not reduce — so plain `decide` gets
stuck. This file provides an **axiom-free** path: a parallel set of polynomial operations on raw
term lists defined by **structural** recursion (so the kernel *can* reduce them), each proved
correct with respect to `toPolyCore` (the noncomputable semantics). A goal is then decided by kernel
`decide` on the two normal-form lists.

One subtlety, already handled: building *product* monomials needs exponent-vector addition, and
`MvDegrees`' own `+` is `Array.zipWith`, which the kernel does **not** reduce either. So `kMul` uses
`addDegK` — a `List.zipWith` form that does reduce — proved equal to `+` by `addDegK_eq_add`, so the
`toPolyCore` proofs are unaffected. With that in place, full ring identities (`+`, `-`, `*`, `^`)
decide axiom-free.

The trade-off is the usual one for kernel reflection: `decide` runs in the kernel interpreter, so it
is only practical for small/medium goals — but it is **axiom-free**.
-/

@[expose] public section

namespace MvSparsePoly.Kernel

open MvSparsePoly

variable {R : Type} [CommRing R] [DecidableEq R] {nvars : ℕ}

/-- A raw term list (the data of an `MvSparsePoly`, without the sortedness/nonzero proofs). -/
abbrev TL (R : Type) (nvars : ℕ) := List (MvDegrees nvars × R)

/-- Insert one term into a descending-sorted, merged term list — **structural** recursion on the
list, so the kernel reduces it. Combines coefficients on an equal monomial. Zero coefficients (e.g.
from
cancellation) are removed once, at the end, by `List.filter` (see `toPolyCore_filter_nonzero`). -/
def insertK (t : MvDegrees nvars × R) : TL R nvars → TL R nvars
  | [] => [t]
  | (j, b) :: rest =>
    match compare t.1 j with
    | .gt => t :: (j, b) :: rest
    | .eq => (j, t.2 + b) :: rest
    | .lt => (j, b) :: insertK t rest

/-- Addition: insert each term of `a` into `b`. -/
def kAdd (a b : TL R nvars) : TL R nvars := a.foldr insertK b

/-- Negation. -/
def kNeg (a : TL R nvars) : TL R nvars := a.map (fun t => (t.1, -t.2))

/-- Subtraction. -/
def kSub (a b : TL R nvars) : TL R nvars := kAdd a (kNeg b)

/-- Kernel-reducible exponent-vector addition. `MvDegrees`' own `+` uses `Array.zipWith`, which the
kernel does **not** reduce; this `List.zipWith` form does. It is `propositionally` equal to `+`
(`addDegK_eq_add`), so all the `toPolyCore` correctness proofs transfer. -/
def addDegK (a b : MvDegrees nvars) : MvDegrees nvars where
  degrees := ⟨List.zipWith (· + ·) a.degrees.toList b.degrees.toList⟩
  correct := by simp [a.correct, b.correct]
  totalDegree :=
    (⟨List.zipWith (· + ·) a.degrees.toList b.degrees.toList⟩ : Array ℕ).foldl (· + ·) 0
  totalDegree_eq := rfl

lemma addDegK_eq_add (a b : MvDegrees nvars) : addDegK a b = a + b := by
  have hsz : a.degrees.size = b.degrees.size := by rw [a.correct, b.correct]
  have hdeg : (⟨List.zipWith (· + ·) a.degrees.toList b.degrees.toList⟩ : Array ℕ)
            = Array.zipWith (· + ·) a.degrees b.degrees := by
    apply Array.ext'; simp [Array.toList_zipWith]
  apply MvDegrees.ext
  · exact hdeg
  · change (⟨List.zipWith (· + ·) a.degrees.toList b.degrees.toList⟩ : Array ℕ).foldl (· + ·) 0
       = a.totalDegree + b.totalDegree
    rw [hdeg, array_zipWith_foldl_add a.degrees b.degrees hsz, ← a.totalDegree_eq,
      ← b.totalDegree_eq]

/-- Multiply a whole list by a single monomial `c·X^d`, then add into the accumulator. Uses
`addDegK` (kernel-reducible) for the product exponents. -/
def kMul (a b : TL R nvars) : TL R nvars :=
  a.foldr (fun t acc => kAdd (b.map (fun s => (addDegK t.1 s.1, t.2 * s.2))) acc) []

/-- Powers, by repeated `kMul` (structural on the exponent). -/
def kPow (a : TL R nvars) : ℕ → TL R nvars
  | 0 => (1 : MvSparsePoly R nvars).terms
  | k + 1 => kMul a (kPow a k)

/-! ### Correctness with respect to `toPolyCore` -/

omit [DecidableEq R] in
@[simp] lemma toPolyCore_cons (t : MvDegrees nvars × R) (l : TL R nvars) :
    toPolyCore (t :: l) = MvPolynomial.monomial (MvDegrees.toFinsupp t.1) t.2 + toPolyCore l := rfl

omit [DecidableEq R] in
/-- `insertK` adds one monomial, as seen through `toPolyCore`. -/
lemma toPolyCore_insertK (d : MvDegrees nvars) (c : R) (l : TL R nvars) :
    toPolyCore (insertK (d, c) l)
      = MvPolynomial.monomial (MvDegrees.toFinsupp d) c + toPolyCore l := by
  induction l with
  | nil => simp [insertK, toPolyCore]
  | cons hd tl ih =>
    obtain ⟨j, b⟩ := hd
    rw [insertK]
    rcases hc : compare d j with _ | _ | _
    · -- lt
      simp only [toPolyCore_cons, ih]
      abel
    · -- eq : `d = j`, so combine the coefficients via additivity of `monomial`
      obtain rfl := compare_eq_iff_eq.mp hc
      simp only [toPolyCore_cons]
      rw [map_add]
      abel
    · -- gt
      simp only [toPolyCore_cons]

omit [DecidableEq R] in
@[simp] lemma toPolyCore_kAdd (a b : TL R nvars) :
    toPolyCore (kAdd a b) = toPolyCore a + toPolyCore b := by
  induction a with
  | nil => simp [kAdd, toPolyCore]
  | cons hd tl ih =>
    obtain ⟨d, c⟩ := hd
    rw [kAdd, List.foldr_cons, ← kAdd, toPolyCore_insertK, ih, toPolyCore_cons, add_assoc]

omit [DecidableEq R] in
@[simp] lemma toPolyCore_kNeg (a : TL R nvars) : toPolyCore (kNeg a) = - toPolyCore a := by
  change toPolyCore (a.map (fun t => (t.1, -t.2))) = - toPolyCore a
  induction a with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    obtain ⟨d, c⟩ := hd
    simp only [List.map_cons, toPolyCore_cons, ih, map_neg]
    abel

omit [DecidableEq R] in
@[simp] lemma toPolyCore_kSub (a b : TL R nvars) :
    toPolyCore (kSub a b) = toPolyCore a - toPolyCore b := by
  rw [kSub, toPolyCore_kAdd, toPolyCore_kNeg, sub_eq_add_neg]

omit [DecidableEq R] in
@[simp] lemma toPolyCore_kMul (a b : TL R nvars) :
    toPolyCore (kMul a b) = toPolyCore a * toPolyCore b := by
  induction a with
  | nil => simp [kMul, toPolyCore]
  | cons hd tl ih =>
    obtain ⟨d, c⟩ := hd
    rw [kMul, List.foldr_cons, ← kMul]
    simp only [addDegK_eq_add]
    rw [toPolyCore_kAdd, ih, toPolyCore_monomial_mul, toPolyCore_cons, add_mul]

@[simp] lemma toPolyCore_kPow (a : TL R nvars) (k : ℕ) :
    toPolyCore (kPow a k) = (toPolyCore a) ^ k := by
  induction k with
  | zero => rw [kPow, pow_zero]; exact toPoly_one
  | succ m ih => rw [kPow, toPolyCore_kMul, ih, pow_succ, mul_comm]

-- Leaf bridges: `toPoly = toPolyCore ∘ terms`, so these are just the existing homomorphism lemmas.
@[simp] lemma toPolyCore_X_terms (i : Fin nvars) :
    toPolyCore (X i : MvSparsePoly R nvars).terms = MvPolynomial.X i := toPoly_X i
@[simp] lemma toPolyCore_C_terms (r : R) :
    toPolyCore (C r : MvSparsePoly R nvars).terms = MvPolynomial.C r := toPoly_C r
@[simp] lemma toPolyCore_one_terms :
    toPolyCore (1 : MvSparsePoly R nvars).terms = 1 := toPoly_one
omit [DecidableEq R] in
@[simp] lemma toPolyCore_zero_terms :
    toPolyCore (0 : MvSparsePoly R nvars).terms = 0 := toPoly_zero

/-- Soundness for `=` goals. `l₁`, `l₂` are the (kernel-computed) normal-form lists; the final
hypothesis compares them *after dropping zero coefficients* (so cancellations like `X·X - X·X`
match `0`). This direction needs no canonical-form invariant — `toPolyCore` is the semantics, and
`toPolyCore_filter_nonzero` says dropping zeros doesn't change it. (A `≠` tactic would also need
`kAdd`/`kMul` to produce *sorted* lists, to invoke `toPolyCore_injective_of_sorted`.) -/
theorem eq_of_core {p q : MvPolynomial (Fin nvars) R} (l₁ l₂ : TL R nvars)
    (h₁ : toPolyCore l₁ = p) (h₂ : toPolyCore l₂ = q)
    (h : l₁.filter (·.2 ≠ 0) = l₂.filter (·.2 ≠ 0)) : p = q := by
  rw [← h₁, ← h₂, ← toPolyCore_filter_nonzero l₁, ← toPolyCore_filter_nonzero l₂, h]

/-! ### Axiom-free `≠` (a differing coefficient witnesses inequality — no canonical-form needed) -/

/-- Coefficient of monomial `D` read directly off a term list (sum over matching terms). -/
def listCoeff (D : MvDegrees nvars) (l : TL R nvars) : R :=
  (l.filter (fun t => t.1 = D)).foldr (fun t s => t.2 + s) 0

omit [DecidableEq R] in
/-- The list-level coefficient agrees with `MvPolynomial.coeff` — for *any* list (no sortedness). -/
lemma coeff_toPolyCore_listCoeff (D : MvDegrees nvars) (l : TL R nvars) :
    MvPolynomial.coeff (MvDegrees.toFinsupp D) (toPolyCore l) = listCoeff D l := by
  induction l with
  | nil => simp [toPolyCore, listCoeff]
  | cons hd tl ih =>
    obtain ⟨i, a⟩ := hd
    rw [toPolyCore_cons, MvPolynomial.coeff_add, MvPolynomial.coeff_monomial, ih]
    by_cases h : i = D
    · subst h; simp [listCoeff]
    · rw [if_neg (fun he => h (toFinsupp_inj.mp he))]
      simp [listCoeff, h]

/-- Boolean test: some monomial appearing in either list has different coefficients. -/
def polyNeBool (l₁ l₂ : TL R nvars) : Bool :=
  (l₁ ++ l₂).any (fun t => decide (listCoeff t.1 l₁ ≠ listCoeff t.1 l₂))

/-- Soundness for `≠` goals: a witnessing coefficient difference (decided in the kernel). -/
theorem ne_of_core {p q : MvPolynomial (Fin nvars) R} (l₁ l₂ : TL R nvars)
    (h₁ : toPolyCore l₁ = p) (h₂ : toPolyCore l₂ = q) (h : polyNeBool l₁ l₂ = true) : p ≠ q := by
  subst h₁ h₂
  obtain ⟨t, _, ht⟩ := List.any_eq_true.mp h
  intro he
  exact (of_decide_eq_true ht)
    (by rw [← coeff_toPolyCore_listCoeff, ← coeff_toPolyCore_listCoeff, he])


end MvSparsePoly.Kernel

public meta section

/-! ## The axiom-free tactic -/

open Lean Elab Tactic Meta MvSparsePoly.Kernel

namespace MvSparsePoly.Kernel

/-- Translate a `MvPolynomial (Fin n) R` expression into a kernel-reducible normal-form term list
`TL R n`, built from the structural ops `kAdd/kMul/kPow/kNeg/kSub` and the leaf term lists
`(X i).terms`, `(C r).terms`, `(1).terms`. -/
partial def reifyK (R n : Expr) (e : Expr) : MetaM Expr := do
  let leafTerms (p : Expr) : MetaM Expr := mkAppM ``MvSparsePoly.terms #[p]
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => mkAppM ``kAdd #[← reifyK R n a, ← reifyK R n b]
  | (``HMul.hMul, #[_, _, _, _, a, b]) => mkAppM ``kMul #[← reifyK R n a, ← reifyK R n b]
  | (``HSub.hSub, #[_, _, _, _, a, b]) => mkAppM ``kSub #[← reifyK R n a, ← reifyK R n b]
  | (``HPow.hPow, #[_, _, _, _, a, k]) => mkAppM ``kPow #[← reifyK R n a, k]
  | (``Neg.neg, #[_, _, a])            => mkAppM ``kNeg #[← reifyK R n a]
  | (``MvPolynomial.X, #[_, _, _, i])  =>
      leafTerms (← mkAppOptM ``MvSparsePoly.X #[n, R, none, none, i])
  | (``DFunLike.coe, #[_, _, _, _, f, c]) =>
      match f.getAppFnArgs with
      | (``MvPolynomial.C, _) => leafTerms (← mkAppOptM ``MvSparsePoly.C #[n, R, none, none, c])
      | _ => throwError "mv_decide: cannot reify {e}"
  | (``OfNat.ofNat, #[_, lit, _]) =>   -- numeral `m` ↦ `(C (m : R)).terms`  (bridge: `map_ofNat`)
      let cm ← mkAppOptM ``OfNat.ofNat #[R, lit, none]
      leafTerms (← mkAppOptM ``MvSparsePoly.C #[n, R, none, none, cm])
  | _ => throwError "mv_decide: cannot reify {e} into a term list"

end MvSparsePoly.Kernel

/-- The bridge simp set: the `@[simp]` homomorphism lemmas that rewrite `toPolyCore (reified)` back
into the original `MvPolynomial`. -/
def bridgeSimpK : MetaM Simp.Context := do
  let lemmas := #[``MvSparsePoly.Kernel.toPolyCore_kAdd, ``MvSparsePoly.Kernel.toPolyCore_kMul,
    ``MvSparsePoly.Kernel.toPolyCore_kSub, ``MvSparsePoly.Kernel.toPolyCore_kNeg,
    ``MvSparsePoly.Kernel.toPolyCore_kPow, ``MvSparsePoly.Kernel.toPolyCore_X_terms,
    ``MvSparsePoly.Kernel.toPolyCore_C_terms, ``MvSparsePoly.Kernel.toPolyCore_one_terms,
    ``MvSparsePoly.Kernel.toPolyCore_zero_terms, ``map_ofNat, ``map_one, ``map_zero]
  let mut s : SimpTheorems := {}
  for l in lemmas do s ← s.addConst l
  Simp.mkContext {} (simpTheorems := #[s]) (congrTheorems := ← getSimpCongrTheorems)

/-- Prove a `MvPolynomial` **equality or inequality** by reflecting onto kernel-reducible
normal-form term lists and closing with kernel `decide +kernel` — **axiom-free** (no
`native_decide`/compiler
trust). Practical for small/medium goals; the kernel interpreter is the bottleneck. -/
elab "mv_decide" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← whnfR (← g.getType)
  let (isNeg, p, q) ←
    if let some (_, a, b) := tgt.eq? then pure (false, a, b)
    else if let some inner := tgt.not? then
      if let some (_, a, b) := (← whnfR inner).eq? then pure (true, a, b)
      else throwError "mv_decide: goal is not an (in)equality of MvPolynomials"
    else throwError "mv_decide: goal is not an (in)equality of MvPolynomials"
  let (``MvPolynomial, #[σ, R, _]) := (← inferType p).getAppFnArgs
    | throwError "mv_decide: goal type is not MvPolynomial (Fin n) R"
  let n := (← whnfR σ).appArg!
  let l₁ ← reifyK R n p
  let l₂ ← reifyK R n q
  -- bridge proofs `toPolyCore lᵢ = p/q`
  let mkBridge (l orig : Expr) : MetaM Expr := do
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``MvSparsePoly.toPolyCore #[l]) orig)
    let (res, _) ← simpGoal m.mvarId! (← bridgeSimpK)
    if let some (_, m2) := res then m2.refl
    instantiateMVars m
  let hp ← mkBridge l₁ p
  let hq ← mkBridge l₂ q
  let lem := if isNeg then ``ne_of_core else ``eq_of_core
  let partialPf ← mkAppM lem #[l₁, l₂, hp, hq]
  let coreTy := (← inferType partialPf).bindingDomain!
  let mCore ← mkFreshExprSyntheticOpaqueMVar coreTy
  g.assign (.app partialPf mCore)
  replaceMainGoal [mCore.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- `mv_compute` is a synonym for the axiom-free `mv_decide` (kept for the name; both are kernel,
no `native_decide`). -/
macro "mv_compute" : tactic => `(tactic| mv_decide)


attribute [nolint defsWithUnderscore] tacticMv_decide tacticMv_compute
