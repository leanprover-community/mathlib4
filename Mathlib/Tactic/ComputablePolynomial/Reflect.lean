/-
Copyright (c) 2026 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.Tactic.ComputablePolynomial.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Axiom-free reflection for **univariate** `Polynomial R`

`poly_decide` (and its synonym `poly_compute`)
prove equalities and inequalities of Mathlib's noncomputable `Polynomial R` by reflecting onto
kernel-reducible normal-form coefficient lists (`List (ℕ × R)`), proving each operation correct
against the semantics `toPolyCore`, and closing with kernel `decide +kernel` —
**no `native_decide`**.

The univariate case is cleaner than the multivariate one: an exponent is a single `ℕ`, so product
exponents are `ℕ` addition (which the kernel reduces) — there is no `Array.zipWith` obstacle, hence
no need for the `addDegK` workaround. Full ring identities (`+`, `-`, `*`, `^`) decide axiom-free.

Trade-off (as always for kernel reflection): `decide +kernel` runs in the kernel interpreter, so it
is for small/medium goals.
-/

@[expose] public section

open Lean Elab Tactic Meta

namespace SparsePoly.Kernel

open SparsePoly

variable {R : Type} [CommRing R] [DecidableEq R]

/-- A raw coefficient list (the data of a `SparsePoly`, without the sorted/nonzero proofs). -/
abbrev TL (R : Type) := List (ℕ × R)

/-- Structural insert-merge into a descending-sorted coefficient list (kernel-reducible). -/
def insertK (t : ℕ × R) : TL R → TL R
  | [] => [t]
  | (j, b) :: rest =>
    match compare t.1 j with
    | .gt => t :: (j, b) :: rest
    | .eq => (j, t.2 + b) :: rest
    | .lt => (j, b) :: insertK t rest

/-- Structural (kernel-reducible) addition of raw coefficient lists. -/
def kAdd (a b : TL R) : TL R := a.foldr insertK b
/-- Structural (kernel-reducible) negation of a raw coefficient list. -/
def kNeg (a : TL R) : TL R := a.map (fun t => (t.1, -t.2))
/-- Structural (kernel-reducible) subtraction of raw coefficient lists. -/
def kSub (a b : TL R) : TL R := kAdd a (kNeg b)
/-- Structural (kernel-reducible) multiplication of raw coefficient lists. -/
def kMul (a b : TL R) : TL R :=
  a.foldr (fun t acc => kAdd (b.flatMap (fun s => [(t.1 + s.1, t.2 * s.2)])) acc) []
/-- Structural (kernel-reducible) power of a raw coefficient list. -/
def kPow (a : TL R) : ℕ → TL R
  | 0 => (1 : SparsePoly R).coeffs
  | k + 1 => kMul a (kPow a k)

/-! ### Correctness with respect to `toPolyCore` -/

omit [DecidableEq R] in
@[simp] lemma toPolyCore_cons (t : ℕ × R) (l : TL R) :
    toPolyCore (t :: l) = Polynomial.C t.2 * Polynomial.X ^ t.1 + toPolyCore l := rfl

omit [DecidableEq R] in
lemma toPolyCore_insertK (i : ℕ) (c : R) (l : TL R) :
    toPolyCore (insertK (i, c) l) = Polynomial.C c * Polynomial.X ^ i + toPolyCore l := by
  induction l with
  | nil => simp [insertK, toPolyCore]
  | cons hd tl ih =>
    obtain ⟨j, b⟩ := hd
    rw [insertK]
    rcases hc : compare i j with _ | _ | _
    · simp only [toPolyCore_cons, ih]; abel
    · obtain rfl := compare_eq_iff_eq.mp hc
      simp only [toPolyCore_cons]
      rw [map_add, add_mul]; abel
    · simp only [toPolyCore_cons]

omit [DecidableEq R] in
@[simp] lemma toPolyCore_kAdd (a b : TL R) :
    toPolyCore (kAdd a b) = toPolyCore a + toPolyCore b := by
  induction a with
  | nil => simp [kAdd, toPolyCore]
  | cons hd tl ih =>
    obtain ⟨i, c⟩ := hd
    rw [kAdd, List.foldr_cons, ← kAdd, toPolyCore_insertK, ih, toPolyCore_cons, add_assoc]

omit [DecidableEq R] in
@[simp] lemma toPolyCore_kNeg (a : TL R) : toPolyCore (kNeg a) = - toPolyCore a := by
  change toPolyCore (a.map (fun t => (t.1, -t.2))) = - toPolyCore a
  induction a with
  | nil => simp [toPolyCore]
  | cons hd tl ih =>
    obtain ⟨i, c⟩ := hd
    simp only [List.map_cons, toPolyCore_cons, ih, map_neg, neg_mul]
    abel

omit [DecidableEq R] in
@[simp] lemma toPolyCore_kSub (a b : TL R) :
    toPolyCore (kSub a b) = toPolyCore a - toPolyCore b := by
  rw [kSub, toPolyCore_kAdd, toPolyCore_kNeg, sub_eq_add_neg]

omit [DecidableEq R] in
@[simp] lemma toPolyCore_kMul (a b : TL R) :
    toPolyCore (kMul a b) = toPolyCore a * toPolyCore b := by
  induction a with
  | nil => simp [kMul, toPolyCore]
  | cons hd tl ih =>
    obtain ⟨i, c⟩ := hd
    rw [kMul, List.foldr_cons, ← kMul, toPolyCore_kAdd, ih, toPolyCore_mul_y, toPolyCore_cons,
      add_mul]

@[simp] lemma toPolyCore_kPow (a : TL R) (k : ℕ) :
    toPolyCore (kPow a k) = (toPolyCore a) ^ k := by
  induction k with
  | zero => rw [kPow, pow_zero]; exact toPoly_one
  | succ m ih => rw [kPow, toPolyCore_kMul, ih, pow_succ, mul_comm]

-- Leaf bridges: `toPoly = toPolyCore ∘ coeffs`, so these are the existing homomorphism lemmas.
@[simp] lemma toPolyCore_X_coeffs : toPolyCore (X : SparsePoly R).coeffs = Polynomial.X := toPoly_X
@[simp] lemma toPolyCore_C_coeffs (r : R) :
    toPolyCore (C r : SparsePoly R).coeffs = Polynomial.C r := toPoly_C r
@[simp] lemma toPolyCore_one_coeffs : toPolyCore (1 : SparsePoly R).coeffs = 1 := toPoly_one
omit [DecidableEq R] in
@[simp] lemma toPolyCore_zero_coeffs : toPolyCore (0 : SparsePoly R).coeffs = 0 := toPoly_zero

/-- Soundness for `=` goals (compares normal forms after dropping zero coefficients). -/
theorem eq_of_core {p q : Polynomial R} (l₁ l₂ : TL R)
    (h₁ : toPolyCore l₁ = p) (h₂ : toPolyCore l₂ = q)
    (h : l₁.filter (·.2 ≠ 0) = l₂.filter (·.2 ≠ 0)) : p = q := by
  rw [← h₁, ← h₂, ← toPolyCore_filter_nonzero l₁, ← toPolyCore_filter_nonzero l₂, h]

/-! ### Axiom-free `≠` (a differing coefficient witnesses inequality — no canonical-form needed) -/

/-- Coefficient of degree `D` read directly off a coefficient list. -/
def listCoeff (D : ℕ) (l : TL R) : R :=
  (l.filter (fun t => t.1 = D)).foldr (fun t s => t.2 + s) 0

omit [DecidableEq R] in
/-- The list-level coefficient agrees with `Polynomial.coeff` — for *any* list (no sortedness). -/
lemma coeff_toPolyCore_listCoeff (D : ℕ) (l : TL R) :
    (toPolyCore l).coeff D = listCoeff D l := by
  induction l with
  | nil => simp [toPolyCore, listCoeff]
  | cons hd tl ih =>
    obtain ⟨i, a⟩ := hd
    rw [toPolyCore_cons, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ih]
    by_cases h : i = D
    · subst h; simp [listCoeff]
    · have h' : D ≠ i := Ne.symm h
      simp [listCoeff, h, h']

/-- Boolean test: some degree appearing in either list has different coefficients. -/
def polyNeBool (l₁ l₂ : TL R) : Bool :=
  (l₁ ++ l₂).any (fun t => decide (listCoeff t.1 l₁ ≠ listCoeff t.1 l₂))

/-- Soundness for `≠` goals: a witnessing coefficient difference (decided in the kernel). -/
theorem ne_of_core {p q : Polynomial R} (l₁ l₂ : TL R)
    (h₁ : toPolyCore l₁ = p) (h₂ : toPolyCore l₂ = q) (h : polyNeBool l₁ l₂ = true) : p ≠ q := by
  subst h₁ h₂
  obtain ⟨t, _, ht⟩ := List.any_eq_true.mp h
  intro he
  exact (of_decide_eq_true ht)
    (by rw [← coeff_toPolyCore_listCoeff, ← coeff_toPolyCore_listCoeff, he])

/-! ### Axiom-free divisibility via kernel-reducible long division -/

/-- Kernel-reducible univariate long division of coefficient lists (structural on `fuel`). Returns
`(quotient, remainder)`. Needs `Div R`; the division *identity* `q = p·quo + rem` holds for any `R`
(`toPolyCore_divModK`), so it is sound regardless of whether `p`'s leading coefficient divides. -/
def divModK [Div R] : ℕ → TL R → TL R → TL R × TL R
  | 0, q, _ => ([], q)
  | fuel + 1, q, p =>
    match q, p with
    | [], _ => ([], [])
    | _, [] => ([], q)
    | (dq, cq) :: qt, (dp, cp) :: pt =>
      if cq = 0 then divModK fuel qt ((dp, cp) :: pt)   -- drop a spurious zero leading term
      else if dq < dp then ([], (dq, cq) :: qt)
      else
        let term : ℕ × R := (dq - dp, cq / cp)
        let r := divModK fuel (kSub ((dq, cq) :: qt) (kMul [term] ((dp, cp) :: pt)))
          ((dp, cp) :: pt)
        (term :: r.1, r.2)

omit [DecidableEq R] in
/-- `toPolyCore` splits a cons into the head monomial plus the tail
(head kept as `toPolyCore [t]`). -/
lemma toPolyCore_cons_split (t : ℕ × R) (l : TL R) :
    toPolyCore (t :: l) = toPolyCore [t] + toPolyCore l := by simp [toPolyCore]

/-- The division identity, through `toPolyCore` (holds for *any* fuel and `R`). -/
lemma toPolyCore_divModK [Div R] : ∀ (n : ℕ) (q p : TL R),
    toPolyCore q = toPolyCore p * toPolyCore (divModK n q p).1 + toPolyCore (divModK n q p).2
  | 0, q, p => by simp [divModK, toPolyCore]
  | n + 1, q, p => by
    match q, p with
    | [], _ => simp [divModK, toPolyCore]
    | _ :: _, [] => simp [divModK, toPolyCore]
    | (dq, cq) :: qt, (dp, cp) :: pt =>
      by_cases hz : cq = 0
      · -- a spurious zero leading term is dropped; `C 0 * X^dq = 0`, so `toPolyCore` is unchanged
        simp only [divModK, toPolyCore_cons, hz, map_zero, zero_mul, zero_add]
        exact toPolyCore_divModK n qt ((dp, cp) :: pt)
      · by_cases h : dq < dp
        · simp [divModK, if_neg hz, h, toPolyCore]
        · simp only [divModK, if_neg hz, if_neg h]
          have ih := toPolyCore_divModK n
            (kSub ((dq, cq) :: qt) (kMul [(dq - dp, cq / cp)] ((dp, cp) :: pt))) ((dp, cp) :: pt)
          rw [toPolyCore_kSub, toPolyCore_kMul] at ih
          -- keep `toPolyCore p` and `toPolyCore [term]` atomic; only split the *quotient* cons
          rw [toPolyCore_cons_split (dq - dp, cq / cp)]
          linear_combination ih

/-- Divisor with a self-computed fuel bound. Each step strictly lowers the working *degree*, but an
exact cancellation can leave a zero-coefficient head consumed by an extra drop step, so we allow up
to `2·(maxdeg) + length + 2` steps — comfortably above the worst case. -/
def divMod [Div R] (q p : TL R) : TL R × TL R :=
  divModK (2 * (q.map Prod.fst).foldr Nat.max 0 + q.length + 2) q p

/-- The division identity for `divMod`. -/
lemma toPolyCore_divMod [Div R] (q p : TL R) :
    toPolyCore q = toPolyCore p * toPolyCore (divMod q p).1 + toPolyCore (divMod q p).2 :=
  toPolyCore_divModK _ q p

/-- Soundness: if `divMod` leaves no nonzero remainder, `p ∣ q`. -/
theorem dvd_of_divMod [Div R] {p q : Polynomial R} (l_p l_q : TL R)
    (h_p : toPolyCore l_p = p) (h_q : toPolyCore l_q = q)
    (h : (divMod l_q l_p).2.filter (·.2 ≠ 0) = []) : p ∣ q := by
  refine ⟨toPolyCore (divMod l_q l_p).1, ?_⟩
  have hrem : toPolyCore (divMod l_q l_p).2 = 0 := by
    rw [← toPolyCore_filter_nonzero, h]; rfl
  rw [← h_q, ← h_p, toPolyCore_divMod l_q l_p, hrem, add_zero]

end SparsePoly.Kernel

public meta section

/-! ## The axiom-free tactic -/

namespace SparsePoly.Kernel

/-- Translate a `Polynomial R` expression into a kernel-reducible normal-form coefficient list. -/
partial def reifyK (R : Expr) (e : Expr) : MetaM Expr := do
  let leaf (p : Expr) : MetaM Expr := mkAppM ``SparsePoly.coeffs #[p]
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => mkAppM ``kAdd #[← reifyK R a, ← reifyK R b]
  | (``HMul.hMul, #[_, _, _, _, a, b]) => mkAppM ``kMul #[← reifyK R a, ← reifyK R b]
  | (``HSub.hSub, #[_, _, _, _, a, b]) => mkAppM ``kSub #[← reifyK R a, ← reifyK R b]
  | (``HPow.hPow, #[_, _, _, _, a, k]) => mkAppM ``kPow #[← reifyK R a, k]
  | (``Neg.neg, #[_, _, a])            => mkAppM ``kNeg #[← reifyK R a]
  | (``Polynomial.X, _)                => leaf (← mkAppOptM ``SparsePoly.X #[R, none, none])
  | (``DFunLike.coe, #[_, _, _, _, f, c]) =>
      match f.getAppFnArgs with
      | (``Polynomial.C, _) => leaf (← mkAppOptM ``SparsePoly.C #[R, none, none, c])
      | _ => throwError "poly_decide: cannot reify {e}"
  | (``OfNat.ofNat, #[_, lit, _]) =>   -- numeral `n` ↦ `(C (n : R)).coeffs`  (bridge: `map_ofNat`)
      leaf (← mkAppOptM ``SparsePoly.C #[R, none, none, ← mkAppOptM ``OfNat.ofNat #[R, lit, none]])
  | _ => throwError "poly_decide: cannot reify {e} into a coefficient list"

/-- The `simp` context of `toPolyCore`-homomorphism lemmas used to bridge a reified coefficient list
back to its original `Polynomial R` expression (used by `poly_decide` and related tactics). -/
def bridgeSimpK : MetaM Simp.Context := do
  let lemmas := #[``SparsePoly.Kernel.toPolyCore_kAdd, ``SparsePoly.Kernel.toPolyCore_kMul,
    ``SparsePoly.Kernel.toPolyCore_kSub, ``SparsePoly.Kernel.toPolyCore_kNeg,
    ``SparsePoly.Kernel.toPolyCore_kPow, ``SparsePoly.Kernel.toPolyCore_X_coeffs,
    ``SparsePoly.Kernel.toPolyCore_C_coeffs, ``SparsePoly.Kernel.toPolyCore_one_coeffs,
    ``SparsePoly.Kernel.toPolyCore_zero_coeffs, ``map_ofNat, ``map_one, ``map_zero]
  let mut s : SimpTheorems := {}
  for l in lemmas do s ← s.addConst l
  Simp.mkContext {} (simpTheorems := #[s]) (congrTheorems := ← getSimpCongrTheorems)

end SparsePoly.Kernel

/-- Prove a `Polynomial R` **equality or inequality** by reflecting onto kernel-reducible normal
forms and closing with kernel `decide +kernel` — **axiom-free**. -/
elab "poly_decide" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← whnfR (← g.getType)
  let (isNeg, p, q) ←
    if let some (_, a, b) := tgt.eq? then pure (false, a, b)
    else if let some inner := tgt.not? then
      if let some (_, a, b) := (← whnfR inner).eq? then pure (true, a, b)
      else throwError "poly_decide: goal is not an (in)equality of Polynomials"
    else throwError "poly_decide: goal is not an (in)equality of Polynomials"
  let (``Polynomial, #[R, _]) := (← inferType p).getAppFnArgs
    | throwError "poly_decide: goal type is not Polynomial R"
  let l₁ ← SparsePoly.Kernel.reifyK R p
  let l₂ ← SparsePoly.Kernel.reifyK R q
  let mkBridge (l orig : Expr) : MetaM Expr := do
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``SparsePoly.toPolyCore #[l]) orig)
    let (res, _) ← simpGoal m.mvarId! (← SparsePoly.Kernel.bridgeSimpK)
    if let some (_, m2) := res then m2.refl
    instantiateMVars m
  let hp ← mkBridge l₁ p
  let hq ← mkBridge l₂ q
  let lem := if isNeg then ``SparsePoly.Kernel.ne_of_core else ``SparsePoly.Kernel.eq_of_core
  let partialPf ← mkAppM lem #[l₁, l₂, hp, hq]
  let coreTy := (← inferType partialPf).bindingDomain!
  let mCore ← mkFreshExprSyntheticOpaqueMVar coreTy
  g.assign (.app partialPf mCore)
  replaceMainGoal [mCore.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- `poly_compute` is a synonym for the axiom-free `poly_decide`. -/
macro "poly_compute" : tactic => `(tactic| poly_decide)

attribute [nolint defsWithUnderscore] tacticPoly_decide tacticPoly_compute
