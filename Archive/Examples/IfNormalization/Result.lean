/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Archive.Examples.IfNormalization.Statement
import Mathlib.Data.List.AList
import Mathlib.Tactic.Recall

/-!
# A solution to the if normalization challenge in Lean.

See `Statement.lean` for background.
-/

macro "◾" : tactic => `(tactic| aesop)
macro "◾" : term => `(term| by aesop)

namespace IfExpr

/-!
We add some local simp lemmas so we can unfold the definitions of the normalization condition.
-/
attribute [local simp] normalized hasNestedIf hasConstantIf hasRedundantIf disjoint vars
  List.disjoint

attribute [local simp] apply_ite ite_eq_iff'

variable {b : Bool} {f : ℕ → Bool} {i : ℕ} {t e : IfExpr}

/-!
Simp lemmas for `eval`.
We don't want a `simp` lemma for `(ite i t e).eval` in general, only once we know the shape of `i`.
-/
@[simp] theorem eval_lit : (lit b).eval f = b := rfl
@[simp] theorem eval_var : (var i).eval f = f i := rfl
@[simp] theorem eval_ite_lit :
    (ite (.lit b) t e).eval f = bif b then t.eval f else e.eval f := rfl
@[simp] theorem eval_ite_var :
    (ite (.var i) t e).eval f = bif f i then t.eval f else e.eval f := rfl
@[simp] theorem eval_ite_ite {a b c d e : IfExpr} :
    (ite (ite a b c) d e).eval f = (ite a (ite b d e) (ite c d e)).eval f := by
  cases h : eval f a <;> simp_all [eval]

/-- Custom size function for if-expressions, used for proving termination. -/
@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1

/-- Normalizes the expression at the same time as assigning all variables in
`e` to the literal Booleans given by `l` -/
def normalize (l : AList (fun _ : ℕ => Bool)) :
    (e : IfExpr) → { e' : IfExpr //
        (∀ f, e'.eval f = e.eval (fun w => (l.lookup w).elim (f w) id))
        ∧ e'.normalized
        ∧ ∀ (v : ℕ), v ∈ vars e' → l.lookup v = none }
  | lit b => ⟨lit b, ◾⟩
  | var v =>
    match h : l.lookup v with
    | none => ⟨var v, ◾⟩
    | some b => ⟨lit b, ◾⟩
  | .ite (lit true)   t e => have t' := normalize l t; ⟨t'.1, ◾⟩
  | .ite (lit false)  t e => have e' := normalize l e; ⟨e'.1, ◾⟩
  | .ite (.ite a b c) t e => have i' := normalize l (.ite a (.ite b t e) (.ite c t e)); ⟨i'.1, ◾⟩
  | .ite (var v)      t e =>
    match h : l.lookup v with
    | none =>
      have ⟨t', ht₁, ht₂, ht₃⟩ := normalize (l.insert v true) t
      have ⟨e', he₁, he₂, he₃⟩ := normalize (l.insert v false) e
      ⟨if t' = e' then t' else .ite (var v) t' e', by
        refine ⟨fun f => ?_, ?_, fun w b => ?_⟩
        · -- eval = eval
          simp? says simp only [apply_ite, eval_ite_var, ite_eq_iff']
          cases hfv : f v
          · simp_all
            congr
            ext w
            by_cases w = v <;> ◾
          · simp [h, ht₁]
            congr
            ext w
            by_cases w = v <;> ◾
        · -- normalized
          have := ht₃ v
          have := he₃ v
          split <;> ◾
        · -- lookup = none
          have := ht₃ w
          have := he₃ w
          by_cases w = v <;> ◾⟩
    | some b =>
      have i' := normalize l (.ite (lit b) t e); ⟨i'.1, ◾⟩
  termination_by e => e.normSize

/-
We recall the statement of the if-normalization problem.

We want a function from if-expressions to if-expressions,
that outputs normalized if-expressions and preserves meaning.
-/
recall IfNormalization :=
  { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }

example : IfNormalization :=
  ⟨_, fun e => ⟨(IfExpr.normalize ∅ e).2.2.1, by simp [(IfExpr.normalize ∅ e).2.1]⟩⟩

end IfExpr
