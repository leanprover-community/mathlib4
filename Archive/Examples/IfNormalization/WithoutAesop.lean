/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Scott Morrison
-/
import Archive.Examples.IfNormalization.Statement
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Data.List.AList

/-!
# A variant of Chris Hughes' solution for the if normalization challenge.

In this variant we eschew the use of `aesop`, and instead write out the proofs.

(In order to avoid duplicated names with `Result.lean`,
we put primes on the declarations in the file.)
-/

set_option autoImplicit true

namespace IfExpr

attribute [local simp] eval normalized hasNestedIf hasConstantIf hasRedundantIf disjoint vars
  List.disjoint max_add_add_right max_mul_mul_left Nat.lt_add_one_iff le_add_of_le_right

theorem eval_ite_ite' :
    (ite (ite a b c) d e).eval f = (ite a (ite b d e) (ite c d e)).eval f := by
  cases h : eval f a <;> simp_all

/-- Custom size function for if-expressions, used for proving termination. -/
@[simp] def normSize' : IfExpr → ℕ
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize' i + max (normSize' t) (normSize' e) + 1

/-- Normalizes the expression at the same time as assigning all variables in
`e` to the literal booleans given by `l` -/
def normalize' (l : AList (fun _ : ℕ => Bool)) :
    (e : IfExpr) → { e' : IfExpr //
        (∀ f, e'.eval f = e.eval (fun w => (l.lookup w).elim (f w) (fun b => b)))
        ∧ e'.normalized
        ∧ ∀ (v : ℕ), v ∈ vars e' → l.lookup v = none }
  | lit b => ⟨lit b, by simp⟩
  | var v =>
    match h : l.lookup v with
    | none => ⟨var v, by simp_all⟩
    | some b => ⟨lit b, by simp_all⟩
  | .ite (lit true) t e =>
    have ⟨t', ht'⟩ := normalize' l t
    ⟨t', by simp_all⟩
  | .ite (lit false) t e =>
    have ⟨e', he'⟩ := normalize' l e
    ⟨e', by simp_all⟩
  | .ite (.ite a b c) d e =>
    have ⟨t', ht₁, ht₂⟩ := normalize' l (.ite a (.ite b d e) (.ite c d e))
    ⟨t', fun f => by rw [ht₁, eval_ite_ite'], ht₂⟩
  | .ite (var v) t e =>
    match h : l.lookup v with
    | none =>
      have ⟨t', ht₁, ht₂, ht₃⟩ := normalize' (l.insert v true) t
      have ⟨e', he₁, he₂, he₃⟩ := normalize' (l.insert v false) e
      ⟨if t' = e' then t' else .ite (var v) t' e', by
        refine ⟨fun f => ?_, ?_, fun w b => ?_⟩
        · simp only [eval, apply_ite, ite_eq_iff']
          cases hfv : f v
          · simp (config := {contextual := true}) only [cond_false, h, he₁]
            refine ⟨fun _ => ?_, fun _ => ?_⟩
            · congr
              ext w
              by_cases h : w = v
              · substs h
                simp_all
              · simp_all
            · congr
              ext w
              by_cases h : w = v
              · substs h
                simp_all
              · simp_all
          · simp only [cond_true, h, ht₁]
            refine ⟨fun _ => ?_, fun _ => ?_⟩
            · congr
              ext w
              by_cases h : w = v
              · substs h
                simp_all
              · simp_all
            · congr
              ext w
              by_cases h : w = v
              · substs h
                simp_all
              · simp_all
        · have := ht₃ v
          have := he₃ v
          simp_all? says simp_all only [Option.elim, normalized, Bool.and_eq_true,
              Bool.not_eq_true', AList.lookup_insert_eq_none, ne_eq, AList.lookup_insert, imp_false]
          obtain ⟨⟨⟨tn, tc⟩, tr⟩, td⟩ := ht₂
          split <;> rename_i h'
          · subst h'
            simp_all
          · simp_all? says simp_all only [hasNestedIf, Bool.or_self, hasConstantIf, and_self,
              hasRedundantIf, Bool.or_false, beq_eq_false_iff_ne, ne_eq, not_false_eq_true,
              disjoint, List.disjoint, decide_True, Bool.and_self]
        · have := ht₃ w
          have := he₃ w
          by_cases h : w = v
          · subst h; simp_all
          · simp_all? says simp_all only [Option.elim, normalized, Bool.and_eq_true,
              Bool.not_eq_true', AList.lookup_insert_eq_none, ne_eq, not_false_eq_true,
              AList.lookup_insert_ne, implies_true]
            obtain ⟨⟨⟨en, ec⟩, er⟩, ed⟩ := he₂
            split at b <;> rename_i h'
            · subst h'; simp_all
            · simp_all only [ne_eq, vars, List.singleton_append, List.cons_append,
                Bool.not_eq_true, List.mem_cons, List.mem_append, false_or]
              cases b <;> simp_all⟩
    | some b =>
      have ⟨e', he'⟩ := normalize' l (.ite (lit b) t e)
      ⟨e', by simp_all⟩
  termination_by e' => e'.normSize'

example : IfNormalization :=
  ⟨fun e => (normalize' ∅ e).1,
   fun e => ⟨(normalize' ∅ e).2.2.1, by simp [(normalize' ∅ e).2.1]⟩⟩
