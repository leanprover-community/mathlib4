import Mathlib

open Lean Meta Elab Tactic

def specializeExpr (pf : Expr) (type? : Option Expr) : MetaM Expr :=
  return pf

elab "specialize_of% " t:term " with " p:term : term => do
  let e ← Term.elabTerm t none
  let ty ← inferType e
  forallTelescope ty fun fvars body => do
    let appE : Expr := mkAppN e fvars
    let mvar ← mkFreshExprMVar none
    let tp : Expr := .forallE `x body mvar .default
    let pE ← Term.elabTerm p tp
    let congred : Expr := mkApp pE appE
    mkLambdaFVars fvars congred

structure Foo where
  foo : Nat
  hfoo : foo = 3

def specialFoo : Foo := ⟨3, rfl⟩

lemma Foo.id (x : Foo) : specialFoo = x := by
  sorry

example (x : Foo) : specialFoo.foo = x.foo :=
  congr($(Foo.id x).foo)

example (x : Foo) : specialFoo.foo = x.foo := by
  rw [specialize_of% Foo.id with
    fun myspecialname ↦ congr($(myspecialname).foo)]
