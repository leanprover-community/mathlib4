import Lean

structure Foo where
  type : Type u

universe u v w

variable (α : Type u) (β : Type v) (γ : Type w)

set_option trace.Meta.isLevelDefEq true in
set_option trace.Elab.step true in
set_option pp.all true in
-- set_option trace.Elab.struct true in
def foo : Foo where
  type := (α ⊕ β) ⊕ γ

set_option pp.all true in
#print foo -- foo.{u, v, w} (α : Type u) (β : Type v) (γ : Type w) : Foo.{max w v u}

set_option pp.all true in
set_option trace.Elab.struct true in
def bar : Foo where
  type := α ⊕ β ⊕ γ

set_option pp.universes true in
#check bar -- bar.{u, v, w} (α : Type u) (β : Type v) (γ : Type w) : Foo.{max (max w v) u}

open Lean Meta Elab Term

#check ConstantInfo

set_option pp.universes true in
open ConstantInfo Expr in
run_meta do
  let env ← getEnv
  if let some info := env.find? `foo then
    if let .defnInfo dv := info then
      let e := dv.value
      logInfo m!"{e}"
      let e ← lambdaTelescope e fun bns body => do
        let head := body.getAppFn
        if let .const c us := head then
          let newHead := Expr.const c (us.map fun u => u.normalize)
          let newBody := mkAppN newHead body.getAppArgs
          mkLambdaFVars bns newBody
        else return e
      logInfo m!"{e}"
  return ()
  -- let e := dv.value
  -- sorry
  -- IO.println e
