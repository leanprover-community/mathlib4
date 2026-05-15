import Mathlib.Tactic.ToFun
import Mathlib.Analysis.Normed.Ring.Basic

variable {R : Type*}

/-
@[to_fun baz] -- should generate Foo.baz
def Foo.bar (f g : R → R) : f * g = g * f := sorry

@[to_fun Bars.baz] -- should generate Foo.Bars.baz
def Foo.Bar.baz (f g : R → R) : f * g = g * f := sorry

@[to_fun Baz.Bars.baz] -- should generate Baz.Bars.baz
def Foo.Bar.baz' (f g : R → R) : f * g = g * f := sorry

-- specifying more components than the original lemma is fine
-- TODO: does to_additive have an analogous test? if not, add it!
@[to_fun Bar.Bars.Bazzz.baz] -- should generate Bar.Bars.Bazzz.baz
def Foo.Bar.baz'' (f g : R → R) : f * g = g * f := sorry
-/

@[to_fun]
theorem Function.mul_comm (f g : ℝ → ℝ) : f * g = g * f := _root_.mul_comm f g

/-- info: Function.fun_mul_comm (f g : ℝ → ℝ) : (fun i => f i * g i) = fun i => g i * f i -/
#guard_msgs in
#check Function.fun_mul_comm

/-- Look I am the doc-string of `foo`. -/
@[to_fun]
theorem foo : (1 : Nat → Nat) = 1 := rfl

open Lean in
/--
info: Eta-expanded form of `foo`

---

Look I am the doc-string of `foo`.
-/
#guard_msgs in
run_meta
  let some doc  ← findDocString? (← getEnv) ``fun_foo | throwError "no docstring found"
  logInfo doc


-- Test that it also works when the generated proof is not a `rfl` proof:

@[to_additive (attr := push ← high)]
lemma Pi.mul_def' {ι : Type*} {M : ι → Type*} [∀ i, Mul (M i)] (f g : ∀ i, M i) :
    f * g = fun i ↦ f i * g i := (rfl)

@[to_fun]
theorem Function.mul_comm' (f g : ℝ → ℝ) : f * g = g * f := _root_.mul_comm f g

/-- info: Function.fun_mul_comm' (f g : ℝ → ℝ) : (fun i => f i * g i) = fun i => g i * f i -/
#guard_msgs in
#check Function.fun_mul_comm'
