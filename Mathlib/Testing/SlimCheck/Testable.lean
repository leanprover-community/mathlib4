/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/

import Mathlib.Testing.SlimCheck.Sampleable
import Lean

/-!
# `Testable` Class
Testable propositions have a procedure that can generate counter-examples
together with a proof that they invalidate the proposition.

This is a port of the Haskell QuickCheck library.

## Creating Customized Instances
The type classes `Testable`, `Sampleable` and `Shrinkable` are the
means by which `SlimCheck` creates samples and tests them. For instance,
the proposition `∀ i j : ℕ, i ≤ j` has a `Testable` instance because `ℕ`
is sampleable and `i ≤ j` is decidable. Once `SlimCheck` finds the `Testable`
instance, it can start using the instance to repeatedly creating samples
and checking whether they satisfy the property. Once it has found a
counter-example it will then use a `Shrinkable` instance to reduce the
example. This allows the user to create new instances and apply
`SlimCheck` to new situations.

### What do I do if I'm testing a property about my newly defined type?
Let us consider a type made for a new formalization:
```lean
structure MyType where
  x : ℕ
  y : ℕ
  h : x ≤ y
  deriving Repr
```
How do we test a property about `MyType`? For instance, let us consider
`Testable.check $ ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y`. Writing this
property as is will give us an error because we do not have an instance
of `Sampleable MyType`. We can define one as follows:
```lean
instance : Sampleable MyType where
  sample := do
    let x ← Sampleable.sample Nat
    let xyDiff ← Sampleable.sample Nat
    pure $ ⟨x, x + xyDiff, sorrere
  shrink := λ ⟨x,y,h⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (λ ⟨⟨fst, snd⟩, ha⟩ => ⟨⟨fst, fst + snd, sorry⟩, sorry⟩)
```
Again, we take advantage of the fact that other types have useful
`Shrinkable` implementations, in this case `Prod`. Note that the second
proof is heavily based on `SizeOf` since its used for termination so
the first step you want to take is almost always to `simp` in order to
get through both `SizeOf` abstraction by `SlimCheck` and the auto generated
`SizeOf` instances.

## Main definitions
  * `Testable` class
  * `Testable.check`: a way to test a proposition using random examples

## Tags

random testing

## References
  * https://hackage.haskell.org/package/QuickCheck
-/

namespace SlimCheck

variable {β : α → Prop}

/-- Result of trying to disprove `p`
The constructors are:
  *  `success : (PSum Unit p) → TestResult p`
     succeed when we find another example satisfying `p`
     In `success h`, `h` is an optional proof of the proposition.
     Without the proof, all we know is that we found one example
     where `p` holds. With a proof, the one test was sufficient to
     prove that `p` holds and we do not need to keep finding examples.
   * `gaveUp : ℕ → TestResult p`
     give up when a well-formed example cannot be generated.
     `gaveUp n` tells us that `n` invalid examples were tried.
     Above 100, we give up on the proposition and report that we
     did not find a way to properly test it.
   * `failure : ¬ p → (List String) → ℕ → TestResult p`
     a counter-example to `p`; the strings specify values for the relevant variables.
     `failure h vs n` also carries a proof that `p` does not hold. This way, we can
     guarantee that there will be no false positive. The last component, `n`,
     is the number of times that the counter-example was shrunk.
-/
inductive TestResult (p : Prop) where
  | success : PSum Unit p → TestResult p
  | gaveUp : Nat → TestResult p
  | failure : ¬ p → List String → Nat → TestResult p
  deriving Inhabited

/-- Configuration for testing a property. -/
structure Configuration where
  numInst : Nat := 100
  maxSize : Nat := 100
  numRetries : Nat := 10
  traceDiscarded : Bool := false
  traceSuccesses : Bool := false
  traceShrink : Bool := false
  traceShrinkCandidates : Bool := false
  randomSeed : Option Nat := none
  quiet : Bool := false
  deriving Inhabited

/--
`PrintableProp p` allows one to print a proposition so that
`SlimCheck` can indicate how values relate to each other.
It's basically a poor man's delaborator.
-/
class PrintableProp (p : Prop) where
  printProp : String

export PrintableProp (printProp)

instance (priority := low) : PrintableProp p where
  printProp := "⋯"

/-- `Testable p` uses random examples to try to disprove `p`. -/
class Testable (p : Prop) where
  run {} (cfg : Configuration) (minimize : Bool) : Gen (TestResult p)

abbrev NamedBinder (n : String) (p : Prop) : Prop := p

namespace TestResult

def toString : TestResult p → String
| success (PSum.inl _) => "success (no proof)"
| success (PSum.inr _) => "success (proof)"
| gaveUp n => s!"gave {n} times"
| failure _ counters n => s!"failed {counters}"

instance : ToString (TestResult p) := ⟨toString⟩

/-- Applicative combinator proof carrying test results. -/
def combine {p q : Prop} : PSum Unit (p → q) → PSum Unit p → PSum Unit q
| PSum.inr f, PSum.inr proof => PSum.inr $ f proof
| _, _ => PSum.inl ()

/-- Combine the test result for properties `p` and `q` to create a test for their conjunction. -/
def and : TestResult p → TestResult q → TestResult (p ∧ q)
| failure h xs n, _ => failure (λ h2 => h h2.left) xs n
| _, failure h xs n => failure (λ h2 => h h2.right) xs n
| success h1, success h2 => success $ combine (combine (PSum.inr And.intro) h1) h2
| gaveUp n, gaveUp m => gaveUp $ n + m
| gaveUp n, _ => gaveUp n
| _, gaveUp n => gaveUp n

/-- Combine the test result for properties `p` and `q` to create a test for their disjunction. -/
def or : TestResult p → TestResult q → TestResult (p ∨ q)
| failure h1 xs n, failure h2 ys m =>
  let h3 := λ h =>
    match h with
    | Or.inl h3 => h1 h3
    | Or.inr h3 => h2 h3
  failure h3 (xs ++ ys) (n + m)
| success h, _ => success $ combine (PSum.inr Or.inl) h
| _, success h => success $ combine (PSum.inr Or.inr) h
| gaveUp n, gaveUp m => gaveUp $ n + m
| gaveUp n, _ => gaveUp n
| _, gaveUp n => gaveUp n

/-- If `q → p`, then `¬ p → ¬ q` which means that testing `p` can allow us
to find counter-examples to `q`. -/
def imp (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q :=
  match r with
  | failure h2 xs n => failure (mt h h2) xs n
  | success h2 => success $ combine p h2
  | gaveUp n => gaveUp n

/-- Test `q` by testing `p` and proving the equivalence between the two. -/
def iff (h : q ↔ p) (r : TestResult p) : TestResult q :=
  imp h.mp r (PSum.inr h.mpr)

/-- When we assign a value to a universally quantified variable,
we record that value using this function so that our counter-examples
can be informative. -/
def addInfo (x : String) (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q :=
  if let failure h2 xs n := r then
    failure (mt h h2) (x :: xs) n
  else
    imp h r p

/-- Add some formatting to the information recorded by `addInfo`. -/
def addVarInfo [Repr γ] (var : String) (x : γ) (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q  :=
  addInfo s!"{var} := {repr x}" h r p

def isFailure : TestResult p → Bool
| failure _ _ _ => true
| _ => false

end TestResult

namespace Configuration

/-- A configuration with all the trace options enabled, useful for debugging. -/
def verbose : Configuration where
  traceDiscarded := true
  traceSuccesses := true
  traceShrink := true
  traceShrinkCandidates := true

end Configuration

namespace Testable

open TestResult

/-- A `dbgTrace` with special formatting -/
def slimTrace [Pure m] (s : String) : m PUnit := dbgTrace s!"[SlimCheck: {s}]" (λ _ => pure ())

instance andTestable [Testable p] [Testable q] : Testable (p ∧ q) where
  run := λ cfg min => do
    let xp ← run p cfg min 
    let xq ← run q cfg min
    pure $ and xp xq

instance orTestable [Testable p] [Testable q] : Testable (p ∨ q) where
  run := λ cfg min => do
    let xp ← run p cfg min 
    -- As a little performance optimization we can just not run the second
    -- test if the first succeeds
    match xp with
    | success (PSum.inl h) => pure $ success (PSum.inl h)
    | success (PSum.inr h) => pure $ success (PSum.inr $ Or.inl h)
    | _ =>
      let xq ← run q cfg min
      pure $ or xp xq

instance iffTestable [Testable ((p ∧ q) ∨ (¬ p ∧ ¬ q))] : Testable (p ↔ q) where
  run := λ cfg min => do
    let h ← run ((p ∧ q) ∨ (¬ p ∧ ¬ q)) cfg min
    pure $ iff iff_iff_and_or_not_and_not h 

instance decGuardTestable [PrintableProp p] [Decidable p] {β : p → Prop} [∀ h, Testable (β h)] : Testable (NamedBinder var $ ∀ h, β h) where
  run := λ cfg min => do
    if h : p then
      let res := (run (β h) cfg min)
      match printProp p with
      | none => (λ r => imp (· $ h) r (PSum.inr $ λ q _ => q)) <$> res
      | some s => (λ r => addInfo s!"guard: {s}" (· $ h) r (PSum.inr $ λ q _ => q)) <$> res
    else if cfg.traceDiscarded || cfg.traceSuccesses then
      let res := (λ _ => pure $ gaveUp 1)
      match printProp p with
      | none => slimTrace "discard: Guard does not hold"; res
      | some s => slimTrace s!"discard: Guard {s} does not hold"; res
    else
      pure $ gaveUp 1

instance forallTypesTestable {f : Type → Prop} [Testable (f Int)] : Testable (NamedBinder var $ ∀ x, f x) where
  run := λ cfg min => do
    let r ← run (f Int) cfg min
    pure $ addVarInfo var "ℤ" (· $ Int) r

/-- Test proposition `p` by randomly selecting one of the provided
testable instances. -/
def combine (ts : List (Testable p)) (h : 0 < ts.length) : Testable p := ⟨λ cfg min => do
  let f := (@Testable.run _ · cfg min)
  have : 0 < List.length (List.map f ts) := by
    rw [List.length_map]
    exact h
  Gen.oneOf (ts.map f) this⟩
/--
Format the counter-examples found in a test failure.
-/
def formatFailure (s : String) (xs : List String) (n : Nat) : String :=
  let counter := String.intercalate "\n" xs
  let parts := [
    "\n===================",
    s,
    counter,
    s!"({n} shrinks)",
    "-------------------"
  ]
  String.intercalate "\n" parts

/--
Increase the number of shrinking steps in a test result.
-/
def addShrinks (n : Nat) : TestResult p → TestResult p
| TestResult.failure p xs m => TestResult.failure p xs (m + n)
| p => p

/-- Shrink a counter-example `x` by using `Shrinkable.shrink x`, picking the first
candidate that falsifies a property and recursively shrinking that one.
The process is guaranteed to terminate because `shrink x` produces
a proof that all the values it produces are smaller (according to `SizeOf`)
than `x`. -/
def minimizeAux [SampleableExt α] [∀ x, Testable (β x)] (cfg : Configuration) (var : String)
    (x : SampleableExt.proxy α) (n : Nat) : OptionT Gen (Σ x, TestResult (β (SampleableExt.interp x))) := do
  let candidates := SampleableExt.shrink.shrink x
  if cfg.traceShrinkCandidates then
    slimTrace s!"Candidates for {var} := {repr x}:\n  {repr candidates}"
  for ⟨candidate, h⟩ in candidates do
    if cfg.traceShrinkCandidates then
      slimTrace s!"Trying {var} := {repr candidate}"
    let res ← OptionT.lift $ Testable.run (β (SampleableExt.interp candidate)) cfg true
    if res.isFailure then
      if cfg.traceShrink then
        slimTrace s!"{var} shrunk to {repr candidate} from {repr x}"
      let currentStep := OptionT.lift $ pure $ Sigma.mk candidate (addShrinks (n + 1) res)
      let nextStep := minimizeAux cfg var candidate (n + 1)
      return ←(nextStep <|> currentStep)
  if cfg.traceShrink then
    slimTrace s!"No shrinking possible for {var} := {repr x}"
  failure

/-- Once a property fails to hold on an example, look for smaller counter-examples
to show the user. -/
def minimize [SampleableExt α] [∀ x, Testable (β x)] (cfg : Configuration) (var : String)
    (x : SampleableExt.proxy α) (r : TestResult (β $ SampleableExt.interp x)) : Gen (Σ x, TestResult (β $ SampleableExt.interp x)) := do
  if cfg.traceShrink then
     slimTrace "Shrink"
     slimTrace s!"Attempting to shrink {var} := {repr x}"
  let res ← OptionT.run $ minimizeAux cfg var x 0
  pure $ res.getD ⟨x, r⟩

/-- Test a universal property by creating a sample of the right type and instantiating the
bound variable with it. -/
instance varTestable [SampleableExt α] [∀ x, Testable (β x)] : Testable (NamedBinder var $ ∀ x : α, β x) where
  run := λ cfg min => do
    let x ← SampleableExt.sample α
    if cfg.traceSuccesses || cfg.traceDiscarded then
      slimTrace s!"{var} := {repr x}"
    let r ← Testable.run (β $ SampleableExt.interp x) cfg false
    let ⟨finalX, finalR⟩ ←
      if isFailure r then
        if cfg.traceSuccesses then
          slimTrace s!"{var} := {repr x} is a failure"
        if min then
          minimize cfg var x r
        else
          pure $ ⟨x, r⟩
      else 
        pure $ ⟨x, r⟩
    pure $ addVarInfo var finalX (· $ SampleableExt.interp finalX) finalR

/-- Test a universal property about propositions -/
instance propVarTestable {β : Prop → Prop} [∀ b : Bool, Testable (β b)] : Testable (NamedBinder var $ ∀ p : Prop, β p) where
  run := λ cfg min =>
    imp (λ h (b : Bool) => h b) <$> Testable.run (NamedBinder var $ ∀ b : Bool, β b) cfg min

instance (priority := high) unusedVarTestable [Nonempty α] [Testable β] : Testable (NamedBinder var $ ∀ x : α, β) where
  run := λ cfg min => do
    if cfg.traceDiscarded || cfg.traceSuccesses then
      slimTrace s!"{var} is unused"
    let r ← Testable.run β cfg min
    let finalR := addInfo s!"{var} is irrelevant (unused)" id r
    pure $ imp (· $ default) finalR (PSum.inr $ λ x _ => x)

instance (priority := low) decidableTestable {p : Prop} [PrintableProp p] [Decidable p] : Testable p where
  run := λ cfg min =>
    if h : p then
      pure $ success (PSum.inr h)
    else
      match printProp p with
      | some s => pure $ failure h [s!"issue: {s} does not hold"] 0
      | none => pure $ failure h [] 0

end Testable

section PrintableProp

instance Eq.printableProp [Repr α] {x y : α} : PrintableProp (x = y) where
  printProp := some $ s!"{repr x} = {repr y}"

instance Ne.printableProp [Repr α] {x y : α} : PrintableProp (x ≠ y) where
  printProp := some $ s!"{repr x} ≠ {repr y}"

instance LE.printableProp [Repr α] [LE α] {x y : α} : PrintableProp (x ≤ y) where
  printProp := some $ s!"{repr x} ≤ {repr y}"

instance LT.printableProp [Repr α] [LT α] {x y : α} : PrintableProp (x < y) where
  printProp := some $ s!"{repr x} < {repr y}"

instance And.printableProp [PrintableProp x] [PrintableProp y]  : PrintableProp (x ∧ y) where
  printProp := OptionM.run do (pure $ s!"{←printProp x} ∧ {←printProp y}")

instance Or.printableProp [PrintableProp x] [PrintableProp y]  : PrintableProp (x ∨ y) where
  printProp := OptionM.run do (pure $ s!"{←printProp x} ∨ {←printProp y}")

instance Iff.printableProp [PrintableProp x] [PrintableProp y]  : PrintableProp (x ↔ y) where
  printProp := OptionM.run do (pure $ s!"{←printProp x} ↔ {←printProp y}")

instance Imp.printableProp [PrintableProp x] [PrintableProp y]  : PrintableProp (x → y) where
  printProp := OptionM.run do (pure $ s!"{←printProp x} → {←printProp y}")

instance Not.printableProp [PrintableProp x] : PrintableProp (¬x) where
  printProp := OptionM.run do (pure $ s!"¬{←printProp x}")

instance True.printableProp : PrintableProp True where
  printProp := some "True"

instance False.printableProp : PrintableProp False where
  printProp := some "False"

instance Bool.printableProp {b : Bool} : PrintableProp b where
  printProp := some $ if b then "true" else "false"

end PrintableProp

section IO
open TestResult

/-- Execute `cmd` and repeat every time the result is `gave_up` (at most `n` times). -/
def retry (cmd : Rand (TestResult p)) (cfg : Configuration) : Nat → Rand (TestResult p)
| 0 => pure $ TestResult.gaveUp 1
| n+1 => do
  let r ← cmd
  match r with
  | success hp => pure $ success hp
  | TestResult.failure h xs n => pure $ failure h xs n
  | gaveUp _ => retry cmd cfg n

/-- Count the number of times the test procedure gave up. -/
def giveUp (x : Nat) : TestResult p → TestResult p
| success (PSum.inl ()) => gaveUp x
| success (PSum.inr p) => success $ (PSum.inr p)
| gaveUp n => gaveUp $ n + x
| TestResult.failure h xs n => failure h xs n

/-- Try `n` times to find a counter-example for `p`. -/
def Testable.runSuiteAux (p : Prop) [Testable p] (cfg : Configuration) : TestResult p → Nat → Rand (TestResult p)
| r, 0 => pure r
| r, n+1 => do
  let size := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
  if cfg.traceSuccesses then
    slimTrace s!"New sample"
    slimTrace s!"Retrying up to {cfg.numRetries} times until guards hold"
  let x ← retry ((Testable.run p cfg true).run ⟨size⟩) cfg cfg.numRetries
  match x with
  | (success (PSum.inl ())) => runSuiteAux p cfg r n
  | (gaveUp g) => runSuiteAux p cfg (giveUp g r) n
  | _ => pure $ x

/-- Try to find a counter-example of `p`. -/
def Testable.runSuite (p : Prop) [Testable p] (cfg : Configuration := {}) : Rand (TestResult p) :=
  Testable.runSuiteAux p cfg (success $ PSum.inl ()) cfg.numInst

/-- Run a test suite for `p` in `BaseIO` using the global RNG in `stdGenRef`. -/
def Testable.checkIO (p : Prop) [Testable p] (cfg : Configuration := {}) : BaseIO (TestResult p) :=
  match cfg.randomSeed with
  | none => IO.runRand (Testable.runSuite p cfg)
  | some seed => IO.runRandWith seed (Testable.runSuite p cfg)

end IO

namespace Decorations

open Lean

/-- Traverse the syntax of a proposition to find universal quantifiers
quantifiers and add `NamedBinder` annotations next to them. -/
partial def addDecorations (e : Expr) : Expr :=
  e.replace $ λ expr =>
    match expr with
    | Expr.forallE name type body data =>
      let n := name.toString
      let newType := addDecorations type
      let newBody := addDecorations body
      let rest := Expr.forallE name newType newBody data
      some $ mkApp2 (mkConst `SlimCheck.NamedBinder) (mkStrLit n) rest
    | _ => none

/-- `DecorationsOf p` is used as a hint to `mk_decorations` to specify
that the goal should be satisfied with a proposition equivalent to `p`
with added annotations. -/
abbrev DecorationsOf (p : Prop) := Prop

open Elab.Tactic
open Meta

/-- In a goal of the shape `⊢ DecorationsOf p`, `mk_decoration` examines
the syntax of `p` and adds `NamedBinder` around universal quantifications
to improve error messages. This tool can be used in the declaration of a
function as follows:
```lean
def foo (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : ...
```
`p` is the parameter given by the user, `p'` is a definitionally equivalent
proposition where the quantifiers are annotated with `NamedBinder`.
-/
local elab "mk_decorations" : tactic => do
  let goal ← getMainGoal
  let goalType ← getMVarType goal
  if let Expr.app (Expr.const ``Decorations.DecorationsOf _ _) body _ := goalType then
    closeMainGoal (addDecorations body)

end Decorations

/-- Run a test suite for `p` and throw an exception if `p` does not not hold.-/
def Testable.check (p : Prop) (cfg : Configuration := {}) (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO PUnit := do
  let x ← Testable.checkIO p' cfg
  match x with
  | TestResult.success _ => if !cfg.quiet then IO.println "Success" else pure ()
  | TestResult.gaveUp n => if !cfg.quiet then IO.println s!"Gave up {n} times"
  | TestResult.failure _ xs n => throw (IO.userError $ formatFailure "Found problems!" xs n)

-- #eval Testable.check (∀ (x y z a : Nat) (h1 : 3 < x) (h2 : 3 < y), x - y = y - x) Configuration.verbose
-- #eval Testable.check (∀ x : Nat, ∀ y : Nat, x + y = y + x) Configuration.verbose
-- #eval Testable.check (∀ (x : (Nat × Nat)), x.fst - x.snd - 10 = x.snd - x.fst - 10) Configuration.verbose
-- #eval Testable.check (∀ (x : Nat) (h : 10 < x), 5 < x) Configuration.verbose

end SlimCheck

