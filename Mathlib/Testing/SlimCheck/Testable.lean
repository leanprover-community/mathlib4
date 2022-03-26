/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Mathlib.Testing.SlimCheck.Sampleable
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Find

namespace SlimCheck

inductive TestResult (p : Prop) where
| success : PSum Unit p → TestResult p
| gaveUp : Nat → TestResult p
| failure : ¬p → List String → Nat → TestResult p
deriving Inhabited

structure Configuration where
  numInst : Nat := 100
  maxSize : Nat := 100
  minSize : Nat := 1
  traceDiscarded : Bool := false
  traceSuccesses : Bool := false
  traceShrink : Bool := false
  traceShrinkCandidates : Bool := false
  randomSeed : Option Nat := none
  quiet : Bool := false
  deriving Inhabited

class PrintableProp (p : Prop) where
  printProp : Option String

export PrintableProp (printProp)

instance (priority := low) : PrintableProp p where
  printProp := none

class Testable (p : Prop) where
  run {} (cfg : Configuration) (minimize : Bool) : Gen (TestResult p)

def NamedBinder (n : String) (p : Prop) : Prop := p

namespace TestResult

def toString : TestResult p → String
| success (PSum.inl _) => "success (no proof)"
| success (PSum.inr _) => "success (proof)"
| gaveUp n => s!"gave {n} times"
| failure _ counters n => s!"failed {counters}"

instance : ToString (TestResult p) := ⟨toString⟩

def combine {p q : Prop} : PSum Unit (p → q) → PSum Unit p → PSum Unit q
| PSum.inr f, PSum.inr proof => PSum.inr $ f proof
| _, _ => PSum.inl ()

def and : TestResult p → TestResult q → TestResult (p ∧ q)
| failure h xs n, _ => failure (λ h2 => h h2.left) xs n
| _, failure h xs n => failure (λ h2 => h h2.right) xs n
| success h1, success h2 => success $ combine (combine (PSum.inr And.intro) h1) h2
| gaveUp n, gaveUp m => gaveUp $ n + m
| gaveUp n, _ => gaveUp n
| _, gaveUp n => gaveUp n

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

def imp (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q :=
  match r with
  | failure h2 xs n => failure (mt h h2) xs n
  | success h2 => success $ combine p h2
  | gaveUp n => gaveUp n

def iff (h : q ↔ p) (r : TestResult p) : TestResult q :=
  imp h.mp r (PSum.inr h.mpr)

def addInfo (x : String) (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q :=
  if let failure h2 xs n := r then
    failure (mt h h2) (x :: xs) n
  else
    imp h r p

def addVarInfo [Repr γ] (var : String) (x : γ) (h : q → p) (r : TestResult p)
    (p : PSum Unit (p → q) := PSum.inl ()) : TestResult q  :=
  addInfo s!"{var} := {repr x}" h r p

def isFailure : TestResult p → Bool
| failure _ _ _ => true
| _ => false

end TestResult

namespace Testable

open TestResult

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

instance decTestable [PrintableProp p] [Decidable p] {β : p → Prop} [∀ h, Testable (β h)] : Testable (NamedBinder var $ ∀ h, β h) where
  run := λ cfg min => do
    if h : p then
      let res := (run (β h) cfg min)
      match printProp p with
      | none => (λ r => imp (· $ h) r (PSum.inr $ λ q _ => q)) <$> res
      | some s => (λ r => addInfo s!"guard: {s}" (· $ h) r (PSum.inr $ λ q _ => q)) <$> res
    else if cfg.traceDiscarded || cfg.traceSuccesses then
      let res := (λ _ => pure $ gaveUp 1)
      match printProp p with
      | none => dbgTrace "discard" res
      | some s => dbgTrace s!"discard: {s} does not hold" res
    else
      pure $ gaveUp 1

instance forallTypesTestable {f : Type → Prop} [Testable (f Int)] : Testable (NamedBinder var $ ∀ x, f x) where
  run := λ cfg min => do
    let r ← run (f Int) cfg min
    pure $ addVarInfo var "ℤ" (· $ Int) r

def traceGiveup [Repr α] (tracing : Bool) (var : String) (val : α) : TestResult p → (Unit → β) → β
| gaveUp _ => if tracing then dbgTrace s!"{var} = {repr val}" else (· $ ())
| _ => (· $ ())

def combine (ts : List (Testable p)) (h : 0 < ts.length) : Testable p := ⟨λ cfg min => do
  let f := (@Testable.run _ · cfg min)
  have : 0 < List.length (List.map f ts) := by
    rw [List.length_map]
    exact h
  Gen.oneOf (ts.map f) this⟩


def formatFailureAux (s : String) (xs : List String) (n : Nat) : String :=
  let counter := String.intercalate "\n" xs
  let parts := [
    "===================",
    s,
    "\n",
    counter,
    s!"({n} shrinks)",
    "-------------------"
  ]
  String.intercalate "\n" parts

def formatFailure (s : String) : TestResult p → String
| TestResult.failure _ xs n => formatFailureAux s xs n
| _ => ""

def addShrinks (n : Nat) : TestResult p → TestResult p
| TestResult.failure p xs m => TestResult.failure p xs (m + n)
| p => p

def minimizeAux {β : α → Prop} [SampleableExt α] [∀ x, Testable (β x)] (cfg : Configuration) (var : String)
    (x : SampleableExt.proxy α) (n : Nat) : OptionT Gen (Σ x, TestResult (β (SampleableExt.interp x))) := do
  let candidates := Shrinkable.shrink.run x
  if cfg.traceShrinkCandidates then
    dbg_trace "candidates for {var} :=\n{repr candidates}\n"
  for ⟨candidate, h⟩ in candidates do
    let res ← OptionT.lift $ Testable.run (β (SampleableExt.interp candidate)) cfg true
    if !res.isFailure then
      if cfg.traceShrink then
        dbg_trace s!"{var} := {repr candidate}" ++ formatFailure "Shrink counter-example:" res
      let currentStep := OptionT.lift $ pure $ Sigma.mk candidate (addShrinks (n + 1) res)
      let nextStep := minimizeAux cfg var candidate (n + 1) <|> currentStep
      return ←nextStep
  failure
  termination_by minimizeAux cfg var x n => x
  decreasing_by simp_all

def minimize {β : α → Prop} [SampleableExt α] [∀ x, Testable (β x)] (cfg : Configuration) (var : String)
    (x : SampleableExt.proxy α) (r : TestResult (β $ SampleableExt.interp x)) : Gen (Σ x, TestResult (β $ SampleableExt.interp x)) := do
  if cfg.traceShrink then
    dbg_trace (s!"{var} := {repr x}" ++ formatFailure "Shrink counter-example:" r)
  let res ← OptionT.run $ minimizeAux cfg var x 0
  pure $ res.getD ⟨x, r⟩
end Testable

end SlimCheck
