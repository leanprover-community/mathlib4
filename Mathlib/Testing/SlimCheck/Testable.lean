/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/

import Mathlib.Testing.SlimCheck.Sampleable
import Lean

namespace SlimCheck

variable {β : α → Prop}

inductive TestResult (p : Prop) where
| success : PSum Unit p → TestResult p
| gaveUp : Nat → TestResult p
| failure : ¬p → List String → Nat → TestResult p
deriving Inhabited

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

class PrintableProp (p : Prop) where
  printProp : Option String

export PrintableProp (printProp)

instance (priority := low) : PrintableProp p where
  printProp := none

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

def combine : PSum Unit (p → q) → PSum Unit p → PSum Unit q
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

namespace Configuration

def verbose : Configuration := {
  traceDiscarded := true,
  traceSuccesses := true,
  traceShrink := true,
  traceShrinkCandidates := true
}

end Configuration

namespace Testable

open TestResult

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

def combine (ts : List (Testable p)) (h : 0 < ts.length) : Testable p := ⟨λ cfg min => do
  let f := (@Testable.run _ · cfg min)
  have : 0 < List.length (List.map f ts) := by
    rw [List.length_map]
    exact h
  Gen.oneOf (ts.map f) this⟩

def formatFailureAux (s : String) (xs : List String) (n : Nat) : String :=
  let counter := String.intercalate "\n" xs
  let parts := [
    "\n===================",
    s,
    counter,
    s!"({n} shrinks)",
    "-------------------"
  ]
  String.intercalate "\n" parts

def addShrinks (n : Nat) : TestResult p → TestResult p
| TestResult.failure p xs m => TestResult.failure p xs (m + n)
| p => p

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

def minimize [SampleableExt α] [∀ x, Testable (β x)] (cfg : Configuration) (var : String)
    (x : SampleableExt.proxy α) (r : TestResult (β $ SampleableExt.interp x)) : Gen (Σ x, TestResult (β $ SampleableExt.interp x)) := do
  if cfg.traceShrink then
     slimTrace "Shrink"
     slimTrace s!"Attempting to shrink {var} := {repr x}"
  let res ← OptionT.run $ minimizeAux cfg var x 0
  pure $ res.getD ⟨x, r⟩

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

instance propVarTestable {β : Prop → Prop} [∀ b : Bool, Testable (β b)] : Testable (NamedBinder var $ ∀ p : Prop, β p) where
  run := λ cfg min =>
    imp (λ h (b : Bool) => h b) <$> Testable.run (NamedBinder var $ ∀ b : Bool, β b) cfg min

instance (priority := high) unusedVarTestable {β : Prop} [Inhabited α] [Testable β] : Testable (NamedBinder var $ ∀ x : α, β) where
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

def retry (cmd : Rand (TestResult p)) (cfg : Configuration) : Nat → Rand (TestResult p)
| 0 => pure $ TestResult.gaveUp 1
| n+1 => do
  let r ← cmd
  match r with
  | success hp => pure $ success hp
  | TestResult.failure h xs n => pure $ failure h xs n
  | gaveUp _ => retry cmd cfg n

def giveUp (x : Nat) : TestResult p → TestResult p
| success (PSum.inl ()) => gaveUp x
| success (PSum.inr p) => success $ (PSum.inr p)
| gaveUp n => gaveUp $ n + x
| TestResult.failure h xs n => failure h xs n

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

def Testable.runSuite (p : Prop) [Testable p] (cfg : Configuration := {}) : Rand (TestResult p) :=
  Testable.runSuiteAux p cfg (success $ PSum.inl ()) cfg.numInst

def Testable.checkIO (p : Prop) [Testable p] (cfg : Configuration := {}) : BaseIO (TestResult p) :=
  match cfg.randomSeed with
  | none => IO.runRand (Testable.runSuite p cfg)
  | some seed => IO.runRandWith seed (Testable.runSuite p cfg)

end IO

namespace Decorations

open Lean

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

abbrev DecorationsOf (p : Prop) := Prop

syntax (name := mkDecorations) "mk_decorations" : tactic

open Elab.Tactic
open Meta

elab_rules : tactic | `(tactic| mk_decorations) => do
  let goal ← getMainGoal
  let goalType ← getMVarType goal
  if let Expr.app (Expr.const `SlimCheck.Decorations.DecorationsOf _ _) body _ := goalType then
    closeMainGoal (addDecorations body)

end Decorations

def Testable.check (p : Prop) (cfg : Configuration := {}) (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO PUnit := do
  let x ← Testable.checkIO p' cfg
  match x with
  | TestResult.success _ => if !cfg.quiet then IO.println "Success" else pure ()
  | TestResult.gaveUp n => if !cfg.quiet then IO.println s!"Gave up {n} times"
  | TestResult.failure _ xs n => throw (IO.userError $ formatFailureAux "Found problems!" xs n)

-- Works
-- #eval Testable.check (∀ (x y z a : Nat) (h1 : 3 < x) (h2 : 3 < y), x - y = y - x) { Configuration.verbose with randomSeed := some 10000}
-- Broken
-- #eval Testable.check (∀ (x y z a : Nat) (h1 : 3 < x) (h2 : 3 < y), x - y = y - x) { Configuration.verbose with randomSeed := some 1000}
-- #eval Testable.check (∀ x : Nat, ∀ y : Nat, x + y = y + x) Configuration.verbose
-- #eval Testable.check (∀ (x : (Nat × Nat)), x.fst - x.snd - 10 = x.snd - x.fst - 10) Configuration.verbose
-- #eval Testable.check (∀ (x : Nat) (h : 10 < x), 5 < x) Configuration.verbose

end SlimCheck
