import Mathlib.Tactic.TacticAnalysis.Declarations
import Mathlib.Tactic.AdaptationNote
import Lean.LibrarySuggestions

section terminalReplacement

section omega

set_option linter.tacticAnalysis.omegaToLia true

/-- warning: `lia` can replace `omega` -/
#guard_msgs in
example : 1 + 1 = 2 := by
  omega

end omega

@[tacticAnalysis linter.tacticAnalysis.dummy]
def foo : Mathlib.TacticAnalysis.Config :=
  Mathlib.TacticAnalysis.terminalReplacement "simp" "simp only" ``Lean.Parser.Tactic.simp
    (fun _ _ _ => `(tactic| simp only))
    (reportSuccess := true) (reportFailure := true)

/--
warning: `simp only` left unsolved goals where `simp` succeeded.
Original tactic:
  simp
Replacement tactic:
  simp only
Unsolved goals:
  [⊢ (List.map (fun x => x + 1) [1, 2, 3]).sum = 9 ]
-/
#guard_msgs in
set_option linter.tacticAnalysis.dummy true in
example : List.sum ([1,2,3].map fun x ↦ x + 1) = 9 := by
  simp

end terminalReplacement

section rwMerge

set_option linter.tacticAnalysis.rwMerge true

def x := 1
def y := 1
def z := 1
theorem xy : x = y := rfl
theorem yz : y = z := rfl

example : x = y := by
  rw [xy]

/--
warning: Try this: rw [xy, yz]
-/
#guard_msgs in
example : x = z := by
  rw [xy]
  rw [yz]

-- Definitions using `where` clauses did not get picked up by the framework,
-- since apparently their syntax bounds do not match the original.
structure Fact (p : Prop) : Prop where
  out : p
/--
warning: Try this: rw [xy, yz]
-/
#guard_msgs in
example : Fact (x = z) where
  out := by
    rw [xy]
    rw [yz]

universe u

def a : PUnit.{u} := ⟨⟩
def b : PUnit.{u} := ⟨⟩
def c : PUnit.{u} := ⟨⟩
theorem ab : a = b := rfl
theorem bc : b = c := rfl

/--
warning: Try this: rw [ab.{u}, bc.{u}]
-/
#guard_msgs in
example : a.{u} = c := by
  rw [ab.{u}]
  rw [bc.{u}]

theorem xyz (h : x = z → y = z) : x = y := by rw [h yz]; rfl

-- The next example tripped up `rwMerge` because `rw [xyz fun h => ?_, ← h, xy]` gives
-- an unknown identifier `h`.
example : x = y := by
  rw [xyz fun h => ?_]
  rw [← h, xy]

end rwMerge

section mergeWithGrind

set_option linter.tacticAnalysis.mergeWithGrind true

example : 1 + 1 = 2 := by
  grind

/--
warning: 'have : 1 + 1 < 3 := by omega; grind' can be replaced with 'grind'
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  have : 1 + 1 < 3 := by omega
  grind

-- `#adaptation_note` is ignored
example : 1 + 1 = 2 := by
  #adaptation_note /-- -/
  grind

set_option linter.unusedTactic false

/-- warning: 'skip; grind' can be replaced with 'grind' -/
#guard_msgs in
example : 0 = 0 := by
  intros
  intros
  intros
  intros
  skip
  grind

set_option linter.unusedTactic true

end mergeWithGrind

section replaceWithGrind

set_option linter.tacticAnalysis.terminalToGrind true

example : 1 + 1 = 2 := by
  grind

/--
warning: replace the proof with 'grind': have : 1 + 1 < 3 := by omega;
  have : 1 + 1 < 4 := by omega;
  rfl
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  have : 1 + 1 < 3 := by omega
  have : 1 + 1 < 4 := by omega
  rfl

universe u v

-- This next example used to fail with `unknown universe level 'v'`.

/--
warning: replace the proof with 'grind': let T : Type max u v := Sigma f;
  have : 1 + 1 = 2 := rfl;
  rfl
-/
#guard_msgs in
example {α : Type u} (f : α → Type max u v) : 1 = 1 := by
  let T : Type max u v := Sigma f
  have : 1 + 1 = 2 := rfl -- Extra line to ensure the linter picks it up.
  rfl

-- Ensure the effects of `classical` are picked up. Otherwise we get an error like:
-- failed to synthesize
--   Decidable b
theorem forall_imp_iff_exists_imp {α : Type} {p : α → Prop} {b : Prop} [ha : Nonempty α] :
    (∀ x, p x) → b ↔ ∃ x, p x → b := by
  classical
  let ⟨a⟩ := ha
  refine ⟨fun h ↦ Decidable.not_forall_not.1 fun h' ↦ ?_, fun ⟨x, hx⟩ h ↦ hx (h x)⟩
  exact if hb : b then h' a fun _ ↦ hb else hb <| h fun x ↦ (Decidable.not_imp_iff_and_not.1 (h' x)).1

end replaceWithGrind

section introMerge

set_option linter.tacticAnalysis.introMerge true

/-- warning: Try this: intro a b -/
#guard_msgs in
example : ∀ a b : Unit, a = b := by
  intro a
  intro b
  rfl

/-- warning: Try this: intro _ b -/
#guard_msgs in
example : ∀ a b : Unit, a = b := by
  intro
  intro b
  rfl

/-- warning: Try this: intro a _ -/
#guard_msgs in
example : ∀ a b : Unit, a = b := by
  intro a
  intro _
  rfl


#guard_msgs in
example : ∀ a b : Unit, a = b := by
  intro a b
  rfl

end introMerge

section tryAtEachStep

-- Disable timing in tests to avoid non-deterministic output
set_option linter.tacticAnalysis.tryAtEachStep.showTiming false

section
set_option linter.tacticAnalysis.tryAtEachStepGrind true

/-- info: `rfl` can be replaced with `grind` -/
#guard_msgs in
example : 1 + 1 = 2 := by
  rfl

/--
info: `skip` (+1 later steps) can be replaced with `grind`
---
info: `rfl` can be replaced with `grind`
---
warning: 'skip' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  skip
  rfl

end

section

def P (_ : Nat) := True
theorem p : P 37 := trivial

set_library_suggestions fun _ _ => pure #[{ name := `p, score := 1.0 }]

example : P 37 := by
  grind +suggestions

/--
info: Try this:
  [apply] simp_all only [p]
-/
#guard_msgs in
example : P 37 := by
  simp_all? +suggestions

set_option linter.tacticAnalysis.tryAtEachStepGrindSuggestions true in
-- FIXME: why is the dagger here?
/-- info: `trivial` can be replaced with `grind +suggestions✝` -/
#guard_msgs in
example : P 37 := by
  trivial

set_option linter.tacticAnalysis.tryAtEachStepSimpAllSuggestions true in
-- FIXME: why is the dagger here?
/--
info: Try this:
  [apply] simp_all +suggestions✝ only [p]
---
info: `trivial` can be replaced with `simp_all? +suggestions✝`
-/
#guard_msgs in
example : P 37 := by
  trivial

end

end tryAtEachStep

section selfReplacements

set_option linter.tacticAnalysis.tryAtEachStep.showTiming false
set_option linter.tacticAnalysis.tryAtEachStepGrind true

-- With selfReplacements true (default), grind replacing grind is reported
/-- info: `grind` can be replaced with `grind` -/
#guard_msgs in
example : 1 + 1 = 2 := by
  grind

section
set_option linter.tacticAnalysis.tryAtEachStep.selfReplacements false

-- With selfReplacements false, grind replacing grind is NOT reported
#guard_msgs in
example : 1 + 1 = 2 := by
  grind

-- Non-self replacements are still reported when selfReplacements is false
/-- info: `rfl` can be replaced with `grind` -/
#guard_msgs in
example : 1 + 1 = 2 := by
  rfl

end

end selfReplacements

section laterSteps

set_option linter.tacticAnalysis.tryAtEachStep.showTiming false
set_option linter.tacticAnalysis.tryAtEachStepGrind true
set_option linter.unusedTactic false

-- Test that later steps are counted correctly
/--
info: `skip` (+3 later steps) can be replaced with `grind`
---
info: `skip` (+2 later steps) can be replaced with `grind`
---
info: `skip` (+1 later steps) can be replaced with `grind`
---
info: `rfl` can be replaced with `grind`
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  skip
  skip
  skip
  rfl

end laterSteps

section grindReplacement

set_option linter.tacticAnalysis.regressions.omegaToLia true

-- We should not complain about `omega` (and others) failing in a `try` context.
example : x = y := by
  try omega
  rfl

-- Example with more than one tactic step:
example : x = y := by
  try
    symm
    symm
    lia
  rfl

set_option linter.unusedVariables false in
theorem create_a_few_goals (h1 : 1 + 1 = 2) (h2 : y = z) : x = y := rfl

-- We should not complain about `omega` (and others) failing in an `any_goals` context.
example : x = y := by
  apply create_a_few_goals
  any_goals omega
  rfl

-- Example with more than one tactic step:
example : x = y := by
  apply create_a_few_goals
  any_goals
    symm
    symm
    lia
  rfl

end grindReplacement

section unknownTactic

-- Test that tryAtEachStepFromStrings gracefully handles unknown tactics
-- (e.g., trying to run `aesop` before Aesop is imported)

register_option linter.tacticAnalysis.unknownTacticTest : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.unknownTacticTest]
def unknownTacticTest :=
  Mathlib.TacticAnalysis.tryAtEachStepFromStrings "nonexistent" "nonexistent_tactic_xyz"

-- This should not crash - the unknown tactic should be silently skipped
set_option linter.tacticAnalysis.unknownTacticTest true in
#guard_msgs in
example : 1 + 1 = 2 := by rfl

end unknownTactic
