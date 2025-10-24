import Mathlib.Tactic.TacticAnalysis.Declarations
import Mathlib.Tactic.AdaptationNote

section terminalReplacement

section omega

set_option linter.tacticAnalysis.omegaToCutsat true

/-- warning: `cutsat` can replace `omega` -/
#guard_msgs in
example : 1 + 1 = 2 := by
  omega

end omega

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
