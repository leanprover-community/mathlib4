import Aesop
import Mathlib.Tactic.Says

set_option says.verify true

variable {X Y Z : Type}

open Function

example {f : X → Y} {g : Y → Z} (hgfinj : Injective (g ∘ f)) : Injective f := by
  rw [Injective]
  aesop? says
    intro a₁ a₂ a
    apply hgfinj
    simp_all only [comp_apply]
