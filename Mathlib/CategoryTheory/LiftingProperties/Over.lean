/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Lifting properties in Over categories

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {S : C}

namespace CommSq.HasLift

lemma over {X₁ X₂ X₃ X₄ : Over S}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} {sq : CommSq t l r b}
    [CommSq.HasLift (f := t.left) (i := l.left) (p := r.left) (g := b.left)
      (sq.map (Over.forget _))] :
    sq.HasLift := by
  let sq' := sq.map (Over.forget _)
  dsimp at sq'
  exact ⟨⟨{
    l := Over.homMk sq'.lift
      (by rw [← Over.w b, ← sq'.fac_right_assoc, Over.w r])
  }⟩⟩

end CommSq.HasLift

namespace HasLiftingProperty

lemma over {A B X Y : Over S}
    (i : A ⟶ B) (p : X ⟶ Y) [HasLiftingProperty i.left p.left] :
    HasLiftingProperty i p := ⟨fun _ ↦ .over⟩

end HasLiftingProperty

end CategoryTheory
