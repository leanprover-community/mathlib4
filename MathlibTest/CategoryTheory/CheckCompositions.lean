import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Tactic.Recall

universe v₁ v₂ v₃ v u₁ u₂ u₃ u

open CategoryTheory Limits

variable {J : Type u} [Category.{v} J] {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] (F : J ⥤ C) (G : C ⥤ D) (H : D ⥤ E)

variable [HasColimitsOfShape J C] [HasColimitsOfShape J E] [PreservesColimit F (G ⋙ H)]

/--
info: In composition
  colimit.ι ((F ⋙ G) ⋙ H) j ≫ (preservesColimitIso (G ⋙ H) F).inv
the source of
  (preservesColimitIso (G ⋙ H) F).inv
is
  colimit (F ⋙ G ⋙ H)
but should be
  colimit ((F ⋙ G) ⋙ H)
-/
#guard_msgs in
set_option linter.unusedTactic false in
example (j : J) :
    colimit.ι ((F ⋙ G) ⋙ H) j ≫ (preservesColimitIso (G ⋙ H) F).inv =
      H.map (G.map (colimit.ι F j)) := by

  -- We know which lemma we want to use, and it's even a simp lemma, but `rw` won't let us apply it
  fail_if_success rw [ι_preservesColimitIso_inv]
  fail_if_success rw [ι_preservesColimitIso_inv (G ⋙ H)]
  fail_if_success simp only [ι_preservesColimitIso_inv]

  -- This would work:
  -- erw [ι_preservesColimitIso_inv (G ⋙ H)]

  -- `check_compositions` checks if the two morphisms we're composing are composed by abusing defeq,
  -- and indeed it tells us that we are abusing definitional associativity of composition of
  -- functors here!
  check_compositions

  -- In this case, we can "fix" this by reassociating in the goal, but usually at this point the
  -- right thing to do is to back off and check how we ended up with a bad goal in the first place.
  dsimp only [Functor.assoc]

  -- This would work now, but it is not needed, because simp works as well
  -- rw [ι_preservesColimitIso_inv]

  simp
