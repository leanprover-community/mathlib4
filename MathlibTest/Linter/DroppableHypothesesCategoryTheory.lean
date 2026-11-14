module
import Mathlib.Tactic.Linter.DroppableHypotheses
import Mathlib.CategoryTheory.Limits.Types.End
import Mathlib.CategoryTheory.Topos.Sheaf

set_option linter.droppableHypotheses true
set_option linter.droppableHypotheses.maxHeartbeats 20000

universe w v u

namespace DroppableHypothesesCategoryTheoryTest

open CategoryTheory CategoryTheory.Limits Opposite

-- Dropping J while retaining the explicitly dependent section binders used to cause a
-- stack overflow in Lean's universe unifier. These trials must be skipped before elaboration.
section
variable {J : Type u} [Category.{v} J] (F : Jᵒᵖ ⥤ J ⥤ Type max w u)

#guard_msgs in
lemma coendRel_iff (j j' : J) (x : (F.obj (op j)).obj j) (x' : (F.obj (op j')).obj j') :
    Types.coendRel F ⟨j, x⟩ ⟨j', x'⟩ ↔
      ∃ (f : j ⟶ j') (y : (F.obj (op j')).obj j),
        (F.map f.op).app _ y = x ∧ (F.obj _).map f y = x' := by
  exact Types.coendRel_iff F j j' x x'
end

section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J (Type (max u v))}

#guard_msgs in
lemma isPullback_χ_truth (m : F ⟶ G) [Mono m] :
    IsPullback m ((Sheaf.isTerminalTerminal J _).from F) (Sheaf.χ m) (Sheaf.truth J) := by
  exact Sheaf.isPullback_χ_truth m
end

end DroppableHypothesesCategoryTheoryTest
