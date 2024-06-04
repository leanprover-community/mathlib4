import Mathlib.Topology.Category.LightProfinite.Basic
import Mathlib.CategoryTheory.Functor.OfSequence

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

namespace LightProfinite

variable (F : ℕᵒᵖ ⥤ LightProfinite)

-- lemma limit_of_surjections_surjective
--     (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
--       Function.Surjective (sorry : limit F ⟶ F.obj ⟨0⟩) := sorry
