import Mathlib.CategoryTheory.Sites.Grothendieck

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (J : GrothendieckTopology C) (e : C ≌ D)

def GrothendieckTopology.transfer : GrothendieckTopology D where
  sieves X := {S | S.functorPushforward e.inverse ∈ J.sieves (e.inverse.obj X)}
  top_mem' X := by simp
  pullback_stable' X Y S f := by
    sorry
  transitive' := sorry

theorem Sieve.functorPushforward_eq {X : C} (S : Sieve X) :
    S.functorPushforward (e.functor ⋙ e.inverse) = S.pullback (e.unitInv.app X) := by
  ext Y f
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨W, g, i, hg, hfi⟩ := h
    simp only [Functor.comp_obj, Functor.id_obj, hfi, Functor.comp_map, Equivalence.inv_fun_map,
      pullback_apply, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [← Category.assoc]
    exact downward_closed S hg _
  · exact ⟨_, f ≫ e.unitInv.app X, e.unit.app Y, h, by simp⟩


theorem GrothendieckTopology.transfer_transfer : (J.transfer e).transfer e.symm = J := by
  ext X S
  simp only [transfer, Equivalence.symm_inverse, Set.mem_setOf_eq, ← Sieve.functorPushforward_comp,
    ← Functor.comp_obj]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · sorry
  · sorry


end CategoryTheory
