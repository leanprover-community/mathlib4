import Mathlib.Algebra.Homology.ShortComplex.Ab

universe u

open CategoryTheory Limits

namespace AddCommGroupCat

-- this was in Algebra.Category.GroupCat.Abelian, but had to be moved
-- in a separate file because of import dependencies

/-- The category of abelian groups satisfies Grothedieck's Axiom AB5. -/
noncomputable instance {J : Type u} [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits <| colim (J := J) (C := AddCommGroupCat.{u}) := by
  refine' Functor.preservesFiniteLimitsOfMapExact _ (fun S hS => _)
  replace hS := fun j => hS.map ((evaluation _ _).obj j)
  simp only [ShortComplex.ab_exact_iff_ker_le_range] at hS ⊢
  intro x (hx : _ = _)
  dsimp at hx
  rcases Concrete.colimit_exists_rep S.X₂ x with ⟨j, y, rfl⟩
  erw [← comp_apply, colimit.ι_map, comp_apply,
    ← map_zero (by exact colimit.ι S.X₃ j : (S.X₃).obj j →+ ↑(colimit S.X₃))] at hx
  rcases Concrete.colimit_exists_of_rep_eq.{u, u, u} S.X₃ _ _ hx with ⟨k, e₁, e₂, hk : _ = S.X₃.map e₂ 0⟩
  rw [map_zero, ← comp_apply, ← NatTrans.naturality, comp_apply] at hk
  rcases hS k hk with ⟨t, ht⟩
  use colimit.ι S.X₁ k t
  erw [← comp_apply, colimit.ι_map, comp_apply, ht]
  exact colimit.w_apply S.X₂ e₁ y

end AddCommGroupCat
