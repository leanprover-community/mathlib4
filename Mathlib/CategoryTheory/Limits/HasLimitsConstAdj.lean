import Mathlib.CategoryTheory.Limits.HasLimits

namespace CategoryTheory

open Category

variable {C J : Type _} [Category C] [Category J]

namespace Limits

variable {F : (J ⥤ C) ⥤ C} (adj : Functor.const J ⊣ F)

@[simps]
def coneOfConstAdjunction (X : J ⥤ C) : Cone X where
  pt := F.obj X
  π := adj.counit.app X

def isLimitConeOfConstAdjunction (X : J ⥤ C) : IsLimit (coneOfConstAdjunction adj X) where
  lift s := adj.homEquiv _ _ s.π
  fac s j := by
    have eq := NatTrans.congr_app (adj.counit.naturality s.π) j
    have eq' := NatTrans.congr_app (@Adjunction.left_triangle_components _ _ _ _ _ _ adj s.pt) j
    dsimp at eq eq' ⊢
    simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj, assoc, eq,
      reassoc_of% eq']
  uniq s m hm := by
    dsimp
    symm
    rw [adj.homEquiv_apply_eq]
    ext j
    simp only [Adjunction.homEquiv_counit, Functor.id_obj, NatTrans.comp_app,
      Functor.const_obj_obj, Functor.const_map_app, ← hm, coneOfConstAdjunction_π]

lemma hasLimitsOfShape_of_const_adjunction : HasLimitsOfShape J C :=
  ⟨fun X => ⟨⟨_, isLimitConeOfConstAdjunction adj X⟩⟩⟩

instance hasLimitsOfShape_of_isLeftAdjoint_const [IsLeftAdjoint (Functor.const J : C ⥤ _)] :
    HasLimitsOfShape J C :=
  hasLimitsOfShape_of_const_adjunction (Adjunction.ofLeftAdjoint _)

end Limits

end CategoryTheory
