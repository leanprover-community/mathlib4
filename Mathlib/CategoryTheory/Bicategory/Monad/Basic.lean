import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

namespace CategoryTheory

namespace Bicategory

universe w v u u₁

variable {B : Type u} [Bicategory.{w, v} B]

structure Monad (a : B) where
  -- a : B
  t : a ⟶ a
  μ : t ≫ t ⟶ t
  η : 𝟙 a ⟶ t
  assoc : μ ▷ t ≫ μ = (α_ _ _ _).hom ≫ t ◁ μ ≫ μ := by aesop_cat
  left_unit : η ▷ t ≫ μ = (λ_ t).hom := by aesop_cat
  right_unit : t ◁ η ≫ μ = (ρ_ t).hom := by aesop_cat

-- local notation "𝟭" => (LocallyDiscrete (Discrete PUnit))

namespace Monad

def ofLaxFromPunit (F : LaxFunctor (LocallyDiscrete (Discrete PUnit.{u₁+1})) B) :
    Monad (F.obj ⟨⟨PUnit.unit⟩⟩) where
  t := F.map (𝟙 _)
  μ := F.mapComp _ _ ≫ F.map₂ (ρ_ _).hom
  η := F.mapId _
  assoc := by
    set a : LocallyDiscrete (Discrete PUnit.{u₁+1}) := ⟨⟨PUnit.unit⟩⟩
    simp only [comp_whiskerRight, Category.assoc, whiskerLeft_comp]
    rw [← F.mapComp_naturality_left_assoc, F.mapComp_assoc_left_assoc,
      ← F.mapComp_naturality_right_assoc]
    simp
  left_unit := (F.map₂_leftUnitor_hom _).symm
  right_unit := (F.map₂_rightUnitor_hom _).symm

end Monad

end Bicategory

end CategoryTheory
