import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

universe v u

open CategoryTheory Simplicial MonoidalCategory

namespace SimplexCategory

def const' (Δ Δ' : SimplexCategory) (x : Fin (Δ'.len + 1)) : Δ ⟶ Δ' :=
  SimplexCategory.Hom.mk ⟨fun _ => x, by tauto⟩

@[simp]
lemma const'_eq_id : const' [0] [0] 0 = 𝟙 _ := by aesop

end SimplexCategory

namespace SSet

noncomputable def monoidalCategory :
  MonoidalCategory SSet.{v} := monoidalOfChosenFiniteProducts
    (FunctorToTypes.functorEmptyLimitCone _)
    (fun K L => FunctorToTypes.binaryProductLimitCone K L)

attribute [local instance] SSet.monoidalCategory

def unitHomEquiv (K : SSet.{v}) : (𝟙_ _ ⟶ K) ≃ K _[0] where
  toFun φ := φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ _ => K.map (SimplexCategory.const' Δ.unop [0] 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp
    erw [← FunctorToTypes.naturality]
    rfl
  right_inv x := by
    dsimp
    rw [SimplexCategory.const'_eq_id]
    erw [FunctorToTypes.map_id_apply]

end SSet

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

section

attribute [local instance] SSet.monoidalCategory

/-- A (pre)simplicial category is a category `C` that is enriched in the category
of simplicial sets in such a way that the `0`-simplicies of this simplicial hom
identifies to morphisms in `C`. -/
class PresimplicialCategory where
  enrichedCategory : EnrichedCategory SSet.{v} C := by infer_instance
  homEquiv (K L : C) : (K ⟶ L) ≃ (𝟙_ SSet.{v} ⟶ EnrichedCategory.Hom K L)
  homEquiv_id (K : C) : homEquiv K K (𝟙 K) = eId SSet K := by aesop_cat
  homEquiv_comp {K L M : C} (f : K ⟶ L) (g : L ⟶ M) :
    homEquiv K M (f ≫ g) = (λ_ _).inv ≫ (homEquiv K L f ⊗ homEquiv L M g) ≫
      eComp SSet K L M := by aesop_cat

end

namespace PresimplicialCategory

attribute [scoped instance] enrichedCategory SSet.monoidalCategory

variable [PresimplicialCategory C]

variable {C}
abbrev sHom (K L : C) : SSet.{v} := EnrichedCategory.Hom K L

noncomputable def sHomMap₂ (K : C) {L L' : C} (g : L ⟶ L') :
    sHom K L ⟶ sHom K L' :=
  (ρ_ _).inv ≫ _ ◁ homEquiv L L' g ≫ eComp SSet K L L'

noncomputable def sHomMap₁ {K K' : C} (f : K ⟶ K') (L : C) :
    sHom K' L ⟶ sHom K L :=
  (λ_ _).inv ≫ homEquiv K K' f ▷ _ ≫ eComp SSet K K' L

variable (C)

@[simps]
noncomputable def sHomFunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} where
  obj K :=
    { obj := fun L => sHom K.unop L
      map := fun φ => sHomMap₂ K.unop φ
      map_id := sorry
      map_comp := sorry }
  map φ :=
    { app := fun L => sHomMap₁ φ.unop L
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

-- TODO: develop API for the "adjoint functors"
-- especially, introduce a data value class containing the data
-- of a representative of `A ⊗ K` for `A : SSet.{v}` and `K`.

end PresimplicialCategory

end CategoryTheory
