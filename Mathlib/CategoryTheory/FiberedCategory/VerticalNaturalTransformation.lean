import Mathlib.CategoryTheory.FiberedCategory.CartesianFunctor

/-!
# Cartesian Functors

For fibered categories `p : 𝒳 ⥤ 𝒮` and `q : 𝒴 ⥤ 𝒮`, a functor `F : 𝒳 ⥤ 𝒴` is cartesian (also
called fibered) if it satisfies `F ⋙ q = p` and it preserves cartesian morphisms.
We show that these form a category in the obvious manner.

## References
* [T. Streicher, *Fibered Categories à la Jean Bénabou*](https://arxiv.org/abs/math/0206203)

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Functor Category IsHomLift

namespace FiberedCategoryTheory
namespace Functor

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]
  (p : 𝒳 ⥤ 𝒮) (q : 𝒴 ⥤ 𝒮) [IsFibered p] [IsFibered q]
  (F : 𝒳 ⥤ 𝒴) [IsCartesianFunctor p q F] (G : 𝒳 ⥤ 𝒴) [IsCartesianFunctor p q G]

class IsVerticalNatAux (τ : F ⟶ G)  where
  isVertical (X : 𝒳) :
    q.map (τ.app X) = (eqToHom <| IsCartesianFunctor.triangle p q F).app X ≫
      (eqToHom <| (IsCartesianFunctor.triangle p q G).symm).app X

end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]
  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [IsFibered p] [IsFibered q]
  (F : CartesianFunctor p q) (G : CartesianFunctor p q)

class IsVertical (τ : F.functor ⟶ G.functor) where
  isVertical (X : 𝒳) : q.map (τ.app X) =
      (eqToHom F.triangle).app X ≫ (eqToHom G.triangle.symm).app X

structure VerticalNatTrans where
  VerticalNat : F.functor ⟶ G.functor
  isVertical : IsVertical F G VerticalNat := by infer_instance

def id_VerticalNatTrans : VerticalNatTrans F F where
  VerticalNat := 𝟙 F.functor
  isVertical := ⟨fun X ↦ by simp⟩
end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]
  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [IsFibered p] [IsFibered q]
  {F : CartesianFunctor p q} {G : CartesianFunctor p q} {H : CartesianFunctor p q}
  (τ : VerticalNatTrans F G) (ε : VerticalNatTrans G H)

def comp_VerticalNatTrans : VerticalNatTrans F H where
  VerticalNat := τ.VerticalNat ≫ ε.VerticalNat
  isVertical := sorry
end

section
variable
  {𝒮 : Type u₁} {𝒳 : Type u₂} {𝒴 : Type u₃}
  [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] [Category.{v₃} 𝒴]
  {p : 𝒳 ⥤ 𝒮} {q : 𝒴 ⥤ 𝒮} [IsFibered p] [IsFibered q]

-- Some lemmas have to be shown here
instance CartesianFunctor.category : Category (CartesianFunctor p q) where
  Hom F G := VerticalNatTrans F G
  id F := id_VerticalNatTrans F
  comp τ ε := comp_VerticalNatTrans
end

end Functor
end FiberedCategoryTheory
