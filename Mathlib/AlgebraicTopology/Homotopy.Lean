import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

open CategoryTheory CategoryTheory.Limits Simplicial SimplicialObject

variable (X Y X' Y': SSet) (m n : ℕ) (f : X ⟶ Y)

example : Δ[m] _[n] =
  (yoneda.obj ([m] : SimplexCategory)).obj (Opposite.op [n]) := rfl

def auxfoomap (m : ℕ) : Fin (m + 1) →o Fin (1) where
  toFun := fun _ => 0
  monotone' := fun _ _ => by intro ; rfl

def foomap : X ⟶ Δ[0] where
  app := by
    intro n _
    exact SimplexCategory.Hom.mk (auxfoomap ((Opposite.unop n).len))

def footerm : IsTerminal Δ[0] := by
  apply Limits.IsTerminal.ofUniqueHom foomap
  intro X f
  ext n X_n
  dsimp [foomap, auxfoomap]
  sorry

/- morphisms Δ[0] ⟶ Δ[1] are in bijection with morphisms [0] ⟶ [1] in the
    simplex category -/
example : (Δ[0] ⟶ Δ[1]) ≃ Δ[1] _[0] := yonedaEquiv

def d₀ : Δ[0] ⟶ Δ[1] := yonedaEquiv.invFun (SimplexCategory.δ (0 : Fin 2))

def d₁ : Δ[0] ⟶ Δ[1] := yonedaEquiv.invFun (SimplexCategory.δ (1 : Fin 2))

noncomputable section

/-
scrap work
-/
def foob (t) : (X ⨯ Δ[0]).obj t ≅ (X.obj t ⨯ Δ[0].obj t) :=
  show ((evaluation _ _).obj t).obj (X ⨯ Δ[0]) ≅ _ from
  preservesLimitIso _ _ ≪≫ HasLimit.isoOfNatIso
    (pairComp X Δ[0] ((evaluation SimplexCategoryᵒᵖ Type).obj t))

def proj_iso : (X ⨯ Δ[0]) ≅ X :=
  prod.mapIso (eqToIso (Eq.refl _))
    (IsTerminal.uniqueUpToIso terminalIsTerminal footerm).symm ≪≫
    (prod.rightUnitor _)

structure SimpHom (f₀ f₁ : X ⟶ Y) where
  /- the homotopy -/
  h : X ⨯ Δ[1] ⟶ Y
  /- h(x, 0) = f₀ x -/
  map_zero : prod.map (𝟙 X) d₀ ≫ h = (proj_iso _).hom ≫ f₀
  /- h(x, 1) = f₁ x -/
  map_one : prod.map (𝟙 X) d₁ ≫ h = Limits.prod.fst ≫ f₁


end section
