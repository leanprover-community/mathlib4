import Mathlib.AlgebraicTopology.SimplicialSet
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory

universe w v u

namespace CategoryTheory

open Simplicial Limits

variable {C : Type u} [Category.{v} C]

namespace SimplicialObject

variable (K L : SimplicialObject C)

@[ext]
structure SimplicialHomObj (A : SSet.{w}) where
  app (Δ : SimplexCategoryᵒᵖ) (a : A.obj Δ) : K.obj Δ ⟶ L.obj Δ
  naturality {Δ Δ' : SimplexCategoryᵒᵖ} (φ : Δ ⟶ Δ') (a : A.obj Δ) :
    K.map φ ≫ app Δ' (A.map φ a) = app Δ a ≫ L.map φ := by aesop_cat

namespace SimplicialHomObj

attribute [reassoc (attr := simp)] naturality

variable {K L} in
lemma congr_app {A : SSet.{w}} {x y : SimplicialHomObj K L A} (h : x = y) (Δ : SimplexCategoryᵒᵖ)
    (a : A.obj Δ) : x.app Δ a = y.app Δ a := by subst h; rfl

@[simps]
def id (A : SSet.{w}) : SimplicialHomObj K K A where
  app _ _ := 𝟙 _

variable {K L}

@[simps]
def comp {M : SimplicialObject C} {A : SSet.{w}} (x : SimplicialHomObj K L A)
    (y : SimplicialHomObj L M A) : SimplicialHomObj K M A where
  app Δ a := x.app Δ a ≫ y.app Δ a

variable {A : SSet.{w}} (x : SimplicialHomObj K L A)

@[simps]
def map {A' : SSet.{w}} (f : A' ⟶ A) :
    SimplicialHomObj K L A' where
  app Δ a := x.app Δ (f.app Δ a)
  naturality {Δ Δ'} φ a := by
    dsimp
    rw [← x.naturality φ (f.app Δ a), FunctorToTypes.naturality _ _ f φ a]

end SimplicialHomObj

@[simps!]
def simplicialHomFunctor : SSet.{w}ᵒᵖ ⥤ Type (max v w) where
  obj A := SimplicialHomObj K L A.unop
  map {A A'} f x := x.map f.unop

@[simps! obj map]
def simplicialHom : SSet.{v} := yoneda.op ⋙ simplicialHomFunctor.{0} K L

variable {K L} in
@[ext]
lemma simplicialHom_ext {Δ : SimplexCategoryᵒᵖ} {x y : (simplicialHom K L).obj Δ}
    (h : ∀ (Δ' : SimplexCategoryᵒᵖ) (f : Δ'.unop ⟶ Δ.unop), x.app Δ' f = y.app Δ' f) : x = y :=
  SimplicialHomObj.ext _ _ (by ext; apply h)

def _root_.SimplexCategory.const' (Δ Δ' : SimplexCategory) (x : Fin (Δ'.len + 1)) : Δ ⟶ Δ' :=
  SimplexCategory.Hom.mk ⟨fun _ => x, by tauto⟩

instance (Δ : SimplexCategory) : Subsingleton (Δ ⟶ [0]) where
  allEq f g := by
    ext : 3
    apply Subsingleton.elim (α := Fin 1)

def simplicialHomEquiv₀ : simplicialHom K L _[0] ≃ (K ⟶ L) where
  toFun x :=
    { app := fun Δ => x.app Δ (SimplexCategory.const' _ _ 0)
      naturality := fun Δ Δ' f => by rw [← x.naturality f]; rfl }
  invFun φ :=
    { app := fun Δ _ => φ.app Δ
      naturality := fun {Δ Δ'} f (s : Δ.unop ⟶ [0]) => by
        obtain rfl := Subsingleton.elim s (SimplexCategory.const' _ _ 0)
        exact φ.naturality f }
  left_inv x := by
    dsimp
    ext Δ (s : _ ⟶ _)
    obtain rfl := Subsingleton.elim s (SimplexCategory.const' _ _ 0)
    rfl
  right_inv φ := rfl

def simplicialHomEquiv (A : SSet.{v}) :
    (A ⟶ simplicialHom K L) ≃ SimplicialHomObj K L A where
  toFun φ :=
    { app := fun Δ a => (φ.app Δ a).app Δ (𝟙 _)
      naturality := fun {Δ Δ'} f a => by
        erw [← (φ.app Δ a).naturality f (𝟙 _),
          ← SimplicialHomObj.congr_app (congr_fun (φ.naturality f) a) Δ' (𝟙 _)]
        rfl }
  invFun x :=
    { app := fun Δ a =>
        { app := fun Δ' f => x.app Δ' (A.map f.op a)
          naturality := fun {Δ' Δ''} φ f => by
            rw [← x.naturality φ (A.map f.op a), ← FunctorToTypes.map_comp_apply]
            rfl }
      naturality := fun Δ Δ' f => by
        dsimp
        ext a Δ'' (φ : Δ''.unop ⟶ Δ'.unop)
        dsimp
        rw [← FunctorToTypes.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ a Δ' f
    exact (SimplicialHomObj.congr_app (congr_fun (φ.naturality f.op) a) Δ' (𝟙 _)).trans
      (congr_arg ((φ.app Δ a).app Δ') (by simp))
  right_inv x := by
    ext Δ a
    dsimp
    erw [FunctorToTypes.map_id_apply _ _]

-- it would be better to define first homotopies between 0-simplicies of simplicial sets
-- and then apply that construction to the simplicial set `simplicialHom K L`
variable {K L} in
structure Homotopy (φ₀ φ₁ : K ⟶ L) where
  h : simplicialHom K L _[1]
  h₀ : (simplicialHom K L).δ 1 h = (simplicialHomEquiv₀ K L).symm φ₀
  h₁ : (simplicialHom K L).δ 0 h = (simplicialHomEquiv₀ K L).symm φ₁

instance : HasTerminal SSet.{v} := by
  dsimp [SSet]
  infer_instance

instance : HasBinaryProducts SSet.{v} := by
  dsimp [SSet]
  infer_instance

-- better use MonoidalOfChosenFiniteProducts and #10616
noncomputable def _root_.SSet.instMonoidalCategory :
  MonoidalCategory SSet.{v} := monoidalOfHasFiniteProducts _

attribute [local instance] SSet.instMonoidalCategory

/-noncomputable instance : EnrichedCategory SSet.{v} (SimplicialObject C) where
  Hom := simplicialHom
  id K := { app := fun Δ x => SimplicialHomObj.id K _ }
  comp K L M := sorry
  id_comp := sorry
  comp_id := sorry
  assoc := sorry-/

end SimplicialObject

end CategoryTheory
