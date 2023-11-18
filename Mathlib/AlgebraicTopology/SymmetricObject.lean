import Mathlib.AlgebraicTopology.SplitSimplicialObject
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.GroupTheory.Perm.Basic

universe v u

open CategoryTheory Limits

def NonemptyFintypeCat :=
  CategoryTheory.FullSubcategory (fun (X : FintypeCat.{u}) ↦ Nonempty X)

namespace NonemptyFintypeCat

instance : CoeSort NonemptyFintypeCat.{u} (Type u) where
  coe X := X.1.1

def of (X : Type u) [Fintype X] [Nonempty X] :
    NonemptyFintypeCat.{u} :=
  ⟨⟨X, inferInstance⟩, inferInstance⟩

@[simps!]
instance : Category NonemptyFintypeCat.{u} := by
  dsimp [NonemptyFintypeCat]
  infer_instance

@[ext]
lemma hom_ext {X Y : NonemptyFintypeCat.{u}} {f g : X ⟶ Y}
    (h : ∀ (x : X), f x = g x) : f = g := funext h

end NonemptyFintypeCat

@[simps]
def SimplexCategory.toNonemptyFintypeCat :
    SimplexCategory ⥤ NonemptyFintypeCat.{0} where
  obj Δ := NonemptyFintypeCat.of (Fin (Δ.len + 1))
  map f x := f.toOrderHom x

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

def SymmetricObject := NonemptyFintypeCat.{0}ᵒᵖ ⥤ C

namespace SymmetricObject

@[simps!]
instance category : Category (SymmetricObject C) := by
  dsimp only [SymmetricObject]
  infer_instance

def toSimplicialObjectFunctor :
    SymmetricObject C ⥤ SimplicialObject C :=
  (whiskeringLeft _ _ _).obj SimplexCategory.toNonemptyFintypeCat.op

variable {C}

abbrev toSimplicialObject (X : SymmetricObject C) : SimplicialObject C :=
  (toSimplicialObjectFunctor C).obj X

def rep (X : SymmetricObject C) (A : NonemptyFintypeCat) :
  Equiv.Perm A →* Aut (X.obj (Opposite.op A)) where
  toFun g :=
    { hom := X.map (Quiver.Hom.op (g⁻¹).1)
      inv := X.map (Quiver.Hom.op g.1)
      hom_inv_id := by
        rw [← X.map_comp, ← X.map_id]
        congr
        apply Quiver.Hom.unop_inj
        ext
        simp
      inv_hom_id := by
        rw [← X.map_comp, ← X.map_id]
        congr
        apply Quiver.Hom.unop_inj
        ext
        simp }
  map_one' := by
    ext
    apply X.map_id
  map_mul' g₁ g₂ := by
    ext
    dsimp [Aut.Aut_mul_def]
    rw [← X.map_comp]
    rfl

variable [HasFiniteCoproducts C]

structure Splitting (X : SymmetricObject C) where
  s : SimplicialObject.Splitting X.toSimplicialObject
  rep (n : ℕ) : Equiv.Perm (Fin (n + 1)) →* Aut (s.N n)
  -- more axioms: compatibility with the inclusions and differentials
  -- `rep n` is an "induced rep from the trivial group"


end SymmetricObject

end CategoryTheory
