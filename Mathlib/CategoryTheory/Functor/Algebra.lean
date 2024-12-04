import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.Quiver.Prefunctor
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


/-!
# The category of algebras for an endofunctor

Given an endofunctor `F` on a category `C`,
an `F`-algebra `X` is an object equipped with a morphism
`F.obj X ⟶ X` satisfying some axioms.
-/

namespace CategoryTheory

open Category Limits

universe v₁ u₁

-- morphism levels before object levels. See note [category_theory universes].
variable {C : Type u₁} [Category.{v₁} C]

namespace Functor

/-- Algebra for an endofunctor -/
structure Algebra (F : C ⥤ C) : Type max u₁ v₁ where
  /-- The underlying object associated to an algebra. -/
  X : C
  /-- The structure morphism associated to an algebra. -/
  σ : (F : C ⥤ C).obj X ⟶ X

namespace Algebra

variable {F : C ⥤ C}

/-- An algebra morphism. -/
@[ext]
structure Hom (A B : Algebra F) where
  /-- The underlying morphism associated to a morphism of algebras. -/
  f : A.X ⟶ B.X
  /-- Compatibility with the structure morphism, for a morphism of algebras. -/
  h : F.map f ≫ B.σ = A.σ ≫ f := by aesop_cat

attribute [reassoc (attr := simp)] Hom.h

namespace Hom

/-- The identity homomorphism for an Eilenberg–Moore algebra. -/
def id (A : Algebra F) : Hom A A where f := 𝟙 A.X

instance (A : Algebra F) : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- Composition of Eilenberg–Moore algebra homomorphisms. -/
def comp {A B C : Algebra F} (f : Hom A B) (g : Hom B C) : Hom A C where f := f.f ≫ g.f

end Hom

instance : CategoryStruct (Algebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): Adding this `ext` lemma to help automation below.
@[ext]
lemma Hom.ext' (X Y : Algebra F) (f g : X ⟶ Y) (h : f.f = g.f) : f = g := Hom.ext h

@[simp]
theorem comp_eq_comp {A A' A'' : Algebra F} (f : A ⟶ A') (g : A' ⟶ A'') :
    Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
theorem id_eq_id (A : Algebra F) : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
theorem id_f (A : Algebra F) : (𝟙 A : A ⟶ A).f = 𝟙 A.X :=
  rfl

@[simp]
theorem comp_f {A A' A'' : Algebra F} (f : A ⟶ A') (g : A' ⟶ A'') : (f ≫ g).f = f.f ≫ g.f :=
  rfl

/-- The category of algebras for an endofunctor. -/
instance : Category (Algebra F) where

end Algebra

variable (F : C ⥤ C)

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
def isoMk {A B : Algebra F} (h : A.X ≅ B.X)
    (w : F.map h.hom ≫ B.σ = A.σ ≫ h.hom := by aesop_cat) : A ≅ B where
  hom := { f := h.hom }
  inv :=
    { f := h.inv
      h := by
        rw [h.eq_comp_inv, Category.assoc, ← w, ← Functor.map_comp_assoc]
        simp }


/-- Given an algebra morphism whose carrier part is an isomorphism, we get an algebra isomorphism.
-/
theorem algebra_iso_of_iso {A B : Algebra F} (g : A ⟶ B) [IsIso g.f] : IsIso g :=
  ⟨⟨{   f := CategoryTheory.inv g.f
        h := by
          rw [IsIso.eq_comp_inv g.f, Category.assoc, ← g.h]
          simp },
      by aesop_cat⟩⟩

/-- The forgetful functor from the category of algebras, forgetting the structure map. -/
@[simps]
def forget : Algebra F ⥤ C where
  obj A := A.X
  map g := g.f

#check CategoryTheory.Functor.ReflectsIsomorphisms

instance forget_reflects_iso : F.forget.ReflectsIsomorphisms where
  -- Porting note: Is this the right approach to introduce instances?
  reflects {_ _} g := fun [IsIso g.f] => algebra_iso_of_iso F g

instance forget_faithful : F.forget.Faithful where

/-- Given an algebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/
theorem algebra_epi_of_epi {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.f] : Epi f :=
  (forget F).epi_of_epi_map h

/-- Given an algebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/
theorem algebra_mono_of_mono {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.f] : Mono f :=
  (forget F).mono_of_mono_map h

#check isTerminalEquivUnique

def IsInitial.ofUnique (X : C) (hX : IsInitial X) :  ∀ Y : C, Unique (X ⟶ Y) := by
  intro Y
  refine ⟨?_, ?_⟩
  refine ⟨?_⟩
  exact hX.desc ⟨X, ⟨_, _⟩⟩
  sorry


def lambek (A : Algebra F) [HasInitial (Algebra F)] (hA : IsInitial A) : F.obj A.X ≅ A.X where
  hom := A.σ
  inv := (hA.to (⟨F.obj A.X, F.map A.σ⟩ : Algebra F)).f
  hom_inv_id := by
    let g : (⟨F.obj A.X, F.map A.σ⟩ : Algebra F) ⟶ A := ⟨A.σ, by rfl⟩
    let comp := (hA.to (⟨F.obj A.X, F.map A.σ⟩ : Algebra F)) ≫ g

  inv_hom_id := by sorry







end Functor

end CategoryTheory
