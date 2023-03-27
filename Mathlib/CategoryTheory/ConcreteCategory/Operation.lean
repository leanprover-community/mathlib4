import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Algebra.Category.GroupCat.Basic

universe w v u v' u'

namespace CategoryTheory

namespace Types

variable {D : Type u'} [Category.{v'} D]

@[simps]
def functorConcat (F₁ F₂ : D ⥤ Type w) : D ⥤ Type w where
  obj X := F₁.obj X × F₂.obj X
  map f a := ⟨F₁.map f a.1, F₂.map f a.2⟩

@[simps]
def functorPr₁ {F₁ F₂ : D ⥤ Type w} : functorConcat F₁ F₂ ⟶ F₁ where
  app X a := a.1

@[simps]
def functorPr₂ {F₁ F₂ : D ⥤ Type w} : functorConcat F₁ F₂ ⟶ F₂ where
  app X a := a.2

def natTransConcat {F F₁ F₂ : D ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    F ⟶ functorConcat F₁ F₂ where
  app X a := ⟨τ₁.app X a, τ₂.app X a⟩
  naturality _ _ f := by
    ext x
    exact Prod.ext (congr_fun (τ₁.naturality f) x) (congr_fun (τ₂.naturality f) x)

end Types

variable (A : Type u) [Category.{v} A] [ConcreteCategory.{w} A]

namespace ConcreteCategory

def operation₀ := (Functor.const A).obj PUnit ⟶ forget A
def operation₁ := forget A ⟶ forget A
def operation₂ := Types.functorConcat (forget A) (forget A) ⟶ forget A
def operation₃ := Types.functorConcat (forget A) (Types.functorConcat (forget A) (forget A)) ⟶ forget A

-- the naturality of these operations should be made automatic...

@[simps]
def AddCommGroup_zero : operation₀ AddCommGroupCat.{u} where
  app M _ := (0 : M)
  naturality M N f:= by
    ext
    exact (AddCommGroupCat.Hom.map_zero f).symm

@[simps]
def AddCommGroup_neg : operation₁ AddCommGroupCat.{u} where
  app M (x : M) := -x
  naturality M N f := by
    ext x
    exact (AddMonoidHom.map_neg (show AddMonoidHom M N from f) x).symm

@[simps]
def AddCommGroup_add : operation₂ AddCommGroupCat.{u} where
  app M := fun ⟨(x : M), (y : M)⟩ => x + y
  naturality M N f := by
    ext
    exact (AddMonoidHom.map_add (show AddMonoidHom M N from f) _ _).symm

end ConcreteCategory

end CategoryTheory
