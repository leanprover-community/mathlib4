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

@[simp]
def natTransConcat {F F₁ F₂ : D ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) :
    F ⟶ functorConcat F₁ F₂ where
  app X a := ⟨τ₁.app X a, τ₂.app X a⟩
  naturality _ _ f := by
    ext x
    exact Prod.ext (congr_fun (τ₁.naturality f) x) (congr_fun (τ₂.naturality f) x)

@[simp]
def functorConcat₃ (F₁ F₂ F₃ : D ⥤ Type w) :=
  functorConcat F₁ (functorConcat F₂ F₃)

@[simps!]
def functorPr₃₁ {F₁ F₂ F₃ : D ⥤ Type w} : functorConcat₃ F₁ F₂ F₃ ⟶ F₁ := functorPr₁

@[simps!]
def functorPr₃₂ {F₁ F₂ F₃ : D ⥤ Type w} : functorConcat₃ F₁ F₂ F₃ ⟶ F₂ :=
  functorPr₂ ≫ functorPr₁

@[simps!]
def functorPr₃₃ {F₁ F₂ F₃ : D ⥤ Type w} : functorConcat₃ F₁ F₂ F₃ ⟶ F₃ :=
  functorPr₂ ≫ functorPr₂

@[simp]
def natTransConcat₃ {F F₁ F₂ F₃ : D ⥤ Type w} (τ₁ : F ⟶ F₁) (τ₂ : F ⟶ F₂) (τ₃ : F ⟶ F₃) :
    F ⟶ functorConcat₃ F₁ F₂ F₃ :=
  natTransConcat τ₁ (natTransConcat τ₂ τ₃)

def functorOperation₀ (F : D ⥤ Type w) := (Functor.const D).obj PUnit ⟶ F
def functorOperation₁ (F : D ⥤ Type w) := F ⟶ F
def functorOperation₂ (F : D ⥤ Type w) := functorConcat F F ⟶ F
def functorOperation₃ (F : D ⥤ Type w) := functorConcat₃ F F F ⟶ F

@[simp]
def functorOperation₀.of_iso {F₁ F₂ : D ⥤ Type w} (h : functorOperation₀ F₁)
  (e : F₁ ≅ F₂) : functorOperation₀ F₂ := h ≫ e.hom

def functorOperation₀.equiv_of_iso {F₁ F₂ : D ⥤ Type w} (e : F₁ ≅ F₂) :
  functorOperation₀ F₁ ≃ functorOperation₀ F₂ where
  toFun h := h.of_iso e
  invFun h := h.of_iso e.symm
  left_inv h := by simp
  right_inv h := by simp

@[simp]
def functorOperation₁.of_iso {F₁ F₂ : D ⥤ Type w} (h : functorOperation₁ F₁)
  (e : F₁ ≅ F₂) : functorOperation₁ F₂ := e.inv ≫ h ≫ e.hom

def functorOperation₁.equiv_of_iso {F₁ F₂ : D ⥤ Type w} (e : F₁ ≅ F₂) :
  functorOperation₁ F₁ ≃ functorOperation₁ F₂ where
  toFun h := h.of_iso e
  invFun h := h.of_iso e.symm
  left_inv h := by simp
  right_inv h := by simp

@[simp]
def functorOperation₂.of_iso {F₁ F₂ : D ⥤ Type w} (h : functorOperation₂ F₁)
    (e : F₁ ≅ F₂) : functorOperation₂ F₂ :=
  natTransConcat (functorPr₁ ≫ e.inv) (functorPr₂ ≫ e.inv) ≫ h ≫ e.hom

def functorOperation₂.equiv_of_iso {F₁ F₂ : D ⥤ Type w} (e : F₁ ≅ F₂) :
  functorOperation₂ F₁ ≃ functorOperation₂ F₂ where
  toFun h := h.of_iso e
  invFun h := h.of_iso e.symm
  left_inv h := by
    apply NatTrans.ext
    ext1 X
    funext
    simp
  right_inv h := by
    apply NatTrans.ext
    ext1 X
    funext
    simp

@[simp]
def functorOperation₃.of_iso {F₁ F₂ : D ⥤ Type w} (h : functorOperation₃ F₁)
    (e : F₁ ≅ F₂) : functorOperation₃ F₂ :=
  natTransConcat₃ (functorPr₃₁ ≫ e.inv) (functorPr₃₂ ≫ e.inv) (functorPr₃₃ ≫ e.inv) ≫
    h ≫ e.hom

def functorOperation₃.equiv_of_iso {F₁ F₂ : D ⥤ Type w} (e : F₁ ≅ F₂) :
  functorOperation₃ F₁ ≃ functorOperation₃ F₂ where
  toFun h := h.of_iso e
  invFun h := h.of_iso e.symm
  left_inv h := by
    apply NatTrans.ext
    ext1 X
    funext
    simp
  right_inv h := by
    apply NatTrans.ext
    ext1 X
    funext
    simp

end Types

variable (A : Type u) [Category.{v} A] [ConcreteCategory.{w} A]

namespace ConcreteCategory

def Operation₀ := (Functor.const A).obj PUnit ⟶ forget A
def Operation₁ := forget A ⟶ forget A
def Operation₂ := Types.functorConcat (forget A) (forget A) ⟶ forget A
def Operation₃ := Types.functorConcat (forget A) (Types.functorConcat (forget A) (forget A)) ⟶ forget A

-- the naturality of these operations should be made automatic...

@[simps]
def AddCommGroup_zero : Operation₀ AddCommGroupCat.{u} where
  app M _ := (0 : M)
  naturality M N f := by
    ext
    exact (AddCommGroupCat.Hom.map_zero f).symm

@[simps]
def AddCommGroup_neg : Operation₁ AddCommGroupCat.{u} where
  app M (x : M) := -x
  naturality M N f := by
    ext x
    exact (AddMonoidHom.map_neg (show AddMonoidHom M N from f) x).symm

@[simps]
def AddCommGroup_add : Operation₂ AddCommGroupCat.{u} where
  app M := fun ⟨(x : M), (y : M)⟩ => x + y
  naturality M N f := by
    ext
    exact (AddCommGroupCat.Hom.map_add _ _ _).symm

end ConcreteCategory

end CategoryTheory
