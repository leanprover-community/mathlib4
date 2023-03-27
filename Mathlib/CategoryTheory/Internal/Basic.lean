import Mathlib.CategoryTheory.ConcreteCategory.Operation

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable (A : Type u₁) [Category.{v₁} A] [ConcreteCategory.{v₂} A]
  (C : Type u₂) [Category.{v₂} C]

structure Internal :=
(obj : C)
(presheaf : Cᵒᵖ ⥤ A)
(iso : yoneda.obj obj ≅ presheaf ⋙ forget A)

instance : Category (Internal A C) := InducedCategory.category (fun X => X.presheaf)

def Internal.presheafFunctor : Internal A C ⥤ Cᵒᵖ ⥤ A := inducedFunctor _
def Internal.typesPresheafFunctor : Internal A C ⥤ Cᵒᵖ ⥤ Type v₂ :=
  Internal.presheafFunctor A C ⋙ (whiskeringRight Cᵒᵖ A (Type v₂)).obj (forget A)

variable {A C}

abbrev Internal.typesPresheaf (X : Internal A C) := (Internal.typesPresheafFunctor A C).obj X

def ConcreteCategory.Operation₀.onTypesPresheaf (oper : Operation₀ A)
    (X : Internal A C) : Types.functorOperation₀ X.typesPresheaf :=
  whiskerLeft X.presheaf oper

def ConcreteCategory.Operation₀.onInternal (oper : Operation₀ A)
    (X : Internal A C) : Types.functorOperation₀ (yoneda.obj X.obj) :=
  (oper.onTypesPresheaf X).of_iso X.iso.symm

def ConcreteCategory.Operation₁.onTypesPresheaf (oper : Operation₁ A)
    (X : Internal A C) : Types.functorOperation₁ X.typesPresheaf :=
  whiskerLeft X.presheaf oper

def ConcreteCategory.Operation₁.onInternal (oper : Operation₁ A)
    (X : Internal A C) : Types.functorOperation₁ (yoneda.obj X.obj) :=
  (oper.onTypesPresheaf X).of_iso X.iso.symm

def ConcreteCategory.Operation₂.onTypesPresheaf (oper : Operation₂ A)
  (X : Internal A C) : Types.functorOperation₂ X.typesPresheaf :=
  whiskerLeft X.presheaf oper

def ConcreteCategory.Operation₂.onInternal (oper : Operation₂ A)
    (X : Internal A C) : Types.functorOperation₂ (yoneda.obj X.obj) :=
  (oper.onTypesPresheaf X).of_iso X.iso.symm

def ConcreteCategory.Operation₃.onTypesPresheaf (oper : Operation₃ A)
  (X : Internal A C) : Types.functorOperation₃ X.typesPresheaf :=
  whiskerLeft X.presheaf oper

def ConcreteCategory.Operation₃.onInternal (oper : Operation₃ A)
    (X : Internal A C) : Types.functorOperation₃ (yoneda.obj X.obj) :=
  (oper.onTypesPresheaf X).of_iso X.iso.symm

end CategoryTheory
