import Mathlib.CategoryTheory.ConcreteCategory.Operation

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

@[simp]
lemma NatTrans.hcomp_id {C D E : Type _} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) : 𝟙 F ◫ 𝟙 G = 𝟙 (F ⋙ G) := by aesop_cat

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

def Internal.objFunctor : Internal A C ⥤ C where
  obj X := X.obj
  map {X Y} f := yoneda.preimage (X.iso.hom ≫ (f ◫ (𝟙 (forget A))) ≫ Y.iso.inv)
  map_id X := yoneda.map_injective (by
    dsimp
    erw [Functor.image_preimage, Functor.map_id, NatTrans.hcomp_id,
      Category.id_comp, Iso.hom_inv_id])
  map_comp {X Y Z} f g := yoneda.map_injective (by
    dsimp
    simp only [Functor.image_preimage, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
    ext X
    dsimp
    erw [NatTrans.comp_app, FunctorToTypes.map_comp_apply])

variable {A C}

abbrev Internal.typesPresheaf (X : Internal A C) := (Internal.typesPresheafFunctor A C).obj X

@[simps]
def Internal.ofIsoObj (X : Internal A C) {Y : C} (e : X.obj ≅ Y) : Internal A C where
  obj := Y
  presheaf := X.presheaf
  iso := yoneda.mapIso e.symm ≪≫ X.iso

@[simps]
def Internal.ofNatIsoObj {D : Type _} [Category D] (F : D ⥤ Internal A C)
  {G : D ⥤ C} (e : F ⋙ Internal.objFunctor A C ≅ G) : D ⥤ Internal A C where
  obj X := (F.obj X).ofIsoObj (e.app X)
  map f := F.map f

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

lemma ConcreteCategory.Operation₂.assoc.onTypesPresheaf {oper : Operation₂ A}
    (h : oper.assoc) (X : Internal A C) : (oper.onTypesPresheaf X).assoc := by
  exact _root_.congr_arg (fun (o : Operation₃ A) => o.onTypesPresheaf X) h

lemma ConcreteCategory.Operation₂.assoc.onInternal {oper : Operation₂ A}
    (h : oper.assoc) (X : Internal A C) : (oper.onInternal X).assoc :=
  (h.onTypesPresheaf X).of_iso X.iso.symm

lemma ConcreteCategory.Operation₂.zero_add.onTypesPresheaf {oper : Operation₂ A}
    {zero : Operation₀ A} (h : oper.zero_add zero) (X : Internal A C) :
      (oper.onTypesPresheaf X).zero_add (zero.onTypesPresheaf X) := by
  exact _root_.congr_arg (fun (o : Operation₁ A) => o.onTypesPresheaf X) h

lemma ConcreteCategory.Operation₂.zero_add.onInternal {oper : Operation₂ A}
    {zero : Operation₀ A} (h : oper.zero_add zero) (X : Internal A C) :
      (oper.onInternal X).zero_add (zero.onInternal X) :=
  (h.onTypesPresheaf X).of_iso X.iso.symm

lemma ConcreteCategory.Operation₂.add_zero.onTypesPresheaf {oper : Operation₂ A}
    {zero : Operation₀ A} (h : oper.add_zero zero) (X : Internal A C) :
      (oper.onTypesPresheaf X).add_zero (zero.onTypesPresheaf X) := by
  exact _root_.congr_arg (fun (o : Operation₁ A) => o.onTypesPresheaf X) h

lemma ConcreteCategory.Operation₂.add_zero.onInternal {oper : Operation₂ A}
    {zero : Operation₀ A} (h : oper.add_zero zero) (X : Internal A C) :
      (oper.onInternal X).add_zero (zero.onInternal X) :=
  (h.onTypesPresheaf X).of_iso X.iso.symm

lemma ConcreteCategory.Operation₂.comm.onTypesPresheaf {oper : Operation₂ A}
    (h : oper.comm) (X : Internal A C) : (oper.onTypesPresheaf X).comm := by
  exact _root_.congr_arg (fun (o : Operation₂ A) => o.onTypesPresheaf X) h

lemma ConcreteCategory.Operation₂.comm.onInternal {oper : Operation₂ A}
    (h : oper.comm) (X : Internal A C) : (oper.onInternal X).comm :=
  (h.onTypesPresheaf X).of_iso X.iso.symm

lemma ConcreteCategory.Operation₂.add_left_neg.onTypesPresheaf {oper : Operation₂ A}
    {neg : Operation₁ A} {zero : Operation₀ A}
    (h : oper.add_left_neg neg zero) (X : Internal A C) :
      (oper.onTypesPresheaf X).add_left_neg
        (neg.onTypesPresheaf X) (zero.onTypesPresheaf X) := by
  exact _root_.congr_arg (fun (o : Operation₁ A) => o.onTypesPresheaf X) h

lemma ConcreteCategory.Operation₂.add_left_neg.onInternal {oper : Operation₂ A}
    {neg : Operation₁ A} {zero : Operation₀ A}
    (h : oper.add_left_neg neg zero) (X : Internal A C) :
      (oper.onInternal X).add_left_neg
        (neg.onInternal X) (zero.onInternal X) :=
  (h.onTypesPresheaf X).of_iso X.iso.symm

end CategoryTheory
