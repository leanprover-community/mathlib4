import Mathlib.CategoryTheory.Internal.Basic

namespace CategoryTheory

namespace Internal

open ConcreteCategory

variable {C : Type _} [Category C]

def addCommGroup (G : Internal AddCommGroupCat C) (X : Cᵒᵖ) :
    AddCommGroup (X.unop ⟶ G.obj) :=
{ zero := (addCommGroupCat_zero.onInternal G).app X PUnit.unit
  add := fun a b => (addCommGroupCat_add.onInternal G).app X ⟨a, b⟩
  add_zero := congr_fun (congr_app (addCommGroupCat_add_zero.onInternal G) X)
  zero_add := congr_fun (congr_app (addCommGroupCat_zero_add.onInternal G) X)
  add_assoc := fun a b c =>
    congr_fun (congr_app (addCommGroupCat_add_assoc.onInternal G) X) ⟨a, ⟨b, c⟩⟩
  neg := (addCommGroupCat_neg.onInternal G).app X
  add_left_neg := congr_fun (congr_app (addCommGroupCat_add_left_neg.onInternal G) X)
  add_comm := fun a b =>
    congr_fun (congr_app (addCommGroupCat_add_comm.onInternal G) X) ⟨a, b⟩ }

@[simp]
def addCommGroup_addMonoidHom (G : Internal AddCommGroupCat C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    letI := addCommGroup G X
    letI := addCommGroup G Y
    (X.unop ⟶ G.obj) →+ (Y.unop ⟶ G.obj) :=
  letI := addCommGroup G X
  letI := addCommGroup G Y
  AddMonoidHom.mk' (fun φ => f.unop ≫ φ) (fun a b =>
    (congr_fun ((addCommGroupCat_add.onInternal G).naturality f) ⟨a, b⟩).symm)

@[simp]
def addCommGroup_addMonoidHom' {G₁ G₂ : Internal AddCommGroupCat C} (f : G₁ ⟶ G₂) (f_obj : G₁.obj ⟶ G₂.obj)
  (h : f_obj = (Internal.objFunctor _ _).map f) (X : Cᵒᵖ) :
    letI := addCommGroup G₁ X
    letI := addCommGroup G₂ X
    (X.unop ⟶ G₁.obj) →+ (X.unop ⟶ G₂.obj) :=
  letI := addCommGroup G₁ X
  letI := addCommGroup G₂ X
  AddMonoidHom.mk' (fun φ => φ ≫ f_obj)
    (fun a b => (congr_fun (congr_app
      (addCommGroupCat_add.onInternal_naturality f f_obj h) X) ⟨a, b⟩).symm)

end Internal

end CategoryTheory
