import Mathlib.CategoryTheory.Internal.Basic

namespace CategoryTheory

namespace Internal

open ConcreteCategory

variable {C : Type _} [Category C]

def addCommGroup (G : Internal AddCommGroupCat C) (X : Cᵒᵖ) :
    AddCommGroup (X.unop ⟶ G.obj) :=
{ zero := (AddCommGroupCat_zero.onInternal G).app X PUnit.unit
  add := fun a b => (AddCommGroupCat_add.onInternal G).app X ⟨a, b⟩
  add_zero := congr_fun (congr_app (AddCommGroupCat_add_zero.onInternal G) X)
  zero_add := congr_fun (congr_app (AddCommGroupCat_zero_add.onInternal G) X)
  add_assoc := fun a b c =>
    congr_fun (congr_app (AddCommGroupCat_add_assoc.onInternal G) X) ⟨a, ⟨b, c⟩⟩
  neg := (AddCommGroupCat_neg.onInternal G).app X
  add_left_neg := congr_fun (congr_app (AddCommGroupCat_add_left_neg.onInternal G) X)
  add_comm := fun a b =>
    congr_fun (congr_app (AddCommGroupCat_add_comm.onInternal G) X) ⟨a, b⟩ }

end Internal

end CategoryTheory
