import Mathlib.CategoryTheory.Internal.Basic

namespace CategoryTheory

namespace Internal

open ConcreteCategory

variable {C : Type _} [Category C]

def addCommGroup (G : Internal AddCommGroupCat C) (X : Cᵒᵖ) :
    AddCommGroup (X.unop ⟶ G.obj) :=
{ zero := (AddCommGroupCat_zero.onInternal G).app X PUnit.unit
  add := fun a b => (AddCommGroupCat_add.onInternal G).app X ⟨a,b⟩
  add_zero := sorry
  zero_add := sorry
  add_assoc := fun a b c =>
    congr_fun (congr_app (AddCommGroupCat_add_assoc.onInternal G) X) ⟨a, ⟨b, c⟩⟩
  neg := fun a => (AddCommGroupCat_neg.onInternal G).app X a
  add_left_neg := sorry
  add_comm := sorry }

end Internal

end CategoryTheory
