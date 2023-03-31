import Mathlib.CategoryTheory.ConcreteCategory.Operation
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

namespace CategoryTheory

open Limits

variable {C : Type _} [Category C]

namespace Internal

def ObjOperation₀ [HasTerminal C] (X : C) := ⊤_ C ⟶ X

def ObjOperation₁ (X : C) := X ⟶ X

def ObjOperation₂ (X : C) [HasBinaryProduct X X] := X ⨯ X ⟶ X

def ObjOperation₃ (X : C) [HasBinaryProduct X X] [HasBinaryProduct X (X ⨯ X)] :=
  X ⨯ X ⨯ X ⟶ X

namespace ObjOperation₀

noncomputable def yonedaEquiv [HasTerminal C] (X : C) :
  ObjOperation₀ X ≃ Types.functorOperation₀ (yoneda.obj X) where
  toFun f :=
  { app := fun T _ => terminal.from _ ≫ f
    naturality := fun _ _ f => by
      ext
      dsimp
      rw [← Category.assoc]
      congr
      apply Subsingleton.elim }
  invFun φ := φ.app (Opposite.op (⊤_ C)) PUnit.unit
  left_inv := fun f => by
    dsimp
    simp only [Subsingleton.elim (terminal.from (⊤_ C)) (𝟙 _), Category.id_comp]
  right_inv := fun φ => NatTrans.ext _ _ (by
    ext T ⟨⟩
    exact (congr_fun (φ.naturality (terminal.from T.unop).op) PUnit.unit).symm)

end ObjOperation₀

namespace ObjOperation₁

def yonedaEquiv (X : C) :
  ObjOperation₁ X ≃ Types.functorOperation₁ (yoneda.obj X) :=
  Equiv.symm CategoryTheory.yonedaEquiv

end ObjOperation₁

namespace ObjOperation₂

noncomputable def yonedaEquiv' (X Y Z : C) [HasBinaryProduct X Y] :
  (X ⨯ Y ⟶ Z) ≃ (Types.functorConcat (yoneda.obj X) (yoneda.obj Y) ⟶ yoneda.obj Z ) where
  toFun f :=
  { app := fun T ⟨x, y⟩ => prod.lift x y ≫ f
    naturality := fun _ _ f => by
      ext
      dsimp
      simp only [prod.comp_lift_assoc] }
  invFun φ := φ.app (Opposite.op (X ⨯ Y)) ⟨prod.fst, prod.snd⟩
  left_inv := by aesop_cat
  right_inv := fun φ => by
    ext Z ⟨x, y⟩
    apply (congr_fun (φ.naturality (prod.lift x y).op) ⟨prod.fst, prod.snd⟩).symm.trans
    dsimp
    simp

noncomputable def yonedaEquiv (X : C) [HasBinaryProduct X X] :
  ObjOperation₂ X ≃ Types.functorOperation₂ (yoneda.obj X) :=
  yonedaEquiv' X X X

end ObjOperation₂

namespace ObjOperation₃

noncomputable def yonedaEquiv' (X₁ X₂ X₃ Y : C) [HasBinaryProduct X₂ X₃]
  [HasBinaryProduct X₁ (X₂ ⨯ X₃)] :
  (X₁ ⨯ (X₂ ⨯ X₃) ⟶ Y) ≃
    (Types.functorConcat₃ (yoneda.obj X₁) (yoneda.obj X₂) (yoneda.obj X₃) ⟶ yoneda.obj Y) where
  toFun f :=
  { app := fun T ⟨x, y, z⟩ => prod.lift x (prod.lift y z) ≫ f
    naturality := fun _ _ f => by
      ext
      dsimp
      simp only [prod.comp_lift_assoc, prod.comp_lift] }
  invFun φ := φ.app (Opposite.op (X₁ ⨯ X₂ ⨯ X₃))
    ⟨prod.fst, prod.snd ≫ prod.fst, prod.snd ≫ prod.snd⟩
  left_inv := fun f => by
    convert Category.id_comp f
    refine' prod.hom_ext (by simp) (prod.hom_ext (by simp) (by simp))
  right_inv := fun φ => by
    ext Z ⟨x, y, z⟩
    refine' (congr_fun (φ.naturality (prod.lift x (prod.lift y z)).op) ⟨prod.fst, prod.snd ≫ prod.fst, prod.snd ≫ prod.snd⟩).symm.trans _
    dsimp
    simp

noncomputable def yonedaEquiv (X : C) [HasBinaryProduct X X] [HasBinaryProduct X (X ⨯ X)] :
  ObjOperation₃ X ≃ Types.functorOperation₃ (yoneda.obj X) :=
  yonedaEquiv' X X X X

end ObjOperation₃

end Internal

end CategoryTheory
