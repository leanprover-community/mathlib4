import Mathlib.CategoryTheory.ConcreteCategory.Operation
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

lemma Function.Injective.eq_iff'' {X Y : Type _} {f : X → Y} (hf : Function.Injective f)
    (x₁ x₂ : X) (y₁ y₂ : Y) (h₁ : f x₁ = y₁) (h₂ : f x₂ = y₂) : x₁ = x₂ ↔ y₁ = y₂ := by
  subst h₁ h₂
  constructor
  . intro h
    rw [h]
  . apply hf

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

variable {X : C} [HasBinaryProduct X X]

noncomputable def swap (oper : ObjOperation₂ X) :
    ObjOperation₂ X :=
  prod.lift prod.snd prod.fst ≫ oper

lemma swap_yonedaEquiv_inv_apply (oper : Types.functorOperation₂ (yoneda.obj X)) :
    ((yonedaEquiv _).symm oper).swap = (yonedaEquiv _).symm oper.swap := by
  simpa using (congr_fun (oper.naturality ((prod.lift prod.snd prod.fst : X ⨯ X ⟶ _)).op)
    ⟨prod.fst, prod.snd⟩).symm

lemma swap_yonedaEquiv_apply (oper : ObjOperation₂ X) :
    (yonedaEquiv _ oper).swap = yonedaEquiv _ oper.swap := by
  obtain ⟨oper, rfl⟩ := (yonedaEquiv X).symm.surjective oper
  apply (yonedaEquiv X).symm.injective
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply,
    swap_yonedaEquiv_inv_apply]

def comm (oper : ObjOperation₂ X) : Prop := oper = oper.swap

lemma comm_iff (oper : ObjOperation₂ X) :
    oper.comm ↔ ((yonedaEquiv _) oper).comm := by
  dsimp only [comm, Types.functorOperation₂.comm]
  rw [swap_yonedaEquiv_apply]
  constructor
  . intro h
    simp only [← h]
  . apply (yonedaEquiv X).injective

lemma comm_iff' (oper : Types.functorOperation₂ (yoneda.obj X)) :
    oper.comm ↔ ((yonedaEquiv _).symm oper).comm := by
  rw [comm_iff, Equiv.apply_symm_apply]

variable [HasTerminal C]

def add_left_neg (oper : ObjOperation₂ X) (neg : ObjOperation₁ X) (zero : ObjOperation₀ X) :
  Prop :=
    prod.lift neg (𝟙 X) ≫ oper = terminal.from X ≫ zero

lemma add_left_neg_iff (oper : ObjOperation₂ X) (neg : ObjOperation₁ X) (zero : ObjOperation₀ X) :
    oper.add_left_neg neg zero ↔
      ((yonedaEquiv _) oper).add_left_neg ((ObjOperation₁.yonedaEquiv _) neg)
      ((ObjOperation₀.yonedaEquiv _) zero) := by
  apply (ObjOperation₁.yonedaEquiv X).injective.eq_iff''
  all_goals
  . apply (ObjOperation₁.yonedaEquiv X).symm.injective
    simp [ObjOperation₁.yonedaEquiv, CategoryTheory.yonedaEquiv]
    rfl

lemma add_left_neg_iff' (oper : Types.functorOperation₂ (yoneda.obj X))
  (neg : Types.functorOperation₁ (yoneda.obj X)) (zero : Types.functorOperation₀ (yoneda.obj X)) :
  oper.add_left_neg neg zero ↔
    ((yonedaEquiv _).symm oper).add_left_neg ((ObjOperation₁.yonedaEquiv _).symm neg)
      ((ObjOperation₀.yonedaEquiv _).symm zero) := by
  rw [add_left_neg_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

def zero_add (oper : ObjOperation₂ X) (zero : ObjOperation₀ X) : Prop :=
    prod.lift (terminal.from X ≫ zero) (𝟙 X) ≫ oper = 𝟙 X

def add_zero (oper : ObjOperation₂ X) (zero : ObjOperation₀ X) : Prop :=
    prod.lift (𝟙 X) (terminal.from X ≫ zero) ≫ oper = 𝟙 X

lemma zero_add_iff (oper : ObjOperation₂ X) (zero : ObjOperation₀ X) :
    oper.zero_add zero ↔
      ((yonedaEquiv _) oper).zero_add ((ObjOperation₀.yonedaEquiv _) zero) := by
  apply (ObjOperation₁.yonedaEquiv X).injective.eq_iff''
  all_goals
    apply (ObjOperation₁.yonedaEquiv X).symm.injective
    simp
    rfl

lemma zero_add_iff' (oper : Types.functorOperation₂ (yoneda.obj X))
  (zero : Types.functorOperation₀ (yoneda.obj X)) :
  oper.zero_add zero ↔
    ((yonedaEquiv _).symm oper).zero_add ((ObjOperation₀.yonedaEquiv _).symm zero) := by
  rw [zero_add_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma add_zero_iff (oper : ObjOperation₂ X) (zero : ObjOperation₀ X) :
    oper.add_zero zero ↔
      ((yonedaEquiv _) oper).add_zero ((ObjOperation₀.yonedaEquiv _) zero) := by
  apply (ObjOperation₁.yonedaEquiv X).injective.eq_iff''
  all_goals
    apply (ObjOperation₁.yonedaEquiv X).symm.injective
    simp
    rfl

lemma add_zero_iff' (oper : Types.functorOperation₂ (yoneda.obj X))
  (zero : Types.functorOperation₀ (yoneda.obj X)) :
  oper.add_zero zero ↔
    ((yonedaEquiv _).symm oper).add_zero ((ObjOperation₀.yonedaEquiv _).symm zero) := by
  rw [add_zero_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

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

namespace ObjOperation₂

variable {X : C} [HasBinaryProduct X X] [HasBinaryProduct X (X ⨯ X)]

def assoc (oper : ObjOperation₂ X) : Prop :=
  prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ oper) (prod.snd ≫ prod.snd) ≫ oper =
    prod.lift prod.fst (prod.snd ≫ oper)  ≫ oper

lemma assoc_iff (oper : ObjOperation₂ X) :
    oper.assoc ↔ ((yonedaEquiv _) oper).assoc := by
  apply (ObjOperation₃.yonedaEquiv X).injective.eq_iff''
  . apply (ObjOperation₃.yonedaEquiv X).symm.injective
    simp
    rfl
  . apply (ObjOperation₃.yonedaEquiv X).symm.injective
    dsimp [ObjOperation₃.yonedaEquiv, ObjOperation₃.yonedaEquiv', yonedaEquiv, yonedaEquiv']
    simp only [← Category.assoc, prod.comp_lift, limit.lift_π, BinaryFan.mk_pt,
      BinaryFan.π_app_left, BinaryFan.mk_fst, limit.lift_π_assoc, pair_obj_right,
      BinaryFan.π_app_right, BinaryFan.mk_snd]

lemma assoc_iff' (oper : Types.functorOperation₂ (yoneda.obj X)) :
    oper.assoc ↔ ((yonedaEquiv _).symm oper).assoc := by
  rw [assoc_iff, Equiv.apply_symm_apply]

end ObjOperation₂

end Internal

end CategoryTheory
