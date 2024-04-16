import Mathlib.CategoryTheory.ConcreteCategory.Operation
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

lemma Function.Injective.eq_iff'' {X Y : Type _} {f : X → Y} (hf : Function.Injective f)
    (x₁ x₂ : X) (y₁ y₂ : Y) (h₁ : f x₁ = y₁) (h₂ : f x₂ = y₂) : x₁ = x₂ ↔ y₁ = y₂ := by
  subst h₁ h₂
  constructor
  · intro h
    rw [h]
  · apply hf

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D]

namespace Limits

@[reassoc (attr := simp)]
lemma PreservesLimitPair.iso_inv_comp_map_fst (F : C ⥤ D) (X Y : C) [HasBinaryProduct X Y]
    [HasBinaryProduct (F.obj X) (F.obj Y)] [PreservesLimit (pair X Y) F] :
    (PreservesLimitPair.iso F X Y).inv ≫ F.map Limits.prod.fst = prod.fst := by
  rw [← cancel_epi (PreservesLimitPair.iso F X Y).hom, Iso.hom_inv_id_assoc,
    PreservesLimitPair.iso_hom, prodComparison_fst]

@[reassoc (attr := simp)]
lemma PreservesLimitPair.iso_inv_comp_map_snd (F : C ⥤ D) (X Y : C) [HasBinaryProduct X Y]
    [HasBinaryProduct (F.obj X) (F.obj Y)] [PreservesLimit (pair X Y) F] :
    (PreservesLimitPair.iso F X Y).inv ≫ F.map Limits.prod.snd = prod.snd := by
  rw [← cancel_epi (PreservesLimitPair.iso F X Y).hom, Iso.hom_inv_id_assoc,
    PreservesLimitPair.iso_hom, prodComparison_snd]

end Limits

open Limits


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

noncomputable def map {X : C} [HasTerminal C] [HasTerminal D] (h : ObjOperation₀ X) (F : C ⥤ D)
  [PreservesLimit (Functor.empty C) F] :
    ObjOperation₀ (F.obj X) :=
  (Limits.PreservesTerminal.iso F).inv ≫ F.map h

end ObjOperation₀

namespace ObjOperation₁

def yonedaEquiv (X : C) :
  ObjOperation₁ X ≃ Types.functorOperation₁ (yoneda.obj X) :=
  Equiv.symm CategoryTheory.yonedaEquiv

def map {X : C} (h : ObjOperation₁ X) (F : C ⥤ D) : ObjOperation₁ (F.obj X) :=
  F.map h

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

lemma yonedaEquiv'_apply_comp {X Y Z Z' : C} [HasBinaryProduct X Y]
    (φ : X ⨯ Y ⟶ Z) (ψ : Z ⟶ Z') :
     (yonedaEquiv' X Y Z') (φ ≫ ψ) =
      (yonedaEquiv' X Y Z) φ ≫ yoneda.map ψ := by
  ext ⟨T⟩ ⟨x₁ : T ⟶ X, x₂ : T ⟶ Y⟩
  dsimp [yonedaEquiv']
  simp only [Category.assoc]

lemma yonedaEquiv'_comp_apply {X' Y' X Y Z : C} [HasBinaryProduct X' Y']
  [HasBinaryProduct X Y] (α : X' ⟶ X) (β : Y' ⟶ Y) (φ : X ⨯ Y ⟶ Z) :
    (yonedaEquiv' X' Y' Z) (prod.map α β ≫ φ) =
      (Types.natTransConcat (Types.functorPr₁ ≫ yoneda.map α)
          (Types.functorPr₂ ≫ yoneda.map β)) ≫ (yonedaEquiv' X Y Z) φ := by
  ext ⟨T⟩ ⟨x₁ : T ⟶ X', x₂ : T ⟶ Y'⟩
  dsimp [yonedaEquiv']
  simp only [prod.lift_map_assoc]

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
  · intro h
    simp only [← h]
  · apply (yonedaEquiv X).injective

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
  · apply (ObjOperation₁.yonedaEquiv X).symm.injective
    simp only [Equiv.symm_apply_apply, Types.natTransConcat, yoneda_obj_obj, NatTrans.id_app,
      types_id_apply]
    congr
    simp [ObjOperation₁.yonedaEquiv, CategoryTheory.yonedaEquiv]
    rfl
  · apply (ObjOperation₁.yonedaEquiv X).symm.injective
    simp only [Equiv.symm_apply_apply, Types.natTransConcat, yoneda_obj_obj, NatTrans.id_app,
      types_id_apply]
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

noncomputable def map (h : ObjOperation₂ X) (F : C ⥤ D) [HasBinaryProduct (F.obj X) (F.obj X)]
  [PreservesLimit (pair X X) F] :
    ObjOperation₂ (F.obj X) :=
  (PreservesLimitPair.iso F X X).inv ≫ F.map h

lemma map_swap (h : ObjOperation₂ X) (F : C ⥤ D) [HasBinaryProduct (F.obj X) (F.obj X)]
    [PreservesLimit (pair X X) F] :
    (h.map F).swap = h.swap.map F := by
  dsimp [map, swap]
  simp only [F.map_comp, ← Category.assoc]
  congr 1
  simp only [← cancel_mono ((PreservesLimitPair.iso F X X).hom),
    ← cancel_epi  (PreservesLimitPair.iso F X X).hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  apply prod.hom_ext
  · simp only [PreservesLimitPair.iso_hom, prod.comp_lift, prodComparison_snd,
      prodComparison_fst, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left,
      BinaryFan.mk_fst, Category.assoc, ← F.map_comp]
  · simp only [PreservesLimitPair.iso_hom, prod.comp_lift, prodComparison_snd,
      prodComparison_fst, limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right,
      BinaryFan.mk_snd, Category.assoc, ← F.map_comp]

lemma comm.map {add : ObjOperation₂ X} (h : add.comm) (F : C ⥤ D)
    [HasBinaryProduct (F.obj X) (F.obj X)] [PreservesLimit (pair X X) F] :
    (add.map F).comm := by
  dsimp only [comm] at h ⊢
  rw [map_swap, ← h]

lemma add_zero.map {add : ObjOperation₂ X} {zero : ObjOperation₀ X}
    (h : add.add_zero zero) (F : C ⥤ D) [HasTerminal D] [PreservesLimit (Functor.empty C) F]
    [HasBinaryProduct (F.obj X) (F.obj X)] [PreservesLimit (pair X X) F] :
    (add.map F).add_zero (zero.map F) := by
  dsimp only [add_zero]
  refine' Eq.trans _ ((congr_arg (fun (f : ObjOperation₁ X) => f.map F) h).trans _)
  · dsimp [ObjOperation₂.map, ObjOperation₁.map, ObjOperation₀.map]
    simp only [F.map_comp, ← Category.assoc]
    congr 1
    simp only [← cancel_mono (PreservesLimitPair.iso F X X).hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    apply prod.hom_ext
    · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
        PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← F.map_comp,
        Functor.map_id]
    · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
        PreservesLimitPair.iso_hom, Category.assoc, prodComparison_snd, ← F.map_comp]
      rw [F.map_comp, ← Category.assoc]
      congr 1
      rw [← cancel_mono (PreservesTerminal.iso F).hom]
      apply Subsingleton.elim
  · apply F.map_id

lemma zero_add.map {add : ObjOperation₂ X} {zero : ObjOperation₀ X}
    (h : add.zero_add zero) (F : C ⥤ D) [HasTerminal D] [PreservesLimit (Functor.empty C) F]
    [HasBinaryProduct (F.obj X) (F.obj X)] [PreservesLimit (pair X X) F] :
    (add.map F).zero_add (zero.map F) := by
  --dsimp only [add_zero]
  refine' Eq.trans _ ((congr_arg (fun (f : ObjOperation₁ X) => f.map F) h).trans _)
  · dsimp [ObjOperation₂.map, ObjOperation₁.map, ObjOperation₀.map]
    simp only [F.map_comp, ← Category.assoc]
    congr 1
    simp only [← cancel_mono (PreservesLimitPair.iso F X X).hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    apply prod.hom_ext
    · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
        PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← F.map_comp ]
      rw [F.map_comp, ← Category.assoc]
      congr 1
      rw [← cancel_mono (PreservesTerminal.iso F).hom]
      apply Subsingleton.elim
    · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
        PreservesLimitPair.iso_hom, Category.assoc, prodComparison_snd, ← F.map_comp, F.map_id]
  · apply F.map_id

lemma add_left_neg.map {add : ObjOperation₂ X} {neg : ObjOperation₁ X} {zero : ObjOperation₀ X}
    (h : add.add_left_neg neg zero) (F : C ⥤ D) [HasTerminal D] [PreservesLimit (Functor.empty C) F]
    [HasBinaryProduct (F.obj X) (F.obj X)] [PreservesLimit (pair X X) F] :
    (add.map F).add_left_neg (neg.map F) (zero.map F) := by
  --dsimp only [add_zero]
  refine' Eq.trans _ ((congr_arg (fun (f : ObjOperation₁ X) => f.map F) h).trans _)
  · dsimp [ObjOperation₂.map, ObjOperation₁.map, ObjOperation₀.map]
    simp only [F.map_comp, ← Category.assoc]
    congr 1
    simp only [← cancel_mono (PreservesLimitPair.iso F X X).hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    apply prod.hom_ext
    · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
        PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← F.map_comp]
    · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
        PreservesLimitPair.iso_hom, Category.assoc, prodComparison_snd, ← F.map_comp, F.map_id]
  · dsimp [ObjOperation₂.map, ObjOperation₁.map, ObjOperation₀.map]
    simp only [F.map_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (PreservesTerminal.iso F).hom]
    apply Subsingleton.elim

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

noncomputable def map {X : C} [HasBinaryProduct X X] [HasBinaryProduct X (X ⨯ X)]
    (h : ObjOperation₃ X) (F : C ⥤ D) [HasBinaryProduct (F.obj X) (F.obj X)]
    [HasBinaryProduct (F.obj X) (F.obj X ⨯ F.obj X)]
    [HasBinaryProduct (F.obj X) (F.obj (X ⨯ X))]
    [PreservesLimit (pair X X) F] [PreservesLimit (pair X (X ⨯ X)) F] :
    ObjOperation₃ (F.obj X) :=
  prod.lift prod.fst (prod.snd ≫ (PreservesLimitPair.iso F X X).inv) ≫
    (PreservesLimitPair.iso F X (X ⨯ X)).inv  ≫ F.map h

end ObjOperation₃

namespace ObjOperation₂

variable {X : C} [HasBinaryProduct X X] [HasBinaryProduct X (X ⨯ X)]

def assoc (oper : ObjOperation₂ X) : Prop :=
  prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ oper) (prod.snd ≫ prod.snd) ≫ oper =
    prod.lift prod.fst (prod.snd ≫ oper)  ≫ oper

lemma assoc_iff (oper : ObjOperation₂ X) :
    oper.assoc ↔ ((yonedaEquiv _) oper).assoc := by
  apply (ObjOperation₃.yonedaEquiv X).injective.eq_iff''
  · apply (ObjOperation₃.yonedaEquiv X).symm.injective
    simp
    rfl
  · apply (ObjOperation₃.yonedaEquiv X).symm.injective
    simp only [Equiv.symm_apply_apply, Types.functorConcat₃, Types.natTransConcat,
      Types.functorConcat_obj, yoneda_obj_obj, Types.functorPr₃₁_app, Types.functorPr₃₂_app,
      Types.functorPr₃₃_app, Prod.mk.eta, FunctorToTypes.comp,
      ObjOperation₃.yonedaEquiv, ObjOperation₃.yonedaEquiv', yonedaEquiv, yonedaEquiv']
    dsimp
    congr
    aesop_cat

lemma assoc_iff' (oper : Types.functorOperation₂ (yoneda.obj X)) :
    oper.assoc ↔ ((yonedaEquiv _).symm oper).assoc := by
  rw [assoc_iff, Equiv.apply_symm_apply]

lemma assoc.map {add : ObjOperation₂ X} (h : add.assoc) (F : C ⥤ D)
    [HasBinaryProduct (F.obj X) (F.obj X)] [PreservesLimit (pair X X) F]
    [HasBinaryProduct (F.obj X) (F.obj X ⨯ F.obj X)]
    [HasBinaryProduct (F.obj X) (F.obj (X ⨯ X))]
    [PreservesLimit (pair X (X ⨯ X)) F] :
  (add.map F).assoc := by
  dsimp only [assoc] at h ⊢
  refine' Eq.trans _ ((congr_arg (fun (f : ObjOperation₃ X) => f.map F) h).trans _)
  · dsimp [ObjOperation₃.map, ObjOperation₂.map]
    simp only [F.map_comp, ← Category.assoc]
    congr 1
    simp only [← cancel_mono (PreservesLimitPair.iso F X X).hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    apply prod.hom_ext
    · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
        PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← F.map_comp]
      simp only [F.map_comp, ← Category.assoc]
      congr 1
      simp only [← cancel_mono (PreservesLimitPair.iso F X X).hom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
      apply prod.hom_ext
      · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
          PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← F.map_comp,
          PreservesLimitPair.iso_inv_comp_map_fst]
      · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
          PreservesLimitPair.iso_hom, Category.assoc, prodComparison_snd, ← F.map_comp]
        simp only [F.map_comp, PreservesLimitPair.iso_inv_comp_map_snd_assoc,
          limit.lift_π_assoc, BinaryFan.mk_pt, pair_obj_right, BinaryFan.π_app_right,
          BinaryFan.mk_snd, Category.assoc, PreservesLimitPair.iso_inv_comp_map_fst]
    · simp only [limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
        PreservesLimitPair.iso_hom, Category.assoc, prodComparison_snd, ← F.map_comp]
      simp only [Functor.map_comp, PreservesLimitPair.iso_inv_comp_map_snd_assoc,
        limit.lift_π_assoc, BinaryFan.mk_pt, pair_obj_right, BinaryFan.π_app_right,
        BinaryFan.mk_snd, Category.assoc, PreservesLimitPair.iso_inv_comp_map_snd]
  · dsimp [ObjOperation₃.map, ObjOperation₂.map]
    simp only [F.map_comp, ← Category.assoc]
    congr 1
    simp only [← cancel_mono (PreservesLimitPair.iso F X X).hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    apply prod.hom_ext
    · simp only [PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← F.map_comp,
        limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
        PreservesLimitPair.iso_inv_comp_map_fst]
    · simp only [PreservesLimitPair.iso_hom, Category.assoc, prodComparison_snd, limit.lift_π,
        BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd, ← F.map_comp]
      simp only [F.map_comp, ← Category.assoc]
      congr 1
      simp only [← cancel_mono (PreservesLimitPair.iso F X X).hom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
      apply prod.hom_ext
      · simp
      · simp

end ObjOperation₂

end Internal

end CategoryTheory
