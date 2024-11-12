/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare

/-!
# The Mayer-Vietoris exact sequence in sheaf cohomology

Let `C` be a category equipped with a Grothendieck topology `J`.
Let `S : J.MayerVietorisSquare` be a Mayer-Vietoris square for `J`.
Let `F` be an abelian sheaf on `(C, J)`.

In this file, we obtain a long exact Mayer-Vietoris sequence:

`... ⟶ H^n₀(S.X₄, F) ⟶ H^n₀(S.X₂, F) ⊞ H^n₀(S.X₃, F) ⟶ H^n₀(S.X₁, F) ⟶ H^n₁(S.X₄, F) ⟶ ...`

-/

universe w v u

namespace CategoryTheory

open Category Opposite Limits Abelian

-- to be moved
namespace Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
lemma unop_sub {X Y : Cᵒᵖ} (f g : X ⟶ Y) :
    (f - g).unop = f.unop - g.unop := rfl

end Preadditive

-- to be moved
namespace Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] (X Y : C)
  [HasBinaryBiproduct X Y] [HasBinaryBiproduct (op X) (op Y)]

/-- Comparison of the binary biproduct in a category and its opposit category. -/
noncomputable def biprodOpIso : op (X ⊞ Y) ≅ op X ⊞ op Y where
  hom := biprod.lift biprod.inl.op biprod.inr.op
  inv := biprod.desc biprod.fst.op biprod.snd.op
  hom_inv_id := Quiver.Hom.unop_inj (by simp)
  inv_hom_id := by ext <;> simp [← op_comp]

@[reassoc (attr := simp)]
lemma biprodOpIso_hom_fst :
    (biprodOpIso X Y).hom ≫ biprod.fst = biprod.inl.op := by
  simp [biprodOpIso]

@[reassoc (attr := simp)]
lemma biprodOpIso_hom_snd :
    (biprodOpIso X Y).hom ≫ biprod.snd = biprod.inr.op := by
  simp [biprodOpIso]

@[reassoc (attr := simp)]
lemma inl_biprodOpIso_inv :
    biprod.inl ≫ (biprodOpIso X Y).inv = biprod.fst.op := by
  simp [biprodOpIso]

@[reassoc (attr := simp)]
lemma inr_biprodOpIso_inv :
    biprod.inr ≫ (biprodOpIso X Y).inv = biprod.snd.op := by
  simp [biprodOpIso]

end Limits

namespace Abelian

-- to be moved
namespace Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

instance (n : ℕ) : (extFunctor (C := C) n).Additive where

instance (X : Cᵒᵖ) (n : ℕ) : ((extFunctor n).obj X).Additive where

instance (Y : C) (n : ℕ) : ((extFunctor n).flip.obj Y).Additive where

attribute [local instance] preservesBinaryBiproductsOfPreservesBiproducts

/-- Commutation of `Ext`-groups with the binary biproduct on
the source. -/
noncomputable def biprodIso (X₁ X₂ Y : C) (n : ℕ) :
    AddCommGrp.of (Ext (X₁ ⊞ X₂) Y n) ≅
      AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n) :=
  (((extFunctor n).flip.obj Y).mapIso (biprodOpIso _ _)).trans
    (((extFunctor n).flip.obj Y).mapBiprod _ _)

lemma biprodIso_hom_fst (X₁ X₂ Y : C) (n : ℕ) :
    (biprodIso X₁ X₂ Y n).hom ≫ biprod.fst =
      ((extFunctor n).flip.obj Y).map (biprod.inl : _ ⟶ _).op := by
  dsimp only [biprodIso, Iso.trans, Functor.mapIso, Functor.mapBiprod_hom]
  rw [assoc]
  erw [biprod.lift_fst]
  rw [← Functor.map_comp, biprodOpIso_hom_fst]

lemma biprodIso_hom_snd (X₁ X₂ Y : C) (n : ℕ) :
    (biprodIso X₁ X₂ Y n).hom ≫ biprod.snd =
      ((extFunctor n).flip.obj Y).map (biprod.inr : _ ⟶ _).op := by
  dsimp only [biprodIso, Iso.trans, Functor.mapIso, Functor.mapBiprod_hom]
  rw [assoc]
  erw [biprod.lift_snd]
  rw [← Functor.map_comp, biprodOpIso_hom_snd]

lemma biprod_inl_comp_biprodIso_inv_apply {X₁ X₂ Y : C} (n : ℕ)
    (x : ((AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n)) : AddCommGrp)) :
    (mk₀ biprod.inl).comp ((biprodIso X₁ X₂ Y n).inv x) (zero_add n) =
      (biprod.fst : AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n) ⟶ _) x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = (biprodIso X₁ X₂ Y n).hom y :=
    ⟨(biprodIso X₁ X₂ Y n).inv x, by erw [← comp_apply]; simp⟩
  erw [← comp_apply]
  rw [Iso.hom_inv_id, id_apply]
  exact congr_fun ((forget _).congr_map (biprodIso_hom_fst X₁ X₂ Y n).symm) y

lemma biprod_inr_comp_biprodIso_inv_apply {X₁ X₂ Y : C} (n : ℕ)
    (x : ((AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n)) : AddCommGrp)) :
    (mk₀ biprod.inr).comp ((biprodIso X₁ X₂ Y n).inv x) (zero_add n) =
      (biprod.snd : AddCommGrp.of (Ext X₁ Y n) ⊞ AddCommGrp.of (Ext X₂ Y n) ⟶ _) x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = (biprodIso X₁ X₂ Y n).hom y :=
    ⟨(biprodIso X₁ X₂ Y n).inv x, by erw [← comp_apply]; simp⟩
  erw [← comp_apply]
  rw [Iso.hom_inv_id, id_apply]
  exact congr_fun ((forget _).congr_map (biprodIso_hom_snd X₁ X₂ Y n).symm) y

end Ext

end Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrp.{v}]
  [HasExt.{w} (Sheaf J AddCommGrp.{v})]

namespace GrothendieckTopology.MayerVietorisSquare

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrp.{v})

/-- The sum of two restriction maps in sheaf cohomology. -/
noncomputable def toBiprod (n : ℕ) :
    F.H' n S.X₄ ⟶ F.H' n S.X₂ ⊞ F.H' n S.X₃ :=
  biprod.lift ((F.cohomologyPresheaf n).map S.f₂₄.op)
      ((F.cohomologyPresheaf n).map S.f₃₄.op)

/-- The sum of two restriction maps in sheaf cohomology. -/
noncomputable def fromBiprod (n : ℕ) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁ :=
  biprod.desc ((F.cohomologyPresheaf n).map S.f₁₂.op)
      (-(F.cohomologyPresheaf n).map S.f₁₃.op)

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- The connecting homomorphism of the Mayer-Vietoris long exact sequence
in sheaf cohomology. -/
noncomputable def δ :
    F.H' n₀ S.X₁ ⟶ F.H' n₁ S.X₄ :=
  AddCommGrp.ofHom (S.shortComplex_shortExact.extClass.precomp _ (by omega))

open ComposableArrows

/-- The Mayer-Vietoris long exact sequence of an abelian sheaf `F : Sheaf J AddCommGrp`
for a Mayer-Vietoris square `S : J.MayerVietorisSquare`. -/
noncomputable def sequence : ComposableArrows AddCommGrp.{w} 5 :=
  mk₅ (S.toBiprod F n₀) (S.fromBiprod F n₀) (S.δ F n₀ n₁ h)
    (S.toBiprod F n₁) (S.fromBiprod F n₁)

lemma biprodIso_inv_toBiprod_apply {n : ℕ} (x : F.H' n S.X₄) :
    (Ext.biprodIso _ _ _ _).inv (S.toBiprod F n x) =
      (Ext.mk₀ S.shortComplex.g).comp x (zero_add _) := by
  apply Ext.biprod_ext
  · dsimp
    simp only [Ext.mk₀_comp_mk₀_assoc, biprod.inl_desc, toBiprod]
    erw [Ext.biprod_inl_comp_biprodIso_inv_apply, ← comp_apply,
      biprod.lift_fst]
    rfl
  · dsimp
    simp only [Ext.mk₀_comp_mk₀_assoc, biprod.inr_desc, toBiprod]
    erw [Ext.biprod_inr_comp_biprodIso_inv_apply, ← comp_apply,
      biprod.lift_snd]
    rfl

lemma biprodIso_hom_fromBiprod (n : ℕ) :
    (Ext.biprodIso _ _ _ _).hom ≫ S.fromBiprod F n =
      ((extFunctor n).flip.obj F).map S.shortComplex.f.op := by
  dsimp only [Ext.biprodIso, fromBiprod, Functor.mapIso, Iso.trans,
    Functor.mapBiprod_hom, shortComplex,
    Sheaf.cohomologyPresheaf, Sheaf.cohomologyPresheafFunctor,
    Functor.comp, Functor.flip, Functor.op]
  simp only [assoc, biprod.lift_desc, Preadditive.comp_add,
    ← Functor.map_comp_assoc, biprodOpIso_hom_fst, biprodOpIso_hom_snd,
    Preadditive.comp_neg]
  simp only [← sub_eq_add_neg, ← Functor.map_neg,
    ← NatTrans.comp_app, ← Functor.map_comp]
  rw [← NatTrans.app_sub, ← Functor.map_sub]
  congr 2
  apply Quiver.Hom.unop_inj
  apply biprod.hom_ext
  · erw [biprod.lift_fst]
    simp
  · erw [biprod.lift_snd]
    simp

lemma mk₀_f_comp_biprodIso_inv_apply
    {n : ℕ} (x : (F.H' n S.X₂ ⊞ F.H' n S.X₃ : AddCommGrp)) :
    (Ext.mk₀ S.shortComplex.f).comp ((Ext.biprodIso _ _ _ _).inv x) (zero_add _) =
      S.fromBiprod F n x := by
  obtain ⟨y, rfl⟩ : ∃ y, x = (Ext.biprodIso _ _ _ _).hom y :=
    ⟨(Ext.biprodIso _ _ _ _).inv x, by erw [← comp_apply]; simp⟩
  erw [← comp_apply, ← comp_apply, Iso.hom_inv_id, id_apply]
  exact congr_fun ((forget _).congr_map (S.biprodIso_hom_fromBiprod F n)).symm y

/-- Comparison isomorphism from the Mayer-Vietoris sequence and the
contravariant sequence of `Ext`-groups. -/
noncomputable def sequenceIso : S.sequence F n₀ n₁ h ≅
    Ext.contravariantSequence S.shortComplex_shortExact F n₀ n₁ (by omega) :=
  isoMk₅ (Iso.refl _) (Ext.biprodIso _ _ _ _).symm
    (Iso.refl _) (Iso.refl _) (Ext.biprodIso _ _ _ _).symm (Iso.refl _)
    (by ext; apply biprodIso_inv_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodIso_inv_apply)
    (by dsimp; rw [comp_id, id_comp]; rfl)
    (by ext; apply biprodIso_inv_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodIso_inv_apply)

lemma sequence_exact : (S.sequence F n₀ n₁ h).Exact :=
  exact_of_iso (S.sequenceIso F n₀ n₁ h).symm (Ext.contravariantSequence_exact _ _ _ _ _)

end GrothendieckTopology.MayerVietorisSquare

end CategoryTheory
