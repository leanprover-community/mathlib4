/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.MayerVietorisSquare

/-
# The Mayer-Vietoris exact sequence in sheaf cohomology

-/

universe w v u

namespace CategoryTheory

open Category Opposite Limits Abelian

-- to be moved
namespace Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (X Y : C)
  [HasBinaryBiproduct X Y] [HasBinaryBiproduct (op X) (op Y)]

noncomputable def biprodOpIso  : op (X ⊞ Y) ≅ op X ⊞ op Y where
  hom := biprod.lift biprod.inl.op biprod.inr.op
  inv := biprod.desc biprod.fst.op biprod.snd.op
  hom_inv_id := sorry
  inv_hom_id := by ext <;> simp [← op_comp]

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

end Ext

end Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrp.{v}]
  [HasExt.{w} (Sheaf J AddCommGrp.{v})]

-- to be moved to `SheafCohomology.Basic`
/-- Given an abelian sheaf `F` on `(C, J)`, `n : ℕ` and `X : C`, this is
the degree-`n` sheaf cohomology of `X` with values in `F`. -/
noncomputable abbrev Sheaf.H' (F : Sheaf J AddCommGrp.{v}) (n : ℕ) (X : C) :
    AddCommGrp.{w} :=
  (F.cohomologyPresheaf n).obj (op X)

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
  sorry

lemma mk₀_f_comp_biprodIso_inv_apply
    {n : ℕ} (x : (F.H' n S.X₂ ⊞ F.H' n S.X₃ : AddCommGrp)) :
    (Ext.mk₀ S.shortComplex.f).comp ((Ext.biprodIso _ _ _ _).inv x) (zero_add _) =
      S.fromBiprod F n x :=
  sorry

/-- Comparison isomorphisms from the Mayer-Vietoris sequence and the
contravariant sequence of `Ext`-groups. -/
noncomputable def sequenceIso : S.sequence F n₀ n₁ h ≅
    Ext.contravariantSequence S.shortComplex_shortExact F n₀ n₁ (by omega) :=
  (isoMk₅ (Iso.refl _) (Ext.biprodIso _ _ _ _).symm
    (Iso.refl _) (Iso.refl _) (Ext.biprodIso _ _ _ _).symm (Iso.refl _)
    (by ext; apply biprodIso_inv_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodIso_inv_apply)
    (by dsimp; rw [comp_id, id_comp]; rfl)
    (by ext; apply biprodIso_inv_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodIso_inv_apply))

lemma sequence_exact : (S.sequence F n₀ n₁ h).Exact :=
  exact_of_iso (S.sequenceIso F n₀ n₁ h).symm (Ext.contravariantSequence_exact _ _ _ _ _)

end GrothendieckTopology.MayerVietorisSquare

end CategoryTheory
