/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The Mayer-Vietoris exact sequence in sheaf cohomology

Let `C` be a category equipped with a Grothendieck topology `J`.
Let `S : J.MayerVietorisSquare` be a Mayer-Vietoris square for `J`.
Let `F` be an abelian sheaf on `(C, J)`.

In this file, we obtain a long exact Mayer-Vietoris sequence:

`... ⟶ H^n(S.X₄, F) ⟶ H^n(S.X₂, F) ⊞ H^n(S.X₃, F) ⟶ H^n(S.X₁, F) ⟶ H^{n + 1}(S.X₄, F) ⟶ ...`

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Opposite Limits Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

namespace GrothendieckTopology.MayerVietorisSquare

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

/-- The sum of two restriction maps in sheaf cohomology. -/
noncomputable def toBiprod (n : ℕ) :
    F.H' n S.X₄ ⟶ F.H' n S.X₂ ⊞ F.H' n S.X₃ :=
  biprod.lift ((F.cohomologyPresheaf n).map S.f₂₄.op)
      ((F.cohomologyPresheaf n).map S.f₃₄.op)

lemma toBiprod_apply {n : ℕ} (y : F.H' n S.X₄) :
    S.toBiprod F n y = (AddCommGrpCat.biprodIsoProd _ _).inv
      ⟨(F.cohomologyPresheaf n).map S.f₂₄.op y,
        (F.cohomologyPresheaf n).map S.f₃₄.op y⟩ := by
  apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
  dsimp [toBiprod]
  ext
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_fst_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply,
      biprod.lift_fst, Iso.inv_hom_id_apply]
  · rw [Iso.addCommGroupIsoToAddEquiv_apply,
      Iso.addCommGroupIsoToAddEquiv_apply,
      ← AddCommGrpCat.biprodIsoProd_inv_comp_snd_apply,
      Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply,
      biprod.lift_snd, Iso.inv_hom_id_apply]

/-- The difference of two restriction maps in sheaf cohomology. -/
noncomputable def fromBiprod (n : ℕ) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁ :=
  biprod.desc ((F.cohomologyPresheaf n).map S.f₁₂.op)
      (-(F.cohomologyPresheaf n).map S.f₁₃.op)

@[reassoc (attr := simp)]
lemma toBiprod_fromBiprod (n : ℕ) : S.toBiprod F n ≫ S.fromBiprod F n = 0 := by
  simp only [toBiprod, fromBiprod, biprod.lift_desc, Preadditive.comp_neg,
    ← sub_eq_add_neg, sub_eq_zero, ← Functor.map_comp, ← op_comp, S.toSquare.fac]

lemma fromBiprod_biprodIsoProd_inv_apply {n : ℕ}
    (y₁ : F.H' n S.X₂) (y₂ : F.H' n S.X₃) :
    S.fromBiprod F n ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨y₁, y₂⟩) =
      (F.cohomologyPresheaf n).map S.f₁₂.op y₁ - (F.cohomologyPresheaf n).map S.f₁₃.op y₂ := by
  dsimp [fromBiprod]
  rw [← ConcreteCategory.comp_apply]
  simp [AddCommGrpCat.biprodIsoProd_inv_comp_desc, sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] toBiprod_apply in
lemma biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply
    {n : ℕ} (x : F.H' n S.X₄) :
    Ext.biprodAddEquiv.symm ((AddCommGrpCat.biprodIsoProd _ _).hom (S.toBiprod F n x)) =
      (Ext.mk₀ S.shortComplex.g).comp x (zero_add n) :=
  Ext.biprodAddEquiv.injective (by cat_disch)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] sub_eq_add_neg in
lemma mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom
    {n : ℕ} (x : ↑(F.H' n S.X₂ ⊞ F.H' n S.X₃)) :
    (Ext.mk₀ S.shortComplex.f).comp
      (Ext.biprodAddEquiv.symm ((AddCommGrpCat.biprodIsoProd _ _).hom x)) (zero_add n) =
    (S.fromBiprod F n x) := by
  obtain ⟨⟨x₂, x₃⟩, rfl⟩ :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective x
  dsimp
  rw [Ext.biprodAddEquiv_symm_apply,
    Iso.addCommGroupIsoToAddEquiv_symm_apply,
    fromBiprod_biprodIsoProd_inv_apply]
  cat_disch

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- The connecting homomorphism of the Mayer-Vietoris long exact sequence
in sheaf cohomology. -/
noncomputable def δ :
    F.H' n₀ S.X₁ ⟶ F.H' n₁ S.X₄ :=
  AddCommGrpCat.ofHom (S.shortComplex_shortExact.extClass.precomp _ (by omega))

open ComposableArrows

/-- The Mayer-Vietoris long exact sequence of an abelian sheaf `F : Sheaf J AddCommGrpCat`
for a Mayer-Vietoris square `S : J.MayerVietorisSquare`. -/
noncomputable abbrev sequence : ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅ (S.toBiprod F n₀) (S.fromBiprod F n₀) (S.δ F n₀ n₁ h)
    (S.toBiprod F n₁) (S.fromBiprod F n₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Comparison isomorphism from the Mayer-Vietoris sequence and the
contravariant sequence of `Ext`-groups. -/
noncomputable def sequenceIso : S.sequence F n₀ n₁ h ≅
    Ext.contravariantSequence S.shortComplex_shortExact F n₀ n₁ (by omega) :=
  isoMk₅ (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _) (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)
    (by dsimp; rw [comp_id, id_comp]; rfl)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)

lemma sequence_exact : (S.sequence F n₀ n₁ h).Exact :=
  exact_of_iso (S.sequenceIso F n₀ n₁ h).symm (Ext.contravariantSequence_exact _ _ _ _ _)

@[reassoc (attr := simp)]
lemma δ_toBiprod : S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0 :=
  (S.sequence_exact F n₀ n₁ h).zero 2

@[reassoc (attr := simp)]
lemma fromBiprod_δ : S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0 :=
  (S.sequence_exact F n₀ n₁ h).zero 1

end GrothendieckTopology.MayerVietorisSquare

end CategoryTheory
