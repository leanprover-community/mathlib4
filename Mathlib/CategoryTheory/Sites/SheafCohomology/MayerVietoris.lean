/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Biprod
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

lemma toBiprod_apply {n : ℕ} (y : F.H' n S.X₄) :
    S.toBiprod F n y = (AddCommGrp.biprodIsoProd _ _).inv
      ⟨(F.cohomologyPresheaf n).map S.f₂₄.op y,
        (F.cohomologyPresheaf n).map S.f₃₄.op y⟩ := by
  apply (AddCommGrp.biprodIsoProd _ _).hom_injective
  dsimp [toBiprod]
  ext
  · rw [← AddCommGrp.biprodIsoProd_inv_comp_fst_apply, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      Iso.hom_inv_id_assoc, biprod.lift_fst,
      ← ConcreteCategory.comp_apply, Iso.inv_hom_id]
    dsimp
  · rw [← AddCommGrp.biprodIsoProd_inv_comp_snd_apply, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      Iso.hom_inv_id_assoc, biprod.lift_snd,
      ← ConcreteCategory.comp_apply, Iso.inv_hom_id]
    dsimp

/-- The sum of two restriction maps in sheaf cohomology. -/
noncomputable def fromBiprod (n : ℕ) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁ :=
  biprod.desc ((F.cohomologyPresheaf n).map S.f₁₂.op)
      (-(F.cohomologyPresheaf n).map S.f₁₃.op)

lemma fromBiprod_biprodIsoProd_inv_apply {n : ℕ}
    (y₁ : F.H' n S.X₂) (y₂ : F.H' n S.X₃) :
    S.fromBiprod F n ((AddCommGrp.biprodIsoProd _ _).inv ⟨y₁, y₂⟩) =
      (F.cohomologyPresheaf n).map S.f₁₂.op y₁ - (F.cohomologyPresheaf n).map S.f₁₃.op y₂ := by
  dsimp [fromBiprod]
  rw [← ConcreteCategory.comp_apply, AddCommGrp.biprodIsoProd_inv_comp_apply,
    biprod.inl_desc, biprod.inr_desc, sub_eq_add_neg]
  dsimp

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

lemma fromBiprodIso_inv_toBiprod_apply {n : ℕ} (x : F.H' n S.X₄) :
    (Ext.fromBiprodIso _ _ _ _).inv (S.toBiprod F n x) =
      (Ext.mk₀ S.shortComplex.g).comp x (zero_add _) := by
  apply Ext.biprod_ext
  · dsimp
    rw [Ext.mk₀_comp_mk₀_assoc, biprod.inl_desc,
      Ext.biprod_inl_comp_fromBiprodIso_inv_apply]
    rw [toBiprod_apply]
    apply AddCommGrp.biprodIsoProd_inv_comp_fst_apply
  · dsimp
    rw [Ext.mk₀_comp_mk₀_assoc, biprod.inr_desc,
      Ext.biprod_inr_comp_fromBiprodIso_inv_apply]
    rw [toBiprod_apply]
    apply AddCommGrp.biprodIsoProd_inv_comp_snd_apply

lemma mk₀_f_comp_fromBiprodIso_inv_apply
    {n : ℕ} (x : (F.H' n S.X₂ ⊞ F.H' n S.X₃ : AddCommGrp)) :
    (Ext.mk₀ S.shortComplex.f).comp ((Ext.fromBiprodIso _ _ _ _).inv x) (zero_add _) =
      S.fromBiprod F n x := by
  obtain ⟨⟨y₁, y₂⟩, rfl⟩ := (AddCommGrp.biprodIsoProd _ _).inv_surjective x
  erw [Ext.fromBiprodIso_inv_apply y₁ y₂]
  rw [Ext.fromBiprodEquiv_symm_apply]
  dsimp
  simp only [Ext.comp_add, Ext.mk₀_comp_mk₀_assoc, biprod.lift_fst, biprod.lift_snd]
  rw [fromBiprod_biprodIsoProd_inv_apply, Ext.mk₀_neg, Ext.neg_comp, sub_eq_add_neg]
  rfl

/-- Comparison isomorphism from the Mayer-Vietoris sequence and the
contravariant sequence of `Ext`-groups. -/
noncomputable def sequenceIso : S.sequence F n₀ n₁ h ≅
    Ext.contravariantSequence S.shortComplex_shortExact F n₀ n₁ (by omega) :=
  isoMk₅ (Iso.refl _) (Ext.fromBiprodIso _ _ _ _).symm
    (Iso.refl _) (Iso.refl _) (Ext.fromBiprodIso _ _ _ _).symm (Iso.refl _)
    (by ext; apply fromBiprodIso_inv_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_fromBiprodIso_inv_apply)
    (by dsimp; rw [comp_id, id_comp]; rfl)
    (by ext; apply fromBiprodIso_inv_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_fromBiprodIso_inv_apply)

lemma sequence_exact : (S.sequence F n₀ n₁ h).Exact :=
  exact_of_iso (S.sequenceIso F n₀ n₁ h).symm (Ext.contravariantSequence_exact _ _ _ _ _)

end GrothendieckTopology.MayerVietorisSquare

end CategoryTheory
