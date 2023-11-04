/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-!
# Sheaves preserve products

We prove that a presheaf which satisfies the sheaf condition with respect to certain presieves
preserve "the corresponding products".

## Main results

More precisely, given a presheaf `F : Cᵒᵖ ⥤ Type*`, we have:

* If `F` satisfies the sheaf condition with respect to the empty sieve on the initial object of `C`,
  then `F` preserves terminal objects.
See `preservesTerminalOfIsSheafForEmpty`.

* If `F` furthermore satisfies the sheaf condition with respect to the presieve consisting of the
  inclusion arrows in a coproduct in `C`, then `F` preserves the corresponding product.
See `preservesProductOfIsSheafFor`.

* If `F` preserves a product, then it satisfies the sheaf condition with respect to the
  corresponding presieve of arrows.
See `isSheafFor_of_preservesProduct`.
-/

universe v u

namespace CategoryTheory.Presieve

open Limits Opposite

variable {C : Type u} [Category.{v} C] (I : C) (F : Cᵒᵖ ⥤ Type (max u v))

variable (hF : (ofArrows (X := I) Empty.elim instIsEmptyEmpty.elim).IsSheafFor F)

/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on any
object, then `F` takes that object to the terminal object.
-/
noncomputable
def isTerminal_of_isSheafFor_empty_presieve : IsTerminal (F.obj (op I)) := by
  refine @IsTerminal.ofUnique _ _ _ fun Y ↦ ?_
  choose t h using hF (by tauto) (by tauto)
  exact ⟨⟨fun _ ↦ t⟩, fun a ↦ by ext; exact h.2 _ (by tauto)⟩

variable {I} (hI : IsInitial I)

/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on the
initial object, then `F` preserves terminal objects.
-/
noncomputable
def preservesTerminalOfIsSheafForEmpty : PreservesLimit (Functor.empty Cᵒᵖ) F :=
  haveI := hI.hasInitial
  (preservesTerminalOfIso F
    ((F.mapIso (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)) ≪≫
    (F.mapIso (initialIsoIsInitial hI).symm.op) ≪≫
    (terminalIsoIsTerminal (isTerminal_of_isSheafFor_empty_presieve I F hF)).symm)))

-- This is the data of a particular disjoint coproduct in `C`.
variable {α : Type} (X : α → C) [HasCoproduct X] [(ofArrows X (Sigma.ι X)).hasPullbacks]
    (hd : ∀ i j [HasInitial C], i ≠ j →
      IsPullback (initial.to _) (initial.to _) (Sigma.ι X i) (Sigma.ι X j))
    [∀ i, Mono (Sigma.ι X i)]

/--
The two parallel maps in the equalizer diagram for the sheaf condition corresponding to the
inclusion maps in a disjoint coproduct are equal.
-/
theorem firstMap_eq_secondMap : Equalizer.Presieve.Arrows.firstMap F X (fun j ↦ Sigma.ι X j) =
    Equalizer.Presieve.Arrows.secondMap F X (fun j ↦ Sigma.ι X j) := by
  ext a ⟨i, j⟩
  simp only [Equalizer.Presieve.Arrows.firstMap, Types.pi_lift_π_apply, types_comp_apply,
    Equalizer.Presieve.Arrows.secondMap]
  by_cases hi : i = j
  · subst hi
    suffices pullback.fst (f := Sigma.ι X i) (g := Sigma.ι X i) =
      pullback.snd (f := Sigma.ι X i) (g := Sigma.ι X i) by rw [this]
    apply Mono.right_cancellation (f := Sigma.ι X i)
    exact pullback.condition
  · haveI := preservesTerminalOfIsSheafForEmpty F hF hI
    haveI := hI.hasInitial
    let i₁ : op (pullback (Sigma.ι X i) (Sigma.ι X j)) ≅ op (⊥_ _) :=
      ((hd i j hi).isoPullback).op
    let i₂ : op (⊥_ C) ≅ (⊤_ Cᵒᵖ) :=
      (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)).symm
    apply_fun (F.mapIso i₁ ≪≫ F.mapIso i₂ ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    simp

theorem piComparison_fac' {Z : C} (π : (i : α) → X i ⟶ Z) [IsIso (Sigma.desc π)] :
    piComparison F (fun x ↦ op (X x)) =
    F.map ((opCoproductIsoProduct X).inv ≫ (inv (Sigma.desc π)).op) ≫
    Equalizer.Presieve.Arrows.forkMap F X π := by
  have h₁ : Pi.lift (fun i ↦ F.map (π i).op) =
      F.map (Pi.lift (fun i ↦ (π i).op)) ≫ piComparison F _ := by simp
  have h₂ : (opCoproductIsoProduct X).inv ≫ (inv (Sigma.desc π)).op =
      inv ((Sigma.desc π).op ≫ (opCoproductIsoProduct X).hom) := by
    simp only [op_inv, IsIso.inv_comp, IsIso.Iso.inv_hom]
  simp only [Equalizer.Presieve.Arrows.forkMap, h₂, h₁,  ← desc_op_comp_opCoproductIsoProduct_hom,
    ← Category.assoc, ← Functor.map_comp, IsIso.inv_comp, IsIso.Iso.inv_hom,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id, Iso.inv_hom_id, Functor.map_id,
    Category.id_comp]

theorem piComparison_fac : piComparison F (fun x ↦ op (X x)) =
    F.map (opCoproductIsoProduct X).inv ≫
    Equalizer.Presieve.Arrows.forkMap F X (Sigma.ι X) := by
  have : Sigma.desc (Sigma.ι X) = 𝟙 _ := by ext; simp
  have _ : IsIso (Sigma.desc (Sigma.ι X)) := by rw [this]; infer_instance
  rw [piComparison_fac' (π := (Sigma.ι X))]
  simp only [op_inv, Functor.map_comp, Functor.map_inv, Category.assoc, this]
  congr
  simp only [op_id, Functor.map_id, IsIso.inv_id]
  rfl

/--
If `F` is a presheaf which `IsSheafFor` a presieve of arrows and the empty presieve, then it
preserves the product corresponding to the presieve of arrows.
-/
noncomputable
def preservesProductOfIsSheafFor (hF' : (ofArrows X (Sigma.ι X)).IsSheafFor F) :
    PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F := by
  refine @PreservesProduct.ofIsoComparison _ _ _ _ F _ (fun x ↦ op (X x)) _ _ ?_
  rw [piComparison_fac]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
  rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF'
  exact fun b ↦ hF' b (congr_fun (firstMap_eq_secondMap F hF hI X hd) b)

/--
If `F` preserves a particular product, then it `IsSheafFor` the corresponging presieve of arrows.
-/
theorem isSheafFor_of_preservesProduct {Z : C} (π : (i : α) → X i ⟶ Z) [IsIso (Sigma.desc π)]
    [PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F] [(ofArrows X π).hasPullbacks] :
    (ofArrows X π).IsSheafFor F := by
  rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
  have hc : IsIso (piComparison F (fun x ↦ op (X x))) := inferInstance
  rw [piComparison_fac' (π := π), isIso_iff_bijective, Function.bijective_iff_existsUnique] at hc
  intro b _
  obtain ⟨t, ht₁, ht₂⟩ := hc b
  refine ⟨F.map ((opCoproductIsoProduct X).inv ≫ (inv (Sigma.desc π)).op ) t, ht₁, fun y hy ↦ ?_⟩
  specialize ht₂ (F.map ((Sigma.desc π).op ≫ (opCoproductIsoProduct X).hom) y)
  apply_fun F.map ((Sigma.desc π).op ≫ (opCoproductIsoProduct X).hom) using injective_of_mono _
  simp only [← FunctorToTypes.map_comp_apply]
  simp only [op_inv, Category.assoc, IsIso.inv_hom_id_assoc,
    Iso.inv_hom_id, FunctorToTypes.map_id_apply]
  apply ht₂
  rw [← hy]
  simp only [op_inv, Functor.map_comp, Functor.map_inv,
    types_comp_apply, FunctorToTypes.map_inv_map_hom_apply]
  congr
  simp only [← Functor.map_inv, ← FunctorToTypes.map_comp_apply, IsIso.hom_inv_id,
    FunctorToTypes.map_id_apply]

theorem isSheafFor_iff_preservesProduct : (ofArrows X (Sigma.ι X)).IsSheafFor F ↔
    Nonempty (PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F) := by
  refine ⟨fun hF' ↦ ⟨preservesProductOfIsSheafFor _ hF hI X hd hF'⟩, fun hF' ↦ ?_⟩
  let _ := hF'.some
  have : Sigma.desc (Sigma.ι X) = 𝟙 _ := by ext; simp
  have _ : IsIso (Sigma.desc (Sigma.ι X)) := by rw [this]; infer_instance
  exact isSheafFor_of_preservesProduct F X (Sigma.ι X)

end CategoryTheory.Presieve
