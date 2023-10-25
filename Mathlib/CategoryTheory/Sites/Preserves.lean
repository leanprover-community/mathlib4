/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.Tactic.ApplyFun

/-!
# Sheaves preserve products

We prove that a presheaf which satisfies the sheaf condition with respect to certain presieves
preserve "the corresponding products".

More precisely, given a presheaf `F : Cᵒᵖ ⥤ Type*`, we have:

## Main results

* If `F` satisfies the sheaf condition with respect to the empty sieve on the initial object of `C`,
  then `F` preserves terminal objects.
See `preservesTerminalOfIsSheafForEmpty`.

* If `F` furthermore satisfies the sheaf condition with respect to the presieve consisting of the
  inclusion arrows in a coproduct in `C`, then `F` preserves the corresponding product.
See `preservesProductOfIsSheafFor`.
-/

universe v u

namespace CategoryTheory.Presieve

open Limits Opposite

variable {C : Type u} [Category.{v} C] (I : C) (F : Cᵒᵖ ⥤ Type (max u v))
    (hF : (ofArrows (X := I) Empty.elim instIsEmptyEmpty.elim).IsSheafFor F)

/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on the
initial object, then `F` takes the initial object to the terminal object.
-/
noncomputable
def isTerminal_obj_initial_of_isSheafFor_empty_presieve : IsTerminal (F.obj (op I)) := by
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
    (terminalIsoIsTerminal (isTerminal_obj_initial_of_isSheafFor_empty_presieve I F hF)).symm)))

variable {α : Type} (X : α → C) [HasCoproduct X]
    [(ofArrows X (fun i ↦ Sigma.ι X i)).hasPullbacks]
    (hd : ∀ i j, i ≠ j → IsInitial (pullback (Sigma.ι X i) (Sigma.ι X j)))
    [∀ i, Mono (Sigma.ι X i)]

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
  · haveI := preservesTerminalOfIsSheafForEmpty F hF
    haveI := hI.hasInitial
    let i₁ : op (pullback (Sigma.ι X i) (Sigma.ι X j)) ≅ op (⊥_ _) :=
      (initialIsoIsInitial (hd i j hi)).op
    let i₂ : op (⊥_ C) ≅ (⊤_ Cᵒᵖ) :=
      (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)).symm
    let _ := preservesTerminalOfIsSheafForEmpty F hF hI
    apply_fun (F.mapIso i₁ ≪≫ F.mapIso i₂ ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    simp

/--
If `F` is a presheaf which `IsSheafFor` a presieve of arrows and the empty presieve, then it
preserves the product corresponding to the presieve of arrows.
-/
theorem preservesProductOfIsSheafFor : (ofArrows X (fun i ↦ Sigma.ι X i)).IsSheafFor F ↔
    Nonempty (PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F) := by
  have h₁ : Pi.lift (fun j ↦ Pi.π (fun a ↦ (op (X a))) j) = 𝟙 _ := by ext; simp
  have h₂ : (fun j ↦ (opCoproductIsoProduct X).inv ≫ (Sigma.ι X j).op) =
    fun j ↦ Pi.π (fun a ↦ (op (X a))) j := by ext; exact opCoproductIsoProduct_inv_comp_ι _ _
  have h₃ : F.map (Pi.lift (fun j ↦ (opCoproductIsoProduct X).inv ≫ (Sigma.ι X j).op)) ≫
    piComparison F (fun z ↦ op (X z)) =
    (F.map (opCoproductIsoProduct X).inv ≫ Pi.lift fun j ↦ F.map ((fun j ↦ Sigma.ι X j) j).op)
  · ext j x
    simp only [h₂, h₁, Functor.map_id, Category.id_comp, piComparison, types_comp_apply,
      Types.pi_lift_π_apply, ← FunctorToTypes.map_comp_apply, congr_fun h₂ j]
  have : piComparison F (fun x ↦ op (X x)) = F.map (opCoproductIsoProduct X).inv ≫
      Equalizer.Presieve.Arrows.forkMap F X (fun i ↦ Sigma.ι X i)
  · rw [Equalizer.Presieve.Arrows.forkMap, ← h₃, h₂, h₁]
    simp
  refine ⟨fun hF' ↦ ?_, fun hF' ↦ ?_⟩
  · constructor
    refine @PreservesProduct.ofIsoComparison _ _ _ _ F _ (fun x ↦ op (X x)) _ _ ?_
    rw [this]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
    rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
    rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF'
    exact fun b ↦ hF' b (congr_fun (firstMap_eq_secondMap F hF hI X hd) b)
  · rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
    let _ := hF'.some
    have hc : IsIso (piComparison F (fun x ↦ op (X x))) := inferInstance
    rw [this, isIso_iff_bijective, Function.bijective_iff_existsUnique] at hc
    intro b _
    obtain ⟨t, ht₁, ht₂⟩ := hc b
    refine ⟨F.map (opCoproductIsoProduct X).inv t, ht₁, fun y hy ↦ ?_⟩
    specialize ht₂ (F.map (opCoproductIsoProduct X).hom y)
    apply_fun (F.mapIso (opCoproductIsoProduct X)).hom using injective_of_mono _
    simp only [Functor.mapIso_hom, FunctorToTypes.map_hom_map_inv_apply]
    apply ht₂
    simpa only [types_comp_apply, FunctorToTypes.map_inv_map_hom_apply]



end CategoryTheory.Presieve
