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

variable {C : Type u} [Category.{v} C] {I : C} (F : Cᵒᵖ ⥤ Type (max u v))

open Limits Opposite

variable (hF : (ofArrows (X := I) Empty.elim instIsEmptyEmpty.elim).IsSheafFor F)

section Terminal

variable (I) in
/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on any
object, then `F` takes that object to the terminal object.
-/
noncomputable
def isTerminal_of_isSheafFor_empty_presieve : IsTerminal (F.obj (op I)) := by
  refine @IsTerminal.ofUnique _ _ _ fun Y ↦ ?_
  choose t h using hF (by tauto) (by tauto)
  exact ⟨⟨fun _ ↦ t⟩, fun a ↦ by ext; exact h.2 _ (by tauto)⟩

/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on the
initial object, then `F` preserves terminal objects.
-/
noncomputable
def preservesTerminalOfIsSheafForEmpty (hI : IsInitial I) : PreservesLimit (Functor.empty Cᵒᵖ) F :=
  haveI := hI.hasInitial
  (preservesTerminalOfIso F
    ((F.mapIso (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)) ≪≫
    (F.mapIso (initialIsoIsInitial hI).symm.op) ≪≫
    (terminalIsoIsTerminal (isTerminal_of_isSheafFor_empty_presieve I F hF)).symm)))

end Terminal

section Product

variable (hI : IsInitial I)

-- This is the data of a particular disjoint coproduct in `C`.
variable {α : Type} {X : α → C} (c : Cofan X) (hc : IsColimit c) [(ofArrows X c.inj).hasPullbacks]
    [HasInitial C] [∀ i, Mono (c.inj i)]
    (hd : ∀ i j, i ≠ j → IsPullback (initial.to _) (initial.to _) (c.inj i) (c.inj j))

/--
The two parallel maps in the equalizer diagram for the sheaf condition corresponding to the
inclusion maps in a disjoint coproduct are equal.
-/
theorem firstMap_eq_secondMap : Equalizer.Presieve.Arrows.firstMap F X c.inj =
    Equalizer.Presieve.Arrows.secondMap F X c.inj := by
  ext a ⟨i, j⟩
  simp only [Equalizer.Presieve.Arrows.firstMap, Types.pi_lift_π_apply, types_comp_apply,
    Equalizer.Presieve.Arrows.secondMap]
  by_cases hi : i = j
  · subst hi
    suffices pullback.fst (f := c.inj i) (g := c.inj i) =
      pullback.snd (f := c.inj i) (g := c.inj i) by rw [this]
    exact Mono.right_cancellation _ _ pullback.condition
  · haveI := preservesTerminalOfIsSheafForEmpty F hF hI
    -- let i₁ : op (pullback (c.inj i) (c.inj j)) ≅ op (⊥_ _) := ((hd i j hi).isoPullback).op
    -- let i₂ : op (⊥_ C) ≅ (⊤_ Cᵒᵖ) :=
    --   (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)).symm
    apply_fun (F.mapIso ((hd i j hi).isoPullback).op ≪≫ F.mapIso (terminalIsoIsTerminal
      (terminalOpOfInitial initialIsInitial)).symm ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    simp

theorem piComparison_fac'' :
    haveI : HasCoproduct X := ⟨⟨c, hc⟩⟩
    piComparison F (fun x ↦ op (X x)) = F.map ((opCoproductIsoProduct X).inv ≫
    ((coproductIsCoproduct X).coconePointUniqueUpToIso hc).op.inv) ≫
    Equalizer.Presieve.Arrows.forkMap F X (fun i ↦ c.ι.app ⟨i⟩) := by
  simp only [Cofan.mk_pt, Equalizer.Presieve.Arrows.forkMap, Category.assoc]
  haveI : HasCoproduct X := ⟨⟨c, hc⟩⟩
  haveI : HasCoproduct (fun i ↦ (Discrete.functor X).obj ⟨i⟩) := ⟨⟨c, hc⟩⟩
  have h₁' : Pi.lift (fun i ↦ F.map (c.ι.app ⟨i⟩).op) =
      F.map (Pi.lift (fun i ↦ (c.ι.app ⟨i⟩).op)) ≫ piComparison F _ := by simp
  erw [h₁', ← Category.assoc, ← Functor.map_comp,
    ← desc_op_comp_opCoproductIsoProduct_hom' hc (π := fun i ↦ c.ι.app ⟨i⟩)]
  have h₂ : Cofan.IsColimit.desc hc (fun i ↦ c.ι.app ⟨i⟩) = 𝟙 _ := hc.desc_self
  rw [h₂]
  simp only [Discrete.functor_obj, Iso.op_inv, op_id, Cofan.mk_pt, Iso.op_hom, Category.id_comp,
    Category.assoc, ← Functor.map_comp]
  rw [← Category.id_comp (piComparison F fun x ↦ op (X x))]
  congr
  rw [← F.map_id]
  congr
  simp [Iso.eq_inv_comp, ← Category.assoc, ← op_comp, eq_comm, ← Iso.eq_comp_inv]

theorem piComparison_fac' {Z : C} [HasCoproduct X] (π : (i : α) → X i ⟶ Z) [IsIso (Sigma.desc π)] :
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

theorem piComparison_fac [HasCoproduct X] : piComparison F (fun x ↦ op (X x)) =
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
def preservesProductOfIsSheafFor (hF' : (ofArrows X c.inj).IsSheafFor F) :
    PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F := by
  haveI : HasCoproduct X := ⟨⟨c, hc⟩⟩
  refine @PreservesProduct.ofIsoComparison _ _ _ _ F _ (fun x ↦ op (X x)) _ _ ?_
  rw [piComparison_fac'' (hc := hc)]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
  rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF'
  haveI : (ofArrows X (Cofan.mk _ (Sigma.ι X)).inj).hasPullbacks := sorry
  exact fun b ↦ hF' b (congr_fun (firstMap_eq_secondMap F hF hI c hd) b)

/--
If `F` preserves a particular product, then it `IsSheafFor` the corresponging presieve of arrows.
-/
theorem isSheafFor_of_preservesProduct [PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F] :
    (ofArrows X c.inj).IsSheafFor F := by
  rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
  haveI : HasCoproduct X := ⟨⟨c, hc⟩⟩
  have hi : IsIso (piComparison F (fun x ↦ op (X x))) := inferInstance
  rw [piComparison_fac'' (hc := hc), isIso_iff_bijective, Function.bijective_iff_existsUnique] at hi
  intro b _
  obtain ⟨t, ht₁, ht₂⟩ := hi b
  -- F.map ((opCoproductIsoProduct X).inv ≫ ((coproductIsCoproduct X).coconePointUniqueUpToIso hc).op.inv)
  refine ⟨F.map ((opCoproductIsoProduct X).inv ≫
    ((coproductIsCoproduct X).coconePointUniqueUpToIso hc).op.inv) t, ht₁, fun y hy ↦ ?_⟩
  specialize ht₂ (F.map (((coproductIsCoproduct X).coconePointUniqueUpToIso hc).hom.op ≫
    (opCoproductIsoProduct X).hom) y)
  apply_fun F.map (((coproductIsCoproduct X).coconePointUniqueUpToIso hc).hom.op ≫
    (opCoproductIsoProduct X).hom) using injective_of_mono _
  simp only [← FunctorToTypes.map_comp_apply, Iso.op, Category.assoc]
  rw [ht₂ ?_]
  · change (𝟙 (F.obj (∏ fun x ↦ op (X x)))) t = _
    rw [← Functor.map_id]
    refine congrFun ?_ t
    congr
    simp [Iso.eq_inv_comp, ← Category.assoc, ← op_comp, eq_comm, ← Iso.eq_comp_inv]
  · rw [← hy]
    simp only [Cofan.mk_pt, Iso.op_inv, Functor.map_comp, FunctorToTypes.map_comp_apply,
      types_comp_apply, FunctorToTypes.map_inv_map_hom_apply]
    congr
    simp only [← Functor.map_inv, ← FunctorToTypes.map_comp_apply, ← op_comp,
      Iso.inv_hom_id, op_id, FunctorToTypes.map_id_apply]

theorem isSheafFor_iff_preservesProduct : (ofArrows X (Sigma.ι X)).IsSheafFor F ↔
    Nonempty (PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F) := by
  refine ⟨fun hF' ↦ ⟨preservesProductOfIsSheafFor _ hF hI X hd hF'⟩, fun hF' ↦ ?_⟩
  let _ := hF'.some
  have : Sigma.desc (Sigma.ι X) = 𝟙 _ := by ext; simp
  have _ : IsIso (Sigma.desc (Sigma.ι X)) := by rw [this]; infer_instance
  exact isSheafFor_of_preservesProduct F X (Sigma.ι X)

end Product

end CategoryTheory.Presieve
