/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

/-!
# Sheaves preserve products

We prove that a presheaf which satisfies the sheaf condition with respect to certain presieves
preserve "the corresponding products".

## Main results

More precisely, given a presheaf `F : Cᵒᵖ ⥤ Type*`, we have:

* If `F` satisfies the sheaf condition with respect to the empty sieve on the initial object of `C`,
  then `F` preserves terminal objects.
See `preservesTerminalOfIsSheafForEmpty`.

* If `F` furthermore satisfies the sheaf condition with respect to the presieve consisting of the
  inclusion arrows in a coproduct in `C`, then `F` preserves the corresponding product.
See `preservesProductOfIsSheafFor`.

* If `F` preserves a product, then it satisfies the sheaf condition with respect to the
  corresponding presieve of arrows.
See `isSheafFor_of_preservesProduct`.
-/

universe v u w

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C] {I : C} (F : Cᵒᵖ ⥤ Type w)

open Limits Opposite

variable (hF : (ofArrows (X := I) Empty.elim Empty.instIsEmpty.elim).IsSheafFor F)

section Terminal

variable (I) in
/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on any
object, then `F` takes that object to the terminal object.
-/
noncomputable
def isTerminal_of_isSheafFor_empty_presieve : IsTerminal (F.obj (op I)) := by
  refine @IsTerminal.ofUnique _ _ _ fun Y ↦ ?_
  choose t h using hF (by tauto) (by tauto)
  exact ⟨⟨fun _ ↦ t⟩, fun a ↦ by ext; exact h.2 _ (by tauto)⟩

include hF in
/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on the
initial object, then `F` preserves terminal objects.
-/
lemma preservesTerminal_of_isSheaf_for_empty (hI : IsInitial I) :
    PreservesLimit (Functor.empty.{0} Cᵒᵖ) F :=
  have := hI.hasInitial
  (preservesTerminal_of_iso F
    ((F.mapIso (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)) ≪≫
    (F.mapIso (initialIsoIsInitial hI).symm.op) ≪≫
    (terminalIsoIsTerminal (isTerminal_of_isSheafFor_empty_presieve I F hF)).symm)))

end Terminal

section Product

variable (hI : IsInitial I)

-- This is the data of a particular disjoint coproduct in `C`.
variable {α : Type*} [Small.{w} α] {X : α → C} (c : Cofan X) (hc : IsColimit c)

theorem piComparison_fac :
    have : HasCoproduct X := ⟨⟨c, hc⟩⟩
    piComparison F (fun x ↦ op (X x)) = F.map (opCoproductIsoProduct' hc (productIsProduct _)).inv ≫
    Equalizer.Presieve.Arrows.forkMap F X c.inj := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  dsimp only [Equalizer.Presieve.Arrows.forkMap]
  have h : Pi.lift (fun i ↦ F.map (c.inj i).op) =
      F.map (Pi.lift (fun i ↦ (c.inj i).op)) ≫ piComparison F _ := by simp
  rw [h, ← Category.assoc, ← Functor.map_comp]
  have hh : Pi.lift (fun i ↦ (c.inj i).op) = (productIsProduct (op <| X ·)).lift c.op := by
    simp [Pi.lift, productIsProduct]
  rw [hh, ← desc_op_comp_opCoproductIsoProduct'_hom hc]
  simp

variable [(ofArrows X c.inj).HasPairwisePullbacks]

include hc in
/--
If `F` preserves a particular product, then it `IsSheafFor` the corresponding presieve of arrows.
-/
theorem isSheafFor_of_preservesProduct [PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F] :
    (ofArrows X c.inj).IsSheafFor F := by
  rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  have hi : IsIso (piComparison F (fun x ↦ op (X x))) := inferInstance
  rw [piComparison_fac (hc := hc), isIso_iff_bijective, Function.bijective_iff_existsUnique] at hi
  intro b _
  obtain ⟨t, ht₁, ht₂⟩ := hi b
  refine ⟨F.map ((opCoproductIsoProduct' hc (productIsProduct _)).inv) t, ht₁, fun y hy ↦ ?_⟩
  apply_fun F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) using injective_of_mono _
  simp [← FunctorToTypes.map_comp_apply,
    ht₂ (F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) y) (by simp [← hy])]

variable [HasInitial C] [∀ i, Mono (c.inj i)]
  (hd : Pairwise fun i j => IsPullback (initial.to _) (initial.to _) (c.inj i) (c.inj j))

include hd hF hI in
/--
The two parallel maps in the equalizer diagram for the sheaf condition corresponding to the
inclusion maps in a disjoint coproduct are equal.
-/
theorem firstMap_eq_secondMap :
    Equalizer.Presieve.Arrows.firstMap F X c.inj =
    Equalizer.Presieve.Arrows.secondMap F X c.inj := by
  ext a ⟨i, j⟩
  simp only [Equalizer.Presieve.Arrows.firstMap, Types.pi_lift_π_apply, types_comp_apply,
    Equalizer.Presieve.Arrows.secondMap]
  by_cases hi : i = j
  · rw [hi, Mono.right_cancellation _ _ pullback.condition]
  · have := preservesTerminal_of_isSheaf_for_empty F hF hI
    apply_fun (F.mapIso ((hd hi).isoPullback).op ≪≫ F.mapIso (terminalIsoIsTerminal
      (terminalOpOfInitial initialIsInitial)).symm ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    ext ⟨i⟩
    exact i.elim

include hc hd hF hI in
/--
If `F` is a presheaf which `IsSheafFor` a presieve of arrows and the empty presieve, then it
preserves the product corresponding to the presieve of arrows.
-/
lemma preservesProduct_of_isSheafFor
    (hF' : (ofArrows X c.inj).IsSheafFor F) :
    PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  refine @PreservesProduct.of_iso_comparison _ _ _ _ F _ (fun x ↦ op (X x)) _ _ ?_
  rw [piComparison_fac (hc := hc)]
  refine IsIso.comp_isIso' inferInstance ?_
  rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
  rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF'
  exact fun b ↦ hF' b (congr_fun (firstMap_eq_secondMap F hF hI c hd) b)

include hc hd hF hI in
theorem isSheafFor_iff_preservesProduct : (ofArrows X c.inj).IsSheafFor F ↔
    PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F :=
  ⟨fun hF' ↦ preservesProduct_of_isSheafFor _ hF hI c hc hd hF',
    fun _ ↦ isSheafFor_of_preservesProduct F c hc⟩

end Product

end CategoryTheory.Presieve
