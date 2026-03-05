/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.WithTerminal.Cone

/-! # Functors equifibered over a fixed functor is closed under limits -/

@[expose] public section

namespace CategoryTheory.NatTrans

open Limits Functor ObjectProperty

variable {J K C D ι : Type*} [Category* J] [Category* C] [Category* K] [Category* D]

set_option backward.isDefEq.respectTransparency false in
instance (F : C ⥤ D) [∀ a b : C, HasCoproductsOfShape (a ⟶ b) D] :
    IsClosedUnderLimitsOfShape (fun f : Over F ↦ f.hom.Equifibered) J := by
  wlog hJ : IsConnected J generalizing J
  · refine ⟨fun G ⟨⟨c, α, hc⟩, H⟩ U V f ↦ ?_⟩
    have hα (i j) (f : i ⟶ j) : α.app i ≫ c.map f = α.app j := by simp [← NatTrans.naturality]
    have hc' := WithTerminal.isLimitEquiv.symm hc
    have inst : IsConnected (WithTerminal J) := isConnected_of_hasTerminal _
    exact (this (J := WithTerminal J) inst).1 G ⟨⟨WithTerminal.liftToTerminal c Over.mkIdTerminal,
      { app i := i.casesOn α.app (Over.mkIdTerminal.from _) }, isLimitOfReflects (Over.forget _) (by
      refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (WithTerminal.isLimitEquiv.symm hc)
      · exact NatIso.ofComponents (fun i ↦ i.casesOn (fun _ ↦ .refl _) (.refl _)) <| by
          rintro (i | _) (j | _) <;> (try rintro ⟨⟩) <;> simp
      · exact Cones.ext (.refl _) (by rintro ⟨⟩ <;> simp))⟩, fun i ↦
        i.casesOn H (.of_isIso (𝟙 F))⟩ f
  refine ⟨fun G ⟨⟨c, α, hc⟩, H⟩ i j f ↦ ⟨⟨by simp⟩, ⟨Limits.PullbackCone.isLimitAux' _ fun s ↦ ?_⟩⟩⟩
  let hcᵢ := isLimitOfPreserves (Over.forget _ ⋙ (evaluation _ _).obj i) hc
  let hcⱼ := isLimitOfPreserves (Over.forget _ ⋙ (evaluation _ _).obj j) hc
  dsimp at s
  let l : s.pt ⟶ G.left.obj i := hcᵢ.lift ⟨_, fun k ↦ (H k f).lift (s.fst ≫ (α.app k).left.app j)
    s.snd (by simp [← s.condition, ← NatTrans.comp_app]), fun k₁ k₂ fk₁k₂ ↦ (H _ f).hom_ext
    (by simp [← NatTrans.naturality, ← NatTrans.comp_app, ← Over.comp_left])
    (by simp [← NatTrans.comp_app])⟩
  refine ⟨l, hcⱼ.hom_ext fun k ↦ ?_, ?_, fun {m} hm₁ hm₂ ↦ hcᵢ.hom_ext
    fun k ↦ ((H k f).hom_ext ?_ ?_).trans (hcᵢ.fac ⟨_, _⟩ k).symm⟩
  · simpa [Category.assoc, NatTrans.naturality] using (hcᵢ.fac_assoc _ _ _).trans (by simp)
  · dsimp
    obtain ⟨k⟩ : Nonempty J := inferInstance
    rw [show G.hom.app i = (α.app k).left.app i ≫ (c.obj k).hom.app i by simp [← comp_app]]
    exact (hcᵢ.fac_assoc ..).trans (by simp)
  · dsimp at *
    simp [← NatTrans.naturality, reassoc_of% hm₁]
  · simpa [← NatTrans.comp_app]

set_option backward.isDefEq.respectTransparency false in
open Over in
instance (F : C ⥤ D) [∀ a b : C, HasProductsOfShape (a ⟶ b) D] :
    IsClosedUnderColimitsOfShape (fun f : Under F ↦ f.hom.Coequifibered) J := by
  have : IsClosedUnderIsomorphisms fun f : Under F ↦ f.hom.Coequifibered :=
    ⟨fun {X Y} e ↦ by rw [← Under.w e.hom, Coequifibered.cancel_right_of_respectsIso]; simp⟩
  have (a b : Cᵒᵖ) : HasCoproductsOfShape (a ⟶ b) Dᵒᵖ :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence Quiver.Hom.opEquiv)
  let e : Over F.op ≌ (Under F)ᵒᵖ := (postEquiv _ (opUnopEquiv _ _)).symm.trans (opEquivOpUnder F)
  rw [isClosedUnderColimitsOfShape_iff_op, ← isClosedUnderLimitsOfShape_inverseImage_iff _ _ e]
  convert (inferInstanceAs% (IsClosedUnderLimitsOfShape)
    (fun f : Over F.op ↦ f.hom.Equifibered) Jᵒᵖ) with f
  simp [e, MorphismProperty.cancel_left_of_respectsIso, ← coequifibered_unop_iff]
  rfl

end CategoryTheory.NatTrans
