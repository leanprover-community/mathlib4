/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Condensed.Light.Epi
import Mathlib.Condensed.Light.Yoneda
/-!

# Limits of epimorphisms in `LightCondMod R`

This file proves that a sequential limit of epimorphisms is epimorphic in `LightCondMod R`
In other words, given epis
`⋯ ⟶ Sₙ₊₁ ⟶ Sₙ ⟶ ⋯ ⟶ S₀`,
the projection map `lim Sₙ ⟶ S₀` is surjective.

This should be generalised to light condensed objects in concrete categories for which
`epi_iff_locallySurjective` holds.
-/

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

namespace LightCondensed

private noncomputable def preimage (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) (S : LightProfinite)
    (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) : (n : ℕ) → ((T : LightProfinite) × (F.obj ⟨n⟩).val.obj ⟨T⟩)
  | 0 => ⟨S, g⟩
  | (n+1) =>
    have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
      (preimage R c hF S g n).1 (preimage R c hF S g n).2
    ⟨this.choose, this.choose_spec.choose_spec.choose_spec.choose⟩

private noncomputable def preimage_transitionMap
    (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
      (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
        (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) (n : ℕ) :
          ((preimage R c hF S g (n+1)).1 ⟶ (preimage R c hF S g n).1) :=
  have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
    (preimage R c hF S g n).1 (preimage R c hF S g n).2
  this.choose_spec.choose

private lemma preimage_transitionMap_surj
    (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
      (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
        (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) (n : ℕ) :
          Function.Surjective (preimage_transitionMap R c hF S g n) :=
  have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
    (preimage R c hF S g n).1 (preimage R c hF S g n).2
  this.choose_spec.choose_spec.choose

private lemma preimage_w
    (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
      (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
        (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) (n : ℕ) :
          (F.map (homOfLE n.le_succ).op).val.app ⟨(LightCondensed.preimage R c hF S g (n+1)).1⟩
            (LightCondensed.preimage R c hF S g (n+1)).2 =
              ((F.obj ⟨n⟩).val.map (preimage_transitionMap R c hF S g n).op)
                (LightCondensed.preimage R c hF S g n).2 := by
  have := (LightCondMod.epi_iff_locallySurjective_on_lightProfinite _ _).mp (hF n)
    (preimage R c hF S g n).1 (preimage R c hF S g n).2
  exact this.choose_spec.choose_spec.choose_spec.choose_spec

private noncomputable def preimage_diagram
    (R : Type*) [Ring R] {F : ℕᵒᵖ ⥤ LightCondMod R} (c : Cone F)
      (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))
        (S : LightProfinite) (g : (F.obj ⟨0⟩).val.obj ⟨S⟩) : ℕᵒᵖ ⥤ LightProfinite :=
  Functor.ofOpSequence (X := fun n ↦ (preimage R c hF S g n).1)
    fun n ↦ preimage_transitionMap R c hF S g n

variable (R : Type*) [Ring R]
variable {F : ℕᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

include hc hF in
lemma epi_limit_of_epi : Epi (c.π.app ⟨0⟩) := by
  rw [LightCondMod.epi_iff_locallySurjective_on_lightProfinite]
  intro S g
  have h : Function.Surjective
      (limit.π (LightCondensed.preimage_diagram R c hF S g) { unop := 0 }) := by
    refine Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit _) ?_
    intro n
    simp only [preimage_diagram, Nat.succ_eq_add_one, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact preimage_transitionMap_surj _ _ _ _ _ _
  refine ⟨limit (preimage_diagram R c hF S g), limit.π (preimage_diagram R c hF S g) ⟨0⟩, h, ?_⟩
  let d : Cone F := {
    pt := (lightProfiniteToLightCondSet ⋙ free R).obj
      (limit (LightCondensed.preimage_diagram R c hF S g))
    π := by
      refine NatTrans.ofOpSequence ?_ ?_
      · exact fun n ↦ (lightProfiniteToLightCondSet ⋙ free R).map
          (limit.π _ ⟨n⟩) ≫ (LightCondMod.yonedaEquiv R).symm (preimage R c hF S g n).2
      · intro n
        rw [← limit.w (LightCondensed.preimage_diagram R c hF S g) (homOfLE n.le_succ).op]
        simp only [Functor.comp_obj, Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map,
          Nat.succ_eq_add_one, Functor.comp_map, Functor.map_comp, Category.assoc, Category.id_comp]
        congr 1
        erw [LightCondMod.yonedaEquiv_symm_naturality_left,
          LightCondMod.yonedaEquiv_symm_naturality_right]
        congr 1
        erw [preimage_w R c hF S g n]
        simp [preimage_diagram]
  }
  let x : lightProfiniteToLightCondSet.obj (limit (preimage_diagram R c hF S g)) ⟶
      (forget R).obj c.pt := by
    exact (freeForgetAdjunction R).homEquiv _ _ (hc.lift d)
  refine ⟨(coherentTopology LightProfinite).yonedaEquiv x, ?_⟩
  change ((forget R).map _).val.app _ _ = _
  erw [← (coherentTopology LightProfinite).yonedaEquiv_comp]
  simp only [x, Functor.const_obj_obj, Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj,
    Category.assoc, ← (forget R).map_comp, hc.fac]
  simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map, LightCondMod.yonedaEquiv,
    Equiv.symm_trans_apply, homOfLE_leOfHom, Functor.const_obj_map, Adjunction.homEquiv_counit,
    NatTrans.ofOpSequence_app, Functor.map_comp, d]
  erw [Adjunction.unit_naturality_assoc]
  simp
  rfl

end LightCondensed
