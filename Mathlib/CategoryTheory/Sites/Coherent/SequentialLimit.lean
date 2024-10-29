/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Subcanonical
/-!
# Limits of epimorphisms in coherent topoi

This file proves that a sequential limit of epimorphisms is epimorphic in the category of sheaves
for the coherent topology on a preregular finitary extensive concrete category where the effective
epimorphisms are precisely the surjective ones.

In other words, given epimorphisms of sheaves

`⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀`,

the projection map `lim Xₙ ⟶ X₀` is an epimorphism.
-/

universe w v u

open CategoryTheory Limits Opposite

attribute [local instance] ConcreteCategory.instFunLike

namespace CategoryTheory.coherentTopology

variable {C : Type u} [Category.{v} C] [Preregular C] [FinitaryExtensive C]
    {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)} {c : Cone F}
    (hc : IsLimit c)
    (hF : ∀ n, Sheaf.IsLocallySurjective (F.map (homOfLE (Nat.le_succ n)).op))

private noncomputable def preimage (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) :
    (n : ℕ) → ((Y : C) × (F.obj ⟨n⟩).val.obj ⟨Y⟩)
  | 0 => ⟨X, y⟩
  | (n+1) => by
    have := hF n
    rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
    specialize this (preimage X y n).1 (preimage X y n).2
    exact ⟨this.choose, this.choose_spec.choose_spec.choose_spec.choose⟩

private noncomputable def preimageTransitionMap (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    (preimage hF X y (n + 1)).1 ⟶ (preimage hF X y n).1 := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose

private lemma preimageTransitionMap_effectiveEpi (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    EffectiveEpi (preimageTransitionMap hF X y n) := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose_spec.choose

private lemma preimage_w (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    (F.map (homOfLE n.le_succ).op).val.app ⟨(preimage hF X y (n+1)).1⟩
      (preimage hF X y (n+1)).2 = ((F.obj ⟨n⟩).val.map (preimageTransitionMap hF X y n).op)
        (preimage hF X y n).2 := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose_spec.choose_spec.choose_spec

private noncomputable def preimageDiagram (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ (preimage hF X y n).1)
    fun n ↦ preimageTransitionMap hF X y n

variable [ConcreteCategory C] (h : ∀ {X Y : C} (f : X ⟶ Y), EffectiveEpi f ↔ Function.Surjective f)

variable [HasLimitsOfShape ℕᵒᵖ C] [PreservesLimitsOfShape ℕᵒᵖ (forget C)]

include hF h hc in
lemma isLocallySurjective_π_app_zero_of_isLocallySurjective_map :
    Sheaf.IsLocallySurjective (c.π.app ⟨0⟩) := by
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff]
  intro X (y : (F.obj _).val.obj _)
  have hh : Function.Surjective
      (limit.π (preimageDiagram hF X y) ⟨0⟩) := by
    refine Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit _) ?_
    intro n
    simp only [preimageDiagram, Nat.succ_eq_add_one, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.ofOpSequence_map_homOfLE_succ]
    rw [← h]
    exact preimageTransitionMap_effectiveEpi _ _ _ _
  rw [← h] at hh
  refine ⟨limit (preimageDiagram hF X y), limit.π (preimageDiagram hF X y) ⟨0⟩, hh, ?_⟩
  let d : Cone F := {
    pt := ((coherentTopology C).yoneda).obj (limit (preimageDiagram hF X y))
    π := by
      refine NatTrans.ofOpSequence ?_ ?_
      · exact fun n ↦ (coherentTopology C).yoneda.map
          (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm (preimage hF X y n).2
      · intro n
        rw [← limit.w (preimageDiagram hF X y) (homOfLE n.le_succ).op]
        simp only [Functor.comp_obj, Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map,
          Nat.succ_eq_add_one, Functor.comp_map, Functor.map_comp, Category.assoc, Category.id_comp]
        congr 1
        erw [GrothendieckTopology.yonedaEquiv_symm_naturality_left,
          GrothendieckTopology.yonedaEquiv_symm_naturality_right]
        congr 1
        erw [preimage_w hF X y n]
        simp [preimageDiagram] }
  refine ⟨(coherentTopology C).yonedaEquiv (hc.lift d), ?_⟩
  change (c.π.app (op 0)).val.app _ _ = _
  rw [← (coherentTopology C).yonedaEquiv_comp]
  simp only [Functor.const_obj_obj, IsLimit.fac, NatTrans.ofOpSequence_app]
  rw [(coherentTopology C).yonedaEquiv_comp, (coherentTopology C).yonedaEquiv_yoneda_map]
  simp
  rfl

variable [HasSheafify (coherentTopology C) (Type v)]
  [Balanced (Sheaf (coherentTopology C) (Type v))]
  [(coherentTopology C).WEqualsLocallyBijective (Type v)]

include h in
lemma epi_π_app_zero_of_epi {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)} {c : Cone F}
    (hc : IsLimit c) (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) : Epi (c.π.app ⟨0⟩) := by
  simp_rw [← Sheaf.isLocallySurjective_iff_epi'] at hF ⊢
  exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF h


end CategoryTheory.coherentTopology
